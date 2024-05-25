/// This example shows how to use cq-fold-proof to perform (vectored) lookup.
///
/// It is cost saving to merge multiple tables into one big cq-lookup table.
/// The following cq lookup-table is a contenation of two tables: 
/// table 1: (4 even numbers) and table 2: (essentially 4 prime numbers,
///  and then padded with repetitions of these entries)
/// TABLE1_TBL_ID           TABLE2_TBL_VALUE
/// 0                       0                //DUMMY entry for unselected
/// 1                       100
/// 1                       200
/// 1                       600
/// 1                       800
/// 2                       17
/// 2                       19
/// 2                       97
/// 2                       repetitions of entries ...
/// This sample also contains one halo2-lookup argument 
/// as comparison of syntax.


use ff::Field;
use std::io::Read;
use std::fs::File;
use std::collections::HashMap;
use halo2_proofs::{
	dev::MockProver,
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
		create_proof_cq, keygen_pk_cq, keygen_vk_custom_cq,
		Advice, Circuit, Column,
        ConstraintSystem, ErrorFront,
		TableColumn, CqTableColumn, Selector, Expression, Instance,
    },
    poly::{
		commitment::{Params},
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverGWC, VerifierGWC},
            strategy::SingleStrategy,
        },
        Rotation,
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer 
    },
};
use halo2_backend::plonk::{cq_lookup::{
		batch_kzg::{ParamsKzgCq,default_trapdoor},
		zk_qanizk_cq::{CqAux,CqAuxVer,gen_hash_idx_for_tables},
		prover::CqProverSchemeKzg,
		verifier::{CqVerifierSchemeKzg},
		utils::{Timer,log_perf,LOG1}
	},
	verifier::verify_proof_cq
};
use halo2curves::bn256::{Bn256, Fr, G1Affine};
use rand_core::OsRng;

//macros for CqTableColumns (these correspond to the unique ID of externally
//stored tables, values and their commitments in cq_cached/ folder
pub const CQ_TABLE1_TBLID: usize = 101;
pub const CQ_TABLE2_VAL: usize = 102;
pub const LOOKUP_TABLE_SIZE: usize = 1usize<<8;

#[allow(dead_code)]
#[derive(Clone, Copy)]
struct TestCircuit <F:Field>{
	a: F
}

#[derive(Debug, Clone)]
struct MyConfig {
	// for the builtin halo2-lookup
    selector: Selector,
    table: TableColumn,
    instance: Column<Instance>,
    advice: Column<Advice>,

	// for the cq-lookup
	cq_selector: Selector,
    cq_table1: CqTableColumn,
    cq_table2: CqTableColumn,
    subtable_id: Column<Advice>,
    subtable_val: Column<Advice>,
}

impl Circuit<Fr> for TestCircuit<Fr> {
    type Config = MyConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self {a: Fr::from(0)}
    }

    fn configure(meta: &mut ConstraintSystem<Fr>)
		-> MyConfig {
        let config = MyConfig {
            selector: meta.complex_selector(),
            table: meta.lookup_table_column(),
            advice: meta.advice_column(),
			instance: meta.instance_column(),

            cq_selector: meta.complex_selector(),
            cq_table1: meta.cq_lookup_table_column(CQ_TABLE1_TBLID),
            cq_table2: meta.cq_lookup_table_column(CQ_TABLE2_VAL),
            subtable_id: meta.advice_column(),
            subtable_val: meta.advice_column(),
        };
		meta.enable_equality(config.instance);

		// the default halo2 lookup
        meta.lookup("lookup", |meta| {
            let selector = meta.query_selector(config.selector);
            let not_selector = Expression::Constant(Fr::ONE) - selector.clone();
            let advice = meta.query_advice(config.advice, Rotation::cur());
            vec![(selector * advice + not_selector, config.table)]
        });

		//cq_lookup is similar, allowing input expressions
        let cqarg_id = meta.cq_lookup("cq_lookup", |meta| {
            let selector = meta.query_selector(config.cq_selector);
            let subtable_id = meta.query_advice(config.subtable_id, 
					Rotation::cur());
            let subtable_val = meta.query_advice(config.subtable_val, 
					Rotation::cur());
			//two cq-tables, each has one column
            vec![
				(selector.clone() * subtable_id , config.cq_table1),
				(selector * subtable_val, config.cq_table2),
			]
        });

		// This is the cq's equivalent to layouter.assign_table().
		// Since cq_tables are fixed, we load it in config (instead of layouter)
		// when b_reset_cache is false, and when cache exists for a 
		// CqTableColumn, it's loaded from cache/ folder 
		// NOTE: the cache loading from file system
		// has not been implemented yet (TODO).
		//
		// The table column data is saved in the ConstraintSystem
		// to improve: the vkey constains ConstraintSystem (later
		// should cut the data part for vkey and retain the data for pkey) 
		//
		// The following mainly calls set_cq_table to set up lookup table
		// contents. The "hs_idx" is used to perform looking up of
		// the position of elements in lookup table when building the cq-proof.
		let mut vid:Vec<u64> = 
			vec![0, 1, 1, 1, 1, 2, 2, 2]; //see example on top
		let mut vals:Vec<u64> = vec![0, 100, 200, 600, 800, 17, 19, 97];
		let n_more = LOOKUP_TABLE_SIZE - vals.len();
		vid.append(&mut vec![2u64; n_more]);
		vals.append(&mut vec![97u64; n_more]);
		let f_subtbl_id:Vec<Fr> = vid.iter().map(|x| Fr::from(*x)).collect(); 
		let f_vals:Vec<Fr> = vals.iter().map(|x| Fr::from(*x)).collect(); 
		let b_reset_cache= true;
		let hs_idx = if b_reset_cache 
		{ gen_hash_idx_for_tables(&vec![f_subtbl_id.clone(), f_vals.clone()]) } 			else {HashMap::<Vec<u8>,usize>::new()};
		meta.set_cq_table(config.cq_table1, b_reset_cache, f_subtbl_id);
		meta.set_cq_table(config.cq_table2, b_reset_cache, f_vals);
		meta.set_hash_idx(cqarg_id, b_reset_cache, hs_idx);

        config
    }

    fn synthesize(
        &self,
        config: MyConfig,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), ErrorFront> {
        layouter.assign_table(
            || "8-bit table",
            |mut table| {
                for row in 0u64..(1 << 8) {
                    table.assign_cell(
                        || format!("row {row}"),
                        config.table,
                        row as usize,
                        || Value::known(Fr::from(row + 1)),
                    )?;
                }

                Ok(())
            },
        )?;

		//set to true to test if MockProver works for failing cases
		let b_introduce_err = false;
		let b_introduce_err_cq = false;

        layouter.assign_region(
            || "assign values",
            |mut region| {
				//1. first 16 entries: for plookup
                for offset in 0u64..(1 << 4) {
                    config.selector.enable(&mut region, offset as usize)?;
					let value = if b_introduce_err && offset==7
					{offset%128+3221} else {(offset%128) + 1};
                    region.assign_advice(
                        || format!("offset {offset}"),
                        config.advice,
                        offset as usize,
                        || Value::known(Fr::from(value)),
                    )?;
                }

				//2. next entries from 16 to 64: for cq-lookup
                for offset in (1<<4)..(1 << 6) {
                    config.cq_selector.enable(&mut region, offset as usize)?;
					let mut value = if offset%2==0 {17} else {97};
					if b_introduce_err_cq && offset==(1u64<<4) + 7{
						value = 333333; //not in cq tables
					}
                    region.assign_advice(
                        || format!("offset {offset}"),
                        config.subtable_val,
                        offset as usize,
                        || Value::known(Fr::from(value)),
                    )?;
                    region.assign_advice(
                        || format!("offset {offset}"),
                        config.subtable_id,
                        offset as usize,
                        || Value::known(Fr::from(2)),
                    )?;
                }

                Ok(())
            },
        )
    }
}


fn main() {
	//1. Mock Prover
	let b_perf = true;
	let mut timer = Timer::new();
	let blinding_factors = 6; //blinding factors for each halo2 column 
    let k = 9;  //log of column size
	let column_size = 1<<k; //size of each column of halo2
    let circuit = TestCircuit { a: Fr::from(0) };
    let public_inputs  = vec![Fr::from(0)];
    let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

	//2. Generating Keys needed for both PSE and CQ
	// when b_fast mode is true, we use trusetd_setup to generate
	// commit_lookup_table and cached polynomials. In this case, 
	// the preprocessing can be much faster. This can only be used
	// when lookup tables are public.
	let b_fast_mode = true;
	let b_read_cache = false;
	let b_write_cache = true;
	let n_selectors = 3;
	let selector_blinders = (0..(n_selectors*blinding_factors))
			.map(|_| Fr::random(OsRng)).collect::<Vec<Fr>>();
	let trapdoor = default_trapdoor::<Bn256>();  //used for "fast mode"
	let (params, params_cq) = if b_read_cache{//read from cache
		let mut timer = Timer::new();
		let params = ParamsKZG::<Bn256>::read(&mut File::open("target/cache/kzg.dat").unwrap() ).expect("reading ParamsKZG failed!");
		let params_cq = ParamsKzgCq::<Bn256>::read("target/cache/params_cq").expect("reading ParamsKzgCQ failed");
		if b_perf{log_perf(LOG1, "-- read params_cq", &mut timer);}
		(params, params_cq)
	}else{//write cache
		if !b_fast_mode {
			ParamsKzgCq::<Bn256>
				::setup(k as u32, LOOKUP_TABLE_SIZE, 
				column_size, OsRng, blinding_factors) 
				//params_cq has same trapdoor with params
		}else{
			ParamsKzgCq::<Bn256>::setup_with_trapdoor(k as u32, 
				LOOKUP_TABLE_SIZE, column_size, blinding_factors, &trapdoor) 
		}
	};
	if b_write_cache{
		let mut timer = Timer::new();
		let mut w1 = File::create("target/cache/kzg.dat").unwrap();
		params.write(&mut w1).unwrap();
		if b_perf{log_perf(LOG1, "-- write kzg_params", &mut timer);}
		params_cq.write("target/cache/params_cq").unwrap();
		if b_perf{log_perf(LOG1, "-- write params_cq", &mut timer);}

	}
		//REMOVE LATER ---------
		let params = ParamsKZG::<Bn256>::read(&mut File::open("target/cache/kzg.dat").unwrap() ).expect("reading ParamsKZG failed!");
		let params_cq = ParamsKzgCq::<Bn256>::read("target/cache/params_cq").expect("reading ParamsKzgCQ failed");
		println!("DEBUG USE 999: return the read out samples");
		//REMOVE LATER --------- ABOVE

	let cq_vkey = params_cq.vkey.clone();
    let compress_selectors = true;
	if b_perf{log_perf(LOG1, "** Generating KZG and CQ Params", &mut timer);}


	//3. Preprocesssing for CQ
    let vk = keygen_vk_custom_cq(&params, &circuit, compress_selectors,
		Some(&selector_blinders)).expect("vk should not fail");
	let map_cq_aux:HashMap<usize,CqAux<Bn256>> = if !b_fast_mode{
		vk.cs().preprocess_cq(&params_cq)
	}else{
		vk.cs().preprocess_cq_with_trapdoor(&params_cq, trapdoor.s)
	};
	let mut map_cq_aux_ver: HashMap<usize, CqAuxVer<Bn256>> = HashMap::new();
	for (k,v) in map_cq_aux.iter(){
		map_cq_aux_ver.insert(*k, v.to_cq_aux_ver());
	}
    let pk = keygen_pk_cq(&params, vk, &circuit, Some(&selector_blinders))
		.expect("pk should not fail");


	//4. Generate and Verify Proof
    let instances: &[&[Fr]] = &[&[Fr::from(0)]];
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
	let cq_prover= CqProverSchemeKzg::<Bn256, Challenge255<G1Affine>, Blake2bWrite<Vec<u8>,G1Affine,Challenge255<_>>>::new(params_cq, map_cq_aux);
	let cq_ver= CqVerifierSchemeKzg::<Bn256, Challenge255<G1Affine>, Blake2bRead<_,_,Challenge255<_>>>::new(cq_vkey, map_cq_aux_ver);
    create_proof_cq::<
        KZGCommitmentScheme<Bn256>,
        ProverGWC<'_, Bn256>,
        Challenge255<G1Affine>,
        _,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<_>>,
        _,
		_
    >(
        &params,
        &pk,
        &[circuit],
        &[instances],
        OsRng,
        &mut transcript,
		&Some(cq_prover), //additional parameter compared with create_proof
    )
    .expect("prover should not fail");
    let proof = transcript.finalize();
	let vb_proof = proof.bytes();


    let strategy = SingleStrategy::new(&params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    assert!(verify_proof_cq::<
        KZGCommitmentScheme<Bn256>,
        VerifierGWC<'_, Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<'_, Bn256>,
		_
    >(
        &params,
        pk.get_vk(),
        strategy,
        &[instances],
        &mut transcript,
		Some(cq_ver), //additional parameter compared with verify_proof
    )
    .is_ok());
	println!("k: {}, PROOF size: {}", k, vb_proof.count());
}
