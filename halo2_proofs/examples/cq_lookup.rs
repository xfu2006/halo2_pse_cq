/// It is cost saving to merge multiple tables into one big cq-lookup table.
/// This example shows how to use cq-folding to perform (vectored) lookup.
/// The cq-table is actually a contenation of two tables: 
/// table 1: (4 even numbers) and table 2: (4 prime numbers)
/// TABLE1_TBL_ID           TABLE2_TBL_VALUE
/// 0                       0                //DUMMY entry for unselected
/// 1                       100
/// 1                       200
/// 1                       600
/// 1                       800
/// 2                       17
/// 2                       19
/// 2                       97
/// * rest are padded with (2, 97) to the given size
///
/// This sample also retains the 128-bit lookup argument in the
/// examples/proof-size as an example for comparing the syntax
/// difference between cq_lookup and halo2(plookup based).


use ff::Field;
use std::io::Read;
use std::collections::HashMap;
use halo2_proofs::dev::MockProver;
//use halo2_proofs::{
 //   circuit::{Layouter, SimpleFloorPlanner, Value},
   // plonk::{Advice, Circuit, Column, ConstraintSystem, ErrorFront},
//};
//use halo2curves::pasta::Fp;

//use halo2_proofs::plonk::{Expression, Selector, TableColumn,CqTableColumn};
//use halo2_proofs::poly::Rotation;
use halo2_backend::plonk::{cq_lookup::{
		batch_kzg::ParamsKzgCq,
		zk_qanizk_cq::{CqAux,CqAuxVer},
		prover::CqProverSchemeKzg,
		verifier::{CqVerifierSchemeKzg}
	},
	verifier::verify_proof_cq
};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        //create_proof, 
		create_proof_cq, keygen_pk_cq, keygen_vk_custom_cq,
		Advice, Circuit, Column,
        ConstraintSystem, ErrorFront,
		//Fixed, Instance,
		TableColumn, CqTableColumn, Selector, Expression, Instance,
    },
    poly::{
        kzg::{
            commitment::{KZGCommitmentScheme}, // ParamsKZG},
            multiopen::{ProverGWC, VerifierGWC},
            strategy::SingleStrategy,
        },
        Rotation,
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer 
    },
    //SerdeFormat,
};
use halo2curves::bn256::{Bn256, Fr, G1Affine};
//use halo2curves::{grumpkin};
//use halo2_proofs::plonk::{Expression, Selector, TableColumn};
use rand_core::OsRng;
use halo2_backend::plonk::cq_lookup::zk_qanizk_cq::gen_hash_idx_for_tables;

//macros for CqTableColumns (these correspond to the unique ID of externally
//stored tables, values and their commitments in cq_cached/ folder
pub const CQ_TABLE1_TBLID: usize = 101;
pub const CQ_TABLE2_VAL: usize = 102;
pub const LOOKUP_TABLE_SIZE: usize = 1usize<<8;

// We use a lookup example
#[allow(dead_code)]
#[derive(Clone, Copy)]
struct TestCircuit <F:Field>{
	a: F
}

#[derive(Debug, Clone)]
struct MyConfig {
    selector: Selector,
    table: TableColumn,
    instance: Column<Instance>,
    advice: Column<Advice>,

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

        meta.lookup("lookup", |meta| {
            let selector = meta.query_selector(config.selector);
            let not_selector = Expression::Constant(Fr::ONE) - selector.clone();
            let advice = meta.query_advice(config.advice, Rotation::cur());
            vec![(selector * advice + not_selector, config.table)]
        });

        let cqarg_id = meta.cq_lookup("cq_lookup", |meta| {
            let selector = meta.query_selector(config.cq_selector);
            let subtable_id = meta.query_advice(config.subtable_id, 
					Rotation::cur());
            let subtable_val = meta.query_advice(config.subtable_val, 
					Rotation::cur());
            vec![
				(selector.clone() * subtable_id , config.cq_table1),
				(selector * subtable_val, config.cq_table2),
			]
        });

		// This is the cq's equivalent to layouter.assign_table().
		// Since cq_tables are fixed, we load it in config (instead of layouter)
		// when b_reset_cache is false, and when cache exists for a 
		// CqTableColumn, it's loaded from cache/ folder
		// The table column data is saved in the ConstraintSystem
		// to improve: the vkey constains ConstraintSystem (later
		// should cut the data part for vkey and retain the data for pkey) 
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
						// will throw error at row 23.
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

const K: u32 = 9;

fn main() {
    let k = 9; 
	let column_size = 1<<k; //size of each column of halo2
    let circuit = TestCircuit { a: Fr::from(0) };
	// blinding_factors: the blinding factors at each halo2 column
	// when cq_prover is called, we'll verify this value
	let blinding_factors = 6; 

    let public_inputs  = vec![Fr::from(0)];
    let prover = MockProver::run(K, &circuit, vec![public_inputs.clone()]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

	// params_cq needs to be generated at the same time with params
	// as they share the same trapdoor of kzg key.
	let n_selectors = 3;
	let selector_blinders = (0..(n_selectors*blinding_factors))
			.map(|_| Fr::random(OsRng)).collect::<Vec<Fr>>();
	let (params, params_cq) = ParamsKzgCq::<Bn256>::setup(k as u32, LOOKUP_TABLE_SIZE, column_size, OsRng, blinding_factors);
	let cq_vkey = params_cq.vkey.clone();
    let compress_selectors = true;
    let vk = keygen_vk_custom_cq(&params, &circuit, compress_selectors,
		Some(&selector_blinders)).expect("vk should not fail");
	let map_cq_aux:HashMap<usize,CqAux<Bn256>> = 
		vk.cs().preprocess_cq(&params_cq);
	let mut map_cq_aux_ver: HashMap<usize, CqAuxVer<Bn256>> = HashMap::new();
	for (k,v) in map_cq_aux.iter(){
		map_cq_aux_ver.insert(*k, v.to_cq_aux_ver());
	}
    let pk = keygen_pk_cq(&params, vk, &circuit, Some(&selector_blinders))
		.expect("pk should not fail");

    let prover = MockProver::run(k.try_into().unwrap(), 
		&circuit, vec![vec![]]).unwrap();
    assert_eq!(prover.verify(), Ok(()));


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
		&Some(cq_prover),
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
		Some(cq_ver),
    )
    .is_ok());
	println!("k: {}, PROOF size: {}", k, vb_proof.count());

}