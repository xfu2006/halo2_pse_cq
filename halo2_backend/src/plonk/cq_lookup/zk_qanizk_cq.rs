/* This file is ported from the ZeroAsset (IZPR) project.
*/
extern crate rayon;
extern crate itertools;

use itertools::Itertools;
use self::rayon::prelude::*; 
use halo2curves::pairing::Engine;
use std::collections::HashMap;
use std::fs::File;
use crate::plonk::{
	cq_lookup::batch_kzg::{KzgProverKey,KzgVerifierKey,precompute_quotient_poly, precompute_lags, par_write_vec_adv, par_read_vec_adv, read_usize, par_write_hash, par_read_hash},
	SerdePrimeField,FromUniformBytes, SerdeFormat, SerdeCurveAffine,
};
use group::ff::{Field,PrimeField};
use group::{Curve,prime::PrimeCurveAffine};
//use std::sync::Arc;
use crate::plonk::cq_lookup::utils::{Timer,log_perf,LOG1};
use rand_core::OsRng;
use crate::plonk::cq_lookup::ft_poly_ops::{vmsm, hash, to_vecu8, to_vecu8_field, compute_coefs_of_lag_points,coefs_to_evals, eval_z_h_over_2n, evals_to_coefs, eval_coefs_at, get_root_of_unity, get_poly, mul, print_poly,eq_poly, div, minus, compute_powers};
use halo2curves::{serde::SerdeObject,CurveAffine};
use crate::plonk::cq_lookup::ft_poly_ops::closest_pow2;
use crate::arithmetic::parallelize;
use std::io;
use std::io::{Write};



/// Aux Information for CQ, AuxInfo and KzgProverKey comprise the
/// prover key for the CQ protocol. Note that when the Lookup (bigger)
/// table is SECRET, CqAux has to be computed using "slower" version
/// of group FFT. But if lookup table is PUBLIC, then trusted setup
/// can compute CqAux to speed up computation.
#[derive(Clone,Debug)]
pub struct CqAux<PE:Engine>{
	/// must be power of 2
	pub n: usize,
	/// commitment to t: Pedersen commitment to T(X) = \sum t_i L_i(X), over G2
	pub commit_t2: PE::G2Affine,
	/// r_t: the random nonce used in commit_t2
	pub r_t: PE::Fr,
	/// t_s_1: [T(s)]_1
	pub t_s_1: PE::G1Affine,
	/// array of quotient polynomials
	pub arr_q: Vec<PE::G1Affine>,
	/// loc_idx which maps each element to its idx
	pub map_idx: HashMap<Vec<u8>, usize>
}

impl <PE:Engine> CqAux<PE>
where
PE::G1Affine : SerdeCurveAffine,
PE::G2Affine : SerdeCurveAffine,
PE::Fr: SerdePrimeField + FromUniformBytes<64>{
	pub fn to_cq_aux_ver(&self) -> CqAuxVer<PE>{
		CqAuxVer{n: self.n, commit_t2: self.commit_t2}
	}

	pub fn par_write(&self, prefix: &str)->io::Result<()>{
		let fpath = format!("{}_{}", prefix, "main");
		let mut w = File::create(&fpath)?;
		w.write_all(&self.n.to_le_bytes())?;
		self.commit_t2.write(&mut w, SerdeFormat::RawBytes)?;
		self.r_t.write(&mut w, SerdeFormat::RawBytes)?;
		self.t_s_1.write(&mut w, SerdeFormat::RawBytes)?;

		par_write_vec_adv(&self.arr_q, &format!("{}_arrq", prefix))?;
		par_write_hash(&self.map_idx, &format!("{}_hsidx", prefix))?;

		Ok( () )
	}

	pub fn par_read(prefix: &str) -> io::Result<Self>{
		let b_perf = true;
		let fpath = format!("{}_{}", prefix, "main");
		let mut r = File::open(&fpath)?;
		let n =  read_usize(&mut r);
		let commit_t2 = PE::G2Affine::read_raw(&mut r)?;
		let r_t = PE::Fr::read_raw(&mut r)?;
		let t_s_1 = PE::G1Affine::read_raw(&mut r)?;
		let arr_q = par_read_vec_adv::<PE::G1Affine>(&format!("{}_arrq", prefix))?;
		let mut timer = Timer::new();
		let map_idx = par_read_hash(&format!("{}_hsidx", prefix))?;
		if b_perf{log_perf(LOG1, "---- establish map_idx", &mut timer);}

		Ok( Self{n, commit_t2, r_t, t_s_1, arr_q, map_idx} )

	}
}

/// write the hash map of cqaux to file
pub fn par_write_hash_cqaux<PE:Engine>(hs: &HashMap<usize, CqAux<PE>>, prefix: &str)-> io::Result<()> 
where
PE::G1Affine : SerdeCurveAffine,
PE::G2Affine : SerdeCurveAffine,
PE::Fr: SerdePrimeField + FromUniformBytes<64>
{
	//1. get vec keys
	let vec_keys = hs.keys().cloned().collect::<Vec<usize>>();
	let mut mainfile = File::create(&format!("{}_keys", prefix)).
		expect("create key file falis");
	mainfile.write_all(&vec_keys.len().to_le_bytes())
		.expect("write keylen fails");
	for k in &vec_keys {mainfile.write_all(&k.to_le_bytes()).expect(
		&format!("write key: {} fails", k));}

	//2. for each cq_aux write it one by one
	for k in &vec_keys{
		hs[&k].par_write(&format!("{}_cqaux_{}", prefix, k))
			.expect(&format!("write cq_aux: {} fails.", k));
	}
	Ok( () )
}

pub fn par_read_hash_cqaux<PE:Engine>(prefix: &str)->io::Result<HashMap<usize, CqAux<PE>>>
where
PE::G1Affine : SerdeCurveAffine,
PE::G2Affine : SerdeCurveAffine,
PE::Fr: SerdePrimeField + FromUniformBytes<64>
{

	let mut vec_keys = vec![];
	let mut mainfile = File::open(&format!("{}_keys", prefix)).
		expect("create key file falis");
	let n = read_usize(&mut mainfile);
	for _i in 0..n{
		vec_keys.push(read_usize(&mut mainfile));
	}

	let mut hs = HashMap::<usize, CqAux<PE>>::new();
	for k in vec_keys{
		let cq_aux = CqAux::<PE>::par_read(&format!("{}_cqaux_{}", prefix, k)).
			expect(&format!("read cqaux {} fails", k));
		hs.insert(k, cq_aux);
	}

	Ok( hs )
}

/// CqAux for the verifier
pub struct CqAuxVer<PE:Engine>{
	pub n: usize,
	pub commit_t2: PE::G2Affine
}


/// Proof for CQ (7 G1 + 2 F)
pub struct CqProof<PE:Engine>{
	/// Pedersen vector commitment to vector m
	pub commit_m: PE::G1Affine,
	/// Pedersen vector commitment to vector A
	pub commit_a: PE::G1Affine,
	/// Pedersen vector commitment to Q_A
	pub commit_qa: PE::G1Affine,
	/// Pedersen vector commit to B
	pub commit_b: PE::G1Affine,
	/// Pedersen vector commitment to Q_B
	pub commit_q_b: PE::G1Affine,
	/// Pedersen vector commitment to P(X) = (B(X) - B_gamma + \eta(D(X))/(X-gamma)
	pub commit_p: PE::G1Affine,
	/// qa-nizk proof
	pub prf_qa: PE::G1Affine,
	/// eval of b(X) at gamma
	pub b_gamma: PE::Fr,
	/// eval of z_V_n2raw(X) at gamma
	pub zv_gamma: PE::Fr,
}

/// generate the preprocessed information
/// given the lookup table, preprocess it, generate the aux information
/// to speed up proof, and the commitment to table.
/// NOTE THAT: compared with the original scheme, the
/// [L_i(s)] and [(L_i(s) - L_i(0)/s] are moved to KzgProverKey
/// because they are orthoganal to T.
pub fn preprocess_cq<PE:Engine>(
	pk: &KzgProverKey<PE>, 
	lookup_table: &Vec<PE::Fr>)-> CqAux<PE> 
	where <PE as Engine>::G2Affine: CurveAffine<ScalarExt=PE::Fr>,
	<PE as Engine>::G1Affine: CurveAffine<ScalarExt=PE::Fr>,
	{
	//1. compute the quotient polynomials
	let b_perf = true;
	let mut timer = Timer::new();
	if b_perf{println!("\n** preprocess cq");}
	let n = pk.n;

	let arr_q = precompute_quotient_poly(lookup_table, n, &pk.vec_g1);
	if b_perf{log_perf(LOG1, "-- quotient poly", &mut timer);}
	let map_idx:HashMap<Vec<u8>, usize> = lookup_table.par_iter().enumerate()
		.map(|(idx, v)| (v.to_repr().as_ref().to_vec(), idx))
		.collect();

	//2. compute the Commit_T = [T(s)]_1 + [r*z_V(s)]_1
	let (r_t, commit_t2, _commit_t_2_raw) = ped_commit(lookup_table, n, 
		&pk.lag_all_2, pk.zh_s2);
	let (_, _, t_s1) = ped_commit(lookup_table, n, 
		&pk.lag_all, pk.zh_s1);
	CqAux{n: n, commit_t2: commit_t2, r_t: r_t, arr_q: arr_q,
		map_idx: map_idx, t_s_1: t_s1}
}



/// this function DIRECTLY generates the commit_t given trapdoor s
/// It should be called by the TRUSTED SETUP (for case table T)
/// which T is passed to the trusted set up.
/// It is much faster than preprocess, however, then the system
/// have MORE dependence on the trusted setup (per-circuit then).
pub fn preprocess_cq_with_trapdoor<PE:Engine>(
	pk: &KzgProverKey<PE>, 
	lookup_table: &Vec<PE::Fr>, s: PE::Fr)-> CqAux<PE> 
	where <PE as Engine>::G2Affine: CurveAffine<ScalarExt=PE::Fr>,
	<PE as Engine>::G1Affine: CurveAffine<ScalarExt=PE::Fr>, {
	//1. set up
	let b_perf = true;
	let mut timer = Timer::new();
	if b_perf{println!("\n** preprocess cq with s");}
	let n = pk.n;

	//2. compute the value t(s) = sum t_i L_i(s)
	let lags_s = precompute_lags(n, s);
	assert!(lookup_table.len()==n, "lookup_table.len: {} !=n : {}",
		lookup_table.len(), n);
	let t_s: PE::Fr = (0..n).into_par_iter().map(|i|
		lags_s[i] * lookup_table[i]).sum();
	let r_t = PE::Fr::random(OsRng);
	let g2 = PE::G2Affine::generator();
	let g1 = PE::G1Affine::generator();
	let commit_t2 = ((g2 * t_s) + (pk.zh_s2*r_t)).to_affine();
	let t_s1 = (g1 * t_s).to_affine();
	if b_perf{log_perf(LOG1, "-- commit_t2 ", &mut timer);}

	//3. precompute the quotient poly
	let mut kzg_proofs = vec![PE::Fr::ZERO; n];
	let omega = get_root_of_unity::<PE::Fr>(n as u64);
	parallelize(&mut kzg_proofs, |sec, start|{
		let mut current_g = omega.pow_vartime([start as u64]);
		let mut i = 0;
		for g in sec.iter_mut() {
			*g = (t_s - lookup_table[start+i])*((s-current_g).invert().unwrap());
			current_g *= omega;
			i +=1;
		}
	});
	let arr_omega = compute_powers::<PE::Fr>(n, omega);
	let fe_n = PE::Fr::from(n as u64);
	let z_n_prime = arr_omega.into_par_iter().map(|x|
		fe_n*x.invert().unwrap()).collect::<Vec<PE::Fr>>();
	let arr_q = kzg_proofs.into_par_iter().zip(z_n_prime.into_par_iter())
		.map(|(x,y)| ((g1*x) * (y.invert().unwrap())).to_affine() )
		.collect::<Vec<PE::G1Affine>>();
	if b_perf{log_perf(LOG1, "-- quotient poly (quick) ", &mut timer);}

	let map_idx:HashMap<Vec<u8>, usize> = lookup_table.par_iter().enumerate()
		.map(|(idx, v)| (v.to_repr().as_ref().to_vec(), idx))
		.collect();
	if b_perf{log_perf(LOG1, "-- bulid map_idx", &mut timer);}


	CqAux{n: n, commit_t2: commit_t2, r_t: r_t, arr_q: arr_q,
		map_idx: map_idx, t_s_1: t_s1}
}

/// generate a proof that query_table is contained in lookup table
/// returns the proof that query_table \subset lookup_table
/// and the random opening for generarating and commit_query_table
/// i.e., (proof, r_query_table, commit_query_table).
/// vec_vkey: used for hash of vkey for random oracle.
pub fn prove_cq<PE:Engine>(
	pk: &KzgProverKey<PE>, 
	aux: &CqAux<PE>, 
	lookup_table: &Vec<PE::Fr>,
	query_table: &Vec<PE::Fr>,
	vec_vkey: &Vec<u8>,
	) -> (CqProof<PE>, PE::Fr, PE::G1Affine) 
	where <PE as Engine>::G2Affine: CurveAffine<ScalarExt=PE::Fr>,
	<PE as Engine>::G1Affine: CurveAffine<ScalarExt=PE::Fr>{
	prove_cq_adv::<PE>(pk, aux, lookup_table, query_table, vec_vkey, PE::Fr::ZERO)
}

/// if r_query is zero, set a new random, otherwise use it as
/// r_query_table, blinding_factors means the LAST "blinding_factors" entries
/// in the query_table are NOT used (this is used to accomodate
/// halo2 for the blinding entries).
pub fn prove_cq_adv<PE:Engine>(
	pk: &KzgProverKey<PE>, 
	aux: &CqAux<PE>, 
	lookup_table: &Vec<PE::Fr>,
	query_table: &Vec<PE::Fr>,
	vec_vkey: &Vec<u8>,
	r_query_input: PE::Fr,
	) 
	-> (CqProof<PE>, PE::Fr, PE::G1Affine) 
	where <PE as Engine>::G2Affine: CurveAffine<ScalarExt=PE::Fr>,
	<PE as Engine>::G1Affine: CurveAffine<ScalarExt=PE::Fr>
{ 
	//1. check input
	let b_perf = true;
	let b_test = false;
	let mut timer = Timer::new();
	let n2_raw = query_table.len();
	let n2 = closest_pow2(n2_raw); 

	//2. compute commit_query, commit_m
	let rng = OsRng;
	let r_query = if r_query_input==PE::Fr::ZERO {
		PE::Fr::random(rng)} else {r_query_input};

	let (commit_query, _) = ped_commit_with_random(
		&query_table, r_query, n2_raw, &pk.lag_all_n2, pk.zv_s1);
	if b_perf {log_perf(LOG1, "-- commit_query_table ", &mut timer);}
	let (idx_m, vec_m) = gen_m::<PE>(&aux.map_idx, &query_table, pk.blinding_factors);

	if b_perf {log_perf(LOG1, "-- gen_m", &mut timer);}
	let (r_m, commit_m, _) = sparse_ped_commit(&vec_m, &idx_m, 
		&pk.lag_all, pk.zh_s1);
	if b_perf {log_perf(LOG1, "-- commit_m v2", &mut timer);}


	//3. compute beta
	let mut v1 = vec_vkey.clone();
	let mut v2 = to_vecu8(&vec![commit_query, commit_m]);
	v1.append(&mut v2);
	let beta = hash::<PE::Fr>(&v1);


	//4. compute A_i and commit_a
	let idx_a = idx_m.clone();
	let one = PE::Fr::ONE;
	let vec_a = vec_m.par_iter().zip(idx_m.par_iter())
		.map(|(m,idx)| *m*((lookup_table[*idx] + beta).invert().unwrap())).
		collect::<Vec<PE::Fr>>();
	let (r_a, commit_a, a_s) = sparse_ped_commit(&vec_a, &idx_a, 
		&pk.lag_all, pk.zh_s1);
	if b_perf {log_perf(LOG1, "-- commit_a", &mut timer);}


	//5. compute commit_qa
	let g1 = PE::G1Affine::generator();
	let (_, _, qa_s) = sparse_ped_commit(&vec_a, &idx_a, &aux.arr_q, pk.zh_s1);
	let commit_qa = qa_s + (aux.t_s_1 *r_a).to_affine() 
		+ (a_s * aux.r_t).to_affine()
		+ (pk.zh_s1 * (aux.r_t * r_a)).to_affine()
		+ (g1 * (r_a * beta - r_m)).to_affine();
	if b_perf {log_perf(LOG1, "-- commit_qa", &mut timer);}

	//6. comptue b, p and qb
	let vec_b = query_table.par_iter().map(|t_i| one*((*t_i + beta).invert().unwrap())).  collect::<Vec<PE::Fr>>();
	let (r_b, commit_b, _) = ped_commit(&vec_b, n2_raw, 
		&pk.lag_all_n2, pk.zv_s1); 
	if b_perf {log_perf(LOG1, "-- commit_b", &mut timer);}


	let (coef_q_b, coef_b, coef_t) = compute_coeff_q_b(&vec_b,r_b,query_table,
		r_query,beta,n2, &pk.coefs_vanish_n2_raw, pk.blinding_factors, n2_raw);
	let commit_q_b = vmsm(&pk.vec_g1, &coef_q_b);
	if b_perf {log_perf(LOG1, "-- compute q_b", &mut timer);}



	//7. gamma and eta
	let mut v1 = to_vecu8(&vec![commit_a, commit_qa.into(), commit_b, 
		commit_q_b]);
	let mut v2 = to_vecu8_field(&vec![beta]);
	v1.append(&mut v2);
	let gamma = hash::<PE::Fr>(&v1);
	let eta = hash::<PE::Fr>(&to_vecu8_field(&vec![gamma]));


	//8. compute b_gamma, D(X) and P(X)
	let b_gamma = eval_coefs_at(&coef_b, gamma); 
	let zv_gamma = eval_coefs_at(&pk.coefs_vanish_n2_raw, gamma); 

	let part1 = minus(&get_poly(coef_b) , &get_poly(vec![b_gamma]));
	let mut coef_t2:Vec<PE::Fr> = coef_t.into_par_iter().
		map(|x| x*b_gamma*eta).collect();
	coef_t2[0] += beta*eta*b_gamma - PE::Fr::from(1u64)*eta;
	let coef_q_b2:Vec<PE::Fr> = coef_q_b.into_par_iter()
		.map(|x| x*zv_gamma*eta).collect();


	let mut coef_zn:Vec<PE::Fr> = (&pk.coefs_vanish_n2_raw).into_par_iter().
		map(|x| (*x)*eta*eta).collect();
	coef_zn[0] = coef_zn[0] - eta*eta*zv_gamma;
	let p_x_part1 = part1 + 
			&minus(&get_poly(coef_t2) , &get_poly(coef_q_b2)) + 
			&get_poly(coef_zn);
	let p_x_part2 = get_poly(vec![PE::Fr::ZERO - gamma, PE::Fr::ONE]);
	let p_x  = div(&p_x_part1, &p_x_part2);
	if b_test{
		let q_x = mul(&p_x, &p_x_part2);
		assert!(eq_poly(&p_x_part1, &q_x), "failed on p_x = div(p_x_part1)");
	}
	let commit_p = vmsm(&pk.vec_g1, &p_x.values); 
	if b_perf {log_perf(LOG1, "-- compute and commit p(X)", &mut timer);}


	//9. qa_nizk proof
	let part1 = sparse_ped_commit2(&vec_a, r_a, &idx_a, 
		&pk.qa_p, pk.qa_p[pk.n]);
	let part2 = vmsm(&pk.qa_p[pk.n+1..], &vec_b) + 
		(pk.qa_p[pk.n+1+n2_raw]*r_b).into();
	let prf_qa = part1 + part2.into();
	if b_perf {log_perf(LOG1, "-- compute prf_qanizk", &mut timer);}

	let prf = CqProof{commit_m: commit_m, commit_a: commit_a,
		commit_qa: commit_qa.into(), 
		commit_b: commit_b, commit_p: commit_p,
		commit_q_b: commit_q_b,
		prf_qa: prf_qa.into(), b_gamma: b_gamma, zv_gamma: zv_gamma};


	//return 
	(prf, r_query, commit_query)
} 


/// verify the proof
pub fn verify_cq<PE:Engine>(
	vk: &KzgVerifierKey<PE>,
	commit_lookup_table: PE::G2Affine, 
	commit_query_table: PE::G1Affine,
	prf: &CqProof<PE>)-> bool{
	//1. compute beta
	let b_perf = false;
	let mut timer = Timer::new();
	let mut v1 = vk.to_bytes();
	let mut v2 = to_vecu8(&vec![commit_query_table, prf.commit_m]);
	v1.append(&mut v2);
	let beta = hash::<PE::Fr>(&v1);
	let mut v1 = to_vecu8(&vec![prf.commit_a, prf.commit_qa, prf.commit_b, 
		prf.commit_q_b]);
	let mut v2 = to_vecu8_field(&vec![beta]);
	v1.append(&mut v2);
	let gamma = hash::<PE::Fr>(&v1);
	let eta = hash::<PE::Fr>(&to_vecu8_field(&vec![gamma])); 
	let mu = hash::<PE::Fr>(&to_vecu8_field(&vec![eta])); 
	if b_perf {log_perf(LOG1, "-- verify ROM hashes", &mut timer);}

	//2. verify equation equation (1) and (3) in batch using \mu
	let g1 = PE::G1Affine::generator();
	let g2 = PE::G2Affine::generator();
	let lhs1 = prf.commit_b.to_curve() - (g1*prf.b_gamma)
		+ commit_query_table*(eta * prf.b_gamma)+
		g1*(eta * beta *prf.b_gamma - eta) -
		prf.commit_q_b*(prf.zv_gamma*eta) + 
		prf.commit_m*mu - 
		prf.commit_a*(mu*beta) +
		vk.zv_s1_raw*(eta*eta) - 
		g1*(prf.zv_gamma*eta*eta);
	let eq1_lhs = PE::pairing(&lhs1.into(), &vk.g2)
		+ PE::pairing(&((prf.commit_qa*mu).to_affine()), &vk.zh_s2);	
	let s_gamma = vk.s2.to_curve() - g2*gamma;
	let eq1_rhs = PE::pairing(&prf.commit_p, &s_gamma.to_affine()) +
		PE::pairing(&(prf.commit_a*mu).to_affine(), &commit_lookup_table);


	if eq1_lhs!=eq1_rhs{return false;}
	if b_perf {log_perf(LOG1, "-- verify eq1 & eq3 batched. ", &mut timer);}


	//3. verify equation 2
	let lhs2 = PE::pairing(&prf.prf_qa, &vk.qa_a);
	let rhs2 = PE::pairing(&prf.commit_a, &vk.qa_d[0]) +
			PE::pairing(&prf.commit_b, &vk.qa_d[1]);
	if lhs2!=rhs2 {return false;}
	if b_perf {log_perf(LOG1, "-- verify eq2", &mut timer);}


	return true;
}

/// sum a vector
fn sum<G: CurveAffine>(v: &Vec<G>)->G{
	let mut g1 = v[0].to_curve();
	for i in 1..v.len(){
		g1 = g1 + v[i];
	}
	g1.to_affine()
}

/// generate a hash table which maps a vector of entries to their idx.
/// require arr_lookup_table each subvector size be the same.
pub fn gen_hash_idx_for_tables<F:PrimeField>(arr_lookup_table:&Vec<Vec<F>>)
	-> HashMap<Vec<u8>, usize>{
	let b_perf = false;
	let mut timer = Timer::new();

	let mut map = HashMap::<Vec<u8>, usize>::new();
	let n = arr_lookup_table[0].len();
	let m = arr_lookup_table.len();
	for tbl in arr_lookup_table {assert!(tbl.len()==n, "lkup tbl size neq!");}
	for i in 0..n{
		let mut v = vec![];
		for j in 0..m{ v.push(arr_lookup_table[j][i]); }
		let bs = to_vecu8_field(&v);
		map.insert(bs, i);
	}
	if b_perf {log_perf(LOG1, &format!("-- gen_hash_idx size: {}", arr_lookup_table[0].len()), &mut timer);}

	map
}
/// generate a proof for 
/// \sum_i=0^k \alpha^i*query_table[i]
/// in \sum_i=0^k alpha^i*lookup_table[i]
/// return (proof, array of nonces used, array of commitments of query table).
/// blinding_factors: the number of not used entries in the end of the query_table.
/// r_querys are the array of randoms (1 for each query table) for computing
/// commit_query. Note when the "alpha" is applied, the highest item
/// alpha^{k-1} is applied to the first query table, and arra^{0} is applied
/// to the last
pub fn fold_prove_cq<PE:Engine>(
	pk: &KzgProverKey<PE>, 
	arr_aux: &Vec<&CqAux<PE>>, 
	arr_lookup_table: &Vec<Vec<PE::Fr>>,
	arr_query_table: &Vec<Vec<PE::Fr>>,
	vec_vkey: &Vec<u8>,
	alpha: PE::Fr,
	hash_idx: &HashMap<Vec<u8>, usize>,
	r_querys_inp: &Vec<PE::Fr>) 
	-> (CqProof<PE>, Vec<PE::Fr>, Vec<PE::G1Affine>)  
	where <PE as Engine>::G2Affine: CurveAffine<ScalarExt=PE::Fr>,
	<PE as Engine>::G1Affine: CurveAffine<ScalarExt=PE::Fr>{
	//1. check input
	let (b_perf, b_test) = (true, true);
	let mut timer = Timer::new();
	let k = arr_query_table.len(); //number of instances of folding
	let n2_raw = arr_query_table[0].len();
	assert!(pk.n2_raw ==n2_raw, "pk.n2_raw: {} != n2_raw: {}", pk.n2_raw, n2_raw);

	let n2 = closest_pow2(n2_raw);
	assert!(n2.is_power_of_two(), "query table size is not power of 2");
	for i in 0..arr_query_table.len() {
		assert!(arr_query_table[i].len()==n2_raw, "len of query_table[{}]!=n2_raw", i);
		assert!(arr_lookup_table[i].len()==arr_lookup_table[0].len(),
			"lookup table {} len != 1st lookup", i);
	}
	if b_perf {println!("-------- fold prove --------");}

	//2. compute commit_query, commit_m
	let vec_3m = (0..k).into_par_iter().map(|i|
		ped_commit_with_random(&arr_query_table[i], r_querys_inp[i], n2_raw, 
			&pk.lag_all_n2, pk.zv_s1)).collect::<Vec<(_,_)>>();
	let commit_query: PE::G1Affine= sum(&
		vec_3m.clone().into_par_iter().zip((0..k).into_par_iter())
		.map(|((c,_),i)| (c*alpha.pow(&[(k-1-i) as u64])).to_affine())
		.collect::<_>());
	let commit_querys = 
		vec_3m.clone().into_par_iter().zip((0..k).into_par_iter())
		.map(|((c,_),_i)| c).collect::<Vec<PE::G1Affine>>();
	let (idx_m, vec_m) = gen_m_tables::<PE>(
		hash_idx, &arr_query_table, pk.blinding_factors);
	let (r_m, commit_m, _) = sparse_ped_commit(&vec_m, &idx_m, 
		&pk.lag_all, pk.zh_s1);
	if b_perf {log_perf(LOG1, "-------- commit_m", &mut timer);}

	//3. compute beta
	let mut v1 = vec_vkey.clone();
	let mut v2 = to_vecu8(&vec![commit_query, commit_m]);
	v1.append(&mut v2);
	let beta = hash::<PE::Fr>(&v1);
	//let beta = hash::<PE::Fr>(&to_vecu8(&vec![commit_query, commit_m]));

	//4. compute A_i and commit_a
	let idx_a = idx_m.clone();
	let one = PE::Fr::ONE;
	let vec_a = vec_m.par_iter().zip(idx_m.par_iter())
		.map(|(m,idx)| *m* (beta + 
			(0..k).into_iter().map(|x| 
			arr_lookup_table[x][*idx] * alpha.pow(&[(k-1-x) as u64]))
			.sum::<PE::Fr>()
		).invert().unwrap()).
		collect::<Vec<PE::Fr>>();
	let (r_a, commit_a, a_s) = sparse_ped_commit(&vec_a, &idx_a, 
		&pk.lag_all, pk.zh_s1);
	if b_perf {log_perf(LOG1, "-------- commit_a", &mut timer);}

	let g1 = PE::G1Affine::generator();
	let arr_alpha:Vec<PE::Fr> = 
		compute_powers(k, alpha).into_iter().rev().collect();
	let arr_q: Vec<PE::G1Affine> = 
		(0..idx_a.len()).into_par_iter().map(|i|
			sum(&((0..k).into_iter().map(|idx|
				(arr_aux[idx].arr_q[idx_a[i]]*arr_alpha[idx])
					.to_affine()).collect::<Vec<PE::G1Affine>>()))
			).collect();
	assert!(arr_q.len()==idx_a.len(), "arr_q.len!=idx_a.len");

	//let (_, _, qa_s) = sparse_ped_commit(&vec_a, &idx_a, &arr_q, pk.zv_s1);
	let (_, _, qa_s) = ped_commit(&vec_a, vec_a.len(), &arr_q, pk.zh_s1);
	let t_s_1:PE::G1Affine = sum(&((0..k).into_par_iter().map(|idx|
		(arr_aux[idx].t_s_1 * (alpha.pow(&[(k-1-idx) as u64]))).to_affine())
		.collect::<Vec<PE::G1Affine>>()));
	let r_t: PE::Fr = (0..k).into_par_iter().map(|idx|
		arr_aux[idx].r_t * alpha.pow(&[(k-1-idx) as u64]))
		.sum();	
	let commit_qa = qa_s.to_curve() + t_s_1*r_a
		+ a_s*r_t
		+ pk.zh_s1*(r_t * r_a)
		+ g1*(r_a * beta - r_m);
	let commit_qa = commit_qa.to_affine();
	if b_perf {log_perf(LOG1, "-------- commit_qa", &mut timer);}


	//6. comptue b, p and qb
	let query_table = (0..n2_raw).into_par_iter().map(|idx|
		(0..k).into_iter().map(|x|
			arr_query_table[x][idx]*alpha.pow(&[(k-1-x) as u64])).sum()).
			collect::<Vec<PE::Fr>>();
	let vec_b = (0..n2_raw).into_par_iter().map(|idx|
		one*(query_table[idx] + beta).invert().unwrap()).
		collect::<Vec<PE::Fr>>();
	let r_query:PE::Fr = (0..k).into_iter().map(|x|
		r_querys_inp[x] * alpha.pow(&[(k-1-x) as u64])).sum();
	let (r_b, commit_b, _)=ped_commit(&vec_b, n2_raw, 
		&pk.lag_all_n2, pk.zv_s1); 
	if b_perf {log_perf(LOG1, "---------- commit_b", &mut timer);}

	let (coef_q_b, coef_b, coef_t) = compute_coeff_q_b(&vec_b,r_b,&query_table,
		r_query,beta,n2, &pk.coefs_vanish_n2_raw, pk.blinding_factors, n2_raw);
	if b_perf {log_perf(LOG1, "---------- compute q_b", &mut timer);}
	let commit_q_b = vmsm(&pk.vec_g1, &coef_q_b);

	//7. gamma and eta
	let mut v1 = to_vecu8(&vec![commit_a, commit_qa, commit_b, 
		commit_q_b]);
	let mut v2 = to_vecu8_field(&vec![beta]);
	v1.append(&mut v2);
	let gamma = hash::<PE::Fr>(&v1);
	let eta = hash::<PE::Fr>(&to_vecu8_field(&vec![gamma]));

	//8. compute b_gamma, D(X) and P(X)
	let b_gamma = eval_coefs_at(&coef_b, gamma); 
	let zv_gamma = eval_coefs_at(&pk.coefs_vanish_n2_raw, gamma); 

	let part1 = minus(&get_poly(coef_b) , &get_poly(vec![b_gamma]));
	let mut coef_t2:Vec<PE::Fr> = coef_t.into_par_iter().
		map(|x| x*b_gamma*eta).collect();
	coef_t2[0] += beta*eta*b_gamma - PE::Fr::from(1u64)*eta;
	let coef_q_b2:Vec<PE::Fr> = coef_q_b.into_par_iter()
		.map(|x| x*zv_gamma*eta).collect();
	let mut coef_zn:Vec<PE::Fr> = (&pk.coefs_vanish_n2_raw).into_par_iter().
		map(|x| (*x)*eta*eta).collect();
	coef_zn[0] = coef_zn[0] - eta*eta*zv_gamma;
	let p_x_part1 = (part1 + 
		&minus(&get_poly(coef_t2) , &get_poly(coef_q_b2))) + &get_poly(coef_zn);
	let p_x_part2 = get_poly(vec![PE::Fr::ZERO - gamma, PE::Fr::ONE]);
	let p_x = div(&p_x_part1, &p_x_part2);
	if b_test{
		let prod = mul(&p_x, &p_x_part2);
		assert!(eq_poly(&prod, &p_x_part1), "ERROR on div!");
	}
	let commit_p = vmsm(&pk.vec_g1, &p_x.values); 
	if b_perf {log_perf(LOG1, "-- compute and commit p(X)", &mut timer);}

	//9. qa_nizk proof
	let part1 = sparse_ped_commit2(&vec_a, r_a, &idx_a, 
		&pk.qa_p, pk.qa_p[pk.n]);
	let part2 = vmsm(&pk.qa_p[pk.n+1..], &vec_b) + 
		((pk.qa_p[pk.n+1+n2_raw]*r_b)).into();
	let prf_qa = (part1 + part2.into()).to_affine();
	if b_perf {log_perf(LOG1, "-- compute prf_qanizk", &mut timer);}


	(CqProof{commit_m: commit_m, commit_a: commit_a,
		commit_qa: commit_qa, commit_b: commit_b, commit_p: commit_p,
		commit_q_b: commit_q_b,
		prf_qa: prf_qa, b_gamma: b_gamma, zv_gamma: zv_gamma},
	r_querys_inp.clone(), commit_querys)
} 

// -----------------------------------------------------------
// endregion: Zero Knowledge CQ Protocol
// -----------------------------------------------------------

// -----------------------------------------------------------
// region: utility functions and data structures
// -----------------------------------------------------------
/// return a seed based on current time
pub fn gen_seed() -> u128{
	return 123098123123123u128; //to be improved later
}

/// compute the Pedersen commitment for t 
/// Define T(X) = \sum_{i=1}^n t_i L_i(X)
/// Commit_t = [T(s)] + r [z_V(s)]
/// vec_lag are the vector of [L_i(s)]
/// zvs is [z_V(s)] where z_V(X) is the vanishing polys of all roots of unity
/// n is a power of 2
/// the function returns (random_opening r, commit_t, [t(s)])
pub fn ped_commit<F: Field, G:CurveAffine<ScalarExt=F>>(
	t: &Vec<G::ScalarExt>, 
	n: usize, 
	vec_lag: &Vec<G>,
	zvs: G)->(G::Scalar, G, G){
	//1. generate random opening r
	//assert!(n.is_power_of_two(), "n is not power of 2");
	//assert!(n==vec_lag.len(), "n!=vec_lag.len()");
	assert!(n>=t.len(), "n<t.len()");
	let rng = OsRng;
	let r = G::Scalar::random(rng);
	let comp2 = zvs * r;

	//2. compute the variable multiscalar mul
	let comp1 = vmsm(vec_lag, t); 
	(r, (comp1 + comp2.into()).into(), comp1)
}

/// supply the random opening
/// return (commitment, commitment_without_random)
pub fn ped_commit_with_random<F: Field, G:CurveAffine<ScalarExt=F>>(
	t: &Vec<G::ScalarExt>, 
	r: G::ScalarExt,
	n: usize, 
	vec_lag: &Vec<G>,
	zvs: G)->(G, G){
	//1. generate random opening r
	assert!(n>=t.len(), "n<t.len()");
	let comp2 = zvs*r;

	//2. compute the variable multiscalar mul
	let comp1 = vmsm(vec_lag, t); 
	((comp1 + comp2.into()).into(), comp1)
}

/// this deals with that the case is sparse
/// idx_arr indicates which elements of vec_lag to take	
/// this is to compute \sum_{i=1}^{idx_arr.len()} vec_lag[idx_arr[i]]^t[i]
/// Return (random_nonce, commit_t = [t(s)] + r*zvs, [t(s)])
pub fn sparse_ped_commit<F: Field, G:CurveAffine<ScalarExt=F>>(
	t: &Vec<G::ScalarExt>, 
	idx_arr: &Vec<usize>,
	vec_lag: &Vec<G>,
	zvs: G)->(G::ScalarExt, G, G){
	//1. generate random opening r
	let n = t.len();
	assert!(n==idx_arr.len(), "idx_arr.len != t.len");
	assert!(n<=vec_lag.len(), "n>vec_lag.len()");
	let rng = OsRng;
	let r = G::Scalar::random(rng);
	let comp2 = zvs * r;

	//2. collect the vector of group elements and exponents
	let arr_g = idx_arr.par_iter().map(|idx| vec_lag[*idx]).collect::<Vec<_>>();
	assert!(arr_g.len()==n, "arr_g.len()!=n");

	//3. compute the variable multiscalar mul
	let comp1 = vmsm(&arr_g, t); 
	(r, (comp1 + comp2.into()).into(), comp1)
}

/// this deals with that the case is sparse
/// idx_arr indicates which elements of vec_lag to take	
/// this is to compute \sum_{i=1}^{idx_arr.len()} vec_lag[idx_arr[i]]^t[i]
/// Return commit_t = [t(s)] + r*zvs, [t(s)])
pub fn sparse_ped_commit2<G:CurveAffine>(
	t: &Vec<G::ScalarExt>, 
	r: G::Scalar,
	idx_arr: &Vec<usize>,
	vec_lag: &Vec<G>,
	zvs: G)->G{
	//1. generate random opening r
	let comp2 = zvs*r;
	let n = t.len();

	//2. collect the vector of group elements and exponents
	let arr_g = idx_arr.par_iter().map(|idx| vec_lag[*idx]).collect::<Vec<_>>();
	assert!(arr_g.len()==n, "arr_g.len()!=n");

	//3. compute the variable multiscalar mul
	let comp1 = vmsm(&arr_g, t); 
	(comp1 + comp2.into()).into()
}

/// generate vector m such that m_i is the number of
/// It returns the compact form (idx_arr, compact_m)
/// where compact_m[i] is m[idx_arr[i]], i.e., it contains
/// all non-zero elements of m_i.
/// the lookup_loc_info maps a field element in lookup_table
/// to its location in lookup table
fn gen_m<PE:Engine>(lookup_loc_info: &HashMap<Vec<u8>,usize>, 
	query_table: &Vec<PE::Fr>, unused: usize)->(Vec<usize>,Vec<PE::Fr>){
	//1. build occurence hashmap
	let mut hashmap = HashMap::new(); //map loc_idx -> occurence
	for raw_v in &query_table[0..query_table.len()-unused]{
		let v = raw_v.to_repr().as_ref().to_vec();
		let loc_in_lookup = lookup_loc_info.get(&v).unwrap(); //crash if not 
		*hashmap.entry(loc_in_lookup).or_insert(0usize) += 1; 
	}

	//2. build the result
	let mut idx_arr = vec![];
	let mut occ_arr = vec![];
	for key in hashmap.keys().sorted(){
		idx_arr.push(**key);
		let occ = hashmap.get(key).unwrap();
		let focc = PE::Fr::from(*occ as u64);
		occ_arr.push(focc);
	}
	return (idx_arr, occ_arr);
}

/// gen_m for multiple table
fn gen_m_tables<PE:Engine>(lookup_loc_info: &HashMap<Vec<u8>,usize>, 
	arr_query_table: &Vec<Vec<PE::Fr>>, unused: usize)
	->(Vec<usize>,Vec<PE::Fr>){
	//1. build occurence hashmap
	let mut hashmap = HashMap::new(); //map loc_idx -> occurence
	let m = arr_query_table[0].len() - unused;
	for i in 0..m{
		let mut raw_v = vec![];
		for j in 0..arr_query_table.len(){ raw_v.push(arr_query_table[j][i]);}
		let v = to_vecu8_field(&raw_v);
		let loc_in_lookup = lookup_loc_info.get(&v).unwrap(); //crash if not 
		*hashmap.entry(loc_in_lookup).or_insert(0usize) += 1; 
	}

	//2. build the result
	let mut idx_arr = vec![];
	let mut occ_arr = vec![];
	for key in hashmap.keys().sorted(){
		idx_arr.push(**key);
		let occ = hashmap.get(key).unwrap();
		let focc = PE::Fr::from(*occ as u64);
		occ_arr.push(focc);
	}
	return (idx_arr, occ_arr);
}


/// extend the vector to the desired size with 0's elements
pub fn extend_vec_to_size<F:Field>(vec: &mut Vec<F>, target_size: usize){
	let n = vec.len();
	if n>=target_size {return;}
	let mut sec2 = vec![F::ZERO; target_size - n];
	vec.append(&mut sec2);
}

/// compute the co-efficients of the polynomial q_b so that
/// cap_b(X) (cap_t(X) + beta) - 1 = q_b(X) z_H(x)
/// where H is the domain of roots of unity of n
/// Analsyis: cap_b(X) (with r_b) is degree n (i.e., n+1 co-efficients).
/// samme are cap_t(X) with r_t. LHS is degree 2n. z_H(X) is degree n
/// we have q_b(X) degree n
/// Retirn (coefs_q_b, coefs_b, coefs_t)
/// NOTE: this version works for b.len()==n which is a power of 2 (allowing
/// fft)
fn compute_coeff_q_b_v1<F:PrimeField>(b: &Vec<F>, r_b: F, t: &Vec<F>, r_t: F, beta: F, n: usize)->(Vec<F>,Vec<F>, Vec<F>){
	assert!(n.is_power_of_two(), "n is not power of 2!");
	assert!(b.len()==n, "b.len!=n");
	let b_test = false;
	let b_perf = false;
	let mut timer = Timer::new();


	//1. compute values of b(X), t(X), z_H(X) over domain [0, 2n)
	// call to_coefs to convert (b, r_rb) and etc first
	let mut coef_b = compute_coefs_of_lag_points(&b, r_b);
	let mut coef_t = compute_coefs_of_lag_points(&t, r_t);
	extend_vec_to_size(&mut coef_b, 2*n);
	extend_vec_to_size(&mut coef_t, 2*n); 
	assert!(coef_b.len()==coef_t.len() && coef_b.len()==2*n, "coefs len nok!");
	if b_perf {log_perf(LOG1, "---- compute coefs b(X), t(X)", &mut timer);}

	//2. compute the corresponding values of q_b
	let rng = OsRng;
	let coset_shift = F::random(rng);
	let v_b = coefs_to_evals(&coef_b, coset_shift);
	let v_t = coefs_to_evals(&coef_t, coset_shift);
	let v_z_h = eval_z_h_over_2n::<F>(n, coset_shift);
	assert!(v_b.len()==n*2, "v_b.len() != 2n");
	assert!(v_t.len()==n*2, "v_t.len() != 2n");
	assert!(v_z_h.len()==n*2, "v_z_h.len() != 2n");
	let mut v_q_b = vec![F::ZERO; v_b.len()];
	let one = F::ONE;
	for i in 0..v_b.len(){
		v_q_b[i] = (v_b[i]*(v_t[i] + beta) - one)*(v_z_h[i].invert().unwrap());
	}
	let coefs_q_b = evals_to_coefs(&v_q_b, coset_shift); 
	let coefs_q_b = coefs_q_b[0..n+1].to_vec();
	if b_perf {log_perf(LOG1, "---- compute coefs q_b(X)", &mut timer);}
	
	//4. check q(b) degree <=n
	if b_test{
		for i in coefs_q_b.len()-1..0{
			if coefs_q_b[i]!=F::ZERO{
				assert!(i<=n, "coefs_q_b.degree(): {} > n: {}", i, n);
				break;
			}
		}
	}

	//5. UNIT testing by random sample
	if b_test{
		//let gamma = F::from(327324234u128);
		let gamma = get_root_of_unity::<F>(2*n as u64) * coset_shift;
		let v_b = eval_coefs_at(&coef_b, gamma);
		let v_t = eval_coefs_at(&coef_t, gamma);
		let v_z_h = gamma.pow(&[n as u64]) - one;
		let v_q_b = eval_coefs_at(&coefs_q_b, gamma);

		assert!(v_b * (v_t + beta) - one == v_q_b * v_z_h, 
			"compute_q_b validation failed!");
	}

	(coefs_q_b, coef_b, coef_t)
}

/// compute the co-efficients of the polynomial q_b so that
/// cap_b(X) (cap_t(X) + beta) - 1 = q_b(X) z_H_n_raw(x).
/// n2_raw represents the real effective items in b.len() 
/// which is NOT NECESSARILY a power of 2.
/// blinding_factors: marks the blinding_factors entries in the end of the
/// query table.
fn compute_coeff_q_b_v2<F:PrimeField>(b: &Vec<F>, r_b: F, t: &Vec<F>, r_t: F, beta: F, n: usize, coef_vanish_n_raw: &Vec<F>, blinding_factors: usize, n2_raw: usize)
->(Vec<F>,Vec<F>, Vec<F>){
	assert!(n.is_power_of_two(), "n is not power of 2!");
	assert!(b.len()<=n, "b.len MUST be < n");
	let b_test = false;
	let b_perf = true;
	let mut timer = Timer::new();

	//1. compute values of b(X), t(X) over domain [0, n]
	let mut b2 = b.clone();
	let mut t2 = t.clone();
	extend_vec_to_size(&mut b2, n);
	extend_vec_to_size(&mut t2, n);
	let coef_b = compute_coefs_of_lag_points(&b2, r_b);
	let mut coef_t = compute_coefs_of_lag_points(&t2, r_t);

	//2. UNIT testing by random sample
	let coef_b_clone = coef_b.clone();
	let coef_t_clone = coef_t.clone();
	assert!(coef_b.len()==coef_t.len() && coef_b.len()==n+1, "coefs len nok!");
	if b_perf {log_perf(LOG1, "---- compute coefs b(X), t(X)", &mut timer);}
	coef_t[0] = coef_t[0] + beta;
	let pb = get_poly(coef_b);
	let pt = get_poly(coef_t);
	let p_bt= mul(&pb , &pt);
	//let p_left = minus(&p_bt,-&get_poly(vec![F::ONE]); 
	let mut p_left = p_bt.clone();
	p_left.values[0] -= F::ONE; //CHECK!
	let p_right = get_poly(coef_vanish_n_raw.clone());
	
	if b_test{
		for i in 0..(n2_raw-blinding_factors){
			let one = F::ONE;
			let gamma = get_root_of_unity::<F>(n as u64)
				.pow(&[i as u64]);
			let v_b = eval_coefs_at(&coef_b_clone.clone(), gamma);
			let v_t = eval_coefs_at(&coef_t_clone.clone(), gamma);
	
			assert!(v_b * (v_t + beta) - one == F::ZERO,
				"b_i * (t_i + beta) != 1");

			let value =eval_coefs_at(&p_left.values, gamma);
			assert!(value==F::ZERO, "p_left not evaluate to 0 at i: {}", i);

			let v2 = eval_coefs_at(&p_right.values,gamma);
			assert!(v2==F::ZERO, "p_right not evaluate to 0 at i: {}", i);
		}
	}


	//2. compute the corresponding values of q_b
	let q_b = div(&p_left, &p_right);
	if b_test{
		let q3 = mul(&q_b, &p_right);
		if !eq_poly(&q3, &p_left){
			print_poly("p_left:", &p_left);
			print_poly("p_right:", &p_right);
			print_poly("q_b:", &q_b);
			assert!(false, "div failed");	
		}
	}
	let coefs_q_b = q_b.values; 

	//2. UNIT testing by random sample
	if b_test{
		let one = F::ONE;
		let gamma = F::from(327324234u64);
		let v_b = eval_coefs_at(&coef_b_clone.clone(), gamma);
		let v_t = eval_coefs_at(&coef_t_clone.clone(), gamma);
		let v_z_h = eval_coefs_at(&p_right.values, gamma);
		let v_q_b = eval_coefs_at(&coefs_q_b, gamma);

		assert!(v_b * (v_t + beta) - one == v_q_b * v_z_h, 
			"compute_q_b validation failed!");
	}

	(coefs_q_b, coef_b_clone, coef_t_clone)
}

/// compute the co-efficients of the polynomial q_b so that
/// cap_b(X) (cap_t(X) + beta) - 1 = q_b(X) z_H_n_raw(x)
/// where H is the domain of roots of unity of n_raw (b.len())
/// Return (coefs_q_b, coefs_b, coefs_t)
/// Added: blinding_factors: the last "blinding_factors" entries in the query table

fn compute_coeff_q_b<F:PrimeField>(b: &Vec<F>, r_b: F, t: &Vec<F>, r_t: F, beta: F, n: usize, coefs_vanish_n_raw: &Vec<F>, blinding_factors: usize, n2_raw: usize)
->(Vec<F>,Vec<F>, Vec<F>){
	assert!(b.len()<=n, "b.len()>n!");
	if b.len()==n && blinding_factors==0{
		return compute_coeff_q_b_v1(b, r_b, t, r_t, beta, n);
	}else{
		return compute_coeff_q_b_v2(b, r_b, t, r_t, beta, 
			n, coefs_vanish_n_raw , blinding_factors, n2_raw);
	}
}

// -----------------------------------------------------------
// endregion: utility functions and data structures
// -----------------------------------------------------------

#[cfg(test)]
mod tests_cq{
	extern crate rayon;
	use halo2curves::bn256::{Bn256, Fr, G1Affine, G2Affine};
	use crate::plonk::cq_lookup::zk_qanizk_cq::*;
	use crate::plonk::cq_lookup::batch_kzg::*;
	use crate::plonk::cq_lookup::ft_poly_ops::rand_arr_field_ele;

	type Fr256 = Fr;
	type PE256 = Bn256;
	type G1_256= G1Affine;
	type G2_256= G2Affine;


	#[test]
	pub fn test_cq(){
		let n = 8usize;
		let seed = 123321u128;
		let trapdoor = default_trapdoor::<PE256>();
		let lookup_table = rand_arr_field_ele::<Fr256>(n, seed); 
		let query_table = vec![lookup_table[1], lookup_table[2], lookup_table[3], lookup_table[1]];
		let (pkey, vkey) = setup_kzg::<PE256>(n, query_table.len(), &trapdoor, 0);
		let cq_aux = preprocess_cq::<PE256>(&pkey, &lookup_table);
		let vkey_bytes = vkey.to_bytes();
		let (prf, _r_query_table, commit_query_table) = prove_cq(&pkey, 
			&cq_aux, &lookup_table, &query_table, &vkey_bytes);
		let bres = verify_cq(&vkey, cq_aux.commit_t2, commit_query_table, &prf);
		assert!(bres==true, "cq failed"); 
		let g1 = <PE256 as Engine>::G1Affine::generator();
		let bres2 = verify_cq(&vkey, cq_aux.commit_t2, (commit_query_table + 
			(g1 * Fr256::from(327u64)).to_affine()).into(), &prf);
		assert!(bres2==false, "cq false case failed!");
	}

	#[test]
	pub fn test_cq_n2_not_power2(){
		let n = 8usize;
		let seed = gen_seed();
		let trapdoor = default_trapdoor::<PE256>();
		let lookup_table = rand_arr_field_ele::<Fr256>(n, seed); 
		let query_table = vec![
			lookup_table[1], lookup_table[2], 
			lookup_table[3], lookup_table[2], 
			lookup_table[6], lookup_table[5], 
			//not used
			Fr256::from(7234234u64), Fr256::from(123123u64)
			];
		let blinding_factors = 2; //the last two entries
		let (pkey, vkey) = setup_kzg::<PE256>(n, query_table.len(), &trapdoor, blinding_factors);
		let cq_aux = preprocess_cq::<PE256>(&pkey, &lookup_table);
		let vkey_bytes = vkey.to_bytes();
		let (prf, _r_query_table, commit_query_table) = prove_cq_adv(
			&pkey, &cq_aux, &lookup_table, &query_table, &vkey_bytes, 
			Fr256::from(123125));
		let bres = verify_cq(&vkey, cq_aux.commit_t2, commit_query_table, &prf);
		assert!(bres, "cq_not_pow2 failed"); 
	}

	#[test]
	pub fn test_fold_cq(){
		let k = 2; //number of tables to fold
		let n = 8usize;
		let seed = gen_seed();
		let trapdoor = default_trapdoor::<PE256>();
		let alpha = rand_arr_field_ele::<Fr256>(1, seed+5)[0];
		let lookup_tables = (0..k).into_par_iter().map(|x|
			rand_arr_field_ele::<Fr256>(n, seed + x as u128)  
		).collect::<Vec<Vec<Fr256>>>();
		//note: each query table needs to have exact idx into the lookup table
		let query_tables = (0..k).into_par_iter().map(|x|
			vec![lookup_tables[x][3],
				lookup_tables[x][2],
				lookup_tables[x][1],
				//not used
				Fr256::from(234),
				Fr256::from(77123)
			]
		).collect::<Vec<Vec<Fr256>>>();
		let blinding_factors = 2;
		let (pkey, vkey) = setup_kzg::<PE256>(n, query_tables[0].len(), 
			&trapdoor, blinding_factors);
		let cq_auxs = (0..k).into_par_iter().map(|x|
			preprocess_cq::<PE256>(&pkey, &lookup_tables[x])
		).collect::<Vec<CqAux<PE256>>>();
		let ref_cq_auxs = cq_auxs.iter().map(|x| x).collect::<Vec<&CqAux<PE256>>>();
		let vkey_bytes = vkey.to_bytes();
		let lookup_loc_info = gen_hash_idx_for_tables(&lookup_tables); 
		let r_queries = rand_arr_field_ele::<Fr256>(k, seed);
		let (prf, _r_query_tables, commit_query_tables) 
			= fold_prove_cq::<PE256>(&pkey, &ref_cq_auxs, 
				&lookup_tables, &query_tables, 
				&vkey_bytes,
				alpha, &lookup_loc_info, &r_queries);
		let vec_commit_query_table= (0..k).into_par_iter().map(|x|
			(commit_query_tables[x]*alpha.pow(&[(k-1-x) as u64])).to_affine()
		).collect::<Vec<G1_256>>();
		let commit_query_table = sum(&vec_commit_query_table);


		let vec_commit_t2 = (0..k).into_par_iter().map(|x|
			(cq_auxs[x].commit_t2*alpha.pow(&[(k-1-x) as u64])).to_affine()
		).collect::<Vec<G2_256>>();
		let commit_t2 = sum(&vec_commit_t2);

		let bres = verify_cq(&vkey, commit_t2,
			commit_query_table, &prf);
		assert!(bres, "fold cq error");
	}
	
}
