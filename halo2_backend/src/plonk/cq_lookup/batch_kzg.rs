/** Ported from IZPR Protocol.
	The main chunk of functions provided are for fast amortized
	KZG proof (Langrange base) based on: 
	D. Feist and D.  Khovratovich "Fast amortized KZG proofs"
	https://eprint.iacr.org/2023/033

*/

extern crate rayon;
use self::rayon::prelude::*; 
use halo2curves::{pairing::Engine,CurveExt};
use crate::plonk::cq_lookup::utils::{Timer,log_perf,LOG1};
use crate::poly::kzg::commitment::ParamsKZG;
use std::fmt::Debug;

use rand_core::RngCore;
use group::{Curve,GroupEncoding};
use group::ff::{Field,PrimeField};
use group::prime::PrimeCurveAffine;
use crate::plonk::SerdeCurveAffine;
use rand_core::OsRng;
use crate::plonk::cq_lookup::ft_poly_ops::{compute_powers,vanish_poly,fixed_msm,fixed_msm_s, closest_pow2,get_root_of_unity,eval_coefs_at, evals_to_coefs, serial_group_fft,serial_fft, serial_group_ifft};


#[derive(Debug,Clone)]
pub struct ParamsKzgCq<PE:Engine>{
	pub pkey: KzgProverKey<PE>,
	pub vkey: KzgVerifierKey<PE>
}

impl<E:Engine> ParamsKzgCq<E> where
    E::G1Affine: SerdeCurveAffine,
    E::G1: CurveExt<AffineExt = E::G1Affine>{

	/// return a pair of ParamsKZG and ParamsKzgCq with the same
	/// trapdoor. k_kzg is for ParamsKZG, and n_cap is the lookup table
	/// size (has to be a power of 2), and n2_raw is the query table
	/// size (might not be a power of 2).
	pub fn setup<R: RngCore + std::clone::Clone>(
		k_kzg: u32, n_cap: usize, n2_raw: usize, rng: R, blinding_factors: usize)->
		(ParamsKZG<E>, ParamsKzgCq<E>){
		let trapdoor = default_trapdoor_rng::<E,R>(rng);

		Self::setup_with_trapdoor(k_kzg, n_cap, n2_raw, blinding_factors,
			&trapdoor)
	}

	pub fn setup_with_trapdoor(
		k_kzg: u32, n_cap: usize, n2_raw: usize, 
		blinding_factors: usize, trapdoor: &KzgTrapDoor<E::Fr>)
		-> (ParamsKZG<E>, ParamsKzgCq<E>){
		let s = trapdoor.s;
		let params_kzg:ParamsKZG<E> = ParamsKZG::setup_with_s(k_kzg, s);
		let (pkey, vkey) = setup_kzg(n_cap, n2_raw, &trapdoor, blinding_factors);

		(params_kzg, Self{pkey, vkey})
		}
}


/// Prover Key for KZG Polynomial Commitment. Note: not CQ proverkey
/// yet as here we do not have cached quotient polynomials.
/// SLIGHLY DIFFERENT from the original scheme in the CQ paper,
/// we moved lag_all and lag_diff from the preprocessed info (by prover)
/// to the prover key generated by trusted up (as lag_all and lag_diff)
/// is not related to the problem statement (i.e., general purpose)
#[derive(Debug,Clone)]
pub struct KzgProverKey<PE:Engine>{
	/// the upper limit of the degree supported (size of lookup table)
	pub n: usize,
	/// the closest power of 2 of n2_raw
	pub n2: usize,
	/// the size of query table
	pub n2_raw: usize,
	/// the number of entries not used in query table, so actually query table
	/// size is n2_raw - blinding_factors (these entries are located at the end
	/// of query tables as binding factors, and they do NOT have to belong
	/// to the container lookup table.
	pub blinding_factors: usize,
	/// [s^0]_1, [s^1]_1, ..., [s^n]_1
	pub vec_g1: Vec<PE::G1Affine>,
	/// qa_nizk matrix M
	pub qa_m: Vec<Vec<PE::G1Affine>>,
	/// qz_nizk prover key P
	pub qa_p: Vec<PE::G1Affine>,
	/// coefs for vanish_polynomial for n2_raw
	pub coefs_vanish_n2_raw: Vec<PE::Fr>,
	/// [z_V(s)]_1, where z_V is the vanishing poly for all roots of unity of n2
	pub zv_s1: PE::G1Affine,
	/// [z_V_raw(s)]_1, where z_V_raw vanish polynomial for 
	/// [root^1...root^n2_raw]2
	pub zv_s1_raw: PE::G1Affine,
	/// [z_H(s)]_1, where z_H is the vanishing poly for all roots of unity of N 
	pub zh_s1: PE::G1Affine,
	/// [z_H(s)]_2, where z_H is the vanishing poly for all roots of unity of N 
	pub zh_s2: PE::G2Affine,

	// --- The following is MOVED HERE for speed up as it's not dependent
	// --- on the Lookup Table T
	// --- NOTE that the following information can be simply computed by
	// --- prover or anyone using the vec_g1 and vec_g2, they just provides
	// --- the cached info for speeding up the calculation of cached quotient polys
	// --- Thus, they do not increase the power of the soundness adversary
	/// lag_all: L_i(s) for all i
	pub lag_all: Vec<PE::G1Affine>,
	/// lag_all: L_i(s) for all i in [0,n2] (for query table)
	pub lag_all_n2: Vec<PE::G1Affine>,
	/// lag_all: L_i(s) for all i, over group G2
	pub lag_all_2: Vec<PE::G2Affine>,
}

/// KZG Verifier Key
#[derive(Debug,Clone)]
pub struct KzgVerifierKey<PE:Engine>{
	/// the upper limit of the degree supported (size of lookup table)
	pub n: usize,
	/// the size of query table
	pub n2_raw: usize,
	/// the n2 rounded up to closest poewr of 2
	pub n2: usize,
	/// generator of G2,
	pub g2: PE::G2Affine,
	/// s2: [s]_2
	pub s2: PE::G2Affine,
	/// zv_s2: [z_V(s)]_2. z_V the vanishing poly of all roots of unity
	pub zv_s2: PE::G2Affine,
	/// zh_s2: [z_H(s)]_2. z_H the vanishing poly of all roots of unity
	pub zh_s2: PE::G2Affine,
	/// qa_nizk verifier key D
	pub qa_d: Vec<PE::G2Affine>,
	/// qz_nizk verifier key [a]_2
	pub qa_a: PE::G2Affine,
	/// [root^1...root^n2_raw]2
	pub zv_s1_raw: PE::G1Affine,
}

impl <PE:Engine> KzgVerifierKey<PE>{
	pub fn to_bytes(&self) -> Vec<u8>{
		//to improve later
		let mut vec = vec![];
		let mut v1 = self.zv_s2.to_bytes().as_ref().to_vec();
		vec.append(&mut v1);

		vec
	}
}

/// the trap door of KZG Polynomial Commitment
#[derive(Clone)]
pub struct KzgTrapDoor<F: Field>{
	/// the trap door for generating KZG key series
	pub s: F,
	/// the trapdoor for QA-NIZK k vector
	pub k1: F,
	pub k2: F,
	pub k3: F,
	/// the trapdoor for QA-NIZK verifier key [a]
	pub a: F
}

/// return the default trapdoor
pub fn default_trapdoor_rng<PE:Engine, R: RngCore + std::clone::Clone>(rng: R) 
-> KzgTrapDoor<PE::Fr>{
	let s = PE::Fr::random(rng.clone());
	let k1 = PE::Fr::random(rng.clone());
	let k2 = PE::Fr::random(rng.clone());
	let k3 = PE::Fr::random(rng.clone());
	let a = PE::Fr::random(rng);
	KzgTrapDoor{s: s, k1: k1, k2:k2, k3:k3, a:a }
}

/// use the default OsRng
pub fn default_trapdoor<PE:Engine>() -> KzgTrapDoor<PE::Fr>{
	default_trapdoor_rng::<PE,OsRng>(OsRng)
}
// ------------------------------------
// region: batch KZG related
// ------------------------------------

/// Precompute the kzg proofs for T(X) evaluates to a T(\omega^i) for each i.
///	This is the algorithm presented in "Fast Amortized KZG Proof" 
pub fn precompute_kzg_proof<G:PrimeCurveAffine>(
	table: &Vec<G::Scalar>, n: usize, kzg_key: &Vec<G>
	)->Vec<G>{

	assert!(n==table.len(), "n! = table.len()");
	assert!(n.is_power_of_two(), "n not pow of 2");


	let f= evals_to_coefs(&table, G::Scalar::ONE);
	let zero = G::Scalar::ZERO;
	assert!(kzg_key.len()>=n, "kzg.len()<t.len()");

	let g1_0 = G::generator().mul(zero).to_affine();
	let v1= kzg_key[0..n].to_vec();
	let mut v2 = v1.clone();
	v2.reverse();
	let mut vec_s = v2.clone();
	vec_s.append(&mut vec![g1_0; n]);

	let vec_y = serial_group_fft(&vec_s);
	let mut vec_c = vec![zero; n];
	vec_c.append(&mut f[1..n].to_vec());
	vec_c.append(&mut vec![zero]);
	assert!(vec_c.len()==2*n, "vec_v.len !=2*n");
	let mut vec_v = vec_c.clone();
	serial_fft(&mut vec_v);


	let nu = get_root_of_unity::<G::Scalar>((2*n) as u64);
	let arr_nu = compute_powers::<G::Scalar>(2*n, nu);
	let vec_u = vec_y.clone().into_par_iter().zip(vec_v.clone().into_par_iter())
		.zip(arr_nu.into_par_iter()).map(|((y,v),nu)|
			y.mul(v * nu).to_affine() ).collect::<Vec<G>>();

	let vec_h = serial_group_ifft(&vec_u);

	//5. build up the KZG proofs from vec_h
	let vec_h = vec_h[0..n].to_vec();
	let kzg_prfs = serial_group_fft(&vec_h);

	kzg_prfs
}

/// compute all L_i(s) for each i.  (slow version)
pub fn precompute_lags<F:PrimeField>(
	n: usize, 
	s: F)->Vec<F>{
	assert!(n.is_power_of_two(), "n is not pow of 2");
	//1. compute Z_n(s)
	let one = F::ONE;
	let z_n_s = s.pow(&[n as u64]) - one;
	let omega = get_root_of_unity::<F>(n as u64);
	let arr_omega = compute_powers::<F>(n, omega);

	//2. compute Z_n'(omega_i)
	// n*(omega^i)^{n-1} = n/omega^i
	let z_n_prime = compute_derive_vanish::<F>(n);

	//3. L_i(s) = Z_n(s)/((s-omega^i) Z_n'(omega^i))
	let arr_l_i = z_n_prime.into_par_iter().zip(arr_omega.into_par_iter()).
		map(|(x, y)|
		z_n_s*((s-y) * x).invert().unwrap()).collect::<Vec<F>>();

	arr_l_i	
}

/// compute all [L_i(s)] for each i. 
pub fn precompute_lag_group<G:PrimeCurveAffine>(
	n: usize, 
	s: G::Scalar)->Vec<G> {
	assert!(n.is_power_of_two(), "n is not pow of 2");
	let arr_l_i = precompute_lags(n, s);	
	let g1 = G::generator();
	fixed_msm(g1, &arr_l_i)
}

/// compute z_n'(omega^i) for each i in [0, n). Note ' means 
/// derive function.
pub fn compute_derive_vanish<F:PrimeField>(n: usize) ->Vec<F>{
	let omega = get_root_of_unity::<F>(n as u64);
	let arr_omega = compute_powers::<F>(n, omega);
	let fe_n = F::from(n as u64);
	let z_n_prime = arr_omega.into_par_iter().map(|x|
		fe_n*x.invert().unwrap()).collect::<Vec<F>>();

	z_n_prime
}

/// see CQ paper for it: compute all quotient polynomials (group form)
pub fn precompute_quotient_poly<G:PrimeCurveAffine>(
	t: &Vec<G::Scalar>, 
	n: usize, 
	kzg_key: &Vec<G>)->Vec<G> {

	let kzg_prfs = precompute_kzg_proof(t, n, kzg_key);
	let z_n_prime = compute_derive_vanish::<G::Scalar>(n);
	let res = kzg_prfs.into_par_iter().zip(z_n_prime.into_par_iter())
		.map(|(x,y)|
			x.mul(y.invert().unwrap()).to_affine() ).collect::<Vec<G>>();

	res
}

// ------------------------------------
// endregion: KZG related
// ------------------------------------


/// generate the 
/// prover and verifier keys for KZG (note: not CQ yet as
/// we need the cached quotient polynomials)
/// n: the size of lookup (container) table, 
/// n2_raw: the size of query table (note: might
/// not be a power of 2).
/// trapdoor: the s for generating KZG keys.
/// blinding_factors: the last "blinding_factors" entries in query table (they are
///   used as blinding factors when combining with halo2)
pub fn setup_kzg<PE:Engine>(n: usize, n2_raw: usize, 
	trapdoor: &KzgTrapDoor<PE::Fr>, blinding_factors: usize) 
	-> (KzgProverKey<PE>, KzgVerifierKey<PE>) {
	let b_perf = true;

	//1. power series [s^0, s^1, ..., s^n] 
	let n2 = closest_pow2(n2_raw);
	let big_n = if n>2*closest_pow2(n2+1) {n} 
		else {2*closest_pow2(n2+1)};
	assert!(n.is_power_of_two(), "n is not power of 2");
	assert!(n2.is_power_of_two(), "n2 is not power of 2");
	let mut timer = Timer::new();
	if b_perf{println!("\n** setup_kzg keys, n: {}, n2: {}, big_n: {}", n, n2, big_n);}
	let s = trapdoor.s;
	let mut vec_exp = vec![PE::Fr::ONE; big_n+1];
	for i in 1..big_n+1 {vec_exp[i] = vec_exp[i-1] * s}
	if b_perf {log_perf(LOG1, "-- build field elemnts: {s^i} --", &mut timer);}

	//2. build ( [s^0]_1, ..., [s^n]_1 ) on G1
	let g1 = PE::G1Affine::generator();
	let vec_g1 = fixed_msm_s(g1, s, big_n+1);
	if b_perf {log_perf(LOG1, "-- build [s^i]_1 --", &mut timer);}

	//3. build ( [s^0]_1, ..., [s^n]_1 ) on G2
	let g2 = PE::G2Affine::generator();

	//4. build the zv_s2 and zv_s1
	let f_zh = s.pow(&[n as u64]) - PE::Fr::ONE;
	let f_zv = s.pow(&[n2 as u64]) - PE::Fr::ONE;
	let zv_s2 = (g2 * f_zv).to_affine();
	let zv_s1 = (g1 * f_zv).to_affine();
	let zh_s1 = (g1 * f_zh).to_affine();
	let zh_s2 = (g2 * f_zh).to_affine();
	if b_perf {log_perf(LOG1, "-- build zv_s --", &mut timer);}

	//5. build [L_i(s)]_1 and [(L_i(s)-L_i(0))/s]_1
	let all_lag = precompute_lag_group::<PE::G1Affine>(n,s);
	if b_perf {log_perf(LOG1, "-- build [L_i(s)]_1 --", &mut timer);}
	let all_lag_n2 = precompute_lag_group::<PE::G1Affine>(n2,s);
	if b_perf {log_perf(LOG1, "-- build [L_i(s)]_1 for n2--", &mut timer);}
	let all_lag_2 = precompute_lag_group::<PE::G2Affine>(n,s);
	if b_perf {log_perf(LOG1, "-- build [L_i(s)]_2 --", &mut timer);}

	//6. build the matrix M for qa_nizk (3 rows with n+n2_raw+2 ele each)
	let zero = PE::Fr::from(0u64);
	let one = PE::Fr::from(1u64);
	let neg_one = zero - one;
	let g_zero = g1 * zero;
	let g_one= g1 * one;
	let g_neg_one= g1 * neg_one;
	let mut row1= all_lag.clone();
	row1.push(zh_s1);
	row1.append(&mut vec![g_zero.into(); n2_raw+1]);

	let mut row2 = vec![g_zero.into(); n+1];
	let mut row2_p2 = (&all_lag_n2[0..n2_raw]).to_vec(); //chop off rest
	row2_p2.push(zv_s1);
	row2.append(&mut row2_p2);

	let mut row3 = vec![g_one.into(); n];
	row3.push(g_zero.into());
	let mut row3_p2_1 = vec![g_neg_one.into(); n2_raw-blinding_factors];
	let mut row3_p2_2 = vec![g_zero.into(); blinding_factors];
	row3_p2_2.push(g_zero.into());
	row3.append(&mut row3_p2_1);
	row3.append(&mut row3_p2_2);
	let qa_m = vec![row1, row2, row3];
	for i in 0..3{assert!(qa_m[i].len()==n+n2_raw+2, "m row {} size {} !=n+n2_raw+2. n: {}, n2_raw: {}", i, qa_m[i].len(), n, n2_raw);}

	//7. build the prover key P for qa_nizk
	//TODO: improve the following
	let k = vec![trapdoor.k1, trapdoor.k2, trapdoor.k3];
	let row_n = qa_m[0].len();
	let qa_p = (0..row_n).into_par_iter().map(|i|
		qa_m.iter().enumerate().map(|(row_id, row)| 
			(row[i].to_curve() * k[row_id])).sum::<PE::G1>().to_affine()
	).collect::<Vec<PE::G1Affine>>();

	//8. build the verifiyer key [a]_2 and C for qa_nizk (as qa_d)
	let a = trapdoor.a;
	let qa_a = g2 * a;
	let qa_d:Vec<PE::G2Affine> = vec![(g2 * (trapdoor.k1*a)).to_affine(),
		(g2 * (trapdoor.k2*a)).to_affine(), 
		(g2 * (trapdoor.k3*a)).to_affine()];
	if b_perf {log_perf(LOG1, "-- build QA-NIZK keys --", &mut timer);}

	//9. compute the coef for vanish array
	let root = get_root_of_unity::<PE::Fr>(n2 as u64);
	let vroots = compute_powers(n2_raw - blinding_factors, root);
	let coefs_vanish_n2_raw = vanish_poly::<PE::Fr>(&vroots);
	let zv_s1_raw = g1 * (eval_coefs_at(&coefs_vanish_n2_raw, trapdoor.s));
	if b_perf {log_perf(LOG1, "-- build vanish poly --", &mut timer);}

	//7. return
	//let s1 = vec_g1[1].clone();
	let s2 = (g2*s).to_affine();
	let pkey = KzgProverKey{n: n, n2_raw: n2_raw, n2: n2,
		vec_g1: vec_g1,  
		lag_all: all_lag, 
		lag_all_2: all_lag_2, 
		lag_all_n2: all_lag_n2, 
		coefs_vanish_n2_raw: coefs_vanish_n2_raw.clone(), //TO REMOVE
		zh_s1: zh_s1,
		zh_s2: zh_s2,
		qa_m: qa_m,
		qa_p: qa_p,
		zv_s1: zv_s1, 
		zv_s1_raw: zv_s1_raw.to_affine(),
		blinding_factors: blinding_factors,
		};
	let vkey = KzgVerifierKey{
			n: n, n2_raw: n2_raw, n2:n2,
			g2: g2, 
			s2: s2, 
			zv_s2: zv_s2,
			zh_s2: zh_s2,
			qa_d: qa_d, qa_a: qa_a.into(),
			zv_s1_raw: zv_s1_raw.to_affine(),
			};
	return (pkey, vkey);
}

/*
// ----------------------------------------------------
// -- Utility Functions -------------------------------
// ----------------------------------------------------
pub fn print_arr_fe<F:FftField>(s: &str, a: &Vec<F>){
	println!("==== {}: {} ====", s, a.len());
	for i in 0..a.len(){
		println!("-- i: {}, val: {}", i, a[i]);
	}
}
pub fn print_arr<G:AffineCurve>(s: &str, a: &Vec<G>){
	println!("==== {}: {} ====", s, a.len());
	for i in 0..a.len(){
		println!("-- i: {}, val: {}", i, a[i]);
	}
}

// ----------------------------------------------------
// -- Logical Functions for Testing 
// ----------------------------------------------------

/// check kzg_key is generated using the trapdoor s
/// i.e., for each i: kzg_key[i] = [s^i]
pub fn check_kzg_key<G:AffineCurve>(kzg_key: &Vec<G>, s: G::ScalarField){
	let n = kzg_key.len()-1;  
	let g = G::prime_subgroup_generator();
	let mut cur_g = g.mul(s).to_affine();
	for i in 0..n+1{
		assert!(cur_g==kzg_key[i], "kzg_key err at idx {}", i);
		cur_g = cur_g + g;
	}
}

/// logical version of precompute_kzg_proof:
/// for each i in [0, n-1]: compute
/// [ (T(s) - t_i))/(s - \omega^i)] 
/// n has to be a power of 2
/// define T(X) = \sum_{i=0}^{n-1} t_i L_i(X)
pub fn logical_precompute_kzg_proof<G:AffineCurve>(
	t: &Vec<G::ScalarField>, 
	n: usize, 
	s: G::ScalarField) 
	-> Vec<G>{
	assert!(n.is_power_of_two(), "n is not power of 2");
	assert!(t.len()<=n+1, "t.len() > n+1");

	let t_s = logical_eval_as_poly(t, s, n);
	let g = G::prime_subgroup_generator();
	let mut res:Vec<G> = vec![];
	let omega =  G::ScalarField::get_root_of_unity(n as u64).unwrap();
	let mut cur_omega = G::ScalarField::ONE; //omega^0
	for i in 0..n{
		let ts_v = t_s - t[i];
		let item = ts_v / (s - cur_omega);
		cur_omega *= omega;
		let g_item = g.mul(item).to_affine();
		res.push(g_item);
	}

	res
}

/// given n is fft domain size, compute for all i in [0, n)
/// L_i(s) where L_i(x) is the Lagrange poly for the FFT domain [0,n)
pub fn logical_precompute_lag_group<G:AffineCurve>(
	n: usize, s: G::ScalarField) -> Vec<G>{
	assert!(n.is_power_of_two(), "n is not power of 2");
	let mut res = vec![];
	let arr = gen_root_unity_arr(n as u64);
	let g = G::prime_subgroup_generator();
	for i in 0..n{
		let item = eval_lag_poly(i, &arr, s); 
		let g_item = g.mul(item).to_affine();
		res.push(g_item);
	}
	res
}

/// copute all L_i(0) for i in [0, n)
pub fn logical_precompute_lag0_fe<F:FftField>(n: usize)->Vec<F>{
	assert!(n.is_power_of_two(), "n is power of 2");
	let arr = gen_root_unity_arr(n as u64);
	let zero = F::zero();
	let mut res = vec![zero; n];
	for i in 0..n{
		res[i] = eval_lag_poly(i, &arr, zero); 
	}

	res
}

/// compute all [(L_i(s)-L_i(0))/s] for each i, logical version for testing
pub fn logical_precompute_lag_diff<G:AffineCurve>(
	n: usize, 
	s: G::ScalarField)
	->Vec<G> where <G as AffineCurve>::Projective: VariableBaseMSM<MSMBase=G, Scalar=<G as AffineCurve>::ScalarField>{
	let mut res = vec![];
	let arr = gen_root_unity_arr(n as u64);
	let g = G::prime_subgroup_generator();
	for i in 0..n{
		let li_s = eval_lag_poly(i, &arr, s); 
		let li_0 = eval_lag_poly(i, &arr, G::ScalarField::zero()); 
		let item = (li_s - li_0)/s;
		let g_item = g.mul(item).to_affine();
		res.push(g_item);
	}
	res
}

/// compute the quotient polys used in CQ paper
/// Q_i(x) = Z_v'(\omega^i)^-1 kzg_prf_i(x)
pub fn logical_precompute_quotient_poly<G:AffineCurve>(
	t: &Vec<G::ScalarField>,
	n: usize,
	s: G::ScalarField) -> Vec<G>{
	//1. compute all kzg_proof for table t
	assert!(n.is_power_of_two(), "n is not power of 2");
	let kzg_prfs: Vec<G> = logical_precompute_kzg_proof(t, n, s);

	//2. compute z_v'(\omega^i)^-1
	//note that z_v(X) = X^n-1 and z_v'(X) = nx^{n-1} 
	let mut res = vec![];
	let omega =  G::ScalarField::get_root_of_unity(n as u64).unwrap();
	let mut omega_i = G::ScalarField::ONE;
	let one = G::ScalarField::ONE;
	let fe_n = G::ScalarField::from(n as u64);
	for i in 0..n{
		let z_der_omega_i = fe_n * omega_i.pow(&[(n-1) as u64]);
		let inv_z_der_omega_i = one/z_der_omega_i;
		let qi_s = kzg_prfs[i].mul(inv_z_der_omega_i).to_affine();
		res.push(qi_s);
		omega_i *= omega;
	}
	res
}

/// logical version of precompute_kzg_proof in field elements:
/// for each i in [0, n-1]: compute
///  (T(s) - t_i))/(s - \omega^i) 
/// n has to be a power of 2
/// define T(X) = \sum_{i=0}^{n-1} t_i L_i(X)
pub fn logical_precompute_kzg_proof_fe<F:FftField>(
	t: &Vec<F>, 
	n: usize, 
	s: F) 
	-> Vec<F>{
	assert!(n.is_power_of_two(), "n is not power of 2");
	assert!(t.len()<=n+1, "t.len() > n+1");

	let t_s = logical_eval_as_poly(t, s, n);
	let mut res:Vec<F> = vec![];
	let omega =  F::get_root_of_unity(n as u64).unwrap();
	let mut cur_omega = F::ONE; //omega^0
	for i in 0..n{
		let ts_v = t_s - t[i];
		let item = ts_v / (s - cur_omega);
		cur_omega *= omega;
		res.push(item);
	}

	res
}

/// precompute the all quotient poly in the field elements
pub fn logical_precompute_quotient_poly_fe<F:FftField>(
	t: &Vec<F>,
	n: usize,
	s: F) -> Vec<F>{
	//1. compute all kzg_proof for table t
	assert!(n.is_power_of_two(), "n is not power of 2");
	let kzg_prfs: Vec<F> = logical_precompute_kzg_proof_fe(t, n, s);

	//2. compute z_v'(\omega^i)^-1
	//note that z_v(X) = X^n-1 and z_v'(X) = nx^{n-1} 
	let mut res = vec![];
	let omega =  F::get_root_of_unity(n as u64).unwrap();
	let mut omega_i = F::ONE;
	let one = F::ONE;
	let fe_n = F::from(n as u64);
	for i in 0..n{
		let z_der_omega_i = fe_n * omega_i.pow(&[(n-1) as u64]);
		let inv_z_der_omega_i = one/z_der_omega_i;
		let qi_s = kzg_prfs[i] * (inv_z_der_omega_i);
		res.push(qi_s);
		omega_i *= omega;
	}
	res
}



#[cfg(test)]
pub mod tests {
	extern crate ark_bls12_381;
	
	use self::ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
	use zk_cq::batch_kzg::*;
	use zk_cq::ft_poly_ops::*;
    use zk_cq::serial_group_fft2::*;

	use self::ark_bls12_381::Bls12_381;
	type Fr381 = ark_bls12_381::Fr;
	type PE381 = Bls12_381;
	type G1_381= ark_bls12_381::G1Affine;

/*

    #[test]
    fn test_lagrange() {
        let poly = rand_poly::<Fr381>(3, 123456789);
        let lag = precompute_lag(&poly);

        // Generate x-values (roots of unity)
        let n = closest_pow2(poly.degree() + 1); // We want n points for interpolation, where n is degree of poly + 1
        let root = Fr381::get_root_of_unity(n as u64).unwrap();
        let x_values: Vec<Fr381> = (0..n).map(|i| root.pow([i as u64])).collect();

        for (i, poly) in lag.iter().enumerate() {
            // Evaluate the polynomial at each root of unity
            for (j, &xj) in x_values.iter().enumerate() {
                let val = poly.evaluate(&xj);

                // Check if the result is close to 0 or 1 (with some tolerance for numerical errors)
                if i == j {
                    assert!(
                        (val - Fr381::ONE).is_zero(),
                        "Value at root {} should be 1",
                        j + 1
                    );
                } else {
                    assert!(
                        (val - Fr381::zero()).is_zero(),
                        "Value at root {} should be 0",
                        j + 1
                    );
                }
            }
        }
    }

	
    #[test]
    fn test_fft() {
		//1. pick a small power of 2
		//2. call logical gropu_fft
		//3. call group_fft
		//4. fail if not the same.
	
	}
*/

	#[test]
	fn test_precompute_kzg_proof(){
		let n = 32;
		let n2 = 4;
		let bits = 64;
		let n3 = 16;
		let mut t = rand_arr_fe::<Fr381>(n3, bits);
		//let mut t = vec![Fr381::from(1u32),Fr381::from(0u32)];
		let trap = default_trapdoor::<PE381>();
		let (pk, vk) = setup_kzg::<PE381>(n, n2, &trap); 

		let arr = precompute_kzg_proof::<G1_381>(&t, n3, &pk.vec_g1);
		let arr2 = logical_precompute_kzg_proof::<G1_381>(&t, n3, trap.s);
		assert!(arr==arr2, "precompute_kzg_proof nok");
	}

	#[test]
	fn test_precompute_lag_group(){
		let n = 512;
		let s = default_trapdoor::<PE381>().s;

		let arr1 = precompute_lag_group::<G1_381>(n, s);
		let arr2 = logical_precompute_lag_group::<G1_381>(n, s);
		assert!(arr1==arr2, "precompute_lag group nok");
	}

	#[test]
	fn test_precompute_lag0_fe(){
		let n = 32;

		let arr1 = precompute_lag0_fe::<Fr381>(n);
		let arr2 = logical_precompute_lag0_fe::<Fr381>(n);
		assert!(arr1==arr2, "precompute_lag0_fe nok");
	}

	#[test]
	fn test_precompute_lag_diff(){
		let n = 32;
		let s = default_trapdoor::<PE381>().s;

		let arr1 = precompute_lag_diff::<G1_381>(n,s);
		let arr2 = logical_precompute_lag_diff::<G1_381>(n, s);
		assert!(arr1==arr2, "precompute_lag_diff nok");
	}

	#[test]
	fn test_precompute_quotient_poly(){
		let n = 32;
		let n2 = 4;
		let bits = 64;
		let mut t = rand_arr_fe::<Fr381>(n, bits);
		let trap = default_trapdoor::<PE381>();
		let (pk, vk) = setup_kzg::<PE381>(n, n2, &trap); 

		let arr1 = precompute_quotient_poly::<G1_381>(&t, n, &pk.vec_g1);
		let arr2 = logical_precompute_quotient_poly::<G1_381>(&t, n, trap.s);
		assert!(arr1==arr2, "precompute_quotient_poly nok");
	}

}
*/
