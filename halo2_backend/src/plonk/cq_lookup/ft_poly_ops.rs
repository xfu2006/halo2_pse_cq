/* PORTED from IZPR Project. This contains several polynomial
operations which enhances the original one in halo2_backend/poly.
*/

extern crate rayon;

use self::rayon::prelude::*; 
use blake2b_simd::{Params as Blake2bParams};
use std::convert::TryInto;
use std::marker::PhantomData;
use ff::{Field,PrimeField};
use halo2curves::fft::{best_fft};
use halo2curves::{CurveAffine};
use halo2_middleware::zal::impls::H2cEngine;
use halo2_middleware::zal::traits::MsmAccel;
use rand_core::OsRng;
use std::cmp::{max, min};
use crate::poly::{Coeff, Polynomial};
use crate::arithmetic::{parallelize, eval_polynomial};
use group::{prime::PrimeCurveAffine,GroupEncoding};
use group::{Curve};
use crate::plonk::cq_lookup::utils::{Timer,log_perf,LOG1};


/// return ceil(log2(n)), return 0 for 0
pub fn log2(n: usize)->usize{
	if n==0 {return 0;}

	let mut k = 0;
	let mut n2 = n-1;
	while n2!=0{
		n2 = n2 >> 1;
		k += 1;
	}

	k
}
/// get the closet power of 2
pub fn closest_pow2(n: usize)->usize{
	let k = log2(n);
	let n2 = 1<<k;
	return n2;
}

/// Return an Random Array of Field Elements 
pub fn rand_arr_field_ele<F: PrimeField>(size: usize, _seed: u128)->Vec<F>{
	let mut vec = vec![F::ZERO; size];
	let rng = OsRng;
	for i in 0..size{
		vec[i] = F::random(rng.clone());
	}	
	return vec;
}

/// serlialize a vec of T into vec of u8
pub fn to_vecu8<G: GroupEncoding>(v: &Vec<G>)->Vec<u8>{
    if v.len()==0 {return vec![];}
    let mut v2 = vec![];
    for u in v{
        let mut slice = u.to_bytes().as_ref().to_vec();
		v2.append(&mut slice);
    }

	v2
}

pub fn to_vecu8_field<F: PrimeField>(v: &Vec<F>)->Vec<u8>{
    if v.len()==0 {return vec![];}
    let mut v2 = vec![];
    for u in v{
        let mut slice = u.to_repr().as_ref().to_vec();
		v2.append(&mut slice);
    }

	v2
}

/// used as Fiat-Shamir transform verifier challenge
pub fn hash<F:PrimeField>(barr: &Vec<u8>) -> F{
	let b_perf = false;
	let mut t1 = Timer::new();
	let mut hasher = Blake2bParams::new().hash_length(32).
		personal(b"Halocq_transcrip").to_state();
	hasher.update(&barr);
	let mut bres:[u8;32] = hasher.finalize().as_bytes().try_into().unwrap();

	let mut repr = F::Repr::default();
	bres[bres.len()-1] = 0; //to limit over F's modulus
	repr.as_mut().copy_from_slice(&bres);
	let res = F::from_repr(repr).unwrap();
	if b_perf{log_perf(LOG1, &format!("hash: {}", barr.len()), &mut t1);}


	res
}


/// Given {p(\omega^0), ..., p(\omega^{n-1})
/// compute the coefficients array of p(X)
pub fn evals_to_coefs<F:PrimeField>(v: &Vec<F>, coset_shift: F) -> Vec<F>{
	let n = v.len();
	assert!(n.is_power_of_two(), "n is not power of 2");
	let mut v2 = v.clone();
	inplace_ifft_coset(&mut v2, coset_shift);

	v2
}

/// Simply call best_fft
pub fn serial_group_fft<G:PrimeCurveAffine>(v: &Vec<G>)->Vec<G>
{
	let b_perf = false;
	let mut t1 = Timer::new();
	t1.start();

	let mut vec:Vec<G::Curve> = v.into_par_iter()
		.map(|x| x.to_curve()).collect();
	let n = vec.len();
	let k = log2(n);
	assert!(n.is_power_of_two(), "vec size is not power of 2");
	let f_omega = get_root_of_unity::<G::Scalar>(n as u64);
	let _omega = (G::generator() * f_omega).to_affine();


	best_fft(&mut vec, f_omega, k as u32);
	let mut target_g = vec![G::identity(); vec.len() as usize];
	parallelize(&mut target_g, |g_sec, starts| {
		G::Curve::batch_normalize(&vec[starts..(starts + g_sec.len())], g_sec);
	});
	if b_perf{log_perf(LOG1, &format!("serial_fft: {}", vec.len()), &mut t1);}

	target_g	

}

/// Simply call best_fft
pub fn serial_group_ifft<G:PrimeCurveAffine>(v: &Vec<G>)->Vec<G>
{
	let b_perf = false;
	let mut t1 = Timer::new();
	t1.start();

	let mut vec:Vec<G::Curve> = v.into_par_iter()
		.map(|x| x.to_curve()).collect();
	let n = vec.len();
	let k = log2(n);
	assert!(n.is_power_of_two(), "vec size is not power of 2");
	let omega = get_root_of_unity::<G::Scalar>(n as u64);
	let omega_inv = omega.invert().unwrap();
	let div = G::Scalar::from(n as u64).invert().unwrap();

	best_fft(&mut vec, omega_inv, k as u32);

	parallelize(&mut vec, |sec, mut _idx|{
		for iter in sec{
			*iter = *iter * div
		}
	});

	let mut target_g = vec![G::identity(); vec.len() as usize];
	parallelize(&mut target_g, |g_sec, starts| {
		G::Curve::batch_normalize(&vec[starts..(starts + g_sec.len())], g_sec);
	});
	if b_perf{log_perf(LOG1, &format!("serial_ffft: {}", vec.len()), &mut t1);}

	target_g	

}

/// logical version of the group fft, for unit testing. 
pub fn serial_logical_group_fft<G: CurveAffine>(a: &Vec<G>) 
	-> Vec<G>{
	let n = a.len();
	let omega = get_root_of_unity::<G::Scalar>(n as u64);
	let arr_omega = compute_powers::<G::Scalar>(n, omega);
	let res = arr_omega.into_par_iter().map(|x|
		vmsm(a, &compute_powers(n, x)) ).collect::<Vec<G>>();

	res
}


/// Similar to logical IFFT. For testing purpose
pub fn serial_logical_group_ifft<G: CurveAffine>(a: &Vec<G>) -> Vec<G>{
	let n = a.len();
	let inv_omega = get_root_of_unity::<G::Scalar>(n as u64).invert().unwrap();
	let arr_omega = compute_powers::<G::Scalar>(n, inv_omega);
	let fe_n = G::Scalar::from(n as u64).invert().unwrap();
	let res = arr_omega.into_par_iter().map(|x|
		vmsm(a, &compute_powers(n, x)) * fe_n).
		collect::<Vec<G::Curve>>();

	batch_to_affine(&res)
}


/// inplace fft with coset
pub fn inplace_fft_coset<F:PrimeField>(res: &mut Vec<F>, t: F){
	assert!(res.len().is_power_of_two(), "input size not power of 2");
	let mut coset = t; 
	let res_len = res.len();
	for i in 1..res_len{
		res[i] = res[i] * coset;
		coset = coset * t;
	}
	serial_fft(res);
}

/// applying ifft on (omega*t)
pub fn inplace_ifft_coset<F:PrimeField>(res: &mut Vec<F>, t: F){
	assert!(res.len().is_power_of_two(), "input size not power of 2");
	serial_ifft(res);
	let t = t.invert().unwrap();
	let mut coset = t; 
	let pow2 = res.len();
	for i in 1..pow2{
		res[i] = res[i] * coset;
		coset = coset * t;
	}
}

/// Print a polynomial
pub fn print_poly<F:PrimeField>(s: &str, f: &Polynomial<F,Coeff>){
	println!("\n==== {}: degree: {} ====", s, f.values.len());
	for i in 0..f.values.len(){
		let c = f.values[i];
		if i==0{
			println!("{:?}", c);
		}else{
			println!("{:?}x^{}", c, i);
		} 
	}
	println!("\n");
}

/// convert poly from coefs form to array of points evaluated
/// at each lagrange poly, i.e., using FFT.
/// Given p(X) = \sum c_i X^n, return
/// {p(\omega^0), ..., p(\omega^{n-1})
pub fn coefs_to_evals<F:PrimeField>(c: &Vec<F>, coset_shift: F) ->Vec<F>{
	let n = c.len();
	assert!(n.is_power_of_two(), "n is not power of 2");
	let mut c2 = c.clone();
	inplace_fft_coset(&mut c2, coset_shift);
	
	c2
}

/// changes vec, require
/// vec size to be power of 2.
pub fn serial_fft<F: PrimeField>(vec: &mut Vec<F>){
	let b_perf = false;
	let mut t1 = Timer::new();
	t1.start();

	let n = vec.len();
	let k = log2(n);
	assert!(n.is_power_of_two(), "vec size is not power of 2");
	let omega = get_root_of_unity::<F>(n as u64);

	best_fft(vec, omega, k as u32);
	if b_perf{log_perf(LOG1, &format!("------ ---- -- serial_fft: {}", vec.len()), &mut t1);}
}

pub fn serial_ifft<F: PrimeField>(vec: &mut Vec<F>){
	let n = vec.len();
	assert!(n.is_power_of_two(), "vec size is not power of 2");
	let n = vec.len();
	let k = log2(n);
	assert!(n.is_power_of_two(), "vec size is not power of 2");
	let omega = get_root_of_unity::<F>(n as u64);
	let omega_inv = omega.invert().unwrap();
	let div = F::from(n as u64).invert().unwrap();
	best_fft(vec, omega_inv, k as u32);
	parallelize(vec, |sec, mut _idx|{
		for iter in sec{
			*iter = *iter * div
		}
	});
}

/// fixed_msm. Looks like halo2 curve does not have fixed_msm
/// as in arkworks. Simply do parallelize as much as possible
pub fn fixed_msm<G: PrimeCurveAffine>(base: G, vec_exp: &Vec<G::Scalar>)
-> Vec<G>{
	let n = vec_exp.len();
	let base_g1 = base.to_curve();
	let mut gs = vec![base_g1; n];
	parallelize(&mut gs, |g, start|{
		let mut i = 0;
		for g in g.iter_mut(){
			*g *= vec_exp[start+i];
			i+=1;
		}
	});

	let mut target_g = vec![G::identity(); n as usize];
	parallelize(&mut target_g, |g_sec, starts| {
		G::Curve::batch_normalize(&gs[starts..(starts + g_sec.len())], g_sec);
	});

	target_g	
}

/// compute the n'th root of unity
pub fn get_root_of_unity<F:PrimeField>(n: u64)->F{
	let mut r = F::ROOT_OF_UNITY;
	let mut nu = n as usize;
	let pow_s = 1usize << F::S;
	while nu!=pow_s{
		r = r.square(); 
		nu = nu * 2;
	}

	r
}


/// build a dense polynomial given coefs vector 
pub fn get_poly<F:PrimeField>(v: Vec<F>)-> Polynomial<F,Coeff>{
	let v2 = if v.len().is_power_of_two() {v} else 
		{extend_vec(&v, closest_pow2(v.len()))};
	Polynomial{ values: v2, _marker: PhantomData }
}

///test by random point evaluation
pub fn eq_poly<F:PrimeField>(a: &Polynomial<F,Coeff>, b: &Polynomial<F,Coeff>)
-> bool{
	let rd = F::random(OsRng);
	let v1 = eval_coefs_at(&a.values, rd); 
	let v2 = eval_coefs_at(&b.values, rd); 

	v1==v2
}

/// convert to projective form
pub fn batch_to_proj<G:CurveAffine>(v: &[G]) -> Vec<G::Curve>{
	let res = v.into_par_iter().map(|x| x.to_curve())
		.collect::<Vec<G::Curve>>();

	res
}

/// convert to affine
pub fn batch_to_affine<C:Curve>(v: &[C]) -> Vec<C::AffineRepr>
where <C as Curve>::AffineRepr: Clone+Send
{
	let n = v.len();
	let v0a = v[0].to_affine();
	let mut res = vec![v0a; n];
	parallelize(&mut res, |g_sec, starts| {
		C::batch_normalize(&v[starts..(starts + g_sec.len())], g_sec);
	});

	res
}

/// compute variable multiscalar multplication
/// given bases: [g1, g2, ..., gn], and exponents [e1, ..., en]
/// return g1^e1 * g2^e2 * .... * gn^en
/// in groth term: [e1*g1] + ... + [en*gn]
pub fn vmsm<G: CurveAffine>(bases: &[G], arr: &[G::Scalar]) -> G{
	let engine = H2cEngine::new();
	assert!(bases.len()>=arr.len(), "VMSM error: bases.len: {} < arr.len: {}",
		bases.len(), arr.len());
	let n = if arr.len()>bases.len() {bases.len()} else {arr.len()};
	let res = engine.msm(&arr[0..n], &bases[0..n]);

	res.into()
}


/// Treat vector as co-efficient array of a poly
/// More exactly T(X) = \sum_{i=0}^{n-1} t_i L_i(X)
/// evaluate T(s)
pub fn logical_eval_as_poly<F: PrimeField>(t: &Vec<F>, s: F, n: usize) -> F{
	assert!(n.is_power_of_two(), "n is not power of 2");
	let mut t_s = F::ZERO;
	let arr_roots = gen_root_unity_arr::<F>(n as u64);
	let mut pow_s = F::ONE;
	for i in 0..t.len(){
		t_s += t[i] * eval_lag_poly(i, &arr_roots, s);
		pow_s *= s;	
	}
	t_s
}

/// generate [\omega^0, .., \omega^{n-1}]
pub fn gen_root_unity_arr<F:PrimeField>(n: u64)->Vec<F>{
	let mut v = vec![];
	let omega =  get_root_of_unity::<F>(n);
	let mut value = F::ONE;
	for _i in 0..n{
		v.push(value);
		value = value * omega;
	}
	return v;
}

/// evaluate the i'th Lagrange basis poly defined over arr
/// L_i(X) = \prod_{j\neq i} (X-a_j)  / \prod{j\neq i} (a_i-a_j)
/// evaluate L_i(x)
/// NOTE: i is in range [0,n-1]
/// slow version, only use it for debugging or testing
pub fn eval_lag_poly<F:Field>(i: usize, arr: &Vec<F>, x: F)->F{
	let mut prod1 = F::ONE;
	let mut prod2 = F::ONE;
	let a_i = arr[i];
	for j in 0..arr.len(){
		if j!=i{
			prod1 *= x - arr[j];
			prod2 *= a_i - arr[j];
		}
	}
	return prod1*(prod2.invert().unwrap());
}

/// return the co-efficients for the vanishing polynomial
/// (x-v[0])...(x-v[n])
pub fn vanish_poly<F:PrimeField>(vec: &Vec<F>) -> Vec<F>{
	let p = vanish_poly_worker(vec, 0, vec.len(), 0);
	p.values[0..vec.len()+1].to_vec()
}

/// extend a copy of the given vec to size n by padding zero
pub fn extend_vec<F:PrimeField>(vec: &Vec<F>, n: usize)->Vec<F>{
	assert!(vec.len()<=n, "vec.len: {} > n: {}!", vec.len(), n);
	let n2 = n - vec.len();
	let mut vec2 = vec![F::ZERO; n2];
	let mut vec3 = vec.clone();
	vec3.append(&mut vec2);

	vec3
}

/// ideally the degree of a and b should be roughly the same
pub fn mul<F:PrimeField>(a: &Polynomial<F,Coeff>, b: &Polynomial<F,Coeff>)-> Polynomial<F,Coeff>{
	let n1 = a.values.len();
	let n2 = b.values.len();
	let n = if n1>n2 {closest_pow2(n1*2)} else {closest_pow2(n2*2)};
	let mut v1 = extend_vec(&a.values, n);
	let mut v2 = extend_vec(&b.values, n);
	serial_fft(&mut v1);
	serial_fft(&mut v2);
	let mut v3 = v1.into_par_iter().zip(v2.into_par_iter()).map(|(x,y)| x*y).
		collect::<Vec<F>>();
	serial_ifft(&mut v3);
	Polynomial{values: v3, _marker: PhantomData}
}

/// Divide the polynomial by x^k.
/// Basically just leave the portion above x^k (included)
///	E.g., let p = 1 + 2x + 3x^2
///	div_by_xk(p, 2) returns 3
///	div_by_xk(p, 1) returnx 3x + 2
///	div_by_xk(p, 4) returns 0
///	div_by_xk(p, 0) returns p itself
pub fn div_by_xk<F:PrimeField>(f: &Polynomial<F, Coeff>, k: usize) 
	-> Polynomial<F,Coeff>{
	let degree = f.values.len()-1;
	let pzero = Polynomial{values: vec![F::ZERO], _marker: PhantomData};
	if k==0{
		//return f.clone() + &pzero; 
		return f.clone();
	}else if k>degree{
		return pzero;
	}else{
		let old_len = f.values.len();
		let new_coefs = &f.values[k..old_len];
		let newp = get_poly(new_coefs.to_vec());
		return newp;
	}
}

/// NOTE: it can ONLY work when a%b = 0, and the coef_0 of b is
/// not zero
pub fn div<F:PrimeField>(a: &Polynomial<F,Coeff>, b: &Polynomial<F,Coeff>)-> Polynomial<F,Coeff>{
	let n1 = a.values.len();
	let n2 = b.values.len();
	let n = if n1>n2 {n1*2} else {n2*2};
	let v1 = extend_vec(&a.values, n);
	let v2 = extend_vec(&b.values, n);
	let shift = F::random(OsRng);
	let v_a = coefs_to_evals(&v1, shift);
	let v_b = coefs_to_evals(&v2, shift);
	let v_3 = v_a.into_par_iter().zip(v_b.into_par_iter()).map(|(x,y)| 
		x*y.invert().unwrap()
		).  collect::<Vec<F>>();
	let coef_q = evals_to_coefs(&v_3, shift);
	let coef_q = coef_q[0..n/2].to_vec();

	Polynomial{values: coef_q, _marker: PhantomData}
}



/// takes care of unequal length of values
pub fn add<F:PrimeField>(a: &Polynomial<F,Coeff>, b: &Polynomial<F,Coeff>)-> Polynomial<F,Coeff>{
	let n1 = a.values.len();
	let n2 = b.values.len();
	let n = if n1>n2 {n1} else {n2};
	let v1 = extend_vec(&a.values, n);
	let v2 = extend_vec(&b.values, n);
	let v3 = v1.into_par_iter().zip(v2.into_par_iter()).map(|(x,y)| x+y).
		collect::<Vec<F>>();

	get_poly(v3)
}

/// takes care of unequal length of values
pub fn minus<F:PrimeField>(a: &Polynomial<F,Coeff>, b: &Polynomial<F,Coeff>)-> Polynomial<F,Coeff>{
	let n1 = a.values.len();
	let n2 = b.values.len();
	let n = if n1>n2 {n1} else {n2};
	let v1 = extend_vec(&a.values, n);
	let v2 = extend_vec(&b.values, n);
	let v3 = v1.into_par_iter().zip(v2.into_par_iter()).map(|(x,y)| x-y).
		collect::<Vec<F>>();

	get_poly(v3)
}



/// return the co-efficients of polynomial for (x-v[0]).... (x-v[n])
pub fn vanish_poly_worker<F:PrimeField>(vec: &Vec<F>, start: usize, end: usize, depth: usize) -> Polynomial<F,Coeff>{
	    let n = end-start;
		let one = F::ONE;
		let zero = F::ZERO;
  		if n==0{
            let v1 = vec![one];
            return get_poly(v1);
        }else if n==1{
			return get_poly(vec![zero-vec[start], one]);
	    }else{
	        let n2 = n/2;
	        let p1 = vanish_poly_worker(vec, start, start+n2, depth+1);
	        let p2 = vanish_poly_worker(vec, start+n2, start+n, depth+1);

	        let p = mul(&p1, &p2);
			let new_vals = p.values[0..2*n].to_vec();
			let p2 = Polynomial{values:new_vals, _marker: PhantomData};
	        return p2;
	    }
}

/// Given vector t
/// and the random point r, compute all co-efficients
/// of T(X) = \sum_{i=0}^{n-1} t_i L_i(X) + r * z_V{X}
/// where V = {\omega^0, ..., \omega^{n-1} for n'th root of unity \omega
/// n = closet_pow2(len(t))
/// notice that it produces a degree n poly, with n+1 coefs
pub fn compute_coefs_of_lag_points<F:PrimeField>(t:&Vec<F>, r: F)->Vec<F>{
	let n = closest_pow2(t.len());
	assert!(n.is_power_of_two(), "n is not power of 2!");
	let b_test = false;

	//1. fft to convert the first part
	let mut coefs = t.clone();
	serial_ifft(&mut coefs);

	//2. add the coefs for z_V(X)
	coefs.push(r); //the highest degree
	coefs[0] = coefs[0] - r; //to apply plus poly r(X^n -1)
	assert!(coefs.len()==n+1, "coefs degree is not n!");

	//3. self check
	if b_test{
		let s = F::from(12312312098u64);
		let v1 = logical_eval_as_poly_ext(&t, r, s, n);
		let v2 = eval_coefs_at(&coefs, s);
		assert!(v1==v2, "compute_coefs_of_lag_points failed");
	}

	coefs
}


/// evaluate z_V(X) over {\mu^0, ..., \mu^{2n-1}} where \mu^2n = 1
/// z_V(X) = X^n - 1
pub fn eval_z_h_over_2n<F:PrimeField>(n: usize, coset_shift: F)->Vec<F>{
	assert!(n.is_power_of_two(), "n is not power of 2");
	let mut vc = vec![F::ZERO; 2*n];
	vc[0] = F::ZERO - F::ONE;
	vc[n] = F::ONE; //thus encoding coefs array for x^n - 1
	inplace_fft_coset(&mut vc, coset_shift);

	vc
}

/// let c be the vector of co-effs of a polynomial C(X)
/// evaluate C(x) = \sum_{i=0}^n c_i x^i
pub fn eval_coefs_at<F:PrimeField>(c: &Vec<F>, x:F)->F{
	eval_polynomial(c, x)
}


/// Let T(X) = \sum_{i=0}^{n-1} t_i L_i(X) + r*z_V(X)
/// evaluate T(s)
pub fn logical_eval_as_poly_ext<F:PrimeField>(t: &Vec<F>, r: F, s: F, n: usize) -> F{
	let part1 = logical_eval_as_poly(t, s, n);
	let part2 = r*(s.pow(&[n as u64]) - F::ONE);
	part1 + part2
}

// ------------------------------------------------------
// the following functions are VERBATIM from 
// ark_works/poly/domain/utils (related to compute_powers)
// ------------------------------------------------------
const MIN_PARALLEL_CHUNK_SIZE: usize = 1 << 7;

pub fn compute_powers_serial<F: Field>(size: usize, root: F) -> Vec<F> {
    compute_powers_and_mul_by_const_serial(size, root, F::ONE)
}

pub fn compute_powers_and_mul_by_const_serial<F: Field>(
    size: usize, root: F, c: F,) -> Vec<F> {
    let mut value = c;
    (0..size) .map(|_| {
            let old_value = value;
            value *= root;
            old_value
        })
        .collect()
}

pub fn compute_powers<F: Field>(size: usize, g: F) -> Vec<F> {
	//assert!(size.is_power_of_two(), "size: {} is not power of 2", size);
    if size < MIN_PARALLEL_CHUNK_SIZE {
        return compute_powers_serial(size, g);
    }
    // compute the number of threads we will be using.
    let num_cpus_available = rayon::current_num_threads();
    let num_elem_per_thread = max(size / num_cpus_available, MIN_PARALLEL_CHUNK_SIZE);
    let num_cpus_used = if size%num_elem_per_thread==0 {size/num_elem_per_thread} else {size/num_elem_per_thread + 1};
    let res: Vec<F> = (0..num_cpus_used)
        .into_par_iter()
        .flat_map(|i| {
            let offset = g.pow(&[(i * num_elem_per_thread) as u64]);
            // Compute the size that this chunks' output should be
            // (num_elem_per_thread, unless there are less than num_elem_per_thread elements remaining)
            let num_elements_to_compute = min(size - i * num_elem_per_thread, num_elem_per_thread);
           let res = compute_powers_and_mul_by_const_serial(num_elements_to_compute, g, offset);
            res
        })
        .collect();
    res
}

// ---------------------------------------------------------------------
// -------- the above code are VERBATIM from ark_work/poly/domain/utils.rs
// ---------------------------------------------------------------------



/*
/// slow: call with caution
pub fn is_zero<F:PrimeField>(f: &Polynomial<F,Coeff>)->bool{
	for i in 0..f.values.len(){
		if f.values[i]!=F::ZERO{return false;}
	}

	true
}







/// returning the polynomial with degree lower than k
///	e.g., mod_by_xk(1 + 2x + 3x^2, 2) should return 1 + 2x
///	mod_by_xk + div_by_xk should always return the original polynomial
pub fn mod_by_xk<F:PrimeField>(f: &Polynomial<F,Coeff>, k: usize) 
	-> Polynomial<F,Coeff>{
	let degree = f.values.len()-1;
	let pzero = Polynomial{values: vec![F::ZERO], _marker: PhantomData};
	if k==0{
		return pzero;
	}else if k>degree{
		//return f + &pzero;
		return f.clone();
	}else{
		let new_coefs = &f.values[0..k];
		let newp = get_poly(new_coefs.to_vec());
		return newp;
	}
}

/// multiply polynomial by x^k 
pub fn mul_by_xk<F:PrimeField>(f: &Polynomial<F,Coeff>, k: usize) 
-> Polynomial<F,Coeff>{
	if k==0 || is_zero(&f){ return f.clone();}
	else{
		let mut v = vec![F::ZERO; k + f.values.len()];
		for i in 0..k{ v[i] = F::ZERO; }
		for i in k..k+f.values.len(){ v[i] = f.values[i-k]; }

		get_poly(v)
	}
}

/** build x^k. If k is 0, return 1 */
pub fn build_xk<F:PrimeField>(k: usize) -> Polynomial<F,Coeff>{
	let mut v = vec![];
	for _i in 0..k{ v.push(F::ZERO); }
	v.push(F::ONE);
	
	get_poly(v)
} 


/// schoolbook O(n^2) complexity multiplication. But faster than FFT 
/// for small degree up to 64 
//#[inline(always)]
pub fn small_mul_poly<F:PrimeField>(a: &Polynomial<F,Coeff>, 
	b: &Polynomial<F,Coeff>) -> Polynomial<F,Coeff>{
	if is_zero(a) || is_zero(b) {return get_poly(vec![F::ZERO]);}
	let n1 = a.values.len()-1;
	let n2 = b.values.len()-1;
	let n = n1 + n2+1;
	let mut vec:Vec<F> = vec![F::ZERO;n];
	let c1 = &a.values;
	let c2 = &b.values;
	for i in 0..n1+1{
		for j in 0..n2+1{
			vec[i+j] += c1[i] * c2[j];
		}
	} 	

	get_poly(vec)
}

//#[inline(always)]
pub fn mul_poly<F:PrimeField>(a: &Polynomial<F,Coeff>, b: &Polynomial<F,Coeff>)
	-> Polynomial<F,Coeff>{
	if a.values.len() + b.values.len()<=196{
		return small_mul_poly(a, b);
	}else{
		return mul(a,b);
	}
}


/** return the ceil of log2(n) */
pub fn ceil_log2(n: usize) -> usize{
	let mut k = log2(n);
	let res = 1<<k;
	if res<n{ k = k + 1; }
	return k as usize;
}

/** constructr polynomial */
fn build_poly<F:PrimeField>(v: &Vec<u64>)->Polynomial<F,Coeff>{
	let mut v2: Vec<F> = vec![];
	for i in 0..v.len(){ v2.push(F::from(v[i])); }
	get_poly(v2)
} 


/// compute the inverse of f mod x^(2^k).
///	Ref: (1) http://people.seas.harvard.edu/~madhusudan/MIT/ST15/scribe/lect06.pdf
pub fn inv<F:PrimeField>(g: &Polynomial<F,Coeff>, k: usize)
->Polynomial<F,Coeff>{
	let mut timer = Timer::new();
	let mut timer2 = Timer::new();
	timer.start();
	timer2.start();
	//1. k = 0 case
	if g.values.len()==0 || g.values[0]==F::ZERO{
		panic!("INV err: coef0 can't be zero!");
	}
	let c0 = g.values[0].invert().unwrap();
	let zero= get_poly(vec![F::ZERO]);
	let one= get_poly(vec![F::from(1u64)]);
	let mut a = get_poly(vec![c0]);
	let mut t = 1;
	let mut b;

	//2. iterative case
	for _u in 0..k{
		//1. compute b
		let m_a = mod_by_xk(&a, 2*t);
		let m_g = mod_by_xk(&g, 2*t);
		let mut ag_1 = mul_poly(&m_a , &m_g);
		ag_1.values[0] -= F::ONE;
		b = div_by_xk(&ag_1, t);
		b = mod_by_xk(&b, t);
		//2. compute a
		//let a1 = mod_by_xk(&(&zero - &mul(&b , &a), t);
		let a1 = mod_by_xk(&neg(&mul(&b , &a)), t);
		let xt_a1 = mul_by_xk(&a1, t);
		a = a + &xt_a1;
		a = mod_by_xk(&a, 2*t);
		t = 2*t;
	}	

	a
}

/// get the degree by scanning non-zero element
pub fn degree<F:PrimeField>(f: &Polynomial<F, Coeff>)->usize{
	let mut degree = f.values.len()-1;
	let n = f.values.len();
	for i in 0..n{
		if f.values[degree]==F::ZERO{
			degree -= 1;
		}else{
			return degree;
		}
	}

	0
}


/// generate a packed version
pub fn pack_poly<F:PrimeField>(f: &Polynomial<F, Coeff>) 
-> Polynomial<F, Coeff>{
	let degree = degree(f);
	let new_vals = f.values[0..degree+1].to_vec();
	let newlen = closest_pow2(degree+1);
	let new_vals = extend_vec(&new_vals, newlen);

	get_poly(new_vals)
}

/// Reverse the co-ef list. n may be higher than degree of f.  
/// n is the TARGET degree
/// CHECK: if REAL degree is needed
pub fn rev<F:PrimeField>(finp: &Polynomial<F, Coeff>, deg: usize) 
	-> Polynomial<F, Coeff>{
	if is_zero(finp) {return get_poly(vec![F::ZERO]);}

	println!("rev STEP 2.1");
	let fdeg= degree(finp);
	println!("rev STEP 2.2");
	let f = pack_poly(finp);
	println!("rev STEP 2.3");
	assert!(degree(&f) == fdeg, "new f degree not equal!");
	assert!(fdeg<=deg, "error: f.degree() > deg!");
	let n_zero = deg-fdeg;
	let mut v = vec![];
	for i in 0..deg+1{
		if i>=n_zero{
			v.push(f.values[fdeg-(i-n_zero)]);
		}else{
			v.push(F::ZERO);
		}
	}

	println!("rev STEP 2.3");
	get_poly(v)
}

/// faster divide_with_q_and_r using the Hensel lift
/// Ref: 
/// (1) http://people.seas.harvard.edu/~madhusudan/MIT/ST15/scribe/lect06.pdf
/// (2) http://people.csail.mit.edu/madhu/ST12/scribe/lect06.pdf
//#[inline(always)]
pub fn new_divide_with_q_and_r<F: PrimeField>(
	f: &Polynomial<F,Coeff>, g: &Polynomial<F,Coeff>)
	->(Polynomial<F,Coeff>, Polynomial<F,Coeff>){
	let pzero = get_poly(vec![F::ZERO]);
	if degree(g)>degree(f) { return (pzero, g.clone()); }

	let rev_f = rev::<F>(&f, degree(f));
	let rev_g = rev::<F>(&g, degree(g));
	let diff_deg = degree(f)-degree(g);


	println!("STEP 3.1");
	let log_diff_deg = ceil_log2(diff_deg);
	let inv_rev_g = inv(&rev_g, log_diff_deg+1);
	println!("STEP 3.2");
	let prod_inv_rev_g_f = &mul(&inv_rev_g , &rev_f);
	let rev_q = mod_by_xk::<F>(&prod_inv_rev_g_f, diff_deg+1); 
	println!("STEP 3.3");
	let q = rev::<F>(&rev_q, degree(&rev_q));
	let degree_diff = diff_deg - degree(&q);
	let q = mul_by_xk(&q, degree_diff);
	let qg = mul_poly(&q , g);
	let minus_qg = neg(&qg);
	let r = f.clone() + &minus_qg;
	return (q,r);
}

/** adaptive: when the expected items is less than 512*256 use old;
otherwise use new_div_with_q_and_r */
//#[inline(always)]
pub fn adapt_divide_with_q_and_r<F: PrimeField>(
	f: &Polynomial<F,Coeff>, g: &Polynomial<F,Coeff>)
	->(Polynomial<F,Coeff>, Polynomial<F,Coeff>){
		new_divide_with_q_and_r(f, g)
}


/// make all minus
pub fn neg<F:PrimeField>(a1: &Polynomial<F,Coeff>) -> Polynomial<F,Coeff>{
	let mut a = a1.clone();
	for i in 0..a.values.len(){
		a.values[i] = F::ZERO - a.values[i];
	}
	a
}
*/


/*
/// compute omega^n-1 for {omega^i} where omega^n2 = 1
pub fn eval_z_h_over_custom_n<F:PrimeField>(n: usize, n2: usize, coset_shift: F)->Vec<F>{
	assert!(n.is_power_of_two(), "n is not power of 2");
	assert!(n2.is_power_of_two(), "n2 is not power of 2");
	assert!(n2>=2*n, "n2<=2*n");
	let mut vc = vec![F::ZERO; n2];
	vc[0] = F::ZERO - F::ONE;
	vc[n] = F::ONE; //thus encoding coefs array for x^n - 1
	inplace_fft_coset(&mut vc, coset_shift);

	vc
}
*/



#[cfg(test)]
mod tests_ft_poly_ops{
	extern crate rayon;
	use halo2curves::bn256::{Fr, G1Affine};
	type Fr256 = Fr;
	type G1_256= G1Affine;

	use crate::plonk::cq_lookup::ft_poly_ops::*;

	fn logical_compute_powers(s: Fr, n: usize)->Vec<Fr>{
		let mut vec = vec![];
		let one = Fr::ONE;
		vec.push(one);
		for i in 0..n-1{
			vec.push(vec[i] * s);
		}
		vec
	}

	#[test]
	pub fn test_compute_powers(){
		let arr_size = vec![4, 8, 9, 15, 16, 32, 33, 37, 64, 128, 129, 257, 502, 1024, 2049];
		let s = Fr::from(12312371u64);
		for size in arr_size{
			let v1 = logical_compute_powers(s, size);
			let v2 = compute_powers(size, s);
			assert!(v1==v2, "failed test_compute_powers for size: {}", size);
		}
	}


	#[test]
	pub fn simple_test_vanish(){
		let vec = vec![Fr256::from(1u64), Fr256::from(2u64)];
		let coefs = vanish_poly::<Fr256>(&vec);
		let zero = Fr256::ZERO;
		for v in vec{
			let v2 = eval_coefs_at(&coefs, v);
			assert!(v2==zero, "v2 is not zero!");
		}
	}

	#[test]
	pub fn test_vanish2(){
		let root = get_root_of_unity::<Fr256>(64);
		let vec = compute_powers::<Fr256>(64, root);
		let coefs = vanish_poly::<Fr256>(&vec);
		assert!(coefs[0] +Fr256::ONE==Fr256::ZERO, "coefs[0]!=-1");
		assert!(coefs[64]==Fr256::ONE, "element 63 is not 1");
	}

	#[test]
	fn test_group_fft(){
		let n = 32;
		let seed = 123123123u128;
		let t = rand_arr_field_ele::<Fr256>(n, seed);
		let mut t2 = t.clone();
		t2[0] = Fr256::from(256);
		let g1 = G1_256::generator();
		let arr_g = fixed_msm(g1, &t);
		let arr_g2 = fixed_msm(g1, &t2);

		let res1 = serial_group_fft::<G1_256>(&arr_g);
		let res2 = serial_logical_group_fft::<G1_256>(&arr_g);
		let res3 = serial_logical_group_fft::<G1_256>(&arr_g2);
		assert!(res1==res2, "fft result nok!");
		assert!(res1!=res3, "fft result nok for no eq test!");
	}


	#[test]
	fn test_group_ifft(){
		let n = 32;
		let seed = 250234234u128;
		let t = rand_arr_field_ele::<Fr256>(n, seed);
		let t2 = rand_arr_field_ele::<Fr256>(n, seed+203);
		let g1 = G1_256::generator();
		let arr_g = fixed_msm(g1, &t);
		let arr_g2 = fixed_msm(g1, &t2);

		let res1 = serial_group_ifft::<G1_256>(&arr_g);
		let res2 = serial_logical_group_ifft::<G1_256>(&arr_g);
		let res3 = serial_logical_group_ifft::<G1_256>(&arr_g2);
		assert!(res1==res2, "ifft result nok!");
		assert!(res1!=res3, "ifft result nok for neq caes!");
	}


	#[test]
	fn test_logical_group_fft(){
		let n = 32;
		let seed = 250234234u128;
		let t = rand_arr_field_ele::<Fr256>(n, seed);
		let g1 = G1_256::generator();
		let arr_g = fixed_msm(g1, &t);
		let mut t2 = t.clone();
		serial_fft(&mut t2);
		let res1 = fixed_msm(g1, &t2);	
		let res2 = serial_logical_group_fft::<G1_256>(&arr_g);
		assert!(res1==res2, "logical_group_fft fails");
	}

	#[test]
	fn test_logical_group_ifft(){
		let n = 32;
		let seed= 9928234u128;
		let t = rand_arr_field_ele::<Fr256>(n, seed);
		let g1 = G1_256::generator();
		let arr_g = fixed_msm(g1, &t);
		let mut t2 = t.clone();
		serial_ifft(&mut t2);
		let res1 = fixed_msm(g1, &t2);	
		let res2 = serial_logical_group_ifft::<G1_256>(&arr_g);
		assert!(res1==res2, "logical_group_ifft fails");
	}

	/// k_a and k_b means to inject how many zero's into
	/// the coeffcient vector
	fn unit_test_div(n1: usize, n2: usize, k_a: usize, k_b: usize){
		let seed =128234234u128;
		let mut p1 = get_poly( rand_arr_field_ele::<Fr256>(n1, seed) );
		let mut p2 = get_poly( rand_arr_field_ele::<Fr256>(n2, seed) );
		for i in 0..k_a{ p1.values[i] = Fr256::ZERO;}
		for i in 0..k_b{ p2.values[i] = Fr256::ZERO;}

		let q = &mul(&p1, &p2);
		let r1 = div(&q, &p2);
		if !eq_poly(&r1, &p1){
			println!("ERROR in unit_test_adapt div: ");
			print_poly("p1: ", &p1);
			print_poly("p2: ", &p2);
			print_poly("q: ", &q);
			print_poly("r1: ", &r1);
			assert!(false, "poly div failed");
		}
	} 

	#[test]
	fn test_adaptive_div(){
		unit_test_div(16, 8, 0, 0);
		unit_test_div(16, 7, 0, 0);
		unit_test_div(22, 2, 2, 1);
		unit_test_div(29, 27, 3, 2);
	}
}
