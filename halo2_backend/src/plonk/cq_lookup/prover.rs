use super::super::ProvingKey;
use super::Argument;
use crate::plonk::evaluation::evaluate;
use crate::{
    arithmetic::{eval_polynomial,  CurveAffine},
	//parallelize
    plonk::circuit::ExpressionBack,
    plonk::{ChallengeTheta, ChallengeX, Error},
	//ChallengeBeta, ChallengeGamma, 
    poly::{
        commitment::{Blind, Params},
        Coeff, EvaluationDomain, LagrangeCoeff, Polynomial, ProverQuery,
    },
    transcript::{EncodedChallenge, TranscriptWrite},
};
use group::{
    ff::{Field},
	//BatchInvert, 
    Curve,
};
use halo2_middleware::ff::WithSmallOrderMulGroup;
use halo2curves::{pairing::Engine};
use halo2_middleware::zal::{impls::PlonkEngine, traits::MsmAccel};
use rand_core::RngCore;
use std::{
    //collections::BTreeMap,
    iter,
    ops::{Mul, MulAssign},
};
use crate::plonk::cq_lookup::{
	batch_kzg::ParamsKzgCq,
	zk_qanizk_cq::{CqAux, fold_prove_cq},
	//ft_poly_ops::{rand_arr_field_ele}
};
use std::collections::HashMap;
use std::marker::PhantomData;

/// the trait for providing cq prover scheme. We implemented
/// the KZG version but for IPA we provide a dummy (empty) struct only
pub trait CqProverScheme{
	/// Application Field
	type F: Field;
	/// Curve used for commitments
	type Curve: CurveAffine<ScalarExt = Self::F>;	
	/// Encoded challenge for transcript writer
	type EC: EncodedChallenge<Self::Curve>;
	/// Transcript Writer
	type TW: TranscriptWrite<Self::Curve, Self::EC>;

	/// fold prove and write the proof to transcript writer, return
	/// the set of randoms used
	fn fold_prove(&self, vec_vals: &Vec<Vec<Self::F>>, table_ids: &Vec<usize>, arr_tables: &Vec<Vec<Self::F>>, transcript: &mut Self::TW, alpha: Self::F, hs_idx: &HashMap<Vec<u8>, usize>)-> Vec<Self::F>;

	/// return the blinding factors (as halo), the number of
	/// non-used items at the end of the query table
	fn get_blinding_factors(&self) -> usize;
}

pub struct CqProverSchemeKzg<PE:Engine, EC: EncodedChallenge<PE::G1Affine>, TW: TranscriptWrite<PE::G1Affine, EC>>
where <PE as Engine>::G1Affine: CurveAffine<ScalarExt=PE::Fr>,
	<PE as Engine>::G2Affine: CurveAffine<ScalarExt=PE::Fr>,
{
	params_cq: ParamsKzgCq<PE>,
	hs_cq_aux: HashMap<usize, CqAux<PE>>,
	vkey_bytes: Vec<u8>,
	_ph1: PhantomData<EC>,
	_ph2: PhantomData<TW>,
}

impl <PE:Engine, EC: EncodedChallenge<PE::G1Affine>, TW: TranscriptWrite<PE::G1Affine, EC>> CqProverSchemeKzg<PE, EC, TW>
where <PE as Engine>::G1Affine: CurveAffine<ScalarExt=PE::Fr>,
	<PE as Engine>::G2Affine: CurveAffine<ScalarExt=PE::Fr>,
{
	pub fn new(params_cq: ParamsKzgCq<PE>, 
		hs_cq_aux: HashMap<usize, CqAux<PE>>) -> Self{
		let vbytes = params_cq.vkey.to_bytes();
		Self{
			params_cq: params_cq, 
			hs_cq_aux: hs_cq_aux, 
			vkey_bytes: vbytes,
			_ph1: PhantomData, 
			_ph2: PhantomData}
	}
}

impl <PE:Engine, EC: EncodedChallenge<PE::G1Affine>, TW: TranscriptWrite<PE::G1Affine, EC>> CqProverScheme for CqProverSchemeKzg<PE, EC, TW>
where <PE as Engine>::G1Affine: CurveAffine<ScalarExt=PE::Fr>,
	<PE as Engine>::G2Affine: CurveAffine<ScalarExt=PE::Fr>,
{
	type F = PE::Fr;
	type Curve = PE::G1Affine;
	type EC = EC;
	type TW = TW;

	/// fold prove and write the proof to transcript writer
	fn fold_prove(&self, vec_vals: &Vec<Vec<Self::F>>, table_ids: &Vec<usize>, arr_tables: &Vec<Vec<Self::F>>, transcript: &mut Self::TW, alpha: Self::F, hs_idx: &HashMap<Vec<u8>, usize>)->Vec<Self::F>{
		//1. constructor the vec of aux
		let mut vec_aux = vec![];
		for tid in table_ids{
			let ref_aux: &CqAux<PE> = 
				self.hs_cq_aux.get(&tid).expect("no aux exist");
			vec_aux.push(ref_aux);
		}

		//2. prove
		//NOTE: here r_queries: blinds are set as ZERO because
		//in halo2, blind factors are used (instead of the original
		// plonk zk approach). This kind of saving the FFT domain size.
		// In fact, the KZG commit_lagrange() in halo2-pse fork
		// did not include blinder in the computation.
		// In https://mirprotocol.org/blog/Adding-zero-knowledge-to-Plonk-Halo
		// there is a detailed discussion and the proof.
		// In this case: we use ZERO as the blinder, and INCREASE 1
		// to the num_blinders value in the constraint system.
		let r_queries = vec![PE::Fr::ZERO; vec_vals.len()];
		let (prf, rqueries_back, _commit_querys) = fold_prove_cq(
			&self.params_cq.pkey, &vec_aux, &arr_tables,
			vec_vals, &self.vkey_bytes, alpha, hs_idx, &r_queries);

		//3. write
		transcript.write_point(prf.commit_m).unwrap();
		transcript.write_point(prf.commit_a).unwrap();
		transcript.write_point(prf.commit_qa).unwrap();
		transcript.write_point(prf.commit_b).unwrap();
		transcript.write_point(prf.commit_q_b).unwrap();
		transcript.write_point(prf.commit_p).unwrap();
		transcript.write_point(prf.prf_qa).unwrap();
		transcript.write_scalar(prf.b_gamma).unwrap();
		transcript.write_scalar(prf.zv_gamma).unwrap();


		//4. return the r_queries used (actually zero, as explained above)
		rqueries_back	
	}

	fn get_blinding_factors(&self) -> usize{
		self.params_cq.pkey.blinding_factors	
	}
}

//dummy object for IPA
pub struct CqProverSchemeIPA<C:CurveAffine, EC: EncodedChallenge<C>, TW: TranscriptWrite<C, EC>>
{
	_ph1: PhantomData<EC>,
	_ph2: PhantomData<TW>,
	_ph3: PhantomData<C>,
}

impl <C:CurveAffine, EC: EncodedChallenge<C>, TW: TranscriptWrite<C, EC>> CqProverScheme for CqProverSchemeIPA<C, EC, TW>
{
	type F = C::ScalarExt;
	type Curve = C;
	type EC = EC;
	type TW = TW;

	/// fold prove and write the proof to transcript writer
	fn fold_prove(&self, _vec_vals: &Vec<Vec<Self::F>>, _table_ids: &Vec<usize>, _arr_tables: &Vec<Vec<Self::F>>, _transcript: &mut Self::TW, _alpha: Self::F, _hs_idx: &HashMap<Vec<u8>, usize>)->Vec<Self::F>{
	unimplemented!("DON'T call CqProverSchemeIPA::fold_prove. It's dummy");
	}

	fn get_blinding_factors(&self) -> usize{
		unimplemented!("DON'T call CqProverSchemeIPA functions. It's dummy");
	}
}

#[derive(Debug)]
pub(in crate::plonk) struct CqCommited<C: CurveAffine> {
	pub (in crate::plonk)
    compressed_input_poly: Polynomial<C::Scalar, Coeff>,
	pub (in crate::plonk)
    compressed_input_blind: Blind<C::Scalar>,
}

pub(in crate::plonk) struct CqEvaluated<C: CurveAffine> {
    constructed: CqCommited<C>,
}

/// Given a CQ-Lookup with input expressions [A_0, A_1, ..., A_{m-1}] 
/// Note we do not allow table expressions: only tables.
/// - constructs A_compressed = \theta^{m-1} A_0 + theta^{m-2} A_1 + ... + \theta A_{m-2} + A_{m-1}
/// The [`CqCommited<C>`] struct is used to update the cq-Lookup, and is then returned.
#[allow(clippy::too_many_arguments)]
pub(in crate::plonk) fn cq_lookup_commit<
    'a,
    'params: 'a,
    F: WithSmallOrderMulGroup<3>,
    C,
    P: Params<'params, C>,
    E: EncodedChallenge<C>,
    R: RngCore,
    T: TranscriptWrite<C, E>,
    M: MsmAccel<C>,
	CP: CqProverScheme<F=F,Curve=C,EC=E, TW=T>
>(
    engine: &PlonkEngine<C, M>,
    arg: &Argument<F>,
    pk: &ProvingKey<C>,
    params: &P,
    domain: &EvaluationDomain<C::Scalar>,
    theta: ChallengeTheta<C>,
    advice_values: &'a [Polynomial<C::Scalar, LagrangeCoeff>],
    fixed_values: &'a [Polynomial<C::Scalar, LagrangeCoeff>],
    instance_values: &'a [Polynomial<C::Scalar, LagrangeCoeff>],
    challenges: &'a [C::Scalar],
    mut _rng: R,
    transcript: &mut T,
	cq_prover: &'params Option<CP>,
) -> Result<CqCommited<C>, Error>
where
    C: CurveAffine<ScalarExt = F>,
    C::Curve: Mul<F, Output = C::Curve> + MulAssign<F>
{
	//1. collect the vector of values and aggregated field value
	let collect_vec_vals = |expressions: &[ExpressionBack<C::Scalar>]| {
		expressions.iter().map(|expression|{
			evaluate(
                    expression,
                    params.n() as usize,
                    1,
                    fixed_values,
                    advice_values,
                    instance_values,
                    challenges,
			)
		}).collect::<Vec<Vec<C::Scalar>>>()
	};

	let compress_expressions = |vec_vals: &Vec<Vec<C::Scalar>>|{
		vec_vals.iter().map(|vec_val|{
			pk.vk.domain.lagrange_from_vec(vec_val.clone())
		}). fold(domain.empty_lagrange(), |acc, expression_val|{
                acc * *theta + &expression_val
		})
	};

	let vec_vals = collect_vec_vals(&arg.input_expressions);
	let compressed_input_expression = compress_expressions(&vec_vals);

	//2. compute the cq proof (if cq_prover exists)
	let blind_sc= C::Scalar::ZERO;
	if !cq_prover.is_none(){
		let cq_prover = cq_prover.as_ref().unwrap();
		let _vec_blinds = cq_prover.fold_prove(&vec_vals, &arg.table_ids, &arg.vec_columns, transcript, *theta, &arg.hs_idx);  //it will write points
	}

    //3. Closure to construct commitment to vector of values
    let commit_values = |values: &Polynomial<C::Scalar, LagrangeCoeff>, blind_sc: F| {
        let poly = pk.vk.domain.lagrange_to_coeff(values.clone());
        let blind = Blind(blind_sc);
        let commitment = params
            .commit_lagrange(&engine.msm_backend, values, blind)
            .to_affine();
        (poly, blind, commitment)
    };

    // Commit to compressed input expression
    let (compressed_input_poly, compressed_input_blind, compressed_input_commitment) = commit_values(&compressed_input_expression, blind_sc);
	transcript.write_point(compressed_input_commitment)?;

    Ok(CqCommited{
        compressed_input_poly,
        compressed_input_blind,
    })
}


impl<C: CurveAffine> CqCommited<C> {
    pub(in crate::plonk) fn evaluate<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        self,
        _pk: &ProvingKey<C>,
        x: ChallengeX<C>,
        transcript: &mut T,
    ) -> Result<CqEvaluated<C>, Error> {
        let compressed_input_eval = eval_polynomial(
			&self.compressed_input_poly, *x);

        // Hash each advice evaluation
        for eval in iter::empty()
            .chain(Some(compressed_input_eval))
        {
            transcript.write_scalar(eval)?;
        }

        Ok(CqEvaluated { constructed: self })
    }
}

impl<C: CurveAffine> CqEvaluated<C> {
    pub(in crate::plonk) fn open<'a>(
        &'a self,
        _pk: &'a ProvingKey<C>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = ProverQuery<'a, C>> + Clone {
        iter::empty()
            .chain(Some(ProverQuery {
                point: *x,
                poly: &self.constructed.compressed_input_poly,
                blind: self.constructed.compressed_input_blind,
            }))
    }
}

