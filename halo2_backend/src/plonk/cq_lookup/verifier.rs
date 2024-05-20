use std::iter;

use super::Argument;
use crate::{
    arithmetic::CurveAffine,
    plonk::circuit::{ExpressionBack, QueryBack, VarBack},
    plonk::{ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX, Error, VerifyingKey},
    poly::{commitment::{MSM}, VerifierQuery},
    transcript::{EncodedChallenge, TranscriptRead},
};
use halo2_middleware::circuit::Any;
use halo2_middleware::ff::Field;
use std::marker::PhantomData;
use std::collections::HashMap;
use crate::plonk::cq_lookup::batch_kzg::KzgVerifierKey;
use halo2curves::{pairing::Engine};
use crate::plonk::cq_lookup::zk_qanizk_cq::{CqProof,verify_cq,CqAuxVer};
use group::{prime::PrimeCurveAffine, Curve};

pub trait CqVerifierScheme{
	/// Application Field
	type F: Field;
	/// Curve used for commitments
	type Curve: CurveAffine<ScalarExt = Self::F>;	
	/// Encoded challenge for transcript writer
	type EC: EncodedChallenge<Self::Curve>;
	/// Transcript Reader 
	type TR: TranscriptRead<Self::Curve, Self::EC>;

	/// Verify: here hide the detials of G2Affine, read from transcript
	/// return true/false and the commitmented commitment of query tables
	/// and their IDs are in table_ids,
	/// alpha is the folding random.
	fn verify(&self, transcript: &mut Self::TR, table_ids: &Vec<usize>,
		alpha: Self::F)->(bool, Self::Curve);
}

pub struct CqVerifierSchemeKzg<PE:Engine, EC: EncodedChallenge<PE::G1Affine>, TR: TranscriptRead<PE::G1Affine, EC>>
where <PE as Engine>::G1Affine: CurveAffine<ScalarExt=PE::Fr>,
	<PE as Engine>::G2Affine: CurveAffine<ScalarExt=PE::Fr>,
{
	vkey: KzgVerifierKey<PE>,
	map_cq_aux_ver: HashMap<usize, CqAuxVer<PE>>,	
	_ph1: PhantomData<EC>,
	_ph2: PhantomData<TR>,
}



impl <PE:Engine, EC: EncodedChallenge<PE::G1Affine>, TR: TranscriptRead<PE::G1Affine, EC>> CqVerifierSchemeKzg<PE, EC, TR>
where <PE as Engine>::G1Affine: CurveAffine<ScalarExt=PE::Fr>,
	<PE as Engine>::G2Affine: CurveAffine<ScalarExt=PE::Fr>,
{
	pub fn new(vkey: KzgVerifierKey<PE>, map_cq_aux_ver: HashMap<usize,CqAuxVer<PE>>) 
		-> Self{
		Self{
			vkey: vkey, 
			map_cq_aux_ver: map_cq_aux_ver,
			_ph1: PhantomData, 
			_ph2: PhantomData}
	}
}

impl <PE:Engine, EC: EncodedChallenge<PE::G1Affine>, TR: TranscriptRead<PE::G1Affine, EC>> CqVerifierScheme for CqVerifierSchemeKzg<PE, EC, TR>
where <PE as Engine>::G1Affine: CurveAffine<ScalarExt=PE::Fr>,
	<PE as Engine>::G2Affine: CurveAffine<ScalarExt=PE::Fr>,
{
	type F = PE::Fr;
	type Curve = PE::G1Affine;
	type EC = EC;
	type TR = TR;

	/// fold prove and write the proof to transcript writer
	fn verify(&self, transcript: &mut Self::TR, table_ids: &Vec<usize>, alpha: Self::F) -> (bool, Self::Curve){
		//1. reconstruct the proof
		let commit_m = transcript.read_point().unwrap();
		let commit_a = transcript.read_point().unwrap();
		let commit_qa = transcript.read_point().unwrap();
		let commit_b = transcript.read_point().unwrap();
		let commit_q_b = transcript.read_point().unwrap();
		let commit_p = transcript.read_point().unwrap();
		let prf_qa = transcript.read_point().unwrap();
		let b_gamma = transcript.read_scalar().unwrap();
		let zv_gamma = transcript.read_scalar().unwrap();
		let cq_prf = CqProof::<PE>{
			commit_m: commit_m,
			commit_a: commit_a,
			commit_qa: commit_qa,
			commit_b: commit_b,
			commit_q_b: commit_q_b,
			commit_p: commit_p,
			prf_qa: prf_qa,
			b_gamma: b_gamma,
			zv_gamma: zv_gamma
		};
		
	    let compressed_input_commitment = transcript.read_point().unwrap();
		

		//2. verify the proof
		let commit_query_table = compressed_input_commitment.clone();
		let k = table_ids.len();	
		let vec_commit_t2 = (0..k).into_iter().map(|x|
			(self.map_cq_aux_ver[&table_ids[x]].commit_t2*alpha
				.pow(&[(k-1-x) as u64])).to_affine()
		).collect::<Vec<PE::G2Affine>>();
		//IMPROVE LATER
		let sum = |v: &Vec<PE::G2Affine>|{
			let mut g1 = v[0].to_curve();
			for i in 1..v.len(){
				g1 = g1 + v[i];
			}
			g1.to_affine()
		};
		let commit_t2 = sum(&vec_commit_t2);

		let bres = verify_cq(&self.vkey, commit_t2,
			commit_query_table, &cq_prf);

		(bres, compressed_input_commitment)
	}
}

// JUST dummy struct to make syntax check happy in 
// halo2_backend/src/plonk/verifier/batch.rs and other places
// that uses IPA
pub struct CqVerifierSchemeIPA<C: CurveAffine, EC: EncodedChallenge<C>, TR: TranscriptRead<C, EC>>
{
	_ph1: PhantomData<C>,
	_ph2: PhantomData<EC>,
	_ph3: PhantomData<TR>,
}

impl <C: CurveAffine, EC: EncodedChallenge<C>, TR: TranscriptRead<C, EC>> CqVerifierScheme for CqVerifierSchemeIPA<C, EC, TR>
{
	type F = C::ScalarExt;
	type Curve = C;
	type EC = EC;
	type TR = TR;

	/// fold prove and write the proof to transcript writer
	fn verify(&self,  _transcript: &mut Self::TR, _table_ids: &Vec<usize>, 
		_alpha: Self::F) -> (bool, Self::Curve){
		unimplemented!("IPA dummy Verifier for CQ should not be called");
	}
}

pub struct CqCompressedInputCommitments<C: CurveAffine> {
    compressed_input_commitment: C, //commit of compressed_input_poly
	pub cq_ver_res: bool, //result of cq verification
}

pub struct CqEvaluated<C: CurveAffine> {
    committed: CqCompressedInputCommitments<C>,
    compressed_input_eval: C::Scalar,
}

pub(in crate::plonk) fn cq_lookup_read_compressed_commitments<
    C: CurveAffine,
    E: EncodedChallenge<C>,
    T: TranscriptRead<C, E>,
	CV: CqVerifierScheme<F=C::ScalarExt,Curve=C,EC=E, TR=T> 
>(
    transcript: &mut T,
	cq_ver: &Option<CV>,
	table_ids: &Vec<usize>,
	theta: C::ScalarExt
) -> Result<CqCompressedInputCommitments<C>, Error> {
	if cq_ver.is_none(){
		Ok(CqCompressedInputCommitments{
			compressed_input_commitment: transcript.read_point()?, 
			cq_ver_res: true
			}
		)
	}else{
		let (bres, com) = cq_ver.as_ref().unwrap()
			.verify(transcript, table_ids, theta);
		Ok(CqCompressedInputCommitments{
			compressed_input_commitment: com, 
			cq_ver_res: bres
		  }
		)
	}

}

impl<C: CurveAffine> CqCompressedInputCommitments<C> {
    pub(crate) fn evaluate<E: EncodedChallenge<C>, T: TranscriptRead<C, E>>(
        self,
        transcript: &mut T,
    ) -> Result<CqEvaluated<C>, Error> {
        let compressed_input_eval = transcript.read_scalar()?;

        Ok(CqEvaluated {
            committed: self,
            compressed_input_eval,
        })
    }
}

impl<C: CurveAffine> CqEvaluated<C> {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn expressions<'a>(
        &'a self,
        _l_0: C::Scalar,
        l_last: C::Scalar,
        l_blind: C::Scalar,
        argument: &'a Argument<C::Scalar>,
        theta: ChallengeTheta<C>,
        _beta: ChallengeBeta<C>,
        _gamma: ChallengeGamma<C>,
        advice_evals: &[C::Scalar],
        fixed_evals: &[C::Scalar],
        instance_evals: &[C::Scalar],
        challenges: &[C::Scalar],
    ) -> impl Iterator<Item = C::Scalar> + 'a {

        let active_rows = C::Scalar::ONE - (l_last + l_blind);
		let compress_expressions = |expressions: &[ExpressionBack<C::Scalar>]| {
			expressions
				.iter()
				.map(|expression| {
					expression.evaluate(
						&|scalar| scalar,
						&|var| match var {
							VarBack::Challenge(challenge) => challenges[challenge.index],
							VarBack::Query(QueryBack {
								index, column_type, ..
							}) => match column_type {
								Any::Fixed => fixed_evals[index],
								Any::Advice => advice_evals[index],
								Any::Instance => instance_evals[index],
							},
						},
						&|a| -a,
						&|a, b| a + b,
						&|a, b| a * b,
					)
				})
				.fold(C::Scalar::ZERO, |acc, eval| acc * *theta + eval)
		};
		let left = self.compressed_input_eval;
		let right = compress_expressions(&argument.input_expressions);

        std::iter::empty()
            .chain(//active_row* (compressed_input_eval - a'(X))
                Some((left-right)*active_rows),
            )
    }

    pub(in crate::plonk) fn queries<'r, M: MSM<C> + 'r>(
        &'r self,
        _vk: &'r VerifyingKey<C>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = VerifierQuery<'r, C, M>> + Clone {
        iter::empty()
            // Open lookup input commitments at x
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.compressed_input_commitment,
                *x,
                self.compressed_input_eval,
            )))
    }
}
