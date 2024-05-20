use crate::plonk::Error;
use halo2_backend::plonk::{
    keygen::{keygen_pk as backend_keygen_pk, keygen_vk as backend_keygen_vk},
    ProvingKey, VerifyingKey,
};
use halo2_backend::{arithmetic::CurveAffine, poly::commitment::Params};
//,plonk::cq_lookup::batch_kzg::ParamsKzgCq};
use halo2_frontend::circuit::{compile_circuit_cq};
use halo2_frontend::plonk::Circuit;
use halo2_middleware::ff::FromUniformBytes;

/// Generate a `VerifyingKey` from an instance of `Circuit`.
/// By default, selector compression is turned **ON**.
///
/// **NOTE**: This `keygen_vk` is legacy one, assuming that `compress_selector: true`.  
/// Hence, it is HIGHLY recommended to pair this util with `keygen_pk`.  
/// In addition, when using this for key generation, user MUST use `compress_selectors: true`.
pub fn keygen_vk<'params, C, P, ConcreteCircuit>(
    params: &P,
    circuit: &ConcreteCircuit,
) -> Result<VerifyingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<'params, C>,
    ConcreteCircuit: Circuit<C::Scalar>,
    C::Scalar: FromUniformBytes<64>,
{
    keygen_vk_custom(params, circuit, true)
}

/// This version takes an additional params for cq_lookup
pub fn keygen_vk_custom<'params, C, P, ConcreteCircuit>(
    params: &P,
    circuit: &ConcreteCircuit,
    compress_selectors: bool,
) -> Result<VerifyingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<'params, C>,
    ConcreteCircuit: Circuit<C::Scalar>,
    C::Scalar: FromUniformBytes<64>
{
	keygen_vk_custom_cq(params, circuit, compress_selectors, None)
}

/// This version takes an additional params for cq_lookup
/// the random_selectors_blinders are passed to compile circuit
pub fn keygen_vk_custom_cq<'params, C, P, ConcreteCircuit>(
    params: &P,
    circuit: &ConcreteCircuit,
    compress_selectors: bool,
	selector_blinders: Option<&Vec<C::ScalarExt>>
) -> Result<VerifyingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<'params, C>,
    ConcreteCircuit: Circuit<C::Scalar>,
    C::Scalar: FromUniformBytes<64>
{
    let (compiled_circuit, _, _) = compile_circuit_cq(params.k(), circuit, compress_selectors, selector_blinders)?;
    Ok(backend_keygen_vk(params, &compiled_circuit)?)
}

/// Generate a `ProvingKey` from a `VerifyingKey` and an instance of `Circuit`.
/// By default, selector compression is turned **ON**.
///
/// **NOTE**: This `keygen_pk` is legacy one, assuming that `compress_selector: true`.  
/// Hence, it is HIGHLY recommended to pair this util with `keygen_vk`.  
/// In addition, when using this for key generation, user MUST use `compress_selectors: true`.
pub fn keygen_pk<'params, C, P, ConcreteCircuit>(
    params: &P,
    vk: VerifyingKey<C>,
    circuit: &ConcreteCircuit,
) -> Result<ProvingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<'params, C>,
    ConcreteCircuit: Circuit<C::Scalar>,
{
	keygen_pk_cq(params, vk, circuit, None)
}

/// Generate a `ProvingKey` from a `VerifyingKey` and an instance of `Circuit`.
/// the selector_blinders is for compile_circuit
pub fn keygen_pk_cq<'params, C, P, ConcreteCircuit>(
    params: &P,
    vk: VerifyingKey<C>,
    circuit: &ConcreteCircuit,
	selector_blinders: Option<&Vec<C::ScalarExt>>
) -> Result<ProvingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<'params, C>,
    ConcreteCircuit: Circuit<C::Scalar>,
{
    keygen_pk_custom_cq(params, vk, circuit, true, selector_blinders)
}

/// Generate a `ProvingKey` from an instance of `Circuit`.
///
/// The selector compression optimization is turned on only if `compress_selectors` is `true`.
///
/// **NOTE**: This `keygen_pk_custom` MUST share the same `compress_selectors` with
/// `VerifyingKey` generation process.
/// Otherwise, the user could get unmatching pk/vk pair.  
/// Hence, it is HIGHLY recommended to pair this util with `keygen_vk_custom`.
pub fn keygen_pk_custom<'params, C, P, ConcreteCircuit>(
    params: &P,
    vk: VerifyingKey<C>,
    circuit: &ConcreteCircuit,
    compress_selectors: bool,
) -> Result<ProvingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<'params, C>,
    ConcreteCircuit: Circuit<C::Scalar>,
{
	keygen_pk_custom_cq(params, vk, circuit, compress_selectors, None)
}

/// selector_blinders needed by the compile_circuit
pub fn keygen_pk_custom_cq<'params, C, P, ConcreteCircuit>(
    params: &P,
    vk: VerifyingKey<C>,
    circuit: &ConcreteCircuit,
    compress_selectors: bool,
	selector_blinders: Option<&Vec<C::ScalarExt>>
) -> Result<ProvingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<'params, C>,
    ConcreteCircuit: Circuit<C::Scalar>,
{
    let (compiled_circuit, _, _) = compile_circuit_cq(params.k(), circuit, compress_selectors, selector_blinders)?;
    Ok(backend_keygen_pk(params, vk, &compiled_circuit)?)
}
