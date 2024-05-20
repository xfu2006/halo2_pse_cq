//! This module:
//! - Evaluates the h polynomial: Evaluator::new(ConstraintSystem).evaluate_h(...)
//! - Evaluates an Expression using Lagrange basis

use crate::multicore;
use crate::plonk::{
    circuit::{ConstraintSystemBack, ExpressionBack, VarBack},
    lookup, cq_lookup, permutation, ProvingKey,
};
use crate::poly::{Basis, LagrangeBasis};
use crate::{
    arithmetic::{parallelize, CurveAffine},
    poly::{Coeff, ExtendedLagrangeCoeff, Polynomial},
};
use group::ff::{Field, PrimeField, WithSmallOrderMulGroup};
use halo2_middleware::circuit::Any;
use halo2_middleware::poly::Rotation;

use super::shuffle;

/// Return the index in the polynomial of size `isize` after rotation `rot`.
fn get_rotation_idx(idx: usize, rot: i32, rot_scale: i32, isize: i32) -> usize {
    (((idx as i32) + (rot * rot_scale)).rem_euclid(isize)) as usize
}

/// Value used in [`Calculation`]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd)]
enum ValueSource {
    /// This is a constant value
    Constant(usize),
    /// This is an intermediate value
    Intermediate(usize),
    /// This is a fixed column
    Fixed(usize, usize),
    /// This is an advice (witness) column
    Advice(usize, usize),
    /// This is an instance (external) column
    Instance(usize, usize),
    /// This is a challenge
    Challenge(usize),
    /// beta
    Beta(),
    /// gamma
    Gamma(),
    /// theta
    Theta(),
    /// y
    Y(),
    /// Previous value
    PreviousValue(),
}

impl Default for ValueSource {
    fn default() -> Self {
        ValueSource::Constant(0)
    }
}

impl ValueSource {
    /// Get the value for this source
    #[allow(clippy::too_many_arguments)]
    fn get<F: Field, B: Basis>(
        &self,
        rotations: &[usize],
        constants: &[F],
        intermediates: &[F],
        fixed_values: &[Polynomial<F, B>],
        advice_values: &[Polynomial<F, B>],
        instance_values: &[Polynomial<F, B>],
        challenges: &[F],
        beta: &F,
        gamma: &F,
        theta: &F,
        y: &F,
        previous_value: &F,
    ) -> F {
        match self {
            ValueSource::Constant(idx) => constants[*idx],
            ValueSource::Intermediate(idx) => intermediates[*idx],
            ValueSource::Fixed(column_index, rotation) => {
                fixed_values[*column_index][rotations[*rotation]]
            }
            ValueSource::Advice(column_index, rotation) => {
                advice_values[*column_index][rotations[*rotation]]
            }
            ValueSource::Instance(column_index, rotation) => {
                instance_values[*column_index][rotations[*rotation]]
            }
            ValueSource::Challenge(index) => challenges[*index],
            ValueSource::Beta() => *beta,
            ValueSource::Gamma() => *gamma,
            ValueSource::Theta() => *theta,
            ValueSource::Y() => *y,
            ValueSource::PreviousValue() => *previous_value,
        }
    }
}

/// Calculation
#[derive(Clone, Debug, PartialEq, Eq)]
enum Calculation {
    /// This is an addition
    Add(ValueSource, ValueSource),
    /// This is a subtraction
    Sub(ValueSource, ValueSource),
    /// This is a product
    Mul(ValueSource, ValueSource),
    /// This is a square
    Square(ValueSource),
    /// This is a double
    Double(ValueSource),
    /// This is a negation
    Negate(ValueSource),
    /// This is Horner's rule: `val = a; val = val * c + b[]`
    Horner(ValueSource, Vec<ValueSource>, ValueSource),
    /// This is a simple assignment
    Store(ValueSource),
}

impl Calculation {
    /// Get the resulting value of this calculation
    #[allow(clippy::too_many_arguments)]
    fn evaluate<F: Field, B: Basis>(
        &self,
        rotations: &[usize],
        constants: &[F],
        intermediates: &[F],
        fixed_values: &[Polynomial<F, B>],
        advice_values: &[Polynomial<F, B>],
        instance_values: &[Polynomial<F, B>],
        challenges: &[F],
        beta: &F,
        gamma: &F,
        theta: &F,
        y: &F,
        previous_value: &F,
    ) -> F {
        let get_value = |value: &ValueSource| {
            value.get(
                rotations,
                constants,
                intermediates,
                fixed_values,
                advice_values,
                instance_values,
                challenges,
                beta,
                gamma,
                theta,
                y,
                previous_value,
            )
        };
        match self {
            Calculation::Add(a, b) => get_value(a) + get_value(b),
            Calculation::Sub(a, b) => get_value(a) - get_value(b),
            Calculation::Mul(a, b) => get_value(a) * get_value(b),
            Calculation::Square(v) => get_value(v).square(),
            Calculation::Double(v) => get_value(v).double(),
            Calculation::Negate(v) => -get_value(v),
            Calculation::Horner(start_value, parts, factor) => {
                let factor = get_value(factor);
                let mut value = get_value(start_value);
                for part in parts.iter() {
                    value = value * factor + get_value(part);
                }
                value
            }
            Calculation::Store(v) => get_value(v),
        }
    }
}

/// Evaluator
#[derive(Clone, Default, Debug)]
pub struct Evaluator<C: CurveAffine> {
    ///  Custom gates evalution
    custom_gates: GraphEvaluator<C>,
    ///  Lookups evalution
    lookups: Vec<GraphEvaluator<C>>,
    ///  CQ-Lookups evalution
    cq_lookups: Vec<GraphEvaluator<C>>,
    ///  Shuffle evalution
    shuffles: Vec<GraphEvaluator<C>>,
}

/// The purpose of GraphEvaluator to is to collect a set of computations and compute them by making a graph of
/// its internal operations to avoid repeating computations.
///
/// Computations can be added in two ways:
///
/// - using [`Self::add_expression`] where expressions are added and internally turned into a graph.
///   A reference to the computation is returned in the form of [ `ValueSource::Intermediate`] reference
///   index.
/// - using [`Self::add_calculation`] where you can add only a single operation or a
///   [Horner polynomial evaluation](https://en.wikipedia.org/wiki/Horner's_method) by using
///   Calculation::Horner
///
/// Finally, call [`Self::evaluate`] to get the result of the last calculation added.
///
#[derive(Clone, Debug)]
struct GraphEvaluator<C: CurveAffine> {
    /// Constants
    constants: Vec<C::ScalarExt>,
    /// Rotations
    rotations: Vec<i32>,
    /// Calculations
    calculations: Vec<CalculationInfo>,
    /// Number of intermediates
    num_intermediates: usize,
}

/// EvaluationData
#[derive(Default, Debug)]
struct EvaluationData<C: CurveAffine> {
    /// Intermediates
    intermediates: Vec<C::ScalarExt>,
    /// Rotations
    rotations: Vec<usize>,
}

/// CalculationInfo contains a calculation to perform and in [`Self::target`] the [`EvaluationData::intermediates`] where the value is going to be stored.  
#[derive(Clone, Debug)]
struct CalculationInfo {
    /// Calculation
    calculation: Calculation,
    /// Target
    target: usize,
}

impl<C: CurveAffine> Evaluator<C> {
    /// Creates a new evaluation structure from a [`ConstraintSystemBack`]
    pub fn new(cs: &ConstraintSystemBack<C::ScalarExt>) -> Self {
        let mut ev = Evaluator::default();

        let mut parts = Vec::new();
        for gate in cs.gates.iter() {
            parts.push(ev.custom_gates.add_expression(&gate.poly));
        }
        ev.custom_gates.add_calculation(Calculation::Horner(
            ValueSource::PreviousValue(),
            parts,
            ValueSource::Y(),
        ));

        // Lookups
        for lookup in cs.lookups.iter() {
            let mut graph = GraphEvaluator::default();

            let mut evaluate_lc = |expressions: &Vec<ExpressionBack<_>>| {
                let parts = expressions
                    .iter()
                    .map(|expr| graph.add_expression(expr))
                    .collect();
                graph.add_calculation(Calculation::Horner(
                    ValueSource::Constant(0),
                    parts,
                    ValueSource::Theta(),
                ))
            };

            // Input coset
            let compressed_input_coset = evaluate_lc(&lookup.input_expressions);
            // table coset
            let compressed_table_coset = evaluate_lc(&lookup.table_expressions);
            // z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
            let right_gamma = graph.add_calculation(Calculation::Add(
                compressed_table_coset,
                ValueSource::Gamma(),
            ));
            let lc = graph.add_calculation(Calculation::Add(
                compressed_input_coset,
                ValueSource::Beta(),
            ));
            graph.add_calculation(Calculation::Mul(lc, right_gamma));

            ev.lookups.push(graph);
        }

        // CQ-Lookups
        for lookup in cs.cq_lookups.iter() {
            let mut graph = GraphEvaluator::default();

            let mut evaluate_lc = |expressions: &Vec<ExpressionBack<_>>| {
                let parts = expressions
                    .iter()
                    .map(|expr| graph.add_expression(expr))
                    .collect();
                graph.add_calculation(Calculation::Horner(
                    ValueSource::Constant(0),
                    parts,
                    ValueSource::Theta(),
                ))
            };

            // Input coset (NOTE: it's needed!)
            let _compressed_input_coset = evaluate_lc(&lookup.input_expressions);

            ev.cq_lookups.push(graph);
        }


        // Shuffles
        for shuffle in cs.shuffles.iter() {
            let evaluate_lc = |expressions: &Vec<ExpressionBack<_>>,
                               graph: &mut GraphEvaluator<C>| {
                let parts = expressions
                    .iter()
                    .map(|expr| graph.add_expression(expr))
                    .collect();
                graph.add_calculation(Calculation::Horner(
                    ValueSource::Constant(0),
                    parts,
                    ValueSource::Theta(),
                ))
            };

            let mut graph_input = GraphEvaluator::default();
            let compressed_input_coset = evaluate_lc(&shuffle.input_expressions, &mut graph_input);
            let _ = graph_input.add_calculation(Calculation::Add(
                compressed_input_coset,
                ValueSource::Gamma(),
            ));

            let mut graph_shuffle = GraphEvaluator::default();
            let compressed_shuffle_coset =
                evaluate_lc(&shuffle.shuffle_expressions, &mut graph_shuffle);
            let _ = graph_shuffle.add_calculation(Calculation::Add(
                compressed_shuffle_coset,
                ValueSource::Gamma(),
            ));

            ev.shuffles.push(graph_input);
            ev.shuffles.push(graph_shuffle);
        }

        ev
    }

    /// Evaluate h poly
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn evaluate_h(
        &self,
        pk: &ProvingKey<C>,
        advice_polys: &[&[Polynomial<C::ScalarExt, Coeff>]],
        instance_polys: &[&[Polynomial<C::ScalarExt, Coeff>]],
        challenges: &[C::ScalarExt],
        y: C::ScalarExt,
        beta: C::ScalarExt,
        gamma: C::ScalarExt,
        theta: C::ScalarExt,
        lookups: &[Vec<lookup::prover::Committed<C>>],
        cq_lookups: &[Vec<cq_lookup::prover::CqCommited<C>>],
        shuffles: &[Vec<shuffle::prover::Committed<C>>],
        permutations: &[permutation::prover::Committed<C>],
    ) -> Polynomial<C::ScalarExt, ExtendedLagrangeCoeff> {
        let domain = &pk.vk.domain;
        let size = domain.extended_len();
        let rot_scale = 1 << (domain.extended_k() - domain.k());
        let fixed = &pk.fixed_cosets[..];
        let extended_omega = domain.get_extended_omega();
        let isize = size as i32;
        let one = C::ScalarExt::ONE;
        let l0 = &pk.l0;
        let l_last = &pk.l_last;
        let l_active_row = &pk.l_active_row;
        let p = &pk.vk.cs.permutation;

        // Calculate the advice and instance cosets
        let advice: Vec<Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>> = advice_polys
            .iter()
            .map(|advice_polys| {
                advice_polys
                    .iter()
                    .map(|poly| domain.coeff_to_extended(poly.clone()))
                    .collect()
            })
            .collect();
        let instance: Vec<Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>> = instance_polys
            .iter()
            .map(|instance_polys| {
                instance_polys
                    .iter()
                    .map(|poly| domain.coeff_to_extended(poly.clone()))
                    .collect()
            })
            .collect();

        let mut values = domain.empty_extended();

        // Core expression evaluations
        let num_threads = multicore::current_num_threads();
        for (((((advice, instance), lookups), cq_lookups), shuffles), permutation) in advice
            .iter()
            .zip(instance.iter())
            .zip(lookups.iter())
            .zip(cq_lookups.iter())
            .zip(shuffles.iter())
            .zip(permutations.iter())
        {
            // Custom gates
            multicore::scope(|scope| {
                let chunk_size = (size + num_threads - 1) / num_threads;
                for (thread_idx, values) in values.chunks_mut(chunk_size).enumerate() {
                    let start = thread_idx * chunk_size;
                    scope.spawn(move |_| {
                        let mut eval_data = self.custom_gates.instance();
                        for (i, value) in values.iter_mut().enumerate() {
                            let idx = start + i;
                            *value = self.custom_gates.evaluate(
                                &mut eval_data,
                                fixed,
                                advice,
                                instance,
                                challenges,
                                &beta,
                                &gamma,
                                &theta,
                                &y,
                                value,
                                idx,
                                rot_scale,
                                isize,
                            );
                        }
                    });
                }
            });

            // Permutations
            let sets = &permutation.sets;
            if !sets.is_empty() {
                let blinding_factors = pk.vk.cs.blinding_factors();
                let last_rotation = Rotation(-((blinding_factors + 1) as i32));
                let chunk_len = pk.vk.cs.degree() - 2;
                let delta_start = beta * C::Scalar::ZETA;

                let first_set = sets.first().unwrap();
                let last_set = sets.last().unwrap();

                // Permutation constraints
                parallelize(&mut values, |values, start| {
                    let mut beta_term = extended_omega.pow_vartime([start as u64, 0, 0, 0]);
                    for (i, value) in values.iter_mut().enumerate() {
                        let idx = start + i;
                        let r_next = get_rotation_idx(idx, 1, rot_scale, isize);
                        let r_last = get_rotation_idx(idx, last_rotation.0, rot_scale, isize);

                        // Enforce only for the first set.
                        // l_0(X) * (1 - z_0(X)) = 0
                        *value = *value * y
                            + ((one - first_set.permutation_product_coset[idx]) * l0[idx]);
                        // Enforce only for the last set.
                        // l_last(X) * (z_l(X)^2 - z_l(X)) = 0
                        *value = *value * y
                            + ((last_set.permutation_product_coset[idx]
                                * last_set.permutation_product_coset[idx]
                                - last_set.permutation_product_coset[idx])
                                * l_last[idx]);
                        // Except for the first set, enforce.
                        // l_0(X) * (z_i(X) - z_{i-1}(\omega^(last) X)) = 0
                        for (set_idx, set) in sets.iter().enumerate() {
                            if set_idx != 0 {
                                *value = *value * y
                                    + ((set.permutation_product_coset[idx]
                                        - permutation.sets[set_idx - 1].permutation_product_coset
                                            [r_last])
                                        * l0[idx]);
                            }
                        }
                        // And for all the sets we enforce:
                        // (1 - (l_last(X) + l_blind(X))) * (
                        //   z_i(\omega X) \prod_j (p(X) + \beta s_j(X) + \gamma)
                        // - z_i(X) \prod_j (p(X) + \delta^j \beta X + \gamma)
                        // )
                        let mut current_delta = delta_start * beta_term;
                        for ((set, columns), cosets) in sets
                            .iter()
                            .zip(p.columns.chunks(chunk_len))
                            .zip(pk.permutation.cosets.chunks(chunk_len))
                        {
                            let mut left = set.permutation_product_coset[r_next];
                            for (values, permutation) in columns
                                .iter()
                                .map(|&column| match column.column_type {
                                    Any::Advice => &advice[column.index],
                                    Any::Fixed => &fixed[column.index],
                                    Any::Instance => &instance[column.index],
                                })
                                .zip(cosets.iter())
                            {
                                left *= values[idx] + beta * permutation[idx] + gamma;
                            }

                            let mut right = set.permutation_product_coset[idx];
                            for values in columns.iter().map(|&column| match column.column_type {
                                Any::Advice => &advice[column.index],
                                Any::Fixed => &fixed[column.index],
                                Any::Instance => &instance[column.index],
                            }) {
                                right *= values[idx] + current_delta + gamma;
                                current_delta *= &C::Scalar::DELTA;
                            }

                            *value = *value * y + ((left - right) * l_active_row[idx]);
                        }
                        beta_term *= &extended_omega;
                    }
                });
            }

            // Lookups
            for (n, lookup) in lookups.iter().enumerate() {
                // Polynomials required for this lookup.
                // Calculated here so these only have to be kept in memory for the short time
                // they are actually needed.
                let product_coset = pk.vk.domain.coeff_to_extended(lookup.product_poly.clone());
                let permuted_input_coset = pk
                    .vk
                    .domain
                    .coeff_to_extended(lookup.permuted_input_poly.clone());
                let permuted_table_coset = pk
                    .vk
                    .domain
                    .coeff_to_extended(lookup.permuted_table_poly.clone());

                // Lookup constraints
                parallelize(&mut values, |values, start| {
                    let lookup_evaluator = &self.lookups[n];
                    let mut eval_data = lookup_evaluator.instance();
                    for (i, value) in values.iter_mut().enumerate() {
                        let idx = start + i;

                        let table_value = lookup_evaluator.evaluate(
                            &mut eval_data,
                            fixed,
                            advice,
                            instance,
                            challenges,
                            &beta,
                            &gamma,
                            &theta,
                            &y,
                            &C::ScalarExt::ZERO,
                            idx,
                            rot_scale,
                            isize,
                        );

                        let r_next = get_rotation_idx(idx, 1, rot_scale, isize);
                        let r_prev = get_rotation_idx(idx, -1, rot_scale, isize);

                        let a_minus_s = permuted_input_coset[idx] - permuted_table_coset[idx];
                        // l_0(X) * (1 - z(X)) = 0
                        *value = *value * y + ((one - product_coset[idx]) * l0[idx]);
                        // l_last(X) * (z(X)^2 - z(X)) = 0
                        *value = *value * y
                            + ((product_coset[idx] * product_coset[idx] - product_coset[idx])
                                * l_last[idx]);
                        // (1 - (l_last(X) + l_blind(X))) * (
                        //   z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
                        //   - z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta)
                        //          (\theta^{m-1} s_0(X) + ... + s_{m-1}(X) + \gamma)
                        // ) = 0
                        *value = *value * y
                            + ((product_coset[r_next]
                                * (permuted_input_coset[idx] + beta)
                                * (permuted_table_coset[idx] + gamma)
                                - product_coset[idx] * table_value)
                                * l_active_row[idx]);
                        // Check that the first values in the permuted input expression and permuted
                        // fixed expression are the same.
                        // l_0(X) * (a'(X) - s'(X)) = 0
                        *value = *value * y + (a_minus_s * l0[idx]);
                        // Check that each value in the permuted lookup input expression is either
                        // equal to the value above it, or the value at the same index in the
                        // permuted table expression.
                        // (1 - (l_last + l_blind)) * (a′(X) − s′(X))⋅(a′(X) − a′(\omega^{-1} X)) = 0
                        *value = *value * y
                            + (a_minus_s
                                * (permuted_input_coset[idx] - permuted_input_coset[r_prev])
                                * l_active_row[idx]);
                    }
                });
            }
			
            // CQ-Lookups
            for (n, lookup) in cq_lookups.iter().enumerate() {
                // Polynomials required for this lookup.
                // Calculated here so these only have to be 
				// kept in memory for the short time
                // they are actually needed.
                let compressed_input_coset = pk
                    .vk
                    .domain
                    .coeff_to_extended(lookup.compressed_input_poly.clone());

                // Lookup constraints
                parallelize(&mut values, |values, start| {
                    let lookup_evaluator = &self.cq_lookups[n];
                    let mut eval_data = lookup_evaluator.instance();
                    for (i, value) in values.iter_mut().enumerate() {
                        let idx = start + i;

                        let compressed_input_value = lookup_evaluator.evaluate(
                            &mut eval_data,
                            fixed,
                            advice,
                            instance,
                            challenges,
                            &beta,
                            &gamma,
                            &theta,
                            &y,
                            &C::ScalarExt::ZERO,
                            idx,
                            rot_scale,
                            isize,
                        );


                        let a_minus_s = compressed_input_coset[idx] - 
							compressed_input_value;
                        // (1 - (l_last(X) + l_blind(X)) * (compressed_input_cost(X) - compressed_input_value(X))
                        *value = *value * y + a_minus_s *  l_active_row[idx];
                    }
                });
            }


            // Shuffle constraints
            for (n, shuffle) in shuffles.iter().enumerate() {
                let product_coset = pk.vk.domain.coeff_to_extended(shuffle.product_poly.clone());

                // Shuffle constraints
                parallelize(&mut values, |values, start| {
                    let input_evaluator = &self.shuffles[2 * n];
                    let shuffle_evaluator = &self.shuffles[2 * n + 1];
                    let mut eval_data_input = shuffle_evaluator.instance();
                    let mut eval_data_shuffle = shuffle_evaluator.instance();
                    for (i, value) in values.iter_mut().enumerate() {
                        let idx = start + i;

                        let input_value = input_evaluator.evaluate(
                            &mut eval_data_input,
                            fixed,
                            advice,
                            instance,
                            challenges,
                            &beta,
                            &gamma,
                            &theta,
                            &y,
                            &C::ScalarExt::ZERO,
                            idx,
                            rot_scale,
                            isize,
                        );

                        let shuffle_value = shuffle_evaluator.evaluate(
                            &mut eval_data_shuffle,
                            fixed,
                            advice,
                            instance,
                            challenges,
                            &beta,
                            &gamma,
                            &theta,
                            &y,
                            &C::ScalarExt::ZERO,
                            idx,
                            rot_scale,
                            isize,
                        );

                        let r_next = get_rotation_idx(idx, 1, rot_scale, isize);

                        // l_0(X) * (1 - z(X)) = 0
                        *value = *value * y + ((one - product_coset[idx]) * l0[idx]);
                        // l_last(X) * (z(X)^2 - z(X)) = 0
                        *value = *value * y
                            + ((product_coset[idx] * product_coset[idx] - product_coset[idx])
                                * l_last[idx]);
                        // (1 - (l_last(X) + l_blind(X))) * (z(\omega X) (s(X) + \gamma) - z(X) (a(X) + \gamma)) = 0
                        *value = *value * y
                            + l_active_row[idx]
                                * (product_coset[r_next] * shuffle_value
                                    - product_coset[idx] * input_value)
                    }
                });
            }
        }
        values
    }
}

impl<C: CurveAffine> Default for GraphEvaluator<C> {
    fn default() -> Self {
        Self {
            // Fixed positions to allow easy access
            constants: vec![
                C::ScalarExt::ZERO,
                C::ScalarExt::ONE,
                C::ScalarExt::from(2u64),
            ],
            rotations: Vec::new(),
            calculations: Vec::new(),
            num_intermediates: 0,
        }
    }
}

impl<C: CurveAffine> GraphEvaluator<C> {
    /// Adds a rotation
    fn add_rotation(&mut self, rotation: &Rotation) -> usize {
        let position = self.rotations.iter().position(|&c| c == rotation.0);
        match position {
            Some(pos) => pos,
            None => {
                self.rotations.push(rotation.0);
                self.rotations.len() - 1
            }
        }
    }

    /// Adds a constant
    fn add_constant(&mut self, constant: &C::ScalarExt) -> ValueSource {
        let position = self.constants.iter().position(|&c| c == *constant);
        ValueSource::Constant(match position {
            Some(pos) => pos,
            None => {
                self.constants.push(*constant);
                self.constants.len() - 1
            }
        })
    }

    /// Adds a calculation.
    /// Currently does the simplest thing possible: just stores the
    /// resulting value so the result can be reused  when that calculation
    /// is done multiple times.
    fn add_calculation(&mut self, calculation: Calculation) -> ValueSource {
        let existing_calculation = self
            .calculations
            .iter()
            .find(|c| c.calculation == calculation);
        match existing_calculation {
            Some(existing_calculation) => ValueSource::Intermediate(existing_calculation.target),
            None => {
                let target = self.num_intermediates;
                self.calculations.push(CalculationInfo {
                    calculation,
                    target,
                });
                self.num_intermediates += 1;
                ValueSource::Intermediate(target)
            }
        }
    }

    /// Generates an optimized evaluation for the expression
    fn add_expression(&mut self, expr: &ExpressionBack<C::ScalarExt>) -> ValueSource {
        match expr {
            ExpressionBack::Constant(scalar) => self.add_constant(scalar),
            ExpressionBack::Var(VarBack::Query(query)) => {
                let rot_idx = self.add_rotation(&query.rotation);
                match query.column_type {
                    Any::Fixed => self.add_calculation(Calculation::Store(ValueSource::Fixed(
                        query.column_index,
                        rot_idx,
                    ))),
                    Any::Advice => self.add_calculation(Calculation::Store(ValueSource::Advice(
                        query.column_index,
                        rot_idx,
                    ))),
                    Any::Instance => self.add_calculation(Calculation::Store(
                        ValueSource::Instance(query.column_index, rot_idx),
                    )),
                }
            }
            ExpressionBack::Var(VarBack::Challenge(challenge)) => self.add_calculation(
                Calculation::Store(ValueSource::Challenge(challenge.index())),
            ),
            ExpressionBack::Negated(a) => match **a {
                ExpressionBack::Constant(scalar) => self.add_constant(&-scalar),
                _ => {
                    let result_a = self.add_expression(a);
                    match result_a {
                        ValueSource::Constant(0) => result_a,
                        _ => self.add_calculation(Calculation::Negate(result_a)),
                    }
                }
            },
            ExpressionBack::Sum(a, b) => {
                // Undo subtraction stored as a + (-b) in expressions
                match &**b {
                    ExpressionBack::Negated(b_int) => {
                        let result_a = self.add_expression(a);
                        let result_b = self.add_expression(b_int);
                        if result_a == ValueSource::Constant(0) {
                            self.add_calculation(Calculation::Negate(result_b))
                        } else if result_b == ValueSource::Constant(0) {
                            result_a
                        } else {
                            self.add_calculation(Calculation::Sub(result_a, result_b))
                        }
                    }
                    _ => {
                        let result_a = self.add_expression(a);
                        let result_b = self.add_expression(b);
                        if result_a == ValueSource::Constant(0) {
                            result_b
                        } else if result_b == ValueSource::Constant(0) {
                            result_a
                        } else if result_a <= result_b {
                            self.add_calculation(Calculation::Add(result_a, result_b))
                        } else {
                            self.add_calculation(Calculation::Add(result_b, result_a))
                        }
                    }
                }
            }
            ExpressionBack::Product(a, b) => {
                let result_a = self.add_expression(a);
                let result_b = self.add_expression(b);
                if result_a == ValueSource::Constant(0) || result_b == ValueSource::Constant(0) {
                    ValueSource::Constant(0)
                } else if result_a == ValueSource::Constant(1) {
                    result_b
                } else if result_b == ValueSource::Constant(1) {
                    result_a
                } else if result_a == ValueSource::Constant(2) {
                    self.add_calculation(Calculation::Double(result_b))
                } else if result_b == ValueSource::Constant(2) {
                    self.add_calculation(Calculation::Double(result_a))
                } else if result_a == result_b {
                    self.add_calculation(Calculation::Square(result_a))
                } else if result_a <= result_b {
                    self.add_calculation(Calculation::Mul(result_a, result_b))
                } else {
                    self.add_calculation(Calculation::Mul(result_b, result_a))
                }
            }
        }
    }

    /// Creates a new evaluation structure
    fn instance(&self) -> EvaluationData<C> {
        EvaluationData {
            intermediates: vec![C::ScalarExt::ZERO; self.num_intermediates],
            rotations: vec![0usize; self.rotations.len()],
        }
    }

    #[allow(clippy::too_many_arguments)]
    /// Fills the EvaluationData
    ///     .intermediaries with the evaluation the calculation
    ///     .rotations with the indexes of the polinomials after rotations
    /// returns the value of last evaluation done.
    fn evaluate<B: Basis>(
        &self,
        data: &mut EvaluationData<C>,
        fixed: &[Polynomial<C::ScalarExt, B>],
        advice: &[Polynomial<C::ScalarExt, B>],
        instance: &[Polynomial<C::ScalarExt, B>],
        challenges: &[C::ScalarExt],
        beta: &C::ScalarExt,
        gamma: &C::ScalarExt,
        theta: &C::ScalarExt,
        y: &C::ScalarExt,
        previous_value: &C::ScalarExt,
        idx: usize,
        rot_scale: i32,
        isize: i32,
    ) -> C::ScalarExt {
        // All rotation index values
        for (rot_idx, rot) in self.rotations.iter().enumerate() {
            data.rotations[rot_idx] = get_rotation_idx(idx, *rot, rot_scale, isize);
        }

        // All calculations, with cached intermediate results
        for calc in self.calculations.iter() {
            data.intermediates[calc.target] = calc.calculation.evaluate(
                &data.rotations,
                &self.constants,
                &data.intermediates,
                fixed,
                advice,
                instance,
                challenges,
                beta,
                gamma,
                theta,
                y,
                previous_value,
            );
        }

        // Return the result of the last calculation (if any)
        if let Some(calc) = self.calculations.last() {
            data.intermediates[calc.target]
        } else {
            C::ScalarExt::ZERO
        }
    }
}

/// Simple evaluation of an [`ExpressionBack`] over the provided lagrange polynomials
pub fn evaluate<F: Field, B: LagrangeBasis>(
    expression: &ExpressionBack<F>,
    size: usize,
    rot_scale: i32,
    fixed: &[Polynomial<F, B>],
    advice: &[Polynomial<F, B>],
    instance: &[Polynomial<F, B>],
    challenges: &[F],
) -> Vec<F> {
    let mut values = vec![F::ZERO; size];
    let isize = size as i32;
    parallelize(&mut values, |values, start| {
        for (i, value) in values.iter_mut().enumerate() {
            let idx = start + i;
            *value = expression.evaluate(
                &|scalar| scalar,
                &|var| match var {
                    VarBack::Challenge(challenge) => challenges[challenge.index()],
                    VarBack::Query(query) => {
                        let rot_idx = get_rotation_idx(idx, query.rotation.0, rot_scale, isize);
                        match query.column_type {
                            Any::Fixed => fixed[query.column_index][rot_idx],
                            Any::Advice => advice[query.column_index][rot_idx],
                            Any::Instance => instance[query.column_index][rot_idx],
                        }
                    }
                },
                &|a| -a,
                &|a, b| a + b,
                &|a, b| a * b,
            );
        }
    });
    values
}

#[cfg(test)]
mod test {
    use crate::plonk::circuit::{ExpressionBack, QueryBack, VarBack};
    use crate::poly::LagrangeCoeff;
    use halo2_middleware::circuit::{Any, ChallengeMid};
    use halo2_middleware::poly::Rotation;
    use halo2curves::pasta::pallas::{Affine, Scalar};

    use super::*;

    fn check(calc: Option<Calculation>, expr: Option<ExpressionBack<Scalar>>, expected: i64) {
        let lagranges = |v: &[&[u64]]| -> Vec<Polynomial<Scalar, LagrangeCoeff>> {
            v.iter()
                .map(|vv| {
                    Polynomial::new_lagrange_from_vec(
                        vv.iter().map(|v| Scalar::from(*v)).collect::<Vec<_>>(),
                    )
                })
                .collect()
        };

        let mut gv = GraphEvaluator::<Affine>::default();
        if let Some(expression) = expr {
            gv.add_expression(&expression);
        } else if let Some(calculation) = calc {
            gv.add_rotation(&Rotation::cur());
            gv.add_rotation(&Rotation::next());
            gv.add_calculation(calculation);
        } else {
            unreachable!()
        }

        let mut evaluation_data = gv.instance();
        let result = gv.evaluate(
            &mut evaluation_data,
            &lagranges(&[&[2, 3], &[1002, 1003]]), // fixed
            &lagranges(&[&[4, 5], &[1004, 1005]]), // advice
            &lagranges(&[&[6, 7], &[1006, 1007]]), // instance
            &[8u64.into(), 9u64.into()],           // challenges
            &Scalar::from_raw([10, 0, 0, 0]),      // beta
            &Scalar::from_raw([11, 0, 0, 0]),      // gamma
            &Scalar::from_raw([12, 0, 0, 0]),      // theta
            &Scalar::from_raw([13, 0, 0, 0]),      // y
            &Scalar::from_raw([14, 0, 0, 0]),      // previous value
            0,                                     // idx
            1,                                     // rot_scale
            32,                                    // isize
        );
        let fq_expected = if expected < 0 {
            -Scalar::from(-expected as u64)
        } else {
            Scalar::from(expected as u64)
        };

        assert_eq!(
            result, fq_expected,
            "Expected {} was {:?}",
            expected, result
        );
    }
    fn check_expr(expr: ExpressionBack<Scalar>, expected: i64) {
        check(None, Some(expr), expected);
    }
    fn check_calc(calc: Calculation, expected: i64) {
        check(Some(calc), None, expected);
    }

    #[test]
    fn graphevaluator_values() {
        use VarBack::*;
        // Check values
        for (col, rot, expected) in [(0, 0, 2), (0, 1, 3), (1, 0, 1002), (1, 1, 1003)] {
            check_expr(
                ExpressionBack::Var(Query(QueryBack {
                    index: 0,
                    column_index: col,
                    column_type: Any::Fixed,
                    rotation: Rotation(rot),
                })),
                expected,
            );
        }
        for (col, rot, expected) in [(0, 0, 4), (0, 1, 5), (1, 0, 1004), (1, 1, 1005)] {
            check_expr(
                ExpressionBack::Var(Query(QueryBack {
                    index: 0,
                    column_index: col,
                    column_type: Any::Advice,
                    rotation: Rotation(rot),
                })),
                expected,
            );
        }
        for (col, rot, expected) in [(0, 0, 6), (0, 1, 7), (1, 0, 1006), (1, 1, 1007)] {
            check_expr(
                ExpressionBack::Var(Query(QueryBack {
                    index: 0,
                    column_index: col,
                    column_type: Any::Instance,
                    rotation: Rotation(rot),
                })),
                expected,
            );
        }
        for (ch, expected) in [(0, 8), (1, 9)] {
            check_expr(
                ExpressionBack::Var(Challenge(ChallengeMid {
                    index: ch,
                    phase: 0,
                })),
                expected,
            );
        }

        check_calc(Calculation::Store(ValueSource::Beta()), 10);
        check_calc(Calculation::Store(ValueSource::Gamma()), 11);
        check_calc(Calculation::Store(ValueSource::Theta()), 12);
        check_calc(Calculation::Store(ValueSource::Y()), 13);
        check_calc(Calculation::Store(ValueSource::PreviousValue()), 14);
    }

    #[test]
    fn graphevaluator_expr_operations() {
        use VarBack::*;
        // Check expression operations
        let two = || {
            Box::new(ExpressionBack::<Scalar>::Var(Query(QueryBack {
                index: 0,
                column_index: 0,
                column_type: Any::Fixed,
                rotation: Rotation(0),
            })))
        };

        let three = || {
            Box::new(ExpressionBack::<Scalar>::Var(Query(QueryBack {
                index: 0,
                column_index: 0,
                column_type: Any::Fixed,
                rotation: Rotation(1),
            })))
        };

        check_expr(ExpressionBack::Sum(two(), three()), 5);
        check_expr(ExpressionBack::Product(two(), three()), 6);
        check_expr(
            ExpressionBack::Sum(ExpressionBack::Negated(two()).into(), three()),
            1,
        );
    }

    #[test]
    fn graphevaluator_calc_operations() {
        // Check calculation operations
        let two = || ValueSource::Fixed(0, 0);
        let three = || ValueSource::Fixed(0, 1);

        check_calc(Calculation::Add(two(), three()), 5);
        check_calc(Calculation::Double(two()), 4);
        check_calc(Calculation::Mul(two(), three()), 6);
        check_calc(Calculation::Square(three()), 9);
        check_calc(Calculation::Negate(two()), -2);
        check_calc(Calculation::Sub(three(), two()), 1);
        check_calc(
            Calculation::Horner(two(), vec![three(), two()], three()),
            2 + 3 * 3 + 2 * 9,
        );
    }
}
