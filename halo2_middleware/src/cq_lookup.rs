use super::circuit::VarMid;
use super::expression::{Expression, Variable};
use ff::Field;
use std::collections::HashMap;
//use std::fmt::{self, Debug};

#[derive(Debug,Clone)]
pub struct Argument<F: Field, V: Variable> {
    pub name: String,
    pub input_expressions: Vec<Expression<F,V>>,
    pub table_ids: Vec<usize>,
	pub vec_columns: Vec<Vec<F>>,
	pub hs_idx: HashMap<Vec<u8>,usize>
}

pub type ArgumentMid<F> = Argument<F, VarMid>;
