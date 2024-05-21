use crate::plonk::Expression;
use halo2_middleware::ff::{Field};
use std::fmt::{self, Debug};
use std::collections::HashMap;

/// Expressions involved in a lookup argument, with a name as metadata.
/// Different from halo2 lookup: table_expressions are just
/// Vector of cache_ids, cq_table columns not allowed to participate
/// in any expression.
#[derive(Clone)]
pub struct Argument<F: Field> {
    pub(crate) name: String,
    pub(crate) input_expressions: Vec<Expression<F>>,
    pub(crate) table_ids: Vec<usize>,
	pub(crate) vec_columns: Vec<Vec<F>>,
	/// map from the vector of table elements in one row to the row idx
	pub(crate) hs_idx: HashMap<Vec<u8>, usize>
}

impl<F: Field> Debug for Argument<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CqArgument")
            .field("input_expressions", &self.input_expressions)
            .field("table_cols", &self.table_ids)
            .finish()
    }
}


#[allow(dead_code)] 
impl<F: Field> Argument<F> {
    /// Constructs a new lookup argument.
    ///
    /// `table_map` is a sequence of `(input, table)` tuples.
	/// NOTE that hs_idx and vec_columns would have to be
	/// set up using set_vec_column and set_hs_idx. Main reasin is that
    pub fn new<S: AsRef<str>>(name: S, table_map: Vec<(Expression<F>, usize)>) -> Self {
	// F should actually be PrimeField here (to allow serialization),
	// but to be backward compatible with halo2 existing code, we took
	// this comparamize.
        let (input_expressions, table_ids): (Vec<Expression<F>>, Vec<usize>)
			= table_map.into_iter().unzip();
		let vec_vals = vec![vec![]; table_ids.len()];
		let hs_idx = HashMap::<Vec<u8>,usize>::new(); //a dummy one
        Argument {
            name: name.as_ref().to_string(),
            input_expressions: input_expressions,
            table_ids: table_ids,
			vec_columns: vec_vals,
			hs_idx: hs_idx,
        }
    }

	/// return the idx of the table_id in table_ids
	/// if not exists, set b_res to false and idx to zero
	pub fn get_table_idx(&self, table_id: usize) -> (bool, usize){
		let mut idx = 0;
		for tbl_id in &self.table_ids{
			if *tbl_id == table_id{ return (true, idx); }
			idx += 1;
		}

		(false, 0)
	}

    pub(crate) fn required_degree(&self) -> usize {
        assert_eq!(self.input_expressions.len(), self.table_ids.len());
        let mut input_degree = 1;
        for expr in self.input_expressions.iter() {
            input_degree = std::cmp::max(input_degree, expr.degree());
        }
        let table_degree = 1; 
        std::cmp::max(
            4,
            2 + input_degree + table_degree,
        )
    }

    /// Returns input of this argument
    pub fn input_expressions(&self) -> &Vec<Expression<F>> {
        &self.input_expressions
    }

    /// Returns table of this argument
    pub fn table_ids(&self) -> &Vec<usize> {
        &self.table_ids
    }

    /// Returns name of this argument
    pub fn name(&self) -> &str {
        &self.name
    }

	/// set up the value of a given (single column) table
	/// b_reset_cache: whether to reload the cache.
	pub fn set_cq_table_value(&mut self, col_id: usize, b_reset_cache: bool,
		vec_vals: Vec<F>){
		let (bres, idx) = self.get_table_idx(col_id);
		if !bres {return;}

		if self.cache_exists(col_id) && !b_reset_cache{
			unimplemented!("load from cache not implemented yet!");
		}else{
			self.vec_columns[idx] = vec_vals;
		}
	}

	/// set up the hash_idx (due to F a general Field not allowing
	/// serilization), the hash table from row to idx has to be
	/// build outside by calling halo2_backend/src/plonk/cq_lookup/zk_cq_nizk::gen_hash_idx_for_tables
	/// similarly when b_reset_cache is false and cache does exist
	/// it loads from cache 
	pub fn set_hash_idx(&mut self, b_reset_cache: bool,
		hash_idx: HashMap<Vec<u8>, usize>){
		if self.cache_exists(self.table_ids[0]) && !b_reset_cache{
			unimplemented!("load from cache not implemented yet!");
		}else{
			self.hs_idx= hash_idx;
		}
	}

	/// check if the cache for table column exists
	pub fn cache_exists(&self, _col_id: usize) -> bool{
		//println!("cache_exists not implemented! return false. col_id: {}", col_id);
		false
	}
}
