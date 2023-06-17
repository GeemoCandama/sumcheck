use std::collections::HashMap;

use ark_ff::biginteger::BigInt;
use ark_ff::fields::{Fp128, MontBackend};
use ark_poly::polynomial::univariate::SparsePolynomial as UniSparsePolynomial;
use ark_poly::polynomial::Polynomial;

#[derive(ark_ff::MontConfig)]
#[modulus = "170141183460469231731687303715884105727"]
#[generator = "43"]
pub struct FqConfig;
pub type Fq = Fp128<MontBackend<FqConfig, 2>>;

fn main() {
    // Setup prover and Verifier with the boolean function:
    //  x_0 || x_1 && x_2 || !x_3
    let x_0 = Box::new(Expr::Terminal(0));
    let x_1 = Box::new(Expr::Terminal(1));
    let x_2 = Box::new(Expr::Terminal(2));
    let x_3 = Box::new(Expr::Terminal(3));
    let bool_form = 
        Expr::Or(Box::new(Expr::Or(x_0, Box::new(Expr::And(x_1, x_2)))), Box::new(Expr::Not(x_3)));

    let verifier = SharpSATSumcheckVerifier {
        bool_form: bool_form.clone(),
        vals: HashMap::new(),
        num_vars: 4,
        cur_var: 0,
    };

    let mut prover = SharpSATSumcheckProver {
        bool_form,
        vals: HashMap::new(),
        num_vars: 4,
        cur_var: 0,
    };
    
    // Calculate the sum over the boolean hypercube of the arithmetized boolean function
    let answer = prover.calculate_full_sum();

    let is_accepted_by_verifier = sumcheck_protocol(&mut prover, &verifier, answer);
}

fn sumcheck_protocol(
    prover: &mut dyn SumcheckProver,
    verifier: &dyn SumcheckVerifier,
    claimed_sum: Fq,
) -> bool {
    println!("{:?}", prover.ith_poly_message(0));
    true
}

#[derive(Clone)]
pub enum Expr {
    Terminal(usize),
    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
}

impl Expr {
    pub fn evaluate(
        &self, 
        vals: &HashMap<usize, bool>
    ) -> bool {
        match self {
            Expr::Terminal(ref t) => *vals.get(t).unwrap_or(&false),
            Expr::And(ref a, ref b) => a.evaluate(vals) && b.evaluate(vals),
            Expr::Or(ref a, ref b) => a.evaluate(vals) || b.evaluate(vals),
            Expr::Not(ref a) => !a.evaluate(vals),
        }
    }

    fn sharp_sat_arithmetization_evaluate_full(
        &self, 
        vals: &HashMap<usize, Fq>,
    ) -> Fq {
        let one = Fq::new(BigInt::new([1, 0]));
        match self {
            Expr::Terminal(t) => {
                match vals.get(t) {
                    Some(b) => *b,
                    None => panic!("This shouldnt happen"),
                }
            }
            Expr::And(a, b) => {
                a.sharp_sat_arithmetization_evaluate_full(vals)
                    * b.sharp_sat_arithmetization_evaluate_full(vals)
            }
            Expr::Or(a, b) => {
                one - (one - a.sharp_sat_arithmetization_evaluate_full(vals))
                    * (one - b.sharp_sat_arithmetization_evaluate_full(vals))
            }
            Expr::Not(a) => one - a.sharp_sat_arithmetization_evaluate_full(vals),
        }
    }

    // Take the boolean formula and arithmetize leaving a free variable
    // We choose to do this because formally specifying the multivariate
    // polynomial that the boolean formula is extended by requires more time.
    fn sharp_sat_arithmetization_uni(
        &self,
        free_var: usize,
        vals: &HashMap<usize, Fq>,
    ) -> UniSparsePolynomial<Fq> {
        let one = Fq::new(BigInt::one());
        match self {
            Expr::Terminal(t) => {
                if *t == free_var {
                    UniSparsePolynomial::from_coefficients_slice(&[(1, one)])
                } else {
                    match vals.get(t) {
                        Some(b) => 
                            UniSparsePolynomial::from_coefficients_slice(&[(0, *b)]),
                        None => panic!("This shouldnt happen"),
                    }
                }
            }
            Expr::And(a, b) => a
                .sharp_sat_arithmetization_uni(free_var, vals)
                .mul(&b.sharp_sat_arithmetization_uni(free_var, vals)),
            Expr::Not(a) => {
                UniSparsePolynomial::from_coefficients_slice(&[(0, one)])
                    + -a.sharp_sat_arithmetization_uni(free_var, vals)
            }
            Expr::Or(a, b) => {
                let one_poly = UniSparsePolynomial::from_coefficients_slice(&[(0, one)]);
                one_poly.clone()
                    + -(one_poly.clone() + -a.sharp_sat_arithmetization_uni(free_var, vals))
                        .mul(&(one_poly + -b.sharp_sat_arithmetization_uni(free_var, vals)))
            }
        }
    }
}

trait SumcheckProver {
    fn ith_poly_message(&mut self, free_var: usize) -> UniSparsePolynomial<Fq>;
}

struct SharpSATSumcheckProver {
    bool_form: Expr,
    vals: HashMap<usize, Fq>,
    num_vars: usize,
    cur_var: usize,
}

impl SharpSATSumcheckProver {
    fn calculate_full_sum(&self) -> Fq {
        let mut field_vals: HashMap<usize, Fq> = HashMap::new();

        // iterate over the boolean hypercube
        let mut cur_var = 0;
        // Note: true -> BigInt[1,0], false -> BigInt[0, 0]
        let mut arithmetized_sum = Fq::new(BigInt::new([0, 0]));
        for i in 0..2u32.pow(self.num_vars as u32) {
            // Example format result when n = 5: 3 -> String::from("00011")
            let bits = format!("{i:0n$b}", n = self.num_vars as usize);
            for c in bits.chars() {
                let field_val: Fq;
                if c == '0' {
                    field_val = Fq::new(BigInt::zero());
                } else if c == '1' {
                    field_val = Fq::new(BigInt::one());
                } else {
                    panic!("this shouldnt happen")
                };

                field_vals.insert(cur_var, field_val);
                cur_var += 1;
            }
            arithmetized_sum += self.bool_form.sharp_sat_arithmetization_evaluate_full(&field_vals);
            cur_var = 0;
        }
        arithmetized_sum
    }
}

impl SumcheckProver for SharpSATSumcheckProver {
    // free_var starts at the 0th variable 
    // This should probably return result
    fn ith_poly_message(&mut self, free_var: usize) -> UniSparsePolynomial<Fq> {
        let mut accumulator_poly = UniSparsePolynomial::from_coefficients_slice(&[(0, Fq::new(BigInt::zero()))]);
        let mut cur_var = 0;
        for i in 0..2u32.pow((self.num_vars - free_var + 1) as u32) {
            // Example format result when n = 5: 3 -> String::from("00011")
            if free_var + 1 < self.num_vars {
                let bits = format!("{i:0n$b}", n = self.num_vars - free_var + 1);
                for c in bits.chars() {
                    let field_val: Fq;
                    if c == '0' {
                        field_val = Fq::new(BigInt::zero());
                    } else if c == '1' {
                        field_val = Fq::new(BigInt::one());
                    } else {
                        panic!("this shouldnt happen")
                    };

                    self.vals.insert(cur_var + self.cur_var as usize, field_val);
                    cur_var += 1;
                }
            }
            accumulator_poly = accumulator_poly + self.bool_form.sharp_sat_arithmetization_uni(free_var, &self.vals);
            cur_var = 0;
        }

        accumulator_poly
    }
}

trait SumcheckVerifier {
    fn poly_eval(&self, vals: &HashMap<usize, Fq>) -> Fq;
}

struct SharpSATSumcheckVerifier {
    bool_form: Expr,
    vals: HashMap<usize, Fq>,
    num_vars: usize,
    cur_var: usize,
}

impl SumcheckVerifier for SharpSATSumcheckVerifier {
    fn poly_eval(&self, vals: &HashMap<usize, Fq>) -> Fq {
        self.bool_form.sharp_sat_arithmetization_evaluate_full(&self.vals)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // This is a test of the arithmetization of the boolean formula
    #[test]
    fn sum_over_boolean_hypercube_is_equivalent() {
        let zero = Fq::new(BigInt::new([0, 0]));
        let one = Fq::new(BigInt::new([1, 0]));
        // Construct a simple boolean formula x_0 || x_1 || ~x_2
        let x_0 = Expr::Terminal(0);
        let x_1 = Expr::Terminal(1);
        let x_2 = Expr::Terminal(2);
        let n = 3;
        let simple_expression = Expr::Or(
            Box::new(Expr::Or(Box::new(x_0), Box::new(x_1))),
            Box::new(Expr::Not(Box::new(x_2))),
        );
        // These are the initial values. They will change immediately.
        let mut bool_vals: HashMap<usize, bool> = HashMap::new();
        let mut field_vals: HashMap<usize, Fq> = HashMap::new();

        // iterate over the boolean hypercube
        let mut cur_var = 0;
        // Note: true -> BigInt[1,0], false -> BigInt[0, 0]
        let mut bool_form_sum = Fq::new(BigInt::new([0, 0]));
        let mut arithmetized_sum = Fq::new(BigInt::new([0, 0]));
        for i in 0..2u32.pow(n) {
            // Example format result when n = 5: 3 -> String::from("00011")
            let bits = format!("{i:0n$b}", n = n as usize);
            for c in bits.chars() {
                let bool_val: bool;
                let field_val: Fq;
                if c == '0' {
                    bool_val = false;
                    field_val = zero;
                } else if c == '1' {
                    bool_val = true;
                    field_val = one;
                } else {
                    panic!("this shouldnt happen")
                };

                bool_vals.insert(cur_var, bool_val);
                field_vals.insert(cur_var, field_val);
                cur_var += 1;
            }
            bool_form_sum += if simple_expression.evaluate(&bool_vals) {
                Fq::new(BigInt::new([1, 0]))
            } else {
                Fq::new(BigInt::new([0, 0]))
            };
            arithmetized_sum += simple_expression.sharp_sat_arithmetization_evaluate_full(&field_vals);
            cur_var = 0;
        }

        assert_eq!(bool_form_sum, arithmetized_sum);
    }

    #[test]
    fn check_simple_uni_poly() {
        let zero = Fq::new(BigInt::new([0, 0]));
        let one = Fq::new(BigInt::new([1, 0]));
        // Construct a simple boolean formula x_0 || x_1 || ~x_2
        let x_0 = Expr::Terminal(0);
        let x_1 = Expr::Terminal(1);
        let x_2 = Expr::Terminal(2);

        let simple_expression = Expr::Or(
            Box::new(Expr::Or(Box::new(x_0), Box::new(x_1))),
            Box::new(Expr::Not(Box::new(x_2))),
        );
        // These are the initial values. They will change immediately.
        let vals: HashMap<usize, Fq> = [
            (0usize, zero), 
            (1usize, zero), 
            (2usize, one)
        ].into_iter().collect();

        // Its equivalent to the full polynomial with everything except for the 0th variable
        // specified P(X_0, 0, 1)
        let uni_poly = simple_expression.sharp_sat_arithmetization_uni(0, &vals);

        // This is the polynomial f(x) = x
        let x_poly = UniSparsePolynomial::from_coefficients_slice(&[(1, one)]);

        assert_eq!(x_poly, uni_poly);
    }
}
