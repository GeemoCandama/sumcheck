# The Key to Delegating (Computation)

![Banner: The Key to Delegating](https://github.com/GeemoCandama/sumcheck/blob/main/images/TheKeyToDelegating.jpg)

## Introduction

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;What problems can be delegated to a server or collection of servers and verified by a
client with an efficient proof of correctness? This is an important question that may have just been
[resolved](https://arxiv.org/abs/2001.04383), but in this essay we'll focus on an earlier result in this direction that surpised many computer
scientists. The result lies at the heart of important theoretical advances as well as
practical systems for delegating computation, it's called the Sumcheck Protocol. To explore the details of the protocol we'll focus on a
concrete problem, namely #SAT.

## Interactive Proof Systems

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Let's formalize one class of methods for computation delegation, in particular interactive proof systems. A $k$-message interactive proof system for a language $L$ with completeness $c$ and soundness $s$, consists of a potentially computationally unbounded prover $P$ and a probabilistic polynomial time verifier $V$ that exchange messages to form the transcript. The system is initialized with both $V$ and $P$ receiving the input $x$, then they alternate sending messages to create the transcript $t = (V(r), P)(x) = (m_1, m_2, ..., m_k)$ where $r$ is $V$'s internal randomness and $k$ is the number of messages passed. Following the exchange, $V$ uses $x$, $t$, and $r$ to decide whether to accept (output 1) or reject (output 0). Intuitively, the verifier should accept with high probability when the prover is honest and with low probablity when the prover is not. Formally:  
1. $\forall x \in L$, $Pr[V(x, t, r) = 1] \ge c$  
2. $\forall x \notin L$ and every prover stategy $P', Pr[V(x, t', r) = 1] \leq s$

The complexity class $IP$ is the class of all languages with an interactive proof system with $c = 2/3$ and $s = 1/3$. $IP$ can be viewed as an extension of $NP$, since setting $s = 0$, $c = 1$, $k = 0$ would result in $NP$. Clearly $NP \subseteq IP$, but how much bigger than $NP$ is $IP$? How much do we gain from the addition of interaction and randomness?

## The Problem: #SAT

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;#SAT is a [# $P$](https://en.wikipedia.org/wiki/%E2%99%AFP)-complete problem so specifying an interactive proof system for it would mean that # $P \subseteq IP$. That's exactly what we will accomplish by the end of this essay, but first we should discuss what #SAT is.
#SAT is the problem of counting the number of unique assignments that satisfy a
given boolean function $\phi : \{0, 1\}^n \rightarrow \{0, 1\}$. The answer to #SAT can be written as $\sum_{x\in\{0, 1\}^n} \phi(x)$. If we were to try to compute this sum directly it would cost $O(2^n)$ since $|\{0, 1\}^n| = 2^n$. Even for moderately sized values of $n$ this wouldn't be feasible, as we imagine the verifier to have limited computational resources.  
We’ll model the boolean expressions as a recursive data structure:
```rust
#[derive(Clone)]
pub enum Expr {
    Terminal(usize),
    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
}
```
Evaluating an expression takes advantage of the recursive structure:
```rust
impl Expr {
    pub fn evaluate(&self, vals: &[bool]) -> bool {
        match self {
            Expr::Terminal(t) => vals[*t],
            Expr::And(ref a, ref b) => a.evaluate(vals) && b.evaluate(vals),
            Expr::Or(ref a, ref b) => a.evaluate(vals) || b.evaluate(vals),
            Expr::Not(ref a) => !a.evaluate(vals),
        }
    }
}
```


## Arithmetization

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;One of the main insights from this protocol is the utility of shifting the problem from boolean functions to polynomials over a finite field $\mathbb{F}$. This allows us to exploit the fact that a polynomial with degree $d$ has at most $d$ roots. We can also sample from a large set of elements to ensure that collision-like events are exceedingly rare.
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;For #SAT, we would like to preserve the the property that summing over the boolean hypercube counts the satisfying configurations. We will replace $AND(x, y)$ by $x * y$, $NOT(y)$ by $1 – y$, and $OR(x, y)$ by $1 – (1 – x) * (1 – y)$. For example: $x \land y \vee \bar z = OR(AND(x, y), NOT(z))$ is transformed to $1 - (1 - xy)z$. Notice that this arithmetization method results in a polynomial $p: \mathbb{F}^n \rightarrow \mathbb{F}$, where $n$ is the number of variables in the boolean function.

To evaluate the polynomial at a point we can use:

```rust
impl Expr {
    ...
    // This is equivalent to evaluating the arithmetized polynomial at at point.
    // Doing it this way allows us to avoid calculating all the terms in the 
    // multivariate polynomial resulting from the arithmetization process.
    fn sharp_sat_arithmetization_evaluate_full(&self, vals: &[Fq]) -> Fq {
        let one = Fq::new(BigInt::new([1, 0]));
        match self {
            Expr::Terminal(t) => vals[*t],
            //  AND(x, y) -> x * y
            Expr::And(a, b) => {
                a.sharp_sat_arithmetization_evaluate_full(vals)
                    * b.sharp_sat_arithmetization_evaluate_full(vals)
            }
            // OR(x, y) -> 1 – (1 – x) * (1 – y)
            Expr::Or(a, b) => {
                one - (one - a.sharp_sat_arithmetization_evaluate_full(vals))
                    * (one - b.sharp_sat_arithmetization_evaluate_full(vals))
            }
            // NOT(y) -> 1 – y
            Expr::Not(a) => one - a.sharp_sat_arithmetization_evaluate_full(vals),
        }
    }
}
```

## Using the Sumcheck Protocol

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Let's construct an interactive proof system for #SAT. The Prover and Verifier take the boolean function $\phi : \{0, 1\}^n \rightarrow \{0, 1\}$ as input. Let $p(x_1, x_2, …, x_n)$ be the multivariate polynomial resulting from arithmetizing $\phi$ as described in the previous section. To begin the protocol $P$ sends a value $C_1$ claimed to equal $\sum_{x\in\{0, 1\}^n} p(x)$, which is the answer to the #SAT instance. In the 1st round, $P$ sends $V$ a univariate polynomial claimed to equal:
$$p_1(X_1) = \sum_{x\in\{0, 1\}^{n-1}} p(X_1, x_2, ..., x_n)$$
$V$ then checks that $C_1$ =  $p_1(0) + p_1(1)$ rejecting otherwise.
Next, $V$ sends a random field element $r_1 \in \mathbb{F}$ to $P$.

In the $ith$ round, for $1 < i < n$, $P$ sends to $V$ a univariate polynomial claimed to equal:
$$p_i(X_i) = \sum_{x\in\{0, 1\}^{n-i}} p(r_1, ..., r_{i-1}, X_i, x_{i+1}, ..., x_n)$$
$V$ then checks that $p_{i-1}(r_{i-1})$ = $p_i(0) + p_i(1)$ rejecting otherwise.
Next, $V$ sends a random field element $r_i \in \mathbb{F}$ to $P$.

In the $nth$ round, $P$ sends to $V$ a univariate polynomial claimed to equal:
$$p_n(X_n) = p(r_1, ..., r_{n-1}, X_n)$$
$V$ then checks that $p_{n-1}(r_{n-1})$ = $p_n(0) + p_n(1)$ rejecting otherwise.

Finally, $V$ chooses a random field element $r_n \in \mathbb{F}$ and ensures that $p_n(r_n) = (r_1, …, r_n)$ rejecting otherwise.

If $V$ has not rejected, then $V$ accepts and outputs $1$.

The code follows the above description fairly closely:
```rust
fn sumcheck_protocol(
    prover: &mut dyn SumcheckProver,
    verifier: &mut dyn SumcheckVerifier,
    claimed_sum: Fq,
    num_vars: usize,
) -> bool {
    let mut prior_poly = UniSparsePolynomial::from_coefficients_slice(&[(0, claimed_sum)]);
    // round_num starts at 0 instead of 1
    for round_num in 0..num_vars {
        // Prover calculates the ith_polynomial
        let prover_message = prover.ith_poly_message(round_num);
        // Verifier ensures that the partial sum is valid
        if !verifier.check_prover_message_validity(round_num, &prior_poly, &prover_message) {
            return false;
        }
        // generate random field element
        let cur_rand_el = verifier.generate_and_store_random_field_element(round_num);
        prover.recieve_rand_element(round_num, cur_rand_el);
        // final check
        if round_num == num_vars - 1 {
            if prover_message.evaluate(&cur_rand_el) != verifier.poly_eval() {
                return false;
            }
        } else {
            prior_poly = prover_message;
        }
    }
    true
}
```
I chose to use trait objects to keep the protocol abstracted from our particular problem's details. Rather, the #SAT details are saved for the `HonestSharpSATSumcheckProver` and `SharpSATSumcheckVerifier` types.

```rust
struct HonestSharpSATSumcheckProver {
    bool_form: Expr,
    vals: Vec<Fq>,
    num_vars: usize,
}

impl SumcheckProver for HonestSharpSATSumcheckProver {
    // free_var starts at the 0th variable
    fn ith_poly_message(&mut self, free_var: usize) -> UniSparsePolynomial<Fq> {
        // Initialize the result polynomial
        let mut accumulator_poly =
            UniSparsePolynomial::from_coefficients_slice(&[(0, Fq::new(BigInt::zero()))]);
        let mut cur_var = 0;
        // sum over the n - (free_var + 1) dimensional boolean hypercube 
        for i in 0..2u32.pow((self.num_vars - (free_var + 1)) as u32) {
            // Example format result when n = 5: 3 -> String::from("00011")
            if free_var + 1 < self.num_vars {
                let bits = format!("{i:0n$b}", n = self.num_vars - (free_var + 1));
                for c in bits.chars() {
                    let field_val: Fq;
                    if c == '0' {
                        field_val = Fq::new(BigInt::zero());
                    } else if c == '1' {
                        field_val = Fq::new(BigInt::one());
                    } else {
                        panic!("this shouldnt happen")
                    };

                    self.vals[cur_var + free_var + 1] = field_val;
                    cur_var += 1;
                }
            }
            accumulator_poly = accumulator_poly
                + self
                    .bool_form
                    .sharp_sat_arithmetization_uni(free_var, &self.vals);
            cur_var = 0;
        }

        accumulator_poly
    }

    fn recieve_rand_element(&mut self, round_num: usize, rand_elem: Fq) {
        self.vals.insert(round_num, rand_elem);
    }
}
```

```rust
struct SharpSATSumcheckVerifier {
    rng: ThreadRng,
    bool_form: Expr,
    vals: Vec<Fq>,
}

impl SumcheckVerifier for SharpSATSumcheckVerifier {
    // This is only used for the final check to calculate
    // p(r_1, ..., r_n)
    fn poly_eval(&self) -> Fq {
        self.bool_form
            .sharp_sat_arithmetization_evaluate_full(&self.vals)
    }

    // This method is used every round to check the univariate polynomial that was
    // sent this round
    fn check_prover_message_validity(
        &self,
        round_num: usize,
        prior_poly: &UniSparsePolynomial<Fq>,
        prover_message: &UniSparsePolynomial<Fq>,
    ) -> bool {
        let field_zero = Fq::new(BigInt::zero());

        // This is p_i(0) + p_i(1)
        let prover_partial_sum = prover_message.evaluate(&field_zero) + 
            prover_message.evaluate(&Fq::new(BigInt::one()));
        let prior_evaluation: Fq;
        if round_num == 0 {
            // In the initital round the polynomial is a constant
            prior_evaluation = prior_poly.evaluate(&field_zero); 
        } else {
            match self.vals.get(&(round_num - 1)) {
                Some(val) => {
                    // in the ith round this is p_{i-1}(r_{i-1})
                    prior_evaluation = prior_poly.evaluate(val);
                },
                None => panic!("No value for the index"),
            }
        }
        // check that p_{i-1}(r_{i-1}) = p_i(0) + p_i(1)
        prior_evaluation == prover_partial_sum
    }
    
    // generate and store a random field element r_i in F_p where 
    // p = 170141183460469231731687303715884105727
    fn generate_and_store_random_field_element(&mut self, round_num: usize) -> Fq {
        let rand_field: Fq = self.rng.gen();
        self.vals[round_num] = rand_field;
        rand_field
    }
}
```

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;We never formally specify the multivariate polynomial, because it would have many terms for large $n$. It's sufficient to just be able to evaluate the polynomial at different points. The verifiers running time is polynomial in $n$ and $deg(p)$, since there are $n$ rounds and the polynomial $p_i$ is specified by it's coefficients. $deg(p)$ is the largest number of $AND(x, y)$ or $OR(x)$ operations applied to one particular variable. This is the largest single variable degree.

## Intuition

&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;During initialization the prover sends $C_1$ which is claimed to equal $H$, the sum of $p$ over the $n$-dimensional boolean hypercube. In each round there are two polynomials $m_i(X_i)$ and $p_i(X_i)$, which are the provers claimed polynomial and the desired polynomial respectively.
In the first round, if $C_1 \neq m_1(0) + m_1(1)$ the verifier rejects immediately. On the other hand, if $C_1 = m_1(0) + m_1(1)$ what we'd really like to know is whether $m_1$ is equivalent to $p_1$. Since computing $p_1$ requires $2^{n-1}$ evaluations of $p$, this isn't feasible for the verifier. However, $p_1$ is of the same form as $p$ but with one less variable, so the verifier asks the prover to repeat the previous steps but for $p_1$ instead of $p$ and requires that $C_2 = m_1(r_1)$. This process recursively continues until the final round, when the prover sends $m_n$ which is claimed to equal $p_n(X_n) = p(r_1, ..., r_{n-1}, X_n)$. The verifier can now check $m_n(r_n) \stackrel{?}{=} p_n(r_n)$. For soundness, $Pr[m_n(r_n) = p_n(r_n)| m_n \neq p_n] \leq deg(p)/|\mathbb{F}|$ by the [Schwartz-Zippel Lemma](https://en.wikipedia.org/wiki/Schwartz%E2%80%93Zippel_lemma). At every round the prover could try to cheat by sending $m_i \neq p_i$ and hence the soundness of the whole protocol is $deg(p)n/|\mathbb{F}|$.  
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;Completeness is satisfied, since if the correct $C_1$ and polynomials are sent to the verifier the randomness does not matter. The correct polynomials are constructed such that they satisfy the protocol, so $c = 1$.   
These statements obviously don't pass as proofs, but due to length constraints I'll leave the proofs to the [pros](https://youtu.be/Mw4bVlU_1gU?t=1958).


## Wrapping Up
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;We've constructed an interactive proof system for the #SAT problem. One can pick the size of the field so that the system has a very small soundness error. This shows that # $P \subseteq IP$. The protocol discussed was introduced in the 1992 paper, *Algebraic methods for interactive proof systems*, by Lund, Fortnow, Karloff, and Nisan, the class $IP$ was thought not to be much larger than NP at the time. The ideas of that paper were then applied in clever ways to achieve the result, $IP = PSPACE$. The Sumcheck Protocol lies at the heart of many interactive proof systems including the [GKR protocol](https://dl.acm.org/doi/10.1145/2699436). If you want to see an example of the Sumcheck Protocol applied to #SAT carried out you can see the tests in the [github repo](https://github.com/GeemoCandama/sumcheck).