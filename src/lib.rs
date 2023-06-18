// #SAT arithmetization

// Given a boolean formula with n variables and a polnomailly bounded number S = poly(n)
// of logical operators from the set {||, &&, !}.
// to_poly converts the formula to an n variable polynomial of degree at most 2S. This is
// accomplished through staightforward transformations:
// 1. AND(a, b) to a * b
// 2. NOT(a) to 1 - a
// 3. OR(a, b) to 1 - (1 - a) * (1 - b)
//
// In each case it can be checked that the resulting function extends the boolean function.

// EXAMPLE FORMULAS
//
// x_1 || x_2 || !x_3

// x_1 || (x_2 && !x_3)
// OR(x_1, AND(x_2, !x_3))
