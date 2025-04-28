import CMvPolynomial.Basic

/--
  The total degree of the first CMvMonomial < total degree of the second CMvMonomial.
-/
example : grevlex #m[4, 2, 3] #m[4, 7, 1] = .lt := by rfl

/-- the CMonomials are equal -/
example : grevlex #m[4, 2, 3] #m[4, 2, 3] = .eq := by
  unfold grevlex
  simp only [totalDegree, compareOfLessAndEq, Vector.mk_lt_mk, List.lt_toArray]
  decide

/--
  The total degree of the first CMvMonomial = total degree of the second CMvMonomial;
  the power of the first variable "breaks the tie".
-/
example : grevlex #m[4, 1, 3] #m[1, 5, 2] = .lt := by
  unfold grevlex
  simp only [totalDegree, compareOfLessAndEq, Vector.mk_lt_mk, List.lt_toArray]
  decide

/--
  The total degree of the first CMvMonomial = total degree of the second CMvMonomial;
  the power of the third variable "breaks the tie".
-/
example : grevlex #m[4, 1, 3] #m[4, 1, 4] = .lt := by
  unfold grevlex
  simp only [totalDegree, compareOfLessAndEq, Vector.mk_lt_mk, List.lt_toArray]
  decide
/--
  The total degree of the first CMvMonomial = total degree of the second CMvMonomial;
  the power of the third variable "breaks the tie".
-/
example : grevlex #m[4, 1, 3] #m[4, 1, 2] = .gt := by
  unfold grevlex
  simp only [totalDegree, compareOfLessAndEq, Vector.mk_lt_mk, List.lt_toArray]
  decide
