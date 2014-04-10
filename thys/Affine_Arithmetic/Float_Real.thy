header {* Dyadic Rational Representation of Real *}
theory Float_Real
imports
  "~~/src/HOL/Library/Float"
begin
text {* \label{sec:floatreal} *}

definition Floatreal :: "float \<Rightarrow> real" where "Floatreal = real_of_float"

lemma Floatreal_real[simp]: "Floatreal = real"
  by (simp add: Floatreal_def real_of_float_def)

code_datatype Floatreal

abbreviation
  float_of_nat :: "nat \<Rightarrow> float"
where
  "float_of_nat \<equiv> of_nat"

abbreviation
  float_of_int :: "int \<Rightarrow> float"
where
  "float_of_int \<equiv> of_int"

text{* Collapse nested embeddings *}

lemma Floatreal_of_nat_eq [simp]: "Floatreal (float_of_nat n) = of_nat n"
by (induct n) simp_all

lemma real_of_float_of_nat_eq: "real (of_nat n :: float) = real n"
  using Floatreal_of_nat_eq
  by (simp add: real_of_nat_def)

lemma real_of_float_of_int_eq: "real (float_of_int z) = of_int z"
  by (cases z rule: int_diff_cases) (simp_all add: of_rat_diff real_of_nat_def real_of_float_of_nat_eq)

text {* Operations *}

text {* Undo code setup for @{term Ratreal}. *}

lemma of_rat_numeral_eq [code_abbrev]:
  "Floatreal (numeral w) = Ratreal (numeral w)"
  by simp

lemma zero_real_code [code]:
  "0 = Floatreal 0"
  by simp

lemma one_real_code [code]:
  "1 = Floatreal 1"
  by simp

lemma [code_abbrev]:
  "(Floatreal (of_int a) :: real) = (Ratreal (Rat.of_int a) :: real)"
  by (auto simp: Rat.of_int_def real_of_float_of_int_eq)

lemma [code_abbrev]:
  "Floatreal 0 \<equiv> Ratreal 0"
  by simp

lemma [code_abbrev]:
  "Floatreal 1 = Ratreal 1"
  by simp

lemmas compute_real_of_float[code del]

lemmas [code del] =
  real_equal_code
  real_less_eq_code
  real_less_code
  real_plus_code
  real_times_code
  real_uminus_code
  real_minus_code
  real_inverse_code
  real_divide_code
  real_floor_code

lemma real_equal_code [code]:
  "HOL.equal (Floatreal x) (Floatreal y) \<longleftrightarrow> HOL.equal x y"
  by (metis (poly_guards_query) Floatreal_real equal float_of_real)

abbreviation FloatR::"int\<Rightarrow>int\<Rightarrow>real" where
  "FloatR a b \<equiv> Floatreal (Float a b)"

lemma real_less_eq_code' [code]: "Floatreal x \<le> Floatreal y \<longleftrightarrow> x \<le> y"
  and real_less_code' [code]: "Floatreal x < Floatreal y \<longleftrightarrow> x < y"
  and real_plus_code' [code]: "Floatreal x + Floatreal y = Floatreal (x + y)"
  and real_times_code' [code]: "Floatreal x * Floatreal y = Floatreal (x * y)"
  and real_uminus_code' [code]: "- Floatreal x = Floatreal (- x)"
  and real_minus_code' [code]: "Floatreal x - Floatreal y = Floatreal (x - y)"
  and real_inverse_code' [code]: "inverse (Floatreal x) =
    (if x = 2 then FloatR 1 (-1) else
    Code.abort (STR ''inverse not of 2'') (\<lambda>_. inverse (Floatreal x)))"
  and real_divide_code' [code]: "FloatR a b / Floatreal y =
    (if y = 2 then if a mod 2 = 0 then FloatR (a div 2) b else FloatR a (b - 1) else
    Code.abort (STR ''division not by 2'') (\<lambda>_. FloatR a b / Floatreal y))"
  and real_floor_code' [code]: "floor (Floatreal x) = int_floor_fl x"
  and real_abs_code' [code]: "abs (Floatreal x) = Floatreal (abs x)"
  by (auto simp add: int_floor_fl.rep_eq powr_divide2[symmetric] powr_minus)

lemma compute_round_down[code]: "round_down prec (Floatreal f) = Floatreal (float_down prec f)"
  by simp

lemma compute_round_up[code]: "round_up prec (Floatreal f) = Floatreal (float_up prec f)"
  by simp

lemma compute_truncate_down[code]: "truncate_down prec (Floatreal f) = Floatreal (float_round_down prec f)"
  by (simp add: Float.float_round_down.rep_eq truncate_down_def)

lemma compute_truncate_up[code]: "truncate_up prec (Floatreal f) = Floatreal (float_round_up prec f)"
  by (simp add: float_round_up.rep_eq truncate_up_def)

lemma [code]: "real_divl p (Floatreal x) (Floatreal y) = Floatreal (float_divl p x y)"
  by (simp add: float_divl.rep_eq real_divl_def)

lemma [code]: "real_divr p (Floatreal x) (Floatreal y) = Floatreal (float_divr p x y)"
  by (simp add: float_divr.rep_eq real_divr_def)

end
