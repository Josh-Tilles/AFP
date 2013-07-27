(*============================================================================================*)
(* Properties about Rounding Errors.                                                          *)
(*============================================================================================*)

(* Author: Lei Yu, University of Cambridge *)

theory RoundError imports IEEE FloatProperty begin

subsection{*Properties about Rounding Errors.*}

definition error :: "real \<Rightarrow> real" where
"error x = Val(Abs_float(round float_format To_nearest x)) - x" 

lemma bound_at_worst_lemma: 
  fixes a x
  assumes threshold: "abs x < threshold float_format"
  assumes finite: "is_finite float_format a"
  shows "abs (valof float_format (round float_format To_nearest x) - x) \<le>
         abs (valof float_format a - x)"
proof -
  have "round float_format To_nearest x = 
        closest (valof float_format)  (\<lambda>a. even (fraction a)) {a. is_finite float_format a} x"
    using threshold by (metis abs_less_iff le_minus_iff not_less round.simps(1))
  then have "is_closest (valof float_format) {a. is_finite float_format a} x 
            (round float_format To_nearest x)" using closest_is_closest 
    by (metis is_finite_finite is_finite_nonempty)
  then show ?thesis using finite is_closest_def by (metis mem_Collect_eq)
qed

lemma error_at_worst_lemma:
  fixes a x
  assumes "abs x < threshold float_format"
  assumes "Finite a"
  shows "abs(error x) \<le> abs(Val a - x) "
proof -
  have "Finite a = is_finite float_format (Rep_float a)" using is_valid_defloat 
    by (metis Finite_def Isdenormal_def Isnormal_def Iszero_def is_finite_def)
  then have "abs(valof float_format (Rep_float(Abs_float(round float_format To_nearest x))) - x)
             \<le> abs (valof float_format (Rep_float a) - x)" using bound_at_worst_lemma assms
    by (metis defloat_float_round)
  then show ?thesis by (metis Val_def error_def)
qed

lemma error_is_zero:
  fixes a x
  assumes "Finite a"
  assumes "Val a = x"
  shows "error x = (0::real)"
proof -
  have "abs x < threshold float_format" using float_val_gt_threshold float_val_lt_threshold assms
    by (metis abs_less_iff minus_less_iff)
  then show ?thesis using error_at_worst_lemma assms
    by (metis abs_le_zero_iff abs_zero diff_self)
qed

lemma valof_scale_up:
  fixes s e k f
  assumes "e \<noteq> 0"
  shows "valof float_format (s::nat, e + k, f) = 2^k * valof float_format (s, e, f)"
using assms
apply auto
by (metis nat_add_commute power_add)

lemma is_finite_zerosign:
  fixes a s x
  assumes "s = (0::nat) \<or> s = 1"
  assumes "is_finite float_format a"
  shows "is_finite float_format (zerosign float_format s a)"
using assms
by (metis exponent.simps fraction.simps is_finite_def is_zero_def 
    minus_zero_def plus_zero_def zerosign_def zerosign_valid)

lemma defloat_float_zerosign_round_finite:
  fixes b x
  assumes threshold: "abs x < threshold float_format"
  assumes b: "b = 0 \<or> b = 1"
  shows "is_finite float_format (Rep_float(Abs_float 
         (zerosign float_format b (round float_format To_nearest x))))"
proof -
  have "round float_format To_nearest x = 
        (closest (valof float_format) (\<lambda>a. even (fraction a)) {a. is_finite float_format a} x)"
    using threshold by (metis (full_types) abs_less_iff leD le_minus_iff round.simps(1))
  then have "is_finite float_format (round float_format To_nearest x) "
    by (metis is_finite_closest)
  then have "is_finite float_format (zerosign float_format b (round float_format To_nearest x))"
    using b is_finite_zerosign by auto
  then show ?thesis by (metis b defloat_float_zerosign_round)
qed

lemma signzero_zero: "is_zero float_format a \<Longrightarrow> 
      valof float_format (zerosign float_format s a) = 0"
apply (auto simp add: zerosign_def)
done

lemma val_zero: "is_zero float_format a \<Longrightarrow> 
      valof float_format a = 0"
apply (cases a)
apply (auto simp add: is_zero_def)
done

lemma float_add:
  fixes a b
  assumes finite_a: "Finite a" and finite_b: "Finite b" 
  assumes threshold: "abs (Val a + Val b) < threshold float_format"
  shows "Finite (a + b) \<and> (Val (a + b) = Val a + Val b + error (Val a + Val b))"
proof-
  have val_threshold: "(valof float_format (Rep_float a)) + (valof float_format (Rep_float b)) < 
    threshold float_format" using threshold by auto
  moreover have "\<not>Isnan a \<and> \<not>Isnan b" using finite_a finite_b by (metis float_distinct_finite)
  moreover have "\<not>Infinity a \<and> \<not>Infinity b" using finite_a finite_b
    by (metis float_distinct_finite)
  ultimately have ab:"(a + b) = Abs_float (zerosign float_format 
    (if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float b) \<and>
        (sign (Rep_float a) = sign (Rep_float b)) 
     then sign (Rep_float a) else 0)
        (round float_format To_nearest (valof float_format (Rep_float a) + 
        valof float_format (Rep_float b))))" using finite_a finite_b 
    by (auto simp add: fadd_def  plus_float_def)
  moreover have sign01: "(if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float b) \<and>
        (sign (Rep_float a) = sign (Rep_float b)) 
     then sign (Rep_float a) else 0) = 0 \<or> 
     (if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float b) \<and>
        (sign (Rep_float a) = sign (Rep_float b)) 
     then sign (Rep_float a) else 0) = 1" using sign_0_1 by (metis is_valid_defloat)
  moreover have "abs (valof float_format (Rep_float a) + 
        valof float_format (Rep_float b)) < threshold float_format" using threshold by auto
  ultimately have finite_ab: "is_finite float_format (Rep_float(Abs_float (zerosign float_format 
        (if is_zero float_format (Rep_float a) \<and> 
            is_zero float_format (Rep_float b) \<and>
            (sign (Rep_float a) = sign (Rep_float b)) 
         then sign (Rep_float a) else 0)
            (round float_format To_nearest (valof float_format (Rep_float a) + 
            valof float_format (Rep_float b))))))" using defloat_float_zerosign_round_finite
    by auto
  then have  "is_finite float_format (Rep_float(a + b))" by (metis ab)
  then have  "Finite (a + b)" 
    by (metis Finite_def Isdenormal_def Isnormal_def Iszero_def is_finite_def)
  have "Val (a + b) = 
    valof float_format (Rep_float(Abs_float (zerosign float_format 
    (if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float b) \<and>
        (sign (Rep_float a) = sign (Rep_float b)) 
     then sign (Rep_float a) else 0)
        (round float_format To_nearest (valof float_format (Rep_float a) + 
        valof float_format (Rep_float b))))))" by (metis Val_def ab)
  also have "... = 
    valof float_format (zerosign float_format 
    (if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float b) \<and>
        (sign (Rep_float a) = sign (Rep_float b)) 
     then sign (Rep_float a) else 0)
        (round float_format To_nearest (valof float_format (Rep_float a) + 
        valof float_format (Rep_float b)))) " using defloat_float_zerosign_round sign01 by auto
  finally have val_ab: "Val (a + b) = valof float_format (zerosign float_format 
    (if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float b) \<and>
        (sign (Rep_float a) = sign (Rep_float b)) 
     then sign (Rep_float a) else 0)
        (round float_format To_nearest (valof float_format (Rep_float a) + 
        valof float_format (Rep_float b))))" .
  have zero: "is_zero float_format (round float_format To_nearest 
    (valof float_format (Rep_float a) + valof float_format (Rep_float b))) \<Longrightarrow> 
    (Val (a + b) = Val a + Val b + error (Val a + Val b))" 
    proof -
      assume assm: 
        "is_zero float_format (round float_format To_nearest (valof float_format (Rep_float a) + 
                     valof float_format (Rep_float b)))"
      then have ab0: "Val (a + b) = 0"  by (metis signzero_zero val_ab)
      have "Val a + Val b + error (Val a + Val b) = 
         valof float_format (round float_format To_nearest (valof float_format (Rep_float a) + 
         valof float_format (Rep_float b)))" using error_def assm 
         by (metis Val_def ab_group_add_class.add_diff_cancel_left
           comm_monoid_add_class.add.right_neutral defloat_float_round diff_add_cancel )
      then have "Val a + Val b + error (Val a + Val b) = 0" using assm  by (metis val_zero)
      then show ?thesis using ab0 by auto
    qed
  have not_zero: "\<not>is_zero float_format (round float_format To_nearest 
    (valof float_format (Rep_float a) + valof float_format (Rep_float b))) \<Longrightarrow> 
    (Val (a + b) = Val a + Val b + error (Val a + Val b))"
    proof -
      assume assm: "\<not>is_zero float_format (round float_format To_nearest 
        (valof float_format (Rep_float a) + valof float_format (Rep_float b)))"
      have "Val (a + b) = valof float_format (zerosign float_format 
        (if is_zero float_format (Rep_float a) \<and> is_zero float_format (Rep_float b) \<and>
            (sign (Rep_float a) = sign (Rep_float b)) 
         then sign (Rep_float a) else 0)
            (round float_format To_nearest (valof float_format (Rep_float a) + 
            valof float_format (Rep_float b)))) " using val_ab by auto
      also have "... = valof float_format (round float_format To_nearest 
        (valof float_format (Rep_float a) + 
        valof float_format (Rep_float b)))" using zerosign_def by (metis assm)
      also have "... = Val a + Val b + error (Val a + Val b)" using error_def 
        by (metis Val_def comm_semiring_1_class.normalizing_semiring_rules(24) 
        defloat_float_round diff_add_cancel)
      finally show ?thesis .
    qed
  then have "(Val (a + b) = Val a + Val b + error (Val a + Val b))" using zero by metis
  thus ?thesis by (metis `Finite (a + b)`) 
qed
       
lemma float_sub:
  fixes a b
  assumes finite_a: "Finite a" and finite_b: "Finite b" 
  assumes threshold: "abs (Val a - Val b) < threshold float_format"
  shows "Finite (a - b) \<and> (Val (a - b) = Val a - Val b + error (Val a - Val b))"
proof-
  have val_threshold: "(valof float_format (Rep_float a)) - (valof float_format (Rep_float b)) < 
    threshold float_format" using threshold by auto
  moreover have "\<not>Isnan a \<and> \<not>Isnan b" using finite_a finite_b by (metis float_distinct_finite)
  moreover have "\<not>Infinity a \<and> \<not>Infinity b" using finite_a finite_b
    by (metis float_distinct_finite)
  ultimately have ab:"(a - b) = Abs_float (zerosign float_format 
    (if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float b) \<and>
        (sign (Rep_float a) \<noteq> sign (Rep_float b)) 
     then sign (Rep_float a) else 0)
        (round float_format To_nearest (valof float_format (Rep_float a) - 
        valof float_format (Rep_float b))))" using finite_a finite_b 
    by (auto simp add: fsub_def minus_float_def)
   moreover have sign01: "(if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float b) \<and>
        (sign (Rep_float a) \<noteq> sign (Rep_float b)) 
     then sign (Rep_float a) else 0) = 0 \<or> 
     (if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float b) \<and>
        (sign (Rep_float a) \<noteq> sign (Rep_float b)) 
     then sign (Rep_float a) else 0) = 1" using sign_0_1 by (metis is_valid_defloat)
  moreover have "abs (valof float_format (Rep_float a) - 
        valof float_format (Rep_float b)) < threshold float_format" using threshold by auto
  ultimately have "is_finite float_format (Rep_float(a - b))" 
    using defloat_float_zerosign_round_finite by auto
  then have "Finite (a - b)" 
    by (metis Finite_def Isdenormal_def Isnormal_def Iszero_def is_finite_def)
  have "Val (a - b) = 
    valof float_format (Rep_float(Abs_float (zerosign float_format 
    (if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float b) \<and>
        (sign (Rep_float a) \<noteq> sign (Rep_float b)) 
     then sign (Rep_float a) else 0)
        (round float_format To_nearest (valof float_format (Rep_float a) - 
        valof float_format (Rep_float b))))))" by (metis Val_def ab)
  also have "... = 
    valof float_format (zerosign float_format 
    (if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float b) \<and>
        (sign (Rep_float a) \<noteq> sign (Rep_float b)) 
     then sign (Rep_float a) else 0)
        (round float_format To_nearest (valof float_format (Rep_float a) - 
        valof float_format (Rep_float b)))) " using defloat_float_zerosign_round sign01 by auto
  finally have val_ab: "Val (a - b) = valof float_format (zerosign float_format 
    (if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float b) \<and>
        (sign (Rep_float a) \<noteq> sign (Rep_float b)) 
     then sign (Rep_float a) else 0)
        (round float_format To_nearest (valof float_format (Rep_float a) - 
        valof float_format (Rep_float b))))" .
  have zero: "is_zero float_format (round float_format To_nearest 
    (valof float_format (Rep_float a) - valof float_format (Rep_float b))) \<Longrightarrow> 
    (Val (a - b) = Val a - Val b + error (Val a - Val b))" 
    proof -
      assume assm: 
        "is_zero float_format (round float_format To_nearest (valof float_format (Rep_float a) - 
         valof float_format (Rep_float b)))"
      then have ab0: "Val (a - b) = 0" using val_ab by (metis signzero_zero)
      have "Val a - Val b + error (Val a - Val b) = 
        valof float_format (round float_format To_nearest (valof float_format (Rep_float a) - 
        valof float_format (Rep_float b)))" using error_def assm
        by (metis Val_def comm_semiring_1_class.normalizing_semiring_rules(24) 
          defloat_float_round diff_add_cancel)
      then have "Val a - Val b + error (Val a - Val b) = 0" using assm  by (metis val_zero)
      then show ?thesis using ab0 by auto
    qed
  have not_zero: "\<not>is_zero float_format (round float_format To_nearest 
    (valof float_format (Rep_float a)  -  valof float_format (Rep_float b))) \<Longrightarrow> 
    (Val (a - b) = Val a - Val b + error (Val a - Val b))"
    proof -
      assume assm: "\<not>is_zero float_format (round float_format To_nearest 
        (valof float_format (Rep_float a) - valof float_format (Rep_float b)))"
      have "Val (a - b) = valof float_format (zerosign float_format 
        (if is_zero float_format (Rep_float a) \<and> is_zero float_format (Rep_float b) \<and>
            (sign (Rep_float a) \<noteq> sign (Rep_float b)) 
        then sign (Rep_float a) else 0)
            (round float_format To_nearest (valof float_format (Rep_float a) - 
            valof float_format (Rep_float b)))) " using val_ab by auto
       also have "... = valof float_format (round float_format To_nearest 
         (valof float_format (Rep_float a) - valof float_format (Rep_float b)))" 
         using zerosign_def by (metis assm)
       also have "... = Val a - Val b + error (Val a - Val b)" using error_def 
         by (metis Val_def ab_group_add_class.add_diff_cancel_left 
           ab_semigroup_add_class.add_ac(1) add_diff_add add_diff_cancel 
           defloat_float_round diff_add_cancel)
       finally show ?thesis .
     qed
  then have "(Val (a - b) = Val a - Val b + error (Val a - Val b))" using zero by metis
  thus ?thesis by (metis `Finite (a - b)`) 
qed      

lemma float_mul:
  fixes a b
  assumes finite_a: "Finite a" and finite_b: "Finite b" 
  assumes threshold: "abs (Val a * Val b) < threshold float_format"
  shows "Finite (a * b) \<and> (Val (a * b) = Val a * Val b + error (Val a * Val b))"
proof-
  have val_threshold: "(valof float_format (Rep_float a)) * (valof float_format (Rep_float b)) < 
    threshold float_format" using threshold by auto
  moreover have "\<not>Isnan a \<and> \<not>Isnan b" using finite_a finite_b by (metis float_distinct_finite)
  moreover have "\<not>Infinity a \<and> \<not>Infinity b" using finite_a finite_b
    by (metis float_distinct_finite)
  ultimately have ab:"(a * b) = Abs_float (zerosign float_format (
    if sign (Rep_float a) = sign (Rep_float b) then 0 else 1)
    (round float_format To_nearest (valof float_format (Rep_float a) * 
    valof float_format (Rep_float b))))"  using finite_a finite_b 
    by (auto simp add: fmul_def times_float_def)
  moreover have sign01: "(
    if sign (Rep_float a) = sign (Rep_float b) then 0 else 1) = 0 \<or> 
    (if sign (Rep_float a) = sign (Rep_float b) then 0 else 1) = 1" using sign_0_1
    by auto
  moreover have "abs (valof float_format (Rep_float a) * 
        valof float_format (Rep_float b)) < threshold float_format" using threshold by auto
  ultimately have "is_finite float_format (Rep_float(a * b))" 
    using defloat_float_zerosign_round_finite by auto
  then have "Finite (a * b)" 
    by (metis Finite_def Isdenormal_def Isnormal_def Iszero_def is_finite_def)
  have "Val (a * b) = 
   valof float_format (Rep_float(Abs_float(zerosign float_format 
        (if (sign (Rep_float a) = sign (Rep_float b)) then 0 else 1)
        (round float_format To_nearest (valof float_format (Rep_float a) * 
        valof float_format (Rep_float b))))))" by (metis Val_def ab)
  also have "... = 
    valof float_format (zerosign float_format 
        (if (sign (Rep_float a) = sign (Rep_float b)) then 0 else 1)
        (round float_format To_nearest (valof float_format (Rep_float a) * 
        valof float_format (Rep_float b)))) " using defloat_float_zerosign_round sign01 by auto
  finally have val_ab: "Val (a * b) = valof float_format  (zerosign float_format 
        (if (sign (Rep_float a) = sign (Rep_float b)) then 0 else 1)
        (round float_format To_nearest (valof float_format (Rep_float a) * 
        valof float_format (Rep_float b))))" .
  have zero: "is_zero float_format (round float_format To_nearest 
    (valof float_format (Rep_float a) * valof float_format (Rep_float b))) \<Longrightarrow> 
    (Val (a * b) = Val a * Val b + error (Val a * Val b))" 
    proof -
      assume assm: 
        "is_zero float_format (round float_format To_nearest (valof float_format (Rep_float a) * 
         valof float_format (Rep_float b)))"
      then have ab0: "Val (a * b) = 0" using val_ab by (metis signzero_zero)
      have "Val a * Val b + error (Val a * Val b) = 
        valof float_format (round float_format To_nearest (valof float_format (Rep_float a) * 
        valof float_format (Rep_float b)))" using error_def assm
        by (metis Val_def comm_semiring_1_class.normalizing_semiring_rules(24) 
        defloat_float_round diff_add_cancel)
      then have "Val a * Val b + error (Val a * Val b) = 0" using assm  by (metis val_zero)
      then show ?thesis using ab0 by auto
    qed
  have not_zero: "\<not>is_zero float_format (round float_format To_nearest 
    (valof float_format (Rep_float a) * valof float_format (Rep_float b))) \<Longrightarrow> 
    (Val (a * b) = Val a * Val b + error (Val a * Val b))"
    proof -
      assume assm: "\<not>is_zero float_format (round float_format To_nearest 
        (valof float_format (Rep_float a) * valof float_format (Rep_float b)))"
      have "Val (a * b) = valof float_format (zerosign float_format (if 
        (sign (Rep_float a) = sign (Rep_float b)) then 0 else 1)
        (round float_format To_nearest (valof float_format (Rep_float a) * 
        valof float_format (Rep_float b)))) " using val_ab by auto
      also have "... = valof float_format (round float_format To_nearest 
        (valof float_format (Rep_float a) * 
        valof float_format (Rep_float b)))" using zerosign_def 
        by (metis signzero_zero val_zero)
      also have "... = Val a * Val b + error (Val a * Val b)" using error_def 
        by (metis Val_def comm_semiring_1_class.normalizing_semiring_rules(24) 
        defloat_float_round diff_add_cancel)
      finally show ?thesis .
    qed
  then have "(Val (a * b) = Val a * Val b + error (Val a * Val b))" using zero
     by metis
  thus ?thesis by (metis `Finite (a * b)`) 
qed


lemma float_div:
  fixes a b
  assumes finite_a: "Finite a" and finite_b: "Finite b"
  assumes not_zero: "\<not>Iszero b"
  assumes threshold: "abs (Val a / Val b) < threshold float_format"
  shows "Finite (a / b) \<and> (Val (a / b) = Val a / Val b + error (Val a / Val b))"
proof-
  have val_threshold: "(valof float_format (Rep_float a)) / (valof float_format (Rep_float b)) < 
    threshold float_format" using threshold not_zero by (metis Val_def abs_less_iff)
  moreover have ab:"(a / b) = Abs_float (zerosign float_format 
    (if sign (Rep_float a) = sign (Rep_float b) then 0 else 1)
    (round float_format To_nearest (valof float_format (Rep_float a) / 
     valof float_format (Rep_float b))))"  using finite_a finite_b 
    by (metis Iszero_def divide_float_def fdiv_def finite_infinity finite_nan not_zero)
  moreover have sign01: "(
    if sign (Rep_float a) = sign (Rep_float b) then 0 else 1) = 0 \<or> 
    (if sign (Rep_float a) = sign (Rep_float b) then 0 else 1) = 1" using sign_0_1
    by auto
  moreover have "abs (valof float_format (Rep_float a) / 
        valof float_format (Rep_float b)) < threshold float_format" using threshold by auto
  ultimately have "is_finite float_format (Rep_float(a / b))" 
    using defloat_float_zerosign_round_finite by auto
  then have "Finite (a / b)" 
    by (metis Finite_def Isdenormal_def Isnormal_def Iszero_def is_finite_def)
  have "Val (a / b) = 
   valof float_format (Rep_float(Abs_float(zerosign float_format 
        (if (sign (Rep_float a) = sign (Rep_float b)) then 0 else 1)
        (round float_format To_nearest (valof float_format (Rep_float a) / 
        valof float_format (Rep_float b))))))" by (metis Val_def ab)
  also have "... = 
    valof float_format (zerosign float_format 
        (if (sign (Rep_float a) = sign (Rep_float b)) then 0 else 1)
        (round float_format To_nearest (valof float_format (Rep_float a) / 
        valof float_format (Rep_float b)))) " using defloat_float_zerosign_round sign01 by auto
  finally have val_ab: "Val (a / b) = valof float_format  (zerosign float_format 
        (if (sign (Rep_float a) = sign (Rep_float b)) then 0 else 1)
        (round float_format To_nearest (valof float_format (Rep_float a) / 
        valof float_format (Rep_float b))))" .
  have zero: "is_zero float_format (round float_format To_nearest 
    (valof float_format (Rep_float a) / valof float_format (Rep_float b))) \<Longrightarrow> 
    (Val (a / b) = Val a / Val b + error (Val a / Val b))" 
    proof -
      assume assm: 
        "is_zero float_format (round float_format To_nearest (valof float_format (Rep_float a) / 
         valof float_format (Rep_float b)))"
      then have ab0: "Val (a / b) = 0" using val_ab by (metis signzero_zero)
      have "Val a / Val b + error (Val a / Val b) = 
        valof float_format (round float_format To_nearest (valof float_format (Rep_float a) / 
        valof float_format (Rep_float b)))" using error_def assm
        by (metis Val_def comm_semiring_1_class.normalizing_semiring_rules(24) 
        defloat_float_round diff_add_cancel)
      then have "Val a / Val b + error (Val a / Val b) = 0" using assm  by (metis val_zero)
      then show ?thesis using ab0 by auto
    qed
  have not_zero: "\<not>is_zero float_format (round float_format To_nearest 
    (valof float_format (Rep_float a) /  valof float_format (Rep_float b))) \<Longrightarrow> 
    (Val (a / b) = Val a / Val b + error (Val a / Val b))"
    proof -
      assume assm: "\<not>is_zero float_format (round float_format To_nearest 
        (valof float_format (Rep_float a) / valof float_format (Rep_float b)))"
      have "Val (a / b) = valof float_format (zerosign float_format 
        (if (sign (Rep_float a) = sign (Rep_float b)) then 0 else 1)
        (round float_format To_nearest (valof float_format (Rep_float a) / 
        valof float_format (Rep_float b)))) " using val_ab by auto 
      also have "... = valof float_format (round float_format To_nearest 
        (valof float_format (Rep_float a) / valof float_format (Rep_float b)))" using zerosign_def 
        by (metis signzero_zero val_zero)
      also have "... = Val a / Val b + error (Val a / Val b)" using error_def 
        by (metis Val_def comm_semiring_1_class.normalizing_semiring_rules(24) 
        defloat_float_round diff_add_cancel)
      finally show ?thesis .
    qed
  then have "(Val (a / b) = Val a / Val b + error (Val a / Val b))" using zero by metis
  thus ?thesis by (metis `Finite (a / b)`) 
qed

(***************"1 + Epsilon" property**************)
definition normalizes :: "real \<Rightarrow> bool" where
"normalizes x = (1/ (2::real)^(bias float_format - 1) \<le> abs x \<and> abs x < threshold float_format)"

end
