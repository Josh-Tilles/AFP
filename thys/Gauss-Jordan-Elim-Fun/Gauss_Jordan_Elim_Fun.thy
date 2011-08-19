(*  Gauss-Jordan elimination for matrices represented as functions
    Author: Tobias Nipkow
*)

theory Gauss_Jordan_Elim_Fun
imports Main
begin

text{* Matrices are functions: *}

type_synonym 'a matrix = "nat \<Rightarrow> nat \<Rightarrow> 'a"

text{* In order to restrict to finite matrices, a matrix is usually combined
with one or two natural numbers indicating the maximal row and column of the
matrix.

Gauss-Jordan elimination is parameterized with a natural number @{text
n}. It indicates that the matrix @{text A} has @{text n} rows and columns.
In fact, @{text A} is the augmented matrix with @{text "n+1"} columns. Column
@{text n} is the ``right-hand side'', i.e.\ the constant vector @{text
b}. The result is the unit matrix augmented with the solution in column
@{text n}; see the correctness theorem below. *}

fun gauss_jordan :: "('a::field)matrix \<Rightarrow> nat \<Rightarrow> ('a)matrix option" where
"gauss_jordan A 0 = Some(A)" |
"gauss_jordan A (Suc m) =
 (case dropWhile (\<lambda>i. A i m = 0) [0..<Suc m] of
   [] \<Rightarrow> None |
   p # _ \<Rightarrow>
    (let Ap' = (\<lambda>j. A p j / A p m);
         A' = (\<lambda>i. if i=p then Ap' else (\<lambda>j. A i j - A i m * Ap' j))
     in gauss_jordan (Fun.swap p m A') m))"

text{* Some auxiliary functions: *}

definition solution :: "('a::field)matrix \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" where
"solution A n x = (\<forall>i<n. (\<Sum> j=0..<n. A i j * x j) = A i n)"

definition unit :: "('a::field)matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"unit A m n =
 (\<forall>i j::nat. m\<le>j \<longrightarrow> j<n \<longrightarrow> A i j = (if i=j then 1 else 0))"

lemma solution_swap:
assumes "p1 < n" "p2 < n"
shows "solution (Fun.swap p1 p2 A) n x = solution A n x" (is "?L = ?R")
proof(cases "p1=p2")
  case True thus ?thesis by simp
next
  case False
  show ?thesis
  proof
    assume ?R thus ?L using assms False by(simp add: solution_def swap_def)
  next
   assume ?L
   show ?R
   proof(auto simp: solution_def)
     fix i assume "i<n"
     show "(\<Sum>j = 0..<n. A i j * x j) = A i n"
     proof cases
       assume "i=p1"
       with `?L` assms False show ?thesis
         by(fastsimp simp add: solution_def swap_def)
     next
       assume "i\<noteq>p1"
       show ?thesis
       proof cases
         assume "i=p2"
         with `?L` assms False show ?thesis
           by(fastsimp simp add: solution_def swap_def)
       next
         assume "i\<noteq>p2"
         with `i\<noteq>p1` `?L` `i<n` assms False show ?thesis
           by(fastsimp simp add: solution_def swap_def)
       qed
     qed
   qed
 qed
qed

(* Converting these apply scripts makes them blow up - see above *)

lemma solution_upd1:
  "c \<noteq> 0 \<Longrightarrow> solution (A(p:=(\<lambda>j. A p j / c))) n x = solution A n x"
apply(cases "p<n")
 prefer 2
 apply(simp add: solution_def)
apply(clarsimp simp add: solution_def)
apply rule
 apply clarsimp
 apply(case_tac "i=p")
  apply (simp add: setsum_divide_distrib[symmetric] eq_divide_eq field_simps)
 apply simp
apply (simp add: setsum_divide_distrib[symmetric] eq_divide_eq field_simps)
done

lemma solution_upd_but1: "\<lbrakk> ap = A p; \<forall>i j. i\<noteq>p \<longrightarrow> a i j = A i j; p<n \<rbrakk> \<Longrightarrow>
 solution (\<lambda>i. if i=p then ap else (\<lambda>j. a i j - c i * ap j)) n x =
 solution A n x"
apply(clarsimp simp add: solution_def)
apply rule
 prefer 2
 apply (simp add: field_simps setsum_subtractf setsum_right_distrib[symmetric])
apply(clarsimp)
apply(case_tac "i=p")
 apply simp
apply (auto simp add: field_simps setsum_subtractf setsum_right_distrib[symmetric] all_conj_distrib)
done

text{* The correctness proof: *}

lemma gauss_jordan_lemma: "m\<le>n \<Longrightarrow> unit A m n \<Longrightarrow> gauss_jordan A m = Some B \<Longrightarrow>
  unit B 0 n \<and> solution A n (\<lambda>j. B j n)"
proof(induct m arbitrary: A B)
  case 0
  { fix a and b c d :: "'a"
    have "(if a then b else c) * d = (if a then b*d else c*d)" by simp
  } with 0 show ?case by(simp add: unit_def solution_def setsum_cases)
next
  case (Suc m)
  let "?Ap' p" = "(\<lambda>j. A p j / A p m)"
  let "?A' p" = "(\<lambda>i. if i=p then ?Ap' p else (\<lambda>j. A i j - A i m * ?Ap' p j))"
  from `gauss_jordan A (Suc m) = Some B`
  obtain p ks where "dropWhile (\<lambda>i. A i m = 0) [0..<Suc m] = p#ks" and
    rec: "gauss_jordan (Fun.swap p m (?A' p)) m = Some B"
    by (auto split: list.splits)
  from this have p: "p\<le>m" "A p m \<noteq> 0"
    apply(simp_all add: dropWhile_eq_Cons_conv del:upt_Suc)
    by (metis set_upt atLeast0AtMost atLeastLessThanSuc_atLeastAtMost atMost_iff in_set_conv_decomp)
  have "m\<le>n" "m<n" using `Suc m \<le> n` by arith+
  have "unit (Fun.swap p m (?A' p)) m n" using Suc.prems(2) p
    unfolding unit_def swap_def Suc_le_eq by (auto simp: le_less)
  from Suc.hyps[OF `m\<le>n` this rec] `m<n` p
  show ?case
    by(simp add: solution_swap solution_upd1 solution_upd_but1[where A = "A(p := ?Ap' p)"])
qed

theorem gauss_jordan_correct:
  "gauss_jordan A n = Some B \<Longrightarrow> solution A n (\<lambda>j. B j n)"
by(simp add:gauss_jordan_lemma[of n n] unit_def  field_simps)

text{* Future work: extend the proof to matrix inversion. *}

hide_const (open) unit

end
