(* Author: Christian Sternagel, JAIST *)

header {* Enumerations of well-ordered sets in increasing order *}

theory Least_Enum
imports Main
begin

text {*Enumerate the elements of a well-ordered infinite set in increasing order.*}
fun enum :: "('a :: wellorder \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a" where
  "enum P 0 = (LEAST n. P n)" |
  "enum P (Suc i) = (LEAST n. n > enum P i \<and> P n)"

lemma enum_mono:
  assumes "\<forall>i. \<exists>j>i. P j"
  shows "enum P i < enum P (Suc i)"
  using assms by (cases i, auto) (metis (lifting) LeastI)+

lemma enum_P:
  assumes "\<forall>i. \<exists>j>i. P j"
  shows "P (enum P i)"
  using assms by (cases i, auto) (metis (lifting) LeastI)+

text {*Enumerate the elements of a well-ordered infinite set that form a chain w.r.t.\ a given
predicate @{term P} starting from a given @{term N} in increasing order.*}
fun enumchain :: "('a :: wellorder \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "enumchain P N 0 = N" |
  "enumchain P N (Suc n) = (LEAST m. m > enumchain P N n \<and> P (enumchain P N n) m)"

lemma enumchain_mono:
  assumes "\<forall>i\<ge>N. \<exists>j>i. P i j"
  shows "N \<le> enumchain P N i \<and> enumchain P N i < enumchain P N (Suc i)"
proof (induct i)
  case 0
  have "enumchain P N 0 \<ge> N" by simp
  moreover then have "\<exists>m>enumchain P N 0. P (enumchain P N 0) m" using assms by blast
  ultimately show ?case by auto (metis (lifting) LeastI)
next
  case (Suc i)
  then have "N \<le> enumchain P N (Suc i)" by auto
  moreover then have "\<exists>m>enumchain P N (Suc i). P (enumchain P N (Suc i)) m" using assms by blast
  ultimately show ?case by (auto) (metis (lifting) LeastI)
qed

lemma enumchain_chain:
  assumes "\<forall>i\<ge>N. \<exists>j>i. P i j"
  shows "P (enumchain P N i) (enumchain P N (Suc i))"
proof (cases i)
  case 0
  moreover have "\<exists>m>enumchain P N 0. P (enumchain P N 0) m" using assms by auto
  ultimately show ?thesis by auto (metis (lifting) LeastI)
next
  case (Suc i)
  moreover have "enumchain P N (Suc i) > N" using enumchain_mono [OF assms] by (metis le_less_trans)
  moreover then have "\<exists>m. m > enumchain P N (Suc i) \<and> P (enumchain P N (Suc i)) m"
    using assms by auto
  ultimately show ?thesis by (auto) (metis (lifting) LeastI)
qed

end

