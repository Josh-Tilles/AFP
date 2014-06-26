(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Well-Quasi-Orders *}

theory Well_Quasi_Orders
imports
  Almost_Full_Relations
  "../Regular-Sets/Regexp_Method"
begin

subsection {* Basic Definitions *}

definition wqo_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "wqo_on P A \<longleftrightarrow> transp_on P A \<and> almost_full_on P A"

lemma wqo_on_UNIV:
  "wqo_on (\<lambda>_ _. True) UNIV"
  using almost_full_on_UNIV by (auto simp: wqo_on_def transp_on_def)

lemma wqo_onI [Pure.intro]:
  "\<lbrakk>transp_on P A; almost_full_on P A\<rbrakk> \<Longrightarrow> wqo_on P A"
  unfolding wqo_on_def almost_full_on_def by blast

lemma wqo_on_imp_reflp_on:
  "wqo_on P A \<Longrightarrow> reflp_on P A"
  using almost_full_on_imp_reflp_on by (auto simp: wqo_on_def)

lemma wqo_on_imp_transp_on:
  "wqo_on P A \<Longrightarrow> transp_on P A"
  by (auto simp: wqo_on_def)

lemma wqo_on_imp_almost_full_on:
  "wqo_on P A \<Longrightarrow> almost_full_on P A"
  by (auto simp: wqo_on_def)

lemma wqo_on_imp_qo_on:
  "wqo_on P A \<Longrightarrow> qo_on P A"
  by (metis qo_on_def wqo_on_imp_reflp_on wqo_on_imp_transp_on)

lemma wqo_on_imp_good:
  "wqo_on P A \<Longrightarrow> \<forall>i. f i \<in> A \<Longrightarrow> good P f"
  by (auto simp: wqo_on_def almost_full_on_def)

lemma wqo_on_subset:
  "A \<subseteq> B \<Longrightarrow> wqo_on P B \<Longrightarrow> wqo_on P A"
  using almost_full_on_subset [of A B P]
    and transp_on_subset [of A B P]
  unfolding wqo_on_def by blast

subsection {* Equivalent Definitions *}

text {*Given a quasi-order @{term P}, the following statements are equivalent:
\begin{enumerate}
\item @{term P} is a almost-full.
\item @{term P} does neither allow decreasing chains nor antichains.
\item Every quasi-order extending @{term P} is well-founded.
\end{enumerate}
*}

lemma wqo_af_conv:
  assumes "qo_on P A"
  shows "wqo_on P A \<longleftrightarrow> almost_full_on P A"
  using assms by (metis qo_on_def wqo_on_def)

lemma wqo_wf_and_no_antichain_conv:
  assumes "qo_on P A"
  shows "wqo_on P A \<longleftrightarrow> wfp_on (strict P) A \<and> \<not> (\<exists>f. antichain_on P f A)"
  unfolding wqo_af_conv [OF assms]
  using qo_af_imp_wf_and_no_antichain [OF assms]
    and wf_and_no_antichain_imp_qo_extension_wf [of P A]
    and every_qo_extension_wf_imp_af [OF _ assms]
    by blast

lemma wqo_extensions_wf_conv:
  assumes "qo_on P A"
  shows "wqo_on P A \<longleftrightarrow>
    (\<forall>Q. (\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q x y) \<and>
    qo_on Q A \<longrightarrow> wfp_on (strict Q) A)"
  unfolding wqo_af_conv [OF assms]
  using qo_af_imp_wf_and_no_antichain [OF assms]
    and wf_and_no_antichain_imp_qo_extension_wf [of P A]
    and every_qo_extension_wf_imp_af [OF _ assms]
    by blast

lemma wqo_on_imp_wfp_on:
  "wqo_on P A \<Longrightarrow> wfp_on (strict P) A"
  by (metis (no_types) wqo_on_imp_qo_on wqo_wf_and_no_antichain_conv)

text {*The homomorphic image of a wqo set is wqo.*}
lemma wqo_on_hom:
  assumes "transp_on Q (h ` A)"
    and "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q (h x) (h y)"
    and "wqo_on P A"
  shows "wqo_on Q (h ` A)"
  using assms and almost_full_on_hom [of A P Q h]
  unfolding wqo_on_def by blast

text {*The monomorphic preimage of a wqo set is wqo.*}
lemma wqo_on_mon:
  assumes trans: "transp_on P A"
    and mon: "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longleftrightarrow> Q (h x) (h y)" "bij_betw h A B"
    and wqo: "wqo_on Q B"
  shows "wqo_on P A"
  using assms and almost_full_on_mon [of A P Q h]
  unfolding wqo_on_def by blast


subsection {* A Typeclass for Well-Quasi-Orders *}

text {*In a well-quasi-order (wqo) every infinite sequence is good.*}
class wqo = preorder +
  assumes good: "good (op \<le>) f"

text {*The following lemma converts between @{const wqo_on} (for the special
case that the domain is the universe of a type) and the class predicate
@{const class.wqo}.*}
lemma wqo_on_UNIV_conv:
  "wqo_on P UNIV \<longleftrightarrow> class.wqo P (strict P)" (is "?lhs = ?rhs")
proof
  assume "?lhs" thus "?rhs"
    unfolding wqo_on_def class.wqo_def class.preorder_def class.wqo_axioms_def
    using almost_full_on_imp_reflp_on [of P UNIV]
    by (auto simp: reflp_on_def almost_full_on_def)
       (unfold transp_on_def, blast)
next
  assume "?rhs" thus "?lhs"
    unfolding class.wqo_def class.preorder_def class.wqo_axioms_def
    by (auto simp: wqo_on_def almost_full_on_def transp_on_def)
qed

text {*The strict part of a wqo is well-founded.*}
lemma (in wqo) "wfP (op <)"
proof -
  have "class.wqo (op \<le>) (op <)" ..
  hence "wqo_on (op \<le>) UNIV"
    unfolding less_le_not_le [abs_def] wqo_on_UNIV_conv [symmetric] .
  from wqo_on_imp_wfp_on [OF this]
    show ?thesis unfolding less_le_not_le [abs_def] wfp_on_UNIV .
qed

lemma wqo_on_with_bot:
  assumes "wqo_on P A"
  shows "wqo_on (option_le P) A\<^sub>\<bottom>"
    (is "wqo_on ?P ?A")
proof -
  {
    from assms have trans [unfolded transp_on_def]: "transp_on P A"
      by (auto simp: wqo_on_def)
    have "transp_on ?P ?A"
      unfolding transp_on_def by (auto, insert trans) (blast+)
  } moreover {
    from assms and almost_full_on_with_bot
      have "almost_full_on ?P ?A" by (auto simp: wqo_on_def)
  } ultimately show ?thesis by (auto simp: wqo_on_def)
qed

text {*When two sets are wqo, then their disjoint sum is wqo.*}
lemma wqo_on_Plus:
  assumes "wqo_on P A" and "wqo_on Q B"
  shows "wqo_on (sum_le P Q) (A <+> B)"
    (is "wqo_on ?P ?A")
proof -
  {
    from assms have trans [unfolded transp_on_def]: "transp_on P A" "transp_on Q B"
      by (auto simp: wqo_on_def)
    have "transp_on ?P ?A"
      unfolding transp_on_def by (auto, insert trans) (blast+)
  } moreover {
    from assms and almost_full_on_Plus have "almost_full_on ?P ?A" by (auto simp: wqo_on_def)
  } ultimately show ?thesis by (auto simp: wqo_on_def)
qed


subsection {* Dickson's Lemma *}

lemma wqo_on_Sigma:
  fixes A1 :: "'a set" and A2 :: "'b set"
  assumes "wqo_on P1 A1" and "wqo_on P2 A2"
  shows "wqo_on (prod_le P1 P2) (A1 \<times> A2)"
    (is "wqo_on ?P ?A")
proof -
  {
    from assms have "transp_on P1 A1" and "transp_on P2 A2" by (auto simp: wqo_on_def)
    hence "transp_on ?P ?A" unfolding transp_on_def prod_le_def by blast
  } moreover {
    from assms and almost_full_on_Sigma [of P1 A1 P2 A2]
      have "almost_full_on ?P ?A" by (auto simp: wqo_on_def)
  } ultimately show ?thesis by (auto simp: wqo_on_def)
qed

lemmas dickson = wqo_on_Sigma


subsection {* Higman's Lemma *}

lemma wqo_on_lists:
  assumes "wqo_on P A" shows "wqo_on (list_emb P) (lists A)"
  using assms and almost_full_on_lists
    and transp_on_list_emb by (auto simp: wqo_on_def)

lemmas higman = wqo_on_lists

text {*Every reflexive and transitive relation on a finite set is a wqo.*}
lemma finite_wqo_on:
  assumes "finite A"
    and refl: "reflp_on P A" and "transp_on P A"
  shows "wqo_on P A"
  using assms and finite_almost_full_on by (auto simp: wqo_on_def)

lemma finite_eq_wqo_on:
  assumes "finite A"
  shows "wqo_on (op =) A"
  using finite_wqo_on [OF assms, of "op ="]
  by (auto simp: reflp_on_def transp_on_def)

lemma wqo_on_lists_over_finite_sets:
  "wqo_on (list_emb (op =)) (UNIV::('a::finite) list set)"
  using wqo_on_lists [OF finite_eq_wqo_on [OF finite [of "UNIV::('a::finite) set"]]] by simp

end

