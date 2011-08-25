header {*  Preliminaries  *}

theory Preliminaries
imports Main "~~/src/HOL/Library/Lattice_Syntax"
begin

subsection {*Simplification Lemmas*}


theorem update_simp [simp]:
  "f x = y \<Longrightarrow> f(x := y) = f"
  by auto

lemma simp_set_function:
  "{s . p s} x = p x"
  by (simp add: Collect_def)

lemma simp_eq_emptyset:
  "(X = {}) = (\<forall> x. x \<notin> X)"
  by blast

lemma mono_comp[simp]:
  "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (f o g)" 
  apply (unfold mono_def)
  by auto

lemma univ_in[simp]: "(x \<in> UNIV) = True"
  by auto

lemma neg_fun_pred: "(- A) x = - (A x)"
  by (simp add: fun_Compl_def)

lemma bot_fun_pred: "bot i = {}"
  by (simp add: bot_fun_def)

subsection {*  Finite sets and cardinal properties  *}

lemma marked_finite [simp]: "finite (-X) \<Longrightarrow> finite (-insert x X)"
  apply (case_tac "(-insert x X) \<subseteq> -X")
  by (rule finite_subset, auto)

lemma finite_insert [simp]: "finite X \<Longrightarrow> finite (insert x X)"
  by auto

lemma card_insert [simp]: "(-insert x X) = (-X) - {x}"
by auto

lemma card_remove [simp]: "finite X \<Longrightarrow> x \<in> X \<Longrightarrow> card (X - {x}) = card(X) - 1"
apply(rule_tac t = X in insert_Diff [THEN subst], assumption)
apply(simp del:insert_Diff_single)
done

lemma nonempty_card [simp]: "finite X \<Longrightarrow> x \<in> X \<Longrightarrow> card(X) \<noteq>  0"
apply auto
done

subsection {*Complete Lattice Results*}

abbreviation
  SUP1_syntax :: "('a \<Rightarrow> 'b::complete_lattice) \<Rightarrow> 'b"  ("(SUP _)" [1000] 1000)
  where "SUP P == SUPR UNIV P"

theorem SUP_upper:
  "P w \<le> SUP P"
  by (simp add: le_SUPI)


theorem SUP_least:
  "(!! w . P w \<le> Q) \<Longrightarrow> SUP P \<le> Q"
  by (simp add: SUP_leI)


lemma SUP_fun_eq:
  "SUP A i = SUP (\<lambda> w . A w i)"
  by (rule SUP_apply)

text {*Monotonic applications which map monotonic to monotonic have monotonic fixpoints*}

definition
  "mono_mono F = (mono F \<and> (\<forall> f . mono f \<longrightarrow> mono (F f)))"

theorem lfp_mono [simp]:
  "mono_mono F \<Longrightarrow> mono (lfp F)"
  apply (simp add: mono_mono_def)
  apply (rule_tac f="F" and P = "mono" in lfp_ordinal_induct)
  apply auto
  apply (simp add: mono_def)
  apply auto
  apply (simp_all add: Sup_fun_def)
  apply (fast intro: SUP_leI le_SUPI2)
  done

text {*Some lattice simplification rules*}

lemma inf_bot_bot[simp]:
  "x \<sqinter> \<bottom> = \<bottom>"
  apply (rule antisym)
  by auto

theorem Sup_bottom:
  "(Sup X = (bot::'a::complete_lattice)) = (\<forall> x \<in> X . x = bot)"
  by (fact Sup_bot_conv)

theorem Inf_top:
  "(Inf X = (\<top>::'a::complete_lattice)) = (\<forall> x \<in> X . x = \<top>)"
  by (fact Inf_top_conv)

(* FIXME: this class is in the standard library now *)
class distributive_complete_lattice = complete_lattice +
  assumes inf_sup_distributivity: "(x \<sqinter> (Sup Y)) = (SUP y: Y . (x \<sqinter> y))"
  and sup_inf_distributivity: "(x \<squnion> (Inf Y)) = (INF y: Y . (x \<squnion> y))"

begin

lemma inf_sup_right_distrib: "((Sup Y) \<sqinter> x) = (SUP y: Y . (y \<sqinter> x))"
  apply (unfold inf_commute)
  apply (unfold inf_sup_distributivity)
  apply (unfold eq_iff)
  apply safe
  apply (unfold SUPR_def)
  apply (rule Sup_least)
  apply safe
  apply (rule Sup_upper)
  apply (unfold inf_commute)
  apply auto
  apply (rule Sup_least)
  apply safe
  apply (rule Sup_upper)
  apply (unfold image_def)
  apply (unfold inf_commute)
  by auto

lemma sup_inf_right_distrib: "((Inf Y) \<squnion> x) = (INF y: Y . (y \<squnion> x))"
  apply (unfold sup_commute)
  apply (unfold sup_inf_distributivity)
  apply (unfold eq_iff)
  apply safe
  apply (unfold INFI_def)
  apply (rule Inf_greatest)
  apply safe
  apply (rule Inf_lower)
  apply (unfold image_def)
  apply (unfold sup_commute)
  by auto


end

instantiation "fun" :: (type, distributive_complete_lattice) distributive_complete_lattice
begin
  instance proof
  fix x::"('a \<Rightarrow> 'b)" fix Y
    show  "x \<sqinter> \<Squnion>Y = (SUP y:Y. x \<sqinter> y)"
    by (simp add: fun_eq_iff inf_fun_def SUPR_def Sup_fun_def image_image inf_sup_distributivity)
  next
  fix x::"('a \<Rightarrow> 'b)" fix Y
    show  "x \<squnion> \<Sqinter> Y = (INF y:Y. x \<squnion> y)"
    by (simp add: fun_eq_iff sup_fun_def INFI_def Inf_fun_def image_image sup_inf_distributivity)
  qed

end

instantiation "bool" :: distributive_complete_lattice
begin
  instance proof
  fix x::bool fix Y
    show  "x \<sqinter> \<Squnion>Y = (SUP y:Y. x \<sqinter> y)"
    by auto
  next
  fix x::bool fix Y
    show  "x \<squnion> \<Sqinter> Y = (INF y:Y. x \<squnion> y)"
    by (metis sup_Inf)
  qed
end

class complete_boolean_algebra = distributive_complete_lattice + boolean_algebra


lemma compl_Sup:
  "- (\<Squnion> X) = (INF (x::('a::complete_boolean_algebra)): X . -x)"
  apply (rule compl_unique)
  apply (unfold inf_sup_right_distrib)
  apply (unfold SUPR_def)
  apply (simp add: Sup_bottom)
  apply (unfold eq_iff) [1]
  apply simp
  apply safe
  apply (rule_tac y = "x \<sqinter> -x"  in order_trans)
  apply (rule_tac inf_greatest)
  apply auto
  apply (rule_tac y = "INFI X uminus"  in order_trans)
  apply auto
  apply (simp add: INFI_def)
  apply (rule Inf_lower)
  apply auto
  apply (unfold inf_compl_bot)
  apply simp
  apply (simp add: INFI_def)
  apply (unfold sup_inf_distributivity)
  apply (simp add: INFI_def)
  apply (simp add: Inf_top)
  apply (unfold eq_iff)
  apply simp
  apply safe
  apply (rule_tac y = "x \<squnion> -x"  in order_trans)
  apply (simp add: sup_compl_top)
  apply (rule_tac sup_least)
  apply auto
  apply (rule_tac y = "\<Squnion> X"  in order_trans)
  apply auto
  apply (rule Sup_upper)
  by assumption

lemma compl_Inf:
  "- (\<Sqinter> X) = (SUP (x::('a::complete_boolean_algebra)): X . -x)"
  apply (rule compl_unique)
  apply (simp add: SUPR_def)
  apply (unfold inf_sup_distributivity)
  apply (simp add: SUPR_def)
  apply (simp add: Sup_bottom)
  apply safe
  apply (unfold eq_iff) [1]
  apply simp
  apply (rule_tac y = "x \<sqinter> -x"  in order_trans)
  apply (rule_tac inf_greatest)
  apply auto
  apply (rule_tac y = " \<Sqinter>X"  in order_trans)
  apply auto
  apply (rule Inf_lower)
  apply auto
  apply (unfold inf_compl_bot)
  apply simp
  apply (unfold sup_inf_right_distrib)
  apply (simp add: INFI_def)
  apply (simp add: Inf_top)
  apply safe
  apply (unfold eq_iff)
  apply simp
  apply (rule_tac y = "x \<squnion> -x"  in order_trans)
  apply (simp add: sup_compl_top)
  apply (rule_tac sup_least)
  apply auto
  apply (rule_tac y = "SUPR X uminus"  in order_trans)
  apply auto
  apply (simp add: SUPR_def)
  apply (rule Sup_upper)
  by (simp add: image_def)

instance "fun" :: (type, complete_boolean_algebra) complete_boolean_algebra ..

instance "bool" :: complete_boolean_algebra ..

end
