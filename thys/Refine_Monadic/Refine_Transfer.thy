header {* \isaheader{Transfer Setup} *}
theory Refine_Transfer
imports
  Refine_Basic
  Refine_While
  Refine_Det 
  "Generic/RefineG_Transfer"
begin

subsection {* Transfer to Deterministic Result Lattice *}
text {*
  TODO: Once lattice and ccpo are connected, also transfer to option monad, that
  is a ccpo, but no complete lattice!
*}
subsubsection {* Connecting Deterministic and Non-Deterministic Result Lattices *}
definition "nres_of r \<equiv> case r of
  dSUCCEEDi \<Rightarrow> SUCCEED
| dFAILi \<Rightarrow> FAIL
| dRETURN x \<Rightarrow> RETURN x"

lemma nres_of_simps[simp]:
  "nres_of dSUCCEED = SUCCEED"
  "nres_of dFAIL = FAIL"
  "nres_of (dRETURN x) = RETURN x"
  apply -
  unfolding nres_of_def bot_dres_def top_dres_def
  by (auto simp del: dres_internal_simps)

lemma nres_of_mono: "mono nres_of"
  apply (rule)
  apply (case_tac x, simp_all, case_tac y, simp_all)
  done

lemma nres_transfer:
  "nres_of dSUCCEED = SUCCEED"
  "nres_of dFAIL = FAIL"
  "nres_of a \<le> nres_of b \<longleftrightarrow> a\<le>b"
  "nres_of a < nres_of b \<longleftrightarrow> a<b"
  "is_chain A \<Longrightarrow> nres_of (Sup A) = Sup (nres_of`A)"
  "is_chain A \<Longrightarrow> nres_of (Inf A) = Inf (nres_of`A)"
  apply simp_all
  apply (case_tac a, simp_all, case_tac [!] b, simp_all) [1]

  apply (simp add: less_le)
  apply (case_tac a, simp_all, case_tac [!] b, simp_all) [1]

  apply (erule dres_Sup_chain_cases)
    apply (cases "A={}")
    apply auto []
    apply (subgoal_tac "A={dSUCCEED}", auto) []

    apply (case_tac "A={dRETURN r}")
    apply auto []
    apply (subgoal_tac "A={dSUCCEED,dRETURN r}", auto) []

    apply (drule imageI[where f=nres_of])
    apply auto []

  apply (erule dres_Inf_chain_cases)
    apply (cases "A={}")
    apply auto []
    apply (subgoal_tac "A={dFAIL}", auto) []

    apply (case_tac "A={dRETURN r}")
    apply auto []
    apply (subgoal_tac "A={dFAIL,dRETURN r}", auto) []

    apply (drule imageI[where f=nres_of])
    apply (auto intro: bot_Inf [symmetric] simp add: INF_def simp del: Inf_image_eq) []
  done

lemma nres_correctD:
  assumes "nres_of S \<le> SPEC \<Phi>"
  shows 
  "S=dRETURN x \<Longrightarrow> \<Phi> x"
  "S\<noteq>dFAIL"
  using assms apply -
  apply (cases S, simp_all)+
  done

subsubsection {* Transfer Theorems Setup*}
interpretation dres!: dist_transfer nres_of 
  apply unfold_locales
  apply (simp add: nres_transfer)
  done

lemma det_FAIL[refine_transfer]: "nres_of (dFAIL) \<le> FAIL" by auto
lemma det_SUCCEED[refine_transfer]: "nres_of (dSUCCEED) \<le> SUCCEED" by auto
lemma det_SPEC: "\<Phi> x \<Longrightarrow> nres_of (dRETURN x) \<le> SPEC \<Phi>" by simp
lemma det_RETURN[refine_transfer]: 
  "nres_of (dRETURN x) \<le> RETURN x" by simp
lemma det_bind[refine_transfer]:
  assumes "nres_of m \<le> M"
  assumes "\<And>x. nres_of (f x) \<le> F x"
  shows "nres_of (dbind m f) \<le> bind M F"
  using assms 
  apply (cases m) 
  apply (auto simp: pw_le_iff refine_pw_simps)
  done

interpretation det_assert!: transfer_generic_Assert_remove 
  bind RETURN ASSERT ASSUME
  nres_of
  by unfold_locales

interpretation det_while!: transfer_WHILE
  dbind dRETURN dWHILEIT dWHILEI dWHILET dWHILE 
  bind RETURN WHILEIT WHILEI WHILET WHILE nres_of
  apply unfold_locales
  apply (auto intro: det_bind)
  done

(*
interpretation det_foreach!: 
  transfer_FOREACH nres_of dRETURN dbind "case_dres True True"
  apply unfold_locales
  apply (blast intro: det_bind)
  apply simp
  apply (case_tac m)
  apply simp_all
  done
*)

(* Done generally in RefineG_Transfer
lemma det_rec_list[refine_transfer]:
  assumes FN: "\<And>s. RETURN (fn s) \<le> (fn' s)"
  assumes FC: "\<And>x l rec rec' s. \<lbrakk> \<And>s. RETURN (rec s) \<le> (rec' s) \<rbrakk> 
    \<Longrightarrow> RETURN (fc x l rec s) \<le> fc' x l rec' s"
  shows "RETURN (rec_list fn fc l s) \<le> rec_list fn' fc' l s"
  apply (induct l arbitrary: s)
  apply (simp add: FN)
  apply (simp add: FC)
  done

lemma det_rec_nat[refine_transfer]:
  assumes FN: "\<And>s. RETURN (fn s) \<le> (fn' s)"
  assumes FC: "\<And>n rec rec' s. \<lbrakk> \<And>s. RETURN (rec s) \<le> (rec' s) \<rbrakk> 
    \<Longrightarrow> RETURN (fc x l rec s) \<le> fc' x l rec' s"
  shows "RETURN (rec_list fn fc l s) \<le> rec_list fn' fc' l s"
  apply (induct l arbitrary: s)
  apply (simp add: FN)
  apply (simp add: FC)
  done
*)

subsection {* Transfer to Plain Function *}

interpretation plain!: transfer RETURN .

lemma plain_RETURN[refine_transfer]: "RETURN a \<le> RETURN a" by simp
lemma plain_bind[refine_transfer]: 
  "\<lbrakk>RETURN x \<le> M; \<And>x. RETURN (f x) \<le> F x\<rbrakk> \<Longrightarrow> RETURN (Let x f) \<le> bind M F"
  apply (erule order_trans[rotated,OF bind_mono])
  apply assumption
  apply simp
  done

interpretation plain_assert!: transfer_generic_Assert_remove 
  bind RETURN ASSERT ASSUME
  RETURN
  by unfold_locales

(*
interpretation plain!: transfer_FOREACH RETURN "(\<lambda>x. x)" Let "(\<lambda>x. x)"
  apply (unfold_locales)
  apply (erule plain_bind, assumption)
  apply simp
  apply simp
  done
*)

subsection {* Total correctness in deterministic monad *}
text {*
  Sometimes one cannot extract total correct programs to executable plain 
  Isabelle functions, for example, if the total correctness only holds for
  certain preconditions. In those cases, one can still show
  @{text "RETURN (the_res S) \<le> S'"}. Here, @{text "the_res"} extracts
  the result from a deterministic monad. As @{text "the_res"} is executable,
  the above shows that @{text "(the_res S)"} is always a correct result.
*}

fun the_res where "the_res (dRETURN x) = x"

text {* The following lemma converts a proof-obligation
  with result extraction to a transfer proof obligation,
  and a proof obligation that the program yields not bottom.

  Note that this rule has to be applied manually, as, otherwise,
  it would interfere with the default setup, that tries to generate a
  plain function.
*}
lemma the_resI:
  assumes "nres_of S \<le> S'"
  assumes "S \<noteq> dSUCCEED"
  shows "RETURN (the_res S) \<le> S'"
  using assms
  by (cases S, simp_all)


text {* The following rule sets up a refinement goal, a transfer goal, and a 
  final optimization goal. *}
definition "detTAG x \<equiv> x"
lemma detTAGI: "x = detTAG x" unfolding detTAG_def by simp
lemma autoref_detI:
  assumes "(b,a)\<in>\<langle>R\<rangle>nres_rel"
  assumes "RETURN c \<le> b"
  assumes "c = detTAG d"
  shows "(RETURN d, a)\<in>\<langle>R\<rangle>nres_rel"
  using assms
  unfolding nres_rel_def detTAG_def
  by simp

end
