header {* \isaheader{Miscellanneous Lemmas and Tools} *}
theory Refine_Misc
imports 
  "../Automatic_Refinement/Automatic_Refinement"
begin

subsection {* ML-level stuff *}

ML {*

structure Refine_Misc = struct
  (* Fail if goal index out of bounds. *)
  (* Use IF_EXGOAL instead!
  fun wrap_nogoals tac i st = if nprems_of st < i then 
    no_tac st 
  else
    tac i st;*)

  (********************)
  (* Monotonicity Prover *)
  (********************)

    structure refine_mono = Named_Thms
      ( val name = @{binding refine_mono}
        val description = "Refinement Framework: " ^
          "Monotonicity rules" )

    (*structure refine_mono_trigger = Named_Thms
      ( val name = @{binding refine_mono_trigger}
        val description = "Refinement Framework: " ^
          "Triggering rules for monotonicity prover" )
    *)

    (* Monotonicity prover: Solve by removing function arguments *)
    fun solve_le_tac ctxt = SOLVED' (REPEAT_ALL_NEW (
      Method.assm_tac ctxt ORELSE' fo_rtac @{thm le_funD} ctxt));

    (* Monotonicity prover. TODO: A related thing is in the 
      partial_function package, can we reuse (parts of) that?
    *)
    fun mono_prover_tac ctxt = REPEAT_ALL_NEW (FIRST' [
      Method.assm_tac ctxt,
      match_tac (refine_mono.get ctxt),
      solve_le_tac ctxt
    ]);

    fun untriggered_mono_tac ctxt = mono_prover_tac ctxt 
      THEN_ALL_NEW (TRY o Tagged_Solver.solve_tac ctxt)

    val declare_mono_triggers =
      Tagged_Solver.add_triggers "Refine_Misc.refine_mono" 
      (* TODO: Hack, how to get correct naming? *)

    val setup = refine_mono.setup
    val decl_setup = 
      Tagged_Solver.declare_solver 
        @{thms monoI monotoneI[of "op \<le>" "op \<le>"]} @{binding refine_mono}
        "Autoref: Monotonicity prover" 
        mono_prover_tac
end;
*}

setup Refine_Misc.setup
declaration Refine_Misc.decl_setup


method_setup refine_mono = 
  {* Scan.succeed (fn ctxt => SIMPLE_METHOD' (
    Refine_Misc.untriggered_mono_tac ctxt
  )) *} 
  "Refinement framework: Monotonicity prover"


text {* Basic configuration for monotonicity prover: *}
lemmas [refine_mono] = monoI monotoneI[of "op \<le>" "op \<le>"]
lemmas [refine_mono] = TrueI le_funI order_refl

lemma case_prod_mono[refine_mono]: 
  "\<lbrakk>\<And>a b. p=(a,b) \<Longrightarrow> f a b \<le> f' a b\<rbrakk> \<Longrightarrow> case_prod f p \<le> case_prod f' p"
  by (auto split: prod.split)

lemma case_option_mono[refine_mono]:
  assumes "fn \<le> fn'"
  assumes "\<And>v. x=Some v \<Longrightarrow> fs v \<le> fs' v"
  shows "case_option fn fs x \<le> case_option fn' fs' x"
  using assms by (auto split: option.split)

lemma case_list_mono[refine_mono]:
  assumes "fn \<le> fn'"
  assumes "\<And>x xs. l=x#xs \<Longrightarrow> fc x xs \<le> fc' x xs"
  shows "case_list fn fc l \<le> case_list fn' fc' l"
  using assms by (auto split: list.split)

lemma if_mono[refine_mono]:
  assumes "b \<Longrightarrow> m1 \<le> m1'"
  assumes "\<not>b \<Longrightarrow> m2 \<le> m2'"
  shows "(if b then m1 else m2) \<le> (if b then m1' else m2')"
  using assms by auto

lemma let_mono[refine_mono]:
  "f x \<le> f' x' \<Longrightarrow> Let x f \<le> Let x' f'" by auto


subsection {* Uncategorized Lemmas *}
lemma all_nat_split_at: "\<forall>i::'a::linorder<k. P i \<Longrightarrow> P k \<Longrightarrow> \<forall>i>k. P i 
  \<Longrightarrow> \<forall>i. P i"
  by (metis linorder_neq_iff)

subsection {* Well-Foundedness *}

lemma wf_no_infinite_down_chainI:
  assumes "\<And>f. \<lbrakk>\<And>i. (f (Suc i), f i)\<in>r\<rbrakk> \<Longrightarrow> False"
  shows "wf r"
  by (metis assms wf_iff_no_infinite_down_chain)

text {* This lemma transfers well-foundedness over a simulation relation. *}
lemma sim_wf:
  assumes WF: "wf (S'\<inverse>)"
  assumes STARTR: "(x0,x0')\<in>R"
  assumes SIM: "\<And>s s' t. \<lbrakk> (s,s')\<in>R; (s,t)\<in>S; (x0',s')\<in>S'\<^sup>* \<rbrakk> 
    \<Longrightarrow> \<exists>t'. (s',t')\<in>S' \<and> (t,t')\<in>R"
  assumes CLOSED: "Domain S  \<subseteq> S\<^sup>*``{x0}"
  shows "wf (S\<inverse>)"
proof (rule wf_no_infinite_down_chainI, simp)
  txt {*
    Informal proof:
    Assume there is an infinite chain in @{text "S"}.
    Due to the closedness property of @{text "S"}, it can be extended to 
    start at @{text x0}.
    Now, we inductively construct an infinite chain in @{text "S'"}, such that
    each element of the new chain is in relation with the corresponding 
    element of the original chain:
      The first element is @{text "x0'"}. 
      For any element @{text "i+1"}, the simulation property yields the next
      element.
    This chain contradicts well-foundedness of @{text "S'"}.
    *}

  fix f
  assume CHAIN: "\<And>i. (f i, f (Suc i))\<in>S"
  txt {* Extend to start with @{text "x0"} *}
  obtain f' where CHAIN': "\<And>i. (f' i, f' (Suc i))\<in>S" and [simp]: "f' 0 = x0"
  proof -
    {
      fix x
      assume S: "x = f 0"
      from CHAIN have "f 0 \<in> Domain S" by auto
      with CLOSED have "(x0,x)\<in>S\<^sup>*" by (auto simp: S)
      then obtain g k where G0: "g 0 = x0" and X: "x = g k" 
        and CH: "(\<forall>i<k. (g i, g (Suc i))\<in>S)"
      proof induct
        case base thus ?case by force
      next
        case (step y z) show ?case proof (rule step.hyps(3))
          fix g k 
          assume "g 0 = x0" and "y = g k" 
            and "\<forall>i<k. (g i, g (Suc i))\<in>S"
          thus ?case using `(y,z)\<in>S`
            by (rule_tac step.prems[where g="g(Suc k := z)" and k="Suc k"])
              auto
        qed
      qed
      def f'\<equiv>"\<lambda>i. if i<k then g i else f (i-k)"
      have "\<exists>f'. f' 0 = x0 \<and> (\<forall>i. (f' i, f' (Suc i))\<in>S)"
        apply (rule_tac x=f' in exI)
        apply (unfold f'_def)
        apply (rule conjI)
        using S X G0 apply (auto) []
        apply (rule_tac k=k in all_nat_split_at)
        apply (auto)
        apply (simp add: CH)
        apply (subgoal_tac "k = Suc i")
        apply (simp add: S[symmetric] CH X)
        apply simp
        apply (simp add: CHAIN)
        apply (subgoal_tac "Suc i - k = Suc (i-k)")
        using CHAIN apply simp
        apply simp
        done
    }
    then obtain f' where "\<forall>i. (f' i,f' (Suc i))\<in>S" and "f' 0 = x0" by blast
    thus ?thesis by (blast intro!: that)
  qed

  txt {* Construct chain in @{text "S'"}*}
  def g'\<equiv>"rec_nat x0' (\<lambda>i x. SOME x'. 
          (x,x')\<in>S' \<and> (f' (Suc i),x')\<in>R \<and> (x0', x')\<in>S'\<^sup>* )"
  {
    fix i
    note [simp] = g'_def
    have "(g' i, g' (Suc i))\<in>S' \<and> (f' (Suc i),g' (Suc i))\<in>R 
      \<and> (x0',g' (Suc i))\<in>S'\<^sup>*"
    proof (induct i)
      case 0 
      from SIM[OF STARTR] CHAIN'[of 0] obtain t' where 
        "(x0',t')\<in>S'" and "(f' (Suc 0),t')\<in>R" by auto
      moreover hence "(x0',t')\<in>S'\<^sup>*" by auto
      ultimately show ?case
        by (auto intro: someI2 simp: STARTR simp del: r_into_rtrancl)
    next
      case (Suc i)
      with SIM[OF _ CHAIN'[of "Suc i"]] 
      obtain t' where LS: "(g' (Suc i),t')\<in>S'" and "(f' (Suc (Suc i)),t')\<in>R"
        by auto
      moreover from LS Suc have "(x0', t')\<in>S'\<^sup>*" by auto
      ultimately show ?case
        apply simp
        apply (rule_tac a="t'" in someI2)
        apply auto
        done
    qed
  } hence S'CHAIN: "\<forall>i. (g' i, g'(Suc i))\<in>S'" by simp
  txt {* This contradicts well-foundedness *}
  with WF show False 
    by (erule_tac wf_no_infinite_down_chainE[where f=g']) simp
qed

text {* Well-founded relation that approximates a finite set from below. *}
definition "finite_psupset S \<equiv> { (Q',Q). Q\<subset>Q' \<and> Q' \<subseteq> S }"
lemma finite_psupset_wf[simp, intro]: "finite S \<Longrightarrow> wf (finite_psupset S)"
  unfolding finite_psupset_def by (blast intro: wf_bounded_supset)

subsection {* Monotonicity and Orderings *}

lemma mono_const[simp, intro!]: "mono (\<lambda>_. c)" by (auto intro: monoI)
lemma mono_if: "\<lbrakk>mono S1; mono S2\<rbrakk> \<Longrightarrow>
  mono (\<lambda>F s. if b s then S1 F s else S2 F s)"
  apply rule
  apply (rule le_funI)
  apply (auto dest: monoD[THEN le_funD])
  done

lemma mono_infI: "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (inf f g)"
  unfolding inf_fun_def
  apply (rule monoI)
  apply (metis inf_mono monoD)
  done

lemma mono_infI': 
  "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (\<lambda>x. inf (f x) (g x) :: 'b::lattice)"
  by (rule mono_infI[unfolded inf_fun_def])

lemma mono_infArg: 
  fixes f :: "'a::lattice \<Rightarrow> 'b::order"
  shows "mono f \<Longrightarrow> mono (\<lambda>x. f (inf x X))"
  apply (rule monoI)
  apply (erule monoD)
  apply (metis inf_mono order_refl) 
  done

lemma mono_Sup:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "mono f \<Longrightarrow> Sup (f`S) \<le> f (Sup S)"
  apply (rule Sup_least)
  apply (erule imageE)
  apply simp
  apply (erule monoD)
  apply (erule Sup_upper)
  done

lemma mono_SupI:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  assumes "mono f"
  assumes "S'\<subseteq>f`S"
  shows "Sup S' \<le> f (Sup S)"
  by (metis Sup_subset_mono assms mono_Sup order_trans)

lemma mono_Inf:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "mono f \<Longrightarrow> f (Inf S) \<le> Inf (f`S)"
  apply (rule Inf_greatest)
  apply (erule imageE)
  apply simp
  apply (erule monoD)
  apply (erule Inf_lower)
  done

lemma mono_funpow: "mono (f::'a::order \<Rightarrow> 'a) \<Longrightarrow> mono (f^^i)"
  apply (induct i)
  apply (auto intro!: monoI) 
  apply (auto dest: monoD)
  done

lemma mono_id[simp, intro!]:
  "mono id"
  "mono (\<lambda>x. x)"
  by (auto intro: monoI)

declare SUP_insert[simp]

lemma (in semilattice_inf) le_infD1:
  "a \<le> inf b c \<Longrightarrow> a \<le> b" by (rule le_infE)
lemma (in semilattice_inf) le_infD2:
  "a \<le> inf b c \<Longrightarrow> a \<le> c" by (rule le_infE)
lemma (in semilattice_inf) inf_leI:
  "\<lbrakk> \<And>x. \<lbrakk> x\<le>a; x\<le>b \<rbrakk> \<Longrightarrow> x\<le>c \<rbrakk> \<Longrightarrow> inf a b \<le> c"
  by (metis inf_le1 inf_le2)

lemma top_Sup: "(top::'a::complete_lattice)\<in>A \<Longrightarrow> Sup A = top"
  by (metis Sup_upper top_le)
lemma bot_Inf: "(bot::'a::complete_lattice)\<in>A \<Longrightarrow> Inf A = bot"
  by (metis Inf_lower le_bot)

lemma mono_compD: "mono f \<Longrightarrow> x\<le>y \<Longrightarrow> f o x \<le> f o y"
  apply (rule le_funI)
  apply (auto dest: monoD le_funD)
  done


subsubsection {* Galois Connections *}
locale galois_connection =
  fixes \<alpha>::"'a::complete_lattice \<Rightarrow> 'b::complete_lattice" and \<gamma>
  assumes galois: "c \<le> \<gamma>(a) \<longleftrightarrow> \<alpha>(c) \<le> a"
begin
  lemma \<alpha>\<gamma>_defl: "\<alpha>(\<gamma>(x)) \<le> x"
  proof -
    have "\<gamma> x \<le> \<gamma> x" by simp
    with galois show "\<alpha>(\<gamma>(x)) \<le> x" by blast
  qed
  lemma \<gamma>\<alpha>_infl: "x \<le> \<gamma>(\<alpha>(x))"
  proof -
    have "\<alpha> x \<le> \<alpha> x" by simp
    with galois show "x \<le> \<gamma>(\<alpha>(x))" by blast
  qed
    
  lemma \<alpha>_mono: "mono \<alpha>"
  proof 
    fix x::'a and y::'a
    assume "x\<le>y"
    also note \<gamma>\<alpha>_infl[of y]
    finally show "\<alpha> x \<le> \<alpha> y" by (simp add: galois)
  qed

  lemma \<gamma>_mono: "mono \<gamma>"
    by rule (metis \<alpha>\<gamma>_defl galois inf_absorb1 le_infE)

  lemma dist_\<gamma>[simp]: 
    "\<gamma> (inf a b) = inf (\<gamma> a) (\<gamma> b)"
    apply (rule order_antisym)
    apply (rule mono_inf[OF \<gamma>_mono])
    apply (simp add: galois)
    apply (simp add: galois[symmetric])
    done

  lemma dist_\<alpha>[simp]: 
    "\<alpha> (sup a b) = sup (\<alpha> a) (\<alpha> b)"
    by (metis (no_types) \<alpha>_mono galois mono_sup order_antisym 
      sup_ge1 sup_ge2 sup_least)

end

subsubsection {* Fixed Points *}
lemma mono_lfp_eqI:
  assumes MONO: "mono f"
  assumes FIXP: "f a \<le> a"
  assumes LEAST: "\<And>x. f x = x \<Longrightarrow> a\<le>x"
  shows "lfp f = a"
  apply (rule antisym)
  apply (rule lfp_lowerbound)
  apply (rule FIXP)
  by (metis LEAST MONO lfp_unfold)

lemma mono_gfp_eqI:
  assumes MONO: "mono f"
  assumes FIXP: "a \<le> f a"
  assumes GREATEST: "\<And>x. f x = x \<Longrightarrow> x\<le>a"
  shows "gfp f = a"
  apply (rule antisym)
  apply (metis GREATEST MONO gfp_unfold)
  apply (rule gfp_upperbound)
  apply (rule FIXP)
  done

lemma lfp_le_gfp: "mono f \<Longrightarrow> lfp f \<le> gfp f"
  by (metis gfp_upperbound lfp_lemma3)

lemma lfp_le_gfp': "mono f \<Longrightarrow> lfp f x \<le> gfp f x"
  by (rule le_funD[OF lfp_le_gfp])

subsubsection {* Connecting Complete Lattices and 
  Chain-Complete Partial Orders *}
(* Note: Also connected by subclass now. However, we need both directions
  of embedding*)
lemma (in complete_lattice) is_ccpo: "class.ccpo Sup (op \<le>) (op <)"
  apply unfold_locales
  apply (erule Sup_upper)
  apply (erule Sup_least)
  done

lemma (in complete_lattice) is_dual_ccpo: "class.ccpo Inf (op \<ge>) (op >)"
  apply unfold_locales
  apply (rule less_le_not_le)
  apply (rule order_refl)
  apply (erule (1) order_trans)
  apply (erule (1) antisym)
  apply (erule Inf_lower)
  apply (erule Inf_greatest)
  done
  
  
lemma ccpo_mono_simp: "monotone (op \<le>) (op \<le>) f \<longleftrightarrow> mono f"
  unfolding monotone_def mono_def by simp
lemma ccpo_monoI: "mono f \<Longrightarrow> monotone (op \<le>) (op \<le>) f" 
  by (simp add: ccpo_mono_simp) 
lemma ccpo_monoD: "monotone (op \<le>) (op \<le>) f \<Longrightarrow> mono f" 
  by (simp add: ccpo_mono_simp) 

lemma dual_ccpo_mono_simp: "monotone (op \<ge>) (op \<ge>) f \<longleftrightarrow> mono f"
  unfolding monotone_def mono_def by auto
lemma dual_ccpo_monoI: "mono f \<Longrightarrow> monotone (op \<ge>) (op \<ge>) f" 
  by (simp add: dual_ccpo_mono_simp) 
lemma dual_ccpo_monoD: "monotone (op \<ge>) (op \<ge>) f \<Longrightarrow> mono f" 
  by (simp add: dual_ccpo_mono_simp) 

lemma ccpo_lfp_simp: "\<And>f. mono f \<Longrightarrow> ccpo.fixp Sup op \<le> f = lfp f"
  apply (rule antisym)
  defer
  apply (rule lfp_lowerbound)
  apply (drule ccpo.fixp_unfold[OF is_ccpo ccpo_monoI, symmetric])
  apply simp

  apply (rule ccpo.fixp_lowerbound[OF is_ccpo ccpo_monoI], assumption)
  apply (simp add: lfp_unfold[symmetric])
  done

lemma ccpo_gfp_simp: "\<And>f. mono f \<Longrightarrow> ccpo.fixp Inf op \<ge> f = gfp f"
  apply (rule antisym)
  apply (rule gfp_upperbound)
  apply (drule ccpo.fixp_unfold[OF is_dual_ccpo dual_ccpo_monoI, symmetric])
  apply simp

  apply (rule ccpo.fixp_lowerbound[OF is_dual_ccpo dual_ccpo_monoI], assumption)
  apply (simp add: gfp_unfold[symmetric])
  done

abbreviation "chain_admissible P \<equiv> ccpo.admissible Sup op \<le> P"
abbreviation "is_chain \<equiv> Complete_Partial_Order.chain (op \<le>)"
lemmas chain_admissibleI[intro?] = ccpo.admissibleI[where lub=Sup and ord="op \<le>"]


abbreviation "dual_chain_admissible P \<equiv> ccpo.admissible Inf (\<lambda>x y. y\<le>x) P"
abbreviation "is_dual_chain \<equiv> Complete_Partial_Order.chain (\<lambda>x y. y\<le>x)"
lemmas dual_chain_admissibleI[intro?] = 
  ccpo.admissibleI[where lub=Inf and ord="(\<lambda>x y. y\<le>x)"]

lemma dual_chain_iff[simp]: "is_dual_chain C = is_chain C"
  unfolding chain_def
  apply auto
  done

lemmas chain_dualI = iffD1[OF dual_chain_iff]
lemmas dual_chainI = iffD2[OF dual_chain_iff]

lemma is_chain_empty[simp, intro!]: "is_chain {}"
  by (rule chainI) auto
lemma is_dual_chain_empty[simp, intro!]: "is_dual_chain {}"
  by (rule dual_chainI) auto

lemma point_chainI: "is_chain M \<Longrightarrow> is_chain ((\<lambda>f. f x)`M)"
  by (auto intro: chainI le_funI dest: chainD le_funD)


text {* We transfer the admissible induction lemmas to complete
  lattices. *}
lemma lfp_cadm_induct:
  "\<lbrakk>chain_admissible P; mono f; P (Sup {}); \<And>x. P x \<Longrightarrow> P (f x)\<rbrakk> \<Longrightarrow> P (lfp f)"
  by (simp only: ccpo_mono_simp[symmetric] ccpo_lfp_simp[symmetric])
     (rule ccpo.fixp_induct[OF is_ccpo])

lemma gfp_cadm_induct:
  "\<lbrakk>dual_chain_admissible P; mono f; P (Inf {}); \<And>x. P x \<Longrightarrow> P (f x)\<rbrakk> \<Longrightarrow> P (gfp f)"
  by (simp only: dual_ccpo_mono_simp[symmetric] ccpo_gfp_simp[symmetric])
     (rule ccpo.fixp_induct[OF is_dual_ccpo])

subsubsection {* Continuity and Kleene Fixed Point Theorem *}
definition "cont f \<equiv> \<forall>C. C\<noteq>{} \<longrightarrow> f (Sup C) = Sup (f`C)"
definition "strict f \<equiv> f bot = bot"
definition "inf_distrib f \<equiv> strict f \<and> cont f"

lemma contI[intro?]: "\<lbrakk>\<And>C. C\<noteq>{} \<Longrightarrow> f (Sup C) = Sup (f`C)\<rbrakk> \<Longrightarrow> cont f" 
  unfolding cont_def by auto
lemma contD: "cont f \<Longrightarrow> C\<noteq>{} \<Longrightarrow> f (Sup C) = Sup (f`C)" 
  unfolding cont_def by auto
lemma contD': "cont f \<Longrightarrow> C\<noteq>{} \<Longrightarrow> f (Sup C) = SUPREMUM C f" 
  using contD by simp

lemma strictD[dest]: "strict f \<Longrightarrow> f bot = bot" 
  unfolding strict_def by auto
-- "We only add this lemma to the simpset for functions on the same type. 
    Otherwise, the simplifier tries it much too often."
lemma strictD_simp[simp]: "strict f \<Longrightarrow> f (bot::'a::bot) = (bot::'a)" 
  unfolding strict_def by auto

lemma strictI[intro?]: "f bot = bot \<Longrightarrow> strict f"
  unfolding strict_def by auto

lemma inf_distribD[simp]: 
  "inf_distrib f \<Longrightarrow> strict f"
  "inf_distrib f \<Longrightarrow> cont f"
  unfolding inf_distrib_def by auto

lemma inf_distribI[intro?]: "\<lbrakk>strict f; cont f\<rbrakk> \<Longrightarrow> inf_distrib f"
  unfolding inf_distrib_def by auto

lemma inf_distribD'[simp]:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "inf_distrib f \<Longrightarrow> f (Sup C) = Sup (f`C)"
  apply (cases "C={}")
  apply (auto dest: inf_distribD contD')
  done

lemma inf_distribI':
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  assumes B: "\<And>C. f (Sup C) = Sup (f`C)"
  shows "inf_distrib f"
  apply (rule)
  apply (rule)
  apply (rule B[of "{}", simplified])
  apply (rule)
  apply (rule B)
  done
  
lemma cont_is_mono[simp]: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "cont f \<Longrightarrow> mono f"
  apply (rule monoI)
  apply (drule_tac C="{x,y}" in contD)
  apply (auto simp: le_iff_sup)
  done

lemma inf_distrib_is_mono[simp]: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "inf_distrib f \<Longrightarrow> mono f"
  by simp

text {* Only proven for complete lattices here. Also holds for CCPOs. *}
theorem kleene_lfp:
  fixes f:: "'a::complete_lattice \<Rightarrow> 'a"
  assumes CONT: "cont f"
  shows "lfp f = (SUP i. (f^^i) bot)"
proof (rule antisym)
  let ?K="{ (f^^i) bot | i . True}"
  note MONO=cont_is_mono[OF CONT]
  {
    fix i
    have "(f^^i) bot \<le> lfp f"
      apply (induct i)
      apply simp
      apply simp
      by (metis MONO lfp_unfold monoD)
  } thus "(SUP i. (f^^i) bot) \<le> lfp f" by (blast intro: SUP_least)
next
  show "lfp f \<le> (SUP i. (f^^i) bot)"
    apply (rule lfp_lowerbound)
    unfolding SUP_def
    apply (simp add: contD [OF CONT] del: Sup_image_eq)
    apply (rule Sup_subset_mono)
    apply (auto)
    apply (rule_tac x="Suc i" in range_eqI)
    apply auto
    done
qed


lemma (in galois_connection) dual_inf_dist_\<gamma>: "\<gamma> (Inf C) = Inf (\<gamma>`C)"
  apply (rule antisym)
  apply (rule Inf_greatest)
  apply clarify
  apply (rule monoD[OF \<gamma>_mono])
  apply (rule Inf_lower)
  apply simp

  apply (subst galois)
  apply (rule Inf_greatest)
  apply (subst galois[symmetric])
  apply (rule Inf_lower)
  apply simp
  done

lemma (in galois_connection) inf_dist_\<alpha>: "inf_distrib \<alpha>"
  apply (rule inf_distribI')
  apply (rule antisym)

  apply (subst galois[symmetric])
  apply (rule Sup_least)
  apply (subst galois)
  apply (rule Sup_upper)
  apply simp

  apply (rule Sup_least)
  apply clarify
  apply (rule monoD[OF \<alpha>_mono])
  apply (rule Sup_upper)
  apply simp
  done

subsection {* Maps *}
subsubsection {* Key-Value Set *}
  
  lemma map_to_set_simps[simp]: 
    "map_to_set Map.empty = {}"
    "map_to_set [a\<mapsto>b] = {(a,b)}"
    "map_to_set (m|`K) = map_to_set m \<inter> K\<times>UNIV"
    "map_to_set (m(x:=None)) = map_to_set m - {x}\<times>UNIV"
    "map_to_set (m(x\<mapsto>v)) = map_to_set m - {x}\<times>UNIV \<union> {(x,v)}"
    "map_to_set m \<inter> dom m\<times>UNIV = map_to_set m"
    "m k = Some v \<Longrightarrow> (k,v)\<in>map_to_set m"
    "single_valued (map_to_set m)"
    apply (simp_all)
    by (auto simp: map_to_set_def restrict_map_def split: split_if_asm
      intro: single_valuedI)
      
  lemma map_to_set_inj:     
    "(k,v)\<in>map_to_set m \<Longrightarrow> (k,v')\<in>map_to_set m \<Longrightarrow> v = v'"
    by (auto simp: map_to_set_def)


end
