theory MDP_Reachability_Problem
  imports Markov_Decision_Process
begin

lemma (in finite_measure) ereal_integral_real:
  assumes [measurable]: "f \<in> borel_measurable M" 
  assumes ae: "AE x in M. 0 \<le> f x" "AE x in M. f x \<le> ereal B"
  shows "ereal (\<integral>x. real (f x) \<partial>M) = (\<integral>\<^sup>+x. f x \<partial>M)"
proof (subst nn_integral_eq_integral[symmetric])
  show "integrable M (\<lambda>x. real (f x))"
    using ae by (intro integrable_const_bound[where B=B]) (auto simp: real_le_ereal_iff)
  show "AE x in M. 0 \<le> real (f x)"
    using ae by (auto simp: real_of_ereal_pos)
  show "(\<integral>\<^sup>+ x. ereal (real (f x)) \<partial>M) = integral\<^sup>N M f"
    using ae by (intro nn_integral_cong_AE) (auto simp: ereal_real)
qed

lemma (in MC_syntax) AE_not_suntil_coinduct [consumes 1, case_names \<psi> \<phi>]:
  assumes "P s"
  assumes \<psi>: "\<And>s. P s \<Longrightarrow> s \<notin> \<psi>"
  assumes \<phi>: "\<And>s t. P s \<Longrightarrow> s \<in> \<phi> \<Longrightarrow> t \<in> K s \<Longrightarrow> P t"
  shows "AE \<omega> in T s. not (HLD \<phi> suntil HLD \<psi>) (s ## \<omega>)"
proof -
  { fix \<omega> have "\<not> (HLD \<phi> suntil HLD \<psi>) (s ## \<omega>) \<longleftrightarrow>
      (\<forall>n. \<not> ((\<lambda>R. HLD \<psi> or (HLD \<phi> aand nxt R)) ^^ n) \<bottom> (s ## \<omega>))"
      unfolding suntil_def
      by (subst continuous_lfp)
         (auto simp add: Order_Continuity.continuous_def) }
  moreover 
  { fix n from `P s` have "AE \<omega> in T s. \<not> ((\<lambda>R. HLD \<psi> or (HLD \<phi> aand nxt R)) ^^ n) \<bottom> (s ## \<omega>)"
    proof (induction n arbitrary: s)
      case (Suc n) then show ?case
        apply (subst AE_T_iff)
        apply (rule measurable_compose[OF measurable_Stream, where M1="count_space UNIV"])
        apply measurable
        apply simp
        apply (auto simp: bot_fun_def intro!: AE_impI dest: \<phi> \<psi>)
        done
    qed simp }
  ultimately show ?thesis
    by (simp add: AE_all_countable)
qed

lemma (in MC_syntax) AE_not_suntil_coinduct_strong [consumes 1, case_names \<psi> \<phi>]:
  assumes "P s"
  assumes P_\<psi>: "\<And>s. P s \<Longrightarrow> s \<notin> \<psi>"
  assumes P_\<phi>: "\<And>s t. P s \<Longrightarrow> s \<in> \<phi> \<Longrightarrow> t \<in> K s \<Longrightarrow> P t \<or> 
    (AE \<omega> in T t. not (HLD \<phi> suntil HLD \<psi>) (t ## \<omega>))"
  shows "AE \<omega> in T s. not (HLD \<phi> suntil HLD \<psi>) (s ## \<omega>)" (is "?nuntil s")
proof -
  have "P s \<or> ?nuntil s"
    using `P s` by auto
  then show ?thesis
  proof (coinduction arbitrary: s rule: AE_not_suntil_coinduct)
    case (\<phi> t s) then show ?case
      by (auto simp: AE_T_iff[of _ s] suntil_Stream[of _ _ s] dest: P_\<phi>)
  qed (auto simp: suntil_Stream dest: P_\<psi>)
qed

declare [[coercion real_of_rat]]

lemma of_rat_setsum: "of_rat (\<Sum>a\<in>A. f a) = (\<Sum>a\<in>A. of_rat (f a))"
  by (induct rule: infinite_finite_induct) (auto simp: of_rat_add)

lemma setsum_strict_mono_single: 
  fixes f :: "_ \<Rightarrow> 'a :: {comm_monoid_add,ordered_cancel_ab_semigroup_add}"
  shows "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> f a < g a \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> f a \<le> g a) \<Longrightarrow> setsum f A < setsum g A"
  using setsum_strict_mono_ex1[of A f g] by auto

lemma prob_space_point_measure:
  "finite S \<Longrightarrow> (\<And>s. s \<in> S \<Longrightarrow> 0 \<le> p s) \<Longrightarrow> (\<Sum>s\<in>S. p s) = 1 \<Longrightarrow> prob_space (point_measure S p)"
  by (rule prob_spaceI) (simp add: space_point_measure emeasure_point_measure_finite)

lemma diff_mono:
  fixes a b c d :: "'a :: ordered_ab_group_add"
  assumes "a \<le> b" "d \<le> c" shows "a - c \<le> b - d"
  unfolding diff_conv_add_uminus by (intro add_mono le_imp_neg_le assms)

inductive_set directed_towards :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set" for A r where
  start: "\<And>x. x \<in> A \<Longrightarrow> x \<in> directed_towards A r"
| step: "\<And>x y. y \<in> directed_towards A r \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> x \<in> directed_towards A r"

hide_fact (open) start step

lemma directed_towards_mono:
  assumes "s \<in> directed_towards A F" "F \<subseteq> G" shows "s \<in> directed_towards A G"
  using assms by induct (auto intro: directed_towards.intros)


locale Reachability_Problem = Finite_Markov_Decision_Process K S for K :: "'s \<Rightarrow> 's pmf set" and S +
  fixes S1 S2 :: "'s set"
  assumes S1: "S1 \<subseteq> S" and S2: "S2 \<subseteq> S" and S1_S2: "S1 \<inter> S2 = {}"
begin

lemma [measurable]:
  "S \<in> sets (count_space UNIV)" "S1 \<in> sets (count_space UNIV)" "S2 \<in> sets (count_space UNIV)"
  by auto

definition
  "v = (\<lambda>cfg\<in>valid_cfg. emeasure (T cfg) {x\<in>space St. (HLD S1 suntil HLD S2) (state cfg ## x)})"

lemma v_eq: "cfg \<in> valid_cfg \<Longrightarrow>
    v cfg = emeasure (T cfg) {x\<in>space St. (HLD S1 suntil HLD S2) (state cfg ## x)}"
  by (auto simp add: v_def)

lemma v_nonneg: "cfg \<in> valid_cfg \<Longrightarrow> 0 \<le> v cfg"
  by (auto simp add: v_def emeasure_nonneg)

lemma real_v: "cfg \<in> valid_cfg \<Longrightarrow> real (v cfg) = \<P>(\<omega> in T cfg. (HLD S1 suntil HLD S2) (state cfg ## \<omega>))"
  by (auto simp add: v_def T.emeasure_eq_measure)

lemma v_le_1: "cfg \<in> valid_cfg \<Longrightarrow> v cfg \<le> 1"
  by (auto simp add: v_def T.emeasure_eq_measure one_ereal_def)

lemma v_neq_Pinf[simp]: "cfg \<in> valid_cfg \<Longrightarrow> v cfg \<noteq> \<infinity>"
  by (auto simp add: v_def)

lemma v_neq_Minf[simp]: "cfg \<in> valid_cfg \<Longrightarrow> v cfg \<noteq> - \<infinity>"
  by (auto simp add: v_def)

lemma v_neq_Inf[simp]: "cfg \<in> valid_cfg \<Longrightarrow> \<bar>v cfg\<bar> \<noteq> \<infinity>"
  by (auto intro!: ereal_infinity_cases)

lemma v_1_AE: "cfg \<in> valid_cfg \<Longrightarrow> v cfg = 1 \<longleftrightarrow> (AE \<omega> in T cfg. (HLD S1 suntil HLD S2) (state cfg ## \<omega>))"
  unfolding v_eq T.emeasure_eq_measure ereal_eq_1 space_T[symmetric, of cfg]
  by (rule T.prob_Collect_eq_1) simp

lemma v_0_AE: "cfg \<in> valid_cfg \<Longrightarrow> v cfg = 0 \<longleftrightarrow> (AE x in T cfg. not (HLD S1 suntil HLD S2) (state cfg ## x))"
  unfolding v_eq T.emeasure_eq_measure ereal_eq_0 space_T[symmetric, of cfg]
  by (rule T.prob_Collect_eq_0) simp

lemma v_S2[simp]: "cfg \<in> valid_cfg \<Longrightarrow> state cfg \<in> S2 \<Longrightarrow> v cfg = 1"
  using S2 by (subst v_1_AE) (auto simp: suntil_Stream)

lemma v_nS12[simp]: "cfg \<in> valid_cfg \<Longrightarrow> state cfg \<notin> S1 \<Longrightarrow> state cfg \<notin> S2 \<Longrightarrow> v cfg = 0"
  by (subst v_0_AE) (auto simp: suntil_Stream)

lemma v_nS[simp]: "cfg \<notin> valid_cfg \<Longrightarrow> v cfg = undefined"
  by (auto simp add: v_def)

lemma v_S1:
  assumes cfg[simp, intro]: "cfg \<in> valid_cfg" and cfg_S1[simp]: "state cfg \<in> S1"
  shows "v cfg = (\<integral>\<^sup>+s. v (cont cfg s) \<partial>action cfg)"
proof -
  have [simp]: "state cfg \<notin> S2"
    using cfg_S1 S1_S2 S1 by blast
  show ?thesis
    by (auto simp: v_eq emeasure_Collect_T[of _ cfg] K_cfg_def map_pmf.rep_eq nn_integral_distr
                   AE_measure_pmf_iff suntil_Stream[of _ _ "state cfg"]
                   valid_cfg_cont
             intro!: nn_integral_cong_AE)
qed

lemma real_v_integrable:
  "integrable (action cfg) (\<lambda>s. real (v (cont cfg s)))"
  by (rule measure_pmf.integrable_const_bound[where B="max 1 (real \<bar>undefined::ereal\<bar>)"])
     (auto simp add: v_def emeasure_nonneg measure_def[symmetric] le_max_iff_disj)

lemma real_v_integral_eq:
  assumes cfg[simp]: "cfg \<in> valid_cfg"
  shows "real (\<integral>\<^sup>+ s. v (cont cfg s) \<partial>action cfg) = \<integral> s. real (v (cont cfg s)) \<partial>action cfg"
 by (subst integral_eq_nn_integral)
    (auto simp: AE_measure_pmf_iff measure_nonneg v_eq T.emeasure_eq_measure valid_cfg_cont
          intro!: arg_cong[where f=real] nn_integral_cong_AE)

lemma v_eq_0_coinduct[consumes 3, case_names valid nS2 cont]:
  assumes *: "P cfg"
  assumes valid: "\<And>cfg. P cfg \<Longrightarrow> cfg \<in> valid_cfg"
  assumes nS2: "\<And>cfg. P cfg \<Longrightarrow> state cfg \<notin> S2"
  assumes cont: "\<And>cfg cfg'. P cfg \<Longrightarrow> state cfg \<in> S1 \<Longrightarrow> cfg' \<in> K_cfg cfg \<Longrightarrow> P cfg' \<or> v cfg' = 0"
  shows "v cfg = 0"
proof -
  from * valid[OF *]
  have "AE x in MC_syntax.T K_cfg cfg. \<not> (HLD S1 suntil HLD S2) (state cfg ## smap state x)"
    unfolding stream.map[symmetric] suntil_smap hld_smap'
  proof (coinduction arbitrary: cfg rule: MC.AE_not_suntil_coinduct_strong)
    case (\<psi> cfg) then show ?case
      by (auto simp del: cfg_onD_state dest: nS2)
  next
    case (\<phi> cfg' cfg)
    then have *: "P cfg" "state cfg \<in> S1" "cfg' \<in> K_cfg cfg" and [simp, intro]: "cfg \<in> valid_cfg"
      by auto
    with cont[OF *] show ?case
      by (subst (asm) v_0_AE)
         (auto simp: suntil_Stream T_def AE_distr_iff suntil_smap hld_smap' cong del: AE_cong)
  qed
  then have "AE \<omega> in T cfg. \<not> (HLD S1 suntil HLD S2) (state cfg ## \<omega>)"
    unfolding T_def by (subst AE_distr_iff) simp_all
  with valid[OF *] show ?thesis
    by (simp add: v_0_AE)
qed


definition "p = (\<lambda>s\<in>S. P_sup s (\<lambda>\<omega>. (HLD S1 suntil HLD S2) (s ## \<omega>)))"

lemma p_eq_SUP_v: "s \<in> S \<Longrightarrow> p s = (SUP cfg : cfg_on s. v cfg)"
  by (auto simp add: p_def v_def P_sup_def T.emeasure_eq_measure intro: valid_cfgI intro!: SUP_cong)

lemma v_le_p: "cfg \<in> valid_cfg \<Longrightarrow> v cfg \<le> p (state cfg)"
  by (subst p_eq_SUP_v) (auto intro!: SUP_upper dest: valid_cfgD valid_cfg_state_in_S)

lemma p_eq_0_imp: "cfg \<in> valid_cfg \<Longrightarrow> p (state cfg) = 0 \<Longrightarrow> v cfg = 0"
  using v_le_p[of cfg] v_nonneg[of cfg] by (auto intro: antisym)

lemma p_eq_0_iff: "s \<in> S \<Longrightarrow> p s = 0 \<longleftrightarrow> (\<forall>cfg\<in>cfg_on s. v cfg = 0)"
  unfolding p_eq_SUP_v by (subst SUP_eq_iff) (auto intro: v_nonneg[OF valid_cfgI])

lemma p_le_1: "s \<in> S \<Longrightarrow> p s \<le> 1"
  by (auto simp: p_eq_SUP_v intro!: SUP_least v_le_1 intro: valid_cfgI)

lemma p_nonneg: "s \<in> S \<Longrightarrow> 0 \<le> p s"
  by (auto simp: p_eq_SUP_v intro!: v_nonneg SUP_upper2[of "simple arb_act s"])

lemma p_undefined[simp]: "s \<notin> S \<Longrightarrow> p s = undefined"
  by (simp add: p_def)

lemma p_not_inf[simp]: "s \<in> S \<Longrightarrow> p s \<noteq> \<infinity>" "s \<in> S \<Longrightarrow> p s \<noteq> -\<infinity>"
  using p_nonneg[of s] p_le_1[of s] by auto

lemma p_S1: "s \<in> S1 \<Longrightarrow> p s = (\<Squnion>D\<in>K s. \<integral>\<^sup>+ t. p t \<partial>D)"
  using S1 S1_S2 K_closed[of s] unfolding p_def
  by (simp add: P_sup_iterate[of _ s] subset_eq set_eq_iff suntil_Stream[of _ _ s])
     (auto intro!: SUP_cong nn_integral_cong_AE simp add: AE_measure_pmf_iff)

lemma p_S2[simp]: "s \<in> S2 \<Longrightarrow> p s = 1"
  using S2 by (auto simp: v_S2[OF valid_cfgI] p_eq_SUP_v)

lemma p_nS12: "s \<in> S \<Longrightarrow> s \<notin> S1 \<Longrightarrow> s \<notin> S2 \<Longrightarrow> p s = 0"
  by (auto simp: p_eq_SUP_v v_nS12[OF valid_cfgI])


definition F_sup :: "('s \<Rightarrow> ereal) \<Rightarrow> 's \<Rightarrow> ereal" where
  "F_sup f = (\<lambda>s\<in>S. if s \<in> S2 then 1 else if s \<in> S1 then SUP D:K s. \<integral>\<^sup>+t. f t \<partial>D else 0)"

lemma F_sup_cong: "(\<And>s. s \<in> S \<Longrightarrow> f s = g s) \<Longrightarrow> F_sup f s = F_sup g s"
  using K_closed[of s]
  by (auto simp: F_sup_def AE_measure_pmf_iff subset_eq
              intro!: SUP_cong nn_integral_cong_AE)

lemma continuous_F_sup: "Order_Continuity.continuous F_sup"
  unfolding Order_Continuity.continuous_def fun_eq_iff F_sup_def[abs_def]
  by (auto simp:  SUP_apply[abs_def] nn_integral_monotone_convergence_SUP intro: SUP_commute)

lemma mono_F_sup: "mono F_sup"
  by (intro continuous_mono continuous_F_sup)

lemma F_sup_nonneg: "s \<in> S \<Longrightarrow> 0 \<le> F_sup F s"
  by (auto simp: F_sup_def intro!: SUP_upper2 nn_integral_nonneg intro: arb_actI)

lemma lfp_F_sup_iterate: "lfp F_sup = (SUP i. (F_sup ^^ i) (\<lambda>x\<in>S. 0))"
proof -
  { have "(SUP i. (F_sup ^^ i) \<bottom>) = (SUP i. (F_sup ^^ i) (\<lambda>x\<in>S. 0))"
    proof (rule SUP_eq)
      fix i show "\<exists>j\<in>UNIV. (F_sup ^^ i) \<bottom> \<le> (F_sup ^^ j) (\<lambda>x\<in>S. 0)"
        by (intro bexI[of _ i] funpow_mono mono_F_sup) auto
      have *: "(\<lambda>x\<in>S. 0) \<le> F_sup \<bottom>"
        using K_wf by (auto simp: F_sup_def le_fun_def) (blast intro: SUP_upper2 nn_integral_nonneg)
      show "\<exists>j\<in>UNIV. (F_sup ^^ i) (\<lambda>x\<in>S. 0) \<le> (F_sup ^^ j) \<bottom>"
        by (auto intro!: exI[of _ "Suc i"] funpow_mono mono_F_sup  *
                 simp del: funpow.simps simp add: funpow_Suc_right F_sup_nonneg le_funI)
    qed }
  then show ?thesis
    by (auto simp: continuous_lfp continuous_F_sup)
qed

lemma p_eq_lfp_F_sup: "p = lfp F_sup"
proof -
  { fix s assume "s \<in> S" let ?F = "\<lambda>P. HLD S2 or (HLD S1 aand nxt P)"
    have "P_sup s (\<lambda>\<omega>. (HLD S1 suntil HLD S2) (s ## \<omega>)) = (\<Squnion>i. P_sup s (\<lambda>\<omega>. (?F ^^ i) \<bottom> (s ## \<omega>)))"
    proof (simp add: suntil_def, rule P_sup_lfp)
      show "op ## s \<in> measurable St St"
        by simp
      (* This proof should work automatically *)
      fix P assume P: "Measurable.pred St P"
      show "Measurable.pred St (HLD S2 or (HLD S1 aand (\<lambda>\<omega>. P (stl \<omega>))))"
        by (intro pred_intros_logic measurable_compose[OF _ P] measurable_compose[OF measurable_shd]) auto
    qed (auto simp: Order_Continuity.continuous_def)
    also have "\<dots> = (SUP i. (F_sup ^^ i) (\<lambda>x\<in>S. 0) s)"
    proof (rule SUP_cong)
      fix i from `s \<in> S` show "P_sup s (\<lambda>\<omega>. (?F ^^ i) \<bottom> (s##\<omega>)) = (F_sup ^^ i) (\<lambda>x\<in>S. 0) s"
      proof (induct i arbitrary: s) 
        case (Suc n) show ?case
        proof (subst P_sup_iterate)
          (* This proof should work automatically *)
          show "Measurable.pred St (\<lambda>\<omega>. (?F ^^ Suc n) \<bottom> (s ## \<omega>))"
            apply (intro measurable_compose[OF measurable_Stream[OF measurable_const measurable_ident_sets[OF refl]] measurable_predpow])
            apply simp
            apply (simp add: bot_fun_def[abs_def])
            apply (intro pred_intros_logic measurable_compose[OF measurable_stl]  measurable_compose[OF measurable_shd])
            apply auto
            done
        next
          show "(\<Squnion>D\<in>K s. \<integral>\<^sup>+ t. P_sup t (\<lambda>\<omega>. (?F ^^ Suc n) \<bottom> (s ## t ## \<omega>)) \<partial>D) =
            (F_sup ^^ Suc n) (\<lambda>x\<in>S. 0) s"
            unfolding funpow.simps comp_def
            using S1 S2 `s \<in> S`
            by (subst F_sup_cong[OF Suc(1)[symmetric]])
               (auto simp add: F_sup_def measure_pmf.emeasure_space_1[simplified] K_wf subset_eq)
        qed
      qed simp
    qed simp
    finally have "lfp F_sup s = P_sup s (\<lambda>\<omega>. (HLD S1 suntil HLD S2) (s ## \<omega>))"
      by (simp add: lfp_F_sup_iterate) }
  moreover have "\<And>s. s \<notin> S \<Longrightarrow> lfp F_sup s = undefined"
    by (subst lfp_unfold[OF mono_F_sup]) (auto simp add: F_sup_def)
  ultimately show ?thesis
    by (auto simp: p_def)
qed

definition "S\<^sub>e = {s\<in>S. p s = 0}"

lemma S\<^sub>e: "S\<^sub>e \<subseteq> S"
  by (auto simp add: S\<^sub>e_def)

lemma v_S\<^sub>e: "cfg \<in> valid_cfg \<Longrightarrow> state cfg \<in> S\<^sub>e \<Longrightarrow> v cfg = 0"
  using p_eq_0_imp[of cfg] by (auto simp: S\<^sub>e_def)

lemma S\<^sub>e_nS2: "S\<^sub>e \<inter> S2 = {}"
  by (auto simp: S\<^sub>e_def)

lemma S\<^sub>e_E1: "s \<in> S\<^sub>e \<inter> S1 \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> t \<in> S\<^sub>e"
  unfolding S\<^sub>e_def using S1
  by (auto simp: p_S1 SUP_eq_iff K_wf nn_integral_nonneg nn_integral_0_iff_AE AE_measure_pmf_iff E_def
           intro: set_pmf_closed p_nonneg antisym
           cong: rev_conj_cong)

lemma S\<^sub>e_E2: "s \<in> S1 \<Longrightarrow> (\<And>t. (s, t) \<in> E \<Longrightarrow> t \<in> S\<^sub>e) \<Longrightarrow> s \<in> S\<^sub>e"
  unfolding S\<^sub>e_def using S1 S1_S2
  by (force simp: p_S1 SUP_eq_iff K_wf nn_integral_nonneg nn_integral_0_iff_AE AE_measure_pmf_iff E_def
            cong: rev_conj_cong)

lemma S\<^sub>e_E_iff: "s \<in> S1 \<Longrightarrow> s \<in> S\<^sub>e \<longleftrightarrow> (\<forall>t. (s, t) \<in> E \<longrightarrow> t \<in> S\<^sub>e)"
  using S\<^sub>e_E1[of s] S\<^sub>e_E2[of s] by blast

definition "S\<^sub>r = S - (S\<^sub>e \<union> S2)"

lemma S\<^sub>r: "S\<^sub>r \<subseteq> S"
  by (auto simp: S\<^sub>r_def)

lemma S\<^sub>r_S1: "S\<^sub>r \<subseteq> S1"
  by (auto simp: p_nS12 S\<^sub>r_def S\<^sub>e_def)

lemma S\<^sub>r_eq: "S\<^sub>r = S1 - S\<^sub>e"
  using S1_S2 S1 S2 by (auto simp add: S\<^sub>r_def S\<^sub>e_def p_nS12)

lemma v_neq_0_imp: "cfg \<in> valid_cfg \<Longrightarrow> v cfg \<noteq> 0 \<Longrightarrow> state cfg \<in> S\<^sub>r \<union> S2"
  using p_eq_0_imp[of cfg] by (auto simp add: S\<^sub>r_def S\<^sub>e_def valid_cfg_state_in_S)

lemma valid_cfg_action_in_K: "cfg \<in> valid_cfg \<Longrightarrow> action cfg \<in> K (state cfg)"
  by (auto dest!: valid_cfgD)

lemma K_cfg_E: "cfg \<in> valid_cfg \<Longrightarrow> cfg' \<in> K_cfg cfg \<Longrightarrow> (state cfg, state cfg') \<in> E"
  by (auto simp: E_def K_cfg_def set_pmf_map valid_cfg_action_in_K)

lemma S\<^sub>r_directed_towards_S2:
  assumes s: "s \<in> S\<^sub>r"
  shows "s \<in> directed_towards S2 {(s, t) | s t. s \<in> S\<^sub>r \<and> (s, t) \<in> E}" (is "s \<in> ?D")
proof -
  { fix cfg assume "s \<notin> ?D" "cfg \<in> cfg_on s"
    with s S\<^sub>r have "state cfg \<in> S\<^sub>r" "state cfg \<notin> ?D" "cfg \<in> valid_cfg"
      by (auto intro: valid_cfgI)
    then have "v cfg = 0"
    proof (coinduction arbitrary: cfg rule: v_eq_0_coinduct)
      case (cont cfg' cfg)
      with v_neq_0_imp[of cfg'] show ?case
        by (auto intro: directed_towards.intros K_cfg_E)
    qed (auto intro: directed_towards.intros) }
  with p_eq_0_iff[of s] s show ?thesis
    unfolding S\<^sub>r_def S\<^sub>e_def by blast
qed

definition "proper ct \<longleftrightarrow> ct \<in> Pi\<^sub>E S K \<and> (\<forall>s\<in>S\<^sub>r. v (simple ct s) > 0)"

lemma S\<^sub>r_nS2: "s \<in> S\<^sub>r \<Longrightarrow> s \<notin> S2"
  by (auto simp: S\<^sub>r_def)

lemma properD1: "proper ct \<Longrightarrow> ct \<in> Pi\<^sub>E S K"
  by (auto simp: proper_def)

lemma proper_eq:
  assumes ct[simp, intro]: "ct \<in> Pi\<^sub>E S K"
  shows "proper ct \<longleftrightarrow> S\<^sub>r \<subseteq> directed_towards S2 (SIGMA s:S\<^sub>r. ct s)"
    (is "_ \<longleftrightarrow> _ \<subseteq> ?D")
proof -
  have *[simp]: "\<And>s. s \<in> S\<^sub>r \<Longrightarrow> s \<in> S" and ct': "ct \<in> Pi S K"
    using ct by (auto simp: S\<^sub>r_def simp del: ct)
  { fix s t have "s \<in> S \<Longrightarrow> t \<in> ct s \<Longrightarrow> t \<in> S"
      using K_closed[of s] ct' by (auto simp add: subset_eq) }
  note ct_closed = this

  let ?C = "simple ct"
  from ct have valid_C[simp]: "\<And>s. s \<in> S \<Longrightarrow> ?C s \<in> valid_cfg"
    by (auto simp add: PiE_def)
  { fix s assume "s \<in> ?D"
    then have "0 < v (?C s)"
    proof induct
      case (step s t)
      then have s: "s \<in> S\<^sub>r" and t: "t \<in> ct s" and [simp]: "s \<in> S"
        by auto
      with S\<^sub>r_S1 ct have "v (?C s) = (\<integral>\<^sup>+t. v (?C t) \<partial>ct s)"
        by (subst v_S1) auto
      also have "\<dots> \<noteq> 0"
        using ct t
        by (subst nn_integral_0_iff_AE) (auto simp add: Pi_iff AE_measure_pmf_iff not_le step intro!: bexI[of _ t])
      finally show ?case
        using ct by (auto simp add: less_le v_nonneg)
    qed (subst v_S2, insert S2, auto) }
  moreover
  { fix s assume s: "s \<notin> ?D" "s \<in> S\<^sub>r"
    with ct' have C: "?C s \<in> cfg_on s" and [simp]: "s \<in> S"
      by auto
    from s have "v (?C s) = 0"
    proof (coinduction arbitrary: s rule: v_eq_0_coinduct)
      case (cont cfg s)
      with S1 obtain t where "cfg = ?C t" "t \<in> ct s" "s \<in> S"
        by (auto simp: set_K_cfg subset_eq)
      with cont(1,2) v_neq_0_imp[of "?C t"] ct_closed[of s t] show ?case
        by (intro exI[of _ t] disjCI) (auto intro: directed_towards.intros)
    qed (auto simp: S\<^sub>r_nS2) }
  ultimately show ?thesis
    unfolding proper_def using ct by (force simp del: v_nS v_S2 v_nS12 ct)
qed

lemma exists_proper:
  obtains ct where "proper ct"
proof atomize_elim
  def r \<equiv> "rec_nat S2 (\<lambda>_ S'. {s\<in>S\<^sub>r. \<exists>t\<in>S'. (s, t) \<in> E})"
  then have [simp]: "r 0 = S2" "\<And>n. r (Suc n) = {s\<in>S\<^sub>r. \<exists>t\<in>r n. (s, t) \<in> E}"
    by simp_all

  { fix s assume "s \<in> S\<^sub>r"
    then have "s \<in> directed_towards S2 {(s, t) | s t. s \<in> S\<^sub>r \<and> (s, t) \<in> E}"
      by (rule S\<^sub>r_directed_towards_S2)
    from this `s\<in>S\<^sub>r` have "\<exists>n. s \<in> r n"
    proof induction
      case (step s t)
      show ?case
      proof cases
        assume "t \<in> S2" with step.prems step.hyps show ?thesis
          by (intro exI[of _ "Suc 0"]) force
      next
        assume "t \<notin> S2"
        with step obtain n where "t \<in> r n" "t \<in> S\<^sub>r"
          by (auto elim: directed_towards.cases)
        with `t\<in>S\<^sub>r` step.hyps show ?thesis
          by (intro exI[of _ "Suc n"]) force
      qed
    qed (simp add: S\<^sub>r_def) }
  note r = this

  { fix s assume "s \<in> S"
    have "\<exists>D\<in>K s. s \<in> S\<^sub>r \<longrightarrow> (\<exists>t\<in>D. \<exists>n. t \<in> r n \<and> (\<forall>m. s \<in> r m \<longrightarrow> n < m))"
    proof cases
      assume s: "s \<in> S\<^sub>r"
      def n \<equiv> "LEAST n. s \<in> r n"
      then have "s \<in> r n" and n: "\<And>i. i < n \<Longrightarrow> s \<notin> r i"
        using r s by (auto intro: LeastI_ex dest: not_less_Least)
      with s have "n \<noteq> 0"
        by (intro notI) (auto simp: S\<^sub>r_def)
      then obtain n' where "n = Suc n'"
        by (cases n) auto
      with `s \<in> r n` obtain t D where "D \<in> K s" "t \<in> D" "t \<in> r n'"
        by (auto simp: E_def)
      with n `n = Suc n'` s show ?thesis
        by (auto intro!: bexI[of _ D] bexI[of _ t] exI[of _ n'] simp: not_less_eq[symmetric])
    qed (insert K_wf `s\<in>S`, auto) }
  then obtain ct where ct: "\<And>s. s \<in> S \<Longrightarrow> ct s \<in> K s"
    "\<And>s. s \<in> S \<Longrightarrow> s \<in> S\<^sub>r \<Longrightarrow> \<exists>t\<in>ct s. \<exists>n. t \<in> r n \<and> (\<forall>m. s \<in> r m \<longrightarrow> n < m)"
    by metis
  then have *: "restrict ct S \<in> Pi\<^sub>E S K"
    by auto

  moreover
  { fix s assume "s \<in> S\<^sub>r"
    then obtain n where "s \<in> r n"
      by (metis r)
    with `s \<in> S\<^sub>r` have "s \<in> directed_towards S2 (SIGMA s : S\<^sub>r. ct s)"
    proof (induction n arbitrary: s rule: less_induct)
      case (less n s)
      moreover with S\<^sub>r have "s \<in> S" by auto
      ultimately obtain t m where "t \<in> ct s" "t \<in> r m" "m < n"
        using ct[of s] by (auto simp: E_def)
      with less.IH[of m t] `s \<in> S\<^sub>r` show ?case
        by (cases m) (auto intro: directed_towards.intros)
    qed }

  ultimately show "\<exists>ct. proper ct"
    using S\<^sub>r S2
    by (auto simp: proper_eq[OF *] subset_eq
             intro!: exI[of _ "restrict ct S"]
             cong: Sigma_cong)
qed

definition "l_desc X ct l s \<longleftrightarrow>
    s \<in> directed_towards S2 (SIGMA s : X. {l s}) \<and>
    v (simple ct s) \<le> v (simple ct (l s)) \<and>
    l s \<in> maximal (\<lambda>s. v (simple ct s)) (ct s)"

lemma exists_l_desc:
  assumes ct: "proper ct"
  shows "\<exists>l\<in>S\<^sub>r \<rightarrow> S\<^sub>r \<union> S2. \<forall>s\<in>S\<^sub>r. l_desc S\<^sub>r ct l s"
proof -
  have ct_closed: "\<And>s t. s \<in> S \<Longrightarrow> t \<in> ct s \<Longrightarrow> t \<in> S"
    using ct K_closed by (auto simp: proper_def PiE_iff)
  have ct_Pi: "ct \<in> Pi S K"
    using ct by (auto simp: proper_def)

  have "finite S\<^sub>r"
    using S_finite by (auto simp: S\<^sub>r_def)
  then show ?thesis
  proof (induct rule: finite_induct_select)
    case (select X)
    then obtain l where l: "l \<in> X \<rightarrow> X \<union> S2" and desc: "\<And>s. s \<in> X \<Longrightarrow> l_desc X ct l s"
      by auto
    obtain x where x: "x \<in> S\<^sub>r - X"
      using `X \<subset> S\<^sub>r` by auto
    then have "x \<in> S"
      by (auto simp: S\<^sub>r_def)

    let ?C = "simple ct"
    let ?v = "\<lambda>s. v (?C s)" and ?E = "\<lambda>s. set_pmf (ct s)"
    let ?M = "\<lambda>s. maximal ?v (?E s)"

    have finite_E[simp]: "\<And>s. s \<in> S \<Longrightarrow> finite (?E s)"
      using K_closed ct by (intro finite_subset[OF _ S_finite]) (auto simp: proper_def subset_eq)

    have valid_C[simp]: "\<And>s. s \<in> S \<Longrightarrow> ?C s \<in> valid_cfg"
      using ct by (auto simp: proper_def intro!: simple_valid_cfg)
    
    have E_ne[simp]: "\<And>s. ?E s \<noteq> {}"
        by (rule set_pmf_not_empty)

    have "\<exists>s\<in>S\<^sub>r - X. \<exists>t\<in>?M s. t \<in> S2 \<union> X"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have not_M: "\<And>s. s \<in> S\<^sub>r - X \<Longrightarrow> ?M s \<inter> (S2 \<union> X) = {}"
        by auto

      let ?S\<^sub>m = "maximal ?v (S\<^sub>r - X)"

      have "finite (S\<^sub>r - X)" "S\<^sub>r - X \<noteq> {}"
        using `X \<subset> S\<^sub>r` by (auto intro!: finite_subset[OF _ S_finite] simp: S\<^sub>r_def)
      from maximal_ne[OF this] obtain s\<^sub>m where s\<^sub>m: "s\<^sub>m \<in> ?S\<^sub>m"
        by force

      have "\<exists>s\<^sub>0\<in>?S\<^sub>m. \<exists>t\<in>?E s\<^sub>0. t \<notin> ?S\<^sub>m"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have S\<^sub>m: "\<And>s\<^sub>0 t. s\<^sub>0 \<in> ?S\<^sub>m \<Longrightarrow> t \<in> ?E s\<^sub>0 \<Longrightarrow> t \<in> ?S\<^sub>m" by blast
        from `s\<^sub>m \<in> ?S\<^sub>m` have [simp]: "s\<^sub>m \<in> S" and "s\<^sub>m \<in> S\<^sub>r"
          by (auto simp: S\<^sub>r_def dest: maximalD1)

        from `s\<^sub>m \<in> ?S\<^sub>m` have "v (?C s\<^sub>m) = 0"
        proof (coinduction arbitrary: s\<^sub>m rule: v_eq_0_coinduct)
          case (cont t s\<^sub>m) with S1 show ?case
            by (intro exI[of _ "state t"] disjCI conjI S\<^sub>m[of s\<^sub>m "state t"])
               (auto simp: set_K_cfg)
        qed (auto simp: S\<^sub>r_def ct_Pi dest!: maximalD1)
        with `s\<^sub>m \<in> S\<^sub>r` `proper ct` show False
          by (auto simp: proper_def)
      qed
      then obtain s\<^sub>0 t where "s\<^sub>0 \<in> ?S\<^sub>m" and t: "t \<in> ?E s\<^sub>0" "t \<notin> ?S\<^sub>m"
        by metis
      with S\<^sub>r_S1 have s\<^sub>0: "s\<^sub>0 \<in> S\<^sub>r - X" and [simp]: "s\<^sub>0 \<in> S" and "s\<^sub>0 \<in> S1"
        by (auto simp: S\<^sub>r_def dest: maximalD1)

      { fix t assume t: "t \<in> S2 \<union> X" "t \<in> ?E s\<^sub>0" and "?v s\<^sub>0 \<le> ?v t"
        have "maximal ?v (?E s\<^sub>0 \<inter> (S2 \<union> X)) \<noteq> {}"
          using finite_E t by (intro maximal_ne) auto
        moreover
        { fix x y assume x: "x \<in> S2 \<union> X" "x \<in> ?E s\<^sub>0" 
            and *: "\<forall>y\<in>?E s\<^sub>0 \<inter> (S2 \<union> X). ?v y \<le> ?v x" and y: "y \<in> ?E s\<^sub>0"
          with S2 `s\<^sub>0 \<in> S`[THEN ct_closed] have [simp]: "x \<in> S" "y \<in> S"
            by auto

          have "?v y \<le> ?v x"
          proof cases
            assume "y \<in> S\<^sub>r - X"
            then have "?v y \<le> ?v s\<^sub>0"
              using `s\<^sub>0 \<in> ?S\<^sub>m` by (auto intro: maximalD2)
            also note `?v s\<^sub>0 \<le> ?v t`
            also have "?v t \<le> ?v x"
              using * t by auto
            finally show ?thesis .
          next
            assume "y \<notin> S\<^sub>r - X" with y * show ?thesis
              by (auto simp: S\<^sub>r_def v_S\<^sub>e[of "?C y"] v_nonneg[of "?C x"] ct_Pi)
          qed }
        then have "maximal ?v (?E s\<^sub>0 \<inter> (S2 \<union> X)) \<subseteq> maximal ?v (?E s\<^sub>0)"
          by (auto simp: maximal_def)
        moreover note not_M[OF s\<^sub>0]
        ultimately have False
          by (blast dest: maximalD1) }
      then have less_s\<^sub>0: "\<And>t. t \<in> S2 \<union> X \<Longrightarrow> t \<in> ?E s\<^sub>0 \<Longrightarrow> ?v t < ?v s\<^sub>0"
        by (auto simp add: not_le[symmetric])

      let ?K = "ct s\<^sub>0"
      from `proper ct` `s\<^sub>0 \<in> S` s\<^sub>0 have "?v s\<^sub>0 \<noteq> 0"
        by (auto simp add: proper_def)

      have "?v s\<^sub>0 = (\<integral>\<^sup>+ x. ?v x \<partial>?K)"
        using v_S1[of "?C s\<^sub>0"] `s\<^sub>0 \<in> S1` `s\<^sub>0 \<in> S` by (simp add: ct_Pi)
      also have "\<dots> < (\<integral>\<^sup>+x. ?v s\<^sub>0 \<partial>?K)"
      proof (intro nn_integral_less)
        have "(\<integral>\<^sup>+x. ?v x \<partial>?K) \<le> (\<integral>\<^sup>+x. 1 \<partial>?K)"
          using ct ct_closed[of s\<^sub>0]
          by (intro nn_integral_mono_AE)
             (auto intro!: v_le_1 simp: AE_measure_pmf_iff proper_def ct_Pi)
        then show "(\<integral>\<^sup>+x. ?v x \<partial>?K) \<noteq> \<infinity>"
          by auto
        have "?v t < ?v s\<^sub>0"
        proof cases
          assume "t \<in> S2 \<union> X" then show ?thesis
            using less_s\<^sub>0[of t] t by simp
        next
          assume "t \<notin> S2 \<union> X"
          show ?thesis
          proof cases
            assume "t \<in> S\<^sub>e" with `?v s\<^sub>0 \<noteq> 0` v_S\<^sub>e[of "?C t"] S\<^sub>e v_nonneg[of "?C s\<^sub>0"] show ?thesis
              by (auto simp: subset_eq ct_Pi)
          next
            assume "t \<notin> S\<^sub>e"
            with t(1) `t \<notin> S2 \<union> X` ct_closed[of s\<^sub>0 t] have "t \<in> S\<^sub>r - X"
              unfolding S\<^sub>r_def by (auto simp: E_def)
            with t(2) show ?thesis
              using `s\<^sub>0 \<in> ?S\<^sub>m` by (auto simp: maximal_def not_le intro: less_le_trans)
          qed
        qed
        then show "\<not> (AE x in ?K. ?v s\<^sub>0 \<le> ?v x)"
          using t by (auto simp: not_le AE_measure_pmf_iff E_def cong del: AE_cong intro!: exI[of _ "t"])

        show "AE x in ?K. ?v x \<le> ?v s\<^sub>0"
        proof (subst AE_measure_pmf_iff, safe)
          fix t assume t: "t \<in> ?E s\<^sub>0"
          show "?v t \<le> ?v s\<^sub>0"
          proof cases
            assume "t \<in> S2 \<union> X" then show ?thesis
              using less_s\<^sub>0[of t] t by simp
          next
            assume "t \<notin> S2 \<union> X"
            show ?thesis
            proof cases
              assume "t \<in> S\<^sub>e"
              then have "?v t = 0"
                by (simp add: p_eq_0_imp S\<^sub>e_def ct_Pi)
              with `?v s\<^sub>0 \<noteq> 0` show ?thesis
                by (auto simp: v_nonneg ct_Pi)
            next
              assume "t \<notin> S\<^sub>e" with t `s\<^sub>0 \<in> ?S\<^sub>m` `t \<notin> S2 \<union> X` `s\<^sub>0 \<in> S` show ?thesis
                by (elim maximalD2) (auto simp: S\<^sub>r_def intro!: ct_closed[of _ t])
            qed
          qed
        qed
      next
        show "AE x in measure_pmf (ct s\<^sub>0). 0 \<le> v (?C x)"
          using ct_Pi K_closed[of s\<^sub>0] `s\<^sub>0 \<in> S`
          by (auto simp add: AE_measure_pmf_iff subset_eq Pi_iff intro!: v_nonneg[OF valid_C])
      qed auto
      also have "\<dots> = ?v s\<^sub>0"
        using `s\<^sub>0 \<in> S` measure_pmf.emeasure_space_1[of "ct s\<^sub>0"] by (simp add: v_nonneg[OF valid_C])
      finally show False
        by simp
    qed
    then obtain s t where s: "s \<in> S\<^sub>r - X" and t: "t \<in> S2 \<union> X" "t \<in> ?M s"
      by auto
    with S2 `X \<subset> S\<^sub>r` have "s \<notin> S2" and "s \<in> S \<and> s \<notin> S2" and "s \<notin> X"and [simp]: "t \<in> S"
      by (auto simp add: S\<^sub>r_def)
    def l' \<equiv> "l(s := t)"
    then have l'_s[simp, intro]: "l' s = t"
      by simp

    let ?D = "\<lambda>X l. directed_towards S2 (SIGMA s : X. {l s})"
    { fix s' assume "s' \<in> ?D X l" "s' \<in> X"
      from this(1) have "s' \<in> ?D (insert s X) l'"
        by (rule directed_towards_mono) (auto simp: l'_def `s \<notin> X`) }
    note directed_towards_l' = this

    show ?case
    proof (intro bexI ballI, elim insertE)
      show "s \<in> S\<^sub>r - X" by fact
      show "l' \<in> insert s X \<rightarrow> insert s X \<union> S2"
        using s t l by (auto simp: l'_def)
    next
      fix s' assume s': "s' \<in> X"
      moreover
      from desc[OF this] have "s' \<in> ?D X l" and *: "?v s' \<le> ?v (l s')" "l s' \<in> ?M s'"
        by (auto simp: l_desc_def)
      moreover have "l' s' = l s'"
        using `s' \<in> X` s by (auto simp add: l'_def)
      ultimately show "l_desc (insert s X) ct l' s'"
        by (auto simp: l_desc_def intro!: directed_towards_l')
    next
      fix s' assume "s' = s"
      show "l_desc (insert s X) ct l' s'"
        unfolding `s' = s` l_desc_def l'_s
      proof (intro conjI)
        show "s \<in> ?D (insert s X) l'"
        proof cases
          assume "t \<notin> S2"
          with t have "t \<in> X" by auto
          with desc have "t \<in> ?D X l"  
            by (simp add: l_desc_def)
          then show ?thesis
            by (force intro: directed_towards.step[OF directed_towards_l'] `t \<in> X`)
        qed (force intro: directed_towards.step directed_towards.start)

        from `s \<in> S\<^sub>r - X` S\<^sub>r_S1 have [simp]: "s \<in> S1" "s \<in> S"
          by (auto simp: S\<^sub>r_def)
        show "?v s \<le> ?v t"
          using t(2)[THEN maximalD2] ct
          by (auto simp add: v_S1 AE_measure_pmf_iff proper_def Pi_iff PiE_def
                   intro!: measure_pmf.nn_integral_le_const v_nonneg)
      qed fact
    qed
  qed simp
qed

lemma F_v_memoryless:
  obtains ct where "ct \<in> Pi\<^sub>E S K" "v\<circ>simple ct = F_sup (v\<circ>simple ct)"
proof atomize_elim
  def R \<equiv> "{(ct(s := D), ct) | ct s D.
    ct \<in> Pi\<^sub>E S K \<and> proper ct \<and>
    s \<in> S\<^sub>r \<and> D \<in> K s \<and> v (simple ct s) < (\<integral>\<^sup>+t. v (simple ct t) \<partial>D) }"

  { fix ct ct' assume ct_ct': "(ct', ct) \<in> R"
    let ?v = "\<lambda>s. v (simple ct s)" and ?v' = "\<lambda>s. v (simple ct' s)"

    from ct_ct' obtain s D where "ct \<in> Pi\<^sub>E S K" "proper ct" and s: "s \<in> S\<^sub>r" and D: "D \<in> K s"
      and not_maximal: "?v s < (\<integral>\<^sup>+t. ?v t \<partial>D)" and ct'_eq: "ct' = ct(s := D)"
      by (auto simp: R_def)
    with S\<^sub>r_S1 have ct: "ct \<in> Pi S K" and "s \<in> S" and "s \<in> S1"
      by (auto simp: S\<^sub>r_def)
    then have valid_ct[simp]: "\<And>s. s \<in> S \<Longrightarrow> simple ct s \<in> cfg_on s"
      by simp

    from ct'_eq have [simp]: "ct' s = D" "\<And>t. t \<noteq> s \<Longrightarrow> ct' t = ct t"
      by simp_all

    from ct_ct' S\<^sub>r have ct'_E: "ct' \<in> Pi\<^sub>E S K"
      by (auto simp: ct'_eq R_def)
    from ct s D have ct': "ct' \<in> Pi S K"
      by (auto simp: ct'_eq)
    then have valid_ct'[simp]: "\<And>s. s \<in> S \<Longrightarrow> simple ct' s \<in> cfg_on s"
      by simp
    
    from exists_l_desc[OF `proper ct`]
    obtain l where l: "l \<in> S\<^sub>r \<rightarrow> S\<^sub>r \<union> S2" and "\<And>s. s \<in> S\<^sub>r \<Longrightarrow> l_desc S\<^sub>r ct l s"
      by auto
    then have directed_l: "\<And>s. s \<in> S\<^sub>r \<Longrightarrow> s \<in> directed_towards S2 (SIGMA s:S\<^sub>r. {l s})"
      and v_l_mono: "\<And>s. s \<in> S\<^sub>r \<Longrightarrow> ?v s \<le> ?v (l s)"
      and l_in_Ea: "\<And>s. s \<in> S\<^sub>r \<Longrightarrow> l s \<in> ct s"
      by (auto simp: l_desc_def dest!: maximalD1)

    let ?E = "\<lambda>ct. SIGMA s:S\<^sub>r. ct s"
    let ?D = "\<lambda>ct. directed_towards S2 (?E ct)"

    have finite_E[simp]: "\<And>s. s \<in> S \<Longrightarrow> finite (ct' s)"
      using ct' K_closed by (intro rev_finite_subset[OF S_finite]) auto
    
    have "maximal ?v (ct' s) \<noteq> {}"
      using ct' D `s\<in>S` finite_E[of s] by (intro maximal_ne set_pmf_not_empty) (auto simp del: finite_E)
    then obtain s' where s': "s' \<in> maximal ?v (ct' s)"
      by blast
    with K_closed[OF `s \<in> S`] D have "s' \<in> S"
      by (auto dest!: maximalD1)

    have "s' \<noteq> s"
    proof
      assume [simp]: "s' = s"
      have "?v s < (\<integral>\<^sup>+t. ?v t \<partial>D)"
        by fact
      also have "\<dots> \<le> (\<integral>\<^sup>+t. ?v s \<partial>D)"
        using `s \<in> S` s' D by (intro nn_integral_mono_AE) (auto simp: AE_measure_pmf_iff intro: maximalD2)
      finally show False
        using measure_pmf.emeasure_space_1[of D] by (simp add: v_nonneg `s \<in> S` ct)
    qed

    have "p s' \<noteq> 0"
    proof
      assume "p s' = 0"
      then have "?v s' = 0"
        using v_le_p[of "simple ct s'"] ct `s' \<in> S` by (auto intro!: antisym v_nonneg ct)
      then have "(\<integral>\<^sup>+t. ?v t \<partial>D) = 0"
        using maximalD2[OF s'] by (subst nn_integral_0_iff_AE) (auto simp: `s\<in>S` D AE_measure_pmf_iff)
      then have "?v s < 0"
        using not_maximal by auto
      then show False
        using v_nonneg[of "simple ct s"] `s\<in>S` by (simp add: ct)
    qed
    with `s' \<in> S` have "s' \<in> S2 \<union> S\<^sub>r"
      by (auto simp: S\<^sub>r_def S\<^sub>e_def)

    have l_acyclic: "(s', s) \<notin> (SIGMA s:S\<^sub>r. {l s})^+"
    proof
      assume "(s', s) \<in> (SIGMA s:S\<^sub>r. {l s})^+"
      then have "?v s' \<le> ?v s"  
        by induct (blast intro: order_trans v_l_mono)+
      also have "\<dots> < (\<integral>\<^sup>+t. ?v t \<partial>D)"
        using not_maximal .
      also have "\<dots> \<le> (\<integral>\<^sup>+t. ?v s' \<partial>D)"
        using s' by (intro nn_integral_mono_AE) (auto simp: `s \<in> S` D AE_measure_pmf_iff intro: maximalD2)
      finally show False
        using measure_pmf.emeasure_space_1[of D] by (simp add: v_nonneg `s' \<in> S` ct)
    qed

    from `s' \<in> S2 \<union> S\<^sub>r` have "s' \<in> ?D ct'"
    proof
      assume "s' \<in> S\<^sub>r"
      then have "l s' \<in> directed_towards S2 (SIGMA s:S\<^sub>r. {l s})"
        using l directed_l[of "l s'"] by (auto intro: directed_towards.start)
      moreover from `s' \<in> S\<^sub>r` have "(s', l s') \<in> (SIGMA s:S\<^sub>r. {l s})^+"
        by auto
      ultimately have "l s' \<in> ?D ct'"
      proof induct
        case (step t t')
        then have t: "t \<noteq> s" "t \<in> S\<^sub>r" "t' = l t"
          using l_acyclic by auto

        from step have "(s', t') \<in> (SIGMA s:S\<^sub>r. {l s})\<^sup>+"
          by (blast intro: trancl_into_trancl)
        from step(2)[OF this] show ?case
          by (rule directed_towards.step) (simp add: l_in_Ea t)
      qed (rule directed_towards.start)
      then show "s' \<in> ?D ct'"
        by (rule directed_towards.step)
           (simp add: l_in_Ea `s' \<in> S\<^sub>r` `s \<in> S\<^sub>r` `s' \<noteq> s`)
    qed (rule directed_towards.start)

    have proper: "proper ct'"
      unfolding proper_eq[OF ct'_E]
    proof
      fix t assume "t \<in> S\<^sub>r"
      from directed_l[OF this] show "t \<in> ?D ct'"
      proof induct
        case (step t t')
        show ?case
        proof cases
          assume "t = s"
          with `s \<in> S\<^sub>r` s'[THEN maximalD1] have "(t, s') \<in> ?E ct'"
            by auto
          with `s' \<in> ?D ct'` show ?thesis
            by (rule directed_towards.step)
        next
          assume "t \<noteq> s"
          with step have "(t, t') \<in> ?E ct'"
            by (auto simp: l_in_Ea)
          with step.hyps(2) show ?thesis
            by (rule directed_towards.step)
        qed
      qed (rule directed_towards.start)
    qed

    have "?v \<le> ?v'"
    proof (intro le_funI leI notI)
      fix t' assume *: "?v' t' < ?v t'"
      then have "t' \<in> S"
        by (metis v_nS simple_valid_cfg_iff ct' ct order.irrefl)

      def \<Delta> \<equiv> "\<lambda>t. real (?v t) - real (?v' t)"
      with * `t' \<in> S` v_nonneg[of "simple ct' t'"] have "0 < \<Delta> t'"
        by (cases "?v t'" "?v' t'" rule: ereal2_cases) (auto simp add: ct' ct)

      { fix t assume t: "t \<in> maximal \<Delta> S"
        with `t' \<in> S` have "\<Delta> t' \<le> \<Delta> t"
          by (auto intro: maximalD2)
        with `0 < \<Delta> t'` have "0 < \<Delta> t" by simp
        with t have "t \<in> S\<^sub>r"
          by (auto simp add: S\<^sub>r_def v_S\<^sub>e ct ct' \<Delta>_def dest!: maximalD1) }
      note max_is_S\<^sub>r = this

      { fix s assume "s \<in> S"
        with v_nonneg[of "simple ct' s"] v_le_1[of "simple ct' s"] 
             v_nonneg[of "simple ct s"] v_le_1[of "simple ct s"]
        have "\<bar>\<Delta> s\<bar> \<le> 1"
          by (cases "?v s" "?v' s" rule: ereal2_cases)
             (auto simp: \<Delta>_def one_ereal_def abs_real_def ct ct') }
      note \<Delta>_le_1[simp] = this
      then have ereal_\<Delta>: "\<And>s. s \<in> S \<Longrightarrow> \<Delta> s = ?v s - ?v' s"
        by (auto simp add: \<Delta>_def v_def T.emeasure_eq_measure ct ct')
      
      from `s \<in> S` S_finite have "maximal \<Delta> S \<noteq> {}"
        by (intro maximal_ne) auto
      then obtain t where "t \<in> maximal \<Delta> S" by auto
      from max_is_S\<^sub>r[OF this] proper have "t \<in> ?D ct'"
        unfolding proper_eq[OF ct'_E] by auto
      from this `t \<in> maximal \<Delta> S` show False
      proof induct
        case (start t)
        then have "t \<in> S\<^sub>r"
          by (intro max_is_S\<^sub>r)
        with `t \<in> S2` show False
          by (auto simp: S\<^sub>r_def)
      next
        case (step t t')
        then have t': "t' \<in> ct' t" and "t \<in> S\<^sub>r" and t: "t \<in> maximal \<Delta> S"
          by (auto intro: max_is_S\<^sub>r simp: comp_def)
        then have "t' \<in> S" "t \<in> S1" "t \<in> S"
          using S\<^sub>r_S1 S1 
          by (auto simp: Pi_closed[OF ct'])
  
        have "\<Delta> t \<le> \<Delta> t'"
        proof (intro leI notI)
          assume less: "\<Delta> t' < \<Delta> t"
          have "(\<integral>s. \<Delta> s \<partial>ct' t) < (\<integral>s. \<Delta> t \<partial>ct' t)"
          proof (intro measure_pmf.integral_less_AE)
            show "emeasure (ct' t) {t'} \<noteq> 0" "{t'} \<in> sets (ct' t)"
              "AE s in ct' t. s\<in>{t'} \<longrightarrow> \<Delta> s \<noteq> \<Delta> t"
              using t' less by (auto simp add: emeasure_pmf_single_eq_zero_iff)
            show "AE s in ct' t. \<Delta> s \<le> \<Delta> t"
              using ct' ct t D
              by (auto simp add: AE_measure_pmf_iff ct `t\<in>S` Pi_iff E_def Pi_closed[OF ct']
                       intro!: maximalD2[of t \<Delta>] intro: Pi_closed[OF ct'] maximalD1)
            show "integrable (ct' t) (\<lambda>_. \<Delta> t)" "integrable (ct' t) \<Delta>"
              using ct ct' `t \<in> S` D
              by (auto intro!: measure_pmf.integrable_const_bound[where B=1] \<Delta>_le_1
                       simp: AE_measure_pmf_iff dest: Pi_closed)
          qed
          also have "\<dots> = \<Delta> t"
            using measure_pmf.prob_space[of "ct' t"] by simp
          also have "\<Delta> t \<le> (\<integral>s. real (?v s) \<partial>ct' t) - (\<integral>s. real (?v' s) \<partial>ct' t)"
          proof -
            have "?v t \<le> (\<integral>\<^sup>+s. ?v s \<partial>ct' t)"
            proof cases
              assume "t = s" with not_maximal show ?thesis by simp
            next
              assume "t \<noteq> s" with S1 `t\<in>S1` ct ct' show ?thesis
                by (subst v_S1) auto
            qed
            also have "\<dots> = ereal (\<integral>s. real (?v s) \<partial>ct' t)"
              using ct ct' `t\<in>S`
              by (intro measure_pmf.ereal_integral_real[symmetric, where B=1])
                 (auto simp: AE_measure_pmf_iff one_ereal_def[symmetric]
                       intro!: v_nonneg v_le_1 simple_valid_cfg intro: Pi_closed)
            finally have "real (?v t) \<le> (\<integral>s. real (?v s) \<partial>ct' t)"
              using ct `t\<in>S` by (simp add: v_def T.emeasure_eq_measure)
            moreover
            { have "?v' t = (\<integral>\<^sup>+s. ?v' s \<partial>ct' t)"
                using ct ct' `t \<in> S1` S1 by (subst v_S1) auto
              also have "\<dots> = ereal (\<integral>s. real (?v' s) \<partial>ct' t)"
                using ct' `t\<in>S`
                by (intro measure_pmf.ereal_integral_real[symmetric, where B=1])
                   (auto simp: AE_measure_pmf_iff one_ereal_def[symmetric]
                         intro!: v_nonneg v_le_1 simple_valid_cfg intro: Pi_closed)
              finally have "real (?v' t) = (\<integral>s. real (?v' s) \<partial>ct' t)"
                using ct' `t\<in>S` by (simp add: v_def T.emeasure_eq_measure) }
            ultimately show ?thesis
              using `t \<in> S` by (simp add: \<Delta>_def ereal_minus_mono)
          qed
          also have "\<dots> = (\<integral>s. \<Delta> s \<partial>ct' t)"
            unfolding \<Delta>_def using Pi_closed[OF ct `t\<in>S`] Pi_closed[OF ct' `t\<in>S`] ct ct'
            by (intro integral_diff[symmetric] measure_pmf.integrable_const_bound[where B=1])
               (auto simp: AE_measure_pmf_iff real_v v_nonneg intro!: real_of_ereal_le_1)
          finally show False
            by simp
        qed
        with t[THEN  maximalD2] `t \<in> S` `t' \<in> S` have "\<Delta> t = \<Delta> t'"
          by (auto intro: antisym)
        with t `t' \<in> S` have "t' \<in> maximal \<Delta> S"
          by (auto simp: maximal_def)
        then show ?case
          by fact
      qed 
    qed
    moreover have "?v s < ?v' s"
    proof -
      have "?v s < (\<integral>\<^sup>+t. ?v t \<partial>D)"
        by fact
      also have "\<dots> \<le> (\<integral>\<^sup>+t. ?v' t \<partial>D)"
        using `?v \<le> ?v'` `s\<in>S` D ct ct'
        by (intro nn_integral_mono) (auto simp: le_fun_def)
      also have "\<dots> = ?v' s"
        using `s\<in>S1` S1 ct' by (subst (2) v_S1) auto
      finally show ?thesis .
    qed
    ultimately have "?v < ?v'"
      by (auto simp: less_le le_fun_def fun_eq_iff)
    note this proper ct' }
  note v_strict = this(1) and proper = this(2) and sc'_R = this(3)

  have "finite (Pi\<^sub>E S K \<times> Pi\<^sub>E S K)"
    by (intro finite_PiE S_finite K_finite finite_SigmaI)
  then have "finite R"
    by (rule rev_finite_subset) (auto simp add: PiE_iff S\<^sub>r_def R_def intro: extensional_arb)
  moreover
  from v_strict have "acyclic R"
    by (rule acyclicI_order)
  ultimately have "wf R"
    by (rule finite_acyclic_wf)
  
  from exists_proper obtain ct' where ct': "proper ct'" .
  def ct \<equiv> "restrict ct' S"
  with ct' have sc_Pi: "ct \<in> Pi S K" and "ct' \<in> Pi S K"
    by (auto simp: proper_def)
  then have ct: "ct \<in> {ct \<in> Pi\<^sub>E S K. proper ct}"
    using ct' directed_towards_mono[where F="SIGMA s:S\<^sub>r. ct' s" and G="SIGMA s:S\<^sub>r. ct s"]
    apply simp
    apply (subst proper_eq)
    by (auto simp: ct_def proper_eq[OF properD1[OF ct']] subset_eq S\<^sub>r_def)

  show "\<exists>ct. ct \<in> Pi\<^sub>E S K \<and> v\<circ>simple ct = F_sup (v\<circ>simple ct)"
  proof (rule wfE_min[OF `wf R` ct])
    fix ct assume ct: "ct \<in> {ct \<in> Pi\<^sub>E S K. proper ct}"
    then have "ct \<in> Pi S K" "proper ct"
      by (auto simp: proper_def)
    assume min: "\<And>ct'. (ct', ct) \<in> R \<Longrightarrow> ct' \<notin> {ct \<in> Pi\<^sub>E S K. proper ct}"
    let ?v = "\<lambda>s. v (simple ct s)"
    { fix s assume "s \<in> S" "s \<in> S1" "s \<notin> S2"
      with ct have "ct s \<in> K s" "?v s \<le> integral\<^sup>N (ct s) ?v" 
        by (auto simp: v_S1 PiE_def intro!: nn_integral_mono)
      moreover
      { have "0 \<le> ?v s"
          using `s\<in>S` ct by (simp add: v_nonneg PiE_def)
        also assume v_less: "?v s < (SUP D:K s. integral\<^sup>N D ?v)"
        also have "\<dots> \<le> p s"
          unfolding p_S1[OF `s\<in>S1`] using `s\<in>S` ct v_le_p[OF simple_valid_cfg, OF `ct \<in> Pi S K`]
          by (auto intro!: SUP_mono nn_integral_mono_AE bexI
                   simp: PiE_def AE_measure_pmf_iff set_pmf_closed)
        finally have "s \<in> S\<^sub>r"
          using `s\<in>S` `s\<notin>S2` by (simp add: S\<^sub>r_def S\<^sub>e_def)

        from v_less obtain D where "D \<in> K s" "?v s < integral\<^sup>N D ?v"
          by (auto simp: less_SUP_iff)
        with ct `s\<in>S` `s\<in>S\<^sub>r` have "(ct(s:=D), ct) \<in> R" "ct(s:=D) \<in> PiE S K"
          unfolding R_def by (auto simp: PiE_def extensional_def)
        from proper[OF this(1)] min[OF this(1)] ct `D \<in> K s` `s\<in>S` this(2)
        have False
          by simp }
      ultimately have "?v s = (SUP D:K s. integral\<^sup>N D ?v)"
        by (auto intro: antisym SUP_upper2[where i="ct s"] leI)
      also have "\<dots> = (SUP D:K s. integral\<^sup>N D (\<lambda>s\<in>S. ?v s))"
        using `s\<in>S` by (auto intro!: SUP_cong nn_integral_cong v_nS simp: ct simple_valid_cfg_iff `ct \<in> Pi S K`)
      finally have "?v s = (SUP D:K s. integral\<^sup>N D (\<lambda>s\<in>S. ?v s))" . }
    then have "?v = F_sup ?v"
      unfolding F_sup_def using ct
      by (auto intro!: ext v_S2 simple_cfg_on v_nS v_nS12 SUP_cong nn_integral_cong
               simp: PiE_def simple_valid_cfg_iff)
    with ct show ?thesis
      by (auto simp: comp_def)
  qed
qed

lemma p_v_memoryless:
  obtains ct where "ct \<in> Pi\<^sub>E S K" "p = v\<circ>simple ct"
proof -
  obtain ct where ct_PiE: "ct \<in> Pi\<^sub>E S K" and eq: "v\<circ>simple ct = F_sup (v\<circ>simple ct)"
    by (rule F_v_memoryless)
  then have ct: "ct \<in> Pi S K"
    by (simp add: PiE_def)
  have "p = v\<circ>simple ct"
  proof (rule antisym)
    show "p \<le> v\<circ>simple ct"
      unfolding p_eq_lfp_F_sup by (rule lfp_lowerbound) (metis order_refl eq)
    show "v\<circ>simple ct \<le> p"
    proof (rule le_funI)
      fix s show "(v\<circ>simple ct) s \<le> p s"
        using v_le_p[of "simple ct s"]
        by (cases "s \<in> S") (auto simp del: simp add: v_def ct)
    qed
  qed
  with ct_PiE that show thesis by auto
qed

definition "n = (\<lambda>s\<in>S. P_inf s (\<lambda>\<omega>. (HLD S1 suntil HLD S2) (s ## \<omega>)))"

lemma n_eq_INF_v: "s \<in> S \<Longrightarrow> n s = (\<Sqinter>cfg\<in>cfg_on s. v cfg)"
  by (auto simp add: n_def v_def P_inf_def T.emeasure_eq_measure valid_cfgI intro!: INF_cong)

lemma n_le_v: "s \<in> S \<Longrightarrow> cfg \<in> cfg_on s \<Longrightarrow> n s \<le> v cfg"
  by (subst n_eq_INF_v) (blast intro!: INF_lower)+

lemma n_eq_1_imp: "s \<in> S \<Longrightarrow> cfg \<in> cfg_on s \<Longrightarrow> n s = 1 \<Longrightarrow> v cfg = 1"
  using n_le_v[of s cfg] v_le_1[of cfg] by (auto intro: antisym valid_cfgI)

lemma n_eq_1_iff: "s \<in> S \<Longrightarrow> n s = 1 \<longleftrightarrow> (\<forall>cfg\<in>cfg_on s. v cfg = 1)"
  apply rule
  apply (metis n_eq_1_imp)
  apply (auto simp: n_eq_INF_v intro!: INF_eqI)
  done

lemma n_le_1: "s \<in> S \<Longrightarrow> n s \<le> 1"
  by (auto simp: n_eq_INF_v intro!: INF_lower2[OF simple_cfg_on[of arb_act]] v_le_1)

lemma n_nonneg: "s \<in> S \<Longrightarrow> 0 \<le> n s"
  by (auto simp: n_eq_INF_v intro!: v_nonneg INF_greatest valid_cfgI)

lemma n_undefined[simp]: "s \<notin> S \<Longrightarrow> n s = undefined"
  by (simp add: n_def)

lemma n_not_inf[simp]: "s \<in> S \<Longrightarrow> n s \<noteq> \<infinity>" "s \<in> S \<Longrightarrow> n s \<noteq> -\<infinity>"
  using n_nonneg[of s] n_le_1[of s] by auto

lemma n_S1: "s \<in> S1 \<Longrightarrow> n s = (\<Sqinter>D\<in>K s. \<integral>\<^sup>+ t. n t \<partial>D)"
  using S1 S1_S2 unfolding n_def
  apply auto
  apply (subst P_inf_iterate)
  apply (auto intro!: nn_integral_cong_AE INF_cong intro: set_pmf_closed
              simp: AE_measure_pmf_iff suntil_Stream set_eq_iff)
  done

lemma n_S2[simp]: "s \<in> S2 \<Longrightarrow> n s = 1"
  using S2 by (auto simp add: n_eq_INF_v valid_cfgI)

lemma n_nS12: "s \<in> S \<Longrightarrow> s \<notin> S1 \<Longrightarrow> s \<notin> S2 \<Longrightarrow> n s = 0"
  by (auto simp add: n_eq_INF_v valid_cfgI)

definition F_inf :: "('s \<Rightarrow> ereal) \<Rightarrow> ('s \<Rightarrow> ereal)" where
  "F_inf f = (\<lambda>s\<in>S. if s \<in> S2 then 1 else if s \<in> S1 then (\<Sqinter>D\<in>K s. \<integral>\<^sup>+ t. f t \<partial>D) else 0)"

lemma F_inf_n: "F_inf n = n"
  by (simp add: F_inf_def n_nS12 n_S1 fun_eq_iff)

lemma F_inf_nS[simp]: "s \<notin> S \<Longrightarrow> F_inf f s = undefined"
  by (simp add: F_inf_def)

lemma mono_F_inf: "mono F_inf"
  by (auto intro!: INF_superset_mono nn_integral_mono simp: mono_def F_inf_def le_fun_def)

lemma F_inf_nonneg: "s \<in> S \<Longrightarrow> 0 \<le> F_inf F s"
  by (auto simp: F_inf_def intro!: INF_greatest nn_integral_nonneg intro: arb_actI)

lemma S1_nS2: "s \<in> S1 \<Longrightarrow> s \<notin> S2"
  using S1_S2 by auto

lemma n_eq_lfp_G: "n = lfp F_inf"
proof (intro antisym lfp_lowerbound le_funI)
  fix s let ?I = "\<lambda>D. (\<integral>\<^sup>+t. lfp F_inf t \<partial>measure_pmf D)"
  def ct \<equiv> "\<lambda>s. SOME D. D \<in> K s \<and> (s \<in> S1 \<longrightarrow> lfp F_inf s = ?I D)"
  { fix s assume s: "s \<in> S"
    then have "finite (?I ` K s)"
      by (auto intro: K_finite)
    with s obtain D where "D \<in> K s" "(\<integral>\<^sup>+t. lfp F_inf t \<partial>D) = Min (?I ` K s)"
      by (auto simp: K_wf dest!: Min_in)
    note this(2)
    also have "\<dots> = (INF D : K s. ?I D)"
      using s K_wf by (subst Min_Inf) (auto intro: K_finite)
    also have "s \<in> S1 \<Longrightarrow> \<dots> = lfp F_inf s"
      using s S1_S2 by (subst (3) lfp_unfold[OF mono_F_inf]) (auto simp add: F_inf_def)
    finally have "\<exists>D. D \<in> K s \<and> (s \<in> S1 \<longrightarrow> lfp F_inf s = ?I D)"
      using `D \<in> K s` by auto
    then have "ct s \<in> K s \<and> (s \<in> S1 \<longrightarrow> lfp F_inf s = ?I (ct s))"
      unfolding ct_def by (rule someI_ex)
    then have "ct s \<in> K s" "s \<in> S1 \<Longrightarrow> lfp F_inf s = ?I (ct s)"
      by auto }
  note ct = this
  then have Pi_ct: "ct \<in> Pi S K"
    by auto
  then have valid_ct[simp]: "\<And>s. s \<in> S \<Longrightarrow> simple ct s \<in> valid_cfg"
    by simp
  let ?F = "\<lambda>P. HLD S2 or (HLD S1 aand nxt P)"
  def P \<equiv> "\<lambda>s n. emeasure (T (simple ct s)) {x\<in>space (T (simple ct s)). (?F ^^ n) (\<lambda>x. False) (s ## x)}"
  { assume "s \<in> S"
    with S1 have [simp, measurable]: "s \<in> S" by auto
    then have "n s \<le> v (simple ct s)"
      by (intro n_le_v) (auto intro: simple_cfg_on[OF Pi_ct])
    also have "\<dots> = emeasure (T (simple ct s)) {x\<in>space (T (simple ct s)). lfp ?F (s ## x)}"
      using S1_S2
      by (simp add: v_eq[OF simple_valid_cfg[OF Pi_ct `s\<in>S`]])
         (simp add: suntil_lfp space_T[symmetric, of "simple ct s"] del: space_T)
    also have "\<dots> = (\<Squnion>n. P s n)" unfolding P_def
      apply (rule emeasure_lfp2[where P="\<lambda>M. \<exists>s. M = T (simple ct s)" and M="T (simple ct s)"])
      apply (intro exI[of _ s] refl)
      apply (auto simp: continuous_def) []
      apply auto []
    proof safe
      fix A s assume "\<And>N. \<exists>s. N = T (simple ct s) \<Longrightarrow> Measurable.pred N A"
      then have "\<And>s. Measurable.pred (T (simple ct s)) A"
        by metis
      then have "\<And>s. Measurable.pred St A"
        by simp
      then show "Measurable.pred (T (simple ct s)) (\<lambda>xs. HLD S2 xs \<or> HLD S1 xs \<and> nxt A xs)"
        by simp
    qed
    also have "\<dots> \<le> lfp F_inf s"
    proof (intro SUP_least)
      fix n from `s\<in>S` show "P s n \<le> lfp F_inf s"
      proof (induct n arbitrary: s)
        case 0 with S1 show ?case
          by (subst lfp_unfold[OF mono_F_inf]) (auto simp: P_def intro: F_inf_nonneg)
      next
        case (Suc n)
        
        show ?case
        proof cases
          assume "s \<in> S1" with S1_S2 S1 have s[simp]: "s \<notin> S2" "s \<in> S" "s \<in> S1" by auto
          have "P s (Suc n) = (\<integral>\<^sup>+t. P t n \<partial>ct s)"
            unfolding P_def space_T
            apply (subst emeasure_Collect_T)
            apply (rule measurable_compose[OF measurable_Stream[OF measurable_const measurable_ident_sets[OF refl]]])
            apply (measurable, assumption)
            apply (auto simp: K_cfg_def map_pmf.rep_eq nn_integral_distr
                        intro!: nn_integral_cong)
            done
          also have "\<dots> \<le> (\<integral>\<^sup>+t. lfp F_inf t \<partial>ct s)"
            using Pi_closed[OF Pi_ct `s \<in> S`]
            by (auto intro!: nn_integral_mono_AE Suc simp: AE_measure_pmf_iff)
          also have "\<dots> = lfp F_inf s"
            by (intro ct(2)[symmetric]) auto
          finally show ?thesis .
        next
          assume "s \<notin> S1" with S2 `s \<in> S` show ?case
            using T.emeasure_space_1[of "simple ct s"]
            by (subst lfp_unfold[OF mono_F_inf]) (auto simp: F_inf_def P_def)
        qed
      qed
    qed
    finally have "n s \<le> lfp F_inf s" . }
  moreover have "s \<notin> S \<Longrightarrow> n s \<le> lfp F_inf s"
    by (subst lfp_unfold[OF mono_F_inf]) (simp add: n_def F_inf_def)
  ultimately show "n s \<le> lfp F_inf s"
    by blast
qed (simp add: F_inf_n)

end

end

