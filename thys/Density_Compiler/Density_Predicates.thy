(*
  Theory: Density_Predicates.thy
  Authors: Manuel Eberl
*)

header {* Density Predicates *}

theory Density_Predicates
imports Probability PDF_Misc Giry_Monad
begin

subsection {* Probability Densities *}

definition is_subprob_density :: "'a measure \<Rightarrow> ('a \<Rightarrow> ereal) \<Rightarrow> bool" where
  "is_subprob_density M f \<equiv> (f \<in> borel_measurable M) \<and> space M \<noteq> {} \<and>
                           (\<forall>x\<in>space M. f x \<ge> 0) \<and> (\<integral>\<^sup>+x. f x \<partial>M) \<le> 1"

lemma is_subprob_densityI[intro]:
    "\<lbrakk>f \<in> borel_measurable M; \<And>x. x \<in> space M \<Longrightarrow> f x \<ge> 0; space M \<noteq> {}; (\<integral>\<^sup>+x. f x \<partial>M) \<le> 1\<rbrakk>
        \<Longrightarrow> is_subprob_density M f"
  unfolding is_subprob_density_def by simp

lemma is_subprob_densityD[dest]:
  "is_subprob_density M f \<Longrightarrow> f \<in> borel_measurable M"
  "is_subprob_density M f \<Longrightarrow> x \<in> space M \<Longrightarrow> f x \<ge> 0" 
  "is_subprob_density M f \<Longrightarrow> space M \<noteq> {}"
  "is_subprob_density M f \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>M) \<le> 1"
  unfolding is_subprob_density_def by simp_all

subsection {* Measure spaces with densities *}

definition has_density :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> ('a \<Rightarrow> ereal) \<Rightarrow> bool" where
  "has_density M N f \<longleftrightarrow> (f \<in> borel_measurable N) \<and> (\<forall>x\<in>space N. f x \<ge> 0) \<and> 
                         space N \<noteq> {} \<and> M = density N f"

lemma has_densityI[intro]:
  "\<lbrakk>f \<in> borel_measurable N; \<And>x. x \<in> space N \<Longrightarrow> f x \<ge> 0; M = density N f; space N \<noteq> {}\<rbrakk> 
      \<Longrightarrow> has_density M N f"
  unfolding has_density_def by blast

lemma has_densityD:
  assumes "has_density M N f"
  shows "f \<in> borel_measurable N" "\<And>x. x \<in> space N \<Longrightarrow> f x \<ge> 0" "M = density N f" "space N \<noteq> {}"
using assms unfolding has_density_def by simp_all


lemma has_density_sets: "has_density M N f \<Longrightarrow> sets M = sets N"
  unfolding has_density_def by simp

lemma has_density_space: "has_density M N f \<Longrightarrow> space M = space N"
  unfolding has_density_def by simp

lemma has_density_emeasure:
    "has_density M N f \<Longrightarrow> X \<in> sets M \<Longrightarrow> emeasure M X = \<integral>\<^sup>+x. f x * indicator X x \<partial>N"
  unfolding has_density_def by (simp_all add: emeasure_density)

lemma has_density_emeasure_space:
    "has_density M N f \<Longrightarrow> emeasure M (space M) = \<integral>\<^sup>+x. f x \<partial>N"
  by (simp add: has_density_emeasure) (simp add: has_density_space nn_integral_over_space)

lemma has_density_emeasure_space':
    "has_density M N f \<Longrightarrow> emeasure (density N f) (space (density N f)) = \<integral>\<^sup>+x. f x \<partial>N"
  by (frule has_densityD(3)[symmetric]) (simp add: has_density_emeasure_space)

lemma has_density_imp_is_subprob_density:
    "\<lbrakk>has_density M N f; (\<integral>\<^sup>+x. f x \<partial>N) = 1\<rbrakk> \<Longrightarrow> is_subprob_density N f"
  by (auto dest: has_densityD)

lemma has_density_imp_is_subprob_density':
    "\<lbrakk>has_density M N f; prob_space M\<rbrakk> \<Longrightarrow> is_subprob_density N f"
  by (auto intro!: has_density_imp_is_subprob_density dest: prob_space.emeasure_space_1
           simp: has_density_emeasure_space)

lemma has_density_equal_on_space:
  assumes "has_density M N f" "\<And>x. x \<in> space N \<Longrightarrow> f x = g x"
  shows "has_density M N g"
proof
  from assms(1) and assms(2)[symmetric] show "\<And>x. x \<in> space N \<Longrightarrow> g x \<ge> 0" 
    by (auto dest: has_densityD)
  from assms show "g \<in> borel_measurable N"
    by (subst measurable_cong[of _ _ f]) (auto dest: has_densityD)  
  with assms show "M = density N g"
    by (subst density_cong[of _ _ f]) (auto dest: has_densityD)
  from assms(1) show "space N \<noteq> {}" by (rule has_densityD)
qed

lemma has_density_cong:
  assumes "\<And>x. x \<in> space N \<Longrightarrow> f x = g x"
  shows "has_density M N f = has_density M N g"
using assms by (intro iffI) (erule has_density_equal_on_space, simp)+

lemma has_density_dens_AE:
    "\<lbrakk>AE y in N. f y = f' y; f' \<in> borel_measurable N; 
      \<And>x. x \<in> space M \<Longrightarrow> f' x \<ge> 0; has_density M N f\<rbrakk>
        \<Longrightarrow> has_density M N f'"
  unfolding has_density_def by (simp cong: density_cong)


subsection {* Probability spaces with densities *}

lemma is_subprob_density_imp_has_density:
    "\<lbrakk>is_subprob_density N f; M = density N f\<rbrakk> \<Longrightarrow> has_density M N f"
  by (rule has_densityI) auto

lemma has_subprob_density_imp_subprob_space':
    "\<lbrakk>has_density M N f; is_subprob_density N f\<rbrakk> \<Longrightarrow> subprob_space M"
proof (rule subprob_spaceI)
  assume "has_density M N f"
  hence "M = density N f" by (simp add: has_density_def)
  also from `has_density M N f` have "space ... \<noteq> {}" by (simp add: has_density_def)
  finally show "space M \<noteq> {}" .
qed (auto simp add: has_density_emeasure_space dest: has_densityD)

lemma has_subprob_density_imp_subprob_space[dest]:
    "is_subprob_density M f \<Longrightarrow> subprob_space (density M f)"
  by (rule has_subprob_density_imp_subprob_space') auto

definition "has_subprob_density M N f \<equiv> has_density M N f \<and> subprob_space M"

(* TODO: Move *)
lemma subprob_space_density_not_empty: "subprob_space (density M f) \<Longrightarrow> space M \<noteq> {}"
  by (subst space_density[symmetric], subst subprob_space.not_empty, assumption) simp

lemma has_subprob_densityI:
  "\<lbrakk>f \<in> borel_measurable N; \<And>x. x \<in> space N \<Longrightarrow> f x \<ge> 0; M = density N f; subprob_space M\<rbrakk> \<Longrightarrow> 
      has_subprob_density M N f"
  unfolding has_subprob_density_def by (auto simp: subprob_space_density_not_empty)

lemma has_subprob_densityI':
  assumes "f \<in> borel_measurable N" "\<And>x. x \<in> space N \<Longrightarrow> f x \<ge> 0" "space N \<noteq> {}"
          "M = density N f" "(\<integral>\<^sup>+x. f x \<partial>N) \<le> 1" 
  shows "has_subprob_density M N f"
proof-
  from assms have D: "has_density M N f" by blast
  moreover from D and assms have "subprob_space M"
    by (auto intro!: subprob_spaceI simp: has_density_emeasure_space emeasure_density_space)
  ultimately show ?thesis unfolding has_subprob_density_def by simp
qed

lemma has_subprob_densityD:
  assumes "has_subprob_density M N f"
  shows "f \<in> borel_measurable N" "\<And>x. x \<in> space N \<Longrightarrow> f x \<ge> 0" "M = density N f" "subprob_space M"
using assms unfolding has_subprob_density_def by (auto dest: has_densityD)

lemma has_subprob_density_imp_has_density:
  "has_subprob_density M N f \<Longrightarrow> has_density M N f" by (simp add: has_subprob_density_def)

lemma has_subprob_density_equal_on_space:
  assumes "has_subprob_density M N f" "\<And>x. x \<in> space N \<Longrightarrow> f x = g x"
  shows "has_subprob_density M N g"
using assms unfolding has_subprob_density_def by (auto dest: has_density_equal_on_space)

lemma has_subprob_density_cong:
  assumes "\<And>x. x \<in> space N \<Longrightarrow> f x = g x"
  shows "has_subprob_density M N f = has_subprob_density M N g"
using assms by (intro iffI) (erule has_subprob_density_equal_on_space, simp)+

lemma has_subprob_density_dens_AE:
    "\<lbrakk>AE y in N. f y = f' y; f' \<in> borel_measurable N; 
      \<And>x. x \<in> space M \<Longrightarrow> f' x \<ge> 0; has_subprob_density M N f\<rbrakk>
      \<Longrightarrow> has_subprob_density M N f'"
  unfolding has_subprob_density_def by (simp add: has_density_dens_AE)


subsection {* Parametrized probability densities *}

definition 
  "has_parametrized_subprob_density M N R f \<equiv> 
       (\<forall>x \<in> space M. has_subprob_density (N x) R (f x)) \<and> split f \<in> borel_measurable (M \<Otimes>\<^sub>M R)"

lemma has_parametrized_subprob_densityI:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> N x = density R (f x)"
  assumes "\<And>x y. x \<in> space M \<Longrightarrow> y \<in> space R \<Longrightarrow> f x y \<ge> 0"
  assumes "\<And>x. x \<in> space M \<Longrightarrow> subprob_space (N x)"
  assumes "split f \<in> borel_measurable (M \<Otimes>\<^sub>M R)"
  shows "has_parametrized_subprob_density M N R f"
  unfolding has_parametrized_subprob_density_def using assms
  by (intro ballI conjI has_subprob_densityI) simp_all

lemma has_parametrized_subprob_densityD:
  assumes "has_parametrized_subprob_density M N R f"
  shows "\<And>x. x \<in> space M \<Longrightarrow> N x = density R (f x)"
    and "\<And>x y. x \<in> space M \<Longrightarrow> y \<in> space R \<Longrightarrow> f x y \<ge> 0"
    and "\<And>x. x \<in> space M \<Longrightarrow> subprob_space (N x)"
    and "split f \<in> borel_measurable (M \<Otimes>\<^sub>M R)"
  using assms unfolding has_parametrized_subprob_density_def
  by (auto dest: has_subprob_densityD)

lemma has_parametrized_subprob_density_integral:
  assumes "has_parametrized_subprob_density M N R f" "x \<in> space M"
  shows "(\<integral>\<^sup>+y. f x y \<partial>R) \<le> 1"
proof-
  have "(\<integral>\<^sup>+y. f x y \<partial>R) = emeasure (density R (f x)) (space (density R (f x)))" using assms
    by (auto simp: emeasure_density_space dest: has_parametrized_subprob_densityD)
  also have "density R (f x) = (N x)" using assms by (auto dest: has_parametrized_subprob_densityD)
  also have "emeasure ... (space ...) \<le> 1" using assms
    by (subst subprob_space.emeasure_space_le_1) (auto dest: has_parametrized_subprob_densityD)
  finally show ?thesis .
qed

lemma has_parametrized_subprob_density_cong:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> N x = N' x"
  shows "has_parametrized_subprob_density M N R f = has_parametrized_subprob_density M N' R f"
using assms unfolding has_parametrized_subprob_density_def by auto

lemma has_parametrized_subprob_density_dens_AE:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> AE y in R. f x y = f' x y"
          "split f' \<in> borel_measurable (M \<Otimes>\<^sub>M R)"
          "\<And>x y. x \<in> space M \<Longrightarrow> y \<in> space R \<Longrightarrow> f' x y \<ge> 0"
          "has_parametrized_subprob_density M N R f"
  shows   "has_parametrized_subprob_density M N R f'"
unfolding has_parametrized_subprob_density_def
proof (intro conjI ballI)
  fix x assume x: "x \<in> space M"
  with assms(4) have "space (N x) = space R"
    by (auto dest!: has_parametrized_subprob_densityD(1))
  with assms and x show "has_subprob_density (N x) R (f' x)"
    by (rule_tac has_subprob_density_dens_AE[of "f x"])
       (auto simp: has_parametrized_subprob_density_def)
qed fact


subsection {* Density in the Giry monad *}

lemma emeasure_bind_density:
  assumes "space M \<noteq> {}" "\<And>x. x \<in> space M \<Longrightarrow> has_density (f x) N (g x)" 
          "f \<in> measurable M (kernel_space N)" "X \<in> sets N"
  shows "emeasure (M \<guillemotright>= f) X = \<integral>\<^sup>+x. \<integral>\<^sup>+y. g x y * indicator X y \<partial>N \<partial>M"
proof-
  from assms have "emeasure (M \<guillemotright>= f) X = \<integral>\<^sup>+x. emeasure (f x) X \<partial>M"
    by (intro emeasure_bind)
  also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+y. g x y * indicator X y \<partial>N \<partial>M" using assms
    by (intro nn_integral_cong) (simp add: has_density_emeasure sets_kernel)
  finally show ?thesis .
qed

lemma bind_density:
  assumes "sigma_finite_measure M" "sigma_finite_measure N"
          "space M \<noteq> {}" "\<And>x. x \<in> space M \<Longrightarrow> has_density (f x) N (g x)" 
          "split g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
          "f \<in> measurable M (kernel_space N)"
  shows "(M \<guillemotright>= f) = density N (\<lambda>y. \<integral>\<^sup>+x. g x y \<partial>M)"
proof (rule measure_eqI)
  interpret sfN: sigma_finite_measure N by fact
  interpret sfNM: pair_sigma_finite N M unfolding pair_sigma_finite_def using assms by simp
  fix X assume "X \<in> sets (M \<guillemotright>= f)"
  with assms have "X \<in> sets N" by auto
  with assms have "emeasure (M \<guillemotright>= f) X = \<integral>\<^sup>+x. \<integral>\<^sup>+y. g x y * indicator X y \<partial>N \<partial>M"
    by (intro emeasure_bind_density) simp_all
  also from `X \<in> sets N` have "... = \<integral>\<^sup>+y. \<integral>\<^sup>+x. g x y * indicator X y \<partial>M \<partial>N"
    by (intro sfNM.Fubini', subst measurable_split_conv, intro borel_measurable_ereal_times,
        subst measurable_split_conv[symmetric], subst measurable_pair_swap_iff, simp add: assms,
        intro measurable_compose[OF measurable_fst borel_measurable_indicator])
  also {
    fix y assume "y \<in> space N"
    have "(\<lambda>x. g x y) = split g \<circ> (\<lambda>x. (x, y))" by (rule ext) simp
    also from `y \<in> space N` have "... \<in> borel_measurable M" 
      by (intro measurable_comp[OF _ assms(5)] measurable_Pair2')
    finally have "(\<lambda>x. g x y) \<in> borel_measurable M" .
  }
  hence "... = \<integral>\<^sup>+y. (\<integral>\<^sup>+x. g x y \<partial>M) * indicator X y \<partial>N"
    by (intro nn_integral_cong nn_integral_multc)  simp_all
  also from `X \<in> sets N` and assms have "... = emeasure (density N (\<lambda>y. \<integral>\<^sup>+x. g x y \<partial>M)) X"
    by (subst emeasure_density) (simp_all add: sfN.borel_measurable_nn_integral)
  finally show "emeasure (M \<guillemotright>= f) X = emeasure (density N (\<lambda>y. \<integral>\<^sup>+x. g x y \<partial>M)) X" .
qed (simp add: assms)


lemma bind_has_density:
  assumes "sigma_finite_measure M" "sigma_finite_measure N"
          "space M \<noteq> {}" "\<And>x. x \<in> space M \<Longrightarrow> has_density (f x) N (g x)" 
          "split g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
          "f \<in> measurable M (kernel_space N)"
  shows "has_density (M \<guillemotright>= f) N (\<lambda>y. \<integral>\<^sup>+x. g x y \<partial>M)"
proof
  interpret sigma_finite_measure M by fact
  show "(\<lambda>y. \<integral>\<^sup>+ x. g x y \<partial>M) \<in> borel_measurable N" using assms
    by (intro borel_measurable_nn_integral, subst measurable_pair_swap_iff) simp
  show "M \<guillemotright>= f = density N (\<lambda>y. \<integral>\<^sup>+ x. g x y \<partial>M)"
    by (intro bind_density) (simp_all add: assms)
  from `space M \<noteq> {}` obtain x where "x \<in> space M" by blast
  with assms have "has_density (f x) N (g x)" by simp
  thus "space N \<noteq> {}" by (rule has_densityD)
qed (simp add: nn_integral_nonneg)

lemma bind_has_density':
  assumes sfM: "sigma_finite_measure M"
      and sfR: "sigma_finite_measure R"
      and not_empty: "space M \<noteq> {}" and dens_M: "has_density M N \<delta>M" 
      and dens_f: "\<And>x. x \<in> space M \<Longrightarrow> has_density (f x) R (\<delta>f x)" 
      and M\<delta>f: "split \<delta>f \<in> borel_measurable (N \<Otimes>\<^sub>M R)"
      and Mf: "f \<in> measurable N (kernel_space R)"
  shows "has_density (M \<guillemotright>= f) R (\<lambda>y. \<integral>\<^sup>+x. \<delta>M x * \<delta>f x y \<partial>N)"
proof-
  from dens_M have M_M: "measurable M = measurable N"
    by (intro ext measurable_cong_sets) (auto dest: has_densityD)
  from dens_M have M_MR: "measurable (M \<Otimes>\<^sub>M R) = measurable (N \<Otimes>\<^sub>M R)"
    by (intro ext measurable_cong_sets sets_pair_measure_cong) (auto dest: has_densityD)
  have "has_density (M \<guillemotright>= f) R (\<lambda>y. \<integral>\<^sup>+x. \<delta>f x y \<partial>M)"
    by (rule bind_has_density) (auto simp: assms M_MR M_M)
  moreover {
    fix y assume A: "y \<in> space R"
    have "(\<lambda>x. \<delta>f x y) = split \<delta>f \<circ> (\<lambda>x. (x,y))" by (rule ext) (simp add: o_def)
    also have "... \<in> borel_measurable N" by (intro measurable_comp[OF _ M\<delta>f] measurable_Pair2' A)
    finally have M_\<delta>f': "(\<lambda>x. \<delta>f x y) \<in> borel_measurable N" .

    from dens_M have "M = density N \<delta>M" by (auto dest: has_densityD)
    also from dens_M have "(\<integral>\<^sup>+x. \<delta>f x y \<partial>...) = \<integral>\<^sup>+x. \<delta>M x * \<delta>f x y \<partial>N"
      by (subst nn_integral_density) (auto dest: has_densityD simp: M_\<delta>f')
    finally have "(\<integral>\<^sup>+x. \<delta>f x y \<partial>M) = \<integral>\<^sup>+x. \<delta>M x * \<delta>f x y \<partial>N" .
  }
  ultimately show "has_density (M \<guillemotright>= f) R (\<lambda>y. \<integral>\<^sup>+x. \<delta>M x * \<delta>f x y \<partial>N)"
    by (rule has_density_equal_on_space) (simp_all add: nn_integral_nonneg)
qed

lemma bind_has_subprob_density:
  assumes "subprob_space M" "sigma_finite_measure N"
          "space M \<noteq> {}" "\<And>x. x \<in> space M \<Longrightarrow> has_density (f x) N (g x)" 
          "split g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
          "f \<in> measurable M (kernel_space N)"
  shows "has_subprob_density (M \<guillemotright>= f) N (\<lambda>y. \<integral>\<^sup>+x. g x y \<partial>M)"
proof (unfold has_subprob_density_def, intro conjI)
  from assms show "has_density (M \<guillemotright>= f) N (\<lambda>y. \<integral>\<^sup>+x. g x y \<partial>M)"
    by (intro bind_has_density) (auto simp: subprob_space_imp_sigma_finite)
  from assms show "subprob_space (M \<guillemotright>= f)" by (intro subprob_space_bind)
qed

lemma bind_has_subprob_density':
  assumes "has_subprob_density M N \<delta>M" "space R \<noteq> {}" "sigma_finite_measure R"
          "\<And>x. x \<in> space M \<Longrightarrow> has_subprob_density (f x) R (\<delta>f x)" 
          "split \<delta>f \<in> borel_measurable (N \<Otimes>\<^sub>M R)" "f \<in> measurable N (kernel_space R)"
  shows "has_subprob_density (M \<guillemotright>= f) R (\<lambda>y. \<integral>\<^sup>+x. \<delta>M x * \<delta>f x y \<partial>N)"
proof (unfold has_subprob_density_def, intro conjI)
  from assms(1) have "space M \<noteq> {}" by (intro subprob_space.not_empty has_subprob_densityD)
  with assms show "has_density (M \<guillemotright>= f) R (\<lambda>y. \<integral>\<^sup>+x. \<delta>M x * \<delta>f x y \<partial>N)"
    by (intro bind_has_density' has_densityI) 
       (auto simp: subprob_space_imp_sigma_finite dest: has_subprob_densityD)
  from assms show "subprob_space (M \<guillemotright>= f)" 
    by (intro subprob_space_bind) (auto dest: has_subprob_densityD)
qed

lemma null_measure_has_subprob_density:
  "space M \<noteq> {} \<Longrightarrow> has_subprob_density (null_measure M) M (\<lambda>_. 0)"
  by (intro has_subprob_densityI) 
     (auto intro: null_measure_eq_density simp: subprob_space_null_measure_iff)

lemma emeasure_has_parametrized_subprob_density:
  assumes "has_parametrized_subprob_density M N R f"
  assumes "x \<in> space M" "X \<in> sets R"
  shows "emeasure (N x) X = \<integral>\<^sup>+y. f x y * indicator X y \<partial>R"
proof-
  from has_parametrized_subprob_densityD(4)[OF assms(1)] and assms(2)
    have Mf: "f x \<in> borel_measurable R" by simp
  have "N x = density R (f x)"
    by (rule has_parametrized_subprob_densityD(1)[OF assms(1,2)])
  also from Mf and assms(3) have "emeasure ... X = \<integral>\<^sup>+y. f x y * indicator X y \<partial>R"
    by (rule emeasure_density)
  finally show ?thesis .
qed

lemma emeasure_count_space_density_singleton:
  assumes "x \<in> A" "has_density M (count_space A) f"
  shows "emeasure M {x} = f x"
proof-
  from has_densityD[OF assms(2)] have nonneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0" by simp    
  from assms have M: "M = density (count_space A) f" by (intro has_densityD)
  from assms have "emeasure M {x} = \<integral>\<^sup>+y. f y * indicator {x} y \<partial>count_space A"
    by (simp add: M emeasure_density)
  also from assms and nonneg have "... = f x"
    apply (subst nn_integral_count_space)
    apply (auto simp: indicator_def) []
    apply (cases "f x > 0")
    apply (auto simp: indicator_def eq_iff)
    done
  finally show ?thesis .
qed

lemma subprob_count_space_density_le_1:
  assumes "has_subprob_density M (count_space A) f" "x \<in> A"
  shows "f x \<le> 1"
proof (cases "f x > 0")
  assume "f x > 0"
  from assms interpret subprob_space M by (intro has_subprob_densityD)
  from assms have M: "M = density (count_space A) f" by (intro has_subprob_densityD)
  from assms have "f x = emeasure M {x}"
    by (intro emeasure_count_space_density_singleton[symmetric]) 
       (auto simp: has_subprob_density_def)
  also have "... \<le> 1" by (rule measure_le_1)
  finally show ?thesis .
qed (auto simp: not_less intro: order.trans[of _ 0 1])

end
