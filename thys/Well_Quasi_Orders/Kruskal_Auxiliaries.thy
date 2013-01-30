(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Auxiliary Lemmas for the Minimal Bad Sequence Proof *}

theory Kruskal_Auxiliaries
imports
  Almost_Full_Relations
begin

lemma bad_of_special_shape':
  assumes refl: "reflp_on P {x. \<exists>i. x \<in> set (g i)}"
    (is "reflp_on P {x. \<exists>i. x \<in> ?G i}")
    and "\<forall>i. f i \<in> {x. \<exists>i. x \<in> set (g i)}"
    and "bad P f"
  shows "\<exists>R (f::nat \<Rightarrow> nat). (\<forall>i. R i \<in> set (g (f i)) \<and> f 0 \<le> f i) \<and> bad P R"
proof -
  from assms have "\<forall>i. \<exists>j. f i \<in> ?G j" by auto
  from choice [OF this] obtain \<phi> where G: "\<And>i. f i \<in> ?G (\<phi> i)" by auto
  have "\<forall>i. \<exists>j>i. \<phi> 0 \<le> \<phi> j"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain i where "\<forall>j>i. \<not> (\<phi> 0 \<le> \<phi> j)" by auto
    then have "\<phi> ` {j. j > i} \<subseteq> {..< \<phi> 0}" (is "\<phi> ` ?I \<subseteq> _") by auto
    then have "finite (\<phi> ` ?I)" by (blast intro: finite_subset)
    moreover have "infinite ?I" by (rule infinite_wo_prefix)
    ultimately obtain k
      where "k > i" and "infinite {j. j > i \<and> \<phi> j = \<phi> k}"
      using pigeonhole_infinite [of ?I \<phi>] by auto
    then have "\<forall>m. \<exists>n>m. n > i \<and> \<phi> n = \<phi> k"
      by (auto simp: infinite_nat_iff_unbounded)
    from choice [OF this] obtain \<psi>
      where *: "\<forall>m. \<psi> m > m \<and> \<psi> m > i \<and> \<phi> (\<psi> m) = \<phi> k" by auto
    let ?\<phi> = "\<phi> \<circ> \<psi>"
    let ?\<psi> = "\<lambda>i. (\<psi> ^^ Suc i) 0"
    from G have "\<forall>i. f (?\<psi> i) \<in> ?G ((\<phi> \<circ> ?\<psi>) i)" by auto
    with * have "\<forall>i. f (?\<psi> i) \<in> ?G (\<phi> k)" by simp
    with pigeonhole_infinite_rel [of "UNIV::nat set" "?G (\<phi> k)" "\<lambda>a b. f (?\<psi> a) = b"]
      obtain x where "x \<in> ?G (\<phi> k)" and "infinite {a. f (?\<psi> a) = x}" by auto
    then have "\<forall>m. \<exists>n>m. f (?\<psi> n) = x" by (auto simp: infinite_nat_iff_unbounded)
    then obtain u v where u: "f (?\<psi> u) = x"
      and "v > u" and v: "f (?\<psi> v) = x" by blast

    from * have "\<forall>i\<ge>0. \<psi> i > i" by auto
    from funpow_mono [OF this] and `v > u`
      have "?\<psi> u < ?\<psi> v" by best
    moreover have "P (f (?\<psi> u)) (f (?\<psi> v))"
      using `x \<in> ?G (\<phi> k)` and refl
      unfolding u v by (auto simp: reflp_on_def)
    ultimately show False using `bad P f` by (auto simp: good_def)
  qed
  from choice [OF this] obtain \<psi>
    where \<psi>: "\<forall>i\<ge>0. (\<psi> i) > i" and *: "\<And>i. \<phi> (\<psi> i) \<ge> \<phi> 0" by blast
  let ?\<psi> = "\<lambda>i. (\<psi> ^^ i) 0"
  let ?\<phi> = "\<lambda>i. \<phi> (?\<psi> i)"
  from funpow_mono [OF \<psi>]
    have **: "\<And>i j. i < j \<Longrightarrow> ?\<psi> i < ?\<psi> j" by auto
  let ?R = "\<lambda>i. f (?\<psi> i)"
  have "\<forall>i. ?R i \<in> ?G (?\<phi> i)" using G by auto
  moreover have "\<forall>i. ?\<phi> i \<ge> ?\<phi> 0" by (rule, induct_tac i) (auto simp: *)
  moreover have "bad P ?R"
    using ** and `bad P f` by (auto simp: good_def)
  ultimately show ?thesis by (blast intro: exI [of _ ?\<phi>] exI[of _ ?R])
qed

end

