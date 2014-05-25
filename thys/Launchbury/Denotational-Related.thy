theory "Denotational-Related"
imports "Denotational" "ResourcedDenotational" ValueSimilarity
begin

text {*
Given the similarity relation it is straight-forward to prove that the standard
and the resourced denotational semantics produce similar results. (Theorem 10 in
|cite{functionspaces}).
*}

theorem denotational_semantics_similar: 
  assumes "\<rho> \<triangleleft>\<triangleright>\<^sup>* \<sigma>"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>C\<^sup>\<infinity>"
using assms
proof(induct e arbitrary: \<rho> \<sigma> rule:exp_induct)
  case (Var v)
  hence "\<rho> v \<triangleleft>\<triangleright> (\<sigma> v)\<cdot>C\<^sup>\<infinity>" by cases auto
  thus ?case by simp
next
  case (Lam v e)
  { fix x y
    assume "x \<triangleleft>\<triangleright> y\<cdot>C\<^sup>\<infinity>"
    with `\<rho> \<triangleleft>\<triangleright>\<^sup>* \<sigma>`
    have "\<rho>(v := x) \<triangleleft>\<triangleright>\<^sup>* \<sigma>(v := y)"
      by (auto 1 4)
    hence "\<lbrakk>e\<rbrakk>\<^bsub>\<rho>(v := x)\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>(v := y)\<^esub>)\<cdot>C\<^sup>\<infinity>"
      by (rule Lam.hyps)
  }
  thus ?case by auto
next
  case (App e v \<rho> \<sigma>)
  hence App': "\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>C\<^sup>\<infinity>" by auto
  thus ?case
  proof (cases rule: slimilar_bot_cases)
    case bot thus ?thesis by auto
  next
    case (Fn f g)
    from `\<rho> \<triangleleft>\<triangleright>\<^sup>* \<sigma>`
    have "\<rho> v \<triangleleft>\<triangleright> (\<sigma> v)\<cdot>C\<^sup>\<infinity>"  by auto
    thus ?thesis using Fn App' by auto
  qed
next
  case (Let as e \<rho> \<sigma>)
  have "\<lbrace>as\<rbrace>\<rho> \<triangleleft>\<triangleright>\<^sup>* \<N>\<lbrace>as\<rbrace>\<sigma>"
  proof (rule parallel_HSem_ind_different_ESem[OF pointwise_adm[OF similar_admI] fun_similar_fmap_bottom])
    fix \<rho>' :: "var \<Rightarrow> Value" and \<sigma>' :: "var \<Rightarrow> CValue"
    assume "\<rho>' \<triangleleft>\<triangleright>\<^sup>* \<sigma>'"
    show "\<rho> ++\<^bsub>domA as\<^esub> \<^bold>\<lbrakk> as \<^bold>\<rbrakk>\<^bsub>\<rho>'\<^esub> \<triangleleft>\<triangleright>\<^sup>* \<sigma> ++\<^bsub>domA as\<^esub> evalHeap as (\<lambda>e. \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<sigma>'\<^esub>)"
    proof(rule pointwiseI)
      case (goal1 x)
      show ?case using `\<rho> \<triangleleft>\<triangleright>\<^sup>* \<sigma>`
        by (auto simp add: lookup_override_on_eq lookupEvalHeap elim: Let(1)[OF _  `\<rho>' \<triangleleft>\<triangleright>\<^sup>* \<sigma>'`] )
    qed
  qed auto
  hence "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>as\<rbrace>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>as\<rbrace>\<sigma>\<^esub>)\<cdot>C\<^sup>\<infinity>" by (rule Let(2))
  thus ?case by simp
qed

corollary evalHeap_similar:
  "\<And>y z. y \<triangleleft>\<triangleright>\<^sup>* z \<Longrightarrow> \<^bold>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>y\<^esub> \<triangleleft>\<triangleright>\<^sup>* \<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>z\<^esub>"
  by (rule pointwiseI)
     (case_tac "x \<in> domA \<Gamma>", auto simp add: lookupEvalHeap denotational_semantics_similar)

theorem heaps_similar: "\<lbrace>\<Gamma>\<rbrace> \<triangleleft>\<triangleright>\<^sup>* \<N>\<lbrace>\<Gamma>\<rbrace>"
  by (rule parallel_HSem_ind_different_ESem[OF pointwise_adm[OF similar_admI]])
     (auto simp add: evalHeap_similar)

end
