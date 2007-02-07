(*  Title:       CoreC++
    ID:          $Id: ClassRel.thy,v 1.7 2007-02-07 17:24:54 stefanberghofer Exp $
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Based on the Jinja theory Common/TypeRel.thy by Tobias Nipkow
*)


header {* \isaheader{The subclass relation} *}

theory ClassRel imports Decl begin


-- "direct repeated subclass"
inductive2
  subclsR   :: "prog \<Rightarrow> [cname, cname] \<Rightarrow> bool" ("_ \<turnstile> _ \<prec>\<^sub>R _" [71,71,71] 70)
  for P :: prog
where
  subclsRI: "\<lbrakk>class P C = Some (Bs,rest); Repeats(D) \<in> set Bs\<rbrakk> 
\<Longrightarrow> P \<turnstile> C \<prec>\<^sub>R D"

-- "direct shared subclass"
inductive2
  subclsS   :: "prog \<Rightarrow> [cname, cname] \<Rightarrow> bool" ("_ \<turnstile> _ \<prec>\<^sub>S _" [71,71,71] 70)
  for P :: prog
where
  subclsSI: "\<lbrakk>class P C = Some (Bs,rest); Shares(D) \<in> set Bs\<rbrakk> 
\<Longrightarrow> P \<turnstile> C \<prec>\<^sub>S D"

 -- "direct subclass"
inductive2
  subcls1   :: "prog \<Rightarrow> [cname, cname] \<Rightarrow> bool" ("_ \<turnstile> _ \<prec>\<^sup>1 _" [71,71,71] 70)
  for P :: prog
where
  subcls1I: "\<lbrakk>class P C = Some (Bs,rest); D \<in>  baseClasses Bs\<rbrakk> 
\<Longrightarrow> P \<turnstile> C \<prec>\<^sup>1 D"

abbreviation
  subcls    :: "prog \<Rightarrow> [cname, cname] \<Rightarrow> bool" ("_ \<turnstile> _ \<preceq>\<^sup>* _"  [71,71,71] 70) where
  "P \<turnstile> C \<preceq>\<^sup>* D \<equiv> (subcls1 P)\<^sup>*\<^sup>* C D"
 

lemma subclsRD:
  "P \<turnstile> C \<prec>\<^sub>R D \<Longrightarrow> \<exists>fs ms Bs. (class P C = Some (Bs,fs,ms)) \<and> (Repeats(D) \<in> set Bs)"
by(auto elim: subclsR.cases)

lemma subclsSD:
  "P \<turnstile> C \<prec>\<^sub>S D \<Longrightarrow> \<exists>fs ms Bs. (class P C = Some (Bs,fs,ms)) \<and> (Shares(D) \<in> set Bs)"
by(auto elim: subclsS.cases)

lemma subcls1D:
  "P \<turnstile> C \<prec>\<^sup>1 D \<Longrightarrow> \<exists>fs ms Bs. (class P C = Some (Bs,fs,ms)) \<and> (D \<in> baseClasses Bs)"
by(auto elim: subcls1.cases)


lemma subclsR_subcls1:
  "P \<turnstile> C \<prec>\<^sub>R D \<Longrightarrow> P \<turnstile> C \<prec>\<^sup>1 D"
by (auto elim!:subclsR.cases intro:subcls1I simp:RepBaseclass_isBaseclass)

lemma subclsS_subcls1:
  "P \<turnstile> C \<prec>\<^sub>S D \<Longrightarrow> P \<turnstile> C \<prec>\<^sup>1 D"
by (auto elim!:subclsS.cases intro:subcls1I simp:ShBaseclass_isBaseclass)

lemma subcls1_subclsR_or_subclsS:
  "P \<turnstile> C \<prec>\<^sup>1 D \<Longrightarrow> P \<turnstile> C \<prec>\<^sub>R D \<or> P \<turnstile> C \<prec>\<^sub>S D"
by (auto dest!:subcls1D intro:subclsRI 
  dest:baseClasses_repeats_or_shares subclsSI)

lemma finite_subcls1: "finite (Collect2 (subcls1 P))"

apply(subgoal_tac "Collect2 (subcls1 P) = (SIGMA C: {C. is_class P C} . 
                     {D. D \<in> baseClasses (fst(the(class P C)))})")
 prefer 2
 apply(fastsimp simp:is_class_def dest: subcls1D elim: subcls1I)
apply simp
apply(rule finite_SigmaI [OF finite_is_class])
apply(rule_tac B = "baseClasses (fst (the (class P C)))" in finite_subset)
apply (auto intro:finite_baseClasses simp:is_class_def)
done


lemma finite_subclsR: "finite (Collect2 (subclsR P))"
by(rule_tac B = "Collect2 (subcls1 P)" in finite_subset, 
  auto simp:subclsR_subcls1 finite_subcls1)

lemma finite_subclsS: "finite (Collect2 (subclsS P))"
by(rule_tac B = "Collect2 (subcls1 P)" in finite_subset, 
  auto simp:subclsS_subcls1 finite_subcls1)

lemma subcls1_class:
  "P \<turnstile> C \<prec>\<^sup>1 D \<Longrightarrow> is_class P C"
by (auto dest:subcls1D simp:is_class_def)

lemma subcls_is_class:
"\<lbrakk>P \<turnstile> D \<preceq>\<^sup>* C; is_class P C\<rbrakk> \<Longrightarrow> is_class P D"
by (induct rule:rtrancl_induct',auto dest:subcls1_class)

end
