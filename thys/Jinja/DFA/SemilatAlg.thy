(*  Title:      HOL/MicroJava/BV/SemilatAlg.thy
    ID:         $Id: SemilatAlg.thy,v 1.1 2005-05-31 23:21:04 lsf37 Exp $
    Author:     Gerwin Klein
    Copyright   2002 Technische Universitaet Muenchen
*)

header {* \isaheader{More on Semilattices} *}

theory SemilatAlg = Typing_Framework:

consts 
  lesubstep_type :: "(nat \<times> 's) set \<Rightarrow> 's ord \<Rightarrow> (nat \<times> 's) set \<Rightarrow> bool"
(*<*)
syntax
  lesubstep_type :: "(nat \<times> 's) set \<Rightarrow> 's ord \<Rightarrow> (nat \<times> 's) set \<Rightarrow> bool"
                    ("(_ /{<='__} _)" [50, 0, 51] 50)
(*>*)
syntax (xsymbols)
  lesubstep_type :: "(nat \<times> 's) set \<Rightarrow> 's ord \<Rightarrow> (nat \<times> 's) set \<Rightarrow> bool"
                    ("(_ /{\<sqsubseteq>\<^bsub>_\<^esub>} _)" [50, 0, 51] 50)
defs lesubstep_type_def:
  "A {\<sqsubseteq>\<^bsub>r\<^esub>} B \<equiv> \<forall>(p,\<tau>) \<in> A. \<exists>\<tau>'. (p,\<tau>') \<in> B \<and> \<tau> \<sqsubseteq>\<^sub>r \<tau>'"

consts
  pluslussub :: "'a list \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" 
(*<*)
syntax 
  pluslussub :: "'a list \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" ("(_ /++'__ _)" [65, 1000, 66] 65)
(*>*)
syntax (xsymbols)
  pluslussub :: "'a list \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" ("(_ /\<Squnion>\<^bsub>_\<^esub> _)" [65, 0, 66] 65)
primrec
  "[] \<Squnion>\<^bsub>f\<^esub> y = y"
  "(x#xs) \<Squnion>\<^bsub>f\<^esub> y = xs \<Squnion>\<^bsub>f\<^esub> (x \<squnion>\<^sub>f y)"

constdefs
  bounded :: "'s step_type \<Rightarrow> nat \<Rightarrow> bool"
  "bounded step n \<equiv> \<forall>p<n. \<forall>\<tau>. \<forall>(q,\<tau>') \<in> set (step p \<tau>). q<n"  

  pres_type :: "'s step_type \<Rightarrow> nat \<Rightarrow> 's set \<Rightarrow> bool"
  "pres_type step n A \<equiv> \<forall>\<tau>\<in>A. \<forall>p<n. \<forall>(q,\<tau>') \<in> set (step p \<tau>). \<tau>' \<in> A"

  mono :: "'s ord \<Rightarrow> 's step_type \<Rightarrow> nat \<Rightarrow> 's set \<Rightarrow> bool"
  "mono r step n A \<equiv> 
  \<forall>\<tau> p \<tau>'. \<tau> \<in> A \<and> p<n \<and> \<tau> \<sqsubseteq>\<^sub>r \<tau>' \<longrightarrow> set (step p \<tau>) {\<sqsubseteq>\<^bsub>r\<^esub>} set (step p \<tau>')"

lemma [iff]: "{} {\<sqsubseteq>\<^bsub>r\<^esub>} B" 
  (*<*) by (simp add: lesubstep_type_def) (*>*)

lemma [iff]: "(A {\<sqsubseteq>\<^bsub>r\<^esub>} {}) = (A = {})"
  (*<*) by (cases "A={}") (auto simp add: lesubstep_type_def) (*>*)

lemma lesubstep_union:
  "\<lbrakk> A\<^isub>1 {\<sqsubseteq>\<^bsub>r\<^esub>} B\<^isub>1; A\<^isub>2 {\<sqsubseteq>\<^bsub>r\<^esub>} B\<^isub>2 \<rbrakk> \<Longrightarrow> A\<^isub>1 \<union> A\<^isub>2 {\<sqsubseteq>\<^bsub>r\<^esub>} B\<^isub>1 \<union> B\<^isub>2"
  (*<*) by (auto simp add: lesubstep_type_def) (*>*)

lemma pres_typeD:
  "\<lbrakk> pres_type step n A; s\<in>A; p<n; (q,s')\<in>set (step p s) \<rbrakk> \<Longrightarrow> s' \<in> A"
(*<*) by (unfold pres_type_def, blast) (*>*)

lemma monoD:
  "\<lbrakk> mono r step n A; p < n; s\<in>A; s \<sqsubseteq>\<^sub>r t \<rbrakk> \<Longrightarrow> set (step p s) {\<sqsubseteq>\<^bsub>r\<^esub>} set (step p t)"
(*<*) by (unfold mono_def, blast) (*>*)

lemma boundedD: 
  "\<lbrakk> bounded step n; p < n; (q,t) \<in> set (step p xs) \<rbrakk> \<Longrightarrow> q < n" 
(*<*) by (unfold bounded_def, blast) (*>*)

lemma lesubstep_type_refl [simp, intro]:
  "(\<And>x. x \<sqsubseteq>\<^sub>r x) \<Longrightarrow> A {\<sqsubseteq>\<^bsub>r\<^esub>} A"
(*<*) by (unfold lesubstep_type_def) auto (*>*)

lemma lesub_step_typeD:
  "A {\<sqsubseteq>\<^bsub>r\<^esub>} B \<Longrightarrow> (x,y) \<in> A \<Longrightarrow> \<exists>y'. (x, y') \<in> B \<and> y \<sqsubseteq>\<^sub>r y'"
(*<*) by (unfold lesubstep_type_def) blast (*>*)


lemma list_update_le_listI [rule_format]:
  "set xs \<subseteq> A \<longrightarrow> set ys \<subseteq> A \<longrightarrow> xs [\<sqsubseteq>\<^sub>r] ys \<longrightarrow> p < size xs \<longrightarrow>  
   x \<sqsubseteq>\<^sub>r ys!p \<longrightarrow> semilat(A,r,f) \<longrightarrow> x\<in>A \<longrightarrow> 
   xs[p := x \<squnion>\<^sub>f xs!p] [\<sqsubseteq>\<^sub>r] ys"
(*<*)
  apply (unfold Listn.le_def lesub_def semilat_def)
  apply (simp add: list_all2_conv_all_nth nth_list_update)
  done
(*>*)


lemma plusplus_closed: includes semilat shows
  "\<And>y. \<lbrakk> set x \<subseteq> A; y \<in> A\<rbrakk> \<Longrightarrow> x \<Squnion>\<^bsub>f\<^esub> y \<in> A"
(*<*)
proof (induct x)
  show "\<And>y. y \<in> A \<Longrightarrow> [] \<Squnion>\<^bsub>f\<^esub> y \<in> A" by simp
  fix y x xs
  assume y: "y \<in> A" and xs: "set (x#xs) \<subseteq> A"
  assume IH: "\<And>y. \<lbrakk> set xs \<subseteq> A; y \<in> A\<rbrakk> \<Longrightarrow> xs \<Squnion>\<^bsub>f\<^esub> y \<in> A"
  from xs obtain x: "x \<in> A" and "set xs \<subseteq> A" by simp
  from x y have "x \<squnion>\<^bsub>f\<^esub> y \<in> A" ..
  with xs have "xs \<Squnion>\<^bsub>f\<^esub> (x \<squnion>\<^bsub>f\<^esub> y) \<in> A" by - (rule IH)
  thus "x#xs \<Squnion>\<^bsub>f\<^esub> y \<in> A" by simp
qed
(*>*)

lemma (in semilat) pp_ub2:
 "\<And>y. \<lbrakk> set x \<subseteq> A; y \<in> A\<rbrakk> \<Longrightarrow> y \<sqsubseteq>\<^bsub>r\<^esub> x \<Squnion>\<^bsub>f\<^esub> y"
(*<*)
proof (induct x)
  from semilat show "\<And>y. y \<sqsubseteq>\<^bsub>r\<^esub> [] \<Squnion>\<^bsub>f\<^esub> y" by simp
  
  fix y a l assume y:  "y \<in> A" and "set (a#l) \<subseteq> A"
  then obtain a: "a \<in> A" and x: "set l \<subseteq> A" by simp
  assume "\<And>y. \<lbrakk>set l \<subseteq> A; y \<in> A\<rbrakk> \<Longrightarrow> y \<sqsubseteq>\<^bsub>r\<^esub> l \<Squnion>\<^bsub>f\<^esub> y"
  hence IH: "\<And>y. y \<in> A \<Longrightarrow> y \<sqsubseteq>\<^bsub>r\<^esub> l \<Squnion>\<^bsub>f\<^esub> y" .

  from a y have "y \<sqsubseteq>\<^bsub>r\<^esub> a \<squnion>\<^bsub>f\<^esub> y" ..
  also from a y have "a \<squnion>\<^bsub>f\<^esub> y \<in> A" ..
  hence "(a \<squnion>\<^bsub>f\<^esub> y) \<sqsubseteq>\<^bsub>r\<^esub> l \<Squnion>\<^bsub>f\<^esub> (a \<squnion>\<^bsub>f\<^esub> y)" by (rule IH)
  finally have "y \<sqsubseteq>\<^bsub>r\<^esub> l \<Squnion>\<^bsub>f\<^esub> (a \<squnion>\<^bsub>f\<^esub> y)" .
  thus "y \<sqsubseteq>\<^bsub>r\<^esub> (a#l) \<Squnion>\<^bsub>f\<^esub> y" by simp
qed
(*>*)


lemma (in semilat) pp_ub1:
shows "\<And>y. \<lbrakk>set ls \<subseteq> A; y \<in> A; x \<in> set ls\<rbrakk> \<Longrightarrow> x \<sqsubseteq>\<^bsub>r\<^esub> ls \<Squnion>\<^bsub>f\<^esub> y"
(*<*)
proof (induct ls)
  show "\<And>y. x \<in> set [] \<Longrightarrow> x \<sqsubseteq>\<^bsub>r\<^esub> [] \<Squnion>\<^bsub>f\<^esub> y" by simp

  fix y s ls
  assume "set (s#ls) \<subseteq> A"
  then obtain s: "s \<in> A" and ls: "set ls \<subseteq> A" by simp
  assume y: "y \<in> A" 

  assume "\<And>y. \<lbrakk>set ls \<subseteq> A; y \<in> A; x \<in> set ls\<rbrakk> \<Longrightarrow> x \<sqsubseteq>\<^bsub>r\<^esub> ls \<Squnion>\<^bsub>f\<^esub> y"
  hence IH: "\<And>y. x \<in> set ls \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sqsubseteq>\<^bsub>r\<^esub> ls \<Squnion>\<^bsub>f\<^esub> y" .

  assume "x \<in> set (s#ls)"
  then obtain xls: "x = s \<or> x \<in> set ls" by simp
  moreover {
    assume xs: "x = s"
    from s y have "s \<sqsubseteq>\<^bsub>r\<^esub> s \<squnion>\<^bsub>f\<^esub> y" ..
    also from s y have "s \<squnion>\<^bsub>f\<^esub> y \<in> A" ..
    with ls have "(s \<squnion>\<^bsub>f\<^esub> y) \<sqsubseteq>\<^bsub>r\<^esub> ls \<Squnion>\<^bsub>f\<^esub> (s \<squnion>\<^bsub>f\<^esub> y)" by (rule pp_ub2)
    finally have "s \<sqsubseteq>\<^bsub>r\<^esub> ls \<Squnion>\<^bsub>f\<^esub> (s \<squnion>\<^bsub>f\<^esub> y)" .
    with xs have "x \<sqsubseteq>\<^bsub>r\<^esub> ls \<Squnion>\<^bsub>f\<^esub> (s \<squnion>\<^bsub>f\<^esub> y)" by simp
  } 
  moreover {
    assume "x \<in> set ls"
    hence "\<And>y. y \<in> A \<Longrightarrow> x \<sqsubseteq>\<^bsub>r\<^esub> ls \<Squnion>\<^bsub>f\<^esub> y" by (rule IH)
    moreover from s y have "s \<squnion>\<^bsub>f\<^esub> y \<in> A" ..
    ultimately have "x \<sqsubseteq>\<^bsub>r\<^esub> ls \<Squnion>\<^bsub>f\<^esub> (s \<squnion>\<^bsub>f\<^esub> y)" .
  }
  ultimately 
  have "x \<sqsubseteq>\<^bsub>r\<^esub> ls \<Squnion>\<^bsub>f\<^esub> (s \<squnion>\<^bsub>f\<^esub> y)" by blast
  thus "x \<sqsubseteq>\<^bsub>r\<^esub> (s#ls) \<Squnion>\<^bsub>f\<^esub> y" by simp
qed
(*>*)


lemma (in semilat) pp_lub:
  assumes "z \<in> A"
  shows 
  "\<And>y. y \<in> A \<Longrightarrow> set xs \<subseteq> A \<Longrightarrow> \<forall>x \<in> set xs. x \<sqsubseteq>\<^bsub>r\<^esub> z \<Longrightarrow> y \<sqsubseteq>\<^bsub>r\<^esub> z \<Longrightarrow> xs \<Squnion>\<^bsub>f\<^esub> y \<sqsubseteq>\<^bsub>r\<^esub> z"
(*<*)
proof (induct xs)
  fix y assume "y \<sqsubseteq>\<^bsub>r\<^esub> z" thus "[] \<Squnion>\<^bsub>f\<^esub> y \<sqsubseteq>\<^bsub>r\<^esub> z" by simp
next
  fix y l ls assume y: "y \<in> A" and "set (l#ls) \<subseteq> A"
  then obtain l: "l \<in> A" and ls: "set ls \<subseteq> A" by auto
  assume "\<forall>x \<in> set (l#ls). x \<sqsubseteq>\<^bsub>r\<^esub> z"
  then obtain "l \<sqsubseteq>\<^bsub>r\<^esub> z" and lsz: "\<forall>x \<in> set ls. x \<sqsubseteq>\<^bsub>r\<^esub> z" by auto
  assume "y \<sqsubseteq>\<^bsub>r\<^esub> z" have "l \<squnion>\<^bsub>f\<^esub> y \<sqsubseteq>\<^bsub>r\<^esub> z" ..  
  moreover
  from l y have "l \<squnion>\<^bsub>f\<^esub> y \<in> A" ..
  moreover
  assume "\<And>y. y \<in> A \<Longrightarrow> set ls \<subseteq> A \<Longrightarrow> \<forall>x \<in> set ls. x \<sqsubseteq>\<^bsub>r\<^esub> z \<Longrightarrow> y \<sqsubseteq>\<^bsub>r\<^esub> z
          \<Longrightarrow> ls \<Squnion>\<^bsub>f\<^esub> y \<sqsubseteq>\<^bsub>r\<^esub> z"
  ultimately
  have "ls \<Squnion>\<^bsub>f\<^esub> (l \<squnion>\<^bsub>f\<^esub> y) \<sqsubseteq>\<^bsub>r\<^esub> z" using ls lsz by -
  thus "(l#ls) \<Squnion>\<^bsub>f\<^esub> y \<sqsubseteq>\<^bsub>r\<^esub> z" by simp
qed
(*>*)


lemma ub1': includes semilat
shows "\<lbrakk>\<forall>(p,s) \<in> set S. s \<in> A; y \<in> A; (a,b) \<in> set S\<rbrakk> 
  \<Longrightarrow> b \<sqsubseteq>\<^bsub>r\<^esub> map snd [(p', t')\<in>S. p' = a] \<Squnion>\<^bsub>f\<^esub> y" 
(*<*)
proof -
  let "b \<sqsubseteq>\<^bsub>r\<^esub> ?map \<Squnion>\<^bsub>f\<^esub> y" = ?thesis

  assume "y \<in> A"
  moreover
  assume "\<forall>(p,s) \<in> set S. s \<in> A"
  hence "set ?map \<subseteq> A" by auto
  moreover
  assume "(a,b) \<in> set S"
  hence "b \<in> set ?map" by (induct S, auto)
  ultimately
  show ?thesis by - (rule pp_ub1)
qed
(*>*)
    
 
lemma plusplus_empty:  
  "\<forall>s'. (q, s') \<in> set S \<longrightarrow> s' \<squnion>\<^bsub>f\<^esub> ss ! q = ss ! q \<Longrightarrow>
   (map snd [(p', t')\<in> S. p' = q] \<Squnion>\<^bsub>f\<^esub> ss ! q) = ss ! q"
(*<*)
apply (induct S)
apply auto 
done
(*>*)


end