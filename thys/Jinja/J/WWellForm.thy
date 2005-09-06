(*  Title:      Jinja/J/WWellForm.thy
    ID:         $Id: WWellForm.thy,v 1.2 2005-09-06 15:06:08 makarius Exp $
    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

header {* \isaheader{Weak well-formedness of Jinja programs} *}

theory WWellForm imports "../Common/WellForm" Expr begin

constdefs
  wwf_J_mdecl :: "J_prog \<Rightarrow> cname \<Rightarrow> J_mb mdecl \<Rightarrow> bool"
  "wwf_J_mdecl P C  \<equiv>  \<lambda>(M,Ts,T,(pns,body)).
  length Ts = length pns \<and> distinct pns \<and> this \<notin> set pns \<and> fv body \<subseteq> {this} \<union> set pns"

lemma wwf_J_mdecl[simp]:
  "wwf_J_mdecl P C (M,Ts,T,pns,body) =
  (length Ts = length pns \<and> distinct pns \<and> this \<notin> set pns \<and> fv body \<subseteq> {this} \<union> set pns)"
(*<*)by(simp add:wwf_J_mdecl_def)(*>*)


syntax
  wwf_J_prog :: "J_prog \<Rightarrow> bool"
translations
  "wwf_J_prog"  ==  "wf_prog wwf_J_mdecl"

end
