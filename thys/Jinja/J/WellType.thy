(*  Title:      Jinja/J/WellType.thy
    ID:         $Id: WellType.thy,v 1.4 2007-02-07 17:19:08 stefanberghofer Exp $
    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

header {* \isaheader{Well-typedness of Jinja expressions} *}

theory WellType
imports "../Common/Objects" Expr
begin

types 
  env  = "vname \<rightharpoonup> ty"

inductive2
  WT :: "[J_prog,env, expr     , ty     ] \<Rightarrow> bool"
         ("_,_ \<turnstile> _ :: _"   [51,51,51]50)
  and WTs :: "[J_prog,env, expr list, ty list] \<Rightarrow> bool"
         ("_,_ \<turnstile> _ [::] _" [51,51,51]50)
  for P :: J_prog
where
  
  WTNew:
  "is_class P C  \<Longrightarrow>
  P,E \<turnstile> new C :: Class C"

| WTCast:
  "\<lbrakk> P,E \<turnstile> e :: Class D;  is_class P C;  P \<turnstile> C \<preceq>\<^sup>* D \<or> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> Cast C e :: Class C"

| WTVal:
  "typeof v = Some T \<Longrightarrow>
  P,E \<turnstile> Val v :: T"

| WTVar:
  "E V = Some T \<Longrightarrow>
  P,E \<turnstile> Var V :: T"
(*
WTBinOp:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1 :: T\<^isub>1;  P,E \<turnstile> e\<^isub>2 :: T\<^isub>2;
     case bop of Eq \<Rightarrow> (P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<or> P \<turnstile> T\<^isub>2 \<le> T\<^isub>1) \<and> T = Boolean
               | Add \<Rightarrow> T\<^isub>1 = Integer \<and> T\<^isub>2 = Integer \<and> T = Integer \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2 :: T"
*)
| WTBinOpEq:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1 :: T\<^isub>1;  P,E \<turnstile> e\<^isub>2 :: T\<^isub>2; P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<or> P \<turnstile> T\<^isub>2 \<le> T\<^isub>1 \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^isub>1 \<guillemotleft>Eq\<guillemotright> e\<^isub>2 :: Boolean"

| WTBinOpAdd:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1 :: Integer;  P,E \<turnstile> e\<^isub>2 :: Integer \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^isub>1 \<guillemotleft>Add\<guillemotright> e\<^isub>2 :: Integer"

| WTLAss:
  "\<lbrakk> E V = Some T;  P,E \<turnstile> e :: T';  P \<turnstile> T' \<le> T;  V \<noteq> this \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> V:=e :: Void"

| WTFAcc:
  "\<lbrakk> P,E \<turnstile> e :: Class C;  P \<turnstile> C sees F:T in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>F{D} :: T"

| WTFAss:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1 :: Class C;  P \<turnstile> C sees F:T in D;  P,E \<turnstile> e\<^isub>2 :: T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^isub>1\<bullet>F{D}:=e\<^isub>2 :: Void"

| WTCall:
  "\<lbrakk> P,E \<turnstile> e :: Class C;  P \<turnstile> C sees M:Ts \<rightarrow> T = (pns,body) in D;
     P,E \<turnstile> es [::] Ts';  P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>M(es) :: T"

| WTBlock:
  "\<lbrakk> is_type P T;  P,E(V \<mapsto> T) \<turnstile> e :: T' \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile> {V:T; e} :: T'"

| WTSeq:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1::T\<^isub>1;  P,E \<turnstile> e\<^isub>2::T\<^isub>2 \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile> e\<^isub>1;;e\<^isub>2 :: T\<^isub>2"
| WTCond:
  "\<lbrakk> P,E \<turnstile> e :: Boolean;  P,E \<turnstile> e\<^isub>1::T\<^isub>1;  P,E \<turnstile> e\<^isub>2::T\<^isub>2;
     P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<or> P \<turnstile> T\<^isub>2 \<le> T\<^isub>1;  P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<longrightarrow> T = T\<^isub>2;  P \<turnstile> T\<^isub>2 \<le> T\<^isub>1 \<longrightarrow> T = T\<^isub>1 \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> if (e) e\<^isub>1 else e\<^isub>2 :: T"

| WTWhile:
  "\<lbrakk> P,E \<turnstile> e :: Boolean;  P,E \<turnstile> c::T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> while (e) c :: Void"

| WTThrow:
  "P,E \<turnstile> e :: Class C  \<Longrightarrow> 
  P,E \<turnstile> throw e :: Void"

| WTTry:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1 :: T;  P,E(V \<mapsto> Class C) \<turnstile> e\<^isub>2 :: T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> try e\<^isub>1 catch(C V) e\<^isub>2 :: T"

-- "well-typed expression lists"

| WTNil:
  "P,E \<turnstile> [] [::] []"

| WTCons:
  "\<lbrakk> P,E \<turnstile> e :: T;  P,E \<turnstile> es [::] Ts \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile> e#es [::] T#Ts"

(*<*)
(*
lemmas [intro!] = WTNew WTCast WTVal WTVar WTBinOp WTLAss WTFAcc WTFAss WTCall WTBlock WTSeq
                  WTWhile WTThrow WTTry WTNil WTCons
lemmas [intro]  = WTCond1 WTCond2
*)
declare WT_WTs.intros[intro!] (* WTNil[iff] *)

lemmas WT_WTs_induct = WT_WTs.induct [split_format (complete)]
  and WT_WTs_inducts = WT_WTs.inducts [split_format (complete)]
(*>*)

lemma [iff]: "(P,E \<turnstile> [] [::] Ts) = (Ts = [])"
(*<*)
apply(rule iffI)
apply (auto elim: WTs.cases)
done
(*>*)

lemma [iff]: "(P,E \<turnstile> e#es [::] T#Ts) = (P,E \<turnstile> e :: T \<and> P,E \<turnstile> es [::] Ts)"
(*<*)
apply(rule iffI)
apply (auto elim: WTs.cases)
done
(*>*)

lemma [iff]: "(P,E \<turnstile> (e#es) [::] Ts) =
  (\<exists>U Us. Ts = U#Us \<and> P,E \<turnstile> e :: U \<and> P,E \<turnstile> es [::] Us)"
(*<*)
apply(rule iffI)
apply (auto elim: WTs.cases)
done
(*>*)

lemma [iff]: "\<And>Ts. (P,E \<turnstile> es\<^isub>1 @ es\<^isub>2 [::] Ts) =
  (\<exists>Ts\<^isub>1 Ts\<^isub>2. Ts = Ts\<^isub>1 @ Ts\<^isub>2 \<and> P,E \<turnstile> es\<^isub>1 [::] Ts\<^isub>1 \<and> P,E \<turnstile> es\<^isub>2[::]Ts\<^isub>2)"
(*<*)
apply(induct es\<^isub>1 type:list)
 apply simp
apply clarsimp
apply(erule thin_rl)
apply (rule iffI)
 apply clarsimp
 apply(rule exI)+
 apply(rule conjI)
  prefer 2 apply blast
 apply simp
apply fastsimp
done
(*>*)

lemma [iff]: "P,E \<turnstile> Val v :: T = (typeof v = Some T)"
(*<*)
apply(rule iffI)
apply (auto elim: WT.cases)
done
(*>*)

lemma [iff]: "P,E \<turnstile> Var V :: T = (E V = Some T)"
(*<*)
apply(rule iffI)
apply (auto elim: WT.cases)
done
(*>*)

lemma [iff]: "P,E \<turnstile> e\<^isub>1;;e\<^isub>2 :: T\<^isub>2 = (\<exists>T\<^isub>1. P,E \<turnstile> e\<^isub>1::T\<^isub>1 \<and> P,E \<turnstile> e\<^isub>2::T\<^isub>2)"
(*<*)
apply(rule iffI)
apply (auto elim: WT.cases)
done
(*>*)

lemma [iff]: "(P,E \<turnstile> {V:T; e} :: T') = (is_type P T \<and> P,E(V\<mapsto>T) \<turnstile> e :: T')"
(*<*)
apply(rule iffI)
apply (auto elim: WT.cases)
done
(*>*)

(*<*)
inductive_cases2 WT_elim_cases[elim!]:
  "P,E \<turnstile> V :=e :: T"
  "P,E \<turnstile> if (e) e\<^isub>1 else e\<^isub>2 :: T"
  "P,E \<turnstile> while (e) c :: T"
  "P,E \<turnstile> throw e :: T"
  "P,E \<turnstile> try e\<^isub>1 catch(C V) e\<^isub>2 :: T"
  "P,E \<turnstile> Cast D e :: T"
  "P,E \<turnstile> a\<bullet>F{D} :: T"
  "P,E \<turnstile> a\<bullet>F{D} := v :: T"
  "P,E \<turnstile> e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2 :: T"
  "P,E \<turnstile> new C :: T"
  "P,E \<turnstile> e\<bullet>M(ps) :: T"
(*>*)


lemma wt_env_mono:
  "P,E \<turnstile> e :: T \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E' \<turnstile> e :: T)" and 
  "P,E \<turnstile> es [::] Ts \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E' \<turnstile> es [::] Ts)"
(*<*)
apply(induct rule: WT_WTs_inducts)
apply(simp add: WTNew)
apply(fastsimp simp: WTCast)
apply(fastsimp simp: WTVal)
apply(simp add: WTVar map_le_def dom_def)
apply(fastsimp simp: WTBinOpEq)
apply(fastsimp simp: WTBinOpAdd)
apply(force simp:map_le_def)
apply(fastsimp simp: WTFAcc)
apply(fastsimp simp: WTFAss del:WT_WTs.intros WT_elim_cases)
apply(fastsimp simp: WTCall)
apply(fastsimp simp: map_le_def WTBlock)
apply(fastsimp simp: WTSeq)
apply(fastsimp simp: WTCond)
apply(fastsimp simp: WTWhile)
apply(fastsimp simp: WTThrow)
apply(fastsimp simp: WTTry map_le_def dom_def)
apply(simp add: WTNil)
apply(simp add: WTCons)
done
(*>*)


lemma WT_fv: "P,E \<turnstile> e :: T \<Longrightarrow> fv e \<subseteq> dom E"
and "P,E \<turnstile> es [::] Ts \<Longrightarrow> fvs es \<subseteq> dom E"
(*<*)
apply(induct rule:WT_WTs.inducts)
apply(simp_all del: fun_upd_apply)
apply fast+
done

end
(*>*)
