(*  Title:      HOL/MicroJava/JVM/JVMDefensive.thy
    ID:         $Id: JVMDefensive.thy,v 1.1 2005-05-31 23:21:04 lsf37 Exp $
    Author:     Gerwin Klein
    Copyright   GPL
*)

header {* \isaheader{A Defensive JVM} *}

theory JVMDefensive
imports JVMExec "../Common/Conform":

text {*
  Extend the state space by one element indicating a type error (or
  other abnormal termination) *}
datatype 'a type_error = TypeError | Normal 'a

consts is_Addr :: "val \<Rightarrow> bool"
recdef is_Addr "{}"
  "is_Addr (Addr a) = True"
  "is_Addr v        = False"

consts is_Intg :: "val \<Rightarrow> bool"
recdef is_Intg "{}"
  "is_Intg (Intg i) = True"
  "is_Intg v        = False"

consts is_Bool :: "val \<Rightarrow> bool"
recdef is_Bool "{}"
  "is_Bool (Bool b) = True"
  "is_Bool v        = False"

constdefs
  is_Ref :: "val \<Rightarrow> bool"
  "is_Ref v \<equiv> v = Null \<or> is_Addr v"


consts
  check_instr :: "[instr, jvm_prog, heap, val list, val list, 
                  cname, mname, pc, frame list] \<Rightarrow> bool"
primrec 
check_instr_Load:
  "check_instr (Load n) P h stk loc C M\<^isub>0 pc frs = 
  (n < length loc)"

check_instr_Store:
  "check_instr (Store n) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (0 < length stk \<and> n < length loc)"

check_instr_Push:
  "check_instr (Push v) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (\<not>is_Addr v)"

check_instr_New:
  "check_instr (New C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  is_class P C"

check_instr_Getfield:
  "check_instr (Getfield F C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (0 < length stk \<and> (\<exists>C' T. P \<turnstile> C sees F:T in C') \<and> 
  (let (C', T) = field P C F; ref = hd stk in 
    C' = C \<and> is_Ref ref \<and> (ref \<noteq> Null \<longrightarrow> 
      h (the_Addr ref) \<noteq> None \<and> 
      (let (D,vs) = the (h (the_Addr ref)) in 
        P \<turnstile> D \<preceq>\<^sup>* C \<and> vs (F,C) \<noteq> None \<and> P,h \<turnstile> the (vs (F,C)) :\<le> T))))" 

check_instr_Putfield:
  "check_instr (Putfield F C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (1 < length stk \<and> (\<exists>C' T. P \<turnstile> C sees F:T in C') \<and>
  (let (C', T) = field P C F; v = hd stk; ref = hd (tl stk) in 
    C' = C \<and> is_Ref ref \<and> (ref \<noteq> Null \<longrightarrow> 
      h (the_Addr ref) \<noteq> None \<and> 
      (let D = fst (the (h (the_Addr ref))) in 
        P \<turnstile> D \<preceq>\<^sup>* C \<and> P,h \<turnstile> v :\<le> T))))" 

check_instr_Checkcast:
  "check_instr (Checkcast C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 < length stk \<and> is_class P C \<and> is_Ref (hd stk))"

check_instr_Invoke:
  "check_instr (Invoke M n) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (n < length stk \<and> is_Ref (stk!n) \<and>  
  (stk!n \<noteq> Null \<longrightarrow> 
    (let a = the_Addr (stk!n); 
         C = cname_of h a;
         Ts = fst (snd (method P C M))
    in h a \<noteq> None \<and> P \<turnstile> C has M \<and> 
       P,h \<turnstile> rev (take n stk) [:\<le>] Ts)))"
 
check_instr_Return:
  "check_instr Return P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 < length stk \<and> ((0 < length frs) \<longrightarrow> 
    (P \<turnstile> C\<^isub>0 has M\<^isub>0) \<and>    
    (let v = hd stk; 
         T = fst (snd (snd (method P C\<^isub>0 M\<^isub>0)))
     in P,h \<turnstile> v :\<le> T)))"
 
check_instr_Pop:
  "check_instr Pop P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (0 < length stk)"

check_instr_IAdd:
  "check_instr IAdd P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (1 < length stk \<and> is_Intg (hd stk) \<and> is_Intg (hd (tl stk)))"

check_instr_IfFalse:
  "check_instr (IfFalse b) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 < length stk \<and> is_Bool (hd stk) \<and> 0 \<le> int pc+b)"

check_instr_CmpEq:
  "check_instr CmpEq P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (1 < length stk)"

check_instr_Goto:
  "check_instr (Goto b) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 \<le> int pc+b)"

check_instr_Throw:
  "check_instr Throw P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 < length stk \<and> is_Ref (hd stk))"

constdefs
  check :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> bool"
  "check P \<sigma> \<equiv> let (xcpt, h, frs) = \<sigma> in
               (case frs of [] \<Rightarrow> True | (stk,loc,C,M,pc)#frs' \<Rightarrow> 
                P \<turnstile> C has M \<and>
                (let (C',Ts,T,mxs,mxl\<^isub>0,ins,xt) = method P C M; i = ins!pc in
                 pc < size ins \<and> size stk \<le> mxs \<and>
                 check_instr i P h stk loc C M pc frs'))"


  exec_d :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_state option type_error"
  "exec_d P \<sigma> \<equiv> if check P \<sigma> then Normal (exec (P, \<sigma>)) else TypeError"


consts
  "exec_1_d" :: "jvm_prog \<Rightarrow> (jvm_state type_error \<times> jvm_state type_error) set" 
syntax (xsymbols)
  "@exec_1_d" :: "jvm_prog \<Rightarrow> jvm_state type_error \<Rightarrow> jvm_state type_error \<Rightarrow> bool" 
                   ("_ \<turnstile> _ -jvmd\<rightarrow>\<^isub>1 _" [61,61,61]60)  
translations
  "P \<turnstile> \<sigma> -jvmd\<rightarrow>\<^isub>1 \<sigma>'" == "(\<sigma>,\<sigma>') \<in> exec_1_d P"
inductive "exec_1_d P" intros
  exec_1_d_ErrorI: "exec_d P \<sigma> = TypeError \<Longrightarrow> P \<turnstile> Normal \<sigma> -jvmd\<rightarrow>\<^isub>1 TypeError"
  exec_1_d_NormalI: "exec_d P \<sigma> = Normal (Some \<sigma>') \<Longrightarrow> P \<turnstile> Normal \<sigma> -jvmd\<rightarrow>\<^isub>1 Normal \<sigma>'"

-- "reflexive transitive closure:"
consts
  "exec_all_d" :: "jvm_prog \<Rightarrow> jvm_state type_error \<Rightarrow> jvm_state type_error \<Rightarrow> bool" 
                   ("_ |- _ -jvmd-> _" [61,61,61]60)
syntax (xsymbols)
  "exec_all_d" :: "jvm_prog \<Rightarrow> jvm_state type_error \<Rightarrow> jvm_state type_error \<Rightarrow> bool" 
                   ("_ \<turnstile> _ -jvmd\<rightarrow> _" [61,61,61]60)  
defs
  exec_all_d_def1: "P \<turnstile> \<sigma> -jvmd\<rightarrow> \<sigma>' \<equiv> (\<sigma>,\<sigma>') \<in> (exec_1_d P)\<^sup>*"

lemma exec_1_d_def:
  "exec_1_d P = {(s,t). \<exists>\<sigma>. s = Normal \<sigma> \<and> t = TypeError \<and> exec_d P \<sigma> = TypeError} \<union> 
                {(s,t). \<exists>\<sigma> \<sigma>'. s = Normal \<sigma> \<and> t = Normal \<sigma>' \<and> exec_d P \<sigma> = Normal (Some \<sigma>')}"
by (auto elim!: exec_1_d.elims intro!: exec_1_d.intros)


declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

lemma if_neq [dest!]:
  "(if P then A else B) \<noteq> B \<Longrightarrow> P"
  by (cases P, auto)

lemma exec_d_no_errorI [intro]:
  "check P \<sigma> \<Longrightarrow> exec_d P \<sigma> \<noteq> TypeError"
  by (unfold exec_d_def) simp

theorem no_type_error_commutes:
  "exec_d P \<sigma> \<noteq> TypeError \<Longrightarrow> exec_d P \<sigma> = Normal (exec (P, \<sigma>))"
  by (unfold exec_d_def, auto)


lemma defensive_imp_aggressive:
  "P \<turnstile> (Normal \<sigma>) -jvmd\<rightarrow> (Normal \<sigma>') \<Longrightarrow> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'"
(*<*)
proof -
  have "\<And>x y. P \<turnstile> x -jvmd\<rightarrow> y \<Longrightarrow> \<forall>\<sigma> \<sigma>'. x = Normal \<sigma> \<longrightarrow> y = Normal \<sigma>' \<longrightarrow>  P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'"
    apply (unfold exec_all_d_def1)
    apply (erule rtrancl_induct)
     apply (simp add: exec_all_def)
    apply (fold exec_all_d_def1)
    apply simp
    apply (intro allI impI)
    apply (erule exec_1_d.elims, simp)
    apply (simp add: exec_all_def exec_d_def split: type_error.splits split_if_asm)
    apply (rule rtrancl_trans, assumption)
    apply blast
    done
  moreover
  assume "P \<turnstile> (Normal \<sigma>) -jvmd\<rightarrow> (Normal \<sigma>')" 
  ultimately
  show "P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'" by blast
qed
(*>*)

end