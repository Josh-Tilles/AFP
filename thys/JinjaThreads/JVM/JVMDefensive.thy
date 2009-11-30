(*  Title:      JinjaThreads/JVM/JVMDefensive.thy
    Author:     Gerwin Klein, Andreas Lochbihler
*)

header {* \isaheader{A Defensive JVM} *}

theory JVMDefensive
imports JVMExec "../Common/ExternalCallWF"
begin

text {*
  Extend the state space by one element indicating a type error (or
  other abnormal termination) *}
datatype 'a type_error = TypeError | Normal 'a

definition is_Array_ref :: "val \<Rightarrow> heap \<Rightarrow> bool" where
  "is_Array_ref v h \<equiv> is_Ref v \<and> (v \<noteq> Null \<longrightarrow> h (the_Addr v) \<noteq> None \<and> is_Arr (the (h (the_Addr v))))"

declare is_Array_ref_def[simp]

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

check_instr_NewArray:
  "check_instr (NewArray T) P h stk loc C0 M0 pc frs =
  (is_type P T \<and> 0 < length stk \<and> is_Intg (hd stk))"

check_instr_ALoad:
  "check_instr ALoad P h stk loc C0 M0 pc frs =
  (1 < length stk \<and> is_Intg (hd stk) \<and> is_Array_ref (hd (tl stk)) h)"

check_instr_AStore:
  "check_instr AStore P h stk loc C0 M0 pc frs =
  (2 < length stk \<and> is_Intg (hd (tl stk)) \<and> is_Array_ref (hd (tl (tl stk))) h)"

check_instr_ALength:
  "check_instr ALength P h stk loc C0 M0 pc frs =
  (0 < length stk \<and> is_Array_ref (hd stk) h)"

check_instr_Getfield:
  "check_instr (Getfield F C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (0 < length stk \<and> (\<exists>C' T. P \<turnstile> C sees F:T in C') \<and> 
  (let (C', T) = field P C F; ref = hd stk in 
    C' = C \<and> is_Ref ref \<and> (ref \<noteq> Null \<longrightarrow> 
      h (the_Addr ref) \<noteq> None \<and> \<not> is_Arr (the (h (the_Addr ref))) \<and>
      (let (D,vs) = the_obj (the (h (the_Addr ref))) in 
        P \<turnstile> D \<preceq>\<^sup>* C \<and> vs (F,C) \<noteq> None \<and> P,h \<turnstile> the (vs (F,C)) :\<le> T))))" 

check_instr_Putfield:
  "check_instr (Putfield F C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (1 < length stk \<and> (\<exists>C' T. P \<turnstile> C sees F:T in C') \<and>
  (let (C', T) = field P C F; v = hd stk; ref = hd (tl stk) in 
    C' = C \<and> is_Ref ref \<and> (ref \<noteq> Null \<longrightarrow> 
      h (the_Addr ref) \<noteq> None \<and> \<not> is_Arr (the (h (the_Addr ref))) \<and>
      (let D = fst (the_obj (the (h (the_Addr ref)))) in 
        P \<turnstile> D \<preceq>\<^sup>* C \<and> P,h \<turnstile> v :\<le> T))))" 

check_instr_Checkcast:
  "check_instr (Checkcast T) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 < length stk \<and> is_type P T (* \<and> is_Ref (hd stk) *))"

check_instr_Invoke:
  "check_instr (Invoke M n) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (n < length stk \<and> is_Ref (stk!n) \<and>  
  (stk!n \<noteq> Null \<longrightarrow> 
    (let a = the_Addr (stk!n); 
         T = the (typeof\<^bsub>h\<^esub> (Addr a));
         C = cname_of h a;
         Ts = fst (snd (method P C M))
    in h a \<noteq> None \<and>
       (if is_external_call P T M then \<exists>U. P,h \<turnstile> a\<bullet>M(rev (take n stk)) : U 
        else \<not> is_Arr (the (h a)) \<and> P \<turnstile> C has M \<and> P,h \<turnstile> rev (take n stk) [:\<le>] Ts))))"

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

check_instr_BinOpInstr:
  "check_instr (BinOpInstr bop) P h stk loc C0 M0 pc frs =
  (1 < length stk \<and> (let T2 = the (typeof\<^bsub>h\<^esub> (hd stk)); T1 = the (typeof\<^bsub>h\<^esub> (hd (tl stk))) in \<exists>T. P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T))"

(*
check_instr_IAdd:
  "check_instr IAdd P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (1 < length stk \<and> is_Intg (hd stk) \<and> is_Intg (hd (tl stk)))"
*)

check_instr_IfFalse:
  "check_instr (IfFalse b) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 < length stk \<and> is_Bool (hd stk) \<and> 0 \<le> int pc+b)"

(*
check_instr_CmpEq:
  "check_instr CmpEq P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (1 < length stk)"
*)

check_instr_Goto:
  "check_instr (Goto b) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 \<le> int pc+b)"

check_instr_Throw:
  "check_instr ThrowExc P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 < length stk \<and> P \<turnstile> the (typeof\<^bsub>h\<^esub> (hd stk)) \<le> Class Throwable)"

check_instr_MEnter:
  "check_instr MEnter P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
   (0 < length stk \<and> is_Ref (hd stk))"

check_instr_MExit:
  "check_instr MExit P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
   (0 < length stk \<and> is_Ref (hd stk))"


constdefs
  check :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> bool"
  "check P \<sigma> \<equiv> let (xcpt, h, frs) = \<sigma> in
               (case frs of [] \<Rightarrow> True | (stk,loc,C,M,pc)#frs' \<Rightarrow> 
                P \<turnstile> C has M \<and>
                (let (C',Ts,T,mxs,mxl\<^isub>0,ins,xt) = method P C M; i = ins!pc in
                 pc < size ins \<and> size stk \<le> mxs \<and>
                 (xcpt = None \<longrightarrow> check_instr i P h stk loc C M pc frs')))"


constdefs
  exec_d :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_ta_state list type_error"
  "exec_d P \<sigma> \<equiv> if check P \<sigma> then Normal (exec P \<sigma>) else TypeError"

inductive
  exec_1_d :: "jvm_prog \<Rightarrow> jvm_state type_error \<Rightarrow> jvm_thread_action \<Rightarrow> jvm_state type_error \<Rightarrow> bool" 
       ("_ \<turnstile> _ -_-jvmd\<rightarrow> _" [61,61,0,61] 60)
  for P :: jvm_prog
where
  exec_1_d_ErrorI: "exec_d P \<sigma> = TypeError \<Longrightarrow> P \<turnstile> Normal \<sigma> -\<epsilon>-jvmd\<rightarrow> TypeError"
| exec_1_d_NormalI: "\<lbrakk> exec_d P \<sigma> = Normal \<Sigma>; (tas, \<sigma>') \<in> set \<Sigma> \<rbrakk>  \<Longrightarrow> P \<turnstile> Normal \<sigma> -tas-jvmd\<rightarrow> Normal \<sigma>'"

lemma jvmd_NormalD:
  "P \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>' \<Longrightarrow> check P \<sigma> \<and> (ta, \<sigma>') \<in> set (exec P \<sigma>) \<and> (\<exists>xcp h f frs. \<sigma> = (xcp, h, f # frs))"
apply(erule exec_1_d.cases, auto simp add: exec_d_def split: split_if_asm)
apply(case_tac b, auto)
done

lemma jvmd_NormalE:
  assumes "P \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'"
  obtains xcp h f frs where "check P \<sigma>" "(ta, \<sigma>') \<in> set (exec P \<sigma>)" "\<sigma> = (xcp, h, f # frs)"
using assms
by(auto dest: jvmd_NormalD)

lemma exec_d_eq_TypeError: "exec_d P \<sigma> = TypeError \<longleftrightarrow> \<not> check P \<sigma>"
by(simp add: exec_d_def)

lemma exec_d_eq_Normal: "exec_d P \<sigma> = Normal (exec P \<sigma>) \<longleftrightarrow> check P \<sigma>"
by(auto simp add: exec_d_def)



-- "reflexive transitive closure:"

definition
  exec_star_d :: "jvm_prog \<Rightarrow> jvm_state type_error \<Rightarrow> jvm_thread_action list \<Rightarrow> jvm_state type_error \<Rightarrow> bool"
                 ("_ \<turnstile>/ _ -_-jvmd\<rightarrow>*/ _" [61,61,0,61] 60)
where
  "P \<turnstile> \<sigma> -tas-jvmd\<rightarrow>* \<sigma>' \<equiv> rtrancl3p (exec_1_d P) \<sigma> tas \<sigma>'"

declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

lemma if_neq [dest!]:
  "(if P then A else B) \<noteq> B \<Longrightarrow> P"
  by (cases P, auto)

lemma exec_d_no_errorI [intro]:
  "check P \<sigma> \<Longrightarrow> exec_d P \<sigma> \<noteq> TypeError"
  by (unfold exec_d_def) simp

theorem no_type_error_commutes:
  "exec_d P \<sigma> \<noteq> TypeError \<Longrightarrow> exec_d P \<sigma> = Normal (exec P \<sigma>)"
  by (unfold exec_d_def, auto)


lemma defensive_imp_aggressive_1:
  "P \<turnstile> (Normal \<sigma>) -tas-jvmd\<rightarrow> (Normal \<sigma>') \<Longrightarrow> P \<turnstile> \<sigma> -tas-jvm\<rightarrow> \<sigma>'"
by(auto elim!: exec_1_d.cases intro!: exec_1.intros simp add: exec_d_def split: split_if_asm)


lemma defensive_imp_aggressive:
  assumes "P \<turnstile> (Normal \<sigma>) -tas-jvmd\<rightarrow>* (Normal \<sigma>')"
  shows "P \<turnstile> \<sigma> -tas-jvm\<rightarrow>* \<sigma>'"
proof -
  have "\<And>x y. P \<turnstile> x -tas-jvmd\<rightarrow>* y \<Longrightarrow> \<forall>\<sigma> \<sigma>'. x = Normal \<sigma> \<longrightarrow> y = Normal \<sigma>' \<longrightarrow>  P \<turnstile> \<sigma> -tas-jvm\<rightarrow>* \<sigma>'"
    apply(unfold exec_star_d_def)
    apply(erule rtrancl3p.induct)
     apply(unfold exec_star_def)
     apply(fastsimp intro: rtrancl3p_refl)
    apply(fold exec_star_d_def)
    apply(simp split: type_error.splits)
    apply(case_tac a, simp, simp)
    apply(case_tac a', simp)
     apply(erule exec_1_d.cases)
      apply(simp)
     apply(simp)
    apply(simp)
    apply(case_tac a'', simp, simp)
    apply(drule defensive_imp_aggressive_1)
    by(rule rtrancl3p_step)
  with `P \<turnstile> (Normal \<sigma>) -tas-jvmd\<rightarrow>* (Normal \<sigma>')`
  show ?thesis
    by blast
qed


lemma check_exec_hext:
  assumes exec: "(ta, xcp', h', frs') \<in> set (exec P (xcp, h, frs))"
  and check: "check P (xcp, h, frs)"
  shows "h \<unlhd> h'"
proof -
  from exec have "frs \<noteq> []" by(auto)
  then obtain f Frs where frs [simp]: "frs = f # Frs"
    by(fastsimp simp add: neq_Nil_conv)
  obtain stk loc C0 M0 pc where f [simp]: "f = (stk, loc, C0, M0, pc)"
    by(cases f, blast)
  show ?thesis
  proof(cases xcp)
    case None
    with check obtain C' Ts T mxs mxl0 ins xt
      where mthd: "P \<turnstile> C0 sees M0 : Ts \<rightarrow> T = (mxs, mxl0, ins, xt) in C'"
                  "method P C0 M0 = (C', Ts, T, mxs, mxl0, ins, xt)"
      and check_ins: "check_instr (ins ! pc) P h stk loc C0 M0 pc Frs"
      and "pc < length ins"
      and "length stk \<le> mxs"
      by(auto simp add: check_def has_method_def)
    from None exec mthd
    have xexec: "(ta, xcp', h', frs') \<in> set (exec_instr (ins ! pc) P h stk loc C0 M0 pc Frs)" by(clarsimp)
    thus ?thesis
    proof(cases "ins ! pc")
      case (New C)
      with xexec show ?thesis by(auto dest: new_Addr_SomeD intro: hext_new)
    next
      case (NewArray T)
      with xexec show ?thesis
	by(auto dest: new_Addr_SomeD intro: hext_new split: split_if_asm)
    next
      case AStore
      with xexec check_ins show ?thesis
	by(auto intro: hext_upd_arr elim!: is_ArrE simp add: split_beta split: split_if_asm)
    next
      case Putfield
      with xexec check_ins show ?thesis
	by(auto intro: hext_upd_obj elim!: is_ArrE simp add: split_beta is_Ref_def split: split_if_asm)
    next
      case (Invoke M n)
      with xexec check_ins show ?thesis
	by(auto intro: hext_upd_obj elim!: is_ArrE
                simp add: min_def split_beta is_Ref_def
                          extRet2JVM_def[folded Datatype.sum_case_def]
                split: split_if_asm sum.split_asm dest: red_external_list_hext)
    qed(auto simp add: split_beta split: split_if_asm)
  next
    case (Some a)
    with exec have "h' = h" by auto
    thus ?thesis by auto
  qed
qed

lemma exec_1_d_hext:
  "\<lbrakk> P \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs') \<rbrakk> \<Longrightarrow> h \<unlhd> h'"
apply(auto elim!: exec_1_d.cases simp add: exec_d_def split: split_if_asm intro: check_exec_hext)
done


end
