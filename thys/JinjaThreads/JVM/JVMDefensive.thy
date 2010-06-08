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

fun is_Array :: "ty \<Rightarrow> bool"
where
  "is_Array (Array T) = True"
| "is_Array _ = False"

lemma is_Array_conv [simp]: "is_Array T \<longleftrightarrow> (\<exists>U. T = Array U)"
by(cases T) simp_all

fun is_Class :: "ty \<Rightarrow> bool"
where
  "is_Class (Class C) = True"
| "is_Class _ = False"

lemma is_Class_conv [simp]: "is_Class T \<longleftrightarrow> (\<exists>C. T = Class C)"
by(cases T) simp_all

context JVM_heap_base begin

definition is_Array_ref :: "val \<Rightarrow> 'heap \<Rightarrow> bool" where
  "is_Array_ref v h \<equiv> 
  is_Ref v \<and> 
  (v \<noteq> Null \<longrightarrow> typeof_addr h (the_Addr v) \<noteq> None \<and> is_Array (the (typeof_addr h (the_Addr v))))"

declare is_Array_ref_def[simp]

primrec check_instr :: "[instr, jvm_prog, 'heap, val list, val list, 
                        cname, mname, pc, frame list] \<Rightarrow> bool"
where
  check_instr_Load:
  "check_instr (Load n) P h stk loc C M\<^isub>0 pc frs = 
  (n < length loc)"

| check_instr_Store:
  "check_instr (Store n) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (0 < length stk \<and> n < length loc)"

| check_instr_Push:
  "check_instr (Push v) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (\<not>is_Addr v)"

| check_instr_New:
  "check_instr (New C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  is_class P C"

| check_instr_NewArray:
  "check_instr (NewArray T) P h stk loc C0 M0 pc frs =
  (is_type P T \<and> 0 < length stk \<and> is_Intg (hd stk))"

| check_instr_ALoad:
  "check_instr ALoad P h stk loc C0 M0 pc frs =
  (1 < length stk \<and> is_Intg (hd stk) \<and> is_Array_ref (hd (tl stk)) h)"

| check_instr_AStore:
  "check_instr AStore P h stk loc C0 M0 pc frs =
  (2 < length stk \<and> is_Intg (hd (tl stk)) \<and> is_Array_ref (hd (tl (tl stk))) h)"

| check_instr_ALength:
  "check_instr ALength P h stk loc C0 M0 pc frs =
  (0 < length stk \<and> is_Array_ref (hd stk) h)"

| check_instr_Getfield:
  "check_instr (Getfield F C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (0 < length stk \<and> (\<exists>C' T. P \<turnstile> C sees F:T in C') \<and> 
  (let (C', T) = field P C F; ref = hd stk in 
    C' = C \<and> is_Ref ref \<and> (ref \<noteq> Null \<longrightarrow> 
      (\<exists>D. typeof_addr h (the_Addr ref) = \<lfloor>Class D\<rfloor> \<and> P \<turnstile> D \<preceq>\<^sup>* C))))"

| check_instr_Putfield:
  "check_instr (Putfield F C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (1 < length stk \<and> (\<exists>C' T. P \<turnstile> C sees F:T in C') \<and>
  (let (C', T) = field P C F; v = hd stk; ref = hd (tl stk) in 
    C' = C \<and> is_Ref ref \<and> (ref \<noteq> Null \<longrightarrow> 
      (\<exists>D. typeof_addr h (the_Addr ref) = \<lfloor>Class D\<rfloor> \<and> P \<turnstile> D \<preceq>\<^sup>* C))))"

| check_instr_Checkcast:
  "check_instr (Checkcast T) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 < length stk \<and> is_type P T)"

| check_instr_Instanceof:
  "check_instr (Instanceof T) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 < length stk \<and> is_type P T \<and> is_Ref (hd stk))"

| check_instr_Invoke:
  "check_instr (Invoke M n) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (n < length stk \<and> is_Ref (stk!n) \<and>  
  (stk!n \<noteq> Null \<longrightarrow> 
    (let a = the_Addr (stk!n); 
         T = the (typeof_addr h a);
         C = the_Class T;
         Ts = fst (snd (method P C M))
    in typeof_addr h a \<noteq> None \<and>
       (if is_external_call P T M then \<exists>U. P,h \<turnstile> a\<bullet>M(rev (take n stk)) : U 
        else is_Class T \<and> P \<turnstile> C has M \<and> P,h \<turnstile> rev (take n stk) [:\<le>] Ts))))"

| check_instr_Return:
  "check_instr Return P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 < length stk \<and> ((0 < length frs) \<longrightarrow> 
    (P \<turnstile> C\<^isub>0 has M\<^isub>0) \<and>    
    (let v = hd stk; 
         T = fst (snd (snd (method P C\<^isub>0 M\<^isub>0)))
     in P,h \<turnstile> v :\<le> T)))"

| check_instr_Pop:
  "check_instr Pop P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (0 < length stk)"

| check_instr_Dup:
  "check_instr Dup P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (0 < length stk)"

| check_instr_BinOpInstr:
  "check_instr (BinOpInstr bop) P h stk loc C0 M0 pc frs =
  (1 < length stk \<and> (let T2 = the (typeof\<^bsub>h\<^esub> (hd stk)); T1 = the (typeof\<^bsub>h\<^esub> (hd (tl stk))) in \<exists>T. P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T))"

| check_instr_IfFalse:
  "check_instr (IfFalse b) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 < length stk \<and> is_Bool (hd stk) \<and> 0 \<le> int pc+b)"

| check_instr_Goto:
  "check_instr (Goto b) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 \<le> int pc+b)"

| check_instr_Throw:
  "check_instr ThrowExc P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 < length stk \<and> P \<turnstile> the (typeof\<^bsub>h\<^esub> (hd stk)) \<le> Class Throwable)"

| check_instr_MEnter:
  "check_instr MEnter P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
   (0 < length stk \<and> is_Ref (hd stk))"

| check_instr_MExit:
  "check_instr MExit P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
   (0 < length stk \<and> is_Ref (hd stk))"

definition check :: "jvm_prog \<Rightarrow> 'heap jvm_state \<Rightarrow> bool"
where
  "check P \<sigma> \<equiv> let (xcpt, h, frs) = \<sigma> in
               (case frs of [] \<Rightarrow> True | (stk,loc,C,M,pc)#frs' \<Rightarrow> 
                P \<turnstile> C has M \<and>
                (let (C',Ts,T,mxs,mxl\<^isub>0,ins,xt) = method P C M; i = ins!pc in
                 pc < size ins \<and> size stk \<le> mxs \<and>
                 (xcpt = None \<longrightarrow> check_instr i P h stk loc C M pc frs')))"


definition exec_d :: "jvm_prog \<Rightarrow> thread_id \<Rightarrow> 'heap jvm_state \<Rightarrow> 'heap jvm_ta_state set type_error"
where
  "exec_d P t \<sigma> \<equiv> if check P \<sigma> then Normal (exec P t \<sigma>) else TypeError"

inductive
  exec_1_d :: "jvm_prog \<Rightarrow> thread_id \<Rightarrow> 'heap jvm_state type_error \<Rightarrow> 'heap jvm_thread_action \<Rightarrow> 'heap jvm_state type_error \<Rightarrow> bool" 
       ("_,_ \<turnstile> _ -_-jvmd\<rightarrow> _" [61,0,61,0,61] 60)
  for P :: jvm_prog and t :: thread_id
where
  exec_1_d_ErrorI: "exec_d P t \<sigma> = TypeError \<Longrightarrow> P,t \<turnstile> Normal \<sigma> -\<epsilon>-jvmd\<rightarrow> TypeError"
| exec_1_d_NormalI: "\<lbrakk> exec_d P t \<sigma> = Normal \<Sigma>; (tas, \<sigma>') \<in> \<Sigma> \<rbrakk>  \<Longrightarrow> P,t \<turnstile> Normal \<sigma> -tas-jvmd\<rightarrow> Normal \<sigma>'"

lemma jvmd_NormalD:
  "P,t \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>' \<Longrightarrow> check P \<sigma> \<and> (ta, \<sigma>') \<in> exec P t \<sigma> \<and> (\<exists>xcp h f frs. \<sigma> = (xcp, h, f # frs))"
apply(erule exec_1_d.cases, auto simp add: exec_d_def split: split_if_asm)
apply(case_tac b, auto)
done

lemma jvmd_NormalE:
  assumes "P,t \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'"
  obtains xcp h f frs where "check P \<sigma>" "(ta, \<sigma>') \<in> exec P t \<sigma>" "\<sigma> = (xcp, h, f # frs)"
using assms
by(auto dest: jvmd_NormalD)

lemma exec_d_eq_TypeError: "exec_d P t \<sigma> = TypeError \<longleftrightarrow> \<not> check P \<sigma>"
by(simp add: exec_d_def)

lemma exec_d_eq_Normal: "exec_d P t \<sigma> = Normal (exec P t \<sigma>) \<longleftrightarrow> check P \<sigma>"
by(auto simp add: exec_d_def)

end

declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

lemma if_neq [dest!]:
  "(if P then A else B) \<noteq> B \<Longrightarrow> P"
  by (cases P, auto)

context JVM_heap_base begin

lemma exec_d_no_errorI [intro]:
  "check P \<sigma> \<Longrightarrow> exec_d P t \<sigma> \<noteq> TypeError"
  by (unfold exec_d_def) simp

theorem no_type_error_commutes:
  "exec_d P t \<sigma> \<noteq> TypeError \<Longrightarrow> exec_d P t \<sigma> = Normal (exec P t \<sigma>)"
  by (unfold exec_d_def, auto)

lemma defensive_imp_aggressive_1:
  "P,t \<turnstile> (Normal \<sigma>) -tas-jvmd\<rightarrow> (Normal \<sigma>') \<Longrightarrow> P,t \<turnstile> \<sigma> -tas-jvm\<rightarrow> \<sigma>'"
by(auto elim!: exec_1_d.cases intro!: exec_1.intros simp add: exec_d_def split: split_if_asm)

end

context JVM_heap begin

lemma check_exec_hext:
  assumes exec: "(ta, xcp', h', frs') \<in> exec P t (xcp, h, frs)"
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
    have xexec: "(ta, xcp', h', frs') \<in> exec_instr (ins ! pc) P t h stk loc C0 M0 pc Frs" by(clarsimp)
    thus ?thesis
    proof(cases "ins ! pc")
      case (New C)
      obtain h' ao where "new_obj h C = (h', ao)" by(cases "new_obj h C")
      with xexec New show ?thesis by(auto simp add: split_beta intro: hext_new_obj)
    next
      case (NewArray T)
      obtain h' ao where "new_arr h T (nat (sint (the_Intg (hd stk)))) = (h', ao)"
        by(cases "new_arr h T (nat (sint (the_Intg (hd stk))))")
      with xexec NewArray show ?thesis
        by(auto intro: hext_new_arr split: split_if_asm)
    next
      case AStore
      with xexec check_ins show ?thesis
	by(auto simp add: split_beta split: split_if_asm intro: hext_heap_write)
    next
      case Putfield
      with xexec check_ins show ?thesis
	by(auto intro: hext_heap_write simp add: split_beta split: split_if_asm)
    next
      case (Invoke M n)
      with xexec check_ins show ?thesis
        apply(auto simp add: min_def split_beta is_Ref_def extRet2JVM_def
                split: split_if_asm intro: red_external_aggr_hext)
        apply(case_tac va)
        apply(auto intro: red_external_aggr_hext)
        done
    qed(auto simp add: split_beta split: split_if_asm)
  next
    case (Some a)
    with exec have "h' = h" by auto
    thus ?thesis by auto
  qed
qed

lemma exec_1_d_hext:
  "\<lbrakk> P,t \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs') \<rbrakk> \<Longrightarrow> h \<unlhd> h'"
by(auto elim!: exec_1_d.cases simp add: exec_d_def split: split_if_asm intro: check_exec_hext)

end

end
