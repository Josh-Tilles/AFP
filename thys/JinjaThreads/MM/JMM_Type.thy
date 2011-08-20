(*  Title:      JinjaThreads/MM/JMM_Type.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Heap implementation for the JMM} *}

theory JMM_Type imports 
  "../Common/ExternalCallWF"
  "../Common/ConformThreaded"
  "JMM_Heap"
begin

section {* Definitions *}

text {*
  The JMM heap only stores type information.
*}

type_synonym 'addr JMM_heap = "'addr \<rightharpoonup> htype"

translations (type) "'addr JMM_heap" <= (type) "'addr \<Rightarrow> htype option"

definition new_Addr :: "('addr \<rightharpoonup> 'b) \<Rightarrow> 'addr option"
where "new_Addr h \<equiv> if \<exists>a. h a = None then Some(SOME a. h a = None) else None"

lemma new_Addr_SomeD:
  "new_Addr h = Some a \<Longrightarrow> h a = None"
by(auto simp add:new_Addr_def split:if_splits intro: someI)

abbreviation jmm_empty :: "'addr JMM_heap" where "jmm_empty == Map.empty"

definition jmm_new_obj :: "'addr JMM_heap \<Rightarrow> cname \<Rightarrow> 'addr JMM_heap \<times> 'addr option"
where "jmm_new_obj h C = (case new_Addr h of None \<Rightarrow> (h, None) | Some a \<Rightarrow> (h(a \<mapsto> Class_type C), Some a))"

definition jmm_new_arr :: "'addr JMM_heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> 'addr JMM_heap \<times> 'addr option"
where "jmm_new_arr h T n = (case new_Addr h of None \<Rightarrow> (h, None) | Some a \<Rightarrow> (h(a \<mapsto> Array_type T n), Some a))"

definition jmm_typeof_addr :: "'addr JMM_heap \<Rightarrow> 'addr \<rightharpoonup> ty"
where "jmm_typeof_addr h a = Option.map ty_of_htype (h a)"

definition jmm_array_length :: "'addr JMM_heap \<Rightarrow> 'addr \<Rightarrow> nat"
where "jmm_array_length h a = alen_of_htype (the (h a))"

definition jmm_heap_read :: "'addr JMM_heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
where "jmm_heap_read h a ad v = True"

inductive jmm_heap_write :: "'addr JMM_heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'addr JMM_heap \<Rightarrow> bool"
where "jmm_heap_write h a ad v h"

definition jmm_hconf :: "'m prog \<Rightarrow> 'addr JMM_heap \<Rightarrow> bool" ("_ \<turnstile>jmm _ \<surd>" [51,51] 50)
where "P \<turnstile>jmm h \<surd> \<longleftrightarrow> ty_of_htype ` ran h \<subseteq> {T. is_type P T}"

definition jmm_allocated :: "'addr JMM_heap \<Rightarrow> 'addr set"
where "jmm_allocated h = dom (jmm_typeof_addr h)"

lemmas jmm_heap_ops_defs =
  jmm_new_obj_def jmm_new_arr_def jmm_typeof_addr_def 
  jmm_array_length_def jmm_heap_read_def jmm_heap_write_def
  jmm_allocated_def

type_synonym 'addr thread_id = "'addr"

abbreviation (input) addr2thread_id :: "'addr \<Rightarrow> 'addr thread_id"
where "addr2thread_id \<equiv> \<lambda>x. x"

abbreviation (input) thread_id2addr :: "'addr thread_id \<Rightarrow> 'addr"
where "thread_id2addr \<equiv> \<lambda>x. x"

interpretation jmm!: heap_base
  addr2thread_id thread_id2addr
  jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length jmm_heap_read jmm_heap_write 
.

notation jmm.hext  ("_ \<unlhd>jmm _" [51,51] 50)
notation jmm.conf ("_,_ \<turnstile>jmm _ :\<le> _"  [51,51,51,51] 50)
notation jmm.addr_loc_type ("_,_ \<turnstile>jmm _@_ : _" [50, 50, 50, 50, 50] 51)
notation jmm.confs ("_,_ \<turnstile>jmm _ [:\<le>] _"  [51,51,51,51] 50)
notation jmm.tconf ("_,_ \<turnstile>jmm _ \<surd>t" [51,51,51] 50)

text {* Now a variation of the JMM with a different read operation that permits to read only type-conformant values *}

interpretation jmm'!: heap_base
  addr2thread_id thread_id2addr
  jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length "jmm.heap_read_typed P" jmm_heap_write
  for P .

notation jmm'.hext ("_ \<unlhd>jmm' _" [51,51] 50)
notation jmm'.conf ("_,_ \<turnstile>jmm' _ :\<le> _"  [51,51,51,51] 50)
notation jmm'.addr_loc_type ("_,_ \<turnstile>jmm' _@_ : _" [50, 50, 50, 50, 50] 51)
notation jmm'.confs ("_,_ \<turnstile>jmm' _ [:\<le>] _"  [51,51,51,51] 50)
notation jmm'.tconf ("_,_ \<turnstile>jmm' _ \<surd>t" [51,51,51] 50)

section {* Heap locale interpretations *}

subsection {* Locale @{text heap} *}

lemma jmm_heap: "heap addr2thread_id thread_id2addr jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length jmm_heap_write P"
proof
  fix h C h' a
  assume "jmm_new_obj h C = (h', \<lfloor>a\<rfloor>)"
  thus "jmm_typeof_addr h' a = \<lfloor>Class C\<rfloor>"
    by(auto simp add: jmm_heap_ops_defs dest: new_Addr_SomeD)
next
  fix h C and h' :: "('addr :: addr) JMM_heap" and a
  assume "jmm_new_obj h C = (h', a)"
  thus "h \<unlhd>jmm h'"
    by(fastsimp simp add: jmm_heap_ops_defs intro: jmm.hextI dest: new_Addr_SomeD[OF sym])
next
  fix h T n h' a
  assume "jmm_new_arr h T n = (h', \<lfloor>a\<rfloor>)"
  thus "jmm_typeof_addr h' a = \<lfloor>T\<lfloor>\<rceil>\<rfloor> \<and> jmm_array_length h' a = n"
    by(auto simp add: jmm_heap_ops_defs dest: new_Addr_SomeD)
next
  fix h T n and h' :: "('addr :: addr) JMM_heap" and a
  assume "jmm_new_arr h T n = (h', a)"
  thus "h \<unlhd>jmm h'"
    by(fastsimp simp add: jmm_heap_ops_defs intro: jmm.hextI dest: new_Addr_SomeD[OF sym])
next
  fix h
  show "ran (jmm_typeof_addr h) \<subseteq> range Class \<union> range Array" using range_ty_of_htype
    by(auto simp add: jmm_heap_ops_defs ran_def)
next
  fix h a al v and h' :: "('addr :: addr) JMM_heap"
  assume "jmm_heap_write h a al v h'"
  thus "h \<unlhd>jmm h'" by cases auto
qed simp

interpretation jmm!: heap
  addr2thread_id thread_id2addr
  jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length jmm_heap_read jmm_heap_write
  P
  for P
by(rule jmm_heap)

declare jmm.typeof_addr_thread_id2_addr_addr2thread_id [simp del]

lemmas jmm'_heap = jmm_heap

interpretation jmm'!: heap
  addr2thread_id thread_id2addr
  jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length "jmm.heap_read_typed P" jmm_heap_write
  P
  for P
by(rule jmm'_heap)

declare jmm'.typeof_addr_thread_id2_addr_addr2thread_id [simp del]

subsection {* Locale @{text "heap_conf"} *}

interpretation jmm!: heap_conf_base
  addr2thread_id thread_id2addr
  jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length jmm_heap_read jmm_heap_write "jmm_hconf P"
  P
  for P .

abbreviation (input) jmm'_hconf :: "'m prog \<Rightarrow> 'addr JMM_heap \<Rightarrow> bool" ("_ \<turnstile>jmm' _ \<surd>" [51,51] 50)
where "jmm'_hconf == jmm_hconf"

interpretation jmm'!: heap_conf_base
  addr2thread_id thread_id2addr
  jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length "jmm.heap_read_typed P" jmm_heap_write "jmm'_hconf P"
  P
  for P .

abbreviation jmm_heap_read_typeable :: "('addr :: addr) itself \<Rightarrow> 'm prog \<Rightarrow> bool"
where "jmm_heap_read_typeable tytok P \<equiv> jmm.heap_read_typeable tytok TYPE('m) P"

abbreviation jmm'_heap_read_typeable :: "('addr :: addr) itself \<Rightarrow> 'm prog \<Rightarrow> bool"
where "jmm'_heap_read_typeable tytok P \<equiv> jmm'.heap_read_typeable tytok TYPE('m) P"

lemma jmm_heap_read_typeable: "jmm_heap_read_typeable tytok P"
by(rule jmm.heap_read_typeableI)(simp add: jmm_heap_read_def)

lemma jmm'_heap_read_typeable: "jmm'_heap_read_typeable tytok P"
by(rule jmm'.heap_read_typeableI)(auto simp add: jmm.heap_read_typed_def jmm_heap_read_def dest: jmm'.addr_loc_type_fun)

lemma jmm_heap_conf:
  "heap_conf addr2thread_id thread_id2addr jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length jmm_heap_write (jmm_hconf P) P"
proof
  show "P \<turnstile>jmm jmm_empty \<surd>"
    by(simp add: jmm_hconf_def)
next
  fix h a T
  assume "jmm_typeof_addr h a = \<lfloor>T\<rfloor>" "P \<turnstile>jmm h \<surd>"
  thus "is_type P T" by(auto simp add: jmm_hconf_def jmm_heap_ops_defs intro: ranI)
next
  fix h C h' a
  assume "jmm_new_obj h C = (h', a)" "P \<turnstile>jmm h \<surd>" "is_class P C"
  thus "P \<turnstile>jmm h' \<surd>"
    by(fastsimp simp add: jmm_hconf_def jmm_heap_ops_defs ran_def split: split_if_asm)
next
  fix h T n h' a
  assume "jmm_new_arr h T n = (h', a)" "P \<turnstile>jmm h \<surd>" "is_type P (T\<lfloor>\<rceil>)"
  thus "P \<turnstile>jmm h' \<surd>"
    by(fastsimp simp add: jmm_hconf_def jmm_heap_ops_defs ran_def split: split_if_asm)
next
  fix h a al v h' T
  assume "jmm_heap_write h a al v h'" "P \<turnstile>jmm h \<surd>"
    and "jmm.addr_loc_type P h a al T" and "P,h \<turnstile>jmm v :\<le> T"
  thus "P \<turnstile>jmm h' \<surd>" by(cases) simp
qed

interpretation jmm!: heap_conf
  addr2thread_id thread_id2addr
  jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length jmm_heap_read jmm_heap_write "jmm_hconf P"
  P
  for P
by(rule jmm_heap_conf)

lemmas jmm'_heap_conf = jmm_heap_conf

interpretation jmm'!: heap_conf
  addr2thread_id thread_id2addr
  jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length "jmm.heap_read_typed P" jmm_heap_write "jmm'_hconf P"
  P
  for P
by(rule jmm'_heap_conf)

subsection {* Locale @{text heap_progress} *}

lemma jmm_heap_progress:
  "heap_progress addr2thread_id thread_id2addr jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length jmm_heap_read jmm_heap_write (jmm_hconf P) P"
proof
  fix h a al T
  assume "P \<turnstile>jmm h \<surd>"
    and al: "jmm.addr_loc_type P h a al T"
  show "\<exists>v. jmm_heap_read h a al v \<and> P,h \<turnstile>jmm v :\<le> T"
    using jmm.defval_conf[of P h T] unfolding jmm_heap_ops_defs by blast
next
  fix h a al T v
  assume "jmm.addr_loc_type P h a al T"
  show "\<exists>h'. jmm_heap_write h a al v h'"
    by(auto intro: jmm_heap_write.intros)
qed

interpretation jmm!: heap_progress
  addr2thread_id thread_id2addr
  jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length jmm_heap_read jmm_heap_write "jmm_hconf P"
  P
  for P
by(rule jmm_heap_progress)

lemma jmm'_heap_progress:
  "heap_progress addr2thread_id thread_id2addr jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length (jmm.heap_read_typed P) jmm_heap_write (jmm'_hconf P) P"
proof
  fix h a al T
  assume "P \<turnstile>jmm' h \<surd>"
    and al: "jmm'.addr_loc_type P h a al T"
  thus "\<exists>v. jmm.heap_read_typed P h a al v \<and> P,h \<turnstile>jmm' v :\<le> T"
    unfolding jmm.heap_read_typed_def jmm_heap_read_def
    by(auto dest: jmm'.addr_loc_type_fun intro: jmm'.defval_conf)
next
  fix h a al T v
  assume "jmm'.addr_loc_type P h a al T"
    and "P,h \<turnstile>jmm' v :\<le> T"
  thus "\<exists>h'. jmm_heap_write h a al v h'"
    by(auto intro: jmm_heap_write.intros)
qed

interpretation jmm'!: heap_progress
  addr2thread_id thread_id2addr
  jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length "jmm.heap_read_typed P" jmm_heap_write "jmm'_hconf P"
  P
  for P
by(rule jmm'_heap_progress)

subsection {* Locale @{text heap_conf_read} *}

lemma jmm'_heap_conf_read:
  "heap_conf_read addr2thread_id thread_id2addr jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length (jmm.heap_read_typed P) jmm_heap_write (jmm'_hconf P) P"
by(rule jmm.heap_conf_read_heap_read_typed)

interpretation jmm'!: heap_conf_read
  addr2thread_id thread_id2addr
  jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length "jmm.heap_read_typed P" jmm_heap_write "jmm'_hconf P"
  P
  for P
by(rule jmm'_heap_conf_read)

interpretation jmm'!: heap_typesafe
  addr2thread_id thread_id2addr
  jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length "jmm.heap_read_typed P" jmm_heap_write "jmm'_hconf P"
  P
  for P
..

subsection {* Locale @{text allocated_heap} *}

lemma jmm_allocated_heap: 
  "allocated_heap addr2thread_id thread_id2addr jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length jmm_heap_write jmm_allocated P"
proof
  show "jmm_allocated jmm_empty = {}" by(auto simp add: jmm_heap_ops_defs)
next
  fix h C h' a
  assume "jmm_new_obj h C = (h', \<lfloor>a\<rfloor>)"
  thus "jmm_allocated h' = insert a (jmm_allocated h) \<and> a \<notin> jmm_allocated h"
    by(auto simp add: jmm_heap_ops_defs split: split_if_asm dest: new_Addr_SomeD)
next
  fix h C h'
  assume "jmm_new_obj h C = (h', None)"
  thus "jmm_allocated h' = jmm_allocated h"
    by(auto simp add: jmm_heap_ops_defs)
next
  fix h T n h' a
  assume "jmm_new_arr h T n = (h', \<lfloor>a\<rfloor>)"
  thus "jmm_allocated h' = insert a (jmm_allocated h) \<and> a \<notin> jmm_allocated h"
    by(auto simp add: jmm_heap_ops_defs split: split_if_asm dest: new_Addr_SomeD)
next
  fix h T n h'
  assume "jmm_new_arr h T n = (h', None)"
  thus "jmm_allocated h' = jmm_allocated h"
    by(auto simp add: jmm_heap_ops_defs)
next
  fix h a al v h'
  assume "jmm_heap_write h a al v h'"
  thus "jmm_allocated h' = jmm_allocated h" by cases simp
qed

interpretation jmm!: allocated_heap
  addr2thread_id thread_id2addr
  jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length jmm_heap_read jmm_heap_write
  jmm_allocated
  P
  for P
by(rule jmm_allocated_heap)

lemmas jmm'_allocated_heap = jmm_allocated_heap

interpretation jmm'!: allocated_heap
  addr2thread_id thread_id2addr
  jmm_empty jmm_new_obj jmm_new_arr jmm_typeof_addr jmm_array_length "jmm.heap_read_typed P" jmm_heap_write
  jmm_allocated
  P
  for P
by(rule jmm'_allocated_heap)

subsection {* Syntax translations *}

notation jmm'.external_WT' ("_,_ \<turnstile>jmm' (_\<bullet>_'(_')) : _" [50,0,0,0,50] 60)

abbreviation jmm'_red_external :: 
  "'m prog \<Rightarrow> 'addr thread_id \<Rightarrow> 'addr JMM_heap \<Rightarrow> 'addr \<Rightarrow> mname \<Rightarrow> 'addr val list
  \<Rightarrow> ('addr :: addr, 'addr thread_id, 'addr JMM_heap) external_thread_action 
  \<Rightarrow> 'addr extCallRet \<Rightarrow> 'addr JMM_heap \<Rightarrow> bool"
where "jmm'_red_external P \<equiv> jmm'.red_external (TYPE('m)) P P"

abbreviation jmm'_red_external_syntax :: 
  "'m prog \<Rightarrow> 'addr thread_id \<Rightarrow> 'addr \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> 'addr JMM_heap
  \<Rightarrow> ('addr :: addr, 'addr thread_id, 'addr JMM_heap) external_thread_action 
  \<Rightarrow> 'addr extCallRet \<Rightarrow> 'addr JMM_heap \<Rightarrow> bool"
  ("_,_ \<turnstile>jmm' (\<langle>(_\<bullet>_'(_')),/_\<rangle>) -_\<rightarrow>ext (\<langle>(_),/(_)\<rangle>)" [50, 0, 0, 0, 0, 0, 0, 0, 0] 51)
where
  "P,t \<turnstile>jmm' \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<equiv> jmm'_red_external P t h a M vs ta va h'"

abbreviation jmm'_red_external_aggr :: 
  "'m prog \<Rightarrow> 'addr thread_id \<Rightarrow> 'addr \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> 'addr JMM_heap 
    \<Rightarrow> ('addr :: addr, 'addr thread_id, 'addr JMM_heap) external_thread_action \<times> 'addr extCallRet \<times> 'addr JMM_heap \<Rightarrow> bool"
where "jmm'_red_external_aggr P \<equiv> jmm'.red_external_aggr TYPE('m) P P"

abbreviation jmm'_heap_copy_loc :: 
  "'m prog \<Rightarrow> 'addr \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr JMM_heap
  \<Rightarrow> ('addr :: addr, 'addr thread_id) obs_event list \<Rightarrow> 'addr JMM_heap \<Rightarrow> bool"
where "jmm'_heap_copy_loc \<equiv> jmm'.heap_copy_loc TYPE('m)"

abbreviation jmm'_heap_copies :: 
  "'m prog \<Rightarrow> 'addr \<Rightarrow> 'addr \<Rightarrow> addr_loc list \<Rightarrow> 'addr JMM_heap
  \<Rightarrow> ('addr :: addr, 'addr thread_id) obs_event list \<Rightarrow> 'addr JMM_heap \<Rightarrow> bool"
where "jmm'_heap_copies \<equiv> jmm'.heap_copies TYPE('m)"

abbreviation jmm'_heap_clone ::
  "'m prog \<Rightarrow> 'addr JMM_heap \<Rightarrow> 'addr \<Rightarrow> 'addr JMM_heap
  \<Rightarrow> (('addr :: addr, 'addr thread_id) obs_event list \<times> 'addr) option \<Rightarrow> bool"
where "jmm'_heap_clone P \<equiv> jmm'.heap_clone TYPE('m) P P"

end