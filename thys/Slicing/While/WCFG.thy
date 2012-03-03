header {* \isaheader{CFG} *}

theory WCFG imports Com "../Basic/BasicDefs" begin

subsection{* CFG nodes *}

datatype w_node = Node nat ("'('_ _ '_')")
  | Entry ("'('_Entry'_')")
  | Exit ("'('_Exit'_')") 

fun label_incr :: "w_node \<Rightarrow> nat \<Rightarrow> w_node" ("_ \<oplus> _" 60)
where "(_ l _) \<oplus> i = (_ l + i _)"
  | "(_Entry_) \<oplus> i = (_Entry_)"
  | "(_Exit_) \<oplus> i  = (_Exit_)"


lemma Exit_label_incr [dest]: "(_Exit_) = n \<oplus> i \<Longrightarrow> n = (_Exit_)"
  by(cases n,auto)

lemma label_incr_Exit [dest]: "n \<oplus> i = (_Exit_) \<Longrightarrow> n = (_Exit_)"
  by(cases n,auto)

lemma Entry_label_incr [dest]: "(_Entry_) = n \<oplus> i \<Longrightarrow> n = (_Entry_)"
  by(cases n,auto)

lemma label_incr_Entry [dest]: "n \<oplus> i = (_Entry_) \<Longrightarrow> n = (_Entry_)"
  by(cases n,auto)

lemma label_incr_inj:
  "n \<oplus> c = n' \<oplus> c \<Longrightarrow> n = n'"
by(cases n)(cases n',auto)+

lemma label_incr_simp:"n \<oplus> i = m \<oplus> (i + j) \<Longrightarrow> n = m \<oplus> j"
by(cases n,auto,cases m,auto)

lemma label_incr_simp_rev:"m \<oplus> (j + i) = n \<oplus> i \<Longrightarrow> m \<oplus> j = n"
by(cases n,auto,cases m,auto)

lemma label_incr_start_Node_smaller:
  "(_ l _) = n \<oplus> i \<Longrightarrow> n = (_(l - i)_)"
by(cases n,auto)

lemma label_incr_ge:"(_ l _) = n \<oplus> i \<Longrightarrow> l \<ge> i"
by(cases n) auto

lemma label_incr_0 [dest]:
  "\<lbrakk>(_0_) = n \<oplus> i; i > 0\<rbrakk> \<Longrightarrow> False" 
by(cases n) auto

lemma label_incr_0_rev [dest]:
  "\<lbrakk>n \<oplus> i = (_0_); i > 0\<rbrakk> \<Longrightarrow> False" 
by(cases n) auto

subsection{* CFG edges *}

type_synonym w_edge = "(w_node \<times> state edge_kind \<times> w_node)"

inductive While_CFG :: "cmd \<Rightarrow> w_node \<Rightarrow> state edge_kind \<Rightarrow> w_node \<Rightarrow> bool"
  ("_ \<turnstile> _ -_\<rightarrow> _")
where

WCFG_Entry_Exit:
  "prog \<turnstile> (_Entry_) -(\<lambda>s. False)\<^isub>\<surd>\<rightarrow> (_Exit_)"

| WCFG_Entry:
  "prog \<turnstile> (_Entry_) -(\<lambda>s. True)\<^isub>\<surd>\<rightarrow> (_0_)"

| WCFG_Skip: 
  "Skip \<turnstile> (_0_) -\<Up>id\<rightarrow> (_Exit_)"

| WCFG_LAss: 
  "V:=e \<turnstile> (_0_) -\<Up>(\<lambda>s. s(V:=(interpret e s)))\<rightarrow> (_1_)"

| WCFG_LAssSkip:
  "V:=e \<turnstile> (_1_) -\<Up>id\<rightarrow> (_Exit_)"

| WCFG_SeqFirst:
  "\<lbrakk>c\<^isub>1 \<turnstile> n -et\<rightarrow> n'; n' \<noteq> (_Exit_)\<rbrakk> \<Longrightarrow> c\<^isub>1;;c\<^isub>2 \<turnstile> n -et\<rightarrow> n'"

| WCFG_SeqConnect: 
  "\<lbrakk>c\<^isub>1 \<turnstile> n -et\<rightarrow> (_Exit_); n \<noteq> (_Entry_)\<rbrakk> \<Longrightarrow> c\<^isub>1;;c\<^isub>2 \<turnstile> n -et\<rightarrow> (_0_) \<oplus> #:c\<^isub>1"

| WCFG_SeqSecond: 
  "\<lbrakk>c\<^isub>2 \<turnstile> n -et\<rightarrow> n'; n \<noteq> (_Entry_)\<rbrakk> \<Longrightarrow> c\<^isub>1;;c\<^isub>2 \<turnstile> n \<oplus> #:c\<^isub>1 -et\<rightarrow> n' \<oplus> #:c\<^isub>1"

| WCFG_CondTrue:
    "if (b) c\<^isub>1 else c\<^isub>2 \<turnstile> (_0_) -(\<lambda>s. interpret b s = Some true)\<^isub>\<surd>\<rightarrow> (_0_) \<oplus> 1"

| WCFG_CondFalse:
    "if (b) c\<^isub>1 else c\<^isub>2 \<turnstile> (_0_) -(\<lambda>s. interpret b s = Some false)\<^isub>\<surd>\<rightarrow> (_0_) \<oplus> (#:c\<^isub>1 + 1)"

| WCFG_CondThen:
  "\<lbrakk>c\<^isub>1 \<turnstile> n -et\<rightarrow> n'; n \<noteq> (_Entry_)\<rbrakk> \<Longrightarrow> if (b) c\<^isub>1 else c\<^isub>2 \<turnstile> n \<oplus> 1 -et\<rightarrow> n' \<oplus> 1"

| WCFG_CondElse:
  "\<lbrakk>c\<^isub>2 \<turnstile> n -et\<rightarrow> n'; n \<noteq> (_Entry_)\<rbrakk> 
  \<Longrightarrow> if (b) c\<^isub>1 else c\<^isub>2 \<turnstile> n \<oplus> (#:c\<^isub>1 + 1) -et\<rightarrow> n' \<oplus> (#:c\<^isub>1 + 1)"

| WCFG_WhileTrue:
    "while (b) c' \<turnstile> (_0_) -(\<lambda>s. interpret b s = Some true)\<^isub>\<surd>\<rightarrow> (_0_) \<oplus> 2"

| WCFG_WhileFalse:
    "while (b) c' \<turnstile> (_0_) -(\<lambda>s. interpret b s = Some false)\<^isub>\<surd>\<rightarrow> (_1_)"

| WCFG_WhileFalseSkip:
  "while (b) c' \<turnstile> (_1_) -\<Up>id\<rightarrow> (_Exit_)"

| WCFG_WhileBody:
  "\<lbrakk>c' \<turnstile> n -et\<rightarrow> n'; n \<noteq> (_Entry_); n' \<noteq> (_Exit_)\<rbrakk> 
  \<Longrightarrow> while (b) c' \<turnstile> n \<oplus> 2 -et\<rightarrow> n' \<oplus> 2"

| WCFG_WhileBodyExit:
  "\<lbrakk>c' \<turnstile> n -et\<rightarrow> (_Exit_); n \<noteq> (_Entry_)\<rbrakk> \<Longrightarrow> while (b) c' \<turnstile> n \<oplus> 2 -et\<rightarrow> (_0_)"

lemmas WCFG_intros = While_CFG.intros[split_format (complete)]
lemmas WCFG_elims = While_CFG.cases[split_format (complete)]
lemmas WCFG_induct = While_CFG.induct[split_format (complete)]


subsection {* Some lemmas about the CFG *}

lemma WCFG_Exit_no_sourcenode [dest]:
  "prog \<turnstile> (_Exit_) -et\<rightarrow> n' \<Longrightarrow> False"
by(induct prog n\<equiv>"(_Exit_)" et n' rule:WCFG_induct,auto)


lemma WCFG_Entry_no_targetnode [dest]:
  "prog \<turnstile> n -et\<rightarrow> (_Entry_) \<Longrightarrow> False"
by(induct prog n et n'\<equiv>"(_Entry_)" rule:WCFG_induct,auto)


lemma WCFG_sourcelabel_less_num_nodes:
  "prog \<turnstile> (_ l _) -et\<rightarrow> n' \<Longrightarrow> l < #:prog"
proof(induct prog "(_ l _)" et n' arbitrary:l rule:WCFG_induct)
  case (WCFG_SeqFirst c\<^isub>1 et n' c\<^isub>2)
  from `l < #:c\<^isub>1` show ?case by simp
next
  case (WCFG_SeqConnect c\<^isub>1 et c\<^isub>2)
  from `l < #:c\<^isub>1` show ?case by simp
next
  case (WCFG_SeqSecond c\<^isub>2 n et n' c\<^isub>1)
  note IH = `\<And>l. n = (_ l _) \<Longrightarrow> l < #:c\<^isub>2`
  from `n \<oplus> #:c\<^isub>1 = (_ l _)` obtain l' where "n = (_ l' _)" by(cases n) auto
  from IH[OF this] have "l' < #:c\<^isub>2" .
  with `n \<oplus> #:c\<^isub>1 = (_ l _)` `n = (_ l' _)` show ?case by simp
next
  case (WCFG_CondThen c\<^isub>1 n et n' b c\<^isub>2)
  note IH = `\<And>l. n = (_ l _) \<Longrightarrow> l < #:c\<^isub>1`
  from `n \<oplus> 1 = (_ l _)` obtain l' where "n = (_ l' _)" by(cases n) auto
  from IH[OF this] have "l' < #:c\<^isub>1" .
  with `n \<oplus> 1 = (_ l _)` `n = (_ l' _)` show ?case by simp
next
  case (WCFG_CondElse c\<^isub>2 n et n' b c\<^isub>1)
  note IH = `\<And>l. n = (_ l _) \<Longrightarrow> l < #:c\<^isub>2`
  from `n \<oplus> (#:c\<^isub>1 + 1) = (_ l _)` obtain l' where "n = (_ l' _)" by(cases n) auto
  from IH[OF this] have "l' < #:c\<^isub>2" .
  with `n \<oplus> (#:c\<^isub>1 + 1) = (_ l _)` `n = (_ l' _)` show ?case by simp
next
  case (WCFG_WhileBody c' n et n' b)
  note IH = `\<And>l. n = (_ l _) \<Longrightarrow> l < #:c'`
  from `n \<oplus> 2 = (_ l _)` obtain l' where "n = (_ l' _)" by(cases n) auto
  from IH[OF this] have "l' < #:c'" .
  with `n \<oplus> 2 = (_ l _)` `n = (_ l' _)` show ?case by simp
next
  case (WCFG_WhileBodyExit c' n et b)
  note IH = `\<And>l. n = (_ l _) \<Longrightarrow> l < #:c'`
  from `n \<oplus> 2 = (_ l _)` obtain l' where "n = (_ l' _)" by(cases n) auto
  from IH[OF this] have "l' < #:c'" .
  with `n \<oplus> 2 = (_ l _)` `n = (_ l' _)` show ?case by simp
qed (auto simp:num_inner_nodes_gr_0)


lemma WCFG_targetlabel_less_num_nodes:
  "prog \<turnstile> n -et\<rightarrow> (_ l _) \<Longrightarrow> l < #:prog"
proof(induct prog n et "(_ l _)" arbitrary:l rule:WCFG_induct)
  case (WCFG_SeqFirst c\<^isub>1 n et c\<^isub>2)
  from `l < #:c\<^isub>1` show ?case by simp
next
  case (WCFG_SeqSecond c\<^isub>2 n et n' c\<^isub>1)
  note IH = `\<And>l. n' = (_ l _) \<Longrightarrow> l < #:c\<^isub>2`
  from `n' \<oplus> #:c\<^isub>1 = (_ l _)` obtain l' where "n' = (_ l' _)" by(cases n') auto
  from IH[OF this] have "l' < #:c\<^isub>2" .
  with `n' \<oplus> #:c\<^isub>1 = (_ l _)` `n' = (_ l' _)` show ?case by simp
next
  case (WCFG_CondThen c\<^isub>1 n et n' b c\<^isub>2)
  note IH = `\<And>l. n' = (_ l _) \<Longrightarrow> l < #:c\<^isub>1`
  from `n' \<oplus> 1 = (_ l _)` obtain l' where "n' = (_ l' _)" by(cases n') auto
  from IH[OF this] have "l' < #:c\<^isub>1" .
  with `n' \<oplus> 1 = (_ l _)` `n' = (_ l' _)` show ?case by simp
next
  case (WCFG_CondElse c\<^isub>2 n et n' b c\<^isub>1)
  note IH = `\<And>l. n' = (_ l _) \<Longrightarrow> l < #:c\<^isub>2`
  from `n' \<oplus> (#:c\<^isub>1 + 1) = (_ l _)` obtain l' where "n' = (_ l' _)" by(cases n') auto
  from IH[OF this] have "l' < #:c\<^isub>2" .
  with `n' \<oplus> (#:c\<^isub>1 + 1) = (_ l _)` `n' = (_ l' _)` show ?case by simp
next
  case (WCFG_WhileBody c' n et n' b)
  note IH = `\<And>l. n' = (_ l _) \<Longrightarrow> l < #:c'`
  from `n' \<oplus> 2 = (_ l _)` obtain l' where "n' = (_ l' _)" by(cases n') auto
  from IH[OF this] have "l' < #:c'" .
  with `n' \<oplus> 2 = (_ l _)` `n' = (_ l' _)` show ?case by simp
qed (auto simp:num_inner_nodes_gr_0)


lemma WCFG_EntryD:
  "prog \<turnstile> (_Entry_) -et\<rightarrow> n'
  \<Longrightarrow> (n' = (_Exit_) \<and> et = (\<lambda>s. False)\<^isub>\<surd>) \<or> (n' = (_0_) \<and> et = (\<lambda>s. True)\<^isub>\<surd>)"
by(induct prog n\<equiv>"(_Entry_)" et n' rule:WCFG_induct,auto)


(*<*)declare One_nat_def [simp del] add_2_eq_Suc' [simp del](*>*)

lemma WCFG_edge_det:
  "\<lbrakk>prog \<turnstile> n -et\<rightarrow> n'; prog \<turnstile> n -et'\<rightarrow> n'\<rbrakk> \<Longrightarrow> et = et'"
proof(induct rule:WCFG_induct)
  case WCFG_Entry_Exit thus ?case by(fastforce dest:WCFG_EntryD)
next
  case WCFG_Entry thus ?case by(fastforce dest:WCFG_EntryD)
next
  case WCFG_Skip thus ?case by(fastforce elim:WCFG_elims)
next
  case WCFG_LAss thus ?case by(fastforce elim:WCFG_elims)
next
  case WCFG_LAssSkip thus ?case by(fastforce elim:WCFG_elims)
next
  case (WCFG_SeqFirst c\<^isub>1 n et n' c\<^isub>2)
  note IH = `c\<^isub>1 \<turnstile> n -et'\<rightarrow> n' \<Longrightarrow> et = et'`
  from `c\<^isub>1 \<turnstile> n -et\<rightarrow> n'` `n' \<noteq> (_Exit_)` obtain l where "n' = (_ l _)"
    by (cases n') auto
  with `c\<^isub>1 \<turnstile> n -et\<rightarrow> n'` have "l < #:c\<^isub>1" 
    by(fastforce intro:WCFG_targetlabel_less_num_nodes)
  with `c\<^isub>1;;c\<^isub>2 \<turnstile> n -et'\<rightarrow> n'` `n' = (_ l _)` have "c\<^isub>1 \<turnstile> n -et'\<rightarrow> n'"
    by(fastforce elim:WCFG_elims intro:WCFG_intros dest:label_incr_ge)
  from IH[OF this] show ?case .
next
  case (WCFG_SeqConnect c\<^isub>1 n et c\<^isub>2)
  note IH = `c\<^isub>1 \<turnstile> n -et'\<rightarrow> (_Exit_) \<Longrightarrow> et = et'`
  from `c\<^isub>1 \<turnstile> n -et\<rightarrow> (_Exit_)` `n \<noteq> (_Entry_)` obtain l where "n = (_ l _)"
    by (cases n) auto
  with `c\<^isub>1 \<turnstile> n -et\<rightarrow> (_Exit_)` have "l < #:c\<^isub>1"
    by(fastforce intro:WCFG_sourcelabel_less_num_nodes)
  with `c\<^isub>1;;c\<^isub>2 \<turnstile> n -et'\<rightarrow> (_ 0 _) \<oplus> #:c\<^isub>1` `n = (_ l _)` have "c\<^isub>1 \<turnstile> n -et'\<rightarrow> (_Exit_)"
    by(fastforce elim:WCFG_elims dest:WCFG_targetlabel_less_num_nodes label_incr_ge)
  from IH[OF this] show ?case .
next
  case (WCFG_SeqSecond c\<^isub>2 n et n' c\<^isub>1)
  note IH = `c\<^isub>2 \<turnstile> n -et'\<rightarrow> n' \<Longrightarrow> et = et'`
  from `c\<^isub>2 \<turnstile> n -et\<rightarrow> n'` `n \<noteq> (_Entry_)` obtain l where "n = (_ l _)"
    by (cases n) auto
  with `c\<^isub>2 \<turnstile> n -et\<rightarrow> n'` have "l < #:c\<^isub>2"
    by(fastforce intro:WCFG_sourcelabel_less_num_nodes)
  with `c\<^isub>1;;c\<^isub>2 \<turnstile> n \<oplus> #:c\<^isub>1 -et'\<rightarrow> n' \<oplus> #:c\<^isub>1` `n = (_ l _)` have "c\<^isub>2 \<turnstile> n -et'\<rightarrow> n'"
    by -(erule WCFG_elims,(fastforce dest:WCFG_sourcelabel_less_num_nodes label_incr_ge
                                    dest!:label_incr_inj)+)
  from IH[OF this] show ?case .
next
  case WCFG_CondTrue thus ?case by(fastforce elim:WCFG_elims)
next
  case WCFG_CondFalse thus ?case by(fastforce elim:WCFG_elims)
next
  case (WCFG_CondThen c\<^isub>1 n et n' b c\<^isub>2)
  note IH = `c\<^isub>1 \<turnstile> n -et'\<rightarrow> n' \<Longrightarrow> et = et'`
  from `c\<^isub>1 \<turnstile> n -et\<rightarrow> n'` `n \<noteq> (_Entry_)` obtain l where "n = (_ l _)"
    by (cases n) auto
  with `c\<^isub>1 \<turnstile> n -et\<rightarrow> n'` have "l < #:c\<^isub>1"
    by(fastforce intro:WCFG_sourcelabel_less_num_nodes)
  with `if (b) c\<^isub>1 else c\<^isub>2 \<turnstile> n \<oplus> 1 -et'\<rightarrow> n' \<oplus> 1` `n = (_ l _)`
  have "c\<^isub>1 \<turnstile> n -et'\<rightarrow> n'"
    by -(erule WCFG_elims,(fastforce dest:label_incr_ge label_incr_inj)+)
  from IH[OF this] show ?case .
next
  case (WCFG_CondElse c\<^isub>2 n et n' b c\<^isub>1)
  note IH = `c\<^isub>2 \<turnstile> n -et'\<rightarrow> n' \<Longrightarrow> et = et'`
  from `c\<^isub>2 \<turnstile> n -et\<rightarrow> n'` `n \<noteq> (_Entry_)` obtain l where "n = (_ l _)"
    by (cases n) auto
  with `c\<^isub>2 \<turnstile> n -et\<rightarrow> n'` have "l < #:c\<^isub>2"
    by(fastforce intro:WCFG_sourcelabel_less_num_nodes)
  with `if (b) c\<^isub>1 else c\<^isub>2 \<turnstile> n \<oplus> (#:c\<^isub>1 + 1) -et'\<rightarrow> n' \<oplus> (#:c\<^isub>1 + 1)` `n = (_ l _)`
  have "c\<^isub>2 \<turnstile> n -et'\<rightarrow> n'"
    by -(erule WCFG_elims,(fastforce dest:WCFG_sourcelabel_less_num_nodes 
                             label_incr_inj label_incr_ge label_incr_simp_rev)+)
  from IH[OF this] show ?case .
next
  case WCFG_WhileTrue thus ?case by(fastforce elim:WCFG_elims)
next
  case WCFG_WhileFalse thus ?case by(fastforce elim:WCFG_elims)
next
  case WCFG_WhileFalseSkip thus ?case by(fastforce elim:WCFG_elims)
next
  case (WCFG_WhileBody c' n et n' b)
  note IH = `c' \<turnstile> n -et'\<rightarrow> n' \<Longrightarrow> et = et'`
  from `c' \<turnstile> n -et\<rightarrow> n'` `n \<noteq> (_Entry_)` obtain l where "n = (_ l _)"
    by (cases n) auto
  moreover
  with `c' \<turnstile> n -et\<rightarrow> n'` have "l < #:c'"
    by(fastforce intro:WCFG_sourcelabel_less_num_nodes)
  moreover
  from `c' \<turnstile> n -et\<rightarrow> n'` `n' \<noteq> (_Exit_)` obtain l' where "n' = (_ l' _)"
    by (cases n') auto
  moreover
  with `c' \<turnstile> n -et\<rightarrow> n'` have "l' < #:c'"
    by(fastforce intro:WCFG_targetlabel_less_num_nodes)
  ultimately have "c' \<turnstile> n -et'\<rightarrow> n'" using `while (b) c' \<turnstile> n \<oplus> 2 -et'\<rightarrow> n' \<oplus> 2`
    by(fastforce elim:WCFG_elims dest:label_incr_start_Node_smaller)
  from IH[OF this] show ?case .
next
  case (WCFG_WhileBodyExit c' n et b)
  note IH = `c' \<turnstile> n -et'\<rightarrow> (_Exit_) \<Longrightarrow> et = et'`
  from `c' \<turnstile> n -et\<rightarrow> (_Exit_)` `n \<noteq> (_Entry_)` obtain l where "n = (_ l _)"
    by (cases n) auto
  with `c' \<turnstile> n -et\<rightarrow> (_Exit_)` have "l < #:c'"
    by(fastforce intro:WCFG_sourcelabel_less_num_nodes)
  with `while (b) c' \<turnstile> n \<oplus> 2 -et'\<rightarrow> (_0_)` `n = (_ l _)`
  have "c' \<turnstile> n -et'\<rightarrow> (_Exit_)"
    by -(erule WCFG_elims,auto dest:label_incr_start_Node_smaller)
  from IH[OF this] show ?case .
qed

(*<*)declare One_nat_def [simp] add_2_eq_Suc' [simp](*>*)

lemma less_num_nodes_edge_Exit:
  obtains l et where "l < #:prog" and "prog \<turnstile> (_ l _) -et\<rightarrow> (_Exit_)"
proof -
  have "\<exists>l et. l < #:prog \<and> prog \<turnstile> (_ l _) -et\<rightarrow> (_Exit_)"
  proof(induct prog)
    case Skip
    have "0 < #:Skip" by simp
    moreover have "Skip \<turnstile> (_0_) -\<Up>id\<rightarrow> (_Exit_)" by(rule WCFG_Skip)
    ultimately show ?case by blast
  next
    case (LAss V e)
    have "1 < #:(V:=e)" by simp
    moreover have "V:=e \<turnstile> (_1_) -\<Up>id\<rightarrow> (_Exit_)" by(rule WCFG_LAssSkip)
    ultimately show ?case by blast
  next
    case (Seq prog1 prog2)
    from `\<exists>l et. l < #:prog2 \<and> prog2 \<turnstile> (_ l _) -et\<rightarrow> (_Exit_)`
    obtain l et where "l < #:prog2" and "prog2 \<turnstile> (_ l _) -et\<rightarrow> (_Exit_)"
      by blast
    from `prog2 \<turnstile> (_ l _) -et\<rightarrow> (_Exit_)` 
    have "prog1;;prog2 \<turnstile> (_ l _) \<oplus> #:prog1 -et\<rightarrow> (_Exit_) \<oplus> #:prog1"
      by(fastforce intro:WCFG_SeqSecond)
    with `l < #:prog2` show ?case by(rule_tac x="l + #:prog1" in exI,auto)
  next
    case (Cond b prog1 prog2)
    from `\<exists>l et. l < #:prog1 \<and> prog1 \<turnstile> (_ l _) -et\<rightarrow> (_Exit_)`
    obtain l et where "l < #:prog1" and "prog1 \<turnstile> (_ l _) -et\<rightarrow> (_Exit_)"
      by blast
    from `prog1 \<turnstile> (_ l _) -et\<rightarrow> (_Exit_)`
    have "if (b) prog1 else prog2 \<turnstile> (_ l _) \<oplus> 1 -et\<rightarrow> (_Exit_) \<oplus> 1"
      by(fastforce intro:WCFG_CondThen)
    with `l < #:prog1` show ?case by(rule_tac x="l + 1" in exI,auto)
  next
    case (While b prog')
    have "1 < #:(while (b) prog')" by simp
    moreover have "while (b) prog' \<turnstile> (_1_) -\<Up>id\<rightarrow> (_Exit_)"
      by(rule WCFG_WhileFalseSkip)
    ultimately show ?case by blast
  qed
  with that show ?thesis by blast
qed


lemma less_num_nodes_edge:
  "l < #:prog \<Longrightarrow> \<exists>n et. prog \<turnstile> n -et\<rightarrow> (_ l _) \<or> prog \<turnstile> (_ l _) -et\<rightarrow> n"
proof(induct prog arbitrary:l)
  case Skip
  from `l < #:Skip` have "l = 0" by simp
  hence "Skip \<turnstile> (_ l _) -\<Up>id\<rightarrow> (_Exit_)" by(fastforce intro:WCFG_Skip)
  thus ?case by blast
next
  case (LAss V e)
  from `l < #:V:=e` have "l = 0 \<or> l = 1" by auto
  thus ?case
  proof
    assume "l = 0"
    hence "V:=e \<turnstile> (_Entry_) -(\<lambda>s. True)\<^isub>\<surd>\<rightarrow> (_ l _)" by(fastforce intro:WCFG_Entry)
    thus ?thesis by blast
  next
    assume "l = 1"
    hence "V:=e \<turnstile> (_ l _) -\<Up>id\<rightarrow> (_Exit_)" by(fastforce intro:WCFG_LAssSkip)
    thus ?thesis by blast
  qed
next
  case (Seq prog1 prog2)
  note IH1 = `\<And>l. l < #:prog1 \<Longrightarrow> 
              \<exists>n et. prog1 \<turnstile> n -et\<rightarrow> (_ l _) \<or> prog1 \<turnstile> (_ l _) -et\<rightarrow> n`
  note IH2 = `\<And>l. l < #:prog2 \<Longrightarrow> 
              \<exists>n et. prog2 \<turnstile> n -et\<rightarrow> (_ l _) \<or> prog2 \<turnstile> (_ l _) -et\<rightarrow> n`
  show ?case
  proof(cases "l < #:prog1")
    case True
    from IH1[OF this] obtain n et 
      where "prog1 \<turnstile> n -et\<rightarrow> (_ l _) \<or> prog1 \<turnstile> (_ l _) -et\<rightarrow> n" by blast
    thus ?thesis
    proof
      assume "prog1 \<turnstile> n -et\<rightarrow> (_ l _)"
      hence "prog1;; prog2 \<turnstile> n -et\<rightarrow> (_ l _)" by(fastforce intro:WCFG_SeqFirst)
      thus ?thesis by blast
    next
      assume edge:"prog1 \<turnstile> (_ l _) -et\<rightarrow> n"
      show ?thesis
      proof(cases "n = (_Exit_)")
        case True
        with edge have "prog1;; prog2 \<turnstile> (_ l _) -et\<rightarrow> (_0_) \<oplus> #:prog1"
          by(fastforce intro:WCFG_SeqConnect)
        thus ?thesis by blast
      next
        case False
        with edge have "prog1;; prog2 \<turnstile> (_ l _) -et\<rightarrow> n"
          by(fastforce intro:WCFG_SeqFirst)
        thus ?thesis by blast
      qed
    qed
  next
    case False
    hence "#:prog1 \<le> l" by simp
    then obtain l' where "l = l' + #:prog1" and "l' = l - #:prog1" by simp
    from `l = l' + #:prog1` `l < #:prog1;; prog2` have "l' < #:prog2" by simp
    from IH2[OF this] obtain n et
      where "prog2 \<turnstile> n -et\<rightarrow> (_ l' _) \<or> prog2 \<turnstile> (_ l' _) -et\<rightarrow> n" by blast
    thus ?thesis
    proof
      assume "prog2 \<turnstile> n -et\<rightarrow> (_ l' _)"
      show ?thesis
      proof(cases "n = (_Entry_)")
        case True
        with `prog2 \<turnstile> n -et\<rightarrow> (_ l' _)` have "l' = 0" by(auto dest:WCFG_EntryD)
        obtain l'' et'' where "l'' < #:prog1" 
          and "prog1 \<turnstile> (_ l'' _) -et''\<rightarrow> (_Exit_)"
          by(erule less_num_nodes_edge_Exit)
        hence "prog1;;prog2 \<turnstile> (_ l'' _) -et''\<rightarrow> (_0_) \<oplus> #:prog1"
          by(fastforce intro:WCFG_SeqConnect)
        with `l' = 0` `l = l' + #:prog1` show ?thesis by simp blast
      next
        case False
        with `prog2 \<turnstile> n -et\<rightarrow> (_ l' _)`
        have "prog1;;prog2 \<turnstile> n \<oplus> #:prog1 -et\<rightarrow> (_ l' _) \<oplus> #:prog1"
          by(fastforce intro:WCFG_SeqSecond)
        with `l = l' + #:prog1` show ?thesis  by simp blast
      qed
    next
      assume "prog2 \<turnstile> (_ l' _) -et\<rightarrow> n"
      hence "prog1;;prog2 \<turnstile> (_ l' _) \<oplus> #:prog1 -et\<rightarrow> n \<oplus> #:prog1"
        by(fastforce intro:WCFG_SeqSecond)
      with `l = l' + #:prog1` show ?thesis  by simp blast
    qed
  qed
next
  case (Cond b prog1 prog2)
  note IH1 = `\<And>l. l < #:prog1 \<Longrightarrow> 
              \<exists>n et. prog1 \<turnstile> n -et\<rightarrow> (_ l _) \<or> prog1 \<turnstile> (_ l _) -et\<rightarrow> n`
  note IH2 = `\<And>l. l < #:prog2 \<Longrightarrow> 
              \<exists>n et. prog2 \<turnstile> n -et\<rightarrow> (_ l _) \<or> prog2 \<turnstile> (_ l _) -et\<rightarrow> n`
  show ?case
  proof(cases "l = 0")
    case True
    have "if (b) prog1 else prog2 \<turnstile> (_Entry_) -(\<lambda>s. True)\<^isub>\<surd>\<rightarrow> (_0_)"
      by(rule WCFG_Entry)
    with True show ?thesis by simp blast
  next
    case False
    hence "0 < l" by simp
    then obtain l' where "l = l' + 1" and "l' = l - 1" by simp
    thus ?thesis
    proof(cases "l' < #:prog1")
      case True
      from IH1[OF this] obtain n et 
        where "prog1 \<turnstile> n -et\<rightarrow> (_ l' _) \<or> prog1 \<turnstile> (_ l' _) -et\<rightarrow> n" by blast
      thus ?thesis
      proof
        assume edge:"prog1 \<turnstile> n -et\<rightarrow> (_ l' _)"
        show ?thesis
        proof(cases "n = (_Entry_)")
          case True
          with edge have "l' = 0" by(auto dest:WCFG_EntryD)
          have "if (b) prog1 else prog2 \<turnstile> (_0_) -(\<lambda>s. interpret b s = Some true)\<^isub>\<surd>\<rightarrow> 
                                          (_0_) \<oplus> 1"
            by(rule WCFG_CondTrue)
          with `l' = 0` `l = l' + 1` show ?thesis by simp blast
        next
          case False
          with edge have "if (b) prog1 else prog2 \<turnstile> n \<oplus> 1 -et\<rightarrow> (_ l' _) \<oplus> 1"
            by(fastforce intro:WCFG_CondThen)
          with `l = l' + 1` show ?thesis by simp blast
        qed
      next
        assume "prog1 \<turnstile> (_ l' _) -et\<rightarrow> n"
        hence "if (b) prog1 else prog2 \<turnstile> (_ l' _) \<oplus> 1 -et\<rightarrow> n \<oplus> 1"
          by(fastforce intro:WCFG_CondThen)
        with `l = l' + 1` show ?thesis by simp blast
      qed
    next
      case False
      hence "#:prog1 \<le> l'" by simp
      then obtain l'' where "l' = l'' + #:prog1" and "l'' = l' - #:prog1"
        by simp
      from `l' = l'' + #:prog1` `l = l' + 1` `l < #:(if (b) prog1 else prog2)`
      have "l'' < #:prog2" by simp
      from IH2[OF this] obtain n et 
        where "prog2 \<turnstile> n -et\<rightarrow> (_ l'' _) \<or> prog2 \<turnstile> (_ l'' _) -et\<rightarrow> n" by blast
      thus ?thesis
      proof
        assume "prog2 \<turnstile> n -et\<rightarrow> (_ l'' _)"
        show ?thesis
        proof(cases "n = (_Entry_)")
          case True
          with `prog2 \<turnstile> n -et\<rightarrow> (_ l'' _)` have "l'' = 0" by(auto dest:WCFG_EntryD)
          have "if (b) prog1 else prog2 \<turnstile> (_0_) -(\<lambda>s. interpret b s = Some false)\<^isub>\<surd>\<rightarrow> 
                                          (_0_) \<oplus> (#:prog1 + 1)"
            by(rule WCFG_CondFalse)
          with `l'' = 0` `l' = l'' + #:prog1` `l = l' + 1` show ?thesis by simp blast
        next
          case False
          with `prog2 \<turnstile> n -et\<rightarrow> (_ l'' _)`
          have "if (b) prog1 else prog2 \<turnstile> n \<oplus> (#:prog1 + 1) -et\<rightarrow> 
                                          (_ l'' _) \<oplus> (#:prog1 + 1)"
            by(fastforce intro:WCFG_CondElse)
          with `l = l' + 1` `l' = l'' + #:prog1` show ?thesis by simp blast
        qed
      next
        assume "prog2 \<turnstile> (_ l'' _) -et\<rightarrow> n"
        hence "if (b) prog1 else prog2 \<turnstile> (_ l'' _) \<oplus> (#:prog1 + 1) -et\<rightarrow> 
                                         n \<oplus> (#:prog1 + 1)"
          by(fastforce intro:WCFG_CondElse)
        with `l = l' + 1` `l' = l'' + #:prog1` show ?thesis by simp blast
      qed
    qed
  qed
next
  case (While b prog')
  note IH = `\<And>l. l < #:prog' 
             \<Longrightarrow> \<exists>n et. prog' \<turnstile> n -et\<rightarrow> (_ l _) \<or> prog' \<turnstile> (_ l _) -et\<rightarrow> n`
  show ?case
  proof(cases "l < 1")
    case True
    have "while (b) prog' \<turnstile> (_Entry_) -(\<lambda>s. True)\<^isub>\<surd>\<rightarrow> (_0_)" by(rule WCFG_Entry)
    with True show ?thesis by simp blast
  next
    case False
    hence "1 \<le> l" by simp
    thus ?thesis
    proof(cases "l < 2")
      case True
      with `1 \<le> l` have "l = 1" by simp
      have "while (b) prog' \<turnstile> (_0_) -(\<lambda>s. interpret b s = Some false)\<^isub>\<surd>\<rightarrow> (_1_)"
        by(rule WCFG_WhileFalse)
      with `l = 1` show ?thesis by simp blast
    next
      case False
      with `1 \<le> l` have "2 \<le> l" by simp
      then obtain l' where "l = l' + 2" and "l' = l - 2" 
        by(simp del:add_2_eq_Suc')
      from `l = l' + 2` `l < #:while (b) prog'` have "l' < #:prog'" by simp
      from IH[OF this] obtain n et 
        where "prog' \<turnstile> n -et\<rightarrow> (_ l' _) \<or> prog' \<turnstile> (_ l' _) -et\<rightarrow> n" by blast
      thus ?thesis
      proof
        assume "prog' \<turnstile> n -et\<rightarrow> (_ l' _)"
        show ?thesis
        proof(cases "n = (_Entry_)")
          case True
          with `prog' \<turnstile> n -et\<rightarrow> (_ l' _)` have "l' = 0" by(auto dest:WCFG_EntryD)
          have "while (b) prog' \<turnstile> (_0_) -(\<lambda>s. interpret b s = Some true)\<^isub>\<surd>\<rightarrow> 
                                  (_0_) \<oplus> 2"
            by(rule WCFG_WhileTrue)
          with `l' = 0` `l = l' + 2` show ?thesis by simp blast
        next
          case False
          with `prog' \<turnstile> n -et\<rightarrow> (_ l' _)`
          have "while (b) prog' \<turnstile> n \<oplus> 2 -et\<rightarrow> (_ l' _) \<oplus> 2"
            by(fastforce intro:WCFG_WhileBody)
          with `l = l' + 2` show ?thesis by simp blast
        qed
      next
        assume "prog' \<turnstile> (_ l' _) -et\<rightarrow> n"
        show ?thesis
        proof(cases "n = (_Exit_)")
          case True
          with `prog' \<turnstile> (_ l' _) -et\<rightarrow> n`
          have "while (b) prog' \<turnstile> (_ l' _) \<oplus> 2 -et\<rightarrow> (_0_)"
            by(fastforce intro:WCFG_WhileBodyExit)
          with `l = l' + 2` show ?thesis by simp blast
        next
          case False
          with `prog' \<turnstile> (_ l' _) -et\<rightarrow> n`
          have "while (b) prog' \<turnstile> (_ l' _) \<oplus> 2 -et\<rightarrow> n \<oplus> 2"
            by(fastforce intro:WCFG_WhileBody)
          with `l = l' + 2` show ?thesis by simp blast
        qed
      qed
    qed
  qed
qed


(*<*)declare One_nat_def [simp del](*>*)

lemma WCFG_deterministic:
  "\<lbrakk>prog \<turnstile> n\<^isub>1 -et\<^isub>1\<rightarrow> n\<^isub>1'; prog \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'; n\<^isub>1 = n\<^isub>2; n\<^isub>1' \<noteq> n\<^isub>2'\<rbrakk>
  \<Longrightarrow> \<exists>Q Q'. et\<^isub>1 = (Q)\<^isub>\<surd> \<and> et\<^isub>2 = (Q')\<^isub>\<surd> \<and> (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))"
proof(induct arbitrary:n\<^isub>2 n\<^isub>2' rule:WCFG_induct)
  case (WCFG_Entry_Exit prog)
  from `prog \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `(_Entry_) = n\<^isub>2` `(_Exit_) \<noteq> n\<^isub>2'`
  have "et\<^isub>2 = (\<lambda>s. True)\<^isub>\<surd>" by(fastforce dest:WCFG_EntryD)
  thus ?case by simp
next
  case (WCFG_Entry prog)
  from `prog \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `(_Entry_) = n\<^isub>2` `(_0_) \<noteq> n\<^isub>2'`
  have "et\<^isub>2 = (\<lambda>s. False)\<^isub>\<surd>" by(fastforce dest:WCFG_EntryD)
  thus ?case by simp
next
  case WCFG_Skip
  from `Skip \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `(_0_) = n\<^isub>2` `(_Exit_) \<noteq> n\<^isub>2'`
  have False by(fastforce elim:WCFG.While_CFG.cases)
  thus ?case by simp
next
  case (WCFG_LAss V e)
  from `V:=e \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `(_0_) = n\<^isub>2` `(_1_) \<noteq> n\<^isub>2'`
  have False by -(erule WCFG.While_CFG.cases,auto)
  thus ?case by simp
next
  case (WCFG_LAssSkip V e)
  from `V:=e \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `(_1_) = n\<^isub>2` `(_Exit_) \<noteq> n\<^isub>2'`
  have False by -(erule WCFG.While_CFG.cases,auto)
  thus ?case by simp
next
  case (WCFG_SeqFirst c\<^isub>1 n et n' c\<^isub>2)
  note IH = `\<And>n\<^isub>2 n\<^isub>2'. \<lbrakk>c\<^isub>1 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'; n = n\<^isub>2; n' \<noteq> n\<^isub>2'\<rbrakk>
  \<Longrightarrow> \<exists>Q Q'. et = (Q)\<^isub>\<surd> \<and> et\<^isub>2 = (Q')\<^isub>\<surd> \<and> (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))`
  from `c\<^isub>1;;c\<^isub>2 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `c\<^isub>1 \<turnstile> n -et\<rightarrow> n'` `n = n\<^isub>2` `n' \<noteq> n\<^isub>2'`
  have "c\<^isub>1 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2' \<or> (c\<^isub>1 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> (_Exit_) \<and> n\<^isub>2' = (_0_) \<oplus> #:c\<^isub>1)"
    apply - apply(erule WCFG.While_CFG.cases)
    apply(auto intro:WCFG.While_CFG.intros)
    by(case_tac n,auto dest:WCFG_sourcelabel_less_num_nodes)+
  thus ?case
  proof
    assume "c\<^isub>1 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'"
    from IH[OF this `n = n\<^isub>2` `n' \<noteq> n\<^isub>2'`] show ?case .
  next
    assume "c\<^isub>1 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> (_Exit_) \<and> n\<^isub>2' = (_0_) \<oplus> #:c\<^isub>1"
    hence edge:"c\<^isub>1 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> (_Exit_)" and n2':"n\<^isub>2' = (_0_) \<oplus> #:c\<^isub>1" by simp_all
    from IH[OF edge `n = n\<^isub>2` `n' \<noteq> (_Exit_)`] show ?case .
  qed
next
  case (WCFG_SeqConnect c\<^isub>1 n et c\<^isub>2)
  note IH = `\<And>n\<^isub>2 n\<^isub>2'. \<lbrakk>c\<^isub>1 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'; n = n\<^isub>2; (_Exit_) \<noteq> n\<^isub>2'\<rbrakk>
  \<Longrightarrow> \<exists>Q Q'. et = (Q)\<^isub>\<surd> \<and> et\<^isub>2 = (Q')\<^isub>\<surd> \<and> (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))`
  from `c\<^isub>1;;c\<^isub>2 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `c\<^isub>1 \<turnstile> n -et\<rightarrow> (_Exit_)` `n = n\<^isub>2` `n \<noteq> (_Entry_)`
    `(_0_) \<oplus> #:c\<^isub>1 \<noteq> n\<^isub>2'` have "c\<^isub>1 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2' \<and> (_Exit_) \<noteq> n\<^isub>2'"
    apply - apply(erule WCFG.While_CFG.cases)
    apply(auto intro:WCFG.While_CFG.intros)
    by(case_tac n,auto dest:WCFG_sourcelabel_less_num_nodes)+
  from IH[OF this[THEN conjunct1] `n = n\<^isub>2` this[THEN conjunct2]]
  show ?case .
next
  case (WCFG_SeqSecond c\<^isub>2 n et n' c\<^isub>1)
  note IH = `\<And>n\<^isub>2 n\<^isub>2'. \<lbrakk>c\<^isub>2 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'; n = n\<^isub>2; n' \<noteq> n\<^isub>2'\<rbrakk>
  \<Longrightarrow> \<exists>Q Q'. et = (Q)\<^isub>\<surd> \<and> et\<^isub>2 = (Q')\<^isub>\<surd> \<and> (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))`
  from `c\<^isub>1;;c\<^isub>2 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `c\<^isub>2 \<turnstile> n -et\<rightarrow> n'` `n \<oplus> #:c\<^isub>1 = n\<^isub>2`
    `n' \<oplus> #:c\<^isub>1 \<noteq> n\<^isub>2'` `n \<noteq> (_Entry_)`
  obtain nx where "c\<^isub>2 \<turnstile> n -et\<^isub>2\<rightarrow> nx \<and> nx \<oplus> #:c\<^isub>1 = n\<^isub>2'"
    apply - apply(erule WCFG.While_CFG.cases)
    apply(auto intro:WCFG.While_CFG.intros)
      apply(cases n,auto dest:WCFG_sourcelabel_less_num_nodes)
     apply(cases n,auto dest:WCFG_sourcelabel_less_num_nodes)
    by(fastforce dest:label_incr_inj)
  with `n' \<oplus> #:c\<^isub>1 \<noteq> n\<^isub>2'` have edge:"c\<^isub>2 \<turnstile> n -et\<^isub>2\<rightarrow> nx" and neq:"n' \<noteq> nx"
    by auto
  from IH[OF edge _ neq] show ?case by simp
next
  case (WCFG_CondTrue b c\<^isub>1 c\<^isub>2)
  from `if (b) c\<^isub>1 else c\<^isub>2 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `(_0_) = n\<^isub>2` `(_0_) \<oplus> 1 \<noteq> n\<^isub>2'`
  show ?case by -(erule WCFG.While_CFG.cases,auto)
next
  case (WCFG_CondFalse b c\<^isub>1 c\<^isub>2)
  from `if (b) c\<^isub>1 else c\<^isub>2 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `(_0_) = n\<^isub>2` `(_0_) \<oplus> #:c\<^isub>1 + 1 \<noteq> n\<^isub>2'`
  show ?case by -(erule WCFG.While_CFG.cases,auto)
next
  case (WCFG_CondThen c\<^isub>1 n et n' b c\<^isub>2)
  note IH = `\<And>n\<^isub>2 n\<^isub>2'. \<lbrakk>c\<^isub>1 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'; n = n\<^isub>2; n' \<noteq> n\<^isub>2'\<rbrakk>
    \<Longrightarrow> \<exists>Q Q'. et = (Q)\<^isub>\<surd> \<and> et\<^isub>2 = (Q')\<^isub>\<surd> \<and> (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))`
  from `if (b) c\<^isub>1 else c\<^isub>2 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `c\<^isub>1 \<turnstile> n -et\<rightarrow> n'` `n \<noteq> (_Entry_)` 
    `n \<oplus> 1 = n\<^isub>2` `n' \<oplus> 1 \<noteq> n\<^isub>2'`
  obtain nx where "c\<^isub>1 \<turnstile> n -et\<^isub>2\<rightarrow> nx \<and> n' \<noteq> nx"
    apply - apply(erule WCFG.While_CFG.cases)
    apply(auto intro:WCFG.While_CFG.intros)
     apply(drule label_incr_inj) apply auto
    apply(drule label_incr_simp_rev[OF sym])
    by(case_tac na,auto dest:WCFG_sourcelabel_less_num_nodes)
  from IH[OF this[THEN conjunct1] _ this[THEN conjunct2]] show ?case by simp
next
  case (WCFG_CondElse c\<^isub>2 n et n' b c\<^isub>1)
  note IH = `\<And>n\<^isub>2 n\<^isub>2'. \<lbrakk>c\<^isub>2 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'; n = n\<^isub>2; n' \<noteq> n\<^isub>2'\<rbrakk>
    \<Longrightarrow> \<exists>Q Q'. et = (Q)\<^isub>\<surd> \<and> et\<^isub>2 = (Q')\<^isub>\<surd> \<and> (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))`
  from `if (b) c\<^isub>1 else c\<^isub>2 \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `c\<^isub>2 \<turnstile> n -et\<rightarrow> n'` `n \<noteq> (_Entry_)` 
    `n \<oplus> #:c\<^isub>1 + 1 = n\<^isub>2` `n' \<oplus> #:c\<^isub>1 + 1 \<noteq> n\<^isub>2'`
  obtain nx where "c\<^isub>2 \<turnstile> n -et\<^isub>2\<rightarrow> nx \<and> n' \<noteq> nx"
    apply - apply(erule WCFG.While_CFG.cases)
    apply(auto intro:WCFG.While_CFG.intros)
     apply(drule label_incr_simp_rev)
     apply(case_tac na,auto,cases n,auto dest:WCFG_sourcelabel_less_num_nodes)
    by(fastforce dest:label_incr_inj)
  from IH[OF this[THEN conjunct1] _ this[THEN conjunct2]] show ?case by simp
next
  case (WCFG_WhileTrue b c')
  from `while (b) c' \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `(_0_) = n\<^isub>2` `(_0_) \<oplus> 2 \<noteq> n\<^isub>2'`
  show ?case by -(erule WCFG.While_CFG.cases,auto)
next
  case (WCFG_WhileFalse b c')
  from `while (b) c' \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `(_0_) = n\<^isub>2` `(_1_) \<noteq> n\<^isub>2'`
  show ?case by -(erule WCFG.While_CFG.cases,auto)
next
  case (WCFG_WhileFalseSkip b c')
  from `while (b) c' \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `(_1_) = n\<^isub>2` `(_Exit_) \<noteq> n\<^isub>2'`
  show ?case by -(erule WCFG.While_CFG.cases,auto dest:label_incr_ge)
next
  case (WCFG_WhileBody c' n et n' b)
  note IH = `\<And>n\<^isub>2 n\<^isub>2'. \<lbrakk>c' \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'; n = n\<^isub>2; n' \<noteq> n\<^isub>2'\<rbrakk>
    \<Longrightarrow> \<exists>Q Q'. et = (Q)\<^isub>\<surd> \<and> et\<^isub>2 = (Q')\<^isub>\<surd> \<and> (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))`
  from `while (b) c' \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `c' \<turnstile> n -et\<rightarrow> n'` `n \<noteq> (_Entry_)`
    `n' \<noteq> (_Exit_)` `n \<oplus> 2 = n\<^isub>2` `n' \<oplus> 2 \<noteq> n\<^isub>2'`
  obtain nx where "c' \<turnstile> n -et\<^isub>2\<rightarrow> nx \<and> n' \<noteq> nx"
    apply - apply(erule WCFG.While_CFG.cases)
    apply(auto intro:WCFG.While_CFG.intros)
      apply(fastforce dest:label_incr_ge[OF sym])
     apply(fastforce dest:label_incr_inj)
    by(fastforce dest:label_incr_inj)
  from IH[OF this[THEN conjunct1] _ this[THEN conjunct2]] show ?case by simp
next
  case (WCFG_WhileBodyExit c' n et b)
  note IH = `\<And>n\<^isub>2 n\<^isub>2'. \<lbrakk>c' \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'; n = n\<^isub>2; (_Exit_) \<noteq> n\<^isub>2'\<rbrakk>
    \<Longrightarrow> \<exists>Q Q'. et = (Q)\<^isub>\<surd> \<and> et\<^isub>2 = (Q')\<^isub>\<surd> \<and> (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))`
  from `while (b) c' \<turnstile> n\<^isub>2 -et\<^isub>2\<rightarrow> n\<^isub>2'` `c' \<turnstile> n -et\<rightarrow> (_Exit_)` `n \<noteq> (_Entry_)`
    `n \<oplus> 2 = n\<^isub>2` `(_0_) \<noteq> n\<^isub>2'`
  obtain nx where "c' \<turnstile> n -et\<^isub>2\<rightarrow> nx \<and> (_Exit_) \<noteq> nx"
    apply - apply(erule WCFG.While_CFG.cases)
    apply(auto intro:WCFG.While_CFG.intros)
     apply(fastforce dest:label_incr_ge[OF sym])
    by(fastforce dest:label_incr_inj)
  from IH[OF this[THEN conjunct1] _ this[THEN conjunct2]] show ?case by simp
qed

(*<*)declare One_nat_def [simp](*>*)

end
