(*  Title:      JinjaThreads/Framework/FWWait.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Semantics of the thread actions for wait, notify and interrupt} *}

theory FWWait imports FWState begin

text {* Update functions for the wait sets in the multithreaded state *}

inductive redT_updW :: "'t \<Rightarrow> ('w, 't) wait_sets \<Rightarrow> ('t,'w) wait_set_action \<Rightarrow> ('w,'t) wait_sets \<Rightarrow> bool"
for t :: 't and ws :: "('w, 't) wait_sets"
where
  "ws t' = \<lfloor>InWS w\<rfloor> \<Longrightarrow> redT_updW t ws (Notify w) (ws(t' \<mapsto> WokenUp WSNotified))"
| "(\<And>t'. ws t' \<noteq> \<lfloor>InWS w\<rfloor>) \<Longrightarrow> redT_updW t ws (Notify w) ws"
| "redT_updW t ws (NotifyAll w) (\<lambda>t. if ws t = \<lfloor>InWS w\<rfloor> then \<lfloor>WokenUp WSNotified\<rfloor> else ws t)"
| "redT_updW t ws (Suspend w) (ws(t \<mapsto> InWS w))"
| "ws t' = \<lfloor>InWS w\<rfloor> \<Longrightarrow> redT_updW t ws (Interrupt t') (ws(t' \<mapsto> WokenUp WSInterrupted))"
| "(\<And>w. ws t' \<noteq> \<lfloor>InWS w\<rfloor>) \<Longrightarrow> redT_updW t ws (Interrupt t') ws"
| "redT_updW t ws Notified (ws(t := None))"
| "redT_updW t ws Interrupted (ws(t := None))"
(*
primrec redT_updW :: "('w,'t) wait_sets \<Rightarrow> 't \<Rightarrow> ('t,'w) wait_set_action \<Rightarrow> ('w,'t) wait_sets"
where
  "redT_updW ws t (Notify w) = (if (\<exists>t. ws t = \<lfloor>InWS w\<rfloor>) then ws((SOME t. ws t = \<lfloor>InWS w\<rfloor>) \<mapsto> WokenUp WSNotified) else ws)"
| "redT_updW ws t (NotifyAll w) = (\<lambda>t. if ws t = \<lfloor>InWS w\<rfloor> then \<lfloor>WokenUp WSNotified\<rfloor> else ws t)"
| "redT_updW ws t (Suspend w) = ws(t \<mapsto> InWS w)"
| "redT_updW ws t (Interrupt T) = (if \<exists>w. (ws t = \<lfloor>InWS w\<rfloor>) then ws(t \<mapsto> WokenUp WSInterrupted) else ws)"
| "redT_updW ws t Notified = ws(t := None)"
| "redT_updW ws t Interrupted = ws(t := None)"
*)

definition redT_updWs :: "'t \<Rightarrow> ('w,'t) wait_sets \<Rightarrow> ('t,'w) wait_set_action list \<Rightarrow> ('w,'t) wait_sets \<Rightarrow> bool"
where "redT_updWs t = rtrancl3p (redT_updW t)"

(*
fun redT_updWs :: "('w,'t) wait_sets \<Rightarrow> 't \<Rightarrow> ('t,'w) wait_set_action list \<Rightarrow> ('w,'t) wait_sets"
where
  "redT_updWs ws t [] = ws"
| "redT_updWs ws t (wa#was) = redT_updWs (redT_updW ws t wa) t was"
*)

inductive_simps redT_updW_simps [simp]:
  "redT_updW t ws (Notify w) ws'"
  "redT_updW t ws (NotifyAll w) ws'"
  "redT_updW t ws (Suspend w) ws'"
  "redT_updW t ws (Interrupt t') ws'"
  "redT_updW t ws Notified ws'"
  "redT_updW t ws Interrupted ws'"

lemma redT_updW_total: "\<exists>ws'. redT_updW t ws wa ws'"
by(cases wa)(auto simp add: redT_updW.simps)

lemma redT_updWs_total: "\<exists>ws'. redT_updWs t ws was ws'"
proof(induct was rule: rev_induct)
  case Nil thus ?case by(auto simp add: redT_updWs_def)
next
  case (snoc wa was)
  then obtain ws' where "redT_updWs t ws was ws'" ..
  also from redT_updW_total[of t ws' wa]
  obtain ws'' where "redT_updW t ws' wa ws''" ..
  ultimately show ?case unfolding redT_updWs_def by(auto intro: rtrancl3p_step)
qed

lemma redT_updWs_trans: "\<lbrakk> redT_updWs t ws was ws'; redT_updWs t ws' was' ws'' \<rbrakk> \<Longrightarrow> redT_updWs t ws (was @ was') ws''"
unfolding redT_updWs_def by(rule rtrancl3p_trans)

(*
lemma redT_updWs_append [simp]:
  "redT_updWs ws t (was @ was') = redT_updWs (redT_updWs ws t was) t was'"
by(induct was arbitrary: ws, auto)
*)

lemma redT_updW_None_implies_None:
  "\<lbrakk> redT_updW t' ws wa ws'; ws t = None; t \<noteq> t' \<rbrakk> \<Longrightarrow> ws' t = None"
by(auto simp add: redT_updW.simps)

(*
lemma redT_updW_None_implies_None:
  "\<lbrakk> t \<noteq> t'; ws t = None \<rbrakk> \<Longrightarrow> redT_updW ws t' wa t = None"
by(cases wa)(auto dest: someI[where P="\<lambda>t. ws t = \<lfloor>InWS w\<rfloor>", standard])
*)

lemma redT_updWs_None_implies_None:
  assumes "redT_updWs t' ws was ws'"
  and "t \<noteq> t'" and "ws t = None"
  shows "ws' t = None"
using `redT_updWs t' ws was ws'` `ws t = None` unfolding redT_updWs_def
by induct(auto intro: redT_updW_None_implies_None[OF _ _ `t \<noteq> t'`])

(*
lemma redT_updWs_None_implies_None:
  assumes "t \<noteq> t'"
  shows "ws t = None \<Longrightarrow> redT_updWs ws t' was t = None"
proof(induct was arbitrary: ws)
  case Nil thus ?case by simp
next
  case (Cons WA WAS WS)
  from `t \<noteq> t'` `WS t = None`
  have "redT_updW WS t' WA t = None"
    by(rule redT_updW_None_implies_None)
  with `\<And>ws. ws t = None \<Longrightarrow> redT_updWs ws t' WAS t = None`
  show ?case by(auto)
qed
*)

lemma redT_updW_WokenUp_imp_WokenUp:
  "\<lbrakk> redT_updW t ws wa ws'; ws t'' = \<lfloor>WokenUp w\<rfloor>; t'' \<noteq> t \<rbrakk> \<Longrightarrow>  ws' t'' = \<lfloor>WokenUp w\<rfloor>"
by(auto simp add: redT_updW.simps)

(*
lemma redT_updW_WokenUp_imp_WokenUp:
  "\<lbrakk> t'' \<noteq> t; ws t'' = \<lfloor>WokenUp w\<rfloor> \<rbrakk> \<Longrightarrow> redT_updW ws t wa t'' = \<lfloor>WokenUp w\<rfloor>"
by(cases wa)(auto dest: someI[where P = "\<lambda>t. ws t = \<lfloor>InWS w'\<rfloor>", standard])
*)

lemma redT_updWs_WokenUp_imp_WokenUp:
  "\<lbrakk> redT_updWs t ws was ws'; t'' \<noteq> t; ws t'' = \<lfloor>WokenUp w\<rfloor> \<rbrakk> \<Longrightarrow> ws' t'' = \<lfloor>WokenUp w\<rfloor>"
unfolding redT_updWs_def 
by(induct rule: rtrancl3p.induct)(auto dest: redT_updW_WokenUp_imp_WokenUp)
(*
lemma redT_updWs_WokenUp_imp_WokenUp:
  "\<lbrakk> t'' \<noteq> t; ws t'' = \<lfloor>WokenUp w\<rfloor> \<rbrakk> \<Longrightarrow> redT_updWs ws t was t'' = \<lfloor>WokenUp w\<rfloor>"
by(induct was arbitrary: ws)(simp_all add: redT_updW_WokenUp_imp_WokenUp)
*)

lemma redT_updW_Some_otherD:
  "\<lbrakk> redT_updW t' ws wa ws'; ws' t = \<lfloor>w\<rfloor>; t \<noteq> t' \<rbrakk> 
  \<Longrightarrow> (case w of InWS w' \<Rightarrow> ws t = \<lfloor>InWS w'\<rfloor> | _ \<Rightarrow> ws t = \<lfloor>w\<rfloor> \<or> (\<exists>w'. ws t = \<lfloor>InWS w'\<rfloor>))"
by(auto simp add: redT_updW.simps split: split_if_asm wait_set_status.split)

(*
lemma redT_updW_Some_otherD:
  "\<lbrakk> t \<noteq> t'; redT_updW ws t' wa t = \<lfloor>w\<rfloor> \<rbrakk>
  \<Longrightarrow> (case w of InWS w' \<Rightarrow> ws t = \<lfloor>InWS w'\<rfloor> | _ \<Rightarrow> ws t = \<lfloor>w\<rfloor> \<or> (\<exists>w'. ws t = \<lfloor>InWS w'\<rfloor>))"
apply(cases wa)
apply(auto split: split_if_asm wait_set_status.split dest: someI[where P = "\<lambda>t. ws t = \<lfloor>InWS w'\<rfloor>", standard])
done
*)


lemma redT_updWs_Some_otherD:
  "\<lbrakk> redT_updWs t' ws was ws'; ws' t = \<lfloor>w\<rfloor>; t \<noteq> t' \<rbrakk> 
  \<Longrightarrow> (case w of InWS w' \<Rightarrow> ws t = \<lfloor>InWS w'\<rfloor> | _ \<Rightarrow> ws t = \<lfloor>w\<rfloor> \<or> (\<exists>w'. ws t = \<lfloor>InWS w'\<rfloor>))"
unfolding redT_updWs_def
apply(induct arbitrary: w rule: rtrancl3p.induct)
apply(fastsimp split: wait_set_status.splits dest: redT_updW_Some_otherD)+
done

(*
lemma redT_updWs_Some_otherD:
  "\<lbrakk> t \<noteq> t'; redT_updWs ws t' was t = \<lfloor>w\<rfloor> \<rbrakk>
  \<Longrightarrow> (case w of InWS w' \<Rightarrow> ws t = \<lfloor>InWS w'\<rfloor> | _ \<Rightarrow> ws t = \<lfloor>w\<rfloor> \<or> (\<exists>w'. ws t = \<lfloor>InWS w'\<rfloor>))"
proof(induct was arbitrary: ws)
  case Nil thus ?case by(simp split: wait_set_status.split)
next
  case (Cons wa was)
  from `redT_updWs ws t' (wa # was) t = \<lfloor>w\<rfloor>`
  have "redT_updWs (redT_updW ws t' wa) t' was t = \<lfloor>w\<rfloor>" by simp
  with `t \<noteq> t'`
  have "case w of InWS w' \<Rightarrow> redT_updW ws t' wa t = \<lfloor>InWS w'\<rfloor>
                | _       \<Rightarrow> redT_updW ws t' wa t = \<lfloor>w\<rfloor> \<or> (\<exists>w'. redT_updW ws t' wa t = \<lfloor>InWS w'\<rfloor>)"
    by(rule Cons)
  thus ?case by(auto dest: redT_updW_Some_otherD[OF `t \<noteq> t'`] split: wait_set_status.split_asm)
qed
*)

lemma redT_updW_None_SomeD:
  "\<lbrakk> redT_updW t ws wa ws'; ws' t' = \<lfloor>w\<rfloor>; ws t' = None \<rbrakk> \<Longrightarrow> t = t' \<and> (\<exists>w'. w = InWS w' \<and> wa = Suspend w')"
by(auto simp add: redT_updW.simps split: split_if_asm)

(*
lemma redT_updW_None_SomeD:
  "\<lbrakk> redT_updW ws t wa t' = \<lfloor>w\<rfloor>; ws t' = None \<rbrakk> \<Longrightarrow> t = t' \<and> (\<exists>w'. w = InWS w' \<and> wa = Suspend w')"
by(cases wa)(auto split: split_if_asm dest: someI[where P="\<lambda>t. ws t = \<lfloor>InWS w'\<rfloor>", standard])
*)

lemma redT_updWs_None_SomeD:
  "\<lbrakk> redT_updWs t ws was ws'; ws' t' = \<lfloor>w\<rfloor>; ws t' = None \<rbrakk> \<Longrightarrow> t = t' \<and> (\<exists>w'. Suspend w' \<in> set was)"
unfolding redT_updWs_def
proof(induct arbitrary: w rule: rtrancl3p.induct)
  case (rtrancl3p_refl ws) thus ?case by simp
next
  case (rtrancl3p_step ws was ws' wa ws'')
  show ?case
  proof(cases "ws' t'")
    case None
    from redT_updW_None_SomeD[OF `redT_updW t ws' wa ws''`, OF `ws'' t' = \<lfloor>w\<rfloor>` this]
    show ?thesis by auto
  next
    case (Some w')
    with `ws t' = None` rtrancl3p_step.hyps(2) show ?thesis by auto
  qed
qed

(*
lemma redT_updWs_None_SomeD:
  "\<lbrakk> redT_updWs ws t was t' = \<lfloor>w\<rfloor>; ws t' = None \<rbrakk> \<Longrightarrow> t = t' \<and> (\<exists>w'. Suspend w' \<in> set was)"
proof(induct was arbitrary: ws w)
  case Nil thus ?case by simp
next
  case (Cons wa was)
  show ?case
  proof(cases "redT_updW ws t wa t'")
    case None
    from `redT_updWs ws t (wa # was) t' = \<lfloor>w\<rfloor>`
    have "redT_updWs (redT_updW ws t wa) t was t' = \<lfloor>w\<rfloor>" by simp
    hence "t = t' \<and> (\<exists>w'. Suspend w' \<in> set was)" using None by(rule Cons)
    thus ?thesis by auto
  next
    case (Some w')
    with `ws t' = None` show ?thesis
      by(auto dest: redT_updW_None_SomeD)
  qed
qed
*)

lemma redT_updW_neq_Some_SomeD:
  "\<lbrakk> redT_updW t' ws wa ws'; ws' t = \<lfloor>InWS w\<rfloor>; ws t \<noteq> \<lfloor>InWS w\<rfloor> \<rbrakk> \<Longrightarrow> t = t' \<and> wa = Suspend w"
by(auto simp add: redT_updW.simps split: split_if_asm)

(*  
lemma redT_updW_neq_Some_SomeD:
  "\<lbrakk> redT_updW ws t' wa t = \<lfloor>InWS w\<rfloor>; ws t \<noteq> \<lfloor>InWS w\<rfloor> \<rbrakk> \<Longrightarrow> t = t' \<and> wa = Suspend w"
by(cases wa)(auto split: split_if_asm)
*)

lemma redT_updWs_neq_Some_SomeD:
  "\<lbrakk> redT_updWs t ws was ws'; ws' t' = \<lfloor>InWS w\<rfloor>; ws t' \<noteq> \<lfloor>InWS w\<rfloor> \<rbrakk> \<Longrightarrow> t = t' \<and> Suspend w \<in> set was"
unfolding redT_updWs_def
proof(induct rule: rtrancl3p.induct)
  case rtrancl3p_refl thus ?case by simp
next
  case (rtrancl3p_step ws was ws' wa ws'')
  show ?case
  proof(cases "ws' t' = \<lfloor>InWS w\<rfloor>")
    case True
    with `ws t' \<noteq> \<lfloor>InWS w\<rfloor>` `\<lbrakk>ws' t' = \<lfloor>InWS w\<rfloor>; ws t' \<noteq> \<lfloor>InWS w\<rfloor>\<rbrakk> \<Longrightarrow> t = t' \<and> Suspend w \<in> set was`
    show ?thesis by simp
  next
    case False
    with `redT_updW t ws' wa ws''` `ws'' t' = \<lfloor>InWS w\<rfloor>`
    have "t' = t \<and> wa = Suspend w" by(rule redT_updW_neq_Some_SomeD)
    thus ?thesis by auto
  qed
qed

(*
lemma redT_updWs_neq_Some_SomeD:
  "\<lbrakk> redT_updWs ws t was t' = \<lfloor>InWS w\<rfloor>; ws t' \<noteq> \<lfloor>InWS w\<rfloor> \<rbrakk> \<Longrightarrow> t = t' \<and> Suspend w \<in> set was"
proof(induct was arbitrary: ws)
  case Nil thus ?case by simp
next
  case (Cons wa was)
  show ?case
  proof(cases "redT_updW ws t wa t' = \<lfloor>InWS w\<rfloor>")
    case False
    from `redT_updWs ws t (wa # was) t' = \<lfloor>InWS w\<rfloor>`
    have "redT_updWs (redT_updW ws t wa) t was t' = \<lfloor>InWS w\<rfloor>" by simp
    hence "t = t' \<and> Suspend w \<in> set was" using False by(rule Cons)
    thus ?thesis by auto
  next
    case True
    hence "t' = t \<and> wa = Suspend w" using `ws t' \<noteq> \<lfloor>InWS w\<rfloor>`
      by(rule redT_updW_neq_Some_SomeD)
    thus ?thesis by simp
  qed
qed
*)

lemma redT_updW_not_Suspend_Some:
  "\<lbrakk> redT_updW t ws wa ws'; ws' t = \<lfloor>w'\<rfloor>; ws t = \<lfloor>w\<rfloor>; \<And>w. wa \<noteq> Suspend w \<rbrakk>
  \<Longrightarrow> w' = w \<or> (\<exists>w'' w'''. w = InWS w'' \<and> w' = WokenUp w''')"
by(auto simp add: redT_updW.simps split: split_if_asm)

lemma redT_updWs_not_Suspend_Some:
  "\<lbrakk> redT_updWs t ws was ws'; ws' t = \<lfloor>w'\<rfloor>; ws t = \<lfloor>w\<rfloor>; \<And>w. Suspend w \<notin> set was \<rbrakk>
  \<Longrightarrow> w' = w \<or> (\<exists>w'' w'''. w = InWS w'' \<and> w' = WokenUp w''')"
unfolding redT_updWs_def
proof(induct arbitrary: w rule: rtrancl3p_converse_induct)
  case refl thus ?case by simp
next
  case (step ws wa ws' was ws'')
  note `ws'' t = \<lfloor>w'\<rfloor>`
  moreover  
  have "ws' t \<noteq> None"
  proof
    assume "ws' t = None"
    with `rtrancl3p (redT_updW t) ws' was ws''` `ws'' t = \<lfloor>w'\<rfloor>`
    obtain w' where "Suspend w' \<in> set was" unfolding redT_updWs_def[symmetric]
      by(auto dest: redT_updWs_None_SomeD)
    with `Suspend w' \<notin> set (wa # was)` show False by simp
  qed
  then obtain w'' where "ws' t = \<lfloor>w''\<rfloor>" by auto
  moreover {
    fix w
    from `Suspend w \<notin> set (wa # was)` have "Suspend w \<notin> set was" by simp }
  ultimately have "w' = w'' \<or> (\<exists>w''' w''''. w'' = InWS w''' \<and> w' = WokenUp w'''')" by(rule step.hyps)
  moreover { fix w
    from `Suspend w \<notin> set (wa # was)` have "wa \<noteq> Suspend w" by auto }
  note redT_updW_not_Suspend_Some[OF `redT_updW t ws wa ws'`, OF `ws' t = \<lfloor>w''\<rfloor>` `ws t = \<lfloor>w\<rfloor>` this]
  ultimately show ?case by auto
qed

(*
lemma redT_updWs_not_Suspend_Some:
  "\<lbrakk> redT_updWs ws t was t = \<lfloor>w'\<rfloor>; ws t = \<lfloor>w\<rfloor>; \<And>w. Suspend w \<notin> set was \<rbrakk>
  \<Longrightarrow> w' = w \<or> (\<exists>w'' w'''. w = InWS w'' \<and> w' = WokenUp w''')"
proof(induct was arbitrary: ws w)
  case Nil thus ?case by simp
next
  case (Cons wa was)
  from `redT_updWs ws t (wa # was) t = \<lfloor>w'\<rfloor>`
  have "redT_updWs (redT_updW ws t wa) t was t = \<lfloor>w'\<rfloor>" by simp
  moreover
  have "redT_updW ws t wa t \<noteq> None"
  proof
    assume "redT_updW ws t wa t = None"
    from redT_updWs_None_SomeD[OF `redT_updWs (redT_updW ws t wa) t was t = \<lfloor>w'\<rfloor>`, OF this]
    obtain w' where "Suspend w' \<in> set was" by auto
    with `Suspend w' \<notin> set (wa # was)` show False by simp
  qed
  then obtain w'' where "redT_updW ws t wa t = \<lfloor>w''\<rfloor>" by auto
  moreover {
    fix w
    from `Suspend w \<notin> set (wa # was)` have "Suspend w \<notin> set was" by simp }
  ultimately have "w' = w'' \<or> (\<exists>w''' w''''. w'' = InWS w''' \<and> w' = WokenUp w'''')" by(rule Cons)
  moreover { fix w
    from `Suspend w \<notin> set (wa # was)` have "wa \<noteq> Suspend w" by auto }
  note redT_updW_not_Suspend_Some[OF `redT_updW ws t wa t = \<lfloor>w''\<rfloor>`, OF `ws t = \<lfloor>w\<rfloor>` this]
  ultimately show ?case by auto
qed
*)

lemma redT_updWs_WokenUp_SuspendD:
  "\<lbrakk> redT_updWs t ws was ws'; Notified \<in> set was \<or> Interrupted \<in> set was; ws' t = \<lfloor>w\<rfloor> \<rbrakk> \<Longrightarrow> \<exists>w. Suspend w \<in> set was"
unfolding redT_updWs_def
by(induct rule: rtrancl3p_converse_induct)(auto dest: redT_updWs_None_SomeD[unfolded redT_updWs_def])

(*
lemma redT_updWs_WokenUp_SuspendD:
  "\<lbrakk> Notified \<in> set was \<or> Interrupted \<in> set was; redT_updWs ws t was t = \<lfloor>w\<rfloor> \<rbrakk> \<Longrightarrow> \<exists>w. Suspend w \<in> set was"
by(induct was arbitrary: ws)(auto dest: redT_updWs_None_SomeD)
*)


lemma redT_updW_Woken_Up_same_no_Notified_Interrupted:
  "\<lbrakk> redT_updW t ws wa ws'; ws' t = \<lfloor>WokenUp w\<rfloor>; ws t = \<lfloor>WokenUp w\<rfloor>; \<And>w. wa \<noteq> Suspend w \<rbrakk>
  \<Longrightarrow> wa \<noteq> Notified \<and> wa \<noteq> Interrupted"
by(fastsimp)

lemma redT_updWs_Woken_Up_same_no_Notified_Interrupted:
  "\<lbrakk> redT_updWs t ws was ws'; ws' t = \<lfloor>WokenUp w\<rfloor>; ws t = \<lfloor>WokenUp w\<rfloor>; \<And>w. Suspend w \<notin> set was \<rbrakk>
  \<Longrightarrow> Notified \<notin> set was \<and> Interrupted \<notin> set was"
unfolding redT_updWs_def
proof(induct rule: rtrancl3p_converse_induct)
  case refl thus ?case by simp
next
  case (step ws wa ws' was ws'')
  note Suspend = `\<And>w. Suspend w \<notin> set (wa # was)`
  note `ws'' t = \<lfloor>WokenUp w\<rfloor>`
  moreover have "ws' t = \<lfloor>WokenUp w\<rfloor>"
  proof(cases "ws' t")
    case None
    with `rtrancl3p (redT_updW t) ws' was ws''` `ws'' t = \<lfloor>WokenUp w\<rfloor>`
    obtain w where "Suspend w \<in> set was" unfolding redT_updWs_def[symmetric]
      by(auto dest: redT_updWs_None_SomeD)
    with Suspend[of w] have False by simp
    thus ?thesis ..
  next
    case (Some w')
    thus ?thesis using `ws t = \<lfloor>WokenUp w\<rfloor>` Suspend `redT_updW t ws wa ws'`
      by(auto simp add: redT_updW.simps split: split_if_asm)
  qed
  moreover
  { fix w from Suspend[of w] have "Suspend w \<notin> set was" by simp }
  ultimately have "Notified \<notin> set was \<and> Interrupted \<notin> set was" by(rule step.hyps)
  moreover 
  { fix w from Suspend[of w] have "wa \<noteq> Suspend w" by auto }
  with `redT_updW t ws wa ws'` `ws' t = \<lfloor>WokenUp w\<rfloor>` `ws t = \<lfloor>WokenUp w\<rfloor>`
  have "wa \<noteq> Notified \<and> wa \<noteq> Interrupted" by(rule redT_updW_Woken_Up_same_no_Notified_Interrupted)
  ultimately show ?case by auto
qed

(*
lemma redT_updWs_Woken_Up_same_no_Notified_Interrupted:
  "\<lbrakk> redT_updWs ws t was t = \<lfloor>WokenUp w\<rfloor>; ws t = \<lfloor>WokenUp w\<rfloor>; \<And>w. Suspend w \<notin> set was \<rbrakk>
  \<Longrightarrow> Notified \<notin> set was \<and> Interrupted \<notin> set was"
proof(induct was arbitrary: ws)
  case Nil thus ?case by simp
next
  case (Cons wa was)
  note Suspend = `\<And>w. Suspend w \<notin> set (wa # was)`
  from `redT_updWs ws t (wa # was) t = \<lfloor>WokenUp w\<rfloor>`
  have was: "redT_updWs (redT_updW ws t wa) t was t = \<lfloor>WokenUp w\<rfloor>" by simp
  moreover have "redT_updW ws t wa t = \<lfloor>WokenUp w\<rfloor>"
  proof(cases "redT_updW ws t wa t")
    case None
    from redT_updWs_None_SomeD[OF was, OF this]
    obtain w where "Suspend w \<in> set was" by auto
    with Suspend[of w] have False by simp
    thus ?thesis ..
  next
    case (Some w')
    thus ?thesis using `ws t = \<lfloor>WokenUp w\<rfloor>` Some Suspend
      by(cases wa)(auto split: split_if_asm dest: someI[where P="\<lambda>t. ws t = \<lfloor>InWS w''\<rfloor>", standard])
  qed
  moreover
  { fix w from Suspend[of w] have "Suspend w \<notin> set was" by simp }
  ultimately have "Notified \<notin> set was \<and> Interrupted \<notin> set was" by(rule Cons)
  moreover 
  { fix w from Suspend[of w] have "wa \<noteq> Suspend w" by auto }
  with `redT_updW ws t wa t = \<lfloor>WokenUp w\<rfloor>` `ws t = \<lfloor>WokenUp w\<rfloor>`
  have "wa \<noteq> Notified \<and> wa \<noteq> Interrupted" by(rule redT_updW_Woken_Up_same_no_Notified_Interrupted)
  ultimately show ?case by auto
qed
*)

text {* Preconditions for wait set actions *}

definition wset_actions_ok :: "('w,'t) wait_sets \<Rightarrow> 't \<Rightarrow> ('t,'w) wait_set_action list \<Rightarrow> bool"
where
  "wset_actions_ok ws t was \<longleftrightarrow>
  (if Notified \<in> set was then ws t = \<lfloor>WokenUp WSNotified\<rfloor>
   else if Interrupted \<in> set was then ws t = \<lfloor>WokenUp WSInterrupted\<rfloor>
   else ws t = None)"

lemma wset_actions_ok_Nil [simp]:
  "wset_actions_ok ws t [] \<longleftrightarrow> ws t = None"
by(simp add: wset_actions_ok_def)

definition waiting :: "'w wait_set_status option \<Rightarrow> bool"
where "waiting w \<longleftrightarrow> (\<exists>w'. w = \<lfloor>InWS w'\<rfloor>)"

lemma not_waiting_iff:
  "\<not> waiting w \<longleftrightarrow> w = None \<or> (\<exists>w'. w = \<lfloor>WokenUp w'\<rfloor>)"
apply(cases "w")
apply(case_tac [2] a)
apply(auto simp add: waiting_def)
done

end
