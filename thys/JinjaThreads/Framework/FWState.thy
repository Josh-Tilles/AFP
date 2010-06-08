(*  Title:      JinjaThreads/Framework/FWState.thy
    Author:     Andreas Lochbihler
*)

header {* 
  \chapter{The generic multithreaded semantics}
  \isaheader{State of the multithreaded semantics} *}

theory FWState imports 
  "../Common/Aux"
begin

datatype lock_action =
    Lock
  | Unlock
  | UnlockFail
  | ReleaseAcquire

datatype ('t,'x,'m) new_thread_action =
    NewThread 't 'x 'm
  | NewThreadFail
  | ThreadExists 't

datatype 't conditional_action = 
    Join 't
  | Notified
  | Interrupted

datatype ('t, 'w) wait_set_action =
    Suspend 'w
  | Notify 'w
  | NotifyAll 'w
  | Interrupt 't

types 'l lock_actions = "'l \<Rightarrow>\<^isub>f lock_action list"

translations
  (type) "'l lock_actions" <= (type) "'l \<Rightarrow>\<^isub>f lock_action list"

types ('l,'t,'x,'m,'w,'o) thread_action =
  "'l lock_actions \<times> ('t,'x,'m) new_thread_action list \<times>
   't conditional_action list \<times> ('t, 'w) wait_set_action list \<times> 'o"
(* pretty printing for thread_action type *)
print_translation {*
  let
    fun tr'
       [Const (@{type_syntax finfun}, _) $ l $
          (Const (@{type_syntax list}, _) $ Const (@{type_syntax lock_action}, _)),
        Const (@{type_syntax "*"}, _) $
          (Const (@{type_syntax list}, _) $ (Const (@{type_syntax new_thread_action}, _) $ t1 $ x $ m)) $
          (Const (@{type_syntax "*"}, _) $
            (Const (@{type_syntax list}, _) $ (Const (@{type_syntax conditional_action}, _) $ t2)) $
            (Const (@{type_syntax "*"}, _) $
              (Const (@{type_syntax list}, _) $ (Const (@{type_syntax wait_set_action}, _) $ t3 $ w)) $ o1))] =
      if t1 = t2 andalso t2 = t3 then Syntax.const @{type_syntax thread_action} $ l $ t1 $ x $ m $ w $ o1
      else raise Match;
  in [(@{type_syntax "*"}, tr')]
  end
*}
typ "('l,'t,'x,'m,'w,'o) thread_action"
 
definition locks_a :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'l lock_actions" ("\<lbrace>_\<rbrace>\<^bsub>l\<^esub>" [0] 1000) where
  "locks_a \<equiv> fst"

definition thr_a :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('t,'x,'m) new_thread_action list" ("\<lbrace>_\<rbrace>\<^bsub>t\<^esub>" [0] 1000) where
  "thr_a \<equiv> fst o snd"

definition cond_a :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 't conditional_action list" ("\<lbrace>_\<rbrace>\<^bsub>c\<^esub>" [0] 1000) where
  "cond_a = fst o snd o snd"

definition wset_a :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('t, 'w) wait_set_action list" ("\<lbrace>_\<rbrace>\<^bsub>w\<^esub>" [0] 1000)where
  "wset_a \<equiv> fst o snd o snd o snd" 

definition obs_a :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'o" ("\<lbrace>_\<rbrace>\<^bsub>o\<^esub>" [0] 1000) where
  "obs_a \<equiv> snd o snd o snd o snd" 

lemma locks_a_conv [simp]: "locks_a (ls, ntsjswss) = ls"
by(simp add:locks_a_def)

lemma thr_a_conv [simp]: "thr_a (ls, nts, jswss) = nts"
by(simp add: thr_a_def)

lemma cond_a_conv [simp]: "cond_a (ls, nts, js, wws) = js"
by(simp add: cond_a_def)

lemma wset_a_conv [simp]: "wset_a (ls, nts, js, wss, obs) = wss"
by(simp add: wset_a_def)

lemma obs_a_conv [simp]: "obs_a (ls, nts, js, wss, obs) = obs"
by(simp add: obs_a_def)

fun ta_update_locks :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> lock_action \<Rightarrow> 'l \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action" where
  "ta_update_locks (ls, nts, js, wss, obs) lta l = (ls(\<^sup>f l := ls\<^sub>f l @ [lta]), nts, js, wss, obs)"

fun ta_update_NewThread :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action" where
  "ta_update_NewThread (ls, nts, js, wss, obs) nt = (ls, nts @ [nt], js, wss, obs)"

fun ta_update_Conditional :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 't conditional_action \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action"
where
  "ta_update_Conditional (ls, nts, js, wss, obs) j = (ls, nts, js @ [j], wss, obs)"

fun ta_update_wait_set :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('t, 'w) wait_set_action \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action" where
  "ta_update_wait_set (ls, nts, js, wss, obs) ws = (ls, nts, js, wss @ [ws], obs)"

fun ta_update_obs :: "('l,'t,'x,'m,'w,'o list) thread_action \<Rightarrow> 'o \<Rightarrow> ('l,'t,'x,'m,'w,'o list) thread_action"
where
  "ta_update_obs (ls, nts, js, wss, obs) ob = (ls, nts, js, wss, obs @ [ob])"

abbreviation empty_ta :: "('l,'t,'x,'m,'w,'o list) thread_action" ("\<epsilon>") where
  "empty_ta \<equiv> (\<lambda>\<^isup>f [], [], [], [], [])"


nonterminals
  locklets locklet
syntax
  "_locklet"  :: "lock_action \<Rightarrow> 'l \<Rightarrow> locklet"             ("(2_/\<rightarrow>_)")
  ""         :: "locklet \<Rightarrow> locklets"             ("_")
  "_locklets" :: "locklet \<Rightarrow> locklets \<Rightarrow> locklets" ("_,/ _")
  "_lockUpdate" :: "'a \<Rightarrow> locklets \<Rightarrow> 'a"            ("_\<lbrace>\<^bsub>l\<^esub>/(_)\<rbrace>" [1000,0] 1000)

translations
  "_lockUpdate ta (_locklets b bs)"  == "_lockUpdate (_lockUpdate ta b) bs"
  "ta\<lbrace>\<^bsub>l\<^esub>x\<rightarrow>y\<rbrace>"                         == "CONST ta_update_locks ta x y"


nonterminals
  ntlets ntlet
syntax
  "_ntlet"  :: "('t,'m,'x) new_thread_action \<Rightarrow> ntlet"             ("(_)")
  ""         :: "ntlet \<Rightarrow> ntlets"             ("_")
  "_ntlets" :: "ntlet \<Rightarrow> ntlets \<Rightarrow> ntlets" ("_,/ _")
  "_ntUpdate" :: "'a \<Rightarrow> ntlets \<Rightarrow> 'a"            ("_\<lbrace>\<^bsub>t\<^esub>/(_)\<rbrace>" [1000,0] 1000)

translations
  "_ntUpdate ta (_ntlets b bs)"  == "_ntUpdate (_ntUpdate ta b) bs"
  "ta\<lbrace>\<^bsub>t\<^esub>nt\<rbrace>"                       == "CONST ta_update_NewThread ta nt"


nonterminals
  jlets jlet
syntax
  "_jlet"  :: "'t conditional_action \<Rightarrow> jlet"             ("(_)")
  ""         :: "jlet \<Rightarrow> jlets"             ("_")
  "_jlets" :: "jlet \<Rightarrow> jlets \<Rightarrow> jlets" ("_,/ _")
  "_jUpdate" :: "'a \<Rightarrow> jlets \<Rightarrow> 'a"            ("_\<lbrace>\<^bsub>c\<^esub>/(_)\<rbrace>" [1000,0] 1000)

translations
  "_jUpdate ta (_jlets b bs)"  == "_jUpdate (_jUpdate ta b) bs"
  "ta\<lbrace>\<^bsub>c\<^esub>nt\<rbrace>"                    == "CONST ta_update_Conditional ta nt"


nonterminals
  wslets wslet
syntax
  "_wslet"  :: "('t, 'w) wait_set_action \<Rightarrow> wslet"             ("(_)")
  ""         :: "wslet \<Rightarrow> wslets"             ("_")
  "_wslets" :: "wslet \<Rightarrow> wslets \<Rightarrow> wslets" ("_,/ _")
  "_wsUpdate" :: "'a \<Rightarrow> wslets \<Rightarrow> 'a"            ("_\<lbrace>\<^bsub>w\<^esub>/(_)\<rbrace>" [1000,0] 1000)

translations
  "_wsUpdate ta (_wslets b bs)"  == "_wsUpdate (_wsUpdate ta b) bs"
  "ta\<lbrace>\<^bsub>w\<^esub>ws\<rbrace>"                      == "CONST ta_update_wait_set ta ws"

nonterminals
  oalets oalet
syntax
  "_oalet"  :: "'o \<Rightarrow> oalet"             ("(_)")
  ""         :: "oalet \<Rightarrow> oalets"             ("_")
  "_oalets" :: "oalet \<Rightarrow> oalets \<Rightarrow> oalets" ("_,/ _")
  "_oaUpdate" :: "'a \<Rightarrow> oalets \<Rightarrow> 'a"      ("_\<lbrace>\<^bsub>o\<^esub>/(_)\<rbrace>" [1000,0] 1000)

translations
  "_oaUpdate ta (_oalets b bs)"  == "_oaUpdate (_oaUpdate ta b) bs"
  "ta\<lbrace>\<^bsub>o\<^esub>os\<rbrace>"                         == "CONST ta_update_obs ta os"

lemmas ta_upd_simps =
  ta_update_locks.simps ta_update_NewThread.simps ta_update_Conditional.simps
  ta_update_wait_set.simps ta_update_obs.simps

declare ta_upd_simps [simp del]

types
  't lock = "('t \<times> nat) option"
  ('l,'t) locks = "'l \<Rightarrow>\<^isub>f 't lock"
  'l released_locks = "'l \<Rightarrow>\<^isub>f nat"
  ('l,'t,'x) thread_info = "'t \<rightharpoonup> ('x \<times> 'l released_locks)"
  ('w,'t) wait_sets = "'t \<rightharpoonup> 'w"
  ('l,'t,'x,'m,'w) state = "('l,'t) locks \<times> (('l,'t,'x) thread_info \<times> 'm) \<times> ('w,'t) wait_sets"
translations
  (type) "('l, 't) locks" <= (type) "'l \<Rightarrow>\<^isub>f ('t \<times> nat) option"
  (type) "('l, 't, 'x) thread_info" <= (type) "'t \<rightharpoonup> ('x \<times> ('l \<Rightarrow>\<^isub>f nat))"

(* pretty printing for state type *)
print_translation {*
  let
    fun tr'
       [Const (@{type_syntax finfun}, _) $ l1 $
        (Const (@{type_syntax option}, _) $
          (Const (@{type_syntax "*"}, _) $ t1 $ Const (@{type_syntax nat}, _))),
        Const (@{type_syntax "*"}, _) $
          (Const (@{type_syntax "*"}, _) $
            (Const (@{type_syntax fun}, _) $ t2 $
              (Const (@{type_syntax option}, _) $
                (Const (@{type_syntax "*"}, _) $ x $
                  (Const (@{type_syntax finfun}, _) $ l2 $ Const (@{type_syntax nat}, _))))) $ m) $
               (Const (@{type_syntax fun}, _) $ t3 $ (Const (@{type_syntax option}, _) $ w))] =
      if t1 = t2 andalso t1 = t3 andalso l1 = l2
      then Syntax.const @{type_syntax state} $ l1 $ t1 $ x $ m $ w
      else raise Match;
  in [(@{type_syntax "*"}, tr')]
  end
*}
(* typ "('l,'t,'x,'m,'w) state" *)

lemma ta_upd_proj_simps [simp]:
  shows ta_obs_proj_simps:
  "\<lbrace>ta\<lbrace>\<^bsub>o\<^esub> obs \<rbrace>\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" "\<lbrace>ta\<lbrace>\<^bsub>o\<^esub> obs \<rbrace>\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" "\<lbrace>ta\<lbrace>\<^bsub>o\<^esub> obs \<rbrace>\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" "\<lbrace>ta\<lbrace>\<^bsub>o\<^esub> obs \<rbrace>\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" "\<lbrace>ta\<lbrace>\<^bsub>o\<^esub> obs \<rbrace>\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> @ [obs]"
  and ta_lock_proj_simps:
  "\<lbrace>ta\<lbrace>\<^bsub>l\<^esub> x\<rightarrow>l \<rbrace>\<rbrace>\<^bsub>l\<^esub> = (let ls = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> in ls(\<^sup>f l := ls\<^sub>f l @ [x]))"
  "\<lbrace>ta\<lbrace>\<^bsub>l\<^esub> x\<rightarrow>l \<rbrace>\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" "\<lbrace>ta\<lbrace>\<^bsub>l\<^esub> x\<rightarrow>l \<rbrace>\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" "\<lbrace>ta\<lbrace>\<^bsub>l\<^esub> x\<rightarrow>l \<rbrace>\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" "\<lbrace>ta\<lbrace>\<^bsub>l\<^esub> x\<rightarrow>l \<rbrace>\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and ta_thread_proj_simps:
  "\<lbrace>ta\<lbrace>\<^bsub>t\<^esub> t \<rbrace>\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" "\<lbrace>ta\<lbrace>\<^bsub>t\<^esub> t \<rbrace>\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> @ [t]" "\<lbrace>ta\<lbrace>\<^bsub>t\<^esub> t \<rbrace>\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" "\<lbrace>ta\<lbrace>\<^bsub>t\<^esub> t \<rbrace>\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" "\<lbrace>ta\<lbrace>\<^bsub>t\<^esub> t \<rbrace>\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and ta_wset_proj_simps:
  "\<lbrace>ta\<lbrace>\<^bsub>w\<^esub> w \<rbrace>\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" "\<lbrace>ta\<lbrace>\<^bsub>w\<^esub> w \<rbrace>\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" "\<lbrace>ta\<lbrace>\<^bsub>w\<^esub> w \<rbrace>\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> @ [w]" "\<lbrace>ta\<lbrace>\<^bsub>w\<^esub> w \<rbrace>\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" "\<lbrace>ta\<lbrace>\<^bsub>w\<^esub> w \<rbrace>\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and ta_cond_proj_simps:
  "\<lbrace>ta\<lbrace>\<^bsub>c\<^esub> c \<rbrace>\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" "\<lbrace>ta\<lbrace>\<^bsub>c\<^esub> c \<rbrace>\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" "\<lbrace>ta\<lbrace>\<^bsub>c\<^esub> c \<rbrace>\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>" "\<lbrace>ta\<lbrace>\<^bsub>c\<^esub> c \<rbrace>\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> @ [c]" "\<lbrace>ta\<lbrace>\<^bsub>c\<^esub> c \<rbrace>\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
by(cases ta, simp add: ta_upd_simps)+

abbreviation no_wait_locks :: "'l \<Rightarrow>\<^isub>f nat"
where "no_wait_locks \<equiv> (\<lambda>\<^isup>f 0)"

lemma neq_no_wait_locks_conv:
  "ln \<noteq> no_wait_locks \<longleftrightarrow> (\<exists>l. ln\<^sub>f l > 0)"
by(auto simp add: expand_finfun_eq expand_fun_eq)

lemma neq_no_wait_locksE:
  assumes "ln \<noteq> no_wait_locks" obtains l where "ln\<^sub>f l > 0"
using assms
by(auto simp add: neq_no_wait_locks_conv)


definition locks :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('l,'t) locks" where
  "locks lstsmws \<equiv> fst lstsmws"

definition thr :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('l,'t,'x) thread_info" where
  "thr lstsmws \<equiv> fst (fst (snd lstsmws))"

definition shr :: "('l,'t,'x,'m,'w) state \<Rightarrow> 'm" where
  "shr lstsmws \<equiv> snd (fst (snd lstsmws))"

definition wset :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('w,'t) wait_sets" where
  "wset lstsmws \<equiv> snd (snd lstsmws)"

lemma locks_conv [simp]: "locks (ls, tsmws) = ls"
by(simp add: locks_def)

lemma thr_conv [simp]: "thr (ls, (ts, m), ws) = ts"
by(simp add: thr_def)

lemma shr_conv [simp]: "shr (ls, (ts, m), ws) = m"
by(simp add: shr_def)

lemma wset_conv [simp]: "wset (ls, (ts, m), ws) = ws"
by(simp add: wset_def)

primrec convert_new_thread_action :: "('x \<Rightarrow> 'x') \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> ('t,'x','m) new_thread_action"
where
  "convert_new_thread_action f (NewThread t x m) = NewThread t (f x) m"
| "convert_new_thread_action f (ThreadExists t) = ThreadExists t"
| "convert_new_thread_action f NewThreadFail = NewThreadFail"

lemma convert_new_thread_action_inv [simp]:
  "NewThread t x h = convert_new_thread_action f nta \<longleftrightarrow> (\<exists>x'. nta = NewThread t x' h \<and> x = f x')"
  "ThreadExists t = convert_new_thread_action f nta \<longleftrightarrow> nta = ThreadExists t"
  "NewThreadFail = convert_new_thread_action f nta \<longleftrightarrow> nta = NewThreadFail"
  "convert_new_thread_action f nta = NewThread t x h \<longleftrightarrow> (\<exists>x'. nta = NewThread t x' h \<and> x = f x')"
  "convert_new_thread_action f nta = ThreadExists t \<longleftrightarrow> nta = ThreadExists t"
  "convert_new_thread_action f nta = NewThreadFail \<longleftrightarrow> nta = NewThreadFail"
by(cases nta, auto)+

lemma convert_new_thread_action_eqI: 
  "\<lbrakk> \<And>t x m. nta = NewThread t x m \<Longrightarrow> nta' = NewThread t (f x) m;
     \<And>t. nta = ThreadExists t \<Longrightarrow> nta' = ThreadExists t;
     nta = NewThreadFail \<Longrightarrow> nta' = NewThreadFail \<rbrakk>
  \<Longrightarrow> convert_new_thread_action f nta = nta'"
apply(cases nta)
apply auto
done

lemma convert_new_thread_action_compose [simp]:
  "convert_new_thread_action f (convert_new_thread_action g ta) = convert_new_thread_action (f o g) ta"
apply(cases ta)
apply(simp_all add: convert_new_thread_action_def)
done


definition convert_extTA :: "('x \<Rightarrow> 'x') \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('l,'t,'x','m,'w,'o) thread_action"
where "convert_extTA f ta = (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>, map (convert_new_thread_action f) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>, snd (snd ta))"

lemma convert_extTA_simps [simp]:
  "convert_extTA f \<epsilon> = \<epsilon>"
  "\<lbrace>convert_extTA f ta\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
  "\<lbrace>convert_extTA f ta\<rbrace>\<^bsub>t\<^esub> = map (convert_new_thread_action f) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  "\<lbrace>convert_extTA f ta\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
  "\<lbrace>convert_extTA f ta\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
  "convert_extTA f (las, tas, was, cas) = (las, map (convert_new_thread_action f) tas, was, cas)"
apply(simp_all add: convert_extTA_def)
apply(cases ta, simp)+
done

lemma convert_extTA_eq_conv:
  "convert_extTA f ta = ta' \<longleftrightarrow>
   \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<and> \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> \<and> \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<and> length \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = length \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> \<and> 
   (\<forall>n < length \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>. convert_new_thread_action f (\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n) = \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> ! n)"
apply(cases ta, cases ta')
apply(auto simp add: convert_extTA_def map_eq_all_nth_conv)
done

lemma convert_extTA_compose [simp]:
  "convert_extTA f (convert_extTA g ta) = convert_extTA (f o g) ta"
by(simp add: convert_extTA_def)

lemma obs_a_convert_extTA [simp]: "obs_a (convert_extTA f ta) = obs_a ta"
by(cases ta) simp

datatype ('l,'o) observable =
    ReacquireLocks "'l released_locks"
  | Observable 'o

abbreviation observable_of :: "'o list \<Rightarrow> ('l, 'o) observable list"
where "observable_of obs \<equiv> map Observable obs"

definition observable_ta_of :: "('l,'t,'x,'m,'w,'o list) thread_action \<Rightarrow> ('l, 'o) observable list \<Rightarrow> ('l,'t,'x,'m,'w,('l,'o) observable list) thread_action"
where "observable_ta_of ta obs = (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>, \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>, \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>, \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>, observable_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> @ obs)"

lemma locks_a_observable_ta_of [simp]:
  "\<lbrace>observable_ta_of ta obs\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
by(simp add: observable_ta_of_def)

lemma thr_a_observable_ta_of [simp]:
  "\<lbrace>observable_ta_of ta obs\<rbrace>\<^bsub>t\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
by(simp add: observable_ta_of_def)

lemma cond_a_observable_ta_of [simp]:
  "\<lbrace>observable_ta_of ta obs\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
by(simp add: observable_ta_of_def)

lemma wset_a_observable_ta_of [simp]:
  "\<lbrace>observable_ta_of ta obs\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
by(simp add: observable_ta_of_def)

lemma obs_a_observable_ta_of [simp]:
  "\<lbrace>observable_ta_of ta obs\<rbrace>\<^bsub>o\<^esub> = observable_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> @ obs"
by(simp add: observable_ta_of_def)

lemma observable_of_inject [simp]:
  "observable_of obs = observable_of obs' \<longleftrightarrow> obs = obs'"
apply(induct obs arbitrary: obs')
 apply fastsimp
apply(case_tac obs')
apply fastsimp+
done

lemma observable_ta_of_inject1 [simp]:
  "observable_ta_of ta obs = observable_ta_of ta' obs \<longleftrightarrow> ta = ta'"  
by(cases ta, cases ta')(auto simp add: observable_ta_of_def)

lemma observable_ta_of_inject2 [simp]:
  "observable_ta_of ta obs = observable_ta_of ta obs' \<longleftrightarrow> obs = obs'"  
by(auto simp add: observable_ta_of_def)

lemma observable_ta_of_empty_Nil [simp]: "observable_ta_of \<epsilon> [] = \<epsilon>"
by(simp add: observable_ta_of_def)

lemma observable_ta_of_eq_empty [simp]: 
  "observable_ta_of ta obs = \<epsilon> \<longleftrightarrow> ta = \<epsilon> \<and> obs = []"
by(cases ta)(simp add: observable_ta_of_def)

lemma empty_eq_observable_ta_of [simp]: 
  "\<epsilon> = observable_ta_of ta obs \<longleftrightarrow> ta = \<epsilon> \<and> obs = []"
by(cases ta)(auto simp add: observable_ta_of_def)

definition is_Interrupted_ta :: "('l,'t,'x,'m,'w,'o list) thread_action \<Rightarrow> bool"
where "is_Interrupted_ta ta \<longleftrightarrow> \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = (\<lambda>\<^isup>f []) \<and> \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = [] \<and> \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = [Interrupted] \<and> \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = []"


types
  ('l,'t,'x,'m,'w,'o) semantics =
    "'t \<Rightarrow> 'x \<times> 'm \<Rightarrow> ('l,'t,'x,'m,'w,'o list) thread_action \<Rightarrow> 'x \<times> 'm \<Rightarrow> bool"

(* pretty printing for semantics *)
print_translation {*
  let
    fun tr'
       [t4,
        Const (@{type_syntax fun}, _) $
          (Const (@{type_syntax "*"}, _) $ x1 $ m1) $
          (Const (@{type_syntax fun}, _) $
            (Const (@{type_syntax "*"}, _) $
              (Const (@{type_syntax finfun}, _) $ l $
                (Const (@{type_syntax list}, _) $ Const (@{type_syntax lock_action}, _))) $
              (Const (@{type_syntax "*"}, _) $
                (Const (@{type_syntax list}, _) $ (Const (@{type_syntax new_thread_action}, _) $ t1 $ x2 $ m2)) $
                (Const (@{type_syntax "*"}, _) $
                  (Const (@{type_syntax list}, _) $ (Const (@{type_syntax conditional_action}, _) $ t2)) $
                  (Const (@{type_syntax "*"}, _) $
                    (Const (@{type_syntax list}, _) $ (Const (@{type_syntax wait_set_action}, _) $ t3 $ w)) $
                    (Const (@{type_syntax list}, _) $ o1))))) $
            (Const (@{type_syntax fun}, _) $ (Const (@{type_syntax "*"}, _) $ x3 $ m3) $
              Const (@{type_syntax bool}, _)))] =
      if x1 = x2 andalso x1 = x3 andalso m1 = m2 andalso m1 = m3 andalso t1 = t2 andalso t2 = t3 andalso t3 = t4
      then Syntax.const @{type_syntax semantics} $ l $ t1 $ x1 $ m1 $ w $ o1
      else raise Match;
  in [(@{type_syntax fun}, tr')]
  end
*}
(* typ "('l,'t,'x,'m,'w,'o) semantics" *)

types ('a, 'b) trsys = "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
types ('a, 'b) bisim = "'a \<Rightarrow> 'b \<Rightarrow> bool"

locale trsys = 
  fixes trsys :: "('s, 'tl) trsys" ("_/ -_\<rightarrow>/ _" [50, 0, 50] 60)
begin

abbreviation Trsys :: "('s, 'tl list) trsys" ("_/ -_\<rightarrow>*/ _" [50,0,50] 60)
where "\<And>tl. s -tl\<rightarrow>* s' \<equiv> rtrancl3p trsys s tl s'"

end

end