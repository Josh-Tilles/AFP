(*  Title:      JinjaThreads/Common/CallExpr.thy
    Author:     Andreas Lochbihler
*)

header {*
  \chapter{Compilation}\label{cha:comp}
  \isaheader{Method calls in expressions} 
*}

theory CallExpr imports 
  "../J/Expr"
begin

primrec inline_call :: "('a,'b) exp \<Rightarrow> ('a,'b) exp \<Rightarrow> ('a,'b) exp"
  and inline_calls :: "('a,'b) exp \<Rightarrow> ('a,'b) exp list \<Rightarrow> ('a,'b) exp list"
where
  "inline_call f (new C) = new C"
| "inline_call f (newA T\<lfloor>e\<rceil>) = newA T\<lfloor>inline_call f e\<rceil>"
| "inline_call f (Cast C e) = Cast C (inline_call f e)"
| "inline_call f (e instanceof T) = (inline_call f e) instanceof T"
| "inline_call f (Val v) = Val v"
| "inline_call f (Var V) = Var V"
| "inline_call f (V:=e) = V := inline_call f e"
| "inline_call f (e \<guillemotleft>bop\<guillemotright> e') = (if is_val e then (e \<guillemotleft>bop\<guillemotright> inline_call f e') else (inline_call f e \<guillemotleft>bop\<guillemotright> e'))"
| "inline_call f (a\<lfloor>i\<rceil>) = (if is_val a then a\<lfloor>inline_call f i\<rceil> else (inline_call f a)\<lfloor>i\<rceil>)"
| "inline_call f (AAss a i e) =
   (if is_val a then if is_val i then AAss a i (inline_call f e) else AAss a (inline_call f i) e
    else AAss (inline_call f a) i e)"
| "inline_call f (a\<bullet>length) = inline_call f a\<bullet>length"
| "inline_call f (e\<bullet>F{D}) = inline_call f e\<bullet>F{D}"
| "inline_call f (FAss e F D e') = (if is_val e then FAss e F D (inline_call f e') else FAss (inline_call f e) F D e')"
| "inline_call f (e\<bullet>M(es)) = 
   (if is_val e then if is_vals es \<and> is_addr e then f else e\<bullet>M(inline_calls f es) else inline_call f e\<bullet>M(es))"
| "inline_call f ({V:T=vo; e}) = {V:T=vo; inline_call f e}"
| "inline_call f (sync\<^bsub>V\<^esub> (o') e) = sync\<^bsub>V\<^esub> (inline_call f o') e"
| "inline_call f (insync\<^bsub>V\<^esub> (a) e) = insync\<^bsub>V\<^esub> (a) (inline_call f e)"
| "inline_call f (e;;e') = inline_call f e;;e'"
| "inline_call f (if (b) e else e') = (if (inline_call f b) e else e')"
| "inline_call f (while (b) e) = while (b) e"
| "inline_call f (throw e) = throw (inline_call f e)"
| "inline_call f (try e1 catch(C V) e2) = try inline_call f e1 catch(C V) e2"

| "inline_calls f [] = []"
| "inline_calls f (e#es) = (if is_val e then e # inline_calls f es else inline_call f e # es)"

primrec fold_es :: "expr \<Rightarrow> expr list \<Rightarrow> expr" where
  "fold_es e [] = e"
| "fold_es e (e' # es) = fold_es (inline_call e e') es"

definition is_call :: "('a, 'b) exp \<Rightarrow> bool"
where "is_call e = (call e \<noteq> None)"

definition is_calls :: "('a, 'b) exp list \<Rightarrow> bool"
where "is_calls es = (calls es \<noteq> None)"



lemma inline_calls_map_Val_append [simp]:
  "inline_calls f (map Val vs @ es) = map Val vs @ inline_calls f es"
by(induct vs, auto)

lemma inline_call_eq_Val_aux:
  "inline_call e E = Val v \<Longrightarrow> call E = \<lfloor>aMvs\<rfloor> \<Longrightarrow> e = Val v"
by(induct E)(auto split: split_if_asm)

lemmas inline_call_eq_Val [dest] = inline_call_eq_Val_aux inline_call_eq_Val_aux[OF sym, THEN sym]

lemma inline_calls_eq_empty [simp]: "inline_calls e es = [] \<longleftrightarrow> es = []"
by(cases es, auto)

lemma inline_calls_map_Val [simp]: "inline_calls e (map Val vs) = map Val vs"
by(induct vs) auto

lemma  fixes E :: "('a,'b) exp" and Es :: "('a,'b) exp list"
  shows inline_call_eq_Throw [dest]: "inline_call e E = Throw a \<Longrightarrow> call E = \<lfloor>aMvs\<rfloor> \<Longrightarrow> e = Throw a \<or> e = addr a"
  and True
by(induct E and Es)(fastsimp split:split_if_asm)+

lemma Throw_eq_inline_call_eq [dest]:
  "inline_call e E = Throw a \<Longrightarrow> call E = \<lfloor>aMvs\<rfloor> \<Longrightarrow> Throw a = e \<or> addr a = e"
by(auto dest: inline_call_eq_Throw[OF sym])

lemma is_vals_inline_calls [dest]:
  "\<lbrakk> is_vals (inline_calls e es); calls es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> is_val e"
by(induct es, auto split: split_if_asm)

lemma [dest]: "\<lbrakk> inline_calls e es = map Val vs; calls es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> is_val e"
              "\<lbrakk> map Val vs = inline_calls e es; calls es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> is_val e"
by(fastsimp intro!: is_vals_inline_calls del: is_val.intros simp add: is_vals_conv elim: sym)+

lemma inline_calls_eq_Val_Throw [dest]:
  "\<lbrakk> inline_calls e es = map Val vs @ Throw a # es'; calls es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> e = Throw a \<or> is_val e"
apply(induct es arbitrary: vs a es')
apply(auto simp add: Cons_eq_append_conv split: split_if_asm)
done

lemma Val_Throw_eq_inline_calls [dest]:
  "\<lbrakk> map Val vs @ Throw a # es' = inline_calls e es; calls es = \<lfloor>aMvs\<rfloor> \<rbrakk> \<Longrightarrow> Throw a = e \<or> is_val e"
by(auto dest: inline_calls_eq_Val_Throw[OF sym])

declare option.split [split del] split_if_asm [split]  split_if [split del]

lemma call_inline_call [simp]:
  "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> call (inline_call {v:T=vo; e'} e) = call e'"
  "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> calls (inline_calls {v:T=vo;e'} es) = call e'"
apply(induct e and es)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp split: split_if)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp split: split_if)
apply(clarsimp)
 apply(fastsimp split: split_if)
apply(fastsimp split: split_if)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp split: split_if)
apply(fastsimp split: split_if)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp)
apply(fastsimp split: split_if)
done

declare option.split [split] split_if [split] split_if_asm [split del]

lemma fv_inline_call: "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> fv (inline_call e' e) \<subseteq> fv e \<union> fv e'"
  and fvs_inline_calls: "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> fvs (inline_calls e' es) \<subseteq> fvs es \<union> fv e'"
by(induct e and es)(fastsimp split: split_if_asm)+

lemma contains_insync_inline_call_conv:
  "contains_insync (inline_call e e') \<longleftrightarrow> contains_insync e \<and> call e' \<noteq> None \<or> contains_insync e'"
  and contains_insyncs_inline_calls_conv:
   "contains_insyncs (inline_calls e es') \<longleftrightarrow> contains_insync e \<and> calls es' \<noteq> None \<or> contains_insyncs es'"
by(induct e' and es')(auto split: split_if_asm simp add: is_vals_conv)

lemma contains_insync_inline_call [simp]:
  "call e' = \<lfloor>aMvs\<rfloor> \<Longrightarrow> contains_insync (inline_call e e') \<longleftrightarrow> contains_insync e \<or> contains_insync e'"
  and contains_insyncs_inline_calls [simp]:
  "calls es' = \<lfloor>aMvs\<rfloor> \<Longrightarrow> contains_insyncs (inline_calls e es') \<longleftrightarrow> contains_insync e \<or> contains_insyncs es'"
by(simp_all add: contains_insync_inline_call_conv contains_insyncs_inline_calls_conv)

lemma fold_es_append [simp]:
  "fold_es e (es @ es') = fold_es (fold_es e es) es'"
by(induct es arbitrary: e, auto)

lemma fold_es_conv_foldl:
  "fold_es e es = foldl inline_call e es"
by(induct es arbitrary: e) simp_all

lemma fv_fold_es: "list_all is_call es \<Longrightarrow> fv (fold_es e es) \<subseteq> fvs (e # es)"
by(induct es arbitrary: e) (auto simp add: is_call_def dest: fv_inline_call)

lemma final_inline_callD: "\<lbrakk> final (inline_call E e); is_call e \<rbrakk> \<Longrightarrow> final E"
by(induct e)(auto simp add: is_call_def split: split_if_asm)

lemma fold_es_finalD: "\<lbrakk> final (fold_es e es); list_all is_call es \<rbrakk> \<Longrightarrow> final e"
by(induct es arbitrary: e)(auto dest: final_inline_callD)

context heap_base begin

definition synthesized_call :: "'m prog \<Rightarrow> 'heap \<Rightarrow> (addr \<times> mname \<times> val list) \<Rightarrow> bool"
where "synthesized_call P h = (\<lambda>(a, M, vs). \<exists>T. typeof_addr h a = \<lfloor>T\<rfloor> \<and> is_external_call P T M)"

lemma synthesized_call_conv:
  "synthesized_call P h (a, M, vs) = (\<exists>T. typeof_addr h a = \<lfloor>T\<rfloor> \<and> is_external_call P T M)"
by(simp add: synthesized_call_def)

end

end