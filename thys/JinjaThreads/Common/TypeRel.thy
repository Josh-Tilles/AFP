(*  Title:      JinjaThreads/Common/TypeRel.thy
    Author:     Tobias Nipkow, Andreas Lochbihler

    Based on the Jinja theory Common/Type.thy by Tobias Nipkow

*)

header {* \isaheader{Relations between Jinja Types} *}

theory TypeRel imports Decl begin

subsection{* The subclass relations *}

inductive subcls1 :: "'m prog \<Rightarrow> cname \<Rightarrow> cname \<Rightarrow> bool" ("_ \<turnstile> _ \<prec>\<^sup>1 _" [71, 71, 71] 70)
  for P :: "'m prog"
where subcls1I: "\<lbrakk> class P C = Some (D, rest); C \<noteq> Object \<rbrakk> \<Longrightarrow> P \<turnstile> C \<prec>\<^sup>1 D"

abbreviation subcls :: "'m prog \<Rightarrow> cname \<Rightarrow> cname \<Rightarrow> bool" ("_ \<turnstile> _ \<preceq>\<^sup>* _"  [71,71,71] 70)
where "P \<turnstile> C \<preceq>\<^sup>* D \<equiv> (subcls1 P)\<^sup>*\<^sup>* C D"

lemma subcls1D:
  "P \<turnstile> C \<prec>\<^sup>1 D \<Longrightarrow> C \<noteq> Object \<and> (\<exists>fs ms. class P C = Some (D,fs,ms))"
(*<*)by(erule subcls1.induct)(fastsimp simp add:is_class_def)(*>*)

lemma [iff]: "\<not> P \<turnstile> Object \<prec>\<^sup>1 C"
(*<*)by(fastsimp dest:subcls1D)(*>*)

lemma [iff]: "(P \<turnstile> Object \<preceq>\<^sup>* C) = (C = Object)"
(*<*)
apply(rule iffI)
 apply(erule converse_rtranclpE)
  apply simp_all
done
(*>*)

lemma finite_subcls1: "finite ({(C, D). P \<turnstile> C \<prec>\<^sup>1 D})"
(*<*)
apply(subgoal_tac "{(C, D). P \<turnstile> C \<prec>\<^sup>1 D} =
 (SIGMA C:{C. is_class P C}. {D. C\<noteq>Object \<and> fst (the (class P C))=D})")
 prefer 2
 apply(fastsimp simp:is_class_def dest: subcls1D elim: subcls1I)
apply simp
apply(rule finite_SigmaI [OF finite_is_class])
apply(rule_tac B = "{fst (the (class P C))}" in finite_subset)
apply  auto
done
(*>*)

lemma finite_subcls1':
  "finite ({(D, C). P \<turnstile> C \<prec>\<^sup>1 D})"
apply(subst finite_converse[symmetric])
apply(simp add: converse_def del: finite_converse)
apply(rule finite_subcls1)
done

lemma subcls_is_class: "(subcls1 P)\<^sup>+\<^sup>+ C D \<Longrightarrow> is_class P C"
apply (unfold is_class_def)
apply(erule tranclp_trans_induct)
apply (auto dest!: subcls1D)
done

lemma subcls_is_class1 [rule_format]: "P \<turnstile> C \<preceq>\<^sup>* D \<Longrightarrow> is_class P D \<longrightarrow> is_class P C"
apply (unfold is_class_def)
apply (erule rtranclp_induct)
apply  (drule_tac [2] subcls1D)
apply  auto
done

subsection{* The subtype relations *}

inductive widen :: "'m prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ \<le> _"   [71,71,71] 70)
  for P :: "'m prog"
where 
  widen_refl[iff]: "P \<turnstile> T \<le> T"
| widen_subcls: "P \<turnstile> C \<preceq>\<^sup>* D  \<Longrightarrow>  P \<turnstile> Class C \<le> Class D"
| widen_null[iff]: "P \<turnstile> NT \<le> Class C"
| widen_null_array[iff]: "P \<turnstile> NT \<le> Array A"
| widen_array_object: "is_type P A \<Longrightarrow> P \<turnstile> Array A \<le> Class Object"
| widen_array_array: "\<lbrakk> P \<turnstile> A \<le> B; \<not> is_NT_Array A \<rbrakk> \<Longrightarrow> P \<turnstile> Array A \<le> Array B"

abbreviation
  widens :: "'m prog \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> bool" ("_ \<turnstile> _ [\<le>] _" [71,71,71] 70)
where
  "P \<turnstile> Ts [\<le>] Ts' == list_all2 (widen P) Ts Ts'"

lemma [iff]: "(P \<turnstile> T \<le> Void) = (T = Void)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma [iff]: "(P \<turnstile> T \<le> Boolean) = (T = Boolean)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma [iff]: "(P \<turnstile> T \<le> Integer) = (T = Integer)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma [iff]: "(P \<turnstile> Void \<le> T) = (T = Void)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma [iff]: "(P \<turnstile> Boolean \<le> T) = (T = Boolean)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma [iff]: "(P \<turnstile> Integer \<le> T) = (T = Integer)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma widen_is_type: "\<lbrakk> P \<turnstile> A \<le> B; A \<noteq> B \<rbrakk> \<Longrightarrow> is_type P A"
proof(induct rule: widen.induct)
  case (widen_subcls C D)
  hence "(subcls1 P)\<^sup>+\<^sup>+ C D"
    by(auto elim: rtranclp.cases dest: rtranclp_into_tranclp1)
  thus ?case by(auto intro: subcls_is_class)
qed(simp_all)

lemma Class_widen: "P \<turnstile> Class C \<le> T  \<Longrightarrow>  \<exists>D. T = Class D"
by(erule widen.cases, auto)

lemma Array_Array_widen:
  "P \<turnstile> Array T \<le> Array U \<Longrightarrow> P \<turnstile> T \<le> U \<and> (is_NT_Array T \<or> is_NT_Array U \<longrightarrow> T = U)"
proof -
  { fix A B
    have "\<lbrakk> P \<turnstile> A \<le> B; A = Array T; B = Array U \<rbrakk> \<Longrightarrow> P \<turnstile> T \<le> U \<and> (is_NT_Array T \<or> is_NT_Array U \<longrightarrow> T = U)"
    proof(induct arbitrary: T U rule: widen.induct)
      case (widen_array_array A B T U)
      note IH = `\<And>T U. \<lbrakk>A = T\<lfloor>\<rceil>; B = U\<lfloor>\<rceil>\<rbrakk> \<Longrightarrow> P \<turnstile> T \<le> U \<and> (is_NT_Array T \<or> is_NT_Array U \<longrightarrow> T = U)`
      from `A\<lfloor>\<rceil> = T\<lfloor>\<rceil>` `B\<lfloor>\<rceil> = U\<lfloor>\<rceil>` have AT: "A = T" and BU: "B = U" by auto
      with `\<not> is_NT_Array A` have nt: "\<not> is_NT_Array T" by simp
      from AT BU `P \<turnstile> A \<le> B` have sub: "P \<turnstile> T \<le> U" by simp
      hence "is_NT_Array U \<Longrightarrow> T = U"
      proof(rule widen.cases)
	fix A' B'
	assume ntU: "is_NT_Array U"
	  and T: "T = A'\<lfloor>\<rceil>"
	  and U: "U = B'\<lfloor>\<rceil>"
	from T U AT BU have "P \<turnstile> A' \<le> B' \<and> (is_NT_Array A' \<or> is_NT_Array B'  \<longrightarrow> A' = B')"
	  by -(rule IH, auto)
	with ntU T U show "T = U" by auto
      qed(insert nt, auto)
      with nt AT BU sub show ?case by(clarsimp)
    qed(auto) }
  thus "P \<turnstile> Array T \<le> Array U \<Longrightarrow> P \<turnstile> T \<le> U \<and> (is_NT_Array T \<or> is_NT_Array U \<longrightarrow> T = U)" by blast
qed

lemma widen_Array: "(P \<turnstile> T \<le> U\<lfloor>\<rceil>) \<longleftrightarrow> (T = NT \<or> (\<exists>V. T = V\<lfloor>\<rceil> \<and> P \<turnstile> V \<le> U \<and> (is_NT_Array V \<longrightarrow> V = U)))"
proof (induct T)
  case (Class C)
  thus ?case by(auto elim: widen.cases)
next
  case (Array T)
  { assume "P \<turnstile> T\<lfloor>\<rceil> \<le> U\<lfloor>\<rceil>"
    hence "P \<turnstile> T \<le> U" "is_NT_Array T \<Longrightarrow> U = T"
      by(auto elim: widen.cases) }
  moreover
  { assume "P \<turnstile> T \<le> U" "is_NT_Array T \<Longrightarrow> U = T"
    hence "P \<turnstile> T\<lfloor>\<rceil> \<le> U\<lfloor>\<rceil>"
      by(cases "is_NT_Array T", auto intro!: widen.intros) }
  ultimately have "(P \<turnstile> T\<lfloor>\<rceil> \<le> U\<lfloor>\<rceil>) = (P \<turnstile> T \<le> U \<and> (is_NT_Array T \<longrightarrow> T = U))"
    by(blast)
  thus ?case by auto
qed(simp_all)

lemma Array_widen: "P \<turnstile> Array A \<le> T \<Longrightarrow> (\<exists>B. T = Array B \<and> (is_NT_Array A \<longrightarrow> A = B)) \<or> T = Class Object"
by(auto elim: widen.cases)

lemma [iff]: "(P \<turnstile> T \<le> NT) = (T = NT)"
(*<*)
apply(induct T)
apply(auto dest:Class_widen Array_widen)
done
(*>*)

lemma widen_NT_Array:
  assumes NT: "is_NT_Array T"
  shows "P \<turnstile> T\<lfloor>\<rceil> \<le> U \<longleftrightarrow> (U = T\<lfloor>\<rceil>) \<or> (U = Class Object)"
proof(rule iffI)
  assume "P \<turnstile> T\<lfloor>\<rceil> \<le> U"
  moreover
  { fix T'
    have "\<lbrakk> P \<turnstile> T' \<le> U; T' = T\<lfloor>\<rceil>; is_NT_Array T' \<rbrakk> \<Longrightarrow> U = T' \<or> U = Class Object"
      by(induct rule: widen.induct, auto) }
  ultimately show "(U = T\<lfloor>\<rceil>) \<or> (U = Class Object)" using NT by auto
next
  assume "U = T\<lfloor>\<rceil> \<or> U = Class Object"
  thus "P \<turnstile> T\<lfloor>\<rceil> \<le> U" using NT
    by(auto intro!: widen_array_object NT_Array_is_type)
qed

lemma Class_widen_Class [iff]: "(P \<turnstile> Class C \<le> Class D) = (P \<turnstile> C \<preceq>\<^sup>* D)"
(*<*)
apply (rule iffI)
apply (erule widen.cases)
apply (auto elim: widen_subcls)
done
(*>*)


lemma widen_Class: "(P \<turnstile> T \<le> Class C) = (T = NT \<or> (\<exists>D. T = Class D \<and> P \<turnstile> D \<preceq>\<^sup>* C) \<or> (C = Object \<and> (\<exists>A. T = Array A \<and> is_type P A)))"
proof(induct T)
  case (Array T)
  have "P \<turnstile> T\<lfloor>\<rceil> \<le> Class C = (C = Object \<and> is_type P T)" 
  proof(rule iffI)
    assume widen: "P \<turnstile> T\<lfloor>\<rceil> \<le> Class C"
    hence "C = Object"
      by(auto dest!: Array_widen)
    moreover from widen have "is_type P T" by(auto dest: widen_is_type)
    ultimately show "C = Object \<and> is_type P T" ..
  next
    assume C: "C = Object \<and> is_type P T"
    hence "P \<turnstile> T\<lfloor>\<rceil> \<le> Class Object"
      by(auto intro: widen.intros)
    with C show "P \<turnstile> T\<lfloor>\<rceil> \<le> Class C" by simp
  qed
  thus ?case by simp
qed(fastsimp)+

lemma NT_widen:
  "P \<turnstile> NT \<le> T = (T = NT \<or> (\<exists>C. T = Class C) \<or> (\<exists>U. T = U\<lfloor>\<rceil>))"
(*<*) by (cases T) auto (*>*)

lemma Class_widen2: "P \<turnstile> Class C \<le> T = (\<exists>D. T = Class D \<and> P \<turnstile> C \<preceq>\<^sup>* D)"
by (cases T, auto elim: widen.cases)

lemma Object_widen: "P \<turnstile> Class Object \<le> T \<Longrightarrow> T = Class Object"
by(case_tac T, auto elim: widen.cases)

lemma NT_Array_widen_Object:
  "\<lbrakk> is_type P T; is_NT_Array T\<rbrakk> \<Longrightarrow>  P \<turnstile> T \<le> Class Object"
by(induct T, auto intro: widen_array_object)

lemma widen_trans[trans]: "\<lbrakk>P \<turnstile> S \<le> U; P \<turnstile> U \<le> T\<rbrakk> \<Longrightarrow> P \<turnstile> S \<le> T"
proof - 
  assume "P \<turnstile> S \<le> U" thus "\<And>T. P \<turnstile> U \<le> T \<Longrightarrow> P \<turnstile> S \<le> T"
  proof induct
    case (widen_refl T T') thus "P \<turnstile> T \<le> T'" .
  next
    case (widen_subcls C D T)
    then obtain E where "T = Class E" by (blast dest: Class_widen)
    with widen_subcls show "P \<turnstile> Class C \<le> T" by (auto elim: rtrancl_trans)
  next
    case (widen_null C RT)
    then obtain D where "RT = Class D" by (blast dest: Class_widen)
    thus "P \<turnstile> NT \<le> RT" by auto
  next
    case (widen_null_array A T)
    hence "(\<exists>B. T = B\<lfloor>\<rceil>) \<or> T = Class Object"
      by(auto dest: Array_widen)
    moreover
    { assume "\<exists>B. T = B\<lfloor>\<rceil>"
      then obtain B where "T = B\<lfloor>\<rceil>" by blast
      hence "P \<turnstile> NT \<le> T" by simp }
    moreover
    { assume "T = Class Object"
      hence "P \<turnstile> NT \<le> T" by simp }
    ultimately show "P \<turnstile> NT \<le> T" by (auto)
  next
    case (widen_array_object A T)
    hence "T = Class Object" by -(rule Object_widen)
    with widen_array_object show "P \<turnstile> A\<lfloor>\<rceil> \<le> T"
      by(auto intro: widen.widen_array_object)
  next
    case (widen_array_array A B T)
    note AsB = `P \<turnstile> A \<le> B`
    note bta = `\<And>T. P \<turnstile> B \<le> T \<Longrightarrow> P \<turnstile> A \<le> T`
    note ANT = `\<not> is_NT_Array A`
    note Bt = `P \<turnstile> B\<lfloor>\<rceil> \<le> T`
    thus ?case
    proof(rule disjE[OF Array_widen])
      assume "\<exists>U. T = U\<lfloor>\<rceil> \<and> (is_NT_Array B \<longrightarrow> B = U)"
      then obtain U
	where U: "T = U\<lfloor>\<rceil>"
	and ntu: "is_NT_Array B \<Longrightarrow> B = U" by blast
      with Bt have "P \<turnstile> B \<le> U"
	by(auto dest: Array_Array_widen)
      with bta have "P \<turnstile> A \<le> U" by blast
      with ANT U ntu show ?thesis
	by(auto intro: widen.widen_array_array)
    next
      assume T: "T = Class Object"
      show ?thesis
      proof(cases "A = B")
	case True
	with Bt show ?thesis by simp
      next
	case False
	with AsB have "is_type P A" by(rule widen_is_type)
	with T show ?thesis
	  by(auto intro!: widen_array_object)
      qed
    qed
  qed
qed
(*>*)

lemma widens_trans: "\<lbrakk>P \<turnstile> Ss [\<le>] Ts; P \<turnstile> Ts [\<le>] Us\<rbrakk> \<Longrightarrow> P \<turnstile> Ss [\<le>] Us"
by (rule list_all2_trans, rule widen_trans)


(*<*)
lemma widens_refl: "P \<turnstile> Ts [\<le>] Ts"
by(rule list_all2_refl[OF widen_refl])

lemmas widens_Cons [iff] = list_all2_Cons1 [of "widen P", standard]
(*>*)

lemma widen_append1:
  "P \<turnstile> (xs @ ys) [\<le>] Ts = (\<exists>Ts1 Ts2. Ts = Ts1 @ Ts2 \<and> length xs = length Ts1 \<and> length ys = length Ts2 \<and> P \<turnstile> xs [\<le>] Ts1 \<and> P \<turnstile> ys [\<le>] Ts2)" 
apply(induct xs arbitrary: Ts)
 apply(simp)
 apply(induct ys arbitrary: Ts)
  apply(simp)
 apply(fastsimp)
apply(clarsimp)
apply(rule iffI)
 apply(clarify)
 apply(rule_tac x="z#Ts1" in exI)
 apply(rule_tac x="Ts2" in exI)
 apply(simp)
apply(clarify)
apply(rule_tac x="z" in exI)
apply(rule_tac x="zs @ Ts2" in exI)
apply(simp)
apply(rule_tac x="zs" in exI)
apply(rule_tac x="Ts2" in exI)
apply(simp)
done

lemma widens_lengthD:
  "P \<turnstile> xs [\<le>] ys \<Longrightarrow> length xs = length ys"
apply(induct xs arbitrary: ys)
apply(auto)
done


lemma widen_refT: "\<lbrakk> is_refT T; P \<turnstile> U \<le> T \<rbrakk> \<Longrightarrow> is_refT U"
apply(erule refTE)
  apply(fastsimp)
 apply(cases U, auto)
apply(cases U, auto)
done

lemma refT_widen: "\<lbrakk> is_refT T; P \<turnstile> T \<le> U \<rbrakk> \<Longrightarrow> is_refT U"
apply(erule refTE)
by(cases U, auto)+

inductive is_lub :: "'m prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> lub'((_,/ _)') = _" [51,51,51,51] 50)
for P :: "'m prog" and U :: ty and V :: ty and T ::  ty
where 
  "\<lbrakk> P \<turnstile> U \<le> T; P \<turnstile> V \<le> T;
     \<And>T'. \<lbrakk> P \<turnstile> U \<le> T'; P \<turnstile> V \<le> T' \<rbrakk> \<Longrightarrow> P \<turnstile> T \<le> T' \<rbrakk>
  \<Longrightarrow> P \<turnstile> lub(U, V) = T"

lemma is_lub_upper:
  "P \<turnstile> lub(U, V) = T \<Longrightarrow> P \<turnstile> U \<le> T \<and> P \<turnstile> V \<le> T"
by(auto elim: is_lub.cases)

lemma is_lub_least:
  "\<lbrakk> P \<turnstile> lub(U, V) = T; P \<turnstile> U \<le> T'; P \<turnstile> V \<le> T' \<rbrakk> \<Longrightarrow> P \<turnstile> T \<le> T'"
by(auto elim: is_lub.cases)

lemma is_lub_Void [iff]:
  "P \<turnstile> lub(Void, Void) = T \<longleftrightarrow> T = Void"
by(auto intro: is_lub.intros elim: is_lub.cases)

subsection{* Method lookup *}

inductive Methods :: "'m prog \<Rightarrow> cname \<Rightarrow> (mname \<rightharpoonup> (ty list \<times> ty \<times> 'm) \<times> cname) \<Rightarrow> bool" ("_ \<turnstile> _ sees'_methods _" [51,51,51] 50)
  for P :: "'m prog"
where 
sees_methods_Object:
 "\<lbrakk> class P Object = Some(D,fs,ms); Mm = Option.map (\<lambda>m. (m,Object)) \<circ> map_of ms \<rbrakk>
  \<Longrightarrow> P \<turnstile> Object sees_methods Mm"
| sees_methods_rec:
 "\<lbrakk> class P C = Some(D,fs,ms); C \<noteq> Object; P \<turnstile> D sees_methods Mm;
    Mm' = Mm ++ (Option.map (\<lambda>m. (m,C)) \<circ> map_of ms) \<rbrakk>
  \<Longrightarrow> P \<turnstile> C sees_methods Mm'"


lemma sees_methods_fun:
assumes 1: "P \<turnstile> C sees_methods Mm"
shows "\<And>Mm'. P \<turnstile> C sees_methods Mm' \<Longrightarrow> Mm' = Mm"
 (*<*)
using 1
proof induct
  case sees_methods_Object thus ?case by(auto elim: Methods.cases)
next
  case (sees_methods_rec C D fs ms Dres Cres Cres')
  have "class": "class P C = Some (D, fs, ms)"
   and notObj: "C \<noteq> Object" and Dmethods: "P \<turnstile> D sees_methods Dres"
   and IH: "\<And>Dres'. P \<turnstile> D sees_methods Dres' \<Longrightarrow> Dres' = Dres"
   and Cres: "Cres = Dres ++ (Option.map (\<lambda>m. (m,C)) \<circ> map_of ms)"
   and Cmethods': "P \<turnstile> C sees_methods Cres'" by fact+
  from Cmethods' notObj "class" obtain Dres'
    where Dmethods': "P \<turnstile> D sees_methods Dres'"
     and Cres': "Cres' = Dres' ++ (Option.map (\<lambda>m. (m,C)) \<circ> map_of ms)"
    by(auto elim: Methods.cases)
  from Cres Cres' IH[OF Dmethods'] show "Cres' = Cres" by simp
qed
(*>*)

lemma visible_methods_exist:
  "P \<turnstile> C sees_methods Mm \<Longrightarrow> Mm M = Some(m,D) \<Longrightarrow>
   (\<exists>D' fs ms. class P D = Some(D',fs,ms) \<and> map_of ms M = Some m)"
 (*<*)by(induct rule:Methods.induct) auto(*>*)

lemma sees_methods_decl_above:
assumes Csees: "P \<turnstile> C sees_methods Mm"
shows "Mm M = Some(m,D) \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
 (*<*)
using Csees
proof induct
  case sees_methods_Object thus ?case by auto
next
  case sees_methods_rec thus ?case
    by(fastsimp simp:Option.map_def split:option.splits
                elim:converse_rtranclp_into_rtranclp[where r = "subcls1 P", standard, OF subcls1I])
qed
(*>*)

lemma sees_methods_idemp:
assumes Cmethods: "P \<turnstile> C sees_methods Mm"
shows "\<And>m D. Mm M = Some(m,D) \<Longrightarrow>
              \<exists>Mm'. (P \<turnstile> D sees_methods Mm') \<and> Mm' M = Some(m,D)"
(*<*)
using Cmethods
proof induct
  case sees_methods_Object thus ?case
    by(fastsimp dest: Methods.sees_methods_Object)
next
  case sees_methods_rec thus ?case
    by(fastsimp split:option.splits dest: Methods.sees_methods_rec)
qed
(*>*)

(*FIXME something wrong with induct: need to attache [consumes 1]
directly to proof of thm, declare does not work. *)

lemma sees_methods_decl_mono:
assumes sub: "P \<turnstile> C' \<preceq>\<^sup>* C"
shows "P \<turnstile> C sees_methods Mm \<Longrightarrow>
       \<exists>Mm' Mm\<^isub>2. P \<turnstile> C' sees_methods Mm' \<and> Mm' = Mm ++ Mm\<^isub>2 \<and>
                 (\<forall>M m D. Mm\<^isub>2 M = Some(m,D) \<longrightarrow> P \<turnstile> D \<preceq>\<^sup>* C)"
(*<*)
      (is "_ \<Longrightarrow> \<exists>Mm' Mm2. ?Q C' C Mm' Mm2")
using sub
proof (induct rule:converse_rtranclp_induct)
  assume "P \<turnstile> C sees_methods Mm"
  hence "?Q C C Mm empty" by simp
  thus "\<exists>Mm' Mm2. ?Q C C Mm' Mm2" by blast
next
  fix C'' C'
  assume sub1: "P \<turnstile> C'' \<prec>\<^sup>1 C'" and sub: "P \<turnstile> C' \<preceq>\<^sup>* C"
  and IH: "P \<turnstile> C sees_methods Mm \<Longrightarrow>
           \<exists>Mm' Mm2. P \<turnstile> C' sees_methods Mm' \<and>
                Mm' = Mm ++ Mm2 \<and> (\<forall>M m D. Mm2 M = Some(m,D) \<longrightarrow> P \<turnstile> D \<preceq>\<^sup>* C)"
  and Csees: "P \<turnstile> C sees_methods Mm"
  from IH[OF Csees] obtain Mm' Mm2 where C'sees: "P \<turnstile> C' sees_methods Mm'"
    and Mm': "Mm' = Mm ++ Mm2"
    and subC:"\<forall>M m D. Mm2 M = Some(m,D) \<longrightarrow> P \<turnstile> D \<preceq>\<^sup>* C" by blast
  obtain fs ms where "class": "class P C'' = Some(C',fs,ms)" "C'' \<noteq> Object"
    using subcls1D[OF sub1] by blast
  let ?Mm3 = "Option.map (\<lambda>m. (m,C'')) \<circ> map_of ms"
  have "P \<turnstile> C'' sees_methods (Mm ++ Mm2) ++ ?Mm3"
    using sees_methods_rec[OF "class" C'sees refl] Mm' by simp
  hence "?Q C'' C ((Mm ++ Mm2) ++ ?Mm3) (Mm2++?Mm3)"
    using converse_rtranclp_into_rtranclp[OF sub1 sub]
    by simp (simp add:map_add_def subC split:option.split)
  thus "\<exists>Mm' Mm2. ?Q C'' C Mm' Mm2" by blast
qed
(*>*)


definition Method :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'm \<Rightarrow> cname \<Rightarrow> bool"
            ("_ \<turnstile> _ sees _: _\<rightarrow>_ = _ in _" [51,51,51,51,51,51,51] 50)
where
  "P \<turnstile> C sees M: Ts\<rightarrow>T = m in D  \<equiv>
  \<exists>Mm. P \<turnstile> C sees_methods Mm \<and> Mm M = Some((Ts,T,m),D)"

definition has_method :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> bool" ("_ \<turnstile> _ has _" [51,0,51] 50)
where
  "P \<turnstile> C has M \<equiv> \<exists>Ts T m D. P \<turnstile> C sees M:Ts\<rightarrow>T = m in D"

lemma has_methodI:
  "P \<turnstile> C sees M:Ts\<rightarrow>T = m in D \<Longrightarrow> P \<turnstile> C has M"
  by (unfold has_method_def) blast

lemma sees_method_fun:
  "\<lbrakk>P \<turnstile> C sees M:TS\<rightarrow>T = m in D; P \<turnstile> C sees M:TS'\<rightarrow>T' = m' in D' \<rbrakk>
   \<Longrightarrow> TS' = TS \<and> T' = T \<and> m' = m \<and> D' = D"
 (*<*)by(fastsimp dest: sees_methods_fun simp:Method_def)(*>*)

lemma sees_method_decl_above:
  "P \<turnstile> C sees M:Ts\<rightarrow>T = m in D \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
 (*<*)by(clarsimp simp:Method_def sees_methods_decl_above)(*>*)

lemma visible_method_exists:
  "P \<turnstile> C sees M:Ts\<rightarrow>T = m in D \<Longrightarrow>
  \<exists>D' fs ms. class P D = Some(D',fs,ms) \<and> map_of ms M = Some(Ts,T,m)"
(*<*)by(fastsimp simp:Method_def dest!: visible_methods_exist)(*>*)


lemma sees_method_idemp:
  "P \<turnstile> C sees M:Ts\<rightarrow>T=m in D \<Longrightarrow> P \<turnstile> D sees M:Ts\<rightarrow>T=m in D"
 (*<*)by(fastsimp simp: Method_def intro:sees_methods_idemp)(*>*)

lemma sees_method_decl_mono:
  "\<lbrakk> P \<turnstile> C' \<preceq>\<^sup>* C; P \<turnstile> C sees M:Ts\<rightarrow>T = m in D;
     P \<turnstile> C' sees M:Ts'\<rightarrow>T' = m' in D' \<rbrakk> \<Longrightarrow> P \<turnstile> D' \<preceq>\<^sup>* D"
 (*<*)
apply(frule sees_method_decl_above)
apply(unfold Method_def)
apply clarsimp
apply(drule (1) sees_methods_decl_mono)
apply clarsimp
apply(drule (1) sees_methods_fun)
apply clarsimp
apply(blast intro:rtranclp_trans)
done
(*>*)

lemma sees_method_is_class:
  "\<lbrakk> P \<turnstile> C sees M:Ts\<rightarrow>T = m in D \<rbrakk> \<Longrightarrow> is_class P C"
(*<*)by (auto simp add: is_class_def Method_def elim: Methods.induct)(*>*)


subsection{* Field lookup *}

inductive
  Fields :: "'m prog \<Rightarrow> cname \<Rightarrow> ((vname \<times> cname) \<times> (ty \<times> fmod)) list \<Rightarrow> bool" ("_ \<turnstile> _ has'_fields _" [51,51,51] 50)
for P :: "'m prog"
where 
has_fields_rec:
"\<lbrakk> class P C = Some(D,fs,ms); C \<noteq> Object; P \<turnstile> D has_fields FDTs;
   FDTs' = map (\<lambda>(F,Tm). ((F,C),Tm)) fs @ FDTs \<rbrakk>
 \<Longrightarrow> P \<turnstile> C has_fields FDTs'"
| has_fields_Object:
"\<lbrakk> class P Object = Some(D,fs,ms); FDTs = map (\<lambda>(F,T). ((F,Object),T)) fs \<rbrakk>
 \<Longrightarrow> P \<turnstile> Object has_fields FDTs"

lemma has_fields_fun:
assumes 1: "P \<turnstile> C has_fields FDTs"
shows "\<And>FDTs'. P \<turnstile> C has_fields FDTs' \<Longrightarrow> FDTs' = FDTs"
 (*<*)
using 1
proof induct
  case has_fields_Object thus ?case by(auto elim: Fields.cases)
next
  case (has_fields_rec C D fs ms Dres Cres Cres')
  have "class": "class P C = Some (D, fs, ms)"
   and notObj: "C \<noteq> Object" and DFields: "P \<turnstile> D has_fields Dres"
   and IH: "\<And>Dres'. P \<turnstile> D has_fields Dres' \<Longrightarrow> Dres' = Dres"
   and Cres: "Cres = map (\<lambda>(F,Tm). ((F,C),Tm)) fs @ Dres"
   and CFields': "P \<turnstile> C has_fields Cres'" by fact+
  from CFields' notObj "class" obtain Dres'
    where DFields': "P \<turnstile> D has_fields Dres'"
     and Cres': "Cres' = map (\<lambda>(F,Tm). ((F,C),Tm)) fs @ Dres'"
    by(auto elim: Fields.cases)
  from Cres Cres' IH[OF DFields'] show "Cres' = Cres" by simp

qed
(*>*)

lemma all_fields_in_has_fields:
assumes sub: "P \<turnstile> C has_fields FDTs"
shows "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* D; class P D = Some(D',fs,ms); (F,Tm) \<in> set fs \<rbrakk>
       \<Longrightarrow> ((F,D),Tm) \<in> set FDTs"
(*<*)
using sub apply(induct)
 apply(simp add:image_def)
 apply(erule converse_rtranclpE)
  apply(force)
 apply(drule subcls1D)
 apply fastsimp
apply(force simp:image_def)
done
(*>*)


lemma has_fields_decl_above:
assumes fields: "P \<turnstile> C has_fields FDTs"
shows "((F,D),Tm) \<in> set FDTs \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
(*<*)
using fields apply(induct)
 prefer 2 apply(fastsimp dest: tranclD)
apply clarsimp
apply(erule disjE)
 apply(clarsimp simp add:image_def)
apply simp
apply(blast dest:subcls1I converse_rtranclp_into_rtranclp)
done
(*>*)


lemma subcls_notin_has_fields:
assumes fields: "P \<turnstile> C has_fields FDTs"
shows "((F,D),Tm) \<in> set FDTs \<Longrightarrow> \<not>  (subcls1 P)\<^sup>+\<^sup>+ D C"
(*<*)
using fields apply(induct)
 prefer 2 apply(fastsimp dest: tranclpD)
apply clarsimp
apply(erule disjE)
 apply(clarsimp simp add:image_def)
 apply(drule tranclpD)
 apply clarify
 apply(frule subcls1D)
 apply(fastsimp dest:tranclpD all_fields_in_has_fields)
apply simp
apply(blast dest:subcls1I tranclp.trancl_into_trancl)
done
(*>*)


lemma has_fields_mono_lem:
assumes sub: "P \<turnstile> D \<preceq>\<^sup>* C"
shows "P \<turnstile> C has_fields FDTs
         \<Longrightarrow> \<exists>pre. P \<turnstile> D has_fields pre@FDTs \<and> dom(map_of pre) \<inter> dom(map_of FDTs) = {}"
(*<*)
using sub apply(induct rule:converse_rtranclp_induct)
 apply(rule_tac x = "[]" in exI)
 apply simp
apply clarsimp
apply(rename_tac D' D pre)
apply(subgoal_tac "(subcls1 P)^++ D' C")
 prefer 2 apply(erule (1) rtranclp_into_tranclp2)
apply(drule subcls1D)
apply clarsimp
apply(rename_tac fs ms)
apply(drule (2) has_fields_rec)
 apply(rule refl)
apply(rule_tac x = "map (\<lambda>(F,Tm). ((F,D'),Tm)) fs @ pre" in exI)
apply simp
apply(simp add:Int_Un_distrib2)
apply(rule equals0I)
apply(auto dest: subcls_notin_has_fields simp:dom_map_of_conv_image_fst image_def)
done
(*>*)

lemma has_fields_is_class:
  "P \<turnstile> C has_fields FDTs \<Longrightarrow> is_class P C"
(*<*)by (auto simp add: is_class_def elim: Fields.induct)(*>*)


(* FIXME why is Field not displayed correctly? TypeRel qualifier seems to confuse printer*)
definition
  has_field :: "'m prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> ty \<Rightarrow> fmod \<Rightarrow> cname \<Rightarrow> bool"
                   ("_ \<turnstile> _ has _:_ '(_') in _" [51,51,51,51,51,51] 50)
where
  "P \<turnstile> C has F:T (fm) in D  \<equiv>
  \<exists>FDTs. P \<turnstile> C has_fields FDTs \<and> map_of FDTs (F,D) = Some (T, fm)"

lemma has_field_mono:
  "\<lbrakk> P \<turnstile> C has F:T (fm) in D; P \<turnstile> C' \<preceq>\<^sup>* C \<rbrakk> \<Longrightarrow> P \<turnstile> C' has F:T (fm) in D"
(*<*)
apply(clarsimp simp:has_field_def)
apply(drule (1) has_fields_mono_lem)
apply(fastsimp simp: map_add_def split:option.splits)
done
(*>*)

lemma has_field_is_class:
  "\<lbrakk> P \<turnstile> C has M:T (fm) in D \<rbrakk> \<Longrightarrow> is_class P C"
(*<*)by (auto simp add: is_class_def has_field_def elim: Fields.induct)(*>*)

lemma has_field_decl_above:
  "P \<turnstile> C has F:T (fm) in D \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
unfolding has_field_def
by(auto dest: map_of_SomeD has_fields_decl_above)

lemma has_field_fun:
  "\<lbrakk>P \<turnstile> C has F:T (fm) in D; P \<turnstile> C has F:T' (fm') in D\<rbrakk> \<Longrightarrow> T' = T \<and> fm = fm'"
by(auto simp:has_field_def dest:has_fields_fun)

definition
  sees_field :: "'m prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> ty \<Rightarrow> fmod \<Rightarrow> cname \<Rightarrow> bool"
                  ("_ \<turnstile> _ sees _:_ '(_') in _" [51,51,51,51,51,51] 50)
where
  "P \<turnstile> C sees F:T (fm) in D  \<equiv>
  \<exists>FDTs. P \<turnstile> C has_fields FDTs \<and>
            map_of (map (\<lambda>((F,D),Tm). (F,(D,Tm))) FDTs) F = Some(D,T,fm)"

lemma map_of_remap_SomeD:
  "map_of (map (\<lambda>((k,k'),x). (k,(k',x))) t) k = Some (k',x) \<Longrightarrow> map_of t (k, k') = Some x"
(*<*)by (induct t) (auto simp:fun_upd_apply split: split_if_asm)(*>*)


lemma has_visible_field:
  "P \<turnstile> C sees F:T (fm) in D \<Longrightarrow> P \<turnstile> C has F:T (fm) in D"
(*<*)by(auto simp add:has_field_def sees_field_def map_of_remap_SomeD)(*>*)


lemma sees_field_fun:
  "\<lbrakk>P \<turnstile> C sees F:T (fm) in D; P \<turnstile> C sees F:T' (fm') in D'\<rbrakk> \<Longrightarrow> T' = T \<and> D' = D \<and> fm = fm'"
(*<*)by(fastsimp simp:sees_field_def dest:has_fields_fun)(*>*)


lemma sees_field_decl_above:
  "P \<turnstile> C sees F:T (fm) in D \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
(*<*)
apply(auto simp:sees_field_def)
apply(blast  intro: has_fields_decl_above map_of_SomeD map_of_remap_SomeD)
done
(*>*)

(* FIXME ugly *)  
lemma sees_field_idemp:
  "P \<turnstile> C sees F:T (fm) in D \<Longrightarrow> P \<turnstile> D sees F:T (fm) in D"
(*<*)
  apply (unfold sees_field_def)
  apply clarsimp
  apply (rule_tac P = "map_of ?xs F = ?y" in mp)
   prefer 2 
   apply assumption 
  apply (thin_tac "map_of ?xs F = ?y")
  apply (erule Fields.induct)
   apply clarsimp
   apply (frule map_of_SomeD)
   apply clarsimp
   apply (fastsimp intro: has_fields_rec)
  apply clarsimp
  apply (frule map_of_SomeD)
  apply clarsimp
  apply (fastsimp intro: has_fields_Object)
  done
(*>*)

subsection "Functional lookup"

definition method :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> cname \<times> ty list \<times> ty \<times> 'm"
where "method P C M  \<equiv>  THE (D,Ts,T,m). P \<turnstile> C sees M:Ts \<rightarrow> T = m in D"

definition field  :: "'m prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> cname \<times> ty \<times> fmod"
where "field P C F  \<equiv>  THE (D,T,fm). P \<turnstile> C sees F:T (fm) in D"
                                                        
definition fields :: "'m prog \<Rightarrow> cname \<Rightarrow> ((vname \<times> cname) \<times> (ty \<times> fmod)) list" 
where "fields P C  \<equiv>  THE FDTs. P \<turnstile> C has_fields FDTs"                

lemma [simp]: "P \<turnstile> C has_fields FDTs \<Longrightarrow> fields P C = FDTs"
(*<*)by (unfold fields_def) (auto dest: has_fields_fun)(*>*)

lemma field_def2 [simp]: "P \<turnstile> C sees F:T (fm) in D \<Longrightarrow> field P C F = (D,T,fm)"
(*<*)by (unfold field_def) (auto dest: sees_field_fun)(*>*)

lemma method_def2 [simp]: "P \<turnstile> C sees M: Ts\<rightarrow>T = m in D \<Longrightarrow> method P C M = (D,Ts,T,m)"
(*<*)by (unfold method_def) (auto dest: sees_method_fun)(*>*)

lemma has_fields_b_fields: 
  "P \<turnstile> C has_fields FDTs \<Longrightarrow> fields P C = FDTs"
unfolding fields_def
by (blast intro: the_equality has_fields_fun)

subsection {* Code generation *}

text {* New introduction rules for subcls1 *}

lemma subcls1_intros:
 "C \<noteq> Object \<Longrightarrow> subcls1 ((C, D, rest) # P) C D"
 "\<lbrakk> subcls1 P C D; C \<noteq> Object; C \<noteq> C' \<rbrakk> \<Longrightarrow> subcls1 ((C', D', rest) # P) C D"
apply -
 apply(rule subcls1I)
  apply(simp add: class_def)
 apply assumption
apply(erule subcls1.cases)
apply(rule subcls1I)
 apply(simp add: class_def)
apply assumption
done

lemma subcls1_cases:
  assumes "subcls1 P C D"
  obtains rest P' where "P = (C, D, rest) # P'" "C \<noteq> Object"
  | rest C' D' P' where "P = (C', D', rest) # P'" "subcls1 P' C D" "C \<noteq> Object" "C \<noteq> C'"
proof(atomize_elim)
  from assms
  show "(\<exists>rest P'. P = (C, D, rest) # P' \<and> C \<noteq> Object) \<or>
    (\<exists>C' D' rest P'. P = (C', D', rest) # P' \<and> P' \<turnstile> C \<prec>\<^sup>1 D \<and> C \<noteq> Object \<and> C \<noteq> C')"
  proof(induct P)
    case Nil thus ?case
      by(auto elim: subcls1.cases simp add: class_def)
  next
    case (Cons a P)
    obtain C' D' rest where [simp]: "a = (C', D', rest)" by(cases a)
    show ?case
    proof(cases "C = C'")
      case True
      with `(a # P) \<turnstile> C \<prec>\<^sup>1 D` show ?thesis
        by(auto elim: subcls1.cases simp add: class_def)
    next
      case False
      with `(a # P) \<turnstile> C \<prec>\<^sup>1 D` have "P \<turnstile> C \<prec>\<^sup>1 D"
        by(auto elim!: subcls1.cases simp add: class_def intro: subcls1I)
      with Cons have "(\<exists>C' D' rest P'. a # P = (C', D', rest) # P' \<and> P' \<turnstile> C \<prec>\<^sup>1 D \<and> C \<noteq> Object \<and> C \<noteq> C')"
        using False by(auto)
      thus ?thesis ..
    qed
  qed
qed

declare subcls1_intros [code_pred_intro]
code_pred subcls1
proof -
  case subcls1 
  from subcls1.prems show thesis
    by(rule subcls1_cases)(assumption|erule that[OF _ refl refl])+
qed

text {*
  Introduce proper constant @{text "subcls'"} for @{term "subcls"}
  and generate executable equation for @{text "subcls'"} 
*}

definition subcls' where "subcls' = subcls"

code_pred [inductify] subcls' .

lemma subcls_conv_subcls' [code_inline]:
  "(subcls1 P)^** = subcls' P"
by(simp add: subcls'_def)

text {* @{term "subcls'_i_i_i"} uses @{term subcls1_i_o_o}, but @{term subcls1_i_i_o} is much more efficient *}
lemma subcls'_i_i_i_code [code]:
  "subcls'_i_i_i P = rtranclp_FioB_i_i (subcls1_i_i_o P)"
apply(rule ext)+
apply(rule pred_iffI)
 apply(erule subcls'_i_i_iE)
 apply clarsimp
 apply(rule rtranclp_FioB_i_iI)
  apply(unfold subcls'_def)[2]
  apply assumption
 apply(rule ext iffI)+
  apply(erule subcls1_i_i_oE)
  apply assumption
 apply(erule subcls1_i_i_oI)
apply(erule rtranclp_FioB_i_iE)
apply clarsimp
apply(rule subcls'_i_i_iI)
apply(unfold subcls'_def)
apply(erule rtranclp_induct)
 apply blast
apply(erule subcls1_i_i_oE)
apply(erule (1) rtranclp.rtrancl_into_rtrancl)
done

text {* 
  Change rule @{thm widen_array_object} such that predicate compiler
  tests on class @{term Object} first. Otherwise @{text "widen_i_o_i"} never terminates.
*}

lemma widen_array_object_code:
  "\<lbrakk> C = Object; is_type P A \<rbrakk> \<Longrightarrow> P \<turnstile> Array A \<le> Class C"
by(auto intro: widen.intros)

(* lemmas [code_pred_intro] =
  widen_refl widen_subcls widen_null widen_null_array widen_array_object_code widen_array_array
code_pred [show_modes] widen 
by(erule widen.cases) auto  *)

lemmas [code_pred_def] =
  widen_refl widen_subcls widen_null widen_null_array widen_array_object_code widen_array_array
code_pred [inductify] widen . 

text {*
  @{term widen_i_i_i} uses @{term "subcls1_i_o_o"}, which is inefficient. Better use @{term subcls1_i_o_i}.
*}

lemma widen_i_i_i_code [code]:
  "widen_i_i_i P T U =
   sup (if T = U then Predicate.single () else bot)
   (sup (case T of Class C \<Rightarrow> (case U of Class D \<Rightarrow> rtranclp_FioB_i_i (subcls1_i_i_o P) C D | _ \<Rightarrow> bot) | _ \<Rightarrow> bot)
   (sup (case T of NT \<Rightarrow> (case U of Class C \<Rightarrow> Predicate.single () | Array A \<Rightarrow> Predicate.single () | _ \<Rightarrow> bot) | _ \<Rightarrow> bot)
   (sup (case T of Array A \<Rightarrow> (case U of Class C \<Rightarrow> if C = Object then (is_type_i_i P A) else bot | _ \<Rightarrow> bot) | _ \<Rightarrow> bot)
        (case T of Array A \<Rightarrow> (case U of Array B \<Rightarrow> Predicate.bind (widen_i_i_i P A B) (unit_case (Predicate.bind (Predicate.if_pred (ground_type A \<noteq> NT)) (unit_case (Predicate.single ())))) | _ \<Rightarrow> bot) | _ \<Rightarrow> bot))))"
apply(subst widen.equation)
apply(rule pred_iffI)
 apply(erule supE bindE singleE)+
  apply(rule supI1)
  apply clarsimp
 apply(erule supE bindE singleE)+
  apply(simp split del: split_if split: ty.split_asm unit.splits)
  apply(erule bindE)
  apply(rule supI2)
  apply simp
  apply(erule rtranclp_FooB_i_iE)
  apply(erule rtranclp_FioB_i_iI)
  apply(rule ext)+
  apply(rule iffI)
   apply(erule subcls1_i_i_oE)
   apply(erule subcls1_i_o_oI)
  apply(erule subcls1_i_o_oE)
  apply(erule subcls1_i_i_oI)
 apply(erule supE bindE singleE)+
  apply(rule supI2)
  apply(rule supI2)
  apply(rule supI1)
  apply(simp split: ty.split_asm)
 apply(erule supE bindE singleE)+
  apply(rule supI2)
  apply(rule supI2)
  apply(rule supI1)
  apply(simp split: ty.split_asm)
 apply(erule supE bindE singleE)+
  apply(rule supI2)
  apply(rule supI2)
  apply(rule supI2)
  apply(rule supI1)
  apply(simp split: ty.split_asm unit.split_asm)
  apply(erule bindE)
  apply(split unit.split_asm)
  apply(simp split: split_if_asm)
 apply(erule bindE singleE)+
 apply(rule supI2)
 apply(rule supI2)
 apply(rule supI2)
 apply(rule supI2)
 apply(simp split: ty.split_asm)
apply(erule supE)
 apply(simp split: split_if_asm)
 apply(rule supI1)
 apply(rule bindI)
  apply(rule singleI)
 apply simp
apply(erule supE)
 apply(simp split: ty.split_asm)
 apply(rule supI2)
 apply(rule supI1)
 apply(rule bindI)
  apply(rule singleI)
 apply(simp)
 apply(erule rtranclp_FioB_i_iE)
 apply(rule bindI)
  apply(erule rtranclp_FooB_i_iI)
  apply(rule ext)+
  apply(rule iffI)
   apply(erule subcls1_i_o_oE)
   apply(erule subcls1_i_i_oI)
  apply(erule subcls1_i_i_oE)
  apply(erule subcls1_i_o_oI)
 apply(simp split: unit.split)
 apply(rule singleI)
apply(erule supE)
 apply(simp split: ty.split_asm)
  apply(rule supI2)
  apply(rule supI2)
  apply(rule supI1)
  apply(rule bindI)
   apply(rule singleI)
  apply simp
 apply(rule supI2)
 apply(rule supI2)
 apply(rule supI2)
 apply(rule supI1)
 apply(rule bindI)
  apply(rule singleI)
 apply simp
apply(erule supE)
 apply(simp split: ty.split_asm)
 apply(rule supI2)
 apply(rule supI2)
 apply(rule supI2)
 apply(rule supI2)
 apply(rule supI1)
 apply(rule bindI)
  apply(rule singleI)
 apply(simp split: split_if_asm)
 apply(erule bindI)
 apply(simp split: unit.split)
 apply(rule singleI)
apply(rule supI2)
apply(rule supI2)
apply(rule supI2)
apply(rule supI2)
apply(rule supI2)
apply(rule bindI)
 apply(rule singleI)
apply(simp split: ty.split_asm)
done

code_pred Methods .

code_pred [inductify] Method .

code_pred [inductify] has_method .

(* FIXME: Necessary only because of bug in code_pred *)
declare fun_upd_def [code_pred_inline]

code_pred Fields .

code_pred [inductify, skip_proof] has_field .

code_pred [inductify, skip_proof] sees_field .

lemma eval_Method_i_i_i_o_o_o_o_conv:
  "Predicate.eval (Method_i_i_i_o_o_o_o P C M) = (\<lambda>(Ts, T, m, D). P \<turnstile> C sees M:Ts\<rightarrow>T=m in D)"
by(auto intro: Method_i_i_i_o_o_o_oI elim: Method_i_i_i_o_o_o_oE intro!: ext)

lemma method_code [code]:
  "method P C M = 
  Predicate.the (Predicate.bind (Method_i_i_i_o_o_o_o P C M) (\<lambda>(Ts, T, m, D). Predicate.single (D, Ts, T, m)))"
apply(simp add: method_def Predicate.the_def Predicate.bind_def Predicate.single_def eval_Method_i_i_i_o_o_o_o_conv)
apply(rule arg_cong[where f=The])
apply(rule ext)
apply clarsimp
done

lemma eval_sees_field_i_i_i_o_o_o_conv:
  "Predicate.eval (sees_field_i_i_i_o_o_o P C F) = (\<lambda>(T, fm, D). P \<turnstile> C sees F:T (fm) in D)"
by(auto intro!: ext intro: sees_field_i_i_i_o_o_oI elim: sees_field_i_i_i_o_o_oE)

lemma eval_sees_field_i_i_i_o_i_conv:
  "Predicate.eval (sees_field_i_i_i_o_o_i P C F D) = (\<lambda>(T, fm). P \<turnstile> C sees F:T (fm) in D)"
by(auto intro!: ext intro: sees_field_i_i_i_o_o_iI elim: sees_field_i_i_i_o_o_iE)

lemma field_code [code]:
  "field P C F = Predicate.the (Predicate.bind (sees_field_i_i_i_o_o_o P C F) (\<lambda>(T, fm, D). Predicate.single (D, T, fm)))"
apply(simp add: field_def Predicate.the_def Predicate.bind_def Predicate.single_def eval_sees_field_i_i_i_o_o_o_conv)
apply(rule arg_cong[where f=The])
apply(rule ext)
apply clarsimp
done

lemma eval_Fields_conv:
  "Predicate.eval (Fields_i_i_o P C) = (\<lambda>FDTs. P \<turnstile> C has_fields FDTs)"
by(auto intro: Fields_i_i_oI elim: Fields_i_i_oE intro!: ext)

lemma fields_code [code]:
  "fields P C = Predicate.the (Fields_i_i_o P C)"
by(simp add: fields_def Predicate.the_def eval_Fields_conv)

end

