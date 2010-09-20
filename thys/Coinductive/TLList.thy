(*  Title:       Terminated coinductive list
    Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)

header {* Terminated coinductive lists *}

theory TLList imports
  "Quotient_Coinductive_List"
  "Quotient_Product"
  "Quotient_Sum"
begin

text {*
  Terminated coinductive lists @{text "('a, 'b) tllist"} are the codatatype defined by the construtors
  @{text "TNil"} of type @{text "'b \<Rightarrow> ('a, 'b) tllist"} and
  @{text "TCons"} of type @{text "'a \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"}.

  Instead of manually constructing @{text "('a, 'b) tllist"},
  we define it as the quotient of @{typ "'a llist \<times> 'b"} w.r.t.
  the equivalence relation that is the identity except for infinite lists @{text "xs"} 
  for which it ignores the second component.
*}

subsection {* Auxiliary lemmas *}

lemma mem_preserve [quot_preserve]: 
  assumes "Quotient R Abs Rep"
  shows "(Rep ---> (Abs ---> id) ---> id) (op \<in>) = op \<in>"
using Quotient_abs_rep[OF assms]
by(simp add: fun_eq_iff mem_def)

lemma mem_respect [quot_respect]:
  "(R ===> (R ===> op =) ===> op =) (op \<in>) (op \<in>)"
by(simp add: fun_eq_iff mem_def)

lemma sum_case_preserve [quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and q2: "Quotient R2 Abs2 Rep2"
  and q3: "Quotient R3 Abs3 Rep3"
  shows "((Abs1 ---> Rep2) ---> (Abs3 ---> Rep2) ---> sum_map Rep1 Rep3 ---> Abs2) sum_case = sum_case"
using Quotient_abs_rep[OF q1] Quotient_abs_rep[OF q2] Quotient_abs_rep[OF q3]
by(simp add: fun_eq_iff split: sum.split)

lemma sum_case_preserve2 [quot_preserve]:
  assumes q: "Quotient R Abs Rep"
  shows "((id ---> Rep) ---> (id ---> Rep) ---> id ---> Abs) sum_case = sum_case"
using Quotient_abs_rep[OF q]
by(auto intro!: ext split: sum.split)

lemma prod_case_preserve [quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and q2: "Quotient R2 Abs2 Rep2"
  and q3: "Quotient R3 Abs3 Rep3"
  shows "((Abs1 ---> Abs2 ---> Rep3) ---> prod_fun Rep1 Rep2 ---> Abs3) prod_case = prod_case"
using Quotient_abs_rep[OF q1] Quotient_abs_rep[OF q2] Quotient_abs_rep[OF q3]
by(simp add: fun_eq_iff split: prod.split)

lemma prod_case_preserve2 [quot_preserve]:
  assumes q: "Quotient R Abs Rep"
  shows "((id ---> id ---> Rep) ---> id ---> Abs) prod_case = prod_case"
using Quotient_abs_rep[OF q]
by(auto intro!: ext)

lemma id_preserve [quot_preserve]:
  assumes "Quotient R Abs Rep"
  shows "(Rep ---> Abs) id = id"
using Quotient_abs_rep[OF assms]
by(auto intro: ext)

lemma split_fst: "R (fst p) = (\<forall>x y. p = (x, y) \<longrightarrow> R x)"
by(cases p) simp

lemma split_fst_asm: "R (fst p) \<longleftrightarrow> (\<not> (\<exists>x y. p = (x, y) \<and> \<not> R x))"
by(cases p)(simp)

subsection {* Type definition *}

fun tlist_eq :: "('a llist \<times> 'b) \<Rightarrow> ('a llist \<times> 'b) \<Rightarrow> bool"
where "tlist_eq (xs, a) (ys, b) \<longleftrightarrow> xs = ys \<and> (lfinite xs \<longrightarrow> a = b)"

lemma tlist_eq_iff: "tlist_eq xsa ysb \<longleftrightarrow> fst xsa = fst ysb \<and> (lfinite (fst xsa) \<longrightarrow> snd xsa = snd ysb)"
by(cases xsa, cases ysb) auto

lemma equivp_tlist_eq: "equivp tlist_eq"
by(rule equivpI)(auto simp add: reflp_def symp_def transp_def)

lemma sum_case_respect_tlist_eq [quot_respect]:
  "((op = ===> tlist_eq) ===> (op = ===> tlist_eq) ===> op = ===> tlist_eq) sum_case sum_case"
by(simp split: sum.split)

lemma prod_case_repsect_tlist_eq [quot_respect]:
  "((op = ===> op = ===> tlist_eq) ===> op = ===> tlist_eq) prod_case prod_case"
by(simp)

lemma id_respect_tlist_eq [quot_respect]:
  "(tlist_eq ===> tlist_eq) id id"
by auto

quotient_type ('a, 'b) tllist = "'a llist \<times> 'b" / tlist_eq
by(rule equivp_tlist_eq)

definition TNIL :: "'a \<Rightarrow> ('b llist \<times> 'a)"
where "TNIL = Pair LNil"

definition TCONS :: "'a \<Rightarrow> ('a llist \<times> 'b) \<Rightarrow> ('a llist \<times> 'b)"
where "TCONS = apfst \<circ> LCons"

quotient_definition "TNil :: 'a \<Rightarrow> ('b, 'a) tllist"
is "TNIL"

quotient_definition "TCons :: 'a \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
is "TCONS"

lemma TNil_respect [quot_respect]:
  "(op = ===> tlist_eq) TNIL TNIL"
by(simp add: TNIL_def)

lemma TCons_respect [quot_respect]:
  "(op = ===> tlist_eq ===> tlist_eq) TCONS TCONS"
by(simp add: TCONS_def)

code_datatype TNil TCons

lemma tllist_simps [simp, induct_simp]:
  shows "TNil b \<noteq> TCons a tr"
  and "TCons a tr \<noteq> TNil b"
  and TNil_inject: "TNil b = TNil b' \<longleftrightarrow> b = b'"
  and TCons_inject: "TCons a tr = TCons a' tr' \<longleftrightarrow> a = a' \<and> tr = tr'"
by(descending, clarsimp simp add: TNIL_def TCONS_def)+

primrec tllist_case_aux :: "('b \<Rightarrow> 'e) \<Rightarrow> ('a \<Rightarrow> ('a llist \<times> 'b) \<Rightarrow> 'e) \<Rightarrow> ('a llist \<times> 'b) \<Rightarrow> 'e"
where "tllist_case_aux f g (xs, b) = (case xs of LNil \<Rightarrow> f b | LCons x xs' \<Rightarrow> g x (xs', b))"

lemma tllist_case_aux_respect [quot_respect]:
  "(op = ===> (op = ===> tlist_eq ===> op =) ===> tlist_eq ===> op =) tllist_case_aux tllist_case_aux"
by(auto intro: ext split: llist_split)

quotient_definition "tllist_case :: ('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> ('c, 'a) tllist \<Rightarrow> 'b) \<Rightarrow> ('c, 'a) tllist \<Rightarrow> 'b"
is "tllist_case_aux"

translations
  "case p of XCONST TNil y \<Rightarrow> a | XCONST TCons x l \<Rightarrow> b" \<rightleftharpoons> "CONST tllist_case (\<lambda>y. a) (\<lambda>x l. b) p"

lemma tllist_case_simps [simp, code, nitpick_simp]:
  shows tllist_case_TNil: "tllist_case f g (TNil b) = f b"
  and tllist_case_TCons: "tllist_case f g (TCons x tr) = g x tr"
by(descending, clarsimp simp add: split_beta TNIL_def TCONS_def)+

lemma tllist_case_cert:
  assumes "CASE \<equiv> tllist_case c d"
  shows "(CASE (TNil b) \<equiv> c b) &&& (CASE (TCons M N) \<equiv> d M N)"
  using assms by simp_all

setup {*
  Code.add_case @{thm tllist_case_cert}
*}

setup {*
  Nitpick.register_codatatype @{typ "('a, 'b) tllist"} @{const_name tllist_case}
    (map dest_Const [@{term TNil}, @{term TCons}])
*}

lemma tllist_exhaust_aux:
  obtains b where "xsb = TNIL b"
  | a xsb' where "xsb = TCONS a xsb'"
apply(cases xsb)
apply(rename_tac xs b)
apply(case_tac xs)
apply(fastsimp simp add: TNIL_def TCONS_def)+
done

lemma tllist_exhaust [case_names TNil TCons, cases type]:
  obtains (TNil) b where "tr = TNil b"
       | (TCons) a tr' where "tr = TCons a tr'"
by(lifting tllist_exhaust_aux)

lemma tllist_split:
  "P (tllist_case f g tr) = ((\<forall>b. tr = TNil b \<longrightarrow> P (f b)) \<and> (\<forall>a tr'. tr = TCons a tr' \<longrightarrow> P (g a tr')))"
by(cases tr) simp_all

lemma tllist_split_asm:
  "P (tllist_case f g tr) = (\<not> ((\<exists>b. tr = TNil b \<and> \<not> P (f b)) \<or> (\<exists>a tr'. tr = TCons a tr' \<and> \<not> P (g a tr'))))"
by(cases tr) simp_all

lemmas tllist_splits =
  tllist_split tllist_split_asm

subsection {* Coinduction and corecursion principles *}

lemma tlist_eq_coinduct [consumes 1, case_names tlist_eq, case_conclusion tlist_eq Nil Cons]:
  assumes major: "(xsb, xsb') \<in> r"
  and step: "\<And>q. q \<in> r \<Longrightarrow> (\<exists>b. prod_rel tlist_eq tlist_eq q (TNIL b, TNIL b)) \<or>
                           (\<exists>a xsb xsb'. prod_rel tlist_eq tlist_eq q (TCONS a xsb, TCONS a xsb') \<and> ((xsb, xsb') \<in> r \<or> tlist_eq xsb xsb'))"
  shows "tlist_eq xsb xsb'"
proof -
  obtain xs b where xsb [simp]: "xsb = (xs, b)" by(cases xsb)
  obtain xs' b' where xsb' [simp]: "xsb' = (xs', b')" by(cases xsb')
  from major have "(xs, xs') \<in> {(xs, xs'). \<exists>b b'. ((xs, b), (xs', b')) \<in> r}" by auto
  hence "xs = xs'"
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain xs xs' b b' where q: "q = (xs, xs')"
      and r: "((xs, b), (xs', b')) \<in> r" by blast
    from step[OF r] show ?case unfolding q by(auto simp add: TCONS_def TNIL_def)
  qed
  moreover {
    assume "lfinite xs"
    hence "b = b'" using major[unfolded xsb xsb', folded `xs = xs'`]
    proof(induct)
      case lfinite_LNil
      thus ?case by(auto dest: step simp add: TNIL_def TCONS_def)
    next
      case (lfinite_LConsI xs x)
      from step[OF `((LCons x xs, b), LCons x xs, b') \<in> r`]
      have "((xs, b), (xs, b')) \<in> r \<or> tlist_eq (xs, b) (xs, b')"
        by(auto simp add: TNIL_def TCONS_def)
      thus ?case using lfinite_LConsI by(auto)
    qed }      
  ultimately show ?thesis by simp
qed

lemma tllist_equalityI [consumes 1, case_names Eqtllist, case_conclusion Eqtllist EqTNil EqTCons]:
  "\<lbrakk> (tr, tr') \<in> r;
     \<And>q. q \<in> r \<Longrightarrow> (\<exists>b. q = (TNil b, TNil b)) \<or>
                   (\<exists>a tr tr'. q = (TCons a tr, TCons a tr') \<and> ((tr, tr') \<in> r \<or> tr = tr')) \<rbrakk>
  \<Longrightarrow> tr = tr'"
by(lifting tlist_eq_coinduct)

definition tllist_corec_aux :: "'a \<Rightarrow> ('a \<Rightarrow> (('b \<times> 'a) + 'c)) \<Rightarrow> ('b llist \<times> 'c)"
where
  "tllist_corec_aux a f =
   (let f' = \<lambda>a. case f a of Inl ba \<Rightarrow> Some ba | Inr c \<Rightarrow> None;
        g  = \<lambda>ac. case ac of Inl a \<Rightarrow> (case f a of Inl (b, a) \<Rightarrow> Inl a | Inr c \<Rightarrow> Inr c) | Inr c \<Rightarrow> Inr c;
        xs = llist_corec a f'
    in (xs, 
        if lfinite xs
        then THE c. (g ^^ (Suc (THE n. llength xs = Fin n))) (Inl a) = Inr c
        else undefined))"

lemma tllist_corec_aux:
  "tllist_corec_aux a f =
   (case f a of Inl (b, a') \<Rightarrow> TCONS b (tllist_corec_aux a' f)
                    | Inr c \<Rightarrow> TNIL c)"
proof(cases "lfinite (llist_corec a (\<lambda>a. case f a of Inl ba \<Rightarrow> Some ba | Inr c \<Rightarrow> None))")
  case False thus ?thesis
    by(auto simp add: tllist_corec_aux_def TNIL_def TCONS_def split: sum.split)(simp_all add: llist_corec)
next
  case True
  thus ?thesis
  proof(induct xs\<equiv>"llist_corec a (\<lambda>a. case f a of Inl ba \<Rightarrow> Some ba | Inr c \<Rightarrow> None)" arbitrary: a)
    case lfinite_LNil[symmetric]
    thus ?case
      by(simp add: llist_corec tllist_corec_aux_def zero_inat_def TNIL_def split: sum.split_asm prod.split_asm)
  next
    case (lfinite_LConsI xs x)
    from `LCons x xs = llist_corec a (\<lambda>a. case f a of Inl ba \<Rightarrow> Some ba | Inr c \<Rightarrow> None)`
    obtain a' where a': "f a = Inl (x, a')"
      and xs: "xs = llist_corec a' (\<lambda>a. case f a of Inl ba \<Rightarrow> Some ba | Inr c \<Rightarrow> None)"
      by(subst (asm) (2) llist_corec)(auto split: sum.split_asm)
    from xs have "tllist_corec_aux a' f = sum_case (prod_case (\<lambda>b a'. TCONS b (tllist_corec_aux a' f))) TNIL (f a')"
      by(rule lfinite_LConsI)
    thus ?case using `lfinite xs` a' xs
      by(auto simp add: tllist_corec_aux_def TCONS_def TNIL_def Let_def iSuc_Fin funpow_Suc_tail_rec llist_corec dest!: lfinite_llength_Fin simp del: funpow.simps)
  qed
qed

quotient_definition "tllist_corec :: 'a \<Rightarrow> ('a \<Rightarrow> (('b \<times> 'a) + 'c)) \<Rightarrow> ('b, 'c) tllist"
is "tllist_corec_aux"

lemma tllist_corec_aux_respect_tlist_eq [quot_respect]:
  "(op = ===> op = ===> tlist_eq) tllist_corec_aux tllist_corec_aux"
by(auto intro: ext equivp_reflp[OF tllist_equivp])

lemma tllist_corec [code, nitpick_simp]:
  "tllist_corec a f = (sum_case (prod_case (\<lambda>b a'. TCons b (tllist_corec a' f))) TNil (f a))"
by(lifting tllist_corec_aux)

subsection {* Library function definitions *}

text {* 
  We lift the constants from @{typ "'a llist"} to @{typ "('a, 'b) tllist"} using the quotient package.
  This way, many results are transferred easily.
*}

definition tllist_of_llist :: "'b \<Rightarrow> 'a llist \<Rightarrow> ('a, 'b) tllist"
where
  "tllist_of_llist s tls = 
   tllist_corec tls (\<lambda>tls. case tls of LNil \<Rightarrow> Inr s 
                           |  LCons tl tls' \<Rightarrow> Inl (tl, tls'))"

primrec TERMINAL :: "('a llist \<times> 'b) \<Rightarrow> 'b"
where "TERMINAL (xs, c) = (if lfinite xs then c else undefined)"

quotient_definition "terminal :: ('a, 'b) tllist \<Rightarrow> 'b"
is "TERMINAL"

primrec tMAP :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> 'a llist \<times> 'c \<Rightarrow> 'b llist \<times> 'd"
where "tMAP f g (xs, b) = (lmap f xs, g b)"

quotient_definition "tmap :: ('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('a, 'c) tllist \<Rightarrow> ('b, 'd) tllist"
is "tMAP"

primrec tAPPEND :: "'a llist \<times> 'b \<Rightarrow> ('b \<Rightarrow> 'a llist \<times> 'c) \<Rightarrow> 'a llist \<times> 'c"
where "tAPPEND (xs, b) f = (lappend xs (fst (f b)), snd (f b))"

quotient_definition "tappend :: ('a, 'b) tllist \<Rightarrow> ('b \<Rightarrow> ('a, 'c) tllist) \<Rightarrow> ('a, 'c) tllist"
is "tAPPEND"

primrec lAPPENDt :: "'a llist \<Rightarrow> 'a llist \<times> 'b \<Rightarrow> 'a llist \<times> 'b"
where "lAPPENDt xs (ys, b) = (lappend xs ys, b)"

quotient_definition "lappendt :: 'a llist \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
is "lAPPENDt"

primrec tFILTER :: "'a \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('b llist \<times> 'a) \<Rightarrow> ('b llist \<times> 'a)"
where "tFILTER b P (xs, b') = (lfilter P xs, if lfinite xs then b' else b)"

quotient_definition "tfilter :: 'a \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('b, 'a) tllist \<Rightarrow> ('b, 'a) tllist"
is "tFILTER"

primrec tCONCAT :: "'a \<Rightarrow> ('b llist llist \<times> 'a) \<Rightarrow> ('b llist \<times> 'a)"
where "tCONCAT b (xss, b') = (lconcat xss, if lfinite xss then b' else b)"

quotient_definition "tconcat :: 'a \<Rightarrow> ('b llist, 'a) tllist \<Rightarrow> ('b, 'a) tllist"
is "tCONCAT"

fun TLLIST_ALL2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a llist \<times> 'c) \<Rightarrow> ('b llist \<times> 'd) \<Rightarrow> bool"
where "TLLIST_ALL2 P Q (xs, b) (ys, b') \<longleftrightarrow> llist_all2 P xs ys \<and> (lfinite xs \<longrightarrow> Q b b')"

quotient_definition "tllist_all2 :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a, 'c) tllist \<Rightarrow> ('b, 'd) tllist \<Rightarrow> bool"
is TLLIST_ALL2

quotient_definition "llist_of_tllist :: ('a, 'b) tllist \<Rightarrow> 'a llist"
is "fst :: ('a llist \<times> 'b) \<Rightarrow> 'a llist"

primrec TNTH :: "('a llist \<times> 'b) \<Rightarrow> nat \<Rightarrow> 'a"
where "TNTH (xs, b) = lnth xs"

quotient_definition "tnth :: ('a, 'b) tllist \<Rightarrow> nat \<Rightarrow> 'a"
is "TNTH"

primrec TLENGTH :: "('a llist \<times> 'b) \<Rightarrow> inat"
where "TLENGTH (xs, b) = llength xs"

quotient_definition "tlength :: ('a, 'b) tllist \<Rightarrow> inat"
is "TLENGTH"

primrec TDROPn :: "nat \<Rightarrow> ('a llist \<times> 'b) \<Rightarrow> ('a llist \<times> 'b)"
where "TDROPn n (xs, b) = (ldropn n xs, b)"

quotient_definition "tdropn :: nat \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
is "TDROPn"

subsection {* From a lazy list to a terminated lazy list @{term tllist_of_llist } *}

lemma tllist_of_llist_simps [simp, code, nitpick_simp]:
  fixes tl
  shows tllist_of_llist_LNil: "tllist_of_llist s LNil = TNil s"
  and tllist_of_llist_LCons: "tllist_of_llist s (LCons tl tls)  = TCons tl (tllist_of_llist s tls)"
by(simp_all add: tllist_of_llist_def tllist_corec)

subsection {* The terminal element @{term "terminal"} *}

lemma TERMINAL_respect [quot_respect]:
  "(tlist_eq ===> op =) TERMINAL TERMINAL"
by(auto)

lemma terminal_TNil [simp, code, nitpick_simp]: "terminal (TNil b) = b"
by(descending)(simp add: TNIL_def)

lemma terminal_TCons [simp, code, nitpick_simp]: "terminal (TCons x xs) = terminal xs"
by(descending)(auto simp add: TCONS_def)

subsection {* @{term "tmap"} *}

lemma tMAP_respect [quot_respect]:
  "(op = ===> op = ===> tlist_eq ===> tlist_eq) tMAP tMAP"
by(auto intro: ext)

lemma tmap_TNil [simp, code, nitpick_simp]: "tmap f g (TNil b) = TNil (g b)"
by(descending)(simp add: TNIL_def)

lemma tmap_TCons [simp, code, nitpick_simp]: "tmap f g (TCons a tr) = TCons (f a) (tmap f g tr)"
by(descending)(auto simp add: TCONS_def)

lemma tmap_compose [simp]: "tmap (f o f') (g o g') ts = tmap f g (tmap f' g' ts)"
by(descending) auto

lemma tmap_id_id [id_simps]:
  "tmap id id = id"
proof
  fix ts :: "('a, 'b) tllist"
  show "tmap id id ts = id ts"
    by(descending)(auto simp add: lmap_id)
qed

subsection {* Appending two terminated lazy lists @{term "tappend" } *}

lemma tappend_respect [quot_respect]:
  "(tlist_eq ===> (op = ===> tlist_eq) ===> tlist_eq) tAPPEND tAPPEND"
apply(auto intro: ext simp add: lappend_inf split: split_fst)
apply(erule_tac x=ba in allE, auto)+
done

lemma tappend_TNil [simp, code, nitpick_simp]: 
  "tappend (TNil b) f = f b"
by(descending)(auto simp add: TNIL_def tlist_eq_iff)

lemma tappend_TCons [simp, code, nitpick_simp]:
  "tappend (TCons a tr) f = TCons a (tappend tr f)"
by(descending)(auto simp add: TCONS_def)

subsection {* Appending a terminated lazy list to a lazy list @{term "lappendt"} *}

lemma lappendt_respect [quot_respect]:
  "(op = ===> tlist_eq ===> tlist_eq) lAPPENDt lAPPENDt"
by(auto intro: ext)

lemma lappendt_LNil [simp, code, nitpick_simp]: "lappendt LNil tr = tr"
by(descending)(clarsimp simp add: TNIL_def)

lemma lappendt_LCons [simp, code, nitpick_simp]:
  "lappendt (LCons x xs) tr = TCons x (lappendt xs tr)"
by(descending)(auto simp add: TCONS_def)

subsection {* Filtering terminated lazy lists @{term tfilter} *}

lemma tfilter_respect [quot_respect]: 
  "(op = ===> op = ===> tlist_eq ===> tlist_eq) tFILTER tFILTER"
by(auto intro: ext)

lemma tfilter_TNil [code, simp]:
  "tfilter b' P (TNil b) = TNil b"
by(descending)(simp add: TNIL_def)

lemma tfilter_TCons [code, simp]:
  "tfilter b P (TCons a tr) = (if P a then TCons a (tfilter b P tr) else tfilter b P tr)"
by(descending)(auto simp add: TCONS_def)

subsection {* Concatenating a terminated lazy list of lazy lists @{term tconcat} *}

lemma tconcat_respect [quot_respect]:
  "(op = ===> tlist_eq ===> tlist_eq) tCONCAT tCONCAT"
by(auto intro: ext)

lemma tconcat_TNil [code, simp]: "tconcat b (TNil b') = TNil b'"
by(descending)(simp add: TNIL_def)

lemma tconcat_TCons [code, simp]: "tconcat b (TCons a tr) = lappendt a (tconcat b tr)"
by(descending)(clarsimp simp add: TCONS_def)

subsection {* @{term tllist_all2} *}

lemma tllist_all2_respect_tlist_eq [quot_respect]:
  "(op = ===> op = ===> tlist_eq ===> tlist_eq ===> op =) TLLIST_ALL2 TLLIST_ALL2"
by(auto dest: llist_all2_lfiniteD)

lemma tllist_all2_TNil [simp]:
  "tllist_all2 P Q (TNil b) (TNil b') \<longleftrightarrow> Q b b'"
by(descending)(simp add: TNIL_def)

lemma tllist_all2_TCons [simp]:
  "tllist_all2 P Q (TCons x ts) (TCons x' ts') \<longleftrightarrow> P x x' \<and> tllist_all2 P Q ts ts'"
by(descending)(auto simp add: TCONS_def)

lemma tllist_all2_TNil1: "tllist_all2 P Q (TNil b) ts \<longleftrightarrow> (\<exists>b'. ts = TNil b' \<and> Q b b')"
by(descending)(auto simp add: TNIL_def llist_all2_LNil1)

lemma tllist_all2_TNil2: "tllist_all2 P Q ts (TNil b') \<longleftrightarrow> (\<exists>b. ts = TNil b \<and> Q b b')"
by(descending)(auto simp add: TNIL_def llist_all2_LNil2)

lemma tllist_all2_TCons1: 
  "tllist_all2 P Q (TCons x ts) ts' \<longleftrightarrow> (\<exists>x' ts''. ts' = TCons x' ts'' \<and> P x x' \<and> tllist_all2 P Q ts ts'')"
by descending(fastsimp simp add: TCONS_def llist_all2_LCons1 dest: llist_all2_lfiniteD)

lemma tllist_all2_TCons2: 
  "tllist_all2 P Q ts' (TCons x ts) \<longleftrightarrow> (\<exists>x' ts''. ts' = TCons x' ts'' \<and> P x' x \<and> tllist_all2 P Q ts'' ts)"
by descending(fastsimp simp add: TCONS_def llist_all2_LCons2 dest: llist_all2_lfiniteD)

lemma tllist_all2_coinduct [consumes 1, case_names tllist_all2, case_conclusion tllist_all2 TNil TCons, coinduct pred]:
  assumes "X xs ys"
  and "\<And>xs ys. X xs ys \<Longrightarrow> 
  (\<exists>b b'. xs = TNil b \<and> ys = TNil b' \<and> R b b') \<or>
  (\<exists>x y xs' ys'. xs = TCons x xs' \<and> ys = TCons y ys' \<and> P x y \<and> (X xs' ys' \<or> tllist_all2 P R xs' ys'))"
  shows "tllist_all2 P R xs ys"
using assms
proof descending
  fix X xsb ysb R P
  assume major: "X xsb ysb"
  and step: "\<And>xsb ysb.
           X xsb ysb \<Longrightarrow>
           (\<exists>b b'. tlist_eq xsb (TNIL b) \<and> tlist_eq ysb (TNIL b') \<and> R b b') \<or>
           (\<exists>x y xsb' ysb'.
               tlist_eq xsb (TCONS x xsb') \<and>
               tlist_eq ysb (TCONS y ysb') \<and>
               P x y \<and> (X xsb' ysb' \<or> TLLIST_ALL2 P R xsb' ysb'))"
  obtain xs b where xsb [simp]: "xsb = (xs, b)" by(cases xsb)
  obtain ys b' where ysb [simp]: "ysb = (ys, b')" by(cases ysb)
  from major have "\<exists>b b'. X (xs, b) (ys, b')" by auto
  hence "llist_all2 P xs ys"
  proof(coinduct)
    case (llist_all2 xs ys)
    then obtain b b' where "X (xs, b) (ys, b')" by blast
    from step[OF this] show ?case
      by(auto simp add: TNIL_def TCONS_def)
  qed
  moreover {
    assume "lfinite xs"
    moreover from `llist_all2 P xs ys`
    have "llength xs = llength ys" by(rule llist_all2_llengthD)
    ultimately have "R b b'" using major unfolding xsb ysb
    proof(induct arbitrary: ys)
      case lfinite_LNil thus ?case
        by(auto dest: step simp add: TNIL_def TCONS_def)
    next
      case (lfinite_LConsI xs x)
      with step[OF `X (LCons x xs, b) (ys, b')`]
      show ?thesis 
        by(clarsimp simp add: TNIL_def TCONS_def)(auto simp add: lfinite_conv_llength_Fin)
    qed
  }
  ultimately show "TLLIST_ALL2 P R xsb ysb" by simp
qed

lemma tllist_all2_cases[consumes 1, case_names TNil TCons, cases pred]:
  assumes "tllist_all2 P Q xs ys"
  obtains (TNil) b b' where "xs = TNil b" "ys = TNil b'" "Q b b'"
  | (TCons) x xs' y ys'
    where "xs = TCons x xs'" and "ys = TCons y ys'" 
    and "P x y" and "tllist_all2 P Q xs' ys'"
using assms
by(cases xs)(fastsimp simp add: tllist_all2_TCons1 tllist_all2_TNil1)+

lemma tllist_all2_tmap1:
  "tllist_all2 P Q (tmap f g xs) ys \<longleftrightarrow> tllist_all2 (\<lambda>x. P (f x)) (\<lambda>x. Q (g x)) xs ys"
by(descending)(auto simp add: llist_all2_lmap1)

lemma tllist_all2_tmap2:
  "tllist_all2 P Q xs (tmap f g ys) \<longleftrightarrow> tllist_all2 (\<lambda>x y. P x (f y)) (\<lambda>x y. Q x (g y)) xs ys"
by(descending)(auto simp add: llist_all2_lmap2)

lemma tllist_all2_mono:
  "\<lbrakk> tllist_all2 P Q xs ys; \<And>x y. P x y \<Longrightarrow> P' x y; \<And>x y. Q x y \<Longrightarrow> Q' x y \<rbrakk>
  \<Longrightarrow> tllist_all2 P' Q' xs ys"
by descending(auto elim!: llist_all2_mono)

subsection {* From a terminated lazy list to a lazy list @{term llist_of_tllist} *}

lemma llist_of_tllist_respect [quot_respect]: 
  "(tlist_eq ===> op =) fst fst"
by auto

lemma llist_of_tllist_TNil [simp, code, nitpick_simp]:
  "llist_of_tllist (TNil b) = LNil"
by(descending)(simp add: TNIL_def)

lemma llist_of_tllist_TCons [simp, code, nitpick_simp]:
  "llist_of_tllist (TCons x xs) = LCons x (llist_of_tllist xs)"
by(descending)(simp add: TCONS_def)

lemma llist_of_tllist_tmap [simp]:
  "llist_of_tllist (tmap f g xs) = lmap f (llist_of_tllist xs)"
by descending(auto)

lemma tllist_of_llist_inverse [simp]:
  "llist_of_tllist (tllist_of_llist b xs) = xs"
by(rule llist_fun_equalityI) simp_all

lemma llist_of_tllist_inverse [simp]:
  "tllist_of_llist (terminal xs) (llist_of_tllist xs) = xs"
proof -
  have "(tllist_of_llist (terminal xs) (llist_of_tllist xs), xs) \<in> 
       {(tllist_of_llist (terminal xs) (llist_of_tllist xs), xs)|xs. True}"
    by blast
  thus ?thesis
  proof(coinduct rule: tllist_equalityI)
    case (Eqtllist q)
    then obtain xs where "q = (tllist_of_llist (terminal xs) (llist_of_tllist xs), xs)" by blast
    thus ?case by(cases xs) auto
  qed
qed

lemma llist_of_tllist_tappend:
  "llist_of_tllist (tappend xs f) = lappend (llist_of_tllist xs) (llist_of_tllist (f (terminal xs)))"
by(descending)(auto simp add: lappend_inf)

lemma llist_of_tllist_lappendt [simp]:
  "llist_of_tllist (lappendt xs tr) = lappend xs (llist_of_tllist tr)"
by descending auto

lemma llist_of_tllist_tfilter [simp]:
  "llist_of_tllist (tfilter b P tr) = lfilter P (llist_of_tllist tr)"
by descending auto

lemma llist_of_tllist_tconcat:
  "llist_of_tllist (tconcat b trs) = lconcat (llist_of_tllist trs)"
by descending auto

subsection {* The nth element of a terminated lazy list @{term "tnth"} *}

lemma TNTH_respect [quot_respect]:
  "(tlist_eq ===> op =) TNTH TNTH"
by auto

lemma tnth_TNil [nitpick_simp]:
  "tnth (TNil b) n = undefined n"
by(descending)(simp add: TNIL_def lnth_LNil)

lemma tnth_TCons:
  "tnth (TCons x xs) n = (case n of 0 \<Rightarrow> x | Suc n' \<Rightarrow> tnth xs n')"
by(descending)(auto simp add: TCONS_def lnth_LCons split: nat.split)

lemma [simp, nitpick_simp]:
  shows tnth_0: "tnth (TCons x xs) 0 = x"
  and tnth_Suc_TCons: "tnth (TCons x xs) (Suc n) = tnth xs n"
by(simp_all add: tnth_TCons)

lemma lnth_llist_of_tllist [simp]:
  "lnth (llist_of_tllist xs) = tnth xs"
by(descending)(auto)

subsection {* The length of a terminated lazy list @{term "tlength"} *}

lemma TLENGTH_respect [quot_respect]:
  "(tlist_eq ===> op =) TLENGTH TLENGTH"
by auto

lemma [simp, code, nitpick_simp]:
  shows tlength_TNil: "tlength (TNil b) = 0"
  and tlength_TCons: "tlength (TCons x xs) = iSuc (tlength xs)"
 apply(descending, simp add: TNIL_def)
apply(descending, auto simp add: TCONS_def)
done

lemma llength_llist_of_tllist [simp]: "llength (llist_of_tllist xs) = tlength xs"
by descending auto

subsection {* @{term "tdropn"} *}

lemma TDROPn_respect [quot_respect]:
  "(op = ===> tlist_eq ===> tlist_eq) TDROPn TDROPn"
by auto

lemma tdropn_0 [simp, code, nitpick_simp]: "tdropn 0 xs = xs"
by descending auto

lemma tdropn_TNil [simp, code]: "tdropn n (TNil b) = (TNil b)"
by descending(auto simp add: TNIL_def)

lemma tdropn_Suc_TCons [simp, code]: "tdropn (Suc n) (TCons x xs) = tdropn n xs"
by descending(auto simp add: TCONS_def)

lemma tdropn_Suc [nitpick_simp]: "tdropn (Suc n) xs = (case xs of TNil b \<Rightarrow> TNil b | TCons x xs' \<Rightarrow> tdropn n xs')"
by(cases xs) simp_all -- "FIXME: Ask Cezary/Christian why descending / lifting raises a type error here"

lemma lappendt_ltake_tdropn:
  "lappendt (ltake (Fin n) (llist_of_tllist xs)) (tdropn n xs) = xs"
by descending (auto)

lemma llist_of_tllist_tdropn [simp]:
  "llist_of_tllist (tdropn n xs) = ldropn n (llist_of_tllist xs)"
by descending auto

lemma tdropn_Suc_conv_tdropn:
  "Fin n < tlength xs \<Longrightarrow> TCons (tnth xs n) (tdropn (Suc n) xs) = tdropn n xs" 
by descending(auto simp add: TCONS_def ldropn_Suc_conv_ldropn)

lemma tlength_tdropn [simp]: "tlength (tdropn n xs) = tlength xs - Fin n"
by descending auto

lemma tnth_tdropn [simp]: "Fin (n + m) < tlength xs \<Longrightarrow> tnth (tdropn n xs) m = tnth xs (m + n)"
by descending auto

end