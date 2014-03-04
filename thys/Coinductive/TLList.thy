(*  Title:       Terminated coinductive list
    Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)

header {* Terminated coinductive lists *}

theory TLList imports
  Coinductive_List
begin

text {*
  Terminated coinductive lists @{text "('a, 'b) tllist"} are the codatatype defined by the construtors
  @{text "TNil"} of type @{text "'b \<Rightarrow> ('a, 'b) tllist"} and
  @{text "TCons"} of type @{text "'a \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"}.
*}

subsection {* Auxiliary lemmas *}

lemma split_fst: "R (fst p) = (\<forall>x y. p = (x, y) \<longrightarrow> R x)"
by(cases p) simp

lemma split_fst_asm: "R (fst p) \<longleftrightarrow> (\<not> (\<exists>x y. p = (x, y) \<and> \<not> R x))"
by(cases p) simp

subsection {* Type definition *}

consts terminal0 :: "'a"

codatatype (tset: 'a, 'b) tllist (map: tmap rel: tllist_all2) =
    TNil (terminal : 'b) (defaults thd : "\<lambda>_. undefined" ttl: "\<lambda>b. TNil b")
  | TCons (thd : 'a) (ttl : "('a, 'b) tllist")
    (defaults terminal: "\<lambda>x :: 'a. \<lambda>xs :: ('a, 'b) tllist. (terminal0 xs :: 'b)")

overloading
  terminal0 == "terminal0::('a, 'b) tllist \<Rightarrow> 'b"
begin

partial_function (tailrec) terminal0 
where "terminal0 xs = (if is_TNil xs then case_tllist id undefined xs else terminal0 (ttl xs))"

end

lemma terminal0_terminal [simp]: "terminal0 = terminal"
apply(rule ext)
apply(subst terminal0.simps)
apply(case_tac x)
apply(simp_all add: terminal_def)
done

lemmas terminal_TNil [code, nitpick_simp] = tllist.sel(1)

lemma terminal_TCons [simp, code, nitpick_simp]: "terminal (TCons x xs) = terminal xs"
by simp

declare tllist.sel(2) [simp del]

primcorec unfold_tllist :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ('c, 'b) tllist" where
  "p a \<Longrightarrow> unfold_tllist p g1 g21 g22 a = TNil (g1 a)" |
  "_ \<Longrightarrow> unfold_tllist p g1 g21 g22 a =
     TCons (g21 a) (unfold_tllist p g1 g21 g22 (g22 a))"

declare
  unfold_tllist.ctr(1) [simp]
  tllist.corec(1) [simp]

subsection {* Code generator setup *}

text {* Setup for quickcheck *}

notation fcomp (infixl "o>" 60)
notation scomp (infixl "o\<rightarrow>" 60)

definition (in term_syntax) valtermify_TNil ::
  "'b :: typerep \<times> (unit \<Rightarrow> Code_Evaluation.term)
   \<Rightarrow> ('a :: typerep, 'b) tllist \<times> (unit \<Rightarrow> Code_Evaluation.term)" 
where
  "valtermify_TNil b = Code_Evaluation.valtermify TNil {\<cdot>} b"

definition (in term_syntax) valtermify_TCons ::
  "'a :: typerep \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow> ('a, 'b :: typerep) tllist \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow> ('a, 'b) tllist \<times> (unit \<Rightarrow> Code_Evaluation.term)" where
  "valtermify_TCons x xs = Code_Evaluation.valtermify TCons {\<cdot>} x {\<cdot>} xs"

instantiation tllist :: (random, random) random begin

primrec random_aux_tllist :: 
  "natural \<Rightarrow> natural \<Rightarrow> Random.seed \<Rightarrow> (('a, 'b) tllist \<times> (unit \<Rightarrow> Code_Evaluation.term)) \<times> Random.seed"
where
  "random_aux_tllist 0 j = 
   Quickcheck_Random.collapse (Random.select_weight 
     [(1, Quickcheck_Random.random j o\<rightarrow> (\<lambda>b. Pair (valtermify_TNil b)))])"
| "random_aux_tllist (Code_Numeral.Suc i) j =
   Quickcheck_Random.collapse (Random.select_weight
     [(Code_Numeral.Suc i, Quickcheck_Random.random j o\<rightarrow> (\<lambda>x. random_aux_tllist i j o\<rightarrow> (\<lambda>xs. Pair (valtermify_TCons x xs)))),
      (1, Quickcheck_Random.random j o\<rightarrow> (\<lambda>b. Pair (valtermify_TNil b)))])"

definition "Quickcheck_Random.random i = random_aux_tllist i i"

instance ..

end

lemma random_aux_tllist_code [code]:
  "random_aux_tllist i j = Quickcheck_Random.collapse (Random.select_weight
     [(i, Quickcheck_Random.random j o\<rightarrow> (\<lambda>x. random_aux_tllist (i - 1) j o\<rightarrow> (\<lambda>xs. Pair (valtermify_TCons x xs)))),
      (1, Quickcheck_Random.random j o\<rightarrow> (\<lambda>b. Pair (valtermify_TNil b)))])"
  apply (cases i rule: natural.exhaust)
  apply (simp_all only: random_aux_tllist.simps natural_zero_minus_one Suc_natural_minus_one)
  apply (subst select_weight_cons_zero) apply (simp only:)
  done

no_notation fcomp (infixl "o>" 60)
no_notation scomp (infixl "o\<rightarrow>" 60)

instantiation tllist :: (full_exhaustive, full_exhaustive) full_exhaustive begin

fun full_exhaustive_tllist 
  ::"(('a, 'b) tllist \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
where
  "full_exhaustive_tllist f i =
   (let A = Typerep.typerep TYPE('a);
        B = Typerep.typerep TYPE('b);
        Tllist = \<lambda>A B. Typerep.Typerep (STR ''TLList.tllist'') [A, B];
        fun = \<lambda>A B. Typerep.Typerep (STR ''fun'') [A, B]
    in
      if 0 < i then 
        case Quickcheck_Exhaustive.full_exhaustive (\<lambda>(b, bt). f (TNil b, \<lambda>_. Code_Evaluation.App 
          (Code_Evaluation.Const (STR ''TLList.TNil'') (fun B (Tllist A B)))
          (bt ()))) (i - 1)
        of None \<Rightarrow> 
            Quickcheck_Exhaustive.full_exhaustive (\<lambda>(x, xt). full_exhaustive_tllist (\<lambda>(xs, xst). 
              f (TCons x xs, \<lambda>_. Code_Evaluation.App (Code_Evaluation.App 
                   (Code_Evaluation.Const (STR ''TLList.TCons'') (fun A (fun (Tllist A B) (Tllist A B))))
                   (xt ())) (xst ())))
              (i - 1)) (i - 1)
        | Some ts \<Rightarrow> Some ts
      else None)"

instance ..

end

instantiation tllist :: (narrowing, narrowing) narrowing begin

context
includes integer.lifting
begin

function narrowing_tllist
where
  "narrowing_tllist n = Quickcheck_Narrowing.sum
    (Quickcheck_Narrowing.apply (Quickcheck_Narrowing.cons TNil) narrowing)
    (Quickcheck_Narrowing.apply (Quickcheck_Narrowing.apply (Quickcheck_Narrowing.cons TCons) narrowing) narrowing_tllist)
    n"
by pat_completeness auto
termination by (relation "measure nat_of_integer") (simp_all, transfer, simp)

instance ..

end
end

text {* More lemmas about generated constants *}

lemma ttl_unfold_tllist:
  "ttl (unfold_tllist IS_TNIL TNIL THD TTL a) = 
  (if IS_TNIL a then TNil (TNIL a) else unfold_tllist IS_TNIL TNIL THD TTL (TTL a))"
by(simp)

lemma is_TNil_ttl [simp]: "is_TNil xs \<Longrightarrow> is_TNil (ttl xs)"
by(cases xs) simp_all

lemma terminal_ttl [simp]: "terminal (ttl xs) = terminal xs"
by(cases xs) simp_all

lemma unfold_tllist_eq_TNil [simp]:
  "unfold_tllist IS_TNIL TNIL THD TTL a = TNil b \<longleftrightarrow> IS_TNIL a \<and> b = TNIL a"
by(auto simp add: unfold_tllist.code)

lemma TNil_eq_unfold_tllist [simp]:
  "TNil b = unfold_tllist IS_TNIL TNIL THD TTL a \<longleftrightarrow> IS_TNIL a \<and> b = TNIL a"
by(auto simp add: unfold_tllist.code)

lemma is_TNil_tmap [simp]: "is_TNil (tmap f g xs) \<longleftrightarrow> is_TNil xs"
by(cases xs) simp_all

lemma tmap_is_TNil: "is_TNil xs \<Longrightarrow> tmap f g xs = TNil (g (terminal xs))"
by(clarsimp simp add: is_TNil_def)

lemma thd_tmap [simp]: "\<not> is_TNil xs \<Longrightarrow> thd (tmap f g xs) = f (thd xs)"
by(cases xs) simp_all

lemma ttl_tmap [simp]: "ttl (tmap f g xs) = tmap f g (ttl xs)"
by(cases xs) simp_all

lemma tmap_eq_TNil_conv:
  "tmap f g xs = TNil y \<longleftrightarrow> (\<exists>y'. xs = TNil y' \<and> g y' = y)"
by(cases xs) simp_all

lemma TNil_eq_tmap_conv:
  "TNil y = tmap f g xs \<longleftrightarrow> (\<exists>y'. xs = TNil y' \<and> g y' = y)"
by(cases xs) auto

lemma thd_in_tset [simp]: "\<not> is_TNil xs \<Longrightarrow> thd xs \<in> tset xs"
by(cases xs) simp_all

lemma tset_ttl: "tset (ttl xs) \<subseteq> tset xs"
by(cases xs) auto

lemma in_tset_ttlD: "x \<in> tset (ttl xs) \<Longrightarrow> x \<in> tset xs"
using tset_ttl[of xs] by auto

lemma case_tllist_def':
"case_tllist tnil tcons xs = (case dtor_tllist xs of Inl z \<Rightarrow> tnil z | Inr (y, ys) \<Rightarrow> tcons y ys)"
apply (case_tac xs)
by auto (auto simp add: TNil_def TCons_def tllist.dtor_ctor BNF_Comp.id_bnf_comp_def)

theorem tllist_set_induct[consumes 1, case_names find step]:
  assumes "x \<in> tset xs" and "\<And>xs. \<not> is_TNil xs \<Longrightarrow> P (thd xs) xs"
  and "\<And>xs y. \<lbrakk>\<not> is_TNil xs; y \<in> tset (ttl xs); P y (ttl xs)\<rbrakk> \<Longrightarrow> P y xs"
  shows "P x xs"
proof -
  have "\<forall>x\<in>tset xs. P x xs"
    apply(rule tllist.dtor_set1_induct)
    using assms
    apply(auto simp add: thd_def ttl_def set2_pre_tllist_def set3_pre_tllist_def set1_pre_tllist_def fsts_def snds_def case_tllist_def' collect_def sum_set_simps sum.set_map split: sum.splits)
     apply(erule_tac x="b" in meta_allE)
     apply(erule meta_impE)
      apply(case_tac b)
       apply(clarsimp simp add: TNil_def tllist.dtor_ctor sum_set_simps BNF_Comp.id_bnf_comp_def)
      apply(clarsimp simp add: TNil_def tllist.dtor_ctor sum_set_simps)
     apply(case_tac b)
     apply(simp_all add: TNil_def TCons_def tllist.dtor_ctor sum_set_simps BNF_Comp.id_bnf_comp_def)[2]
    apply(rotate_tac -2)
    apply(erule_tac x="b" in meta_allE)
    apply(erule_tac x="xa" in meta_allE)
    apply(erule meta_impE)
     apply(case_tac b)
      apply(clarsimp simp add: TNil_def tllist.dtor_ctor sum_set_simps BNF_Comp.id_bnf_comp_def)
     apply(clarsimp simp add: TNil_def tllist.dtor_ctor sum_set_simps)
    apply(case_tac b)
    apply(simp_all add: TNil_def TCons_def tllist.dtor_ctor sum_set_simps BNF_Comp.id_bnf_comp_def)
    done
  with `x \<in> tset xs` show ?thesis by blast
qed

theorem set2_tllist_induct[consumes 1, case_names find step]:
  assumes "x \<in> set2_tllist xs" and "\<And>xs. is_TNil xs \<Longrightarrow> P (terminal xs) xs"
  and "\<And>xs y. \<lbrakk>\<not> is_TNil xs; y \<in> set2_tllist (ttl xs); P y (ttl xs)\<rbrakk> \<Longrightarrow> P y xs"
  shows "P x xs"
proof -
  have "\<forall>x\<in>set2_tllist xs. P x xs"
    apply(rule tllist.dtor_set2_induct)
    using assms
    apply(auto simp add: is_TNil_def thd_def ttl_def terminal_def set2_pre_tllist_def
      set3_pre_tllist_def set1_pre_tllist_def fsts_def snds_def case_tllist_def' collect_def
      sum_set_simps sum.set_map split: sum.splits)
     apply(case_tac b)
      apply(simp add: TNil_def tllist.dtor_ctor sum_set_simps BNF_Comp.id_bnf_comp_def)
      apply(erule_tac x="b" in meta_allE)
      apply(erule meta_impE)
       apply fastforce
      apply(simp add: tllist.dtor_ctor BNF_Comp.id_bnf_comp_def)
     apply(simp add: TCons_def tllist.dtor_ctor sum_set_simps BNF_Comp.id_bnf_comp_def)
    apply(rotate_tac -2)
    apply(erule_tac x="b" in meta_allE)
    apply(erule_tac x="xa" in meta_allE)
    apply(erule meta_impE)
     apply(case_tac b)
      apply(clarsimp simp add: TNil_def tllist.dtor_ctor sum_set_simps BNF_Comp.id_bnf_comp_def)
     apply(clarsimp simp add: TNil_def tllist.dtor_ctor sum_set_simps BNF_Comp.id_bnf_comp_def)
    apply(case_tac b)
    apply(simp_all add: TNil_def TCons_def tllist.dtor_ctor sum_set_simps BNF_Comp.id_bnf_comp_def)
    done
  with `x \<in> set2_tllist xs` show ?thesis by blast
qed


subsection {* Connection with @{typ "'a llist"} *}

context fixes b :: 'b begin
primcorec tllist_of_llist :: "'a llist \<Rightarrow> ('a, 'b) tllist" where
  "tllist_of_llist xs = (case xs of LNil \<Rightarrow> TNil b | LCons x xs' \<Rightarrow> TCons x (tllist_of_llist xs'))"
end

primcorec llist_of_tllist :: "('a, 'b) tllist \<Rightarrow> 'a llist"
where "llist_of_tllist xs = (case xs of TNil _ \<Rightarrow> LNil | TCons x xs' \<Rightarrow> LCons x (llist_of_tllist xs'))"

simps_of_case tllist_of_llist_simps [simp, code, nitpick_simp]: tllist_of_llist.code

lemmas tllist_of_llist_LNil = tllist_of_llist_simps(1)
  and tllist_of_llist_LCons = tllist_of_llist_simps(2)

lemma terminal_tllist_of_llist_lnull [simp]:
  "lnull xs \<Longrightarrow> terminal (tllist_of_llist b xs) = b"
unfolding lnull_def by simp

declare tllist_of_llist.sel(1)[simp del]

lemma lhd_LNil: "lhd LNil = undefined"
by(simp add: lhd_def)

lemma thd_TNil: "thd (TNil b) = undefined"
by(simp add: thd_def)

lemma thd_tllist_of_llist [simp]: "thd (tllist_of_llist b xs) = lhd xs"
by(cases xs)(simp_all add: thd_TNil lhd_LNil)

lemma ttl_tllist_of_llist [simp]: "ttl (tllist_of_llist b xs) = tllist_of_llist b (ltl xs)"
by(cases xs) simp_all

lemma llist_of_tllist_eq_LNil:
  "llist_of_tllist xs = LNil \<longleftrightarrow> is_TNil xs"
using llist_of_tllist.disc_iff(1) unfolding lnull_def .

simps_of_case llist_of_tllist_simps [simp, code, nitpick_simp]: llist_of_tllist.code

lemmas llist_of_tllist_TNil = llist_of_tllist_simps(1)
  and llist_of_tllist_TCons = llist_of_tllist_simps(2)

declare llist_of_tllist.sel [simp del]

lemma lhd_llist_of_tllist [simp]: "\<not> is_TNil xs \<Longrightarrow> lhd (llist_of_tllist xs) = thd xs"
by(cases xs) simp_all

lemma ltl_llist_of_tllist [simp]:
  "ltl (llist_of_tllist xs) = llist_of_tllist (ttl xs)"
by(cases xs) simp_all

lemma tllist_of_llist_cong [cong]:
  assumes "xs = xs'" "lfinite xs' \<Longrightarrow> b = b'"
  shows "tllist_of_llist b xs = tllist_of_llist b' xs'"
proof(unfold `xs = xs'`)
  from assms have "lfinite xs' \<longrightarrow> b = b'" by simp
  thus "tllist_of_llist b xs' = tllist_of_llist b' xs'"
    by(coinduction arbitrary: xs') auto
qed

lemma llist_of_tllist_inverse [simp]: 
  "tllist_of_llist (terminal b) (llist_of_tllist b) = b"
by(coinduction arbitrary: b) simp_all

lemma tllist_of_llist_eq [simp]: "tllist_of_llist b' xs = TNil b \<longleftrightarrow> b = b' \<and> xs = LNil"
by(cases xs) auto

lemma TNil_eq_tllist_of_llist [simp]: "TNil b = tllist_of_llist b' xs \<longleftrightarrow> b = b' \<and> xs = LNil"
by(cases xs) auto

lemma tllist_of_llist_inject [simp]:
  "tllist_of_llist b xs = tllist_of_llist c ys \<longleftrightarrow> xs = ys \<and> (lfinite ys \<longrightarrow> b = c)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof(intro iffI conjI impI)
  assume ?rhs
  thus ?lhs by(auto intro: tllist_of_llist_cong)
next
  assume ?lhs
  thus "xs = ys"
    by(coinduction arbitrary: xs ys)(auto simp add: lnull_def neq_LNil_conv)
  assume "lfinite ys"
  thus "b = c" using `?lhs`
    unfolding `xs = ys` by(induct) simp_all
qed

lemma tllist_of_llist_inverse [simp]:
  "llist_of_tllist (tllist_of_llist b xs) = xs"
by(coinduction arbitrary: xs) auto


definition cr_tllist :: "('a llist \<times> 'b) \<Rightarrow> ('a, 'b) tllist \<Rightarrow> bool"
  where "cr_tllist \<equiv> (\<lambda>(xs, b) ys. tllist_of_llist b xs = ys)"

lemma Quotient_tllist:
  "Quotient (\<lambda>(xs, a) (ys, b). xs = ys \<and> (lfinite ys \<longrightarrow> a = b))
     (\<lambda>(xs, a). tllist_of_llist a xs) (\<lambda>ys. (llist_of_tllist ys, terminal ys)) cr_tllist"
unfolding Quotient_alt_def cr_tllist_def by(auto intro: tllist_of_llist_cong)

lemma reflp_tllist: "reflp (\<lambda>(xs, a) (ys, b). xs = ys \<and> (lfinite ys \<longrightarrow> a = b))"
by(simp add: reflp_def)

setup_lifting (no_code) Quotient_tllist reflp_tllist

context
begin
interpretation lifting_syntax .

lemma TNil_transfer [transfer_rule]:
  "(B ===> pcr_tllist A B) (Pair LNil) TNil"
by(auto simp add: pcr_tllist_def cr_tllist_def intro!: fun_relI relcomppI)

lemma TCons_transfer [transfer_rule]:
  "(A ===> pcr_tllist A B ===> pcr_tllist A B) (apfst \<circ> LCons) TCons"
by(auto 4 3 intro!: fun_relI relcomppI simp add: pcr_tllist_def prod_rel_def llist_all2_LCons1 cr_tllist_def)

lemma tmap_tllist_of_llist:
  "tmap f g (tllist_of_llist b xs) = tllist_of_llist (g b) (lmap f xs)"
by(coinduction arbitrary: xs)(auto simp add: tmap_is_TNil)

lemma tmap_transfer [transfer_rule]:
  "(op = ===> op = ===> pcr_tllist op = op = ===> pcr_tllist op = op =) (map_pair \<circ> lmap) tmap"
by(auto intro!: fun_relI simp add: cr_tllist_def tllist.pcr_cr_eq tmap_tllist_of_llist)

lemma lset_llist_of_tllist [simp]:
  "lset (llist_of_tllist xs) = tset xs" (is "?lhs = ?rhs")
proof(intro set_eqI iffI)
  fix x
  assume "x \<in> ?lhs"
  thus "x \<in> ?rhs"
    by(induct "llist_of_tllist xs" arbitrary: xs rule: llist_set_induct)(auto dest: in_tset_ttlD)
next
  fix x
  assume "x \<in> ?rhs"
  thus "x \<in> ?lhs"
  proof(induct rule: tllist_set_induct)
    case (find xs)
    thus ?case by(cases xs) auto
  next
    case step
    thus ?case
      by(auto simp add: ltl_llist_of_tllist[symmetric] simp del: ltl_llist_of_tllist dest: in_lset_ltlD)
  qed
qed

lemma tset_tllist_of_llist [simp]:
  "tset (tllist_of_llist b xs) = lset xs"
by(simp add: lset_llist_of_tllist[symmetric] del: lset_llist_of_tllist)

lemma tset_transfer [transfer_rule]:
  "(pcr_tllist op = op = ===> op =) (lset \<circ> fst) tset"
by(auto simp add: cr_tllist_def tllist.pcr_cr_eq)

lemma is_TNil_transfer [transfer_rule]:
  "(pcr_tllist op = op = ===> op =) (\<lambda>(xs, b). lnull xs) is_TNil"
by(auto simp add: tllist.pcr_cr_eq cr_tllist_def)

lemma thd_transfer [transfer_rule]:
  "(pcr_tllist op = op = ===> op =) (lhd \<circ> fst) thd"
by(auto simp add: cr_tllist_def tllist.pcr_cr_eq)

lemma ttl_transfer [transfer_rule]:
  "(pcr_tllist A B ===> pcr_tllist A B) (apfst ltl) ttl"
by(auto simp add: pcr_tllist_def cr_tllist_def prod_rel_def intro!: fun_relI relcomppI intro: llist_all2_ltlI)

lemma llist_of_tllist_transfer [transfer_rule]:
  "(pcr_tllist op = B ===> op =) fst llist_of_tllist"
by(auto simp add: pcr_tllist_def cr_tllist_def llist_all2_eq)

lemma tllist_of_llist_transfer [transfer_rule]:
  "(op = ===> op = ===> pcr_tllist op = op =) (\<lambda>b xs. (xs, b)) tllist_of_llist"
by(auto simp add: tllist.pcr_cr_eq cr_tllist_def)

lemma terminal_tllist_of_llist_lfinite [simp]:
  "lfinite xs \<Longrightarrow> terminal (tllist_of_llist b xs) = b"
by(induct rule: lfinite.induct) simp_all

lemma set2_tllist_tllist_of_llist [simp]:
  "set2_tllist (tllist_of_llist b xs) = (if lfinite xs then {b} else {})"
proof(cases "lfinite xs")
  case True
  thus ?thesis by(induct) auto
next
  case False
  { fix x
    assume "x \<in> set2_tllist (tllist_of_llist b xs)"
    hence False using False
      by(induct "tllist_of_llist b xs" arbitrary: xs rule: set2_tllist_induct) fastforce+ }
  thus ?thesis using False by auto
qed

lemma set2_tllist_transfer [transfer_rule]:
  "(pcr_tllist A B ===> set_rel B) (\<lambda>(xs, b). if lfinite xs then {b} else {}) set2_tllist"
by(auto 4 4 simp add: pcr_tllist_def cr_tllist_def dest: llist_all2_lfiniteD intro: set_relI)

lemma tllist_all2_transfer [transfer_rule]:
  "(op = ===> op = ===> pcr_tllist op = op = ===> pcr_tllist op = op = ===> op =)
     (\<lambda>P Q (xs, b) (ys, b'). llist_all2 P xs ys \<and> (lfinite xs \<longrightarrow> Q b b')) tllist_all2"
unfolding tllist.pcr_cr_eq
apply(rule fun_relI)+
apply(clarsimp simp add: cr_tllist_def llist_all2_def tllist_all2_def)
apply(safe elim!: GrpE)
   apply simp_all
   apply(rule_tac b="tllist_of_llist (b, ba) bb" in relcomppI)
    apply(auto intro!: GrpI simp add: tmap_tllist_of_llist)[2]
  apply(rule_tac b="tllist_of_llist (b, ba) bb" in relcomppI)
   apply(auto simp add: tmap_tllist_of_llist intro!: GrpI split: split_if_asm)[2]
 apply(rule_tac b="llist_of_tllist bb" in relcomppI)
apply(auto intro!: GrpI)
apply(transfer, auto intro: GrpI split: split_if_asm)+
done

subsection {* Library function definitions *}

text {* 
  We lift the constants from @{typ "'a llist"} to @{typ "('a, 'b) tllist"} using the lifting package.
  This way, many results are transferred easily.
*}

lift_definition tappend :: "('a, 'b) tllist \<Rightarrow> ('b \<Rightarrow> ('a, 'c) tllist) \<Rightarrow> ('a, 'c) tllist"
is "\<lambda>(xs, b) f. apfst (lappend xs) (f b)"
by(auto simp add: split_def lappend_inf)

lift_definition lappendt :: "'a llist \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
is "apfst \<circ> lappend"
by(simp add: split_def)

lift_definition tfilter :: "'b \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
is "\<lambda>b P (xs, b'). (lfilter P xs, if lfinite xs then b' else b)"
by(simp add: split_beta)

lift_definition tconcat :: "'b \<Rightarrow> ('a llist, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
is "\<lambda>b (xss, b'). (lconcat xss, if lfinite xss then b' else b)"
by(simp add: split_beta)

lift_definition tnth :: "('a, 'b) tllist \<Rightarrow> nat \<Rightarrow> 'a"
is "lnth \<circ> fst" by(auto)

lift_definition tlength :: "('a, 'b) tllist \<Rightarrow> enat"
is "llength \<circ> fst" by auto

lift_definition tdropn :: "nat \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
is "apfst \<circ> ldropn" by auto

abbreviation tfinite :: "('a, 'b) tllist \<Rightarrow> bool"
where "tfinite xs \<equiv> lfinite (llist_of_tllist xs)"

subsection {* @{term "tfinite"} *}

lemma tfinite_induct [consumes 1, case_names TNil TCons]:
  assumes "tfinite xs"
  and "\<And>y. P (TNil y)"
  and "\<And>x xs. \<lbrakk>tfinite xs; P xs\<rbrakk> \<Longrightarrow> P (TCons x xs)"
  shows "P xs"
using assms
by transfer (clarsimp, erule lfinite.induct)

lemma is_TNil_tfinite [simp]: "is_TNil xs \<Longrightarrow> tfinite xs"
by transfer clarsimp

subsection {* The terminal element @{term "terminal"} *}

lemma terminal_tinfinite:
  assumes "\<not> tfinite xs"
  shows "terminal xs = undefined"
unfolding terminal0_terminal[symmetric]
using assms
apply(rule contrapos_np)
by(induct xs rule: terminal0.raw_induct[rotated 1, OF refl, consumes 1])(auto split: tllist.split_asm) 

lemma terminal_tllist_of_llist:
  "terminal (tllist_of_llist y xs) = (if lfinite xs then y else undefined)"
by(simp add: terminal_tinfinite)

lemma terminal_transfer [transfer_rule]:
  "(pcr_tllist A op = ===> op =) (\<lambda>(xs, b). if lfinite xs then b else undefined) terminal"
by(auto simp add: cr_tllist_def pcr_tllist_def terminal_tllist_of_llist intro!: fun_relI dest: llist_all2_lfiniteD)

lemma terminal_tmap [simp]: "tfinite xs \<Longrightarrow> terminal (tmap f g xs) = g (terminal xs)"
by(induct rule: tfinite_induct) simp_all

subsection {* @{term "tmap"} *}

lemma tmap_eq_TCons_conv:
  "tmap f g xs = TCons y ys \<longleftrightarrow>
  (\<exists>z zs. xs = TCons z zs \<and> f z = y \<and> tmap f g zs = ys)"
by(cases xs) simp_all

lemma TCons_eq_tmap_conv:
  "TCons y ys = tmap f g xs \<longleftrightarrow>
  (\<exists>z zs. xs = TCons z zs \<and> f z = y \<and> tmap f g zs = ys)"
by(cases xs) auto

subsection {* Appending two terminated lazy lists @{term "tappend" } *}

lemma tappend_TNil [simp, code, nitpick_simp]:
  "tappend (TNil b) f = f b"
by transfer auto

lemma tappend_TCons [simp, code, nitpick_simp]:
  "tappend (TCons a tr) f = TCons a (tappend tr f)"
by transfer(auto simp add: apfst_def map_pair_def split: prod.splits)

subsection {* Appending a terminated lazy list to a lazy list @{term "lappendt"} *}

lemma lappendt_LNil [simp, code, nitpick_simp]: "lappendt LNil tr = tr"
by transfer auto

lemma lappendt_LCons [simp, code, nitpick_simp]:
  "lappendt (LCons x xs) tr = TCons x (lappendt xs tr)"
by transfer auto

lemma terminal_lappendt_lfinite [simp]:
  "lfinite xs \<Longrightarrow> terminal (lappendt xs ys) = terminal ys"
by transfer auto

lemma tllist_of_llist_eq_lappendt_conv:
  "tllist_of_llist a xs = lappendt ys zs \<longleftrightarrow> 
  (\<exists>xs' a'. xs = lappend ys xs' \<and> zs = tllist_of_llist a' xs' \<and> (lfinite ys \<longrightarrow> a = a'))"
by transfer auto

lemma tset_lappendt_lfinite [simp]:
  "lfinite xs \<Longrightarrow> tset (lappendt xs ys) = lset xs \<union> tset ys"
by transfer auto

subsection {* Filtering terminated lazy lists @{term tfilter} *}

lemma tfilter_TNil [simp]:
  "tfilter b' P (TNil b) = TNil b"
by transfer auto

lemma tfilter_TCons [simp]:
  "tfilter b P (TCons a tr) = (if P a then TCons a (tfilter b P tr) else tfilter b P tr)"
by transfer auto

lemma is_TNil_tfilter[simp]:
  "is_TNil (tfilter y P xs) \<longleftrightarrow> (\<forall>x \<in> tset xs. \<not> P x)"
by transfer auto

lemma tfilter_empty_conv:
  "tfilter y P xs = TNil y' \<longleftrightarrow> (\<forall>x \<in> tset xs. \<not> P x) \<and> (if tfinite xs then terminal xs = y' else y = y')"
by transfer(clarsimp simp add: lfilter_eq_LNil)

lemma tfilter_eq_TConsD:
  "tfilter a P ys = TCons x xs \<Longrightarrow>
   \<exists>us vs. ys = lappendt us (TCons x vs) \<and> lfinite us \<and> (\<forall>u\<in>lset us. \<not> P u) \<and> P x \<and> xs = tfilter a P vs"
by transfer(fastforce dest: lfilter_eq_LConsD[OF sym])

text {* Use a version of @{term "tfilter"} for code generation that does not evaluate the first argument *}

definition tfilter' :: "(unit \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
where [simp, code del]: "tfilter' b = tfilter (b ())"

lemma tfilter_code [code, code_unfold]:
  "tfilter = (\<lambda>b. tfilter' (\<lambda>_. b))" 
by simp

lemma tfilter'_code [code]:
  "tfilter' b' P (TNil b) = TNil b"
  "tfilter' b' P (TCons a tr) = (if P a then TCons a (tfilter' b' P tr) else tfilter' b' P tr)"
by simp_all

end

hide_const (open) tfilter'

subsection {* Concatenating a terminated lazy list of lazy lists @{term tconcat} *}

lemma tconcat_TNil [simp]: "tconcat b (TNil b') = TNil b'"
by transfer auto

lemma tconcat_TCons [simp]: "tconcat b (TCons a tr) = lappendt a (tconcat b tr)"
by transfer auto

text {* Use a version of @{term "tconcat"} for code generation that does not evaluate the first argument *}

definition tconcat' :: "(unit \<Rightarrow> 'b) \<Rightarrow> ('a llist, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
where [simp, code del]: "tconcat' b = tconcat (b ())"

lemma tconcat_code [code, code_unfold]: "tconcat = (\<lambda>b. tconcat' (\<lambda>_. b))"
by simp

lemma tconcat'_code [code]:
  "tconcat' b (TNil b') = TNil b'"
  "tconcat' b (TCons a tr) = lappendt a (tconcat' b tr)"
by simp_all

hide_const (open) tconcat'

subsection {* @{term tllist_all2} *}

lemmas tllist_all2_TNil = tllist.rel_inject(1)
lemmas tllist_all2_TCons = tllist.rel_inject(2)

lemma tllist_all2_TNil1: "tllist_all2 P Q (TNil b) ts \<longleftrightarrow> (\<exists>b'. ts = TNil b' \<and> Q b b')"
by transfer auto

lemma tllist_all2_TNil2: "tllist_all2 P Q ts (TNil b') \<longleftrightarrow> (\<exists>b. ts = TNil b \<and> Q b b')"
by transfer auto

lemma tllist_all2_TCons1: 
  "tllist_all2 P Q (TCons x ts) ts' \<longleftrightarrow> (\<exists>x' ts''. ts' = TCons x' ts'' \<and> P x x' \<and> tllist_all2 P Q ts ts'')"
by transfer(fastforce simp add: llist_all2_LCons1 dest: llist_all2_lfiniteD)

lemma tllist_all2_TCons2: 
  "tllist_all2 P Q ts' (TCons x ts) \<longleftrightarrow> (\<exists>x' ts''. ts' = TCons x' ts'' \<and> P x' x \<and> tllist_all2 P Q ts'' ts)"
by transfer(fastforce simp add: llist_all2_LCons2 dest: llist_all2_lfiniteD)

lemma tllist_all2_coinduct [consumes 1, case_names tllist_all2, case_conclusion tllist_all2 is_TNil TNil TCons, coinduct pred: tllist_all2]:
  assumes "X xs ys"
  and "\<And>xs ys. X xs ys \<Longrightarrow>
  (is_TNil xs \<longleftrightarrow> is_TNil ys) \<and>
  (is_TNil xs \<longrightarrow> is_TNil ys \<longrightarrow> R (terminal xs) (terminal ys)) \<and>
  (\<not> is_TNil xs \<longrightarrow> \<not> is_TNil ys \<longrightarrow> P (thd xs) (thd ys) \<and> (X (ttl xs) (ttl ys) \<or> tllist_all2 P R (ttl xs) (ttl ys)))"
  shows "tllist_all2 P R xs ys"
using assms
apply(transfer fixing: P R)
apply clarsimp
apply(rule conjI)
 apply(erule llist_all2_coinduct, blast, blast)
proof(rule impI)
  case (goal1 X xs b ys c)
  from `lfinite xs` `X (xs, b) (ys, c)`
  show "R b c"
    by(induct arbitrary: ys rule: lfinite_induct)(auto dest: goal1(2))
qed

lemma tllist_all2_cases[consumes 1, case_names TNil TCons, cases pred]:
  assumes "tllist_all2 P Q xs ys"
  obtains (TNil) b b' where "xs = TNil b" "ys = TNil b'" "Q b b'"
  | (TCons) x xs' y ys'
    where "xs = TCons x xs'" and "ys = TCons y ys'" 
    and "P x y" and "tllist_all2 P Q xs' ys'"
using assms
by(cases xs)(fastforce simp add: tllist_all2_TCons1 tllist_all2_TNil1)+

lemma tllist_all2_tmap1:
  "tllist_all2 P Q (tmap f g xs) ys \<longleftrightarrow> tllist_all2 (\<lambda>x. P (f x)) (\<lambda>x. Q (g x)) xs ys"
by(transfer)(auto simp add: llist_all2_lmap1)

lemma tllist_all2_tmap2:
  "tllist_all2 P Q xs (tmap f g ys) \<longleftrightarrow> tllist_all2 (\<lambda>x y. P x (f y)) (\<lambda>x y. Q x (g y)) xs ys"
by(transfer)(auto simp add: llist_all2_lmap2)

lemma tllist_all2_mono:
  "\<lbrakk> tllist_all2 P Q xs ys; \<And>x y. P x y \<Longrightarrow> P' x y; \<And>x y. Q x y \<Longrightarrow> Q' x y \<rbrakk>
  \<Longrightarrow> tllist_all2 P' Q' xs ys"
by transfer(auto elim!: llist_all2_mono)

lemma tllist_all2_tlengthD: "tllist_all2 P Q xs ys \<Longrightarrow> tlength xs = tlength ys"
by(transfer)(auto dest: llist_all2_llengthD)

lemma tllist_all2_tfiniteD: "tllist_all2 P Q xs ys \<Longrightarrow> tfinite xs = tfinite ys"
by(transfer)(auto dest: llist_all2_lfiniteD)

lemma tllist_all2_tfinite1_terminalD:
  "\<lbrakk> tllist_all2 P Q xs ys; tfinite xs \<rbrakk> \<Longrightarrow> Q (terminal xs) (terminal ys)"
by(frule tllist_all2_tfiniteD)(transfer, auto)

lemma tllist_all2_tfinite2_terminalD:
  "\<lbrakk> tllist_all2 P Q xs ys; tfinite ys \<rbrakk> \<Longrightarrow> Q (terminal xs) (terminal ys)"
by(metis tllist_all2_tfinite1_terminalD tllist_all2_tfiniteD)

lemma tllist_all2D_llist_all2_llist_of_tllist:
  "tllist_all2 P Q xs ys \<Longrightarrow> llist_all2 P (llist_of_tllist xs) (llist_of_tllist ys)"
by(transfer) auto

lemma tllist_all2_is_TNilD:
  "tllist_all2 P Q xs ys \<Longrightarrow> is_TNil xs \<longleftrightarrow> is_TNil ys"
by(cases xs)(auto simp add: tllist_all2_TNil1 tllist_all2_TCons1)

lemma tllist_all2_thdD:
  "\<lbrakk> tllist_all2 P Q xs ys; \<not> is_TNil xs \<or> \<not> is_TNil ys \<rbrakk> \<Longrightarrow> P (thd xs) (thd ys)"
by(cases xs)(auto simp add: tllist_all2_TNil1 tllist_all2_TCons1)

lemma tllist_all2_ttlI:
  "\<lbrakk> tllist_all2 P Q xs ys; \<not> is_TNil xs \<or> \<not> is_TNil ys \<rbrakk> \<Longrightarrow> tllist_all2 P Q (ttl xs) (ttl ys)"
by(cases xs)(auto simp add: tllist_all2_TNil1 tllist_all2_TCons1)

lemma tllist_all2_refl:
  "tllist_all2 P Q xs xs \<longleftrightarrow> (\<forall>x \<in> tset xs. P x x) \<and> (tfinite xs \<longrightarrow> Q (terminal xs) (terminal xs))"
by transfer(auto)

lemma tllist_all2_reflI:
  "\<lbrakk> \<And>x. x \<in> tset xs \<Longrightarrow> P x x; tfinite xs \<Longrightarrow> Q (terminal xs) (terminal xs) \<rbrakk>
  \<Longrightarrow> tllist_all2 P Q xs xs"
by(simp add: tllist_all2_refl)

lemma tllist_all2_conv_all_tnth:
  "tllist_all2 P Q xs ys \<longleftrightarrow> 
  tlength xs = tlength ys \<and> 
  (\<forall>n. enat n < tlength xs \<longrightarrow> P (tnth xs n) (tnth ys n)) \<and>
  (tfinite xs \<longrightarrow> Q (terminal xs) (terminal ys))"
by transfer(auto 4 4 simp add: llist_all2_conv_all_lnth split: split_if_asm dest: lfinite_llength_enat not_lfinite_llength)

lemma tllist_all2_tnthD:
  "\<lbrakk> tllist_all2 P Q xs ys; enat n < tlength xs \<rbrakk> 
  \<Longrightarrow> P (tnth xs n) (tnth ys n)"
by(simp add: tllist_all2_conv_all_tnth)

lemma tllist_all2_tnthD2:
  "\<lbrakk> tllist_all2 P Q xs ys; enat n < tlength ys \<rbrakk> 
  \<Longrightarrow> P (tnth xs n) (tnth ys n)"
by(simp add: tllist_all2_conv_all_tnth)

lemmas tllist_all2_eq = tllist.rel_eq

lemma tmap_eq_tmap_conv_tllist_all2:
  "tmap f g xs = tmap f' g' ys \<longleftrightarrow>
  tllist_all2 (\<lambda>x y. f x = f' y) (\<lambda>x y. g x = g' y) xs ys"
apply transfer
apply(clarsimp simp add: lmap_eq_lmap_conv_llist_all2)
apply(auto dest: llist_all2_lfiniteD)
done

lemma tllist_all2_trans:
  "\<lbrakk> tllist_all2 P Q xs ys; tllist_all2 P Q ys zs; transp P; transp Q \<rbrakk>
  \<Longrightarrow> tllist_all2 P Q xs zs"
by transfer(auto elim: llist_all2_trans dest: llist_all2_lfiniteD transpD)

lemma tllist_all2_tappendI:
  "\<lbrakk> tllist_all2 P Q xs ys;
     \<lbrakk> tfinite xs; tfinite ys; Q (terminal xs) (terminal ys) \<rbrakk>
     \<Longrightarrow> tllist_all2 P R (xs' (terminal xs)) (ys' (terminal ys)) \<rbrakk>
  \<Longrightarrow> tllist_all2 P R (tappend xs xs') (tappend ys ys')"
apply transfer
apply(auto 4 3 simp add: apfst_def map_pair_def lappend_inf split: prod.split_asm dest: llist_all2_lfiniteD intro: llist_all2_lappendI)
apply(frule llist_all2_lfiniteD, simp add: lappend_inf)
done

lemma llist_all2_tllist_of_llistI:
  "tllist_all2 A B xs ys \<Longrightarrow> llist_all2 A (llist_of_tllist xs) (llist_of_tllist ys)"
by(coinduction arbitrary: xs ys)(auto dest: tllist_all2_is_TNilD tllist_all2_thdD intro: tllist_all2_ttlI)

lemma tllist_all2_tllist_of_llist [simp]:
  "tllist_all2 A B (tllist_of_llist b xs) (tllist_of_llist c ys) \<longleftrightarrow>
  llist_all2 A xs ys \<and> (lfinite xs \<longrightarrow> B b c)"
by transfer auto

subsection {* From a terminated lazy list to a lazy list @{term llist_of_tllist} *}

lemma llist_of_tllist_tmap [simp]:
  "llist_of_tllist (tmap f g xs) = lmap f (llist_of_tllist xs)"
by transfer auto

lemma llist_of_tllist_tappend:
  "llist_of_tllist (tappend xs f) = lappend (llist_of_tllist xs) (llist_of_tllist (f (terminal xs)))"
by(transfer)(auto simp add: lappend_inf)

lemma llist_of_tllist_lappendt [simp]:
  "llist_of_tllist (lappendt xs tr) = lappend xs (llist_of_tllist tr)"
by transfer auto

lemma llist_of_tllist_tfilter [simp]:
  "llist_of_tllist (tfilter b P tr) = lfilter P (llist_of_tllist tr)"
by transfer auto

lemma llist_of_tllist_tconcat:
  "llist_of_tllist (tconcat b trs) = lconcat (llist_of_tllist trs)"
by transfer auto

lemma llist_of_tllist_eq_lappend_conv:
  "llist_of_tllist xs = lappend us vs \<longleftrightarrow> 
  (\<exists>ys. xs = lappendt us ys \<and> vs = llist_of_tllist ys \<and> terminal xs = terminal ys)"
by transfer auto

subsection {* The nth element of a terminated lazy list @{term "tnth"} *}

lemma tnth_TNil [nitpick_simp]:
  "tnth (TNil b) n = undefined n"
by(transfer)(simp add: lnth_LNil)

lemma tnth_TCons:
  "tnth (TCons x xs) n = (case n of 0 \<Rightarrow> x | Suc n' \<Rightarrow> tnth xs n')"
by(transfer)(auto simp add: lnth_LCons split: nat.split)

lemma tnth_code [simp, nitpick_simp, code]:
  shows tnth_0: "tnth (TCons x xs) 0 = x"
  and tnth_Suc_TCons: "tnth (TCons x xs) (Suc n) = tnth xs n"
by(simp_all add: tnth_TCons)

lemma lnth_llist_of_tllist [simp]:
  "lnth (llist_of_tllist xs) = tnth xs"
by(transfer)(auto)

lemma tnth_tmap [simp]: "enat n < tlength xs \<Longrightarrow> tnth (tmap f g xs) n = f (tnth xs n)"
by transfer simp

subsection {* The length of a terminated lazy list @{term "tlength"} *}

lemma [simp, nitpick_simp]:
  shows tlength_TNil: "tlength (TNil b) = 0"
  and tlength_TCons: "tlength (TCons x xs) = eSuc (tlength xs)"
 apply(transfer, simp)
apply(transfer, auto)
done

lemma llength_llist_of_tllist [simp]: "llength (llist_of_tllist xs) = tlength xs"
by transfer auto

lemma tlength_tmap [simp]: "tlength (tmap f g xs) = tlength xs"
by transfer simp

definition gen_tlength :: "nat \<Rightarrow> ('a, 'b) tllist \<Rightarrow> enat"
where "gen_tlength n xs = enat n + tlength xs"

lemma gen_tlength_code [code]:
  "gen_tlength n (TNil b) = enat n"
  "gen_tlength n (TCons x xs) = gen_tlength (n + 1) xs"
by(simp_all add: gen_tlength_def iadd_Suc eSuc_enat[symmetric] iadd_Suc_right)

lemma tlength_code [code]: "tlength = gen_tlength 0"
by(simp add: gen_tlength_def fun_eq_iff zero_enat_def)

subsection {* @{term "tdropn"} *}

lemma tdropn_0 [simp, code, nitpick_simp]: "tdropn 0 xs = xs"
by transfer auto

lemma tdropn_TNil [simp, code]: "tdropn n (TNil b) = (TNil b)"
by transfer(auto)

lemma tdropn_Suc_TCons [simp, code]: "tdropn (Suc n) (TCons x xs) = tdropn n xs"
by transfer(auto)

lemma tdropn_Suc [nitpick_simp]: "tdropn (Suc n) xs = (case xs of TNil b \<Rightarrow> TNil b | TCons x xs' \<Rightarrow> tdropn n xs')"
by(cases xs) simp_all

lemma lappendt_ltake_tdropn:
  "lappendt (ltake (enat n) (llist_of_tllist xs)) (tdropn n xs) = xs"
by transfer (auto)

lemma llist_of_tllist_tdropn [simp]:
  "llist_of_tllist (tdropn n xs) = ldropn n (llist_of_tllist xs)"
by transfer auto

lemma tdropn_Suc_conv_tdropn:
  "enat n < tlength xs \<Longrightarrow> TCons (tnth xs n) (tdropn (Suc n) xs) = tdropn n xs" 
by transfer(auto simp add: ldropn_Suc_conv_ldropn)

lemma tlength_tdropn [simp]: "tlength (tdropn n xs) = tlength xs - enat n"
by transfer auto

lemma tnth_tdropn [simp]: "enat (n + m) < tlength xs \<Longrightarrow> tnth (tdropn n xs) m = tnth xs (m + n)"
by transfer auto

subsection {* @{term "tset"} *}

lemma tset_induct [consumes 1, case_names find step]:
  assumes "x \<in> tset xs"
  and "\<And>xs. P (TCons x xs)"
  and "\<And>x' xs. \<lbrakk> x \<in> tset xs; x \<noteq> x'; P xs \<rbrakk> \<Longrightarrow> P (TCons x' xs)"
  shows "P xs"
using assms
by transfer(clarsimp, erule lset_induct)

lemma tset_conv_tnth: "tset xs = {tnth xs n|n . enat n < tlength xs}"
by transfer(simp add: lset_conv_lnth)

lemma in_tset_conv_tnth: "x \<in> tset xs \<longleftrightarrow> (\<exists>n. enat n < tlength xs \<and> tnth xs n = x)"
using tset_conv_tnth[of xs] by auto

subsection {* Setup for Lifting/Transfer *}

context
begin
interpretation lifting_syntax .

(* FIXME: move to Main *)

lemma OO_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_total B"
  shows "((A ===> B ===> op =) ===> (B ===> C ===> op =) ===> A ===> C ===> op =) op OO op OO"
unfolding OO_def[abs_def]
by transfer_prover

end

subsubsection {* Relator and predicator properties *}

lift_definition tllist_all :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) tllist \<Rightarrow> bool"
is "\<lambda>P Q (xs, b). llist_all P xs \<and> (lfinite xs \<longrightarrow> Q b)" 
by auto

declare tllist_all2_eq [relator_eq]

lemma tllist_all2_mono2 [relator_mono]:
  assumes "A \<le> B" and "C \<le> D"
  shows "(tllist_all2 A C) \<le> (tllist_all2 B D)"
using assms by(auto intro: tllist_all2_mono)

lemma tllist_all2_OO [relator_distr]:
  "tllist_all2 A B OO tllist_all2 A' B' = tllist_all2 (A OO A') (B OO B')"
by transfer(auto intro!: ext simp add: llist_all2_OO[symmetric] dest: llist_all2_lfiniteD)

lemma Domainp_tllist [relator_domain]:
  assumes A: "Domainp A = P"
  and B: "Domainp B = Q"
  shows "Domainp (tllist_all2 A B) = (tllist_all P Q)"
  unfolding Domainp_iff[abs_def]
by(transfer fixing: A B P Q)(clarsimp simp add: fun_eq_iff Domainp_iff[symmetric] Domainp_llist[OF A] B)

lemma reflp_tllist_all2[reflexivity_rule]: 
  assumes R: "reflp R" and Q: "reflp Q"
  shows "reflp (tllist_all2 R Q)"
proof(rule reflpI)
  fix xs
  show "tllist_all2 R Q xs xs"
    apply(coinduction arbitrary: xs)
    using assms by(auto elim: reflpE)
qed

lemma tllist_all2_left_total[reflexivity_rule]:
  assumes R: "left_total R"
  and S: "left_total S"
  shows "left_total (tllist_all2 R S)"
proof (rule left_totalI)
  fix xs
  have *: "\<And>x. R x (SOME y. R x y)"
    using R by(rule left_totalE)(rule someI_ex)
  have **: "\<And>x. S x (SOME y. S x y)"
    using S by(rule left_totalE)(rule someI_ex)

  have "tllist_all2 R S xs (tmap (\<lambda>x. SOME y. R x y) (\<lambda>x. SOME y. S x y) xs)"
    by(coinduction arbitrary: xs)(auto simp add: * **)
  thus "\<exists>ys. tllist_all2 R S xs ys" ..
qed

lemma left_unique_tllist_all2 [reflexivity_rule]:
  assumes A: "left_unique A" and B: "left_unique B"
  shows "left_unique (tllist_all2 A B)"
proof(rule left_uniqueI)
  fix xs ys zs
  assume "tllist_all2 A B xs zs" "tllist_all2 A B ys zs"
  thus "xs = ys"
    by(coinduction arbitrary: xs ys zs rule: tllist.strong_coinduct)(auto 4 3 dest: left_uniqueD[OF A] left_uniqueD[OF B] tllist_all2_is_TNilD tllist_all2_thdD tllist_all2_tfinite1_terminalD intro: tllist_all2_ttlI)
qed

lemma tllist_all2_right_total[transfer_rule]:
  assumes R: "right_total R"
  and S: "right_total S"
  shows "right_total (tllist_all2 R S)"
  unfolding right_total_def
proof
  fix ys
  have *: "\<And>y. R (SOME x. R x y) y"
    using assms unfolding right_total_def by - (rule someI_ex, blast)
  have **: "\<And>y. S (SOME x. S x y) y"
    using assms unfolding right_total_def by - (rule someI_ex, blast)

  have "tllist_all2 R S (tmap (\<lambda>y. SOME x. R x y) (\<lambda>y. SOME x. S x y) ys) ys"
    by(coinduction arbitrary: ys)(auto simp add: * **)
  thus "\<exists>xs. tllist_all2 R S xs ys" ..
qed

lemma bi_total_tllist_all2 [transfer_rule]:
  "\<lbrakk> bi_total A; bi_total B \<rbrakk> \<Longrightarrow> bi_total (tllist_all2 A B)"
by(simp add: bi_total_conv_left_right tllist_all2_right_total tllist_all2_left_total)

lemma right_unique_tllist_all2 [transfer_rule]:
  assumes A: "right_unique A" and B: "right_unique B"
  shows "right_unique (tllist_all2 A B)"
proof(rule right_uniqueI)
  fix xs ys zs
  assume "tllist_all2 A B xs ys" "tllist_all2 A B xs zs"
  thus "ys = zs"
    by(coinduction arbitrary: xs ys zs rule: tllist.strong_coinduct)(auto 4 3 dest: tllist_all2_is_TNilD right_uniqueD[OF B] right_uniqueD[OF A] tllist_all2_thdD tllist_all2_tfinite2_terminalD intro: tllist_all2_ttlI)
qed

lemma bi_unique_tllist_all2 [transfer_rule]:
  "\<lbrakk> bi_unique A; bi_unique B \<rbrakk> \<Longrightarrow> bi_unique (tllist_all2 A B)"
by(simp add: bi_unique_conv_left_right left_unique_tllist_all2 right_unique_tllist_all2)

subsubsection {* Quotient theorem for the Lifting package *}

lemma Quotient_llist[quot_map]:
  assumes "Quotient R1 Abs1 Rep1 T1"
  and "Quotient R2 Abs2 Rep2 T2"
  shows "Quotient (tllist_all2 R1 R2) (tmap Abs1 Abs2) (tmap Rep1 Rep2) (tllist_all2 T1 T2)"
unfolding Quotient_alt_def
proof(intro conjI strip)
  from assms have 1: "\<And>x y. T1 x y \<Longrightarrow> Abs1 x = y"
    and 2: "\<And>x y. T2 x y \<Longrightarrow> Abs2 x = y"
    unfolding Quotient_alt_def by simp_all
  fix xs ys
  assume "tllist_all2 T1 T2 xs ys"
  thus "tmap Abs1 Abs2 xs = ys"
    by(coinduction arbitrary: xs ys)(auto simp add: 1 2 dest: tllist_all2_is_TNilD tllist_all2_tfinite1_terminalD tllist_all2_thdD intro: tllist_all2_ttlI)
next
  from assms have 1: "\<And>x. T1 (Rep1 x) x"
    and 2: "\<And>x. T2 (Rep2 x) x"
    unfolding Quotient_alt_def by simp_all
  fix xs
  show "tllist_all2 T1 T2 (tmap Rep1 Rep2 xs) xs"
    by(simp add: tllist_all2_tmap1 1 2 tllist_all2_refl)
next
  from assms have 1: "R1 = (\<lambda>x y. T1 x (Abs1 x) \<and> T1 y (Abs1 y) \<and> Abs1 x = Abs1 y)"
    and 2: "R2 = (\<lambda>x y. T2 x (Abs2 x) \<and> T2 y (Abs2 y) \<and> Abs2 x = Abs2 y)"
    unfolding Quotient_alt_def by(simp_all add: fun_eq_iff)
  fix xs ys
  show "tllist_all2 R1 R2 xs ys
    \<longleftrightarrow> tllist_all2 T1 T2 xs (tmap Abs1 Abs2 xs) \<and> 
    tllist_all2 T1 T2 ys (tmap Abs1 Abs2 ys) \<and> 
    tmap Abs1 Abs2 xs = tmap Abs1 Abs2 ys"
    unfolding 1 2 tmap_eq_tmap_conv_tllist_all2
    by(auto 4 3 simp add: tllist_all2_conv_all_tnth dest: lfinite_llength_enat not_lfinite_llength)
qed

subsubsection {* Transfer rules for the Transfer package *}

context
begin
interpretation lifting_syntax .

lemma set1_pre_tllist_transfer [transfer_rule]:
  "(rel_pre_tllist A B C ===> set_rel A) set1_pre_tllist set1_pre_tllist"
by(auto simp add: rel_pre_tllist_def vimage2p_def fun_rel_def set1_pre_tllist_def set_rel_def collect_def sum_set_defs sum_rel_def fsts_def split: sum.split_asm)

lemma set2_pre_tllist_transfer [transfer_rule]:
  "(rel_pre_tllist A B C ===> set_rel B) set2_pre_tllist set2_pre_tllist"
by(auto simp add: rel_pre_tllist_def vimage2p_def fun_rel_def set2_pre_tllist_def set_rel_def collect_def sum_set_defs snds_def sum_rel_def split: sum.split_asm)

lemma set3_pre_tllist_transfer [transfer_rule]:
  "(rel_pre_tllist A B C ===> set_rel C) set3_pre_tllist set3_pre_tllist"
by(auto simp add: rel_pre_tllist_def vimage2p_def fun_rel_def set3_pre_tllist_def set_rel_def collect_def sum_set_defs snds_def sum_rel_def split: sum.split_asm)

lemma dtor_tllist_transfer [transfer_rule]:
  "(tllist_all2 A B ===> rel_pre_tllist A B (tllist_all2 A B)) dtor_tllist dtor_tllist"
apply(rule fun_relI)
apply(erule tllist_all2_cases)
apply(auto simp add: rel_pre_tllist_def vimage2p_def BNF_Comp.id_bnf_comp_def sum_rel_def TNil_def TCons_def tllist.dtor_ctor split: sum.split)
done

lemma TNil_transfer2 [transfer_rule]: "(B ===> tllist_all2 A B) TNil TNil"
by auto

lemma TCons_transfer2 [transfer_rule]:
  "(A ===> tllist_all2 A B ===> tllist_all2 A B) TCons TCons"
unfolding fun_rel_def by simp

lemma case_tllist_transfer [transfer_rule]:
  "((B ===> C) ===> (A ===> tllist_all2 A B ===> C) ===> tllist_all2 A B ===> C)
    case_tllist case_tllist"
unfolding fun_rel_def
by (simp add: tllist_all2_TNil1 tllist_all2_TNil2 split: tllist.split)

lemma unfold_tllist_transfer [transfer_rule]:
  "((A ===> op =) ===> (A ===> B) ===> (A ===> C) ===> (A ===> A) ===> A ===> tllist_all2 C B) unfold_tllist unfold_tllist"
proof(rule fun_relI)+
  fix IS_TNIL1 :: "'a \<Rightarrow> bool" and IS_TNIL2
    TERMINAL1 TERMINAL2 THD1 THD2 TTL1 TTL2 x y
  assume rel: "(A ===> op =) IS_TNIL1 IS_TNIL2" "(A ===> B) TERMINAL1 TERMINAL2"
    "(A ===> C) THD1 THD2" "(A ===> A) TTL1 TTL2"
    and "A x y"
  show "tllist_all2 C B (unfold_tllist IS_TNIL1 TERMINAL1 THD1 TTL1 x) (unfold_tllist IS_TNIL2 TERMINAL2 THD2 TTL2 y)"
    using `A x y`
    apply(coinduction arbitrary: x y)
    using rel by(auto 4 4 elim: fun_relE)
qed

lemma corec_tllist_transfer [transfer_rule]:
  "((A ===> op =) ===> (A ===> B) ===> (A ===> C) ===> (A ===> op =) ===> (A ===> tllist_all2 C B) ===> (A ===> A) ===> A ===> tllist_all2 C B) corec_tllist corec_tllist"
proof(rule fun_relI)+
  fix IS_TNIL1 MORE1 :: "'a \<Rightarrow> bool" and IS_TNIL2
    TERMINAL1 TERMINAL2 THD1 THD2 MORE2 STOP1 STOP2 TTL1 TTL2 x y
  assume rel: "(A ===> op =) IS_TNIL1 IS_TNIL2" "(A ===> B) TERMINAL1 TERMINAL2"
    "(A ===> C) THD1 THD2" "(A ===> op =) MORE1 MORE2"
    "(A ===> tllist_all2 C B) STOP1 STOP2" "(A ===> A) TTL1 TTL2"
    and "A x y"
  show "tllist_all2 C B (corec_tllist IS_TNIL1 TERMINAL1 THD1 MORE1 STOP1 TTL1 x) (corec_tllist IS_TNIL2 TERMINAL2 THD2 MORE2 STOP2 TTL2 y)"
    using `A x y`
    apply(coinduction arbitrary: x y)
    using rel by(auto 4 4 elim: fun_relE)
qed

lemma ttl_transfer2 [transfer_rule]:
  "(tllist_all2 A B ===> tllist_all2 A B) ttl ttl"
  unfolding ttl_def[abs_def] by transfer_prover

lemma tset_transfer2 [transfer_rule]:
  "(tllist_all2 A B ===> set_rel A) tset tset"
by (intro fun_relI set_relI) (auto simp only: in_tset_conv_tnth tllist_all2_conv_all_tnth Bex_def)

lemma tmap_transfer2 [transfer_rule]:
  "((A ===> B) ===> (C ===> D) ===> tllist_all2 A C ===> tllist_all2 B D) tmap tmap"
by(auto simp add: fun_rel_def tllist_all2_tmap1 tllist_all2_tmap2 elim: tllist_all2_mono)

lemma is_TNil_transfer2 [transfer_rule]:
  "(tllist_all2 A B ===> op =) is_TNil is_TNil"
by(auto dest: tllist_all2_is_TNilD)

lemma tappend_transfer [transfer_rule]:
  "(tllist_all2 A B ===> (B ===> tllist_all2 A C) ===> tllist_all2 A C) tappend tappend"
by(auto intro: tllist_all2_tappendI elim: fun_relE)

lemma lappendt_transfer [transfer_rule]:
  "(llist_all2 A ===> tllist_all2 A B ===> tllist_all2 A B) lappendt lappendt"
unfolding fun_rel_def
by transfer(auto intro: llist_all2_lappendI)

lemma llist_of_tllist_transfer2 [transfer_rule]:
  "(tllist_all2 A B ===> llist_all2 A) llist_of_tllist llist_of_tllist"
by(auto intro: llist_all2_tllist_of_llistI)

lemma tllist_of_llist_transfer2 [transfer_rule]:
  "(B ===> llist_all2 A ===> tllist_all2 A B) tllist_of_llist tllist_of_llist"
by(auto intro!: fun_relI)

lemma tlength_transfer [transfer_rule]:
  "(tllist_all2 A B ===> op =) tlength tlength"
by(auto dest: tllist_all2_tlengthD)

lemma tdropn_transfer [transfer_rule]:
  "(op = ===> tllist_all2 A B ===> tllist_all2 A B) tdropn tdropn"
unfolding fun_rel_def
by transfer(auto intro: llist_all2_ldropnI)

lemma tfilter_transfer [transfer_rule]:
  "(B ===> (A ===> op =) ===> tllist_all2 A B ===> tllist_all2 A B) tfilter tfilter"
unfolding fun_rel_def
by transfer(auto intro: llist_all2_lfilterI dest: llist_all2_lfiniteD)

lemma tconcat_transfer [transfer_rule]:
  "(B ===> tllist_all2 (llist_all2 A) B ===> tllist_all2 A B) tconcat tconcat"
unfolding fun_rel_def
by transfer(auto intro: llist_all2_lconcatI dest: llist_all2_lfiniteD)

lemma tllist_all2_rsp:
  assumes R1: "\<forall>x y. R1 x y \<longrightarrow> (\<forall>a b. R1 a b \<longrightarrow> S x a = T y b)"
  and R2: "\<forall>x y. R2 x y \<longrightarrow> (\<forall>a b. R2 a b \<longrightarrow> S' x a = T' y b)"
  and xsys: "tllist_all2 R1 R2 xs ys"
  and xs'ys': "tllist_all2 R1 R2 xs' ys'"
  shows "tllist_all2 S S' xs xs' = tllist_all2 T T' ys ys'"
proof
  assume "tllist_all2 S S' xs xs'"
  with xsys xs'ys' show "tllist_all2 T T' ys ys'"
  proof(coinduction arbitrary: ys ys' xs xs')
    case (tllist_all2 ys ys' xs xs')
    thus ?case
      by cases (auto 4 4 simp add: tllist_all2_TCons1 tllist_all2_TCons2 tllist_all2_TNil1 tllist_all2_TNil2 dest: R1[rule_format] R2[rule_format])
  qed
next
  assume "tllist_all2 T T' ys ys'"
  with xsys xs'ys' show "tllist_all2 S S' xs xs'"
  proof(coinduction arbitrary: xs xs' ys ys')
    case (tllist_all2 xs xs' ys ys')
    thus ?case
      by cases(auto 4 4 simp add: tllist_all2_TCons1 tllist_all2_TCons2 tllist_all2_TNil1 tllist_all2_TNil2 dest: R1[rule_format] R2[rule_format])
  qed
qed

lemma tllist_all2_transfer2 [transfer_rule]:
  "((R1 ===> R1 ===> op =) ===> (R2 ===> R2 ===> op =) ===>
    tllist_all2 R1 R2 ===> tllist_all2 R1 R2 ===> op =) tllist_all2 tllist_all2"
by (simp add: tllist_all2_rsp fun_rel_def)

end

text {* 
  Delete lifting rules for @{typ "('a, 'b) tllist"} 
  because the parametricity rules take precedence over
  most of the transfer rules. They can be restored by 
  including the bundle @{text "tllist.lifting"}.
*}

lifting_update tllist.lifting
lifting_forget tllist.lifting

end
