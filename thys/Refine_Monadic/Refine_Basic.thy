header {* \isaheader{Basic Concepts} *}
theory Refine_Basic
imports Main 
  "~~/src/HOL/Library/Monad_Syntax" 
  "Refine_Misc"
  "Generic/RefineG_Recursion"
  "Generic/RefineG_Assert"
begin

subsection {* Setup *}
  ML {*
    structure Refine = struct

    open Refine_Misc;

    structure vcg = Named_Thms
      ( val name = @{binding refine_vcg}
        val description = "Refinement Framework: " ^ 
          "Verification condition generation rules (intro)" )

    structure refine0 = Named_Thms
      ( val name = @{binding refine0}
        val description = "Refinement Framework: " ^
          "Refinement rules applied first (intro)" )

    structure refine = Named_Thms
      ( val name = @{binding refine}
        val description = "Refinement Framework: Refinement rules (intro)" )

    structure refine2 = Named_Thms
      ( val name = @{binding refine2}
        val description = "Refinement Framework: " ^
          "Refinement rules 2nd stage (intro)" )

    structure refine_pw_simps = Named_Thms
      ( val name = @{binding refine_pw_simps}
        val description = "Refinement Framework: " ^
          "Simplifier rules for pointwise reasoning" )

    (* Replaced by respective solvers in tagged solver
    structure refine_post = Named_Thms
      ( val name = @{binding refine_post}
        val description = "Refinement Framework: " ^
          "Postprocessing rules" )
    *)



    (* If set to true, the product splitter of refine_rcg is disabled. *)
    val no_prod_split = 
      Attrib.setup_config_bool @{binding refine_no_prod_split} (K false);

    fun rcg_tac add_thms ctxt = 
      let 
        val ref_thms = (refine0.get ctxt 
          @ add_thms @ refine.get ctxt @ refine2.get ctxt);
        val prod_ss = (Splitter.add_split @{thm prod.split} 
          (put_simpset HOL_basic_ss ctxt));
        val prod_simp_tac = 
          if Config.get ctxt no_prod_split then 
            K no_tac
          else
            (simp_tac prod_ss THEN' 
              REPEAT_ALL_NEW (resolve_tac @{thms impI allI}));
      in
        REPEAT_ALL_NEW (DETERM o (resolve_tac ref_thms ORELSE' prod_simp_tac))
      end;

      fun post_tac ctxt = let
        (*val thms = refine_post.get ctxt;*)
      in
        REPEAT_ALL_NEW (FIRST' [
          eq_assume_tac,
          (*match_tac thms,*)
          SOLVED' (Tagged_Solver.solve_tac ctxt)]) 
           (* TODO: Get rid of refine_post! Use tagged_solver instead *)
      end;

    end;
  *}
  setup {* Refine.vcg.setup *}
  setup {* Refine.refine0.setup *}
  setup {* Refine.refine.setup *}
  setup {* Refine.refine2.setup *}
  (*setup {* Refine.refine_post.setup *}*)
  setup {* Refine.refine_pw_simps.setup *}

  method_setup refine_rcg = 
    {* Attrib.thms >> (fn add_thms => fn ctxt => SIMPLE_METHOD' (
      Refine.rcg_tac add_thms ctxt THEN_ALL_NEW (TRY o Refine.post_tac ctxt)
    )) *} 
    "Refinement framework: Generate refinement conditions"

  (* Use tagged-solver instead!
  method_setup refine_post = 
    {* Scan.succeed (fn ctxt => SIMPLE_METHOD' (
      Refine.post_tac ctxt
    )) *} 
    "Refinement framework: Postprocessing of refinement goals"
    *)


subsection {* Nondeterministic Result Lattice and Monad *}
text {*
  In this section we introduce a complete lattice of result sets with an
  additional top element that represents failure. On this lattice, we define
  a monad: The return operator models a result that consists of a single value,
  and the bind operator models applying a function to all results.
  Binding a failure yields always a failure.
  
  In addition to the return operator, we also introduce the operator 
  @{text RES}, that embeds a set of results into our lattice. Its synonym for
  a predicate is @{text SPEC}.

  Program correctness is expressed by refinement, i.e., the expression
  @{text "M \<le> SPEC \<Phi>"} means that @{text M} is correct w.r.t.\ 
  specification @{text \<Phi>}. This suggests the following view on the program 
  lattice: The top-element is the result that is never correct. We call this
  result @{text FAIL}. The bottom element is the program that is always correct.
  It is called @{text SUCCEED}. An assertion can be encoded by failing if the
  asserted predicate is not true. Symmetrically, an assumption is encoded by
  succeeding if the predicate is not true. 
*}


datatype_new 'a nres = FAILi | RES "'a set"
text {*
  @{text FAILi} is only an internal notation, that should not be exposed to 
  the user.
  Instead, @{text FAIL} should be used, that is defined later as abbreviation 
  for the bottom element of the lattice.
*}
instantiation nres :: (type) complete_lattice
begin
fun less_eq_nres where
  "_ \<le> FAILi \<longleftrightarrow> True" |
  "(RES a) \<le> (RES b) \<longleftrightarrow> a\<subseteq>b" |
  "FAILi \<le> (RES _) \<longleftrightarrow> False"

fun less_nres where
  "FAILi < _ \<longleftrightarrow> False" |
  "(RES _) < FAILi \<longleftrightarrow> True" |
  "(RES a) < (RES b) \<longleftrightarrow> a\<subset>b"

fun sup_nres where
  "sup _ FAILi = FAILi" |
  "sup FAILi _ = FAILi" |
  "sup (RES a) (RES b) = RES (a\<union>b)"

fun inf_nres where 
  "inf x FAILi = x" |
  "inf FAILi x = x" |
  "inf (RES a) (RES b) = RES (a\<inter>b)"

definition "Sup X \<equiv> if FAILi\<in>X then FAILi else RES (\<Union>{x . RES x \<in> X})"
definition "Inf X \<equiv> if \<exists>x. RES x\<in>X then RES (\<Inter>{x . RES x \<in> X}) else FAILi"

definition "bot \<equiv> RES {}"
definition "top \<equiv> FAILi"

instance
  apply (intro_classes)
  unfolding Sup_nres_def Inf_nres_def bot_nres_def top_nres_def
  apply (case_tac x, case_tac [!] y, auto) []
  apply (case_tac x, auto) []
  apply (case_tac x, case_tac [!] y, case_tac [!] z, auto) []
  apply (case_tac x, (case_tac [!] y)?, auto) []
  apply (case_tac x, (case_tac [!] y)?, simp_all) []
  apply (case_tac x, (case_tac [!] y)?, auto) []
  apply (case_tac x, case_tac [!] y, case_tac [!] z, auto) []
  apply (case_tac x, (case_tac [!] y)?, auto) []
  apply (case_tac x, (case_tac [!] y)?, auto) []
  apply (case_tac x, case_tac [!] y, case_tac [!] z, auto) []
  apply (case_tac x, auto) []
  apply (case_tac z, fastforce+) []
  apply (case_tac x, auto) []
  apply (case_tac z, fastforce+) []
  apply auto []
  apply auto []
  done
  
end

abbreviation "FAIL \<equiv> top::'a nres"
abbreviation "SUCCEED \<equiv> bot::'a nres"
abbreviation "SPEC \<Phi> \<equiv> RES (Collect \<Phi>)"
definition "RETURN x \<equiv> RES {x}"

text {* We try to hide the original @{text "FAILi"}-element as well as possible. 
*}
lemma nres_cases[case_names FAIL RES, cases type]:
  obtains "M=FAIL" | X where "M=RES X"
  apply (cases M, fold top_nres_def) by auto

lemma nres_simp_internals: 
  "RES {} = SUCCEED"
  "FAILi = FAIL" 
  unfolding top_nres_def bot_nres_def by simp_all

lemma nres_inequalities[simp]: 
  "FAIL \<noteq> RES X"
  "FAIL \<noteq> SUCCEED" 
  "FAIL \<noteq> RETURN x"
  "SUCCEED \<noteq> FAIL"
  "SUCCEED \<noteq> RETURN x"
  "RES X \<noteq> FAIL"
  "RETURN x \<noteq> FAIL"
  "RETURN x \<noteq> SUCCEED"
  unfolding top_nres_def bot_nres_def RETURN_def
  by auto

lemma nres_more_simps[simp]:
  "SUCCEED = RES X \<longleftrightarrow> X={}"
  "RES X = SUCCEED \<longleftrightarrow> X={}"
  "RES X = RETURN x \<longleftrightarrow> X={x}"
  "RES X = RES Y \<longleftrightarrow> X=Y"
  "RETURN x = RES X \<longleftrightarrow> {x}=X"
  "RETURN x = RETURN y \<longleftrightarrow> x=y"
  unfolding top_nres_def bot_nres_def RETURN_def by auto

lemma nres_order_simps[simp]:
  "\<And>M. SUCCEED \<le> M"
  "\<And>M. M \<le> SUCCEED \<longleftrightarrow> M=SUCCEED"
  "\<And>M. M \<le> FAIL"
  "\<And>M. FAIL \<le> M \<longleftrightarrow> M=FAIL"
  "\<And>X Y. RES X \<le> RES Y \<longleftrightarrow> X\<le>Y"
  "\<And>X. Sup X = FAIL \<longleftrightarrow> FAIL\<in>X"
  "\<And>X f. SUPREMUM X f = FAIL \<longleftrightarrow> FAIL \<in> f ` X"
  "\<And>X. FAIL = Sup X \<longleftrightarrow> FAIL\<in>X"
  "\<And>X f. FAIL = SUPREMUM X f \<longleftrightarrow> FAIL \<in> f ` X"
  "\<And>X. FAIL\<in>X \<Longrightarrow> Sup X = FAIL"
  "\<And>X. FAIL\<in>f ` X \<Longrightarrow> SUPREMUM X f = FAIL"
  "\<And>A. Sup (RES ` A) = RES (Sup A)"
  "\<And>A. SUPREMUM A RES = RES (Sup A)"
  "\<And>A. A\<noteq>{} \<Longrightarrow> Inf (RES`A) = RES (Inf A)"
  "\<And>A. A\<noteq>{} \<Longrightarrow> INFIMUM A RES = RES (Inf A)"
  "Inf {} = FAIL"
  "Inf UNIV = SUCCEED"
  "Sup {} = SUCCEED"
  "Sup UNIV = FAIL"
  "\<And>x y. RETURN x \<le> RETURN y \<longleftrightarrow> x=y"
  "\<And>x Y. RETURN x \<le> RES Y \<longleftrightarrow> x\<in>Y"
  "\<And>X y. RES X \<le> RETURN y \<longleftrightarrow> X \<subseteq> {y}"
  unfolding Sup_nres_def Inf_nres_def SUP_def INF_def RETURN_def
  by (auto simp add: bot_unique top_unique nres_simp_internals)

lemma Sup_eq_RESE:
  assumes "Sup A = RES B"
  obtains C where "A=RES`C" and "B=Sup C"
proof -
  show ?thesis
    using assms unfolding Sup_nres_def
    apply (simp split: split_if_asm)
    apply (rule_tac C="{X. RES X \<in> A}" in that)
    apply auto []
    apply (case_tac x, auto simp: nres_simp_internals) []
    apply (auto simp: nres_simp_internals) []
    done
qed

declare nres_simp_internals[simp]

subsubsection {* Pointwise Reasoning *}

definition "nofail S \<equiv> S\<noteq>FAIL"
definition "inres S x \<equiv> RETURN x \<le> S"

lemma nofail_simps[simp, refine_pw_simps]:
  "nofail FAIL \<longleftrightarrow> False"
  "nofail (RES X) \<longleftrightarrow> True"
  "nofail (RETURN x) \<longleftrightarrow> True"
  "nofail SUCCEED \<longleftrightarrow> True"
  unfolding nofail_def
  by (simp_all add: RETURN_def)

lemma inres_simps[simp, refine_pw_simps]:
  "inres FAIL = (\<lambda>_. True)"
  "inres (RES X) = (\<lambda>x. x\<in>X)"
  "inres (RETURN x) = (\<lambda>y. x=y)"
  "inres SUCCEED = (\<lambda>_. False)"
  unfolding inres_def [abs_def]
  by (auto simp add: RETURN_def)

lemma not_nofail_iff: 
  "\<not>nofail S \<longleftrightarrow> S=FAIL" by (cases S) auto

lemma not_nofail_inres[simp, refine_pw_simps]: 
  "\<not>nofail S \<Longrightarrow> inres S x" 
  apply (cases S) by auto

lemma intro_nofail[refine_pw_simps]: 
  "S\<noteq>FAIL \<longleftrightarrow> nofail S"
  "FAIL\<noteq>S \<longleftrightarrow> nofail S"
  by (cases S, simp_all)+

text {* The following two lemmas will introduce pointwise reasoning for
  orderings and equalities. *}
lemma pw_le_iff: 
  "S \<le> S' \<longleftrightarrow> (nofail S'\<longrightarrow> (nofail S \<and> (\<forall>x. inres S x \<longrightarrow> inres S' x)))"
  apply (cases S, simp_all)
  apply (case_tac [!] S', auto)
  done

lemma pw_eq_iff:
  "S=S' \<longleftrightarrow> (nofail S = nofail S' \<and> (\<forall>x. inres S x \<longleftrightarrow> inres S' x))"
  apply (rule iffI)
  apply simp
  apply (rule antisym)
  apply (simp_all add: pw_le_iff)
  done

lemma pw_leI: 
  "(nofail S'\<longrightarrow> (nofail S \<and> (\<forall>x. inres S x \<longrightarrow> inres S' x))) \<Longrightarrow> S \<le> S'"
  by (simp add: pw_le_iff)

lemma pw_leI': 
  assumes "nofail S' \<Longrightarrow> nofail S"
  assumes "\<And>x. \<lbrakk>nofail S'; inres S x\<rbrakk> \<Longrightarrow> inres S' x"
  shows "S \<le> S'"
  using assms
  by (simp add: pw_le_iff)

lemma pw_eqI: 
  assumes "nofail S = nofail S'" 
  assumes "\<And>x. inres S x \<longleftrightarrow> inres S' x" 
  shows "S=S'"
  using assms by (simp add: pw_eq_iff)

lemma pwD1:
  assumes "S\<le>S'" "nofail S'" 
  shows "nofail S"
  using assms by (simp add: pw_le_iff)

lemma pwD2:
  assumes "S\<le>S'" "inres S x"
  shows "inres S' x"
  using assms 
  by (auto simp add: pw_le_iff)

lemmas pwD = pwD1 pwD2

text {*
  When proving refinement, we may assume that the refined program does not 
  fail. *}
lemma le_nofailI: "\<lbrakk> nofail M' \<Longrightarrow> M \<le> M' \<rbrakk> \<Longrightarrow> M \<le> M'"
  by (cases M') auto

text {* The following lemmas push pointwise reasoning over operators,
  thus converting an expression over lattice operators into a logical
  formula. *}

lemma pw_sup_nofail[refine_pw_simps]:
  "nofail (sup a b) \<longleftrightarrow> nofail a \<and> nofail b"
  apply (cases a, simp)
  apply (cases b, simp_all)
  done

lemma pw_sup_inres[refine_pw_simps]:
  "inres (sup a b) x \<longleftrightarrow> inres a x \<or> inres b x"
  apply (cases a, simp)
  apply (cases b, simp)
  apply (simp)
  done

lemma pw_Sup_inres[refine_pw_simps]: "inres (Sup X) r \<longleftrightarrow> (\<exists>M\<in>X. inres M r)"
  apply (cases "Sup X")
  apply (simp)
  apply (erule bexI[rotated])
  apply simp
  apply (erule Sup_eq_RESE)
  apply (simp)
  done

lemma pw_SUP_inres [refine_pw_simps]: "inres (SUPREMUM X f) r \<longleftrightarrow> (\<exists>M\<in>X. inres (f M) r)"
  using pw_Sup_inres [of "f ` X"] by simp

lemma pw_Sup_nofail[refine_pw_simps]: "nofail (Sup X) \<longleftrightarrow> (\<forall>x\<in>X. nofail x)"
  apply (cases "Sup X")
  apply force
  apply simp
  apply (erule Sup_eq_RESE)
  apply auto
  done

lemma pw_SUP_nofail [refine_pw_simps]: "nofail (SUPREMUM X f) \<longleftrightarrow> (\<forall>x\<in>X. nofail (f x))"
  using pw_Sup_nofail [of "f ` X"] by simp

lemma pw_inf_nofail[refine_pw_simps]:
  "nofail (inf a b) \<longleftrightarrow> nofail a \<or> nofail b"
  apply (cases a, simp)
  apply (cases b, simp_all)
  done

lemma pw_inf_inres[refine_pw_simps]:
  "inres (inf a b) x \<longleftrightarrow> inres a x \<and> inres b x"
  apply (cases a, simp)
  apply (cases b, simp)
  apply (simp)
  done

lemma pw_Inf_nofail[refine_pw_simps]: "nofail (Inf C) \<longleftrightarrow> (\<exists>x\<in>C. nofail x)"
  apply (cases "C={}")
  apply simp
  apply (cases "Inf C")
  apply (subgoal_tac "C={FAIL}")
  apply simp
  apply auto []
  apply (subgoal_tac "C\<noteq>{FAIL}")
  apply (auto simp: not_nofail_iff) []
  apply auto []
  done

lemma pw_INF_nofail [refine_pw_simps]: "nofail (INFIMUM C f) \<longleftrightarrow> (\<exists>x\<in>C. nofail (f x))"
  using pw_Inf_nofail [of "f ` C"] by simp

lemma pw_Inf_inres[refine_pw_simps]: "inres (Inf C) r \<longleftrightarrow> (\<forall>M\<in>C. inres M r)"
  apply (unfold Inf_nres_def)
  apply auto
  apply (case_tac M)
  apply force
  apply force
  apply (case_tac M)
  apply force
  apply force
  done

lemma pw_INF_inres [refine_pw_simps]: "inres (INFIMUM C f) r \<longleftrightarrow> (\<forall>M\<in>C. inres (f M) r)"
  using pw_Inf_inres [of "f ` C"] by simp


subsubsection {* Monad Operators *}
definition bind where "bind M f \<equiv> case M of 
  FAILi \<Rightarrow> FAIL |
  RES X \<Rightarrow> Sup (f`X)"

lemma bind_FAIL[simp]: "bind FAIL f = FAIL"
  unfolding bind_def by (auto split: nres.split)

lemma bind_SUCCEED[simp]: "bind SUCCEED f = SUCCEED"
  unfolding bind_def by (auto split: nres.split)

lemma bind_RES: "bind (RES X) f = Sup (f`X)" unfolding bind_def 
  by (auto)

adhoc_overloading
  Monad_Syntax.bind Refine_Basic.bind

lemma pw_bind_nofail[refine_pw_simps]:
  "nofail (bind M f) \<longleftrightarrow> (nofail M \<and> (\<forall>x. inres M x \<longrightarrow> nofail (f x)))"
  apply (cases M)
  by (auto simp: bind_RES refine_pw_simps)
  
lemma pw_bind_inres[refine_pw_simps]:
  "inres (bind M f) = (\<lambda>x. nofail M \<longrightarrow> (\<exists>y. (inres M y \<and> inres (f y) x)))"
  apply (rule ext)
  apply (cases M)
  apply (auto simp add: bind_RES refine_pw_simps)
  done

lemma pw_bind_le_iff:
  "bind M f \<le> S \<longleftrightarrow> (nofail S \<longrightarrow> nofail M) \<and> 
    (\<forall>x. nofail M \<and> inres M x \<longrightarrow> f x \<le> S)"
  by (auto simp: pw_le_iff refine_pw_simps)

lemma pw_bind_leI: "\<lbrakk> 
  nofail S \<Longrightarrow> nofail M; \<And>x. \<lbrakk>nofail M; inres M x\<rbrakk> \<Longrightarrow> f x \<le> S\<rbrakk> 
  \<Longrightarrow> bind M f \<le> S"
  by (simp add: pw_bind_le_iff)

text {* \paragraph{Monad Laws} *}
lemma nres_monad1[simp]: "bind (RETURN x) f = f x"
  by (rule pw_eqI) (auto simp: refine_pw_simps)
lemma nres_monad2[simp]: "bind M RETURN = M"
  by (rule pw_eqI) (auto simp: refine_pw_simps)
lemma nres_monad3[simp]: "bind (bind M f) g = bind M (\<lambda>x. bind (f x) g)"
  by (rule pw_eqI) (auto simp: refine_pw_simps)
lemmas nres_monad_laws = nres_monad1 nres_monad2 nres_monad3


text {* \paragraph{Monotonicity and Related Properties} *}
lemma bind_mono[refine_mono]:
  "\<lbrakk> M \<le> M'; \<And>x. RETURN x \<le> M \<Longrightarrow> f x \<le> f' x \<rbrakk> \<Longrightarrow>
  bind M f \<le> bind M' f'"
  by (auto simp: refine_pw_simps pw_le_iff)

lemma bind_mono1[simp, intro!]: "mono (\<lambda>M. bind M f)"
  apply (rule monoI)
  apply (rule bind_mono)
  by auto

lemma bind_mono1'[simp, intro!]: "mono bind"
  apply (rule monoI)
  apply (rule le_funI)
  apply (rule bind_mono)
  by auto

lemma bind_mono2'[simp, intro!]: "mono (bind M)"
  apply (rule monoI)
  apply (rule bind_mono)
  by (auto dest: le_funD)


lemma bind_distrib_sup: "bind (sup M N) f = sup (bind M f) (bind N f)"
  by (auto simp add: pw_eq_iff refine_pw_simps)

lemma RES_Sup_RETURN: "Sup (RETURN`X) = RES X"
  by (rule pw_eqI) (auto simp add: refine_pw_simps)

subsection {* Data Refinement *}
text {*
  In this section we establish a notion of pointwise data refinement, by
  lifting a relation @{text "R"} between concrete and abstract values to 
  our result lattice.

  We define two lifting operations: @{text "\<Up>R"} yields a function from 
  concrete to abstract values (abstraction function), and @{text "\<Down>R"} yields
  a function from abstract to concrete values (concretization function).
  The abstraction function fails if it cannot abstract its argument, i.e.,
  if there is a value in the argument with no abstract counterpart. 
  The concretization function, however, will just ignore abstract elements with
  no concrete counterpart. This matches the intuition that the concrete 
  datastructure needs not to be able to represent any abstract value, while 
  concrete values that have no corresponding abstract value make no sense.
  Also, the concretization relation will ignore abstract values that have
  a concretization whose abstractions are not all included in the result to
  be abstracted. Intuitively, this indicates an abstraction mismatch.

  The concretization function results from the abstraction function by the
  natural postulate that concretization and abstraction function form a
  Galois connection, i.e., that abstraction and concretization can be exchanged:
  @{text [display] "\<Up>R M \<le> M' \<longleftrightarrow> M \<le> \<Down>R M'"}
  
  Our approach is inspired by \cite{mmo97}, that also uses the adjuncts of
  a Galois connection to express data refinement by program refinement.
*}

definition abs_fun ("\<Up>") where
  "abs_fun R M \<equiv> case M of 
    FAILi \<Rightarrow> FAIL |
    RES X \<Rightarrow> (
      if X\<subseteq>Domain R then
        RES (R``X)
      else
        FAIL
    )"

lemma 
  abs_fun_FAIL[simp]: "\<Up>R FAIL = FAIL" and
  abs_fun_RES: "\<Up>R (RES X) = (
      if X\<subseteq>Domain R then
        RES (R``X)
      else
        FAIL
    )"
  unfolding abs_fun_def 
  by (auto split: nres.split)

definition conc_fun ("\<Down>") where
  "conc_fun R M \<equiv> case M of 
    FAILi \<Rightarrow> FAIL |
    RES X \<Rightarrow> RES {c. \<exists>a\<in>X. (c,a)\<in>R \<and> (\<forall>a'. (c,a')\<in>R \<longrightarrow> a'\<in>X)}"

lemma 
  conc_fun_FAIL[simp]: "\<Down>R FAIL = FAIL" and
  conc_fun_RES: "\<Down>R (RES X) = RES {c. \<exists>a\<in>X. (c,a)\<in>R \<and> (\<forall>a'. (c,a')\<in>R \<longrightarrow> a'\<in>X)}"
  unfolding conc_fun_def 
  by (auto split: nres.split)
  
lemma ac_galois: "galois_connection (\<Up>R) (\<Down>R)"
  apply (unfold_locales)
  apply rule
  unfolding conc_fun_def abs_fun_def
  apply (force split: nres.split nres.split_asm split_if_asm 
    simp add: top_nres_def[symmetric]) []

  apply (force split: nres.split nres.split_asm split_if_asm 
    simp add: top_nres_def[symmetric]) []
  done

interpretation ac!: galois_connection "(\<Up>R)" "(\<Down>R)"
  by (rule ac_galois)

lemma pw_abs_nofail[refine_pw_simps]: 
  "nofail (\<Up>R M) \<longleftrightarrow> (nofail M \<and> (\<forall>x. inres M x \<longrightarrow> x\<in>Domain R))"
  apply (cases M)
  apply simp
  apply (auto simp: abs_fun_RES)
  done

lemma pw_abs_inres[refine_pw_simps]: 
  "inres (\<Up>R M) a \<longleftrightarrow> (nofail (\<Up>R M) \<longrightarrow> (\<exists>c. inres M c \<and> (c,a)\<in>R))"
  apply (cases M)
  apply simp
  apply (auto simp: abs_fun_RES)
  done

lemma pw_conc_nofail[refine_pw_simps]: 
  "nofail (\<Down>R S) = nofail S"
  by (cases S) (auto simp: conc_fun_RES)

lemma pw_conc_inres:
  "inres (\<Down>R S') = (\<lambda>s. nofail S' 
  \<longrightarrow> (\<exists>s'. (s,s')\<in>R \<and> inres S' s' \<and> (\<forall>s''. (s,s'')\<in>R \<longrightarrow> inres S' s'')))"
  apply (rule ext)
  apply (cases S')
  apply (auto simp: conc_fun_RES)
  done

lemma pw_conc_inres_sv[refine_pw_simps]:
  "inres (\<Down>R S') = (\<lambda>s. nofail S' 
  \<longrightarrow> (\<exists>s'. (s,s')\<in>R \<and> inres S' s' \<and> (
    \<not> single_valued R \<longrightarrow> (\<forall>s''. (s,s'')\<in>R \<longrightarrow> inres S' s''))))"
  apply (rule ext)
  apply (cases S')
  apply (auto simp: conc_fun_RES dest: single_valuedD)
  done

lemma abs_fun_strict[simp]:
  "\<Up> R SUCCEED = SUCCEED"
  unfolding abs_fun_def by (auto split: nres.split)

lemma conc_fun_strict[simp]:
  "\<Down> R SUCCEED = SUCCEED"
  unfolding conc_fun_def by (auto split: nres.split)

lemmas [simp, intro!] = ac.\<alpha>_mono ac.\<gamma>_mono

lemma conc_fun_chain: "single_valued R \<Longrightarrow> \<Down>R (\<Down>S M) = \<Down>(R O S) M"
  unfolding conc_fun_def
  by (auto split: nres.split dest: single_valuedD)

lemma conc_Id[simp]: "\<Down>Id = id"
  unfolding conc_fun_def [abs_def] by (auto split: nres.split)

lemma abs_Id[simp]: "\<Up>Id = id"
  unfolding abs_fun_def [abs_def] by (auto split: nres.split)

lemma conc_fun_fail_iff[simp]: 
  "\<Down>R S = FAIL \<longleftrightarrow> S=FAIL"
  "FAIL = \<Down>R S \<longleftrightarrow> S=FAIL"
  by (auto simp add: pw_eq_iff refine_pw_simps)

lemma conc_trans[trans]:
  assumes A: "C \<le> \<Down>R B" and B: "B \<le> \<Down>R' A" 
  shows "C \<le> \<Down>R (\<Down>R' A)"
proof -
  from A have "\<Up>R C \<le> B" by (simp add: ac.galois)
  also note B
  finally show ?thesis 
    by (simp add: ac.galois)
qed

lemma abs_trans[trans]:
  assumes A: "\<Up>R C \<le> B" and B: "\<Up>R' B \<le> A" 
  shows "\<Up>R' (\<Up>R C) \<le> A"
  using assms unfolding ac.galois[symmetric]
  by (rule conc_trans)

(*
definition "difun R \<equiv> 
  \<forall>a a' c c'. (a,c)\<in>R \<and> (a',c')\<in>R \<and> (a,c')\<in>R \<longrightarrow> (a',c)\<in>R"

lemma sv_is_difun: "single_valued R \<Longrightarrow> difun R"
  unfolding single_valued_def difun_def
  by auto

definition "conc_fun' R m \<equiv> case m of
  FAILi \<Rightarrow> FAIL
| RES X \<Rightarrow> RES {c. \<exists>a\<in>X. (c,a)\<in>R}"

definition "abs_fun' R m' \<equiv> case m' of
  FAILi \<Rightarrow> FAIL
| RES X' \<Rightarrow> RES {a. \<exists>c\<in>X'. (c,a)\<in>R}"

lemma [simp]: 
  "conc_fun' R FAIL = FAIL"
  "conc_fun' R (RES X) = RES {c. \<exists>a\<in>X. (c,a)\<in>R}"
  "abs_fun' R FAIL = FAIL"
  "abs_fun' R (RES X') = RES {a. \<exists>c\<in>X'. (c,a)\<in>R}"
  unfolding conc_fun'_def abs_fun'_def
  by (auto split: nres.split)

lemma ac_galois: 
  "difun R \<Longrightarrow> galois_connection (abs_fun' R) (conc_fun' R)"
  apply (unfold_locales)
  apply rule
  unfolding conc_fun'_def abs_fun'_def
  apply (clarsimp split: nres.split nres.split_asm)
  apply (intro conjI allI impI)
  apply auto []
  apply clarsimp

  unfolding difun_def
  apply clarsimp

  apply (force split: nres.split nres.split_asm)
  apply auto []
  apply auto []

  apply (auto split: nres.split nres.split_asm split_if_asm 
    simp add: top_nres_def[symmetric]) []
  apply (drule (1) set_mp)
  apply auto []


  apply (force split: nres.split nres.split_asm split_if_asm 
    simp add: top_nres_def[symmetric]) []
  done
*)




subsubsection {* Transitivity Reasoner Setup *}

text {* WARNING: The order of the single statements is important here! *}
lemma conc_trans_additional[trans]:
  "\<And>A B C. A\<le>\<Down>R  B \<Longrightarrow> B\<le>    C \<Longrightarrow> A\<le>\<Down>R  C"
  "\<And>A B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>\<Down>R  C \<Longrightarrow> A\<le>\<Down>R  C"
  "\<And>A B C. A\<le>\<Down>R  B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>\<Down>R  C"

  "\<And>A B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>    C"
  "\<And>A B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>    C \<Longrightarrow> A\<le>    C"
  "\<And>A B C. A\<le>    B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>    C"
  using conc_trans[where R=R and R'=Id]
  by (auto intro: order_trans)

text {* WARNING: The order of the single statements is important here! *}
lemma abs_trans_additional[trans]:
  "\<And>A B C. \<lbrakk> A \<le> B; \<Up> R B \<le> C\<rbrakk> \<Longrightarrow> \<Up> R A \<le> C"
  "\<And>A B C. \<lbrakk>\<Up> Id A \<le> B; \<Up> R B \<le> C\<rbrakk> \<Longrightarrow> \<Up> R A \<le> C"
  "\<And>A B C. \<lbrakk>\<Up> R A \<le> B; \<Up> Id B \<le> C\<rbrakk> \<Longrightarrow> \<Up> R A \<le> C"

  "\<And>A B C. \<lbrakk>\<Up> Id A \<le> B; \<Up> Id B \<le> C\<rbrakk> \<Longrightarrow> A \<le> C"
  "\<And>A B C. \<lbrakk>\<Up> Id A \<le> B; B \<le> C\<rbrakk> \<Longrightarrow> A \<le> C"
  "\<And>A B C. \<lbrakk>A \<le> B; \<Up> Id B \<le> C\<rbrakk> \<Longrightarrow> A \<le> C"
  using conc_trans_additional[unfolded ac.galois]
    abs_trans[where R=Id and R'=R]
  by auto


subsection {* Derived Program Constructs *}
text {*
  In this section, we introduce some programming constructs that are derived 
  from the basic monad and ordering operations of our nondeterminism monad.
*}
subsubsection {* ASSUME and ASSERT *}

definition ASSERT where "ASSERT \<equiv> iASSERT RETURN"
definition ASSUME where "ASSUME \<equiv> iASSUME RETURN"
interpretation assert?: generic_Assert bind RETURN ASSERT ASSUME
  apply unfold_locales
  by (simp_all add: ASSERT_def ASSUME_def)

lemma pw_ASSERT[refine_pw_simps]:
  "nofail (ASSERT \<Phi>) \<longleftrightarrow> \<Phi>"
  "inres (ASSERT \<Phi>) x"
  by (cases \<Phi>, simp_all)+

lemma pw_ASSUME[refine_pw_simps]:
  "nofail (ASSUME \<Phi>)"
  "inres (ASSUME \<Phi>) x \<longleftrightarrow> \<Phi>"
  by (cases \<Phi>, simp_all)+

text {* Assumptions and assertions are in particular useful with bindings, hence
  we show some handy rules here: *}

subsubsection {* Recursion *}
lemma pw_REC_nofail: "nofail (REC B x) \<longleftrightarrow> mono B \<and>
  (\<exists>F. (\<forall>x. 
    nofail (F x) \<longrightarrow> nofail (B F x) 
    \<and> (\<forall>x'. inres (B F x) x' \<longrightarrow> inres (F x) x')
  ) \<and> nofail (F x))"
proof -
  have "nofail (REC B x) \<longleftrightarrow> mono B \<and>
  (\<exists>F. (\<forall>x. B F x \<le> F x) \<and> nofail (F x))"
    unfolding REC_def lfp_def
    by (auto simp: refine_pw_simps intro: le_funI dest: le_funD)
  thus ?thesis
    unfolding pw_le_iff .
qed

lemma pw_REC_inres: "inres (REC B x) x' = (mono B \<longrightarrow>
  (\<forall>F. (\<forall>x''. 
    nofail (F x'') \<longrightarrow> nofail (B F x'') 
    \<and> (\<forall>x. inres (B F x'') x \<longrightarrow> inres (F x'') x)) 
    \<longrightarrow> inres (F x) x'))"
proof -
  have "inres (REC B x) x' 
    \<longleftrightarrow> (mono B \<longrightarrow> (\<forall>F. (\<forall>x''. B F x'' \<le> F x'') \<longrightarrow> inres (F x) x'))"
    unfolding REC_def lfp_def
    by (auto simp: refine_pw_simps intro: le_funI dest: le_funD)
  thus ?thesis unfolding pw_le_iff .
qed
  
lemmas pw_REC = pw_REC_inres pw_REC_nofail

lemma pw_RECT_nofail: "nofail (RECT B x) \<longleftrightarrow> mono B \<and>
  (\<forall>F. (\<forall>y. nofail (B F y) \<longrightarrow>
             nofail (F y) \<and> (\<forall>x. inres (F y) x \<longrightarrow> inres (B F y) x)) \<longrightarrow>
        nofail (F x))"
proof -
  have "nofail (RECT B x) \<longleftrightarrow> (mono B \<and> (\<forall>F. (\<forall>y. F y \<le> B F y) \<longrightarrow> nofail (F x)))"
    unfolding RECT_def gfp_def
    by (auto simp: refine_pw_simps intro: le_funI dest: le_funD)
  thus ?thesis
    unfolding pw_le_iff .
qed

lemma pw_RECT_inres: "inres (RECT B x) x' = (mono B \<longrightarrow>
   (\<exists>M. (\<forall>y. nofail (B M y) \<longrightarrow>
             nofail (M y) \<and> (\<forall>x. inres (M y) x \<longrightarrow> inres (B M y) x)) \<and>
        inres (M x) x'))"
proof -
  have "inres (RECT B x) x' \<longleftrightarrow> mono B \<longrightarrow> (\<exists>M. (\<forall>y. M y \<le> B M y) \<and> inres (M x) x')"
    unfolding RECT_def gfp_def
    by (auto simp: refine_pw_simps intro: le_funI dest: le_funD)
  thus ?thesis unfolding pw_le_iff .
qed
  
lemmas pw_RECT = pw_RECT_inres pw_RECT_nofail

subsection {* Proof Rules *}

subsubsection {* Proving Correctness *}
text {*
  In this section, we establish Hoare-like rules to prove that a program
  meets its specification.
*}

lemma RETURN_rule[refine_vcg]: "\<Phi> x \<Longrightarrow> RETURN x \<le> SPEC \<Phi>"
  by (auto simp: RETURN_def)
lemma RES_rule[refine_vcg]: "\<lbrakk>\<And>x. x\<in>S \<Longrightarrow> \<Phi> x\<rbrakk> \<Longrightarrow> RES S \<le> SPEC \<Phi>"
  by auto
lemma SUCCEED_rule[refine_vcg]: "SUCCEED \<le> SPEC \<Phi>" by auto
lemma FAIL_rule: "False \<Longrightarrow> FAIL \<le> SPEC \<Phi>" by auto
lemma SPEC_rule[refine_vcg]: "\<lbrakk>\<And>x. \<Phi> x \<Longrightarrow> \<Phi>' x\<rbrakk> \<Longrightarrow> SPEC \<Phi> \<le> SPEC \<Phi>'" by auto

lemma RETURN_to_SPEC_rule[refine_vcg]: "m\<le>SPEC (op = v) \<Longrightarrow> m\<le>RETURN v"
  by (simp add: pw_le_iff refine_pw_simps)

lemma Sup_img_rule_complete: 
  "(\<forall>x. x\<in>S \<longrightarrow> f x \<le> SPEC \<Phi>) \<longleftrightarrow> Sup (f`S) \<le> SPEC \<Phi>"
  apply rule
  apply (rule pw_leI)
  apply (auto simp: pw_le_iff refine_pw_simps) []
  apply (intro allI impI)
  apply (rule pw_leI)
  apply (auto simp: pw_le_iff refine_pw_simps) []
  done

lemma SUP_img_rule_complete: 
  "(\<forall>x. x\<in>S \<longrightarrow> f x \<le> SPEC \<Phi>) \<longleftrightarrow> SUPREMUM S f \<le> SPEC \<Phi>"
  using Sup_img_rule_complete [of S f] by simp

lemma Sup_img_rule[refine_vcg]: 
  "\<lbrakk> \<And>x. x\<in>S \<Longrightarrow> f x \<le> SPEC \<Phi> \<rbrakk> \<Longrightarrow> Sup(f`S) \<le> SPEC \<Phi>"
  by (auto simp: SUP_img_rule_complete[symmetric])

text {* This lemma is just to demonstrate that our rule is complete. *}
lemma bind_rule_complete: "bind M f \<le> SPEC \<Phi> \<longleftrightarrow> M \<le> SPEC (\<lambda>x. f x \<le> SPEC \<Phi>)"
  by (auto simp: pw_le_iff refine_pw_simps)
lemma bind_rule[refine_vcg]: 
  "\<lbrakk> M \<le> SPEC (\<lambda>x. f x \<le> SPEC \<Phi>) \<rbrakk> \<Longrightarrow> bind M (\<lambda>x. f x) \<le> SPEC \<Phi>"
  -- {* Note: @{text "\<eta>"}-expanded version helps Isabelle's unification to keep meaningful 
      variable names from the program *}
  by (auto simp: bind_rule_complete)

lemma ASSUME_rule[refine_vcg]: "\<lbrakk>\<Phi> \<Longrightarrow> \<Psi> ()\<rbrakk> \<Longrightarrow> ASSUME \<Phi> \<le> SPEC \<Psi>"
  by (cases \<Phi>) auto

lemma ASSERT_rule[refine_vcg]: "\<lbrakk>\<Phi>; \<Phi> \<Longrightarrow> \<Psi> ()\<rbrakk> \<Longrightarrow> ASSERT \<Phi> \<le> SPEC \<Psi>" by auto

lemma prod_rule[refine_vcg]: 
  "\<lbrakk>\<And>a b. p=(a,b) \<Longrightarrow> S a b \<le> SPEC \<Phi>\<rbrakk> \<Longrightarrow> case_prod S p \<le> SPEC \<Phi>"
  by (auto split: prod.split)

(* TODO: Add a simplifier setup that normalizes nested case-expressions to
  the vcg! *)
lemma prod2_rule[refine_vcg]:
  assumes "\<And>a b c d. \<lbrakk>ab=(a,b); cd=(c,d)\<rbrakk> \<Longrightarrow> f a b c d \<le> SPEC \<Phi>"
  shows "(\<lambda>(a,b) (c,d). f a b c d) ab cd \<le> SPEC \<Phi>"
  using assms
  by (auto split: prod.split)

lemma if_rule[refine_vcg]: 
  "\<lbrakk> b \<Longrightarrow> S1 \<le> SPEC \<Phi>; \<not>b \<Longrightarrow> S2 \<le> SPEC \<Phi>\<rbrakk> 
  \<Longrightarrow> (if b then S1 else S2) \<le> SPEC \<Phi>"
  by (auto)

lemma option_rule[refine_vcg]: 
  "\<lbrakk> v=None \<Longrightarrow> S1 \<le> SPEC \<Phi>; \<And>x. v=Some x \<Longrightarrow> f2 x \<le> SPEC \<Phi>\<rbrakk> 
  \<Longrightarrow> case_option S1 f2 v \<le> SPEC \<Phi>"
  by (auto split: option.split)

lemma Let_rule[refine_vcg]:
  "f x \<le> SPEC \<Phi> \<Longrightarrow> Let x f \<le> SPEC \<Phi>" by auto

lemma Let_rule':
  assumes "\<And>x. x=v \<Longrightarrow> f x \<le> SPEC \<Phi>"
  shows "Let v (\<lambda>x. f x) \<le> SPEC \<Phi>"
  using assms by simp


text {* The following lemma shows that greatest and least fixed point are equal,
  if we can provide a variant. *}
thm RECT_eq_REC
lemma RECT_eq_REC_old:
  assumes WF: "wf V"
  assumes I0: "I x"
  assumes IS: "\<And>f x. I x \<Longrightarrow> 
    body (\<lambda>x'. do { ASSERT (I x' \<and> (x',x)\<in>V); f x'}) x \<le> body f x"
  shows "REC\<^sub>T body x = REC body x"
  apply (rule RECT_eq_REC)
  apply (rule WF)
  apply (rule I0)
  apply (rule order_trans[OF _ IS])
  apply (subgoal_tac "(\<lambda>x'. if I x' \<and> (x', x) \<in> V then f x' else FAIL) = 
    (\<lambda>x'. ASSERT (I x' \<and> (x', x) \<in> V) \<guillemotright>= (\<lambda>_. f x'))")
  apply simp
  apply (rule ext)
  apply (rule pw_eqI)
  apply (auto simp add: refine_pw_simps)
  done

(* TODO: Also require RECT_le_rule. Derive RECT_invisible_refine from that. *)
lemma REC_le_rule:
  assumes M: "mono body"
  assumes I0: "(x,x')\<in>R"
  assumes IS: "\<And>f x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le> M x'; (x,x')\<in>R \<rbrakk> 
    \<Longrightarrow> body f x \<le> M x'"
  shows "REC body x \<le> M x'"
proof -
  have "\<forall>x x'. (x,x')\<in>R \<longrightarrow> lfp body x \<le> M x'"
    apply (rule lfp_cadm_induct[OF _ _ M])
      apply rule+
      unfolding Sup_fun_def
      apply (rule SUP_least)
      apply simp

      apply simp

      using IS 
      apply blast
    done
  with I0 show ?thesis 
    unfolding REC_def
    by (auto simp: M)
qed


(* TODO: Invariant annotations and vcg-rule
  Possibility 1: Semantically alter the program, such that it fails if the 
    invariant does not hold
  Possibility 2: Only syntactically annotate the invariant, as hint for the VCG.
*)

subsubsection {* Proving Monotonicity *}

lemma nr_mono_bind:
  assumes MA: "mono A" and MB: "\<And>s. mono (B s)"
  shows "mono (\<lambda>F s. bind (A F s) (\<lambda>s'. B s F s'))"
  apply (rule monoI)
  apply (rule le_funI)
  apply (rule bind_mono)
  apply (auto dest: monoD[OF MA, THEN le_funD]) []
  apply (auto dest: monoD[OF MB, THEN le_funD]) []
  done


lemma nr_mono_bind': "mono (\<lambda>F s. bind (f s) F)"
  apply rule
  apply (rule le_funI)
  apply (rule bind_mono)
  apply (auto dest: le_funD)
  done

lemmas nr_mono = nr_mono_bind nr_mono_bind' mono_const mono_if mono_id

subsubsection {* Proving Refinement *}
text {* In this subsection, we establish rules to prove refinement between 
  structurally similar programs. All rules are formulated including a possible
  data refinement via a refinement relation. If this is not required, the 
  refinement relation can be chosen to be the identity relation.
  *}

text {* If we have two identical programs, this rule solves the refinement goal
  immediately, using the identity refinement relation. *}
lemma Id_refine[refine0]: "S \<le> \<Down>Id S" by auto

lemma RES_refine: 
  assumes "S\<subseteq>Domain R" 
  assumes "\<And>x x'. \<lbrakk>x\<in>S; (x,x')\<in>R\<rbrakk> \<Longrightarrow> x'\<in>S'"
  shows "RES S \<le> \<Down>R (RES S')" 
  using assms 
  by (force simp: conc_fun_RES)

lemma RES_refine_sv: 
  "\<lbrakk>single_valued R; 
    \<And>s. s\<in>S \<Longrightarrow> \<exists>s'\<in>S'. (s,s')\<in>R\<rbrakk> \<Longrightarrow> RES S \<le> \<Down>R (RES S')" 
  by (auto simp: conc_fun_RES dest: single_valuedD)

lemma SPEC_refine: 
  assumes "S \<le> SPEC (\<lambda>x. x\<in>Domain R \<and> (\<forall>x'. (x,x')\<in>R \<longrightarrow> \<Phi> x'))"
  shows "S \<le> \<Down>R (SPEC \<Phi>)" 
  using assms by (force simp: pw_le_iff refine_pw_simps)

lemma SPEC_refine_sv: 
  assumes "single_valued R"
  assumes "S \<le> SPEC (\<lambda>x. \<exists>x'. (x,x')\<in>R \<and> \<Phi> x')"
  shows "S \<le> \<Down>R (SPEC \<Phi>)"
  using assms
  by (force simp: pw_le_iff refine_pw_simps dest: single_valuedD)

(* TODO/FIXME: This is already part of a type-based heuristics! *)
lemma Id_SPEC_refine[refine]: 
  "S \<le> SPEC \<Phi> \<Longrightarrow> S \<le> \<Down>Id (SPEC \<Phi>)" by simp

lemma RETURN_refine: 
  assumes "x\<in>Domain R"
  assumes "\<And>x''. (x,x'')\<in>R \<Longrightarrow> x''=x'"
  shows "RETURN x \<le> \<Down>R (RETURN x')"
  using assms by (auto simp: pw_le_iff refine_pw_simps)

lemma RETURN_refine_sv[refine]:
  assumes "single_valued R"
  assumes "(x,x')\<in>R"
  shows "RETURN x \<le> \<Down>R (RETURN x')"
  apply (rule RETURN_refine)
  using assms
  by (auto dest: single_valuedD)

lemma RETURN_SPEC_refine_sv:
  assumes SV: "single_valued R"
  assumes "\<exists>x'. (x,x')\<in>R \<and> \<Phi> x'"
  shows "RETURN x \<le> \<Down>R (SPEC \<Phi>)"
  using assms 
  by (auto simp: pw_le_iff refine_pw_simps)

lemma FAIL_refine[refine]: "X \<le> \<Down>R FAIL" by auto
lemma SUCCEED_refine[refine]: "SUCCEED \<le> \<Down>R X'" by auto

text {* The next two rules are incomplete, but a good approximation for refining
  structurally similar programs. *}
lemma bind_refine':
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x'. \<lbrakk> (x,x')\<in>R'; inres M x; inres M' x';
    nofail M; nofail M'
  \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bind M (\<lambda>x. f x) \<le> \<Down> R (bind M' (\<lambda>x'. f' x'))"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  apply fast
  done

lemma bind_refine[refine]:
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x'. \<lbrakk> (x,x')\<in>R' \<rbrakk> 
    \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bind M (\<lambda>x. f x) \<le> \<Down> R (bind M' (\<lambda>x'. f' x'))"
  apply (rule bind_refine') using assms by auto

text {* Special cases for refinement of binding to @{text "RES"}
  statements *}
lemma bind_refine_RES:
  "\<lbrakk>RES X \<le> \<Down> R' M';
  \<And>x x'. \<lbrakk>(x, x') \<in> R'; x \<in> X \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')\<rbrakk>
  \<Longrightarrow> RES X \<guillemotright>= (\<lambda>x. f x) \<le> \<Down> R (M' \<guillemotright>= (\<lambda>x'. f' x'))"

  "\<lbrakk>M \<le> \<Down> R' (RES X');
  \<And>x x'. \<lbrakk>(x, x') \<in> R'; x' \<in> X' \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')\<rbrakk>
  \<Longrightarrow> M \<guillemotright>= (\<lambda>x. f x) \<le> \<Down> R (RES X' \<guillemotright>= (\<lambda>x'. f' x'))"

  "\<lbrakk>RES X \<le> \<Down> R' (RES X');
  \<And>x x'. \<lbrakk>(x, x') \<in> R'; x \<in> X; x' \<in> X'\<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')\<rbrakk>
  \<Longrightarrow> RES X \<guillemotright>= (\<lambda>x. f x) \<le> \<Down> R (RES X' \<guillemotright>= (\<lambda>x'. f' x'))"
  by (auto intro!: bind_refine')

declare bind_refine_RES(1,2)[refine]
declare bind_refine_RES(3)[refine]


lemma ASSERT_refine[refine]:
  "\<lbrakk> \<Phi>'\<Longrightarrow>\<Phi> \<rbrakk> \<Longrightarrow> ASSERT \<Phi> \<le> \<Down>Id (ASSERT \<Phi>')"
  by (cases \<Phi>') auto

lemma ASSUME_refine[refine]: 
  "\<lbrakk> \<Phi> \<Longrightarrow> \<Phi>' \<rbrakk> \<Longrightarrow> ASSUME \<Phi> \<le> \<Down>Id (ASSUME \<Phi>')"
  by (cases \<Phi>) auto

text {*
  Assertions and assumptions are treated specially in bindings
*}
lemma ASSERT_refine_right:
  assumes "\<Phi> \<Longrightarrow> S \<le>\<Down>R S'"
  shows "S \<le>\<Down>R (do {ASSERT \<Phi>; S'})"
  using assms by (cases \<Phi>) auto
lemma ASSERT_refine_right_pres:
  assumes "\<Phi> \<Longrightarrow> S \<le>\<Down>R (do {ASSERT \<Phi>; S'})"
  shows "S \<le>\<Down>R (do {ASSERT \<Phi>; S'})"
  using assms by (cases \<Phi>) auto

lemma ASSERT_refine_left:
  assumes "\<Phi>"
  assumes "\<Phi> \<Longrightarrow> S \<le> \<Down>R S'"
  shows "do{ASSERT \<Phi>; S} \<le> \<Down>R S'"
  using assms by (cases \<Phi>) auto

lemma ASSUME_refine_right:
  assumes "\<Phi>"
  assumes "\<Phi> \<Longrightarrow> S \<le>\<Down>R S'"
  shows "S \<le>\<Down>R (do {ASSUME \<Phi>; S'})"
  using assms by (cases \<Phi>) auto

lemma ASSUME_refine_left:
  assumes "\<Phi> \<Longrightarrow> S \<le> \<Down>R S'"
  shows "do {ASSUME \<Phi>; S} \<le> \<Down>R S'"
  using assms by (cases \<Phi>) auto

lemma ASSUME_refine_left_pres:
  assumes "\<Phi> \<Longrightarrow> do {ASSUME \<Phi>; S} \<le> \<Down>R S'"
  shows "do {ASSUME \<Phi>; S} \<le> \<Down>R S'"
  using assms by (cases \<Phi>) auto

text {* Warning: The order of @{text "[refine]"}-declarations is 
  important here, as preconditions should be generated before 
  additional proof obligations. *}
lemmas [refine0] = ASSUME_refine_right
lemmas [refine0] = ASSERT_refine_left
lemmas [refine0] = ASSUME_refine_left
lemmas [refine0] = ASSERT_refine_right

text {* For backward compatibility, as @{text "intro refine"} still
  seems to be used instead of @{text "refine_rcg"}. *}
lemmas [refine] = ASSUME_refine_right
lemmas [refine] = ASSERT_refine_left
lemmas [refine] = ASSUME_refine_left
lemmas [refine] = ASSERT_refine_right


lemma REC_refine[refine]:
  assumes M: "mono body"
  assumes R0: "(x,x')\<in>R"
  assumes RS: "\<And>f f' x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le>\<Down>S (f' x'); (x,x')\<in>R \<rbrakk> 
    \<Longrightarrow> body f x \<le>\<Down>S (body' f' x')"
  shows "REC (\<lambda>f x. body f x) x \<le>\<Down>S (REC (\<lambda>f' x'. body' f' x') x')"
  unfolding REC_def
  apply (clarsimp simp add: M)
proof -
  assume M': "mono body'"
  have "\<forall>x x'. (x,x')\<in>R \<longrightarrow> lfp body x \<le> \<Down>S (lfp body' x')"
    apply (rule lfp_cadm_induct[OF _ _ M])
      apply rule+
      unfolding Sup_fun_def
      apply (rule SUP_least)
      apply simp

      apply simp

      apply (rule)+
      apply (subst lfp_unfold[OF M'])
      apply (rule RS)
      apply blast
      apply assumption
    done
  thus "lfp body x \<le> \<Down> S (lfp body' x')" by (blast intro: R0)
qed

lemma RECT_refine[refine]:
  assumes M: "mono body"
  assumes R0: "(x,x')\<in>R"
  assumes RS: "\<And>f f' x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le>\<Down>S (f' x'); (x,x')\<in>R \<rbrakk> 
    \<Longrightarrow> body f x \<le>\<Down>S (body' f' x')"
  shows "RECT (\<lambda>f x. body f x) x \<le>\<Down>S (RECT (\<lambda>f' x'. body' f' x') x')"
  unfolding RECT_def
  apply (clarsimp simp add: M)
proof -
  assume M': "mono body'"
  have "\<forall>x x'. (x,x')\<in>R \<longrightarrow> \<Up>S (gfp body x) \<le> (gfp body' x')"
    apply (rule gfp_cadm_induct[OF _ _ M'])
      apply rule+
      unfolding Inf_fun_def
      apply (rule INF_greatest)
      apply simp

      apply simp

      apply (rule)+
      apply (subst gfp_unfold[OF M])
      apply (rule RS[unfolded ac.galois])
      apply blast
      apply assumption
    done
  thus "gfp body x \<le> \<Down> S (gfp body' x')" 
    unfolding ac.galois by (blast intro: R0)
qed

lemma if_refine[refine]:
  assumes "b \<longleftrightarrow> b'"
  assumes "\<lbrakk>b;b'\<rbrakk> \<Longrightarrow> S1 \<le> \<Down>R S1'"
  assumes "\<lbrakk>\<not>b;\<not>b'\<rbrakk> \<Longrightarrow> S2 \<le> \<Down>R S2'"
  shows "(if b then S1 else S2) \<le> \<Down>R (if b' then S1' else S2')"
  using assms by auto

lemma Let_unfold_refine[refine]:
  assumes "f x \<le> \<Down>R (f' x')"
  shows "Let x f \<le> \<Down>R (Let x' f')"
  using assms by auto

text {* The next lemma is sometimes more convenient, as it prevents
  large let-expressions from exploding by being completely unfolded. *}
lemma Let_refine:
  assumes "(m,m')\<in>R'"
  assumes "\<And>x x'. (x,x')\<in>R' \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "Let m (\<lambda>x. f x) \<le>\<Down>R (Let m' (\<lambda>x'. f' x'))"
  using assms by auto

lemma case_option_refine[refine]:
  assumes "(x,x')\<in>Id"
  assumes "fn \<le> \<Down>R fn'"
  assumes "\<And>v v'. \<lbrakk>x=Some v; (v,v')\<in>Id\<rbrakk> \<Longrightarrow> fs v \<le> \<Down>R (fs' v')"
  shows "case_option fn (\<lambda>v. fs v) x \<le> \<Down>R (case_option fn' (\<lambda>v'. fs' v') x')"
  using assms by (auto split: option.split)

text {* It is safe to split conjunctions in refinement goals.*}
declare conjI[refine]

text {* The following rules try to compensate for some structural changes,
  like inlining lets or converting binds to lets. *}
lemma remove_Let_refine[refine2]:
  assumes "M \<le> \<Down>R (f x)"
  shows "M \<le> \<Down>R (Let x f)" using assms by auto

lemma intro_Let_refine[refine2]:
  assumes "f x \<le> \<Down>R M'"
  shows "Let x f \<le> \<Down>R M'" using assms by auto
  
lemma bind2let_refine[refine2]:
  assumes "RETURN x \<le> \<Down>R' M'"
  assumes "\<And>x'. (x,x')\<in>R' \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "Let x f \<le> \<Down>R (bind M' (\<lambda>x'. f' x'))"
  using assms 
  apply (simp add: pw_le_iff refine_pw_simps) 
  apply fast
  done

lemma bind_Let_refine2[refine2]: "\<lbrakk> 
    m' \<le>\<Down>R' (RETURN x);
    \<And>x'. \<lbrakk>inres m' x'; (x',x)\<in>R'\<rbrakk> \<Longrightarrow> f' x' \<le> \<Down>R (f x) 
  \<rbrakk> \<Longrightarrow> m'\<guillemotright>=(\<lambda>x'. f' x') \<le> \<Down>R (Let x (\<lambda>x. f x))"
  apply (simp add: pw_le_iff refine_pw_simps)
  apply blast
  done

lemma bind2letRETURN_refine[refine2]:
  assumes "RETURN x \<le> \<Down>R' M'"
  assumes "\<And>x'. (x,x')\<in>R' \<Longrightarrow> RETURN (f x) \<le> \<Down>R (f' x')"
  shows "RETURN (Let x f) \<le> \<Down>R (bind M' (\<lambda>x'. f' x'))"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  apply fast
  done

lemma RETURN_as_SPEC_refine_sv[refine2]:
  assumes "single_valued R"
  assumes "M \<le> SPEC (\<lambda>c. (c,a)\<in>R)"
  shows "M \<le> \<Down>R (RETURN a)"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  done

lemma if_RETURN_refine [refine2]:
  assumes "b \<longleftrightarrow> b'"
  assumes "\<lbrakk>b;b'\<rbrakk> \<Longrightarrow> RETURN S1 \<le> \<Down>R S1'"
  assumes "\<lbrakk>\<not>b;\<not>b'\<rbrakk> \<Longrightarrow> RETURN S2 \<le> \<Down>R S2'"
  shows "RETURN (if b then S1 else S2) \<le> \<Down>R (if b' then S1' else S2')"
  (* this is nice to have for small functions, hence keep it in refine2 *)
  using assms
  by (simp add: pw_le_iff refine_pw_simps)

lemma RES_sng_as_SPEC_refine_sv[refine2]:
  assumes "single_valued R"
  assumes "M \<le> SPEC (\<lambda>c. (c,a)\<in>R)"
  shows "M \<le> \<Down>R (RES {a})"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  done

lemma RETURN_as_SPEC_refine: 
  "\<And>M R. M \<le> \<Down>R (SPEC (\<lambda>x. x=v)) \<Longrightarrow> M \<le>\<Down>R (RETURN v)"
  by (simp add: RETURN_def)

lemma intro_spec_refine_iff:
  "(bind (RES X) f \<le> \<Down>R M) \<longleftrightarrow> (\<forall>x\<in>X. f x \<le> \<Down>R M)"
  apply (simp add: pw_le_iff refine_pw_simps)
  apply blast
  done

lemma intro_spec_refine[refine2]:
  assumes "\<And>x. x\<in>X \<Longrightarrow> f x \<le> \<Down>R M"
  shows "bind (RES X) (\<lambda>x. f x) \<le> \<Down>R M"
  using assms
  by (simp add: intro_spec_refine_iff)


text {* The following rules are intended for manual application, to reflect 
  some common structural changes, that, however, are not suited to be applied
  automatically. *}

text {* Replacing a let by a deterministic computation *}
lemma let2bind_refine:
  assumes "m \<le> \<Down>R' (RETURN m')"
  assumes "\<And>x x'. (x,x')\<in>R' \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "bind m (\<lambda>x. f x) \<le> \<Down>R (Let m' (\<lambda>x'. f' x'))"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  apply blast
  done



text {* Introduce a new binding, without a structural match in the abstract 
  program *}
lemma intro_bind_refine:
  assumes "m \<le> \<Down>R' (RETURN m')"
  assumes "\<And>x. (x,m')\<in>R' \<Longrightarrow> f x \<le> \<Down>R m''"
  shows "bind m (\<lambda>x. f x) \<le> \<Down>R m''"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  apply blast
  done

lemma intro_bind_refine_id:
  assumes "m \<le> (SPEC (op = m'))"
  assumes "f m' \<le> \<Down>R m''"
  shows "bind m f \<le> \<Down>R m''"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  apply blast
  done

subsection {* Relators *}

definition nres_rel where 
  nres_rel_def_internal: "nres_rel R \<equiv> {(c,a). c \<le> \<Down>R a}"

lemma nres_rel_def: "\<langle>R\<rangle>nres_rel \<equiv> {(c,a). c \<le> \<Down>R a}"
  by (simp add: nres_rel_def_internal relAPP_def)

lemma nres_relD: "(c,a)\<in>\<langle>R\<rangle>nres_rel \<Longrightarrow> c \<le>\<Down>R a" by (simp add: nres_rel_def)
lemma nres_relI: "c \<le>\<Down>R a \<Longrightarrow> (c,a)\<in>\<langle>R\<rangle>nres_rel" by (simp add: nres_rel_def)

lemma param_RES[param]:
  "(RES,RES) \<in> \<langle>R\<rangle>set_rel \<rightarrow> \<langle>R\<rangle>nres_rel"
  unfolding set_rel_def nres_rel_def
  by (auto intro: RES_refine)

lemma param_RETURN[param]: 
  "single_valued R \<Longrightarrow> (RETURN,RETURN) \<in> R \<rightarrow> \<langle>R\<rangle>nres_rel"
  by (auto simp: nres_rel_def RETURN_refine_sv)

lemma param_bind[param]:
  "(bind,bind) \<in> \<langle>Ra\<rangle>nres_rel \<rightarrow> (Ra\<rightarrow>\<langle>Rb\<rangle>nres_rel) \<rightarrow> \<langle>Rb\<rangle>nres_rel"
  by (auto simp: nres_rel_def intro: bind_refine dest: fun_relD)

subsection {* Autoref Setup *}

consts i_nres :: "interface \<Rightarrow> interface"
lemmas [autoref_rel_intf] = REL_INTFI[of nres_rel i_nres]

(*lemma id_nres[autoref_id_self]: "ID_LIST 
  (l SUCCEED FAIL bind (REC::_ \<Rightarrow> _ \<Rightarrow> _ nres,1) (RECT::_ \<Rightarrow> _ \<Rightarrow> _ nres,1))"
  by simp_all
*)
(*definition [simp]: "op_RETURN x \<equiv> RETURN x"
lemma [autoref_op_pat_def]: "RETURN x \<equiv> op_RETURN x" by simp
*)

definition [simp]: "op_nres_ASSERT_bnd \<Phi> m \<equiv> do {ASSERT \<Phi>; m}"

context begin interpretation autoref_syn .
lemma id_ASSERT[autoref_op_pat_def]:
  "do {ASSERT \<Phi>; m} \<equiv> OP (op_nres_ASSERT_bnd \<Phi>)$m"
  by simp

definition [simp]: "op_nres_ASSUME_bnd \<Phi> m \<equiv> do {ASSUME \<Phi>; m}"
lemma id_ASSUME[autoref_op_pat_def]:
  "do {ASSUME \<Phi>; m} \<equiv> OP (op_nres_ASSUME_bnd \<Phi>)$m"
  by simp

end

lemma autoref_SUCCEED[autoref_rules]: "(SUCCEED,SUCCEED) \<in> \<langle>R\<rangle>nres_rel"
  by (auto simp: nres_rel_def)

lemma autoref_FAIL[autoref_rules]: "(FAIL,FAIL) \<in> \<langle>R\<rangle>nres_rel"
  by (auto simp: nres_rel_def)

lemma autoref_RETURN[autoref_rules]: 
  "PREFER single_valued R \<Longrightarrow> (RETURN,RETURN) \<in> R \<rightarrow> \<langle>R\<rangle>nres_rel"
  by (auto simp: nres_rel_def RETURN_refine_sv)

lemma autoref_bind[autoref_rules]: 
  "(bind,bind) \<in> \<langle>R1\<rangle>nres_rel \<rightarrow> (R1\<rightarrow>\<langle>R2\<rangle>nres_rel) \<rightarrow> \<langle>R2\<rangle>nres_rel"
  apply (intro fun_relI)
  apply (rule nres_relI)
  apply (rule bind_refine)
  apply (erule nres_relD)
  apply (erule (1) fun_relD[THEN nres_relD])
  done
 
context begin interpretation autoref_syn .
lemma autoref_ASSERT[autoref_rules]:
  assumes "\<Phi> \<Longrightarrow> (m',m)\<in>\<langle>R\<rangle>nres_rel"
  shows "(
    m',
    (OP (op_nres_ASSERT_bnd \<Phi>) ::: \<langle>R\<rangle>nres_rel \<rightarrow> \<langle>R\<rangle>nres_rel) $ m)\<in>\<langle>R\<rangle>nres_rel"
  using assms unfolding nres_rel_def
  by (simp add: ASSERT_refine_right)

lemma autoref_ASSUME[autoref_rules]:
  assumes "SIDE_PRECOND \<Phi>"
  assumes "\<Phi> \<Longrightarrow> (m',m)\<in>\<langle>R\<rangle>nres_rel"
  shows "(
    m',
    (OP (op_nres_ASSUME_bnd \<Phi>) ::: \<langle>R\<rangle>nres_rel \<rightarrow> \<langle>R\<rangle>nres_rel) $ m)\<in>\<langle>R\<rangle>nres_rel"
  using assms unfolding nres_rel_def
  by (simp add: ASSUME_refine_right)

lemma autoref_REC[autoref_rules]:
  assumes "(B,B')\<in>(Ra\<rightarrow>\<langle>Rr\<rangle>nres_rel) \<rightarrow> Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel"
  assumes "DEFER mono B"
  shows "(REC B,
    (OP REC 
      ::: ((Ra\<rightarrow>\<langle>Rr\<rangle>nres_rel) \<rightarrow> Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel) \<rightarrow> Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel)$B'
    ) \<in> Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel"
  apply (intro fun_relI)
  using assms
  apply (auto simp: nres_rel_def intro!: REC_refine)
  apply (simp add: fun_rel_def)
  apply blast
  done

lemma autoref_RECT[autoref_rules]:
  assumes "(B,B') \<in> (Ra\<rightarrow>\<langle>Rr\<rangle>nres_rel) \<rightarrow> Ra\<rightarrow>\<langle>Rr\<rangle>nres_rel"
  assumes "DEFER mono B"
  shows "(RECT B,
    (OP RECT 
      ::: ((Ra\<rightarrow>\<langle>Rr\<rangle>nres_rel) \<rightarrow> Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel) \<rightarrow> Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel)$B'
   ) \<in> Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel"
  apply (intro fun_relI)
  using assms
  apply (auto simp: nres_rel_def intro!: RECT_refine)
  apply (simp add: fun_rel_def)
  apply blast
  done
end

subsection {* Convenience Rules*}
text {*
  In this section, we define some lemmas that simplify common prover tasks.
*}

lemma ref_two_step: "A\<le>\<Down>R  B \<Longrightarrow> B\<le>    C \<Longrightarrow> A\<le>\<Down>R  C" 
  by (rule conc_trans_additional)

   
lemma pw_ref_sv_iff:
  shows "single_valued R \<Longrightarrow> S \<le> \<Down>R S' 
  \<longleftrightarrow> (nofail S' 
    \<longrightarrow> nofail S \<and> (\<forall>x. inres S x \<longrightarrow> (\<exists>s'. (x, s') \<in> R \<and> inres S' s')))"
  by (simp add: pw_le_iff refine_pw_simps)

lemma pw_ref_svI:
  assumes "single_valued R"
  assumes "nofail S' 
    \<longrightarrow> nofail S \<and> (\<forall>x. inres S x \<longrightarrow> (\<exists>s'. (x, s') \<in> R \<and> inres S' s'))"
  shows "S \<le> \<Down>R S'"
  using assms
  by (simp add: pw_ref_sv_iff)

text {* Introduce an abstraction relation. Usage: 
  @{text "rule introR[where R=absRel]"}
*}
lemma introR: "(a,a')\<in>R \<Longrightarrow> (a,a')\<in>R" .

lemma intro_prgR: "c \<le> \<Down>R a \<Longrightarrow> c \<le> \<Down>R a" by auto


lemma le_ASSERTI_pres:
  assumes "\<Phi> \<Longrightarrow> S \<le> do {ASSERT \<Phi>; S'}"
  shows "S \<le> do {ASSERT \<Phi>; S'}"
  using assms by (auto intro: le_ASSERTI)

lemma RETURN_ref_SPECD:
  assumes "RETURN c \<le> \<Down>R (SPEC \<Phi>)"
  obtains a where "(c,a)\<in>R" "\<Phi> a"
  using assms
  by (auto simp: pw_le_iff refine_pw_simps)

lemma RETURN_ref_RETURND:
  assumes "RETURN c \<le> \<Down>R (RETURN a)"
  shows "(c,a)\<in>R"
  using assms
  apply (auto simp: pw_le_iff refine_pw_simps)
  done

lemma SPEC_eq_is_RETURN:
  "SPEC (op = x) = RETURN x"
  "SPEC (\<lambda>x. x=y) = RETURN y"
  by (auto simp: RETURN_def)

lemma RETURN_SPEC_conv: "RETURN r = SPEC (\<lambda>x. x=r)"
  by (simp add: RETURN_def)

lemma build_rel_SPEC: 
  "M \<le> SPEC ( \<lambda>x. \<Phi> (\<alpha> x) \<and> I x) \<Longrightarrow> M \<le> \<Down>(build_rel \<alpha> I) (SPEC \<Phi>)"
  by (auto simp: pw_le_iff refine_pw_simps build_rel_def)

lemma refine_IdD: "c \<le> \<Down>Id a \<Longrightarrow> c \<le> a" by simp

lemma le_RES_nofailI:
  assumes "a\<le>RES x"
  shows "nofail a"
  using assms
  by (metis nofail_simps(2) pwD1)

lemma sv_add_invar_refineI:
  assumes "single_valued R"
  assumes "f x \<le>\<Down>R (f' x')"
    and "nofail (f x) \<Longrightarrow> f x \<le> SPEC I"
  shows "f x \<le> \<Down> {(c, a). (c, a) \<in> R \<and> I c} (f' x')"
  using assms
  by (simp add: pw_le_iff refine_pw_simps sv_add_invar)


lemma bind_RES_RETURN_eq: "bind (RES X) (\<lambda>x. RETURN (f x)) = 
  RES { f x | x. x\<in>X }"
  by (simp add: pw_eq_iff refine_pw_simps)
    blast

lemma bind_RES_RETURN2_eq: "bind (RES X) (\<lambda>(x,y). RETURN (f x y)) = 
  RES { f x y | x y. (x,y)\<in>X }"
  apply (simp add: pw_eq_iff refine_pw_simps)
  apply blast
  done

lemma le_SPEC_bindI: 
  assumes "\<Phi> x"
  assumes "m \<le> f x"
  shows "m \<le> SPEC \<Phi> \<guillemotright>= f"
  using assms by (auto simp add: pw_le_iff refine_pw_simps)

lemma bind_assert_refine: 
  assumes "m1 \<le> SPEC \<Phi>"
  assumes "\<And>x. \<Phi> x \<Longrightarrow> m2 x \<le> m'"
  shows "do {x\<leftarrow>m1; ASSERT (\<Phi> x); m2 x} \<le> m'"
  using assms
  by (simp add: pw_le_iff refine_pw_simps) blast


text {* The following rules are useful for massaging programs before the 
  refinement takes place *}
lemma let_to_bind_conv: 
  "Let x f = RETURN x\<guillemotright>=f"
  by simp

lemmas bind_to_let_conv = let_to_bind_conv[symmetric]

lemma pull_out_let_conv: "RETURN (Let x f) = Let x (\<lambda>x. RETURN (f x))"
  by simp

lemma push_in_let_conv: 
  "Let x (\<lambda>x. RETURN (f x)) = RETURN (Let x f)"
  "Let x (RETURN o f) = RETURN (Let x f)"
  by simp_all

lemma pull_out_RETURN_case_option: 
  "case_option (RETURN a) (\<lambda>v. RETURN (f v)) x = RETURN (case_option a f x)"
  by (auto split: option.splits)

lemma if_bind_cond_refine: 
  assumes "ci \<le> RETURN b"
  assumes "b \<Longrightarrow> ti\<le>\<Down>R t"
  assumes "\<not>b \<Longrightarrow> ei\<le>\<Down>R e"
  shows "do {b\<leftarrow>ci; if b then ti else ei} \<le> \<Down>R (if b then t else e)"
  using assms
  by (auto simp add: refine_pw_simps pw_le_iff)

lemma intro_RETURN_Let_refine:
  assumes "RETURN (f x) \<le> \<Down>R M'"
  shows "RETURN (Let x f) \<le> \<Down>R M'" 
  (* this should be needed very rarely - so don't add it *)
  using assms by auto

text {* 
  This rule establishes equality between RECT and REC, using an additional 
  invariant. Note that the default way is to prove termination in
  first place, instead of re-proving parts of the invariant just for the
  termination proof. *}
lemma RECT_eq_REC':
  assumes WF: "wf V'"
  assumes I0: "I x"
  assumes IS: "\<And>f x. I x \<Longrightarrow> (\<And>x. f x \<le> RECT body x) \<Longrightarrow>
    body (\<lambda>x'. if (I x' \<and> (x',x)\<in>V') then f x' else top) x \<le> body f x"
  shows "RECT body x = REC body x"
proof (cases "mono body")
  assume "\<not>mono body"
  thus ?thesis unfolding REC_def RECT_def by simp
next
  assume MONO: "mono body"

  have lfp_ubound: "\<And>x. lfp body x \<le> RECT body x"
  proof -
    fix x
    from REC_le_RECT[of body x, unfolded REC_def] MONO
    show "lfp body x \<le> RECT body x" by auto
  qed

  from lfp_le_gfp' MONO have "lfp body x \<le> gfp body x" .
  moreover have "I x \<longrightarrow> gfp body x \<le> lfp body x"
    using WF
    apply (induct rule: wf_induct[consumes 1])
    apply (rule impI)
    apply (subst lfp_unfold[OF MONO])
    apply (subst gfp_unfold[OF MONO])
    apply (rule order_trans[OF _ IS])
    apply (rule monoD[OF MONO,THEN le_funD])
    apply (rule le_funI)
    apply simp
    apply simp
    apply (rule lfp_ubound)
    done
  ultimately show ?thesis
    unfolding REC_def RECT_def
    apply (rule_tac antisym)
    using I0 MONO by auto
qed

subsubsection {* Boolean Operations on Specifications *}
lemma SPEC_iff:
  assumes "P \<le> SPEC (\<lambda>s. Q s \<longrightarrow> R s)"
  and "P \<le> SPEC (\<lambda>s. \<not> Q s \<longrightarrow> \<not> R s)"
  shows "P \<le> SPEC (\<lambda>s. Q s \<longleftrightarrow> R s)"
  using assms[THEN pw_le_iff[THEN iffD1]]
  by (auto intro!: pw_leI)

lemma SPEC_rule_conjI:
  assumes "A \<le> SPEC P" and "A \<le> SPEC Q"
    shows "A \<le> SPEC (\<lambda>v. P v \<and> Q v)"
proof -
  have "A \<le> inf (SPEC P) (SPEC Q)" using assms by (rule_tac inf_greatest) assumption
  thus ?thesis by (auto simp add:Collect_conj_eq)
qed

lemma SPEC_rule_conjunct1:
  assumes "A \<le> SPEC (\<lambda>v. P v \<and> Q v)"
    shows "A \<le> SPEC P"
proof -
  note assms
  also have "\<dots> \<le> SPEC P" by (rule SPEC_rule) auto
  finally show ?thesis .
qed

lemma SPEC_rule_conjunct2:
  assumes "A \<le> SPEC (\<lambda>v. P v \<and> Q v)"
    shows "A \<le> SPEC Q"
proof -
  note assms
  also have "\<dots> \<le> SPEC Q" by (rule SPEC_rule) auto
  finally show ?thesis .
qed


subsubsection {* Pointwise Reasoning *}
lemma inres_if:
  "\<lbrakk> inres (if P then Q else R) x; \<lbrakk>P; inres Q x\<rbrakk> \<Longrightarrow> S; \<lbrakk>\<not> P; inres R x\<rbrakk> \<Longrightarrow> S \<rbrakk> \<Longrightarrow> S"
by (metis (full_types))

lemma inres_SPEC:
  "inres M x \<Longrightarrow> M \<le> SPEC \<Phi> \<Longrightarrow> \<Phi> x"
by (auto dest: pwD2)

lemma SPEC_nofail:
  "X \<le> SPEC \<Phi> \<Longrightarrow> nofail X"
by (auto dest: pwD1)


end
