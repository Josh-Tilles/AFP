(*  Title:      Containers/Map_To_Mapping.thy
    Author:     Andreas Lochbihler, ETH Zurich *)

theory Map_To_Mapping imports
  "Mapping_Impl"
begin

section {* Infrastructure for operation identification *}

text {*
  To convert theorems from @{typ "'a \<Rightarrow> 'b option"} to @{typ "('a, 'b) mapping"} using lifting / transfer,
  we first introduce constants for the empty map and map lookup, then apply lifting / transfer,
  and finally eliminate the non-converted constants again.
*}

text {* Dynamic theorem list of rewrite rules that are applied before Transfer.transferred *}
ML {*
structure Containers_Pre = Named_Thms
(
  val name = @{binding containers_pre}
  val description = "Preprocessing rewrite rules in operation identification for Containers"
)
*}
setup {* Containers_Pre.setup *}

text {* Dynamic theorem list of rewrite rules that are applied after Transfer.transferred *}
ML {*
structure Containers_Post = Named_Thms
(
  val name = @{binding containers_post}
  val description = "Postprocessing rewrite rules in operation identification for Containers"
)
*}
setup {* Containers_Post.setup *}

context begin interpretation lifting_syntax .

definition map_empty :: "'a \<Rightarrow> 'b option"
where [code_unfold]: "map_empty = Map.empty"

declare map_empty_def[containers_post, symmetric, containers_pre]

declare Mapping.empty.transfer[transfer_rule del]

lemma map_empty_transfer [transfer_rule]:
  "(pcr_mapping A B) map_empty Mapping.empty"
unfolding map_empty_def by(rule Mapping.empty.transfer)


definition map_apply :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a \<Rightarrow> 'b option"
where [code_unfold]: "map_apply = (\<lambda>m. m)"

lemma eq_map_apply: "m x \<equiv> map_apply m x"
by(simp add: map_apply_def)

declare eq_map_apply[symmetric, abs_def, containers_post]

text {* We cannot use @{thm [source] eq_map_apply} as a fold rule for operator identification,
  because it would loop. We use a simproc instead. *}
ML {*
val map_apply_simproc = 
  Simplifier.simproc_global_i @{theory} "map_apply" [@{term "f x :: 'a option"}]
    (fn ctxt => fn redex => case redex of
      Const (@{const_name map_apply}, _) $ _ $ _ => NONE
    | f $ x => 
      let
        val thy = Proof_Context.theory_of ctxt;
        val cTr = 
          redex
          |> fastype_of
          |> dest_Type
          |> snd |> hd
          |> ctyp_of thy;
        val cTx = ctyp_of thy (fastype_of x);
        val cts = map (SOME o cterm_of thy) [f, x];
      in
        SOME (Drule.instantiate' [SOME cTr, SOME cTx] cts @{thm eq_map_apply})
      end
    | _ => NONE);
*}

lemma map_apply_parametric [transfer_rule]:
  "((A ===> B) ===> A ===> B) map_apply map_apply"
unfolding map_apply_def by(transfer_prover)

lemma map_apply_transfer [transfer_rule]:
  "(pcr_mapping A B ===> A ===> rel_option B) map_apply Mapping.lookup"
by(auto simp add: pcr_mapping_def cr_mapping_def Mapping.lookup_def map_apply_def dest: rel_funD)


definition map_update :: "'a \<Rightarrow> 'b option \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> 'b option)"
where "map_update x y f = f(x := y)"

lemma map_update_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(A ===> rel_option B ===> (A ===> rel_option B) ===> (A ===> rel_option B)) map_update map_update"
unfolding map_update_def[abs_def] by transfer_prover

context begin
local_setup {* Local_Theory.map_naming (Name_Space.mandatory_path "Mapping") *}

lift_definition update' :: "'a \<Rightarrow> 'b option \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping"
is map_update parametric map_update_parametric .

lemma update'_code [simp, code, code_unfold]:
  "update' x None = Mapping.delete x"
  "update' x (Some y) = Mapping.update x y"
by(transfer, simp add: map_update_def fun_eq_iff)+

end

declare map_update_def[abs_def, containers_post] map_update_def[symmetric, containers_pre]


definition map_is_empty :: "('a \<Rightarrow> 'b option) \<Rightarrow> bool"
where "map_is_empty m \<longleftrightarrow> m = Map.empty"

lemma map_is_empty_folds:
  "m = map_empty \<longleftrightarrow> map_is_empty m"
  "map_empty = m \<longleftrightarrow> map_is_empty m"
by(auto simp add: map_is_empty_def map_empty_def)

declare map_is_empty_folds[containers_pre]
  map_is_empty_def[abs_def, containers_post]

lemma map_is_empty_transfer [transfer_rule]:
  assumes "bi_total A"
  shows "(pcr_mapping A B ===> op =) map_is_empty Mapping.is_empty"
unfolding map_is_empty_def[abs_def] Mapping.is_empty_def[abs_def] dom_eq_empty_conv[symmetric]
by(rule rel_funI)+(auto simp del: dom_eq_empty_conv dest: rel_setD2 rel_setD1 Mapping.keys.transfer[THEN rel_funD, OF assms])

end

ML {*
signature CONTAINERS = sig
  val identify : Context.generic -> thm -> thm;
  val identify_attribute : attribute;
end

structure Containers: CONTAINERS =
struct

fun identify ctxt thm =
  let
    val ctxt' = Context.proof_of ctxt
    val ss = put_simpset HOL_basic_ss ctxt'
    val ctxt1 = ss addsimps Containers_Pre.get ctxt' addsimprocs [map_apply_simproc]
    val ctxt2 = ss addsimps Containers_Post.get ctxt'

    (* Hack to recover Transfer.transferred function from attribute *)
    fun transfer_transferred ctxt thm = Transfer.transferred_attribute [] (ctxt, thm) |> snd |> the
  in
    thm
    |> full_simplify ctxt1
    |> transfer_transferred ctxt
    |> full_simplify ctxt2
  end

val identify_attribute = Thm.rule_attribute identify

end
*}

attribute_setup "containers_identify" =
  {* Scan.succeed Containers.identify_attribute *}
  "Transfer theorems for operator identification in Containers"

hide_const (open) map_apply map_empty map_is_empty map_update
hide_fact (open) map_apply_def map_empty_def eq_map_apply

end