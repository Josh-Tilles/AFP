theory SINVAR_NonInterference_impl
imports SINVAR_NonInterference "../TopoS_Interface_impl"
begin


code_identifier code_module SINVAR_NonInterference_impl => (Scala) SINVAR_NonInterference


subsubsection {* SecurityInvariant NonInterference List Implementation*}

definition undirected_reachable :: "'v list_graph \<Rightarrow> 'v => 'v list" where
  "undirected_reachable G v = removeAll v (succ_tran (undirected G) v)"

lemma undirected_reachable_set: "set (undirected_reachable G v) = {e2. (v,e2) \<in> (set (edgesL (undirected G)))\<^sup>+} - {v}"
  by(simp add: undirected_succ_tran_set undirected_nodes_set undirected_reachable_def)

fun sinvar_set :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "sinvar_set G nP = (\<forall> n \<in> set (nodesL G). (nP n) = Interfering \<longrightarrow> set (map nP (undirected_reachable G n)) \<subseteq> {Unrelated})"

(* equal: lemma sinvar_list_eq_set*)
fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> n \<in> set (nodesL G). (nP n) = Interfering \<longrightarrow> (let result = remdups (map nP (undirected_reachable G n)) in result = [] \<or> result = [Unrelated]))"

lemma "P = Q \<Longrightarrow> (\<forall> x. P x) = (\<forall> x. Q x)"
  by(erule arg_cong)


lemma sinvar_eq_help1: "nP ` set (undirected_reachable G n) = set (map nP (undirected_reachable G n))"
  by auto
lemma sinvar_eq_help2: "set l = {Unrelated} \<Longrightarrow> remdups l = [Unrelated]"
 apply(induction l)
  apply simp
 apply(simp)
  apply (metis empty_iff insertI1 set_empty2 subset_singletonD)
 done
lemma sinvar_eq_help3: "(let result = remdups (map nP (undirected_reachable G n)) in result = [] \<or> result = [Unrelated]) = (set (map nP (undirected_reachable G n)) \<subseteq> {Unrelated})"
  apply simp
  apply(rule iffI)
   apply(erule disjE)
    apply simp
   apply(simp only: set_map[symmetric]) 
   apply(subst set_remdups[symmetric])
   apply simp
  apply(case_tac " nP ` set (undirected_reachable G n) = {}")
   apply fast
  apply(case_tac " nP ` set (undirected_reachable G n) = {Unrelated}")
   defer
   apply(subgoal_tac "nP ` set (undirected_reachable G n) \<subseteq> {Unrelated} \<Longrightarrow>
    nP ` set (undirected_reachable G n) \<noteq> {} \<Longrightarrow>
    nP ` set (undirected_reachable G n) \<noteq> {Unrelated} \<Longrightarrow> False")
    apply fast
   apply (metis subset_singletonD)
  apply simp
  apply(rule disjI2)
  apply(simp only: sinvar_eq_help1)
  apply(simp add:sinvar_eq_help2)
  done

lemma sinvar_list_eq_set: "sinvar = sinvar_set"
  apply(insert sinvar_eq_help3)
  apply(simp add: fun_eq_iff)
  apply(rule allI)+
  apply fastforce
  done

fun verify_globals :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> unit \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"



value "sinvar 
    \<lparr> nodesL = [1::nat,2,3,4], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
    (\<lambda>e. SINVAR_NonInterference.default_node_properties)"
value "sinvar 
    \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4)] \<rparr>
    ((\<lambda>e. SINVAR_NonInterference.default_node_properties)(1:= Interfering, 2:= Unrelated, 3:= Unrelated, 4:= Unrelated))"
value "sinvar 
    \<lparr> nodesL = [1::nat,2,3,4,5, 8,9,10], edgesL = [(1,2), (2,3), (3,4), (5,4), (8,9),(9,8)] \<rparr>
    ((\<lambda>e. SINVAR_NonInterference.default_node_properties)(1:= Interfering, 2:= Unrelated, 3:= Unrelated, 4:= Unrelated))"
value "sinvar 
    \<lparr> nodesL = [1::nat], edgesL = [(1,1)] \<rparr>
    ((\<lambda>e. SINVAR_NonInterference.default_node_properties)(1:= Interfering))"

value "(undirected_reachable \<lparr> nodesL = [1::nat], edgesL = [(1,1)] \<rparr> 1) = []" 
  (* apply(simp add: removeAll_def remdups_def undirected_reachable_def succ_tran_def trancl_list_impl_def trancl_impl_def) *)





definition NonInterference_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> ('v \<times> 'v) list list" where
  "NonInterference_offending_list = Generic_offending_list sinvar"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_NonInterference.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_NonInterference.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "NonInterference_eval G P = (valid_list_graph G \<and> 
  verify_globals G (SecurityInvariant.node_props SINVAR_NonInterference.default_node_properties P) (model_global_properties P) \<and> 
  sinvar G (SecurityInvariant.node_props SINVAR_NonInterference.default_node_properties P))"



lemma sinvar_correct: "valid_list_graph G \<Longrightarrow> SINVAR_NonInterference.sinvar (list_graph_to_graph G) nP = sinvar G nP"
   apply(simp add: sinvar_list_eq_set)
   apply(rule all_nodes_list_I)
   apply(simp add: fun_eq_iff)
   apply(clarify)
   apply(rename_tac x)
   proof -
    fix x :: 'a
    have f1: "\<And>e_x1 e_x2. - insert (e_x1\<Colon>'a) (List.coset e_x2) = set e_x2 - {e_x1}"
      by (metis compl_coset insert_code(2) set_removeAll)
    hence f2: "\<And>e_x1 e_x e_x2. e_x1 ` (- insert (e_x\<Colon>'a) (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected e_x2) e_x))) = set (map e_x1 (removeAll e_x (FiniteListGraph.succ_tran (FiniteListGraph.undirected e_x2) e_x))\<Colon>node_config list)"
      by (metis SINVAR_NonInterference_impl.undirected_reachable_def sinvar_eq_help1 set_removeAll)
    have f3: "\<And>e_x2 e_x1. - insert (e_x2\<Colon>'a) (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected e_x1) e_x2)) = SINVAR_NonInterference.undirected_reachable (list_graph_to_graph e_x1) e_x2"
      using f1 by (metis SINVAR_NonInterference.undirected_reachable_def succ_tran_correct undirected_correct)
    have "\<not> nP ` (- insert x (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected G) x))) \<subseteq> {Unrelated} \<and> \<not> nP ` (- insert x (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected G) x))) \<subseteq> {Unrelated} \<or> nP ` (- insert x (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected G) x))) \<subseteq> {Unrelated} \<and> nP ` (- insert x (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected G) x))) \<subseteq> {Unrelated}"
      by metis
    moreover
    { assume "nP ` (- insert x (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected G) x))) \<subseteq> {Unrelated} \<and> nP ` (- insert x (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected G) x))) \<subseteq> {Unrelated}"
      hence "(nP x = Interfering \<longrightarrow> nP ` SINVAR_NonInterference.undirected_reachable (list_graph_to_graph G) x \<subseteq> {Unrelated}) = (nP x = Interfering \<longrightarrow> nP ` set (SINVAR_NonInterference_impl.undirected_reachable G x) \<subseteq> {Unrelated})"
        using f2 f3 by (metis SINVAR_NonInterference_impl.undirected_reachable_def image_set) }
    moreover
    { assume "\<not> nP ` (- insert x (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected G) x))) \<subseteq> {Unrelated} \<and> \<not> nP ` (- insert x (List.coset (FiniteListGraph.succ_tran (FiniteListGraph.undirected G) x))) \<subseteq> {Unrelated}"
      hence "(nP x = Interfering \<longrightarrow> nP ` SINVAR_NonInterference.undirected_reachable (list_graph_to_graph G) x \<subseteq> {Unrelated}) = (nP x = Interfering \<longrightarrow> nP ` set (SINVAR_NonInterference_impl.undirected_reachable G x) \<subseteq> {Unrelated})"
        using f2 f3 by (metis SINVAR_NonInterference_impl.undirected_reachable_def image_set) }
    ultimately show "(nP x = Interfering \<longrightarrow> nP ` SINVAR_NonInterference.undirected_reachable (list_graph_to_graph G) x \<subseteq> {Unrelated}) = (nP x = Interfering \<longrightarrow> nP ` set (SINVAR_NonInterference_impl.undirected_reachable G x) \<subseteq> {Unrelated})"
      by metis
  qed



interpretation NonInterference_impl:TopoS_List_Impl 
  where default_node_properties=SINVAR_NonInterference.default_node_properties
  and sinvar_spec=SINVAR_NonInterference.sinvar
  and sinvar_impl=sinvar
  and verify_globals_spec=SINVAR_NonInterference.verify_globals
  and verify_globals_impl=verify_globals
  and receiver_violation=SINVAR_NonInterference.receiver_violation
  and offending_flows_impl=NonInterference_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=NonInterference_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(rule conjI)
   apply(simp add: TopoS_NonInterference)
  apply(rule conjI)
   apply(intro allI impI)
   apply(fact sinvar_correct)
  apply(simp)
 apply(rule conjI)
  apply(unfold NonInterference_offending_list_def)
  apply(intro allI impI)
  apply(rule Generic_offending_list_correct)
   apply(assumption)
  apply(simp only: sinvar_correct)
 apply(rule conjI)
  apply(intro allI)
  apply(simp only: NetModel_node_props_def)
  apply(metis NonInterference.node_props.simps NonInterference.node_props_eq_node_props_formaldef)
 apply(simp only: NonInterference_eval_def)
 apply(intro allI impI)
 apply(rule TopoS_eval_impl_proofrule[OF TopoS_NonInterference])
  apply(simp only: sinvar_correct)
 apply(simp)
done

subsubsection {* NonInterference packing *}
  definition SINVAR_LIB_NonInterference :: "('v::vertex, node_config, unit) TopoS_packed" where
    "SINVAR_LIB_NonInterference \<equiv> 
    \<lparr> nm_name = ''NonInterference'', 
      nm_receiver_violation = SINVAR_NonInterference.receiver_violation,
      nm_default = SINVAR_NonInterference.default_node_properties, 
      nm_sinvar = sinvar,
      nm_verify_globals = verify_globals,
      nm_offending_flows = NonInterference_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = NonInterference_eval
      \<rparr>"
  interpretation SINVAR_LIB_NonInterference_interpretation: TopoS_modelLibrary SINVAR_LIB_NonInterference
      SINVAR_NonInterference.sinvar SINVAR_NonInterference.verify_globals
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_NonInterference_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)




text {*Example: *}

  definition "example_graph  = \<lparr> nodesL = [1::nat,2,3,4,5, 8,9,10], edgesL = [(1,2), (2,3), (3,4), (5,4), (8,9),(9,8)] \<rparr>"
  definition"example_conf = ((\<lambda>e. SINVAR_NonInterference.default_node_properties)(1:= Interfering, 2:= Unrelated, 3:= Unrelated, 4:= Unrelated, 8:= Unrelated, 9:= Unrelated))"
  
  value "sinvar example_graph example_conf"
  value "NonInterference_offending_list example_graph example_conf"



hide_const (open) NetModel_node_props
hide_const (open) sinvar verify_globals

end
