theory SINVAR_NonInterference
imports "../TopoS_Helper"
begin

subsection {* SecurityInvariant NonInterference *}

datatype_new node_config = Interfering | Unrelated

definition default_node_properties :: "node_config"
  where  "default_node_properties = Interfering"

definition undirected_reachable :: "'v graph \<Rightarrow> 'v => 'v set" where
  "undirected_reachable G v = (succ_tran (undirected G) v) - {v}"


lemma undirected_reachable_mono:
  "E' \<subseteq> E \<Longrightarrow> undirected_reachable \<lparr>nodes = N, edges = E'\<rparr> n \<subseteq> undirected_reachable \<lparr>nodes = N, edges = E\<rparr> n"
unfolding undirected_reachable_def undirected_def succ_tran_def
by (fastforce intro: trancl_mono)

fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> n \<in> (nodes G). (nP n) = Interfering \<longrightarrow> (nP ` (undirected_reachable G n)) \<subseteq> {Unrelated})"

fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> 'b \<Rightarrow> bool" where
  "verify_globals _ _ _ = True"

definition receiver_violation :: "bool" where 
  "receiver_violation = True"


text{*simplifications for sets we need in the uniqueness proof*}
  lemma tmp1: "{(b, a). a = vertex_1 \<and> b = vertex_2} = {(vertex_2, vertex_1)}" by auto
  lemma tmp6: "{(vertex_1, vertex_2), (vertex_2, vertex_1)}\<^sup>+ = 
    {(vertex_1, vertex_1), (vertex_2, vertex_2), (vertex_1, vertex_2), (vertex_2, vertex_1)}"
    apply(rule)
     apply(rule)
     apply(case_tac x, simp)
     apply(erule_tac r="{(vertex_1, vertex_2), (vertex_2, vertex_1)}" in trancl_induct)
      apply(auto)
     apply (metis (mono_tags) insertCI r_r_into_trancl)+
  done
  lemma tmp2: "(insert (vertex_1, vertex_2) {(b, a). a = vertex_1 \<and> b = vertex_2})\<^sup>+ = 
    {(vertex_1, vertex_1), (vertex_2, vertex_2), (vertex_1, vertex_2), (vertex_2, vertex_1)}"
    apply(subst tmp1)
    apply(fact tmp6)
    done
  lemma tmp3: "{(b, a). False} = {}" by simp
  lemma tmp4: "{(e1, e2). e1 = vertex_1 \<and> e2 = vertex_2 \<and> (e1 = vertex_1 \<longrightarrow> e2 \<noteq> vertex_2)} = {}" by blast
  lemma tmp5: "{(b, a). a = vertex_1 \<and> b = vertex_2 \<or> a = vertex_1 \<and> b = vertex_2 \<and> (a = vertex_1 \<longrightarrow> b \<noteq> vertex_2)} = 
    {(vertex_2, vertex_1)}" by fastforce
  lemma unique_default_example: "undirected_reachable \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> vertex_1 = {vertex_2}"
    by(auto simp add: undirected_def undirected_reachable_def succ_tran_def tmp2)
  lemma unique_default_example_hlp1: "delete_edges \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> {(vertex_1, vertex_2)} = 
    \<lparr>nodes = {vertex_1, vertex_2}, edges = {}\<rparr>"
    by(simp add: delete_edges_def)
  lemma unique_default_example_2: 
    "undirected_reachable (delete_edges \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> {(vertex_1,vertex_2 )}) vertex_1 = {}"
    apply(simp add: undirected_def undirected_reachable_def succ_tran_def unique_default_example_hlp1)
    apply(subst tmp3)
    by auto
  lemma unique_default_example_3: 
    "undirected_reachable (delete_edges \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> {(vertex_1,vertex_2 )}) vertex_2 = {}"
    apply(simp add: undirected_def undirected_reachable_def succ_tran_def unique_default_example_hlp1)
    apply(subst tmp3)
    by auto
  lemma unique_default_example_4: 
    "(undirected_reachable (add_edge vertex_1 vertex_2 (delete_edges \<lparr>nodes = {vertex_1, vertex_2}, 
    edges = {(vertex_1, vertex_2)}\<rparr> {(vertex_1, vertex_2)})) vertex_1) = {vertex_2}"
    apply(simp add: delete_edges_def add_edge_def undirected_def undirected_reachable_def succ_tran_def)
    apply(subst tmp4)
    apply(subst tmp5)
    apply(simp)
    apply(subst tmp6)
    by force
  lemma unique_default_example_5: 
    "(undirected_reachable (add_edge vertex_1 vertex_2 (delete_edges \<lparr>nodes = {vertex_1, vertex_2}, 
    edges = {(vertex_1, vertex_2)}\<rparr> {(vertex_1, vertex_2)})) vertex_2) = {vertex_1}"
    apply(simp add: delete_edges_def add_edge_def undirected_def undirected_reachable_def succ_tran_def)
    apply(subst tmp4)
    apply(subst tmp5)
    apply(simp)
    apply(subst tmp6)
    by force


  (*lemma empty_undirected_reachable_false: "xb \<in> undirected_reachable \<lparr>nodes = nodes G, edges = {(e1, e2). False}\<rparr> na \<longleftrightarrow> False"
    apply(simp add: undirected_reachable_def succ_tran_def undirected_def)
    apply(subst tmp3)
    by fastforce*)

  lemma empty_undirected_reachable_false: "xb \<in> undirected_reachable (delete_edges G (edges G)) na \<longleftrightarrow> False"
    apply(simp add: undirected_reachable_def succ_tran_def undirected_def delete_edges_edges_empty)
    apply(subst tmp3)
    by fastforce

subsubsection{*monotonic and preliminaries*}
  lemma sinvar_mono: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
  unfolding SecurityInvariant_withOffendingFlows.sinvar_mono_def
    apply(clarsimp)
    apply(rename_tac nP N E' n E xa)
    apply(erule_tac x=n in ballE)
     prefer 2
     apply simp
    apply(simp)
    apply(drule_tac N=N and n=n in undirected_reachable_mono)
    apply(blast)
    done
    
  
  interpretation SecurityInvariant_preliminaries
  where sinvar = sinvar
  and verify_globals = verify_globals
    apply unfold_locales
      apply(frule_tac finite_distinct_list[OF valid_graph.finiteE])
      apply(erule_tac exE)
      apply(rename_tac list_edges)
      apply(rule_tac ff="list_edges" in SecurityInvariant_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF sinvar_mono])
          apply(auto)[4]
      apply(auto simp add: SecurityInvariant_withOffendingFlows.is_offending_flows_def empty_undirected_reachable_false)[1]
     apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_sinvar_mono[OF sinvar_mono])
    apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_mono])
  done


interpretation NonInterference: SecurityInvariant_IFS
where default_node_properties = SINVAR_NonInterference.default_node_properties
and sinvar = SINVAR_NonInterference.sinvar
and verify_globals = verify_globals
  unfolding SINVAR_NonInterference.default_node_properties_def
  apply unfold_locales
   apply(rule ballI)
   apply(drule SINVAR_NonInterference.offending_notevalD)
   apply(simp)
   apply clarify
   apply(rename_tac xa)
   apply(case_tac "nP xa")
    (*case Interfering*)
    apply simp
    apply(erule_tac x=n and A="nodes G" in ballE)
     prefer 2
     apply fast
    apply(simp)
    apply(thin_tac "valid_graph G")
    apply(thin_tac "(a,b) \<in> f")
    apply(thin_tac "n \<in> nodes G")
    apply(thin_tac "nP n = Interfering")
    apply(erule disjE)
     apply (metis fun_upd_other fun_upd_same imageI node_config.distinct(1) set_rev_mp singleton_iff)
    apply (metis fun_upd_other fun_upd_same imageI node_config.distinct(1) set_rev_mp singleton_iff)
   (*case Unrelated*)
   apply simp
  (*unique: *)
  apply(erule default_uniqueness_by_counterexample_IFS)
  apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
      SecurityInvariant_withOffendingFlows.is_offending_flows_def)
  apply (simp add:delete_edges_set_nodes)
  apply (simp split: split_split_asm split_split)
  apply(rule_tac x="\<lparr> nodes={vertex_1,vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
  apply(rule conjI)
   apply(simp add: valid_graph_def)
  apply(rule_tac x="(\<lambda> x. default_node_properties)(vertex_1 := Interfering, vertex_2 := Interfering)" in exI, simp)
  apply(rule conjI)
   apply(simp add: unique_default_example)
  apply(rule_tac x="vertex_2" in exI, simp)
  apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
  apply(simp add: unique_default_example)
  apply(simp add: unique_default_example_2)
  apply(simp add: unique_default_example_3)
  apply(simp add: unique_default_example_4)
  apply(simp add: unique_default_example_5)
  apply(case_tac otherbot)
   apply simp
  apply(simp add:graph_ops)
  done


  lemma TopoS_NonInterference: "SecurityInvariant sinvar default_node_properties receiver_violation"
  unfolding receiver_violation_def by unfold_locales
   

hide_const (open) sinvar verify_globals receiver_violation default_node_properties

--{*Hide all the helper lemmas.*}
hide_fact tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 unique_default_example 
          unique_default_example_2 unique_default_example_3 unique_default_example_4
          unique_default_example_5 empty_undirected_reachable_false

end
