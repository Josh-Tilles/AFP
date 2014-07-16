theory FiniteGraph
imports Main 
begin

(*Lots of this theory is based on a work by Benedikt Nordhoff and Peter Lammich*)

section {*Specification of a finite directed graph*}

text{* A graph G=(V,E) consits of a set of vertices V, also called nodes, 
       and a set of edges E. The edges are tuples of vertices. Both, 
       the set of vertices and edges is finite. *}

(* Inspired by
Title: 	Dijkstra's Shortest Path Algorithm
Author: 	Benedikt Nordhoff and Peter Lammich
http://afp.sourceforge.net/entries/Dijkstra_Shortest_Path.shtml
*)

section {* Definitions *}
  text {* A graph is represented by a record. *}
  record 'v graph =
    nodes :: "'v set"
    edges :: "('v \<times>'v) set"

  text {* In a valid graph, edges only go from nodes to nodes. *}
  locale valid_graph = 
    fixes G :: "'v graph"
    -- "Edges only refernce to existing nodes"
    assumes E_valid: "fst ` (edges G) \<subseteq> (nodes G)"
                     "snd ` (edges G) \<subseteq> (nodes G)"
    and finiteE: "finite (edges G)" (*implied by finiteV*)
    and finiteV: "finite (nodes G)"
  begin
    abbreviation "V \<equiv> (nodes G)"
    abbreviation "E \<equiv> (edges G)"

    lemma E_validD: assumes "(v,v') \<in> E"
      shows "v \<in> V" "v' \<in> V"
      apply -
       apply (rule set_mp[OF E_valid(1)])
       using assms apply force
      apply (rule set_mp[OF E_valid(2)])
      using assms apply force
      done

    lemma E_validD2: "\<forall>e \<in> E. fst e \<in> V \<and> snd e \<in> V"
    by (auto simp add: E_validD)
  end

subsection {* Basic operations on Graphs *}

 
  text {* The empty graph. *}
  definition empty where 
    "empty \<equiv> \<lparr> nodes = {}, edges = {} \<rparr>"

  text {* Adds a node to a graph. *}
  definition add_node :: "'v \<Rightarrow> 'v graph \<Rightarrow> 'v graph" where 
    "add_node v G \<equiv> \<lparr> nodes = ({v} \<union> (nodes G)), edges=edges G \<rparr>"

  text {* Deletes a node from a graph. Also deletes all adjacent edges. *}
  definition delete_node where "delete_node v G \<equiv> \<lparr> 
    nodes = (nodes G) - {v},   
    edges = {(e1, e2). (e1, e2) \<in> edges G \<and> e1 \<noteq> v \<and> e2 \<noteq> v}
    \<rparr>"

  text {* Adds an edge to a graph. *}
  definition add_edge where 
  "add_edge v v' G = \<lparr>nodes = nodes G \<union> {v,v'}, edges = {(v, v')} \<union> edges G \<rparr>"


  text {* Deletes an edge from a graph. *}
  definition delete_edge where "delete_edge v v' G \<equiv> \<lparr>nodes = nodes G, 
    edges = {(e1,e2). (e1, e2) \<in> edges G \<and> (e1,e2) \<noteq> (v,v')} \<rparr>"
  
  definition delete_edges::"'v graph \<Rightarrow> ('v \<times> 'v) set \<Rightarrow> 'v graph" where 
    "delete_edges G es = \<lparr>nodes = nodes G, 
    edges = {(e1,e2). (e1, e2) \<in> edges G \<and> (e1,e2) \<notin> es} \<rparr>"

  fun delete_edges_list::"'v graph \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 'v graph" where 
    "delete_edges_list G [] = G"|
    "delete_edges_list G ((v,v')#es) = delete_edges_list (delete_edge v v' G) es"


  definition fully_connected :: "'v graph \<Rightarrow> 'v graph" where
    "fully_connected G \<equiv> \<lparr>nodes = nodes G, edges = nodes G \<times> nodes G \<rparr>"


text {* extended graph operations *}
  text {* Reflexive transitive successors of a node. Or: All reachable nodes for v including v. *}
  definition succ_rtran :: "'v graph \<Rightarrow> 'v \<Rightarrow> 'v set" where
    "succ_rtran G v = {e2. (v,e2) \<in> (edges G)\<^sup>*}"

  text {* Transitive successors of a node. Or: All reachable nodes for v. *}
  definition succ_tran :: "'v graph \<Rightarrow> 'v \<Rightarrow> 'v set" where
    "succ_tran G v = {e2. (v,e2) \<in> (edges G)\<^sup>+}"

  --"succ_tran is always finite"
  lemma succ_tran_finite: "valid_graph G \<Longrightarrow> finite (succ_tran G v)"
  proof -
    assume "valid_graph G"
    from valid_graph.finiteE[OF this] have "finite ((edges G)\<^sup>+)" using finite_trancl[symmetric, of "edges G"] by metis
    from this have "finite {(e1,e2). (e1, e2) \<in> (edges G)\<^sup>+}" by simp
    from this have finite: "finite (snd ` {(e1,e2). (e1, e2) \<in> (edges G)\<^sup>+})" by (metis finite_imageI)
    have "{(e1,e2). (e1, e2) \<in> (edges G)\<^sup>+ \<and> e1 = v} \<subseteq> {(e1,e2). (e1, e2) \<in> (edges G)\<^sup>+}" by blast
    have 1: "snd ` {(e1,e2). (e1, e2) \<in> (edges G)\<^sup>+ \<and> e1 = v} \<subseteq> snd ` {(e1,e2). (e1, e2) \<in> (edges G)\<^sup>+}" by blast
    have 2: "snd ` {(e1,e2). (e1, e2) \<in> (edges G)\<^sup>+ \<and> e1 = v} = {e2. (v,e2) \<in> (edges G)\<^sup>+}" by force
    from 1 2 have "{e2. (v,e2) \<in> (edges G)\<^sup>+} \<subseteq> snd ` {(e1,e2). (e1, e2) \<in> (edges G)\<^sup>+}" by blast
    from this finite have "finite {e2. (v, e2) \<in> (edges G)\<^sup>+}" by (metis finite_subset)
    thus "finite (succ_tran G v)" using succ_tran_def by metis
  qed
  
  text{* If there is no edge leaving from v, then v has no successors *}
  lemma succ_tran_empty: "\<lbrakk> valid_graph G; v \<notin> (fst ` edges G) \<rbrakk> \<Longrightarrow> succ_tran G v = {}"
  by (metis (lifting) Collect_empty_eq Domain.DomainI converse_tranclE fst_eq_Domain succ_tran_def)

  text{* succ_tran is subset of nodes *}
  lemma succ_tran_subseteq_nodes: "\<lbrakk> valid_graph G \<rbrakk> \<Longrightarrow> succ_tran G v \<subseteq> nodes G"
    apply(simp add: succ_tran_def)
    by (metis (lifting) mem_Collect_eq subsetI trancl.cases valid_graph.E_validD(2))


  text {* The number of reachable nodes from v *}
  definition num_reachable :: "'v graph \<Rightarrow> 'v \<Rightarrow> nat" where
    "num_reachable G v = card (succ_tran G v)"

  definition num_reachable_norefl :: "'v graph \<Rightarrow> 'v \<Rightarrow> nat" where
    "num_reachable_norefl G v = card (succ_tran G v - {v})"

  text{*card returns 0 for infinite sets. Here, for a valid graph, if num_reachable is zero,
        there are actually no nodes reachable.*}
  lemma num_reachable_zero: "\<lbrakk>valid_graph G; num_reachable G v = 0\<rbrakk> \<Longrightarrow> succ_tran G v = {}"
  apply(unfold num_reachable_def)
  apply(case_tac "finite (succ_tran G v)")
   apply(simp)
  apply(blast intro: succ_tran_finite)
  done
  lemma num_succtran_zero: "\<lbrakk>succ_tran G v = {}\<rbrakk> \<Longrightarrow> num_reachable G v = 0"
  by(unfold num_reachable_def, simp)
  lemma num_reachable_zero_iff: "\<lbrakk>valid_graph G\<rbrakk> \<Longrightarrow> (num_reachable G v = 0) <-> (succ_tran G v = {})"
  by(metis num_succtran_zero num_reachable_zero)


section{*Undirected Graph*}

subsection{*undirected graph simulation*}
  text {* Create undirected graph from directed graph by adding backward links *}

  definition backflows :: "('v \<times> 'v) set \<Rightarrow> ('v \<times> 'v) set" where
    "backflows E \<equiv> {(r,s). (s,r) \<in> E}"

  definition undirected :: "'v graph \<Rightarrow> 'v graph"
    where "undirected G = \<lparr> nodes = nodes G, edges = (edges G) \<union> {(b,a). (a,b) \<in> edges G} \<rparr>"

section {*Lemmata*}

  lemma graph_eq_intro: "(nodes (G::'a graph) = nodes G') \<Longrightarrow> (edges G = edges G') \<Longrightarrow> G = G'"
  by simp

  -- "finite"
  lemma valid_graph_finite_filterE: "valid_graph G \<Longrightarrow> finite {(e1, e2). (e1, e2) \<in> edges G \<and> P e1 e2}"
  by(simp add: valid_graph.finiteE split_def)
  lemma valid_graph_finite_filterV: "valid_graph G \<Longrightarrow> finite {n. n \<in> nodes G \<and> P n}"
  by(simp add: valid_graph.finiteV)

  -- "empty"
  lemma empty_valid[simp]: "valid_graph empty"
    unfolding empty_def by unfold_locales auto
  lemma nodes_empty[simp]: "nodes empty = {}" unfolding empty_def by simp
  lemma edges_empty[simp]: "edges empty = {}" unfolding empty_def by simp

  -- "add node"
  lemma add_node_valid[simp]:
    "valid_graph g \<Longrightarrow> valid_graph (add_node v g)"
      unfolding add_node_def
      unfolding valid_graph_def
      by (auto)

  lemma delete_node_valid[simp]:
  "valid_graph G \<Longrightarrow> valid_graph (delete_node v G)"
  by(auto simp add: delete_node_def valid_graph_def valid_graph_finite_filterE)

  -- "add edgde"
  lemma add_edge_valid[simp]: "valid_graph G \<Longrightarrow> valid_graph (add_edge v v' G)"
  by(auto simp add: add_edge_def add_node_def valid_graph_def)

  -- "delete edge"
  lemma delete_edge_valid[simp]: "valid_graph G \<Longrightarrow> valid_graph (delete_edge v v' G)"
  by(auto simp add: delete_edge_def add_node_def valid_graph_def split_def)
 
  -- "delte edges"
  lemma delete_edges_list_valid[simp]: "valid_graph G \<Longrightarrow> valid_graph (delete_edges_list G E)"
    by(induction E arbitrary: G, simp, force)
  lemma delete_edges_valid[simp]: "valid_graph G \<Longrightarrow> valid_graph (delete_edges G E)"
  by(auto simp add: delete_edges_def add_node_def valid_graph_def split_def)
  lemma delete_edges_list_set: "delete_edges_list G E = delete_edges G (set E)"
    apply(induction E arbitrary: G)
     apply(simp_all add: delete_edges_def)
    apply(clarify)
    by(simp add: delete_edge_def)
  lemma delete_edges_list_union: "delete_edges_list G (ff @ keeps) = delete_edges G (set ff \<union> set keeps)"
   by(simp add: delete_edges_list_set)
  lemma add_edge_delete_edges_list: 
    "(add_edge (fst a) (snd a) (delete_edges_list G (a # ff))) = (add_edge (fst a) (snd a) (delete_edges G (set ff)))"
   by(auto simp add: delete_edges_list_set delete_edges_def add_edge_def add_node_def)
  lemma delete_edges_empty[simp]: "delete_edges G {} = G"
   by(simp add: delete_edges_def)
  lemma delete_edges_simp2: "delete_edges G E = \<lparr> nodes = nodes G, edges = edges G - E\<rparr>"
   by(auto simp add: delete_edges_def)
  lemma delete_edges_set_nodes: "nodes (delete_edges G E) = nodes G"
   by(simp add: delete_edges_simp2)
  lemma delete_edges_edges_mono: "E' \<subseteq> E \<Longrightarrow> edges (delete_edges G E) \<subseteq> edges (delete_edges G E')"
    by(simp add: delete_edges_def, fast)
  lemma delete_edges_edges_empty: "(delete_edges G (edges G)) = G\<lparr>edges := {}\<rparr>"
    by(simp add: delete_edges_simp2)

 --"add delete"
  lemma add_delete_edge: "valid_graph (G::'a graph) \<Longrightarrow> (a,b) \<in> edges G \<Longrightarrow> 
  add_edge a b (delete_edge a b G) = G"
   apply(simp add: delete_edge_def add_edge_def valid_graph_def)
   apply(clarify)
   apply(rule graph_eq_intro)
    by (auto)

  lemma add_delete_edges: "valid_graph (G::'v graph) \<Longrightarrow> (a,b) \<in> edges G \<Longrightarrow> (a,b) \<notin> fs \<Longrightarrow>
  add_edge a b (delete_edges G (insert (a, b) fs)) = (delete_edges G fs)"
  apply(simp add: delete_edges_simp2 add_edge_def valid_graph_def)
  apply(clarify)
  apply(auto)
  done

 --"fully_connected"
  lemma fully_connected_simp: "fully_connected \<lparr>nodes = N, edges = ignore \<rparr>\<equiv> \<lparr>nodes = N, edges = N \<times> N \<rparr>"
    by(simp add: fully_connected_def)
  lemma fully_connected_valid: "valid_graph G \<Longrightarrow> valid_graph (fully_connected G)"
    by(simp add: fully_connected_def valid_graph_def)

 --"succ_tran"
 lemma succ_tran_mono: 
  "valid_graph \<lparr>nodes=N, edges=E\<rparr> \<Longrightarrow> E' \<subseteq> E \<Longrightarrow> succ_tran \<lparr>nodes=N, edges=E'\<rparr> v \<subseteq> succ_tran \<lparr>nodes=N, edges=E\<rparr> v"
   apply(drule valid_graph.finiteE)
   apply(frule_tac A="E'" in rev_finite_subset, simp)
   apply(simp add: num_reachable_def)
   apply(simp add: succ_tran_def)
   apply(metis (lifting, full_types) Collect_mono trancl_mono)
  done

  --"num_reachable"
  lemma num_reachable_mono:
  "valid_graph \<lparr>nodes=N, edges=E\<rparr> \<Longrightarrow> E' \<subseteq> E \<Longrightarrow> num_reachable \<lparr>nodes=N, edges=E'\<rparr> v \<le> num_reachable \<lparr>nodes=N, edges=E\<rparr> v"
   apply(simp add: num_reachable_def)
   apply(frule_tac E'="E'" and v="v" in succ_tran_mono, simp)
   apply(frule_tac v="v" in succ_tran_finite)
   apply(simp add: card_mono)
  done

  --"num_reachable_norefl"
  lemma num_reachable_norefl_mono:
  "valid_graph \<lparr>nodes=N, edges=E\<rparr> \<Longrightarrow> E' \<subseteq> E \<Longrightarrow> num_reachable_norefl \<lparr>nodes=N, edges=E'\<rparr> v \<le> num_reachable_norefl \<lparr>nodes=N, edges=E\<rparr> v"
   apply(simp add: num_reachable_norefl_def)
   apply(frule_tac E'="E'" and v="v" in succ_tran_mono, simp)
   apply(frule_tac v="v" in succ_tran_finite)
   using card_mono by (metis Diff_mono finite_Diff subset_refl)

  --"backflows"
  lemma backflows_valid: 
    "valid_graph \<lparr>nodes=N, edges=E\<rparr> \<Longrightarrow> valid_graph \<lparr>nodes=N, edges=backflows E\<rparr>"
    using [[simproc add: finite_Collect]] by(auto simp add: valid_graph_def backflows_def)
  lemma undirected_backflows: 
    "undirected G = \<lparr> nodes = nodes G, edges = (edges G) \<union> backflows (edges G) \<rparr>"
    by(simp add: backflows_def undirected_def)
  lemma backflows_id: 
    "backflows (backflows E) = E"
    by(simp add: backflows_def)
  lemma backflows_finite: "finite E \<Longrightarrow> finite (backflows E)"
    using [[simproc add: finite_Collect]] by(simp add: backflows_def) 
  lemma backflows_minus_backflows: "backflows (X - backflows Y) = (backflows X) - Y"
    by(auto simp add: backflows_def)
  lemma backflows_subseteq: "X \<subseteq> Y <-> backflows X \<subseteq> backflows Y"
    by(auto simp add: backflows_def)
  lemma backflows_un: "backflows (A \<union> B) = (backflows A) \<union> (backflows B)"
    by(auto simp add: backflows_def)
  lemma backflows_inter: "backflows (A \<inter> B) = (backflows A) \<inter> (backflows B)"
    by(auto simp add: backflows_def)
  lemma backflows_alt_fstsnd: "backflows E = (\<lambda>e. (snd e, fst e)) ` E"
    by(auto simp add: backflows_def, force)






lemmas graph_ops=add_node_def delete_node_def add_edge_def delete_edge_def delete_edges_simp2


  --"valid_graph"
  lemma valid_graph_remove_edges: "valid_graph \<lparr> nodes = V, edges = E \<rparr> \<Longrightarrow> valid_graph \<lparr> nodes = V, edges=E - X\<rparr>"
    by (metis delete_edges_simp2 delete_edges_valid select_convs(1) select_convs(2))

  lemma valid_graph_remove_edges_union: 
    "valid_graph \<lparr> nodes = V, edges = E \<union> E' \<rparr> \<Longrightarrow> valid_graph \<lparr> nodes = V, edges=E\<rparr>"
    by(auto simp add: valid_graph_def)

  lemma valid_graph_union_edges: "\<lbrakk> valid_graph \<lparr> nodes = V, edges = E \<rparr>; valid_graph \<lparr> nodes = V, edges=E'\<rparr> \<rbrakk> \<Longrightarrow>
     valid_graph \<lparr> nodes = V, edges=E \<union> E'\<rparr>"
    by(auto simp add: valid_graph_def)

  lemma valid_graph_add_subset_edges: "\<lbrakk> valid_graph \<lparr> nodes = V, edges = E \<rparr>; E' \<subseteq> E \<rbrakk> \<Longrightarrow>
     valid_graph \<lparr> nodes = V, edges= E \<union> E'\<rparr>"
    by(auto simp add: valid_graph_def) (metis rev_finite_subset)





(*Inspired by 
Benedikt Nordhoff and Peter Lammich
Dijkstra's Shortest Path Algorithm
http://afp.sourceforge.net/entries/Dijkstra_Shortest_Path.shtml*)
(*more a literal copy of http://afp.sourceforge.net/browser_info/current/AFP/Dijkstra_Shortest_Path/Graph.html*)

  text {* Successors of a node. *}
  definition succ :: "'v graph \<Rightarrow> 'v \<Rightarrow> 'v set"
    where "succ G v \<equiv> {v'. (v,v')\<in>edges G}"


  lemma succ_finite[simp, intro]: "finite (edges G) \<Longrightarrow> finite (succ G v)"
    unfolding succ_def
    by (rule finite_subset[where B="snd`edges G"]) force+

  lemma succ_empty: "succ empty v = {}" unfolding empty_def succ_def by auto

  lemma (in valid_graph) succ_subset: "succ G v \<subseteq> V"
    unfolding succ_def using E_valid
    by (force)


end

