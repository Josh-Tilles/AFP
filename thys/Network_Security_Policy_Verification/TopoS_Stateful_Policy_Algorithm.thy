theory TopoS_Stateful_Policy_Algorithm
imports TopoS_Stateful_Policy TopoS_Composition_Theory
begin

section{*Stateful Policy -- Algorithm*}

subsection{* Some unimportant lemmata *}
  lemma False_set: "{(r, s). False} = {}" by simp
  lemma valid_reqs_ACS_D: "valid_reqs M \<Longrightarrow> valid_reqs (get_ACS M)"
    by(simp add: valid_reqs_def get_ACS_def)
  lemma valid_reqs_IFS_D: "valid_reqs M \<Longrightarrow> valid_reqs (get_IFS M)"
    by(simp add: valid_reqs_def get_IFS_def)
  lemma all_security_requirements_fulfilled_ACS_D: "all_security_requirements_fulfilled M G \<Longrightarrow>
    all_security_requirements_fulfilled (get_ACS M) G"
    by(simp add: all_security_requirements_fulfilled_def get_ACS_def)
  lemma all_security_requirements_fulfilled_IFS_D: "all_security_requirements_fulfilled M G \<Longrightarrow>
    all_security_requirements_fulfilled (get_IFS M) G"
    by(simp add: all_security_requirements_fulfilled_def get_IFS_def)
  lemma all_security_requirements_fulfilled_mono_stateful_policy_to_network_graph:
      "\<lbrakk> valid_reqs M; E' \<subseteq> E; valid_graph \<lparr> nodes = V, edges = Efix \<union> E \<rparr> \<rbrakk> \<Longrightarrow>  
        all_security_requirements_fulfilled M 
          (stateful_policy_to_network_graph \<lparr> hosts = V, flows_fix = Efix, flows_state = E \<rparr>)\<Longrightarrow>
        all_security_requirements_fulfilled M 
          (stateful_policy_to_network_graph \<lparr> hosts = V, flows_fix = Efix, flows_state = E' \<rparr>)"
    apply(simp add: stateful_policy_to_network_graph_def all_flows_def)
    apply(drule all_security_requirements_fulfilled_mono[where E="Efix \<union> E \<union> backflows E" and E'="Efix \<union> E' \<union> backflows E'" and V="V"])
       apply(thin_tac "valid_graph ?G")
       apply(thin_tac "all_security_requirements_fulfilled ?M ?G")
       apply(simp add: backflows_def, blast)
      apply(thin_tac "all_security_requirements_fulfilled ?M ?G")
      apply(simp add: valid_graph_def)
      apply(simp add: backflows_def)
      apply(auto)[1]
     apply(simp_all)
   done


subsection {* Sketch for generating a stateful policy from a simple directed policy *}
  text{* Having no stateful flows, we trivially get a valid stateful policy. *}
    lemma trivial_stateful_policy_compliance:
    "\<lbrakk> valid_graph \<lparr> nodes = V, edges = E \<rparr>; valid_reqs M; all_security_requirements_fulfilled M \<lparr> nodes = V, edges = E \<rparr> \<rbrakk> \<Longrightarrow> 
      stateful_policy_compliance \<lparr> hosts = V, flows_fix = E, flows_state = {} \<rparr> \<lparr> nodes = V, edges = E \<rparr> M"
      apply(unfold_locales)
                   apply(simp_all add: valid_graph_def stateful_policy_to_network_graph_def all_flows_def backflows_def False_set)
       apply(simp add: get_IFS_def get_ACS_def all_security_requirements_fulfilled_def)
      apply(clarify)
      apply(drule valid_reqs_ACS_D) 
      apply(drule all_security_requirements_fulfilled_ACS_D)
      apply(drule(1) all_security_requirements_fulfilled_imp_get_offending_empty)
      by force


  text{*trying better*}

    text{*First, filtering flows that cause no IFS violations*}
    (*the edges front of the lsit are more likely to be kept*)
    fun filter_IFS_no_violations_accu :: "'v::vertex graph \<Rightarrow> 'v SecurityInvariant_configured list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<times> 'v) list" where
      "filter_IFS_no_violations_accu G M accu [] = accu" |
      "filter_IFS_no_violations_accu G M accu (e#Es) = (if
        all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<lparr> hosts = nodes G, flows_fix = edges G, flows_state = set (e#accu) \<rparr>)
        then filter_IFS_no_violations_accu G M (e#accu) Es
        else filter_IFS_no_violations_accu G M accu Es)"
    definition filter_IFS_no_violations :: "'v::vertex graph \<Rightarrow> 'v SecurityInvariant_configured list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<times> 'v) list" where
      "filter_IFS_no_violations G M Es = filter_IFS_no_violations_accu G M [] Es"


    lemma filter_IFS_no_violations_subseteq_input: "set (filter_IFS_no_violations G M Es) \<subseteq> set Es"
    apply(subgoal_tac "\<forall> accu. set (filter_IFS_no_violations_accu G M accu Es) \<subseteq> set Es \<union> set accu")
     apply(erule_tac x="[]" in allE)
     apply(simp add: filter_IFS_no_violations_def)
    unfolding filter_IFS_no_violations_def
    apply(induct_tac Es)
     apply(simp_all)
    apply(metis List.set.simps(2) Un_insert_right subset_insertI2)
    done
    lemma filter_IFS_no_violations_accu_correct_induction: "valid_reqs (get_IFS M) \<Longrightarrow> valid_graph \<lparr> nodes = V, edges = E \<rparr> \<Longrightarrow>
            all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<lparr> hosts = V, flows_fix = E, flows_state = set (accu) \<rparr>) \<Longrightarrow> 
            (set accu) \<union> (set edgesList) \<subseteq> E \<Longrightarrow> 
            all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<lparr> hosts = V, flows_fix = E, flows_state = set (filter_IFS_no_violations_accu \<lparr> nodes = V, edges = E \<rparr> M accu edgesList) \<rparr>)"
      apply(induction edgesList arbitrary: accu)
       by(simp_all)
    lemma filter_IFS_no_violations_correct: "\<lbrakk>valid_reqs (get_IFS M); valid_graph G;
            all_security_requirements_fulfilled (get_IFS M) G; 
            (set edgesList) \<subseteq> edges G \<rbrakk> \<Longrightarrow> 
            all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<lparr> hosts = nodes G, flows_fix = edges G, flows_state = set (filter_IFS_no_violations G M edgesList) \<rparr>)"
    unfolding filter_IFS_no_violations_def
    apply(case_tac G, simp)
    apply(drule(1) filter_IFS_no_violations_accu_correct_induction[where accu="[]", simplified])
      apply(simp_all)
    by(simp add: stateful_policy_to_network_graph_def all_flows_def backflows_def False_set)
    lemma filter_IFS_no_violations_accu_no_IFS: "valid_reqs (get_IFS M) \<Longrightarrow> valid_graph G \<Longrightarrow> get_IFS M = [] \<Longrightarrow>
            (set accu) \<union> (set edgesList) \<subseteq> edges G \<Longrightarrow> 
            filter_IFS_no_violations_accu G M accu edgesList = rev(edgesList)@accu"
      apply(induction edgesList arbitrary: accu)
       by(simp_all add: all_security_requirements_fulfilled_def)


    lemma filter_IFS_no_violations_accu_maximal_induction: "valid_reqs (get_IFS M) \<Longrightarrow> valid_graph \<lparr> nodes = V, edges = E \<rparr> \<Longrightarrow> 
      set accu \<subseteq> E \<Longrightarrow> set edgesList \<subseteq> E \<Longrightarrow>
        \<forall> e \<in> E - (set accu \<union> set edgesList).
            \<not> all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<lparr> hosts = V, flows_fix = E, flows_state = {e} \<union> (set accu) \<rparr>)
         \<Longrightarrow>
           let stateful = set (filter_IFS_no_violations_accu \<lparr> nodes = V, edges = E \<rparr> M accu edgesList) in
            (\<forall> e \<in> E - stateful.
            \<not> all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<lparr> hosts = V, flows_fix = E, flows_state = {e} \<union> stateful \<rparr>))"
      proof(induction edgesList arbitrary: accu)
      case Nil thus ?case by(simp add: Let_def)
      next
      case(Cons e Es)
        from Cons.prems(3) Cons.prems(2) have "fst ` set accu \<subseteq> V" and "snd ` set accu \<subseteq> V"
          by(auto simp add: valid_graph_def)
        --"@{const valid_graph} for some complicated structures"
        from Cons.prems(2) this Cons.prems(4)  have "\<And>ea. ea\<in>E \<Longrightarrow> valid_graph \<lparr> nodes = V, edges = insert e (insert ea (set accu)) \<rparr>"
          by(auto simp add: valid_graph_def)
        from backflows_valid[OF this] valid_graph_union_edges[OF Cons.prems(2)]
        have "\<And>ea. ea\<in>E  \<Longrightarrow> valid_graph \<lparr> nodes = V, edges = E \<union> backflows (insert e (insert ea (set accu))) \<rparr>" by (simp)
        hence "\<And>ea. ea\<in>E \<Longrightarrow> valid_graph \<lparr> nodes = V, edges = E \<union> set accu \<union> backflows (insert e (insert ea (set accu))) \<rparr>" 
          by (metis Cons.prems(3) sup.order_iff)
        from this Cons.prems(4)
        have "\<And>ea. ea\<in>E \<Longrightarrow> valid_graph \<lparr> nodes = V, edges = insert e (insert ea (E \<union> set accu \<union> backflows (insert e (insert ea (set accu))))) \<rparr>"
          by (metis List.set.simps(2) Un_insert_left insert_absorb insert_subset)
        hence validgraph1: "\<And>ea. ea\<in>E - (set (e # accu) \<union> set Es) \<Longrightarrow> 
          valid_graph \<lparr> nodes = V, edges = insert e (insert ea (E \<union> set accu \<union> backflows (insert e (insert ea (set accu))))) \<rparr>" by(simp)

        have validgraph2: "\<And> ea. 
         insert ea (E \<union> set accu \<union> backflows (insert ea (set accu))) \<subseteq> insert e (insert ea (E \<union> set accu \<union> backflows (insert e (insert ea (set accu)))))"
         apply(simp add: backflows_def)
         by blast
        
        from all_security_requirements_fulfilled_mono[OF Cons.prems(1) validgraph2 validgraph1] have neg_mono:
            "\<And>ea. ea \<in> E - (set (e # accu) \<union> set Es) \<Longrightarrow>
         \<not> all_security_requirements_fulfilled (get_IFS M) 
            \<lparr>nodes = V, edges = insert ea (E \<union> set accu \<union> backflows (insert ea (set accu)))\<rparr>
         \<Longrightarrow>
         \<not> all_security_requirements_fulfilled (get_IFS M) 
            \<lparr>nodes = V, edges = insert e (insert ea (E \<union> set accu \<union> backflows (insert e (insert ea (set accu)))))\<rparr>"
           apply(simp)
           by blast

         from Cons.prems(5) have "\<And>ea. ea\<in>E - (set (e # accu) \<union> set Es) \<Longrightarrow>
          \<not> all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph 
              \<lparr>hosts = V, flows_fix = E, flows_state = {ea} \<union> set (e # accu)\<rparr>)"
           apply(erule_tac x="ea" in ballE)
           prefer 2
           apply simp
          apply(simp only: stateful_policy_to_network_graph_def all_flows_def stateful_policy.select_convs)
          apply(simp)
          apply(frule(1) neg_mono[simplified])
          by(simp)
         hence goalTrue:
          "\<forall> ea\<in>E - (set (e # accu) \<union> set Es). 
            \<not> all_security_requirements_fulfilled (get_IFS M) 
                (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = {ea} \<union> set (e # accu)\<rparr>)"
         by simp
         
        show ?case
        apply(simp add: Let_def)
        apply(rule conjI)

         apply(rule impI)
         apply(thin_tac "?A") (*dont't need it*)
         using Cons.IH[where accu="e # accu", OF Cons.prems(1) Cons.prems(2) _ _ goalTrue, simplified Let_def] Cons.prems(3) Cons.prems(4)
         apply(auto) [1]

        apply(rule impI)
        using Cons.IH[where accu="accu", OF Cons.prems(1) Cons.prems(2), simplified Let_def] Cons.prems(5) Cons.prems(3) Cons.prems(4)
        apply(auto)
        done
     qed
    lemma filter_IFS_no_violations_maximal: "\<lbrakk>valid_reqs (get_IFS M); valid_graph G;
            (set edgesList) = edges G \<rbrakk> \<Longrightarrow> 
            let stateful = set (filter_IFS_no_violations G M edgesList) in 
            \<forall> e \<in> edges G - stateful.
              \<not> all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<lparr> hosts = nodes G, flows_fix = edges G, flows_state = {e} \<union> stateful \<rparr>)"
    unfolding filter_IFS_no_violations_def
    apply(case_tac G, simp)
    apply(drule(1) filter_IFS_no_violations_accu_maximal_induction[where accu="[]" and edgesList="edgesList"])
       by(simp_all)

    --"It is not only maximal for single flows but all non-empty subsets"
    corollary filter_IFS_no_violations_maximal_allsubsets: 
    assumes a1: "valid_reqs (get_IFS M)"
    and     a2: "valid_graph G"
    and     a4: "(set edgesList) = edges G"
    shows   "let stateful = set (filter_IFS_no_violations G M edgesList) in 
            \<forall> E \<subseteq> edges G - stateful. E \<noteq> {} \<longrightarrow>
              \<not> all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<lparr> hosts = nodes G, flows_fix = edges G, flows_state = E \<union> stateful \<rparr>)"
    proof -
      let ?stateful = "set (filter_IFS_no_violations G M edgesList)"
      from filter_IFS_no_violations_maximal[OF a1 a2 a4] have not_fulfilled_single: 
        "\<forall>e\<in>edges G - ?stateful. \<not> all_security_requirements_fulfilled (get_IFS M)
                (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = {e} \<union> ?stateful\<rparr>)"
        by(simp add: Let_def)
      have neg_mono:
        "\<And> e E. e \<in> E \<Longrightarrow> E \<subseteq> edges G - ?stateful \<Longrightarrow> E \<noteq> {} \<Longrightarrow>
          \<not> all_security_requirements_fulfilled (get_IFS M) 
              (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = {e} \<union> ?stateful\<rparr>) \<Longrightarrow> 
          \<not> all_security_requirements_fulfilled (get_IFS M) 
              (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = E \<union> ?stateful\<rparr>)"
        proof -
          fix e E
          assume h1: "e \<in> E"
          and    h2: "E \<subseteq> edges G - ?stateful"
          and    h3: "E \<noteq> {}"
          and    h4: "\<not> all_security_requirements_fulfilled (get_IFS M) 
            (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = {e} \<union> ?stateful\<rparr>)"
  
          from filter_IFS_no_violations_subseteq_input a4 have "?stateful \<subseteq> edges G" by blast
          hence "edges G \<union> (E \<union> ?stateful) = edges G" using h2 by blast
          from a2 this have validgraph1: "valid_graph \<lparr>nodes = nodes G, edges = edges G \<union> (E \<union> ?stateful)\<rparr>"
          by(case_tac G, simp)
  
          from h1 h2 h3 have subseteq: "({e} \<union> ?stateful) \<subseteq> (E \<union> ?stateful)" by blast

          have revimp: "\<And>A B. (A \<Longrightarrow> B) \<Longrightarrow> (\<not> B \<Longrightarrow> \<not> A)" by fast
          
          from all_security_requirements_fulfilled_mono_stateful_policy_to_network_graph[OF a1 subseteq validgraph1] h4
          show "\<not> all_security_requirements_fulfilled (get_IFS M) 
            (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = E \<union> ?stateful\<rparr>)" 
            apply(rule revimp)
            by assumption
        qed
      
      show ?thesis
      proof(simp add: Let_def,rule allI,rule impI, rule impI)
        fix E
        assume h1: "E \<subseteq> edges G - ?stateful"
        and    h2: "E \<noteq> {}"

        from  h1 h2 obtain e where e_prop1: "e \<in> E" by blast 
        from this h1 have "e \<in> edges G - ?stateful" by blast
        from this not_fulfilled_single have e_prop2: "\<not> all_security_requirements_fulfilled (get_IFS M)
          (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = {e} \<union> ?stateful\<rparr>)"
          by simp
        
        from neg_mono[OF e_prop1 h1 h2 e_prop2]
        show " \<not> all_security_requirements_fulfilled (get_IFS M)
               (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = E \<union> set (filter_IFS_no_violations G M edgesList)\<rparr>)"
        .
      qed
    qed
    
    --"soundness and completeness"
    thm filter_IFS_no_violations_correct filter_IFS_no_violations_maximal





  text{*Next *}
    (*"\<forall>F \<in> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<T> ). F \<subseteq> backflows (filternew_flows_state \<T>)"*)
    (*first in list are more likely to be kept*)
    fun filter_compliant_stateful_ACS_accu :: "'v::vertex graph \<Rightarrow> 'v SecurityInvariant_configured list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<times> 'v) list" where
      "filter_compliant_stateful_ACS_accu G M accu [] = accu" |
      "filter_compliant_stateful_ACS_accu G M accu (e#Es) = (if
        e \<notin> backflows (edges G) \<and> (\<forall>F \<in> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr> hosts = nodes G, flows_fix = edges G, flows_state = set (e#accu) \<rparr>). F \<subseteq> backflows (set (e#accu)))
        then filter_compliant_stateful_ACS_accu G M (e#accu) Es
        else filter_compliant_stateful_ACS_accu G M accu Es)"
    definition filter_compliant_stateful_ACS :: "'v::vertex graph \<Rightarrow> 'v SecurityInvariant_configured list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<times> 'v) list" where
      "filter_compliant_stateful_ACS G M Es = filter_compliant_stateful_ACS_accu G M [] Es"


    lemma filter_compliant_stateful_ACS_subseteq_input: "set (filter_compliant_stateful_ACS G M Es) \<subseteq> set Es"
      apply(subgoal_tac "\<forall> accu. set (filter_compliant_stateful_ACS_accu G M accu Es) \<subseteq> set Es \<union> set accu")
       apply(erule_tac x="[]" in allE)
       apply(simp add: filter_compliant_stateful_ACS_def)
      apply(induct_tac Es)
       apply(simp_all)
      apply(metis List.set.simps(2) Un_insert_right subset_insertI2)
      done
    lemma filter_compliant_stateful_ACS_accu_correct_induction: "valid_reqs (get_ACS M) \<Longrightarrow> valid_graph \<lparr> nodes = V, edges = E \<rparr> \<Longrightarrow>
            (set accu) \<union> (set edgesList) \<subseteq> E \<Longrightarrow> 
            \<forall>F \<in> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr> hosts = V, flows_fix = E, flows_state = set (accu) \<rparr>). F \<subseteq> backflows (set accu) \<Longrightarrow> 
            (\<forall>a \<in> set accu. a \<notin> (backflows E)) \<Longrightarrow>
            \<T> = \<lparr> hosts = V, flows_fix = E, flows_state = set (filter_compliant_stateful_ACS_accu \<lparr> nodes = V, edges = E \<rparr> M accu edgesList) \<rparr> \<Longrightarrow>
            \<forall>F \<in> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<T>). F \<subseteq> backflows (filternew_flows_state \<T>)"
      proof(induction edgesList arbitrary: accu)
        case Nil
          from Nil(5) have "backflows (set accu) = backflows {e \<in> set accu. e \<notin> backflows E}" by (metis (lifting) Collect_cong Collect_mem_eq)
          from this Nil(4) have "\<forall>F\<in>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = set accu\<rparr>). F \<subseteq> backflows {e \<in> set accu. e \<notin> backflows E}" by simp
          from this Nil(6) show ?case by(simp add: filternew_flows_state_alt2)
        next
        case (Cons e Es)
          from Cons.IH[OF Cons.prems(1) Cons.prems(2)] Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6)
          show ?case by(simp add: filternew_flows_state_alt2 split: split_if split_if_asm)
      qed

    
    lemma filter_compliant_stateful_ACS_accu_no_side_effects: "valid_reqs (get_ACS M) \<Longrightarrow> valid_graph G \<Longrightarrow>
            \<forall>F \<in> get_offending_flows (get_ACS M) \<lparr>nodes = nodes G, edges = edges G \<union> backflows (edges G)\<rparr>. F \<subseteq> (backflows (edges G)) - (edges G) \<Longrightarrow>
            (set accu) \<union> (set edgesList) \<subseteq> edges G \<Longrightarrow> 
            (\<forall>a \<in> set accu. a \<notin> (backflows (edges G))) \<Longrightarrow>
            filter_compliant_stateful_ACS_accu G M accu edgesList = rev([ e \<leftarrow> edgesList. e \<notin> backflows (edges G)])@accu"
      apply(simp add: backflows_minus_backflows)
      apply(induction edgesList arbitrary: accu)
       apply(simp)
      apply(simp add: stateful_policy_to_network_graph_def all_flows_def)
      apply(rule impI)
      apply(case_tac G, simp, rename_tac V E)
      thm Un_set_offending_flows_bound_minus_subseteq'[where X="backflows E - E" and E="E \<union> backflows E"]
      apply(drule_tac X="backflows E - E" and E="E \<union> backflows E" and E'="(E \<union> backflows E) - (insert a (E \<union> set accu \<union> backflows (insert a (set accu))))" in Un_set_offending_flows_bound_minus_subseteq')
         defer
         prefer 2
         apply blast
        apply auto[1]
       apply(subgoal_tac "E \<union> backflows E - (E \<union> backflows E - insert a (E \<union> set accu \<union> backflows (insert a (set accu)))) = insert a (E \<union> set accu \<union> backflows (insert a (set accu)))")
        apply(simp)
        prefer 2
        apply (metis Un_assoc Un_least Un_mono backflows_subseteq double_diff insert_def insert_subset subset_refl)
       apply(subgoal_tac "backflows (insert a (set accu)) \<subseteq> backflows E - E - (E \<union> backflows E - insert a (E \<union> set accu \<union> backflows (insert a (set accu))))")
        apply(blast)
       apply(simp add: backflows_def)
       apply fast
      using FiniteGraph.backflows_valid FiniteGraph.valid_graph_union_edges by metis



    lemma filter_compliant_stateful_ACS_correct: 
      assumes a1: "valid_reqs (get_ACS M)"
      and     a2: "valid_graph G"
      and     a3: "set edgesList \<subseteq> edges G"  
      and     a4: "all_security_requirements_fulfilled (get_ACS M) G"
      and     a5: "\<T> = \<lparr> hosts = nodes G, flows_fix = edges G, flows_state = set (filter_compliant_stateful_ACS G M edgesList) \<rparr>"
      shows   "\<forall>F \<in> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<T>). F \<subseteq> backflows (filternew_flows_state \<T>)"
      proof -
        obtain V E where VE: "G = \<lparr> nodes = V, edges = E \<rparr>" by(case_tac G, blast)
        from VE a2 have validVE: "valid_graph \<lparr> nodes = V, edges = E \<rparr>" by simp
        from VE a3 have "set edgesList \<subseteq> E" by simp

        from a5 VE have a5': "\<T> = \<lparr>hosts = V, flows_fix = E, flows_state = set (filter_compliant_stateful_ACS_accu \<lparr>nodes = V, edges = E\<rparr> M [] edgesList)\<rparr>"
          unfolding filter_compliant_stateful_ACS_def
          by(simp)

        from all_security_requirements_fulfilled_imp_get_offending_empty[OF a1 a4] VE
        have "\<forall>F\<in>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = {}\<rparr>). F \<subseteq> backflows {}"
          by(simp add: stateful_policy_to_network_graph_def all_flows_def backflows_def False_set)

        from filter_compliant_stateful_ACS_accu_correct_induction[where accu="[]" and edgesList="edgesList", simplified, OF a1 validVE `set edgesList \<subseteq> E` this a5']
        show ?thesis .
     qed


    lemma filter_compliant_stateful_ACS_accu_induction_maximal:"\<lbrakk> valid_reqs (get_ACS M);  valid_graph \<lparr> nodes = V, edges = E \<rparr>;
            (set edgesList) \<subseteq> E;
            (set accu) \<subseteq> E; 
            stateful = set (filter_compliant_stateful_ACS_accu \<lparr> nodes = V, edges = E \<rparr> M accu edgesList);
            \<forall>e \<in> E - (set edgesList \<union> set accu \<union> {e \<in> E. e \<in> backflows E}).
            \<not> (\<Union> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr> hosts = V, flows_fix = E, flows_state = set accu \<union> {e} \<rparr>) 
                \<subseteq> backflows (filternew_flows_state \<lparr> hosts = V, flows_fix = E, flows_state = set accu \<union> {e} \<rparr>))
            \<rbrakk> \<Longrightarrow>
            \<forall>e \<in> E - (stateful \<union> {e \<in> E. e \<in> backflows E}). (* E - {computed stateful flows plus trivial stateful flows} *)
            \<not> (\<Union> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr> hosts = V, flows_fix = E, flows_state = stateful \<union> {e} \<rparr>) 
                \<subseteq> backflows (filternew_flows_state \<lparr> hosts = V, flows_fix = E, flows_state = stateful \<union> {e} \<rparr>))"
   proof(induction edgesList arbitrary: accu E)
   case Nil from Nil(5)[simplified] Nil(6) show ?case by(simp)
   next
   case (Cons a Es)
     --"case distinction"
     let ?caseDistinction="a \<notin> backflows (E) \<and>  (\<forall>F\<in>get_offending_flows (get_ACS M)
                 (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = set (a # accu)\<rparr>).
                    F \<subseteq> backflows (set (a # accu)))"
     from Cons.prems(3) have "set Es \<subseteq> E" by simp

     show ?case
      proof(cases ?caseDistinction)
        assume CaseTrue: ?caseDistinction
        from CaseTrue have 
          "set (filter_compliant_stateful_ACS_accu \<lparr>nodes = V, edges = E\<rparr> M accu (a # Es)) = 
           set (filter_compliant_stateful_ACS_accu \<lparr>nodes = V, edges = E\<rparr> M (a # accu) Es)"
           by(simp)
        from this Cons.prems(5) have statefulsimp:
          "stateful = set (filter_compliant_stateful_ACS_accu \<lparr>nodes = V, edges = E\<rparr> M (a # accu) Es)" by simp
        from Cons.prems(3) Cons.prems(4) have "set (a # accu) \<subseteq> E" by simp

        have "\<forall>e\<in>E - (set Es \<union> set (a # accu) \<union> {e \<in> E. e \<in> backflows E}).
     \<not> \<Union>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = set (a # accu) \<union> {e}\<rparr>)
        \<subseteq> backflows (filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = set (a # accu) \<union> {e}\<rparr>)"
          proof(rule ballI)
            fix e
            assume h1: "e \<in> E - (set Es \<union> set (a # accu) \<union> {e \<in> E. e \<in> backflows E})"

            from conjunct1[OF CaseTrue] have filternew_flows_state_moveout_a:
              "filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = set (a # accu) \<union> {e}\<rparr> = 
              {a} \<union> filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = set accu \<union> {e}\<rparr>"
              apply(simp add: filternew_flows_state_alt) by blast

            have backflowssubseta: "\<And>X. backflows X \<subseteq> backflows ({a} \<union> X)" by(simp add: backflows_def, blast)

            from Cons.prems(6) h1 have 
              "\<not> \<Union>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = set accu \<union> {e}\<rparr>)
                \<subseteq> backflows (filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = set accu \<union> {e}\<rparr>)" by simp
            from this obtain dat_offender where 
              dat_in: "dat_offender \<in> \<Union>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = set accu \<union> {e}\<rparr>)"
              and dat_offends: "dat_offender \<notin> backflows (filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = set accu \<union> {e}\<rparr>)" by blast

            have validGraphA: "valid_graph (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = set (a # accu) \<union> {e}\<rparr>)"
              proof(simp add: stateful_policy_to_network_graph_def all_flows_def)
              from Cons.prems(2) h1 Cons.prems(3) Cons.prems(4)
              have "valid_graph \<lparr>nodes=V, edges = insert e (insert a (set accu)) \<rparr>" 
              apply(auto simp add: valid_graph_def) by force
              from this backflows_valid
              have vgh1: "valid_graph \<lparr>nodes = V, edges = backflows (insert e (insert a (set accu)))\<rparr>" by auto
              from Cons.prems(2) valid_graph_add_subset_edges h1  Cons.prems(3) Cons.prems(4)
              have vgh2: "valid_graph \<lparr>nodes = V, edges = insert e ((insert a E) \<union> set accu)\<rparr>"
                proof -
                  have f1: "e \<in> E - (set Es \<union> insert a (set accu) \<union> {R \<in> E. R \<in> backflows E})"
                    using h1 by simp
                  have f2: "insert a (set accu) \<subseteq> E"
                    by (metis List.set.simps(2) `set (a # accu) \<subseteq> E`)
                  have f3: "e \<in> E"
                    using f1 by fastforce
                  have "E \<union> insert a (set accu) = E"
                    using f2 by fastforce
                  thus "valid_graph \<lparr>nodes = V, edges = insert e (insert a E \<union> set accu)\<rparr>"
                    using f3 Cons.prems(2) Un_insert_right insert_absorb sup_commute by fastforce
                qed
              from vgh1 vgh2 valid_graph_union_edges
              show "valid_graph \<lparr>nodes = V, edges = insert e (insert a (E \<union> set accu \<union> backflows (insert e (insert a (set accu)))))\<rparr>" by fastforce
           qed
            
            from dat_in have dat_in_simplified: 
              "dat_offender \<in> \<Union>get_offending_flows (get_ACS M) \<lparr>nodes = V, edges = insert e (E \<union> set accu \<union> backflows (insert e (set accu)))\<rparr>"
              by(simp add: stateful_policy_to_network_graph_def all_flows_def)

            have subsethlp: "insert e (E \<union> set accu \<union> backflows (insert e (set accu))) \<subseteq> E \<union> (set (a # accu) \<union> {e}) \<union> backflows (set (a # accu) \<union> {e})"
              apply(simp)
              apply(rule, blast)
              apply(rule, blast)
              apply(rule)
              apply(simp add: backflows_def, fast)
              done

            from get_offending_flows_union_mono[OF 
                Cons.prems(1) 
                validGraphA[simplified stateful_policy_to_network_graph_def all_flows_def graph.select_convs stateful_policy.select_convs],
                OF subsethlp]
            dat_in_simplified have dat_in_a: "dat_offender \<in> \<Union>get_offending_flows (get_ACS M) 
              (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = set (a # accu) \<union> {e}\<rparr>)"
              by(simp add: stateful_policy_to_network_graph_def all_flows_def, fast)

            have "dat_offender \<noteq> (snd a, fst a)"
              proof(rule ccontr)
              assume "\<not> dat_offender \<noteq> (snd a, fst a)"
              hence hlpassm: "dat_offender = (snd a, fst a)" by simp
              from this obtain a1 a2 where "dat_offender = (a2, a1)" by blast
              
              
              have "\<Union>get_offending_flows (get_ACS M) \<lparr>nodes = V, edges = insert e (E \<union> set accu \<union> backflows (insert e (set accu)))\<rparr> \<subseteq> 
                  insert e (E \<union> set accu \<union> backflows (insert e (set accu)))"
                by (metis Cons.prems(1) Sup_le_iff get_offending_flows_subseteq_edges)
              from this h1 have UN_get_subset: 
                    "\<Union>get_offending_flows (get_ACS M) \<lparr>nodes = V, edges = insert e (E \<union> set accu \<union> backflows (insert e (set accu)))\<rparr> \<subseteq> 
                   (E \<union> set accu \<union> backflows (insert e (set accu)))"
                by blast

            from dat_offends have dat_offends_simplified: 
              "dat_offender \<notin> backflows (insert e (set accu)) - E"
                by(simp only: filternew_flows_state_alt stateful_policy.select_convs backflows_minus_backflows, simp)
              
              from conjunct1[OF CaseTrue] hlpassm have "dat_offender \<notin> E"
                by(simp add: backflows_def, fastforce)
              from dat_in_simplified UN_get_subset this have "dat_offender \<in> set accu \<union> backflows (insert e (set accu))" by blast
              from this Cons.prems(4) `dat_offender \<notin> E` have "dat_offender \<in> backflows (insert e (set accu))" by blast
              from dat_offends_simplified[simplified] this have "dat_offender \<in> E" by simp
              from `dat_offender \<notin> E` `dat_offender \<in> E` show False by simp
            qed

            from this dat_offends have 
              "dat_offender \<notin> backflows ({a} \<union> filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = set accu \<union> {e}\<rparr>)"
              apply(simp add: backflows_def) by force

            from dat_in_a this
            show "\<not> \<Union>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = set (a # accu) \<union> {e}\<rparr>)
            \<subseteq> backflows (filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = set (a # accu) \<union> {e}\<rparr>)"
            apply(subst filternew_flows_state_moveout_a) by blast
          qed

        from Cons.IH[OF Cons.prems(1) Cons.prems(2) `set Es \<subseteq> E` `set (a # accu) \<subseteq> E` statefulsimp this ] show "?case" 
          by(simp)
      next
        assume CaseFalse: "\<not> ?caseDistinction"

        from CaseFalse have funapplysimp: 
          "set (filter_compliant_stateful_ACS_accu \<lparr>nodes = V, edges = E\<rparr> M accu (a # Es)) = 
           set (filter_compliant_stateful_ACS_accu \<lparr>nodes = V, edges = E\<rparr> M accu Es)"
           by auto
        from this Cons.prems(5) have statefulsimp:
          "stateful = set (filter_compliant_stateful_ACS_accu \<lparr>nodes = V, edges = E\<rparr> M accu Es)" by simp
        from Cons.prems(4) have "set accu \<subseteq> E" .

        have "a \<in> E - (set Es \<union> set accu \<union> {e \<in> E. e \<in> backflows E})\<Longrightarrow> \<not> \<Union>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = set accu \<union> {a}\<rparr>)
          \<subseteq> backflows (filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = set accu \<union> {a}\<rparr>)"
          proof(rule ccontr)
            assume h1: "a \<in> E - (set Es \<union> set accu \<union> {e \<in> E. e \<in> backflows E})"
            and    "\<not> \<not>\<Union>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = set accu \<union> {a}\<rparr>) \<subseteq> backflows (filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = set accu \<union> {a}\<rparr>)"
            hence hccontr: "\<Union>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = set accu \<union> {a}\<rparr>) \<subseteq> backflows (filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = set accu \<union> {a}\<rparr>)" by simp

            moreover from h1 have stateful_to_graph: "stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = set accu \<union> {a}\<rparr> =  \<lparr>nodes = V, edges = E \<union> set accu \<union> backflows (insert a (set accu))\<rparr>"
              by(simp add: stateful_policy_to_network_graph_def all_flows_def, blast)
            moreover have "backflows (filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = set accu \<union> {a}\<rparr>) = backflows (insert a (set accu)) - E"
              by(simp add: filternew_flows_state_alt backflows_minus_backflows)
            ultimately have hccontr_simp:
              "\<Union>get_offending_flows (get_ACS M) \<lparr>nodes = V, edges = E \<union> set accu \<union> backflows (insert a (set accu))\<rparr> \<subseteq> backflows (insert a (set accu)) - E" by simp

            from Cons.prems(3) Cons.prems(4) have backaaccusubE: "backflows (set (a # accu)) \<subseteq> backflows E" by(simp add: backflows_def, fastforce)
            from h1 have "a \<notin> backflows E" by fastforce
            from backaaccusubE `a \<notin> backflows E` have "a \<notin> backflows (insert a (set accu))" by auto


            from `a \<notin> backflows E` CaseFalse have "\<not> (\<forall>F\<in>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = set (a # accu)\<rparr>). F \<subseteq> backflows (set (a # accu)))" by(simp)
            from this stateful_to_graph have "\<not> (\<forall>F\<in>get_offending_flows (get_ACS M) \<lparr>nodes = V, edges = E \<union> set accu \<union> backflows (insert a (set accu))\<rparr>. F \<subseteq> backflows (insert a (set accu)))" by(simp)
            from this hccontr_simp show False by blast
        qed
        from  Cons.prems(6)[simplified funapplysimp statefulsimp] this
        have "\<forall>e\<in>E - (set Es \<union> set accu \<union> {e \<in> E. e \<in> backflows E}).
       \<not> \<Union>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = set accu \<union> {e}\<rparr>)
          \<subseteq> backflows (filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = set accu \<union> {e}\<rparr>)"
          by auto

        from Cons.IH[OF Cons.prems(1) Cons.prems(2) `set Es \<subseteq> E` `set accu \<subseteq> E` statefulsimp this]
        show ?case by simp
      qed
   qed






   

    lemma filter_compliant_stateful_ACS_maximal: "\<lbrakk> valid_reqs (get_ACS M); valid_graph \<lparr> nodes = V, edges = E \<rparr>;
            (set edgesList) = E;
            stateful = set (filter_compliant_stateful_ACS \<lparr> nodes = V, edges = E \<rparr> M edgesList)
            \<rbrakk> \<Longrightarrow>
            \<forall>e \<in> E - (stateful \<union> {e \<in> E. e \<in> backflows E}). (* E - {computed stateful flows plus trivial stateful flows} *)
            \<not> (\<Union> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr> hosts = V, flows_fix = E, flows_state = stateful \<union> {e} \<rparr>) 
                \<subseteq> backflows (filternew_flows_state \<lparr> hosts = V, flows_fix = E, flows_state = stateful \<union> {e} \<rparr>))"
    apply(drule(1) filter_compliant_stateful_ACS_accu_induction_maximal[where accu="[]", simplified])
       apply(blast)
      apply(simp add: filter_compliant_stateful_ACS_def)
     apply(simp)
     apply fastforce
    apply(simp add: filter_compliant_stateful_ACS_def)
   done


    lemma filter_compliant_stateful_ACS_maximal_allsubsets:
      assumes a1: "valid_reqs (get_ACS M)" and a2: "valid_graph \<lparr> nodes = V, edges = E \<rparr>"
      and a3: "(set edgesList) = E"
      and a4: "stateful = set (filter_compliant_stateful_ACS \<lparr> nodes = V, edges = E \<rparr> M edgesList)"
      and a5: "X \<subseteq> E - (stateful \<union> backflows E)" and a6: "X \<noteq> {}"
      shows "
      \<not> (\<Union> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr> hosts = V, flows_fix = E, flows_state = stateful \<union> X \<rparr>) 
                \<subseteq> backflows (filternew_flows_state \<lparr> hosts = V, flows_fix = E, flows_state = stateful \<union> X \<rparr>))"
    proof(rule ccontr, simp)
      from a5 have "X \<subseteq> E" by blast
      assume accontr: "\<Union>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = stateful \<union> X\<rparr>) \<subseteq> backflows (filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = stateful \<union> X\<rparr>)"
      hence "\<Union>get_offending_flows (get_ACS M) \<lparr>nodes = V, edges = E \<union> (stateful \<union> X) \<union> backflows (stateful \<union> X)\<rparr> \<subseteq> backflows (stateful \<union> X) - E"
      by(simp add: stateful_policy_to_network_graph_def all_flows_def filternew_flows_state_alt backflows_minus_backflows)
      hence "\<Union>get_offending_flows (get_ACS M) \<lparr>nodes = V, edges = E \<union> X \<union> backflows (stateful \<union> X)\<rparr> \<subseteq> backflows (stateful \<union> X) - E"
      using a4 a3 filter_compliant_stateful_ACS_subseteq_input by (metis Diff_subset_conv Un_Diff_cancel Un_assoc a3 bot.extremum_unique sup_bot_right)
      hence accontr_simp: "\<Union>get_offending_flows (get_ACS M) \<lparr>nodes = V, edges = E \<union> (backflows stateful) \<union> (backflows X)\<rparr> \<subseteq> backflows (stateful \<union> X) - E"
      using Set.Un_absorb2[OF `X \<subseteq> E`] backflows_un[of "stateful" "X"] by (metis Un_assoc)
      
      from a2 a5 have "finite X" apply(simp add: valid_graph_def) by (metis (full_types) finite_Diff finite_subset)
      from a6 obtain x where "x \<in> X" by blast


      from `x \<in> X` a5 have xX_simp1: "(backflows X) - (backflows (X - {x}) - E)  = backflows {x}"
        apply(simp add: backflows_def) by fast
      from a5 have "X \<inter> stateful = {}" by auto
      from `x \<in> X` this have xX_simp2: "(backflows stateful) - (backflows (X - {x}) - E) = backflows stateful"
        apply(simp add: backflows_def) by fast
      have xX_simp3:"backflows (stateful \<union> X) - (backflows (X - {x}) - E) = backflows (stateful \<union> {x})"
        apply(simp only: backflows_un)
        using xX_simp1 xX_simp2 by blast

      have xX_simp4: "backflows (stateful \<union> X) - E - (backflows (X - {x}) - E) = backflows (filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = stateful \<union> {x}\<rparr>)"
        apply(simp add: filternew_flows_state_alt backflows_minus_backflows)
        using xX_simp3 by auto


      have xX_simp5: "(E \<union> backflows stateful \<union> backflows X) - (backflows (X - {x}) - E) = E \<union> backflows stateful \<union> backflows {x}"
      using xX_simp3[simplified backflows_un] by blast

      have Eexpand: "E \<union> stateful \<union> {x} = E" 
      using a4 a3 filter_compliant_stateful_ACS_subseteq_input a5 `x\<in>X` by blast

      have "backflows (stateful \<union> X) - E - backflows (X - {x}) = (backflows (stateful \<union> X) - E) - backflows (X - {x})" by simp
      from `finite X` backflows_finite have finite: "finite (backflows (X - {x}) - E)" by auto
      from a2 a4 a3 filter_compliant_stateful_ACS_subseteq_input have "valid_graph \<lparr>nodes = V, edges = stateful\<rparr>" by (metis Diff_partition valid_graph_remove_edges_union)
      from backflows_valid[OF this] have "valid_graph \<lparr>nodes = V, edges = backflows stateful\<rparr>" .
      from a2 `X \<subseteq> E` have "valid_graph \<lparr>nodes = V, edges = X\<rparr>" by (metis double_diff dual_order.refl valid_graph_remove_edges)
       from backflows_valid[OF this] have "valid_graph \<lparr>nodes = V, edges = backflows X\<rparr>" .
      from this valid_graph_union_edges `valid_graph \<lparr>nodes = V, edges = backflows stateful\<rparr>` a2 have validG: 
        "valid_graph \<lparr>nodes = V, edges = E \<union> backflows stateful \<union> backflows X\<rparr>" by metis

      from `x\<in>X` have subset: "backflows (X - {x}) - E \<subseteq> E \<union> backflows stateful \<union> backflows X" apply(simp add: backflows_def) by fast

      from Un_set_offending_flows_bound_minus_subseteq'[OF a1 validG subset accontr_simp] have
        "\<Union>get_offending_flows (get_ACS M) \<lparr>nodes = V, edges = (E \<union> backflows stateful \<union> backflows X) - (backflows (X - {x}) - E)\<rparr> \<subseteq> (backflows (stateful \<union> X) - E) - (backflows (X - {x}) - E)" by simp
      from this xX_simp4 xX_simp5 have trans1:
        "\<Union>get_offending_flows (get_ACS M) \<lparr>nodes = V, edges = E \<union> backflows stateful \<union> backflows {x}\<rparr> \<subseteq> backflows (filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = stateful \<union> {x}\<rparr>)" by simp

      hence "\<Union>get_offending_flows (get_ACS M) \<lparr>nodes = V, edges = E \<union> backflows (stateful \<union> {x})\<rparr> \<subseteq> backflows (filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = stateful \<union> {x}\<rparr>)"
      apply(simp only: backflows_un) by (metis Un_assoc)
      hence contr1: "\<Union>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = stateful \<union> {x}\<rparr>) \<subseteq> backflows (filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = stateful \<union> {x}\<rparr>)"
      apply(simp only: stateful_policy_to_network_graph_def all_flows_def stateful_policy.select_convs)
      using Eexpand by (metis Un_assoc)
      

      from filter_compliant_stateful_ACS_maximal[OF a1 a2 a3 a4] have
        "\<forall>e\<in>E - (stateful \<union> {e \<in> E. e \<in> backflows E}). \<not> \<Union>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = stateful \<union> {e}\<rparr>) \<subseteq> backflows (filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = stateful \<union> {e}\<rparr>)" .
      from this a5 `x \<in> X` have contr2: "\<not> \<Union>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = V, flows_fix = E, flows_state = stateful \<union> {x}\<rparr>) \<subseteq> backflows (filternew_flows_state \<lparr>hosts = V, flows_fix = E, flows_state = stateful \<union> {x}\<rparr>)" by blast

      from contr1 contr2
      show "False" by simp
    qed


    text{*@{term filter_compliant_stateful_ACS} is correct and maximal*}
    thm filter_compliant_stateful_ACS_correct filter_compliant_stateful_ACS_maximal


    text{*Getting those together. We cannot say @{text "edgesList = E"} here because one filters first. I guess filtering ACS first is easier, ...*}










  definition generate_valid_stateful_policy_IFSACS :: "'v::vertex graph \<Rightarrow> 'v SecurityInvariant_configured list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 'v stateful_policy" where
    "generate_valid_stateful_policy_IFSACS G M edgesList \<equiv> (let filterIFS = filter_IFS_no_violations G M edgesList in
        (let filterACS = filter_compliant_stateful_ACS G M filterIFS in \<lparr> hosts = nodes G, flows_fix = edges G, flows_state = set filterACS \<rparr>))"


  lemma generate_valid_stateful_policy_IFSACS_valid_stateful_policy: assumes validG: "valid_graph G"
          and     edgesList: "(set edgesList) = edges G"
          shows "valid_stateful_policy (generate_valid_stateful_policy_IFSACS G M edgesList)"
   proof -
    from  validG show ?thesis
     apply(simp add: generate_valid_stateful_policy_IFSACS_def valid_stateful_policy_def)
     apply(auto simp add: valid_graph_def)
     using edgesList filter_IFS_no_violations_subseteq_input filter_compliant_stateful_ACS_subseteq_input by (metis set_rev_mp)
   qed

   lemma generate_valid_stateful_policy_IFSACS_select_simps:
   shows "hosts (generate_valid_stateful_policy_IFSACS G M edgesList) = nodes G"
   and   "flows_fix (generate_valid_stateful_policy_IFSACS G M edgesList) = edges G"
   and   "flows_state (generate_valid_stateful_policy_IFSACS G M edgesList) \<subseteq> set edgesList"
   proof -
   show  "hosts (generate_valid_stateful_policy_IFSACS G M edgesList) = nodes G"
      by(simp add: generate_valid_stateful_policy_IFSACS_def)
    show "flows_fix (generate_valid_stateful_policy_IFSACS G M edgesList) = edges G"
      by(simp add: generate_valid_stateful_policy_IFSACS_def)
    show "flows_state (generate_valid_stateful_policy_IFSACS G M edgesList) \<subseteq> set edgesList"
      apply(simp add: generate_valid_stateful_policy_IFSACS_def)
      using filter_IFS_no_violations_subseteq_input filter_compliant_stateful_ACS_subseteq_input by (metis subset_trans)
    qed

  lemma generate_valid_stateful_policy_IFSACS_all_security_requirements_fulfilled_IFS: assumes validReqs: "valid_reqs M"
          and     validG: "valid_graph G"
          and     high_level_policy_valid: "all_security_requirements_fulfilled M G"
          and     edgesList: "(set edgesList) \<subseteq> edges G"
          shows "all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph (generate_valid_stateful_policy_IFSACS G M edgesList))"
  proof -
   have simp3: "flows_state (generate_valid_stateful_policy_IFSACS G M edgesList) \<subseteq> edges G" using generate_valid_stateful_policy_IFSACS_select_simps(3) edgesList by fast

    have "set (filter_compliant_stateful_ACS G M (filter_IFS_no_violations G M edgesList)) \<subseteq> set (filter_IFS_no_violations G M edgesList)"
      using filter_compliant_stateful_ACS_subseteq_input edgesList by (metis)
    from backflows_subseteq this have 
      "backflows (set (filter_compliant_stateful_ACS G M (filter_IFS_no_violations G M edgesList))) \<subseteq> backflows (set (filter_IFS_no_violations G M edgesList))" by metis
    hence subseteqhlp1:
      "edges G \<union> backflows (set (filter_compliant_stateful_ACS G M (filter_IFS_no_violations G M edgesList))) \<subseteq> edges G \<union> backflows (set (filter_IFS_no_violations G M edgesList))" by blast

    from high_level_policy_valid have "all_security_requirements_fulfilled (get_IFS M) G" by(simp add: all_security_requirements_fulfilled_def get_IFS_def)
    from filter_IFS_no_violations_correct[OF valid_reqs_IFS_D[OF validReqs] validG this edgesList] have 
      "all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = set (filter_IFS_no_violations G M edgesList)\<rparr>)" .
      from this edgesList have goalIFS:
        "all_security_requirements_fulfilled (get_IFS M) \<lparr>nodes = nodes G, edges = edges G \<union> backflows (set (filter_IFS_no_violations G M edgesList))\<rparr>"
        apply(simp add: stateful_policy_to_network_graph_def all_flows_def)
        by (metis Un_absorb2 filter_IFS_no_violations_subseteq_input order_trans)


      from  validG filter_IFS_no_violations_subseteq_input[where Es="edgesList" and G="G" and M="M"] edgesList have 
        "valid_graph \<lparr>nodes = nodes G, edges = set (filter_IFS_no_violations G M edgesList)\<rparr>" 
         apply(case_tac G, simp)
         by (metis le_iff_sup valid_graph_remove_edges_union)
      from backflows_valid[OF this] have
        "valid_graph \<lparr>nodes = nodes G, edges = backflows (set (filter_IFS_no_violations G M edgesList))\<rparr>" by(simp)
      from this valid_graph_union_edges validG have 
        "valid_graph \<lparr>nodes = nodes G, edges = edges G \<union> backflows (set (filter_IFS_no_violations G M edgesList))\<rparr>" 
        by (metis graph.cases graph.select_convs(1) graph.select_convs(2))

      from all_security_requirements_fulfilled_mono[OF valid_reqs_IFS_D[OF validReqs] subseteqhlp1 this goalIFS]
        have "all_security_requirements_fulfilled (get_IFS M) \<lparr>nodes = nodes G, edges = edges G \<union> backflows (set (filter_compliant_stateful_ACS G M (filter_IFS_no_violations G M edgesList)))\<rparr>"
        .
      thus ?thesis
        apply(simp add: stateful_policy_to_network_graph_def all_flows_def generate_valid_stateful_policy_IFSACS_select_simps simp3 Un_absorb2)
        by(simp add: generate_valid_stateful_policy_IFSACS_def)
  qed

  theorem generate_valid_stateful_policy_IFSACS_stateful_policy_compliance:
  assumes validReqs: "valid_reqs M"
        and     validG: "valid_graph G"
        and     high_level_policy_valid: "all_security_requirements_fulfilled M G"
        and     edgesList: "(set edgesList) = edges G"
        and     Tau: "\<T> = generate_valid_stateful_policy_IFSACS G M edgesList"
    shows "stateful_policy_compliance \<T> G M"
    proof -
      have 1: "valid_stateful_policy \<T>"
        apply(simp add: Tau)
        by(simp add: generate_valid_stateful_policy_IFSACS_valid_stateful_policy[OF validG edgesList])
      have 2: "valid_stateful_policy (generate_valid_stateful_policy_IFSACS G M edgesList)"
        by(simp add: generate_valid_stateful_policy_IFSACS_valid_stateful_policy[OF validG edgesList])
      have 3: "hosts \<T> = nodes G"
        apply(simp add: Tau)
        by(simp add: generate_valid_stateful_policy_IFSACS_select_simps(1))
      have 4: "flows_fix \<T> \<subseteq> edges G"
        apply(simp add: Tau)
        by(simp add: generate_valid_stateful_policy_IFSACS_select_simps(2))
      have 5: " all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<T>)"
        apply(simp add: Tau)
        using generate_valid_stateful_policy_IFSACS_all_security_requirements_fulfilled_IFS[OF validReqs validG high_level_policy_valid] edgesList by blast
      have 6: "\<forall>F\<in>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<T>). F \<subseteq> backflows (filternew_flows_state \<T>)"
        using filter_compliant_stateful_ACS_correct[OF valid_reqs_ACS_D[OF validReqs] validG _ _ Tau[simplified generate_valid_stateful_policy_IFSACS_def Let_def]] all_security_requirements_fulfilled_ACS_D[OF high_level_policy_valid]
        edgesList filter_IFS_no_violations_subseteq_input by metis

    from 1 2 3 4 5 6 validReqs high_level_policy_valid validG
    show ?thesis
    unfolding stateful_policy_compliance_def by simp
  qed





  definition generate_valid_stateful_policy_IFSACS_2 :: "'v::vertex graph \<Rightarrow> 'v SecurityInvariant_configured list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 'v stateful_policy" where
    "generate_valid_stateful_policy_IFSACS_2 G M edgesList \<equiv> 
    \<lparr> hosts = nodes G, flows_fix = edges G, flows_state = set (filter_IFS_no_violations G M edgesList) \<inter> set (filter_compliant_stateful_ACS G M edgesList) \<rparr>"


  lemma generate_valid_stateful_policy_IFSACS_2_valid_stateful_policy: assumes validG: "valid_graph G"
          and     edgesList: "(set edgesList) = edges G"
          shows "valid_stateful_policy (generate_valid_stateful_policy_IFSACS_2 G M edgesList)"
   proof -
    from  validG show ?thesis
     apply(simp add: generate_valid_stateful_policy_IFSACS_2_def valid_stateful_policy_def)
     apply(auto simp add: valid_graph_def)
     using edgesList filter_IFS_no_violations_subseteq_input by (metis set_rev_mp)
   qed

   lemma generate_valid_stateful_policy_IFSACS_2_select_simps:
   shows "hosts (generate_valid_stateful_policy_IFSACS_2 G M edgesList) = nodes G"
   and   "flows_fix (generate_valid_stateful_policy_IFSACS_2 G M edgesList) = edges G"
   and   "flows_state (generate_valid_stateful_policy_IFSACS_2 G M edgesList) \<subseteq> set edgesList"
   proof -
   show  "hosts (generate_valid_stateful_policy_IFSACS_2 G M edgesList) = nodes G"
      by(simp add: generate_valid_stateful_policy_IFSACS_2_def)
    show "flows_fix (generate_valid_stateful_policy_IFSACS_2 G M edgesList) = edges G"
      by(simp add: generate_valid_stateful_policy_IFSACS_2_def)
    show "flows_state (generate_valid_stateful_policy_IFSACS_2 G M edgesList) \<subseteq> set edgesList"
      apply(simp add: generate_valid_stateful_policy_IFSACS_2_def)
      using filter_compliant_stateful_ACS_subseteq_input by (metis inf.coboundedI2)
    qed

  lemma generate_valid_stateful_policy_IFSACS_2_all_security_requirements_fulfilled_IFS: assumes validReqs: "valid_reqs M"
          and     validG: "valid_graph G"
          and     high_level_policy_valid: "all_security_requirements_fulfilled M G"
          and     edgesList: "(set edgesList) \<subseteq> edges G"
          shows "all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph (generate_valid_stateful_policy_IFSACS_2 G M edgesList))"
  proof -
    have subseteq: "set (filter_IFS_no_violations G M edgesList) \<inter> set (filter_compliant_stateful_ACS G M edgesList) \<subseteq> set (filter_IFS_no_violations G M edgesList)" by blast

    from validG filter_IFS_no_violations_subseteq_input edgesList
    have validG': "valid_graph \<lparr>nodes = nodes G, edges = edges G \<union> set (filter_IFS_no_violations G M edgesList)\<rparr>" 
      by (metis graph_eq_intro Un_absorb2 graph.select_convs(1) graph.select_convs(2) order.trans)

    from high_level_policy_valid have "all_security_requirements_fulfilled (get_IFS M) G" by(simp add: all_security_requirements_fulfilled_def get_IFS_def)
    from filter_IFS_no_violations_correct[OF valid_reqs_IFS_D[OF validReqs] validG this edgesList] have 
      "all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = set (filter_IFS_no_violations G M edgesList)\<rparr>)" .


    from all_security_requirements_fulfilled_mono_stateful_policy_to_network_graph[OF valid_reqs_IFS_D[OF validReqs] subseteq validG' this]
    have "all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph (generate_valid_stateful_policy_IFSACS_2 G M edgesList))"
      by(simp add: generate_valid_stateful_policy_IFSACS_2_def)
    thus ?thesis .
  qed


  lemma generate_valid_stateful_policy_IFSACS_2_filter_compliant_stateful_ACS:
  assumes validReqs: "valid_reqs M"
        and     validG: "valid_graph G"
        and     high_level_policy_valid: "all_security_requirements_fulfilled M G"
        and     edgesList: "(set edgesList) \<subseteq> edges G"
        and     Tau: "\<T> = generate_valid_stateful_policy_IFSACS_2 G M edgesList"
  shows "\<forall>F\<in>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<T>). F \<subseteq> backflows (filternew_flows_state \<T>)"
    proof- 
      let ?filterACS = "set (filter_compliant_stateful_ACS G M edgesList)"
      let ?filterIFS = "set (filter_IFS_no_violations G M edgesList)"
      from all_security_requirements_fulfilled_ACS_D[OF high_level_policy_valid] have "all_security_requirements_fulfilled (get_ACS M) G" .

      from filter_compliant_stateful_ACS_correct[OF valid_reqs_ACS_D[OF validReqs] validG edgesList this] have 
        "\<forall>F\<in>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph  \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = ?filterACS\<rparr>). 
          F \<subseteq> backflows (?filterACS) - edges G"
        apply(simp)
        apply(simp add: backflows_minus_backflows[symmetric])
        by(simp add: filternew_flows_state_alt)
      hence "\<forall>F\<in>get_offending_flows (get_ACS M) \<lparr>nodes = nodes G, edges = edges G \<union> backflows (?filterACS)\<rparr>. F \<subseteq> backflows (?filterACS) - edges G"
        apply(simp add: stateful_policy_to_network_graph_def all_flows_def)
        using filter_compliant_stateful_ACS_subseteq_input by (metis (lifting, no_types) Un_absorb2 edgesList order_trans)
      from this validReqs have offending_filterACS_upperbound:
        "\<And>m. m \<in> set (get_ACS M) \<Longrightarrow> 
        \<Union>c_offending_flows m \<lparr>nodes = nodes G, edges = edges G \<union> backflows (?filterACS)\<rparr> \<subseteq> 
          backflows (?filterACS) - edges G"
        by(simp add: valid_reqs_def get_offending_flows_def, blast)

      from validG filter_compliant_stateful_ACS_subseteq_input edgesList have "valid_graph \<lparr>nodes = nodes G, edges = ?filterACS\<rparr>"
        by (metis graph.cases graph.select_convs(1) graph.select_convs(2) le_iff_sup valid_graph_remove_edges_union)
      from this backflows_valid have "valid_graph \<lparr>nodes = nodes G, edges = backflows (?filterACS)\<rparr>" by blast
      moreover have "valid_graph \<lparr>nodes = nodes G, edges = edges G\<rparr>" using validG by(case_tac G, simp)
      ultimately have validG1: "valid_graph \<lparr>nodes = nodes G, edges = edges G \<union> backflows (?filterACS)\<rparr>"
        using valid_graph_union_edges by blast
        
      from edgesList have edgesUnsimp: "edges G \<union> (?filterACS \<inter> ?filterIFS) = edges G"
        using filter_IFS_no_violations_subseteq_input filter_compliant_stateful_ACS_subseteq_input by blast

      --"We set up a ?REM that we use in the @{thm configured_SecurityInvariant.Un_set_offending_flows_bound_minus_subseteq} lemma"
      let ?REM = "(backflows (?filterACS) - backflows (?filterIFS)) - edges G"

      have REM_gives_desired_upper_bound: "(backflows (?filterACS) - edges G) - ?REM = backflows (?filterACS \<inter> ?filterIFS) - edges G"
        by(simp add: backflows_def, blast)

      have REM_gives_desired_edges: "(edges G \<union> backflows (?filterACS)) - ?REM = edges G \<union> (backflows (?filterACS \<inter> ?filterIFS))"
        by(simp add: backflows_def, blast)

      from validG have "finite (edges G)" using valid_graph_def by blast
      hence "finite (backflows ?filterACS)" using backflows_finite by (metis List.finite_set)
      hence finite1: "finite (backflows (?filterACS) - backflows (?filterIFS) - edges G)" by fast

      from configured_SecurityInvariant.Un_set_offending_flows_bound_minus_subseteq[where E'="?REM" and X="(backflows (?filterACS) - edges G)",
          OF _ validG1 offending_filterACS_upperbound, simplified REM_gives_desired_upper_bound REM_gives_desired_edges
          ] valid_reqs_ACS_D[OF validReqs, unfolded valid_reqs_def]
      have "\<And>m. m \<in> set (get_ACS M) \<Longrightarrow>
              \<forall>F\<in>c_offending_flows m \<lparr>nodes = nodes G, edges = edges G \<union> backflows (?filterACS \<inter> ?filterIFS)\<rparr>.
                  F \<subseteq> backflows (?filterACS \<inter> ?filterIFS) - edges G" by blast
      hence "\<forall>F\<in>get_offending_flows (get_ACS M)
         \<lparr>nodes = nodes G, edges = edges G \<union> (backflows (?filterACS \<inter> ?filterIFS))\<rparr>. F \<subseteq> backflows (?filterACS \<inter> ?filterIFS) - edges G"
       using get_offending_flows_def by fast
      hence "\<forall>F\<in>get_offending_flows (get_ACS M)
         \<lparr>nodes = nodes G, edges = edges G \<union> (?filterACS \<inter> ?filterIFS) \<union> (backflows (?filterACS \<inter> ?filterIFS))\<rparr>.
       F \<subseteq> backflows (?filterACS \<inter> ?filterIFS) - edges G"
        by(simp add: edgesUnsimp)
      hence "\<forall>F\<in>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = ?filterACS \<inter> ?filterIFS\<rparr>).
                F \<subseteq> backflows (?filterACS \<inter> ?filterIFS) - edges G"
        by(simp add: stateful_policy_to_network_graph_def all_flows_def)

      thus ?thesis
        apply(simp add: Tau generate_valid_stateful_policy_IFSACS_2_def)
        apply(simp add: filternew_flows_state_alt backflows_minus_backflows)
        by (metis inf_commute)
    qed
        




  theorem generate_valid_stateful_policy_IFSACS_2_stateful_policy_compliance:
  assumes validReqs: "valid_reqs M"
        and     validG: "valid_graph G"
        and     high_level_policy_valid: "all_security_requirements_fulfilled M G"
        and     edgesList: "(set edgesList) = edges G"
        and     Tau: "\<T> = generate_valid_stateful_policy_IFSACS_2 G M edgesList"
    shows "stateful_policy_compliance \<T> G M"
    proof -
      have 1: "valid_stateful_policy \<T>"
        apply(simp add: Tau)
        by(simp add: generate_valid_stateful_policy_IFSACS_2_valid_stateful_policy[OF validG edgesList])
      have 2: "valid_stateful_policy (generate_valid_stateful_policy_IFSACS G M edgesList)"
        by(simp add: generate_valid_stateful_policy_IFSACS_valid_stateful_policy[OF validG edgesList])
      have 3: "hosts \<T> = nodes G"
        apply(simp add: Tau)
        by(simp add: generate_valid_stateful_policy_IFSACS_2_select_simps(1))
      have 4: "flows_fix \<T> \<subseteq> edges G"
        apply(simp add: Tau)
        by(simp add: generate_valid_stateful_policy_IFSACS_2_select_simps(2))
      have 5: "all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<T>)"
        apply(simp add: Tau)
        using generate_valid_stateful_policy_IFSACS_2_all_security_requirements_fulfilled_IFS[OF validReqs validG high_level_policy_valid] edgesList by blast
      have 6: "\<forall>F\<in>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<T>). F \<subseteq> backflows (filternew_flows_state \<T>)"
        using generate_valid_stateful_policy_IFSACS_2_filter_compliant_stateful_ACS[OF 
            validReqs validG high_level_policy_valid]
        Tau edgesList by auto

    from 1 2 3 4 5 6 validReqs high_level_policy_valid validG
    show ?thesis
    unfolding stateful_policy_compliance_def by simp
  qed





  text{*
    If there are no IFS requirements and the ACS requirements cause no side effects,
    effectively, the graph can be considered as undirected graph! 
  *}
  lemma generate_valid_stateful_policy_IFSACS_2_noIFS_noACSsideeffects_imp_fullgraph:
  assumes validReqs: "valid_reqs M"
        and     validG: "valid_graph G"
        and     high_level_policy_valid: "all_security_requirements_fulfilled M G"
        and     edgesList: "(set edgesList) = edges G"
        and     no_ACS_sideeffects: "\<forall>F \<in> get_offending_flows (get_ACS M) \<lparr>nodes = nodes G, edges = edges G \<union> backflows (edges G)\<rparr>. F \<subseteq> (backflows (edges G)) - (edges G)"
        and     no_IFS: "get_IFS M = []"
  shows "stateful_policy_to_network_graph (generate_valid_stateful_policy_IFSACS_2 G M edgesList) = undirected G"
  proof -
    from filter_IFS_no_violations_accu_no_IFS[OF valid_reqs_IFS_D[OF validReqs] validG no_IFS] edgesList
      have "filter_IFS_no_violations G M edgesList = rev edgesList"
      by(simp add: filter_IFS_no_violations_def)
    from this filter_compliant_stateful_ACS_subseteq_input have flows_state_IFS: "flows_state (generate_valid_stateful_policy_IFSACS_2 G M edgesList) = set (filter_compliant_stateful_ACS G M edgesList)"
      by(auto simp add: generate_valid_stateful_policy_IFSACS_2_def)

    have flowsfix: "flows_fix (generate_valid_stateful_policy_IFSACS_2 G M edgesList) = edges G" by(simp add: generate_valid_stateful_policy_IFSACS_2_def)

    have hosts: "hosts (generate_valid_stateful_policy_IFSACS_2 G M edgesList) = nodes G" by(simp add: generate_valid_stateful_policy_IFSACS_2_def)

    from filter_compliant_stateful_ACS_accu_no_side_effects[OF valid_reqs_ACS_D[OF validReqs] validG no_ACS_sideeffects] have 
      "filter_compliant_stateful_ACS G M edgesList = rev [e\<leftarrow>edgesList . e \<notin> backflows (edges G)]"
      by(simp add: filter_compliant_stateful_ACS_def edgesList)
    hence filterACS: "set (filter_compliant_stateful_ACS G M edgesList) = edges G - (backflows (edges G))" using edgesList by force

    show ?thesis
      apply(simp add: undirected_backflows stateful_policy_to_network_graph_def all_flows_def)
      apply(simp add: hosts filterACS flows_state_IFS flowsfix)
      apply(simp add: backflows_minus_backflows)
      by fast
    qed
  lemma generate_valid_stateful_policy_IFSACS_noIFS_noACSsideeffects_imp_fullgraph:
  assumes validReqs: "valid_reqs M"
        and     validG: "valid_graph G"
        and     high_level_policy_valid: "all_security_requirements_fulfilled M G"
        and     edgesList: "(set edgesList) = edges G"
        and     no_ACS_sideeffects: "\<forall>F \<in> get_offending_flows (get_ACS M) \<lparr>nodes = nodes G, edges = edges G \<union> backflows (edges G)\<rparr>. F \<subseteq> (backflows (edges G)) - (edges G)"
        and     no_IFS: "get_IFS M = []"
  shows "stateful_policy_to_network_graph (generate_valid_stateful_policy_IFSACS G M edgesList) = undirected G"
  proof -
    from filter_IFS_no_violations_accu_no_IFS[OF valid_reqs_IFS_D[OF validReqs] validG no_IFS] edgesList
      have "filter_IFS_no_violations G M edgesList = rev edgesList"
      by(simp add: filter_IFS_no_violations_def)
    from this filter_compliant_stateful_ACS_subseteq_input have flows_state_IFS: "flows_state (generate_valid_stateful_policy_IFSACS G M edgesList) = set (filter_compliant_stateful_ACS G M (rev edgesList))"
      by(simp add: generate_valid_stateful_policy_IFSACS_def)

    have flowsfix: "flows_fix (generate_valid_stateful_policy_IFSACS G M edgesList) = edges G" by(simp add: generate_valid_stateful_policy_IFSACS_def)

    have hosts: "hosts (generate_valid_stateful_policy_IFSACS G M edgesList) = nodes G" by(simp add: generate_valid_stateful_policy_IFSACS_def)

    from filter_compliant_stateful_ACS_accu_no_side_effects[OF valid_reqs_ACS_D[OF validReqs] validG no_ACS_sideeffects] have 
      "filter_compliant_stateful_ACS G M (rev edgesList) = [e\<leftarrow>edgesList . e \<notin> backflows (edges G)]"
      apply(simp add: filter_compliant_stateful_ACS_def edgesList) by (metis rev_filter rev_swap)
    hence filterACS: "set (filter_compliant_stateful_ACS G M (rev edgesList)) = edges G - (backflows (edges G))" using edgesList by force

    show ?thesis
      apply(simp add: undirected_backflows stateful_policy_to_network_graph_def all_flows_def)
      apply(simp add: hosts filterACS flows_state_IFS flowsfix)
      apply(simp add: backflows_minus_backflows)
      by fast
    qed


(*


text{* In the following, we see failed attempts which try to prove that under composition, the IFS and ACS filtering is also maximal.
       I guess this does not hold in general. Need a counter example. *}

*)
(*Scratch*)
(*
  definition is_max_stateful_flows :: "'v::vertex graph \<Rightarrow> 'v SecurityInvariant_configured list \<Rightarrow> ('v \<times> 'v) set \<Rightarrow> ('v \<times> 'v) set \<Rightarrow> bool" where
    "is_max_stateful_flows G M Base S \<equiv> \<forall> e \<in> Base - S. \<not> stateful_policy_compliance \<lparr> hosts = nodes G, flows_fix = edges G, flows_state = S \<union> {e} \<rparr> G M"



  theorem "\<lbrakk> valid_reqs M; valid_graph G; all_security_requirements_fulfilled M G; (set edgesList) \<subseteq> edges G
    \<rbrakk> \<Longrightarrow>
        is_max_stateful_flows G M (set edgesList) (flows_state (generate_valid_stateful_policy_IFSACS_2 G M edgesList))"
  proof(induction edgesList)
  case Nil
    from Nil have "flows_state (generate_valid_stateful_policy_IFSACS_2 G M []) = {}" using generate_valid_stateful_policy_IFSACS_2_select_simps by fastforce
    thus ?case by(simp add: is_max_stateful_flows_def) 
  next
  case (Cons e Es)
    from all_security_requirements_fulfilled_ACS_D Cons.prems have all_fulfilled_ACS: "all_security_requirements_fulfilled (get_ACS M) G" by simp
    from all_security_requirements_fulfilled_IFS_D Cons.prems have all_fulfilled_IFS: "all_security_requirements_fulfilled (get_IFS M) G" by simp
    have validStateful: "\<And>e. e \<in> set Es \<Longrightarrow> valid_stateful_policy \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = insert e (flows_state (generate_valid_stateful_policy_IFSACS_2 G M Es))\<rparr>" sorry
    

    from Cons.prems(4) have "set Es \<subseteq> edges G" by simp

    let ?statefulEs = "flows_state (generate_valid_stateful_policy_IFSACS_2 G M Es)"

    from Cons.IH[OF Cons.prems(1) Cons.prems(2) Cons.prems(3) `set Es \<subseteq> edges G`] have
      "is_max_stateful_flows G M (set Es) (flows_state (generate_valid_stateful_policy_IFSACS_2 G M Es))" .
    from this have IH: "\<forall>e\<in>set Es - ?statefulEs.
       \<not> all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = insert e (?statefulEs)\<rparr>) \<or>
       \<not> (\<forall>F\<in>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = insert e (?statefulEs)\<rparr>).
           F \<subseteq> backflows (filternew_flows_state \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = insert e (?statefulEs)\<rparr>))"
      apply(simp add: is_max_stateful_flows_def)
      apply(simp add: stateful_policy_compliance_def)
      apply(simp add: Cons validStateful)
      done


    let ?statefulEs_e = "flows_state (generate_valid_stateful_policy_IFSACS_2 G M (e#Es))"

    thm filter_IFS_no_violations_maximal filter_compliant_stateful_ACS_maximal
    thm filter_IFS_no_violations_accu_maximal_induction[where accu="[]", simplified]
    thm filter_compliant_stateful_ACS_accu_induction_maximal[where accu="[]", simplified]

    have "\<forall>e\<in>insert e (set Es) - ?statefulEs_e.
       \<not> all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = insert e (?statefulEs_e)\<rparr>) \<or>
       \<not> (\<forall>F\<in>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = insert e (?statefulEs_e)\<rparr>).
           F \<subseteq> backflows (filternew_flows_state \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = insert e (?statefulEs_e)\<rparr>))"
    sorry

    from this show "is_max_stateful_flows G M (set (e # Es)) (flows_state (generate_valid_stateful_policy_IFSACS_2 G M (e # Es)))"
      apply(simp add: is_max_stateful_flows_def)
      by(simp add: stateful_policy_compliance_def)
oops
      



(*IDEA: induction oder edgesList?? needs assumption,. ....*)
  theorem generate_valid_stateful_policy_IFSACS_stateful_policy_compliance_maximum:
  assumes validReqs: "valid_reqs M"
      and     validG: "valid_graph G"
      and     high_level_policy_valid: "all_security_requirements_fulfilled M G"
      and     edgesList: "(set edgesList) = edges G"
      and     stateful: "stateful = flows_state (generate_valid_stateful_policy_IFSACS_2 G M edgesList)"
      and     addede: "e \<in> edges G - stateful"
  shows "\<not> stateful_policy_compliance \<lparr> hosts = nodes G, flows_fix = edges G, flows_state = stateful \<union> {e} \<rparr> G M"
  proof
    
    have G_unfold: "G = \<lparr>nodes = nodes G, edges = edges G\<rparr>" by(case_tac G, simp)
    hence G_fold: "\<lparr>nodes = nodes G, edges = edges G\<rparr> = G" by presburger
    from validG have validG': "valid_graph \<lparr>nodes = nodes G, edges = edges G\<rparr>" by(case_tac G, simp)
    let ?filterACS = "set (filter_compliant_stateful_ACS G M edgesList)"
    let ?filterIFS = "set (filter_IFS_no_violations G M edgesList)"

    from stateful have stateful':  "stateful = ?filterIFS \<inter> ?filterACS"
      by(simp add: generate_valid_stateful_policy_IFSACS_2_def)
    from this filter_IFS_no_violations_subseteq_input filter_compliant_stateful_ACS_subseteq_input edgesList have "stateful \<subseteq> edges G" by blast

    from validG addede `stateful \<subseteq> edges G` have valid_statefulG: 
      "valid_stateful_policy \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = insert e stateful\<rparr>"
      by(simp add: valid_stateful_policy_def valid_graph_def)

    assume ccontr: "stateful_policy_compliance \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = stateful \<union> {e}\<rparr> G M"
    hence IFS_cctr: "all_security_requirements_fulfilled (get_IFS M) 
      (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = insert e stateful\<rparr>)"
      and 
      ACS_cctr: "\<forall>F\<in>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = insert e stateful\<rparr>).
        F \<subseteq> backflows (filternew_flows_state \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = insert e stateful\<rparr>)"
      by(simp_all add: stateful_policy_compliance_def validG validReqs high_level_policy_valid valid_statefulG)
      (**use theorem to ...**)

    from get_offending_flows_union_mono[OF validReqs]
    have ACS_subset1:
        "\<Union> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = insert e stateful\<rparr>) \<subseteq>
         \<Union> get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = insert e ?filterACS\<rparr>)"
    apply(simp add: stateful_policy_to_network_graph_def all_flows_def)
    sorry

    have ACS_subset2:
      "backflows (filternew_flows_state \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = insert e stateful\<rparr>) \<subseteq> 
       backflows (filternew_flows_state \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = ?filterACS \<union> {e}\<rparr>)"
      apply(simp add: backflows_subseteq[symmetric])
      apply(simp add: stateful' filternew_flows_state_alt)
      by auto
    
    thm ACS_cctr ACS_subset1 ACS_subset2 

    thm filter_IFS_no_violations_accu_maximal_induction[where accu="[]", simplified]
    thm filter_compliant_stateful_ACS_accu_induction_maximal[where accu="[]", simplified]

    from filter_IFS_no_violations_maximal[OF valid_reqs_IFS_D[OF validReqs] validG edgesList] have IFS_max:
      "\<forall>e\<in>edges G - ?filterIFS.
        \<not> all_security_requirements_fulfilled (get_IFS M)
            (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = {e} \<union> ?filterIFS\<rparr>)" by metis

    from filter_compliant_stateful_ACS_maximal[OF valid_reqs_ACS_D[OF validReqs] validG' edgesList, where stateful="?filterACS"] have ACS_max:
      "\<forall>e\<in>edges G - (?filterACS \<union> {e \<in> edges G. e \<in> backflows (edges G)}).
     \<not> \<Union>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = ?filterACS \<union> {e}\<rparr>)
        \<subseteq> backflows (filternew_flows_state \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = ?filterACS \<union> {e}\<rparr>)"
      by(simp add: G_fold)

    show "False"
  oops













(**test**)




  definition generate_valid_stateful_policy_IFSACS_3 :: "'v::vertex set \<Rightarrow> 'v SecurityInvariant_configured list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 'v stateful_policy" where
    "generate_valid_stateful_policy_IFSACS_3 V M edgesList \<equiv> (let filterIFS = filter_IFS_no_violations \<lparr>nodes = V, edges = set edgesList\<rparr> M edgesList in
        (let G' = \<lparr> nodes = V, edges = set edgesList \<union> set filterIFS \<rparr> in 
        (let filterACS = filter_compliant_stateful_ACS G' M (edgesList @ filterIFS) in \<lparr> hosts = V, flows_fix = edges G', flows_state = set filterACS \<rparr>)))"

  text{*It does NOT hold that all security requirements are fulfilled for G'. Therefore, this algorithm does not produce a correct solution. *}

  thm filter_compliant_stateful_ACS_accu_correct_induction[where accu="[]", simplified]
  thm filter_compliant_stateful_ACS_correct

  theorem generate_valid_stateful_policy_IFSACS_stateful_policy_compliance_maximum:
  assumes validReqs: "valid_reqs M"
      and     validG: "valid_graph G"
      and     high_level_policy_valid: "all_security_requirements_fulfilled M G"
      and     edgesList: "(set edgesList) = edges G"
      and     stateful: "stateful = flows_state (generate_valid_stateful_policy_IFSACS G M edgesList)"
      and     addede: "e \<in> edges G - stateful"
  shows "\<not> stateful_policy_compliance \<lparr> hosts = nodes G, flows_fix = edges G, flows_state = stateful \<union> {e} \<rparr> G M"
  proof -
    from validG have validG': "valid_graph \<lparr>nodes = nodes G, edges = edges G\<rparr>" by(case_tac G, simp)

    let ?filter_IFS = "(filter_IFS_no_violations G M edgesList)"
    from stateful have stateful_simp: 
      "stateful = set (filter_compliant_stateful_ACS G M (?filter_IFS))" by(simp add: generate_valid_stateful_policy_IFSACS_def)
    hence stateful_subset_filterIFS: "stateful \<subseteq> set ?filter_IFS" using filter_compliant_stateful_ACS_subseteq_input by blast
    
    let ?IFSviolators = "edges G - set ?filter_IFS"
    from filter_IFS_no_violations_maximal[OF valid_reqs_IFS_D[OF validReqs] validG edgesList] have
      "\<forall>e \<in> ?IFSviolators. \<not> all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = {e} \<union> set ?filter_IFS\<rparr>)" by metis
    from this addede have 
      "stateful = set ?filter_IFS \<Longrightarrow> \<not> all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = stateful \<union> {e}\<rparr>)" by simp

    (* from filter_IFS_no_violations_maximal_allsubsets[OF valid_reqs_IFS_D[OF validReqs] validG edgesList] have
      "\<forall>E \<subseteq> edges G - set ?filter_IFS. E \<noteq> {} \<longrightarrow> \<not> all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = E \<union> set ?filter_IFS\<rparr>)" by metis
    hence filter_IFS_max_rule:
      "\<And>E. E \<subseteq> edges G - set ?filter_IFS \<Longrightarrow> E \<noteq> {} \<Longrightarrow> \<not> all_security_requirements_fulfilled (get_IFS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = E \<union> set ?filter_IFS\<rparr>)" by metis*)

    let ?ACSviolators = "edges G - (set (filter_compliant_stateful_ACS \<lparr>nodes = nodes G, edges = edges G\<rparr> M edgesList) \<union> {e \<in> edges G. e \<in> backflows (edges G)})"
    from filter_compliant_stateful_ACS_maximal[OF valid_reqs_ACS_D[OF validReqs] validG' edgesList] have
      "\<And> statefulACS. statefulACS = set (filter_compliant_stateful_ACS \<lparr>nodes = nodes G, edges = edges G\<rparr> M edgesList) \<Longrightarrow>
      \<forall> e \<in> ?ACSviolators.
        \<not> \<Union>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = statefulACS \<union> {e}\<rparr>) \<subseteq> 
              backflows (filternew_flows_state \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = statefulACS \<union> {e}\<rparr>)"
        by simp
    (*\<dots>*)

    from edgesList have filterIFS_subset_edges: "set (filter_IFS_no_violations G M edgesList) \<subseteq> edges G" by (metis filter_IFS_no_violations_subseteq_input)
    from stateful_simp[unfolded filter_compliant_stateful_ACS_def] have "stateful = set (filter_compliant_stateful_ACS_accu \<lparr>nodes = nodes G, edges = edges G\<rparr> M [] (filter_IFS_no_violations G M edgesList))"
      by(case_tac G, simp)

    from filter_compliant_stateful_ACS_accu_induction_maximal[where accu="[]" and E="edges G" and V="nodes G" and stateful="stateful" and edgesList="?filter_IFS", simplified, 
        OF valid_reqs_ACS_D[OF validReqs] validG' filterIFS_subset_edges this]
    have "\<forall>e\<in>edges G - (set (filter_IFS_no_violations G M edgesList) \<union> {e \<in> edges G. e \<in> backflows (edges G)}).
     \<not> \<Union>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = {e}\<rparr>) \<subseteq> backflows (filternew_flows_state \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = {e}\<rparr>) \<Longrightarrow>
      \<forall>e\<in>edges G - (stateful \<union> {e \<in> edges G. e \<in> backflows (edges G)}).
      \<not> \<Union>get_offending_flows (get_ACS M) (stateful_policy_to_network_graph \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = insert e stateful\<rparr>) \<subseteq> backflows (filternew_flows_state \<lparr>hosts = nodes G, flows_fix = edges G, flows_state = insert e stateful\<rparr>)"
    .

    show ?thesis
  oops

*)
end
