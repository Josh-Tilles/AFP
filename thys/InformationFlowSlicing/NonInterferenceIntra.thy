header {* \isaheader{Slicing guarantees IFC Noninterference} *}

theory NonInterferenceIntra imports 
  "../Slicing/StaticIntra/Slice" 
  "../Slicing/Basic/CFGExit_wf"
begin

section {* Assumptions of this Approach *}

text {*
Classical IFC noninterference, a special case of a noninterference
definition using partial equivalence relations (per)
\cite{SabelfeldS:01}, partitions the variables (i.e.\ locations) into
security levels. Usually, only levels for secret or high, written
@{text H}, and public or low, written @{text L}, variables are
used. Basically, a program that is noninterferent has to fulfil one
basic property: executing the program in two different initial states
that may differ in the values of their @{text H}-variables yields two
final states that again only differ in the values of their 
@{text H}-variables; thus the values of the @{text H}-variables did not
influence those of the @{text L}-variables.

Every per-based approach makes certain
assumptions: (i) all \mbox{@{text H}-variables} are defined at the
beginning of the program, (ii) all @{text L}-variables are observed (or
used in our terms) at the end and (iii) every variable is either
@{text H} or @{text L}. This security label is fixed for a variable
and can not be altered during a program run. Thus, we have to extend 
the prerequisites of the slicing framework in \cite{Wasserrab:08} accordingly
in a new locale:

*}

locale NonInterferenceIntraGraph = 
  BackwardSlice sourcenode targetnode kind valid_edge Entry Def Use state_val 
  backward_slice +
  CFGExit_wf sourcenode targetnode kind valid_edge Entry Def Use state_val Exit
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and backward_slice :: "'node \<Rightarrow> 'node set" 
  and sem :: "'com \<Rightarrow> 'state \<Rightarrow> 'com \<Rightarrow> 'state \<Rightarrow> bool" 
    ("((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [0,0,0,0] 81)
  and identifies :: "'node \<Rightarrow> 'com \<Rightarrow> bool" ("_ \<triangleq> _" [51, 0] 80)
  and Exit :: "'node" ("'('_Exit'_')") +
  fixes H :: "'var set"
  fixes L :: "'var set"
  fixes High :: "'node"  ("'('_High'_')")
  fixes Low :: "'node"   ("'('_Low'_')")
  assumes Entry_edge_Exit_or_High:
  "\<lbrakk>valid_edge a; sourcenode a = (_Entry_)\<rbrakk> 
    \<Longrightarrow> targetnode a = (_Exit_) \<or> targetnode a = (_High_)"
  and High_target_Entry_edge:
  "\<exists>a. valid_edge a \<and> sourcenode a = (_Entry_) \<and> targetnode a = (_High_) \<and>
       kind a = (\<lambda>s. True)\<^isub>\<surd>"
  and Entry_predecessor_of_High:
  "\<lbrakk>valid_edge a; targetnode a = (_High_)\<rbrakk> \<Longrightarrow> sourcenode a = (_Entry_)"
  and Exit_edge_Entry_or_Low: "\<lbrakk>valid_edge a; targetnode a = (_Exit_)\<rbrakk> 
    \<Longrightarrow> sourcenode a = (_Entry_) \<or> sourcenode a = (_Low_)"
  and Low_source_Exit_edge:
  "\<exists>a. valid_edge a \<and> sourcenode a = (_Low_) \<and> targetnode a = (_Exit_) \<and> 
       kind a = (\<lambda>s. True)\<^isub>\<surd>"
  and Exit_successor_of_Low:
  "\<lbrakk>valid_edge a; sourcenode a = (_Low_)\<rbrakk> \<Longrightarrow> targetnode a = (_Exit_)"
  and DefHigh: "Def (_High_) = H" 
  and UseHigh: "Use (_High_) = H"
  and UseLow: "Use (_Low_) = L"
  and HighLowDistinct: "H \<inter> L = {}"
  and HighLowUNIV: "H \<union> L = UNIV"
  and Low_neq_Exit:"(_Low_) \<noteq> (_Exit_)"

begin

lemmas [simp] = Low_neq_Exit Low_neq_Exit[symmetric]


lemma Entry_path_High_path:
  assumes "(_Entry_) -as\<rightarrow>* n" and "inner_node n"
  obtains a' as' where "as = a'#as'" and "(_High_) -as'\<rightarrow>* n" 
  and "kind a' = (\<lambda>s. True)\<^isub>\<surd>"
proof(atomize_elim)
  from `(_Entry_) -as\<rightarrow>* n` `inner_node n`
  show "\<exists>a' as'. as = a'#as' \<and> (_High_) -as'\<rightarrow>* n \<and> kind a' = (\<lambda>s. True)\<^isub>\<surd>"
  proof(induct n'\<equiv>"(_Entry_)" as n rule:path.induct)
    case (Cons_path n'' as n' a n)
    from `n'' -as\<rightarrow>* n'` `inner_node n'` have "n'' \<noteq> (_Exit_)" 
      by(fastsimp simp:inner_node_def)
    with `valid_edge a` `sourcenode a = n` `n = (_Entry_)` `targetnode a = n''`
    have "n'' = (_High_)" by -(drule Entry_edge_Exit_or_High,auto)
    from High_target_Entry_edge
    obtain a' where "valid_edge a'" and "sourcenode a' = (_Entry_)"
      and "targetnode a' = (_High_)" and "kind a' = (\<lambda>s. True)\<^isub>\<surd>"
      by blast
    with `valid_edge a` `sourcenode a = n` `n = (_Entry_)` `targetnode a = n''`
      `n'' = (_High_)`
    have "a = a'" by(auto dest:edge_det)
    with `n'' -as\<rightarrow>* n'` `n'' = (_High_)` `kind a' = (\<lambda>s. True)\<^isub>\<surd>` show ?case by blast
  qed fastsimp
qed


lemma Exit_path_Low_path:
  assumes "n -as\<rightarrow>* (_Exit_)" and "inner_node n"
  obtains a' as' where "as = as'@[a']" and "n -as'\<rightarrow>* (_Low_)"
  and "kind a' = (\<lambda>s. True)\<^isub>\<surd>"
proof(atomize_elim)
  from `n -as\<rightarrow>* (_Exit_)`
  show "\<exists>as' a'. as = as'@[a'] \<and> n -as'\<rightarrow>* (_Low_) \<and> kind a' = (\<lambda>s. True)\<^isub>\<surd>"
  proof(induct as rule:rev_induct)
    case Nil
    with `inner_node n` show ?case by fastsimp
  next
    case (snoc a' as')
    from `n -as'@[a']\<rightarrow>* (_Exit_)`
    have "n -as'\<rightarrow>* sourcenode a'" and "valid_edge a'" and "targetnode a' = (_Exit_)"
      by(auto elim:path_split_snoc)
    { assume "sourcenode a' = (_Entry_)"
      with `n -as'\<rightarrow>* sourcenode a'` have "n = (_Entry_)"
	by(blast intro!:path_Entry_target)
      with `inner_node n` have False by(simp add:inner_node_def) }
    with `valid_edge a'` `targetnode a' = (_Exit_)` have "sourcenode a' = (_Low_)"
      by(blast dest!:Exit_edge_Entry_or_Low)
    from Low_source_Exit_edge
    obtain ax where "valid_edge ax" and "sourcenode ax = (_Low_)"
      and "targetnode ax = (_Exit_)" and "kind ax = (\<lambda>s. True)\<^isub>\<surd>"
      by blast
    with `valid_edge a'` `targetnode a' = (_Exit_)` `sourcenode a' = (_Low_)`
    have "a' = ax" by(fastsimp intro:edge_det)
    with `n -as'\<rightarrow>* sourcenode a'` `sourcenode a' = (_Low_)` `kind ax = (\<lambda>s. True)\<^isub>\<surd>`
    show ?case by blast
  qed
qed


lemma not_Low_High: "V \<notin> L \<Longrightarrow> V \<in> H"
  using HighLowUNIV
  by fastsimp

lemma not_High_Low: "V \<notin> H \<Longrightarrow> V \<in> L"
  using HighLowUNIV
  by fastsimp


section {* Low Equivalence *}

text {*
In classical noninterference, an external observer can only see public values,
in our case the @{text L}-variables. If two states agree in the values of all 
@{text L}-variables, these states are indistinguishable for him. 
\emph{Low equivalence} groups those states in an equivalence class using 
the relation @{text "\<approx>\<^isub>L"}:
*}

definition lowEquivalence :: "'state \<Rightarrow> 'state \<Rightarrow> bool" (infixl "\<approx>\<^isub>L" 50)
  where "s \<approx>\<^isub>L s' \<equiv> \<forall>V \<in> L. state_val s V = state_val s' V"

text {* The following lemmas connect low equivalent states with
relevant variables as necessary in the correctness proof for slicing. *}

lemma relevant_vars_Entry:
  assumes "V \<in> rv n\<^isub>c (_Entry_)" and "(_High_) \<notin> backward_slice n\<^isub>c"
  shows "V \<in> L"
proof -
  from `V \<in> rv n\<^isub>c (_Entry_)` obtain as n' where "(_Entry_) -as\<rightarrow>* n'"
    and "n' \<in> backward_slice n\<^isub>c" and "V \<in> Use n'"
    and "\<forall>nx \<in> set(sourcenodes as). V \<notin> Def nx" by(erule rvE)
  from `(_Entry_) -as\<rightarrow>* n'` have "valid_node n'" by(rule path_valid_node)
  thus ?thesis
  proof(cases n' rule:valid_node_cases)
    case Entry
    with `V \<in> Use n'` have False by(simp add:Entry_empty)
    thus ?thesis by simp
  next
    case Exit
    with `V \<in> Use n'` have False by(simp add:Exit_empty)
    thus ?thesis by simp
  next
    case inner
    with `(_Entry_) -as\<rightarrow>* n'` obtain a' as' where "as = a'#as'"
      and "(_High_) -as'\<rightarrow>* n'" by -(erule Entry_path_High_path)
    from `(_Entry_) -as\<rightarrow>* n'` `as = a'#as'`
    have "sourcenode a' = (_Entry_)" by(fastsimp elim:path.cases)
    show ?thesis
    proof(cases "as' = []")
      case True
      with `(_High_) -as'\<rightarrow>* n'` have "n' = (_High_)" by fastsimp
      with `n' \<in> backward_slice n\<^isub>c` `(_High_) \<notin> backward_slice n\<^isub>c`
      have False by simp
      thus ?thesis by simp
    next
      case False
      with `(_High_) -as'\<rightarrow>* n'` have "hd (sourcenodes as') = (_High_)"
	by(rule path_sourcenode)
      from False have "hd (sourcenodes as') \<in> set (sourcenodes as')"
	by(fastsimp intro:hd_in_set simp:sourcenodes_def)
      with `as = a'#as'` have "hd (sourcenodes as') \<in> set (sourcenodes as)"
	by(simp add:sourcenodes_def)
      with `hd (sourcenodes as') = (_High_)` `\<forall>nx \<in> set(sourcenodes as). V \<notin> Def nx`
      have "V \<notin> Def (_High_)" by fastsimp
      hence "V \<notin> H" by(simp add:DefHigh)
      thus ?thesis by(rule not_High_Low)
    qed
  qed
qed



lemma lowEquivalence_relevant_nodes_Entry:
  assumes "s \<approx>\<^isub>L s'" and "(_High_) \<notin> backward_slice n\<^isub>c"
  shows "\<forall>V \<in> rv n\<^isub>c (_Entry_). state_val s V = state_val s' V"
proof
  fix V assume "V \<in> rv n\<^isub>c (_Entry_)"
  with `(_High_) \<notin> backward_slice n\<^isub>c` have "V \<in> L" by -(rule relevant_vars_Entry)
  with `s \<approx>\<^isub>L s'` show "state_val s V = state_val s' V" by(simp add:lowEquivalence_def)
qed



lemma rv_Low_Use_Low:
  "\<lbrakk>n -as\<rightarrow>* (_Low_); n -as'\<rightarrow>* (_Low_);
    \<forall>V \<in> rv (_Low_) n. state_val s V = state_val s' V;
    preds (slice_kinds (_Low_) as) s; preds (slice_kinds (_Low_) as') s'\<rbrakk>
  \<Longrightarrow> \<forall>V \<in> Use (_Low_). state_val (transfers (slice_kinds (_Low_) as) s) V =
                       state_val (transfers (slice_kinds (_Low_) as') s') V"
proof(induct n as n\<equiv>"(_Low_)" arbitrary:as' s s' rule:path.induct)
  case (empty_path n)
  { fix V assume "V \<in> Use (_Low_)"
    moreover
    from `valid_node n` `n = (_Low_)` have "(_Low_) -[]\<rightarrow>* (_Low_)"
      by(fastsimp intro:path.empty_path)
    moreover
    from `valid_node n` `n = (_Low_)` have "(_Low_) \<in> backward_slice (_Low_)"
      by(fastsimp intro:refl)
    ultimately have "V \<in> rv (_Low_) n" using `n = (_Low_)`
      by(fastsimp intro:rvI simp:sourcenodes_def) }
  hence "\<forall>V \<in> Use (_Low_). V \<in> rv (_Low_) n" by simp
  from `n -as'\<rightarrow>* (_Low_)` `n = (_Low_)` have "as' = []"
  proof(induct n as' n'\<equiv>"(_Low_)" rule:path.induct)
    case (Cons_path n'' as n' a n)
    from `valid_edge a` `sourcenode a = n` `n = (_Low_)`
    have "targetnode a = (_Exit_)" by -(rule Exit_successor_of_Low,simp+)
    with `targetnode a = n''` `n'' -as\<rightarrow>* n'`
    have "n' = (_Exit_)" by -(rule path_Exit_source,fastsimp)
    with `n' = (_Low_)` have False by simp
    thus ?case by simp
  qed simp
  with `\<forall>V \<in> Use (_Low_). V \<in> rv (_Low_) n` 
    `\<forall>V\<in>rv (_Low_) n. state_val s V = state_val s' V`
  show ?case by(auto simp:slice_kinds_def)
next
  case (Cons_path n'' as n' a n)
  note IH = `\<And>as' s s'. \<lbrakk>n'' -as'\<rightarrow>* (_Low_); 
    \<forall>V\<in>rv (_Low_) n''. state_val s V = state_val s' V;
    preds (slice_kinds (_Low_) as) s; preds (slice_kinds (_Low_) as') s'; 
    n' = (_Low_)\<rbrakk>
    \<Longrightarrow> \<forall>V\<in>Use (_Low_). state_val (transfers (slice_kinds (_Low_) as) s) V =
                       state_val (transfers (slice_kinds (_Low_) as') s') V`
  show ?case
  proof(cases as')
    case Nil
    with `n -as'\<rightarrow>* (_Low_)` have "n = (_Low_)" by fastsimp
    with `valid_edge a` `sourcenode a = n` have "targetnode a = (_Exit_)"
      by -(rule Exit_successor_of_Low,simp+)
    from Low_source_Exit_edge obtain ax where "valid_edge ax"
      and "sourcenode ax = (_Low_)" and "targetnode ax = (_Exit_)"
      and "kind ax = (\<lambda>s. True)\<^isub>\<surd>" by blast
    from `valid_edge a` `sourcenode a = n` `n = (_Low_)` `targetnode a = (_Exit_)`
      `valid_edge ax` `sourcenode ax = (_Low_)` `targetnode ax = (_Exit_)`
    have "a = ax" by(fastsimp dest:edge_det)
    with `kind ax = (\<lambda>s. True)\<^isub>\<surd>` have "kind a = (\<lambda>s. True)\<^isub>\<surd>" by simp
    with `targetnode a = (_Exit_)` `targetnode a = n''` `n'' -as\<rightarrow>* n'`
    have "n' = (_Exit_)" by -(rule path_Exit_source,auto)
    with `n' = (_Low_)` have False by simp
    thus ?thesis by simp
  next
    case (Cons ax asx)
    with `n -as'\<rightarrow>* (_Low_)` have "n = sourcenode ax" and "valid_edge ax" 
      and "targetnode ax -asx\<rightarrow>* (_Low_)" by(auto elim:path_split_Cons)
    show ?thesis
    proof(cases "targetnode ax = n''")
      case True
      with `targetnode ax -asx\<rightarrow>* (_Low_)` have "n'' -asx\<rightarrow>* (_Low_)" by simp
      from `valid_edge ax` `valid_edge a` `n = sourcenode ax` `sourcenode a = n`
	True `targetnode a = n''` have "ax = a"	by(fastsimp intro:edge_det)
      from `preds (slice_kinds (_Low_) (a#as)) s` 
      have preds1:"preds (slice_kinds (_Low_) as) (transfer (slice_kind (_Low_) a) s)"
	by(simp add:slice_kinds_def)
      from `preds (slice_kinds (_Low_) as') s'` Cons `ax = a`
      have preds2:"preds (slice_kinds (_Low_) asx) 
	                 (transfer (slice_kind (_Low_) a) s')"
	by(simp add:slice_kinds_def)
      from `valid_edge a` `sourcenode a = n` `targetnode a = n''`
	`preds (slice_kinds (_Low_) (a#as)) s` `preds (slice_kinds (_Low_) as') s'`
	`ax = a` Cons `\<forall>V\<in>rv (_Low_) n. state_val s V = state_val s' V`
      have "\<forall>V\<in>rv (_Low_) n''. state_val (transfer (slice_kind (_Low_) a) s) V =
	                       state_val (transfer (slice_kind (_Low_) a) s') V"
	by -(rule rv_edge_slice_kinds,auto)
      from IH[OF `n'' -asx\<rightarrow>* (_Low_)` this preds1 preds2 `n' = (_Low_)`] 
	Cons `ax = a` show ?thesis by(simp add:slice_kinds_def)
    next
      case False
      with `valid_edge a` `valid_edge ax` `sourcenode a = n` `n = sourcenode ax`
	`targetnode a = n''` `preds (slice_kinds (_Low_) (a#as)) s`
	`preds (slice_kinds (_Low_) as') s'` Cons
	`\<forall>V\<in>rv (_Low_) n. state_val s V = state_val s' V`
      have False by -(rule rv_branching_edges_slice_kinds_False,auto)
      thus ?thesis by simp
    qed
  qed
qed


section {* The Correctness Proofs *}

text {*
In the following, we present two correctness proofs that slicing guarantees
IFC noninterference. In both theorems, 
@{text "(_High_) \<notin> backward_slice (_Low_)"} makes sure that no high variable
(which are all defined in @{text "(_High_)"}) can influence a low variable
(which are all used in @{text "(_Low_)"}).

First, a theorem regarding 
@{text "(_Entry_) -as\<rightarrow>* (_Exit_)"} paths in the control flow graph (CFG),
which agree to a complete program execution: *}

lemma nonInterferenceSecurity_path_to_Low:
  assumes "s \<approx>\<^isub>L s'" and "(_High_) \<notin> backward_slice (_Low_)" 
  and "(_Entry_) -as\<rightarrow>* (_Low_)" and "preds (kinds as) s"
  and "(_Entry_) -as'\<rightarrow>* (_Low_)" and "preds (kinds as') s'"
  shows "transfers (kinds as) s \<approx>\<^isub>L transfers (kinds as') s'"
proof -
  from `(_Entry_) -as\<rightarrow>* (_Low_)` `preds (kinds as) s` 
  obtain asx where "preds (slice_kinds (_Low_) asx) s"
    and "\<forall>V \<in> Use (_Low_). state_val(transfers (slice_kinds (_Low_) asx) s) V = 
                           state_val(transfers (kinds as) s) V"
    and "slice_edges (_Low_) as = slice_edges (_Low_) asx"
    and "(_Entry_) -asx\<rightarrow>* (_Low_)" by(erule fundamental_property_of_static_slicing)
  from `(_Entry_) -as'\<rightarrow>* (_Low_)` `preds (kinds as') s'` 
  obtain asx' where "preds (slice_kinds (_Low_) asx') s'"
    and "\<forall>V \<in> Use (_Low_). state_val (transfers (slice_kinds (_Low_) asx') s') V = 
                           state_val (transfers (kinds as') s') V"
    and "slice_edges (_Low_) as' = slice_edges (_Low_) asx'"
    and "(_Entry_) -asx'\<rightarrow>* (_Low_)" by(erule fundamental_property_of_static_slicing)
  from `s \<approx>\<^isub>L s'` `(_High_) \<notin> backward_slice (_Low_)`
  have "\<forall>V \<in> rv (_Low_) (_Entry_). state_val s V = state_val s' V" 
    by(rule lowEquivalence_relevant_nodes_Entry)
  with `(_Entry_) -asx\<rightarrow>* (_Low_)` `(_Entry_) -asx'\<rightarrow>* (_Low_)`
    `preds (slice_kinds (_Low_) asx) s` `preds (slice_kinds (_Low_) asx') s'`
  have "\<forall>V \<in> Use (_Low_). state_val (transfers (slice_kinds (_Low_) asx) s) V =
                          state_val (transfers (slice_kinds (_Low_) asx') s') V"
    by -(rule rv_Low_Use_Low,auto)
  with `\<forall>V \<in> Use (_Low_). state_val(transfers (slice_kinds (_Low_) asx) s) V = 
                          state_val(transfers (kinds as) s) V`
    `\<forall>V \<in> Use (_Low_). state_val (transfers (slice_kinds (_Low_) asx') s') V = 
                       state_val (transfers (kinds as') s') V`
  show ?thesis by(auto simp:lowEquivalence_def UseLow)
qed


theorem nonInterferenceSecurity_path:
  assumes "s \<approx>\<^isub>L s'" and "(_High_) \<notin> backward_slice (_Low_)" 
  and "(_Entry_) -as\<rightarrow>* (_Exit_)" and "preds (kinds as) s"
  and "(_Entry_) -as'\<rightarrow>* (_Exit_)" and "preds (kinds as') s'"
  shows "transfers (kinds as) s \<approx>\<^isub>L transfers (kinds as') s'"
proof -
  from `(_Entry_) -as\<rightarrow>* (_Exit_)` obtain x xs where "as = x#xs"
    and "(_Entry_) = sourcenode x" and "valid_edge x" 
    and "targetnode x -xs\<rightarrow>* (_Exit_)"
    apply(cases "as = []")
     apply(simp,drule empty_path_nodes,drule Entry_noteq_Exit,simp)
    by(erule path_split_Cons)
  from `valid_edge x` have "valid_node (targetnode x)" by simp
  hence "inner_node (targetnode x)"
  proof(cases rule:valid_node_cases)
    case Entry
    with `valid_edge x` have False by(rule Entry_target)
    thus ?thesis by simp
  next
    case Exit
    with `targetnode x -xs\<rightarrow>* (_Exit_)` have "xs = []"
      by -(rule path_Exit_source,simp)
    from Entry_Exit_edge obtain z where "valid_edge z"
      and "sourcenode z = (_Entry_)" and "targetnode z = (_Exit_)"
      and "kind z = (\<lambda>s. False)\<^isub>\<surd>" by blast
    from `valid_edge x` `valid_edge z` `(_Entry_) = sourcenode x` 
      `sourcenode z = (_Entry_)` Exit `targetnode z = (_Exit_)`
    have "x = z" by(fastsimp intro:edge_det)
    with `preds (kinds as) s` `as = x#xs` `xs = []` `kind z = (\<lambda>s. False)\<^isub>\<surd>` 
    have False by(simp add:kinds_def)
    thus ?thesis by simp
  qed simp
  with `targetnode x -xs\<rightarrow>* (_Exit_)` obtain x' xs' where "xs = xs'@[x']"
    and "targetnode x -xs'\<rightarrow>* (_Low_)" and "kind x' = (\<lambda>s. True)\<^isub>\<surd>"
    by(fastsimp elim:Exit_path_Low_path)
  with `(_Entry_) = sourcenode x` `valid_edge x`
  have "(_Entry_) -x#xs'\<rightarrow>* (_Low_)" by(fastsimp intro:Cons_path)
  from `as = x#xs` `xs = xs'@[x']` have "as = (x#xs')@[x']" by simp
  with `preds (kinds as) s` have "preds (kinds (x#xs')) s"
    by(simp add:kinds_def preds_split)
  from `(_Entry_) -as'\<rightarrow>* (_Exit_)` obtain y ys where "as' = y#ys"
    and "(_Entry_) = sourcenode y" and "valid_edge y" 
    and "targetnode y -ys\<rightarrow>* (_Exit_)"
    apply(cases "as' = []")
     apply(simp,drule empty_path_nodes,drule Entry_noteq_Exit,simp)
    by(erule path_split_Cons)
  from `valid_edge y` have "valid_node (targetnode y)" by simp
  hence "inner_node (targetnode y)"
  proof(cases rule:valid_node_cases)
    case Entry
    with `valid_edge y` have False by(rule Entry_target)
    thus ?thesis by simp
  next
    case Exit
    with `targetnode y -ys\<rightarrow>* (_Exit_)` have "ys = []"
      by -(rule path_Exit_source,simp)
    from Entry_Exit_edge obtain z where "valid_edge z"
      and "sourcenode z = (_Entry_)" and "targetnode z = (_Exit_)"
      and "kind z = (\<lambda>s. False)\<^isub>\<surd>" by blast
    from `valid_edge y` `valid_edge z` `(_Entry_) = sourcenode y` 
      `sourcenode z = (_Entry_)` Exit `targetnode z = (_Exit_)`
    have "y = z" by(fastsimp intro:edge_det)
    with `preds (kinds as') s'` `as' = y#ys` `ys = []` `kind z = (\<lambda>s. False)\<^isub>\<surd>` 
    have False by(simp add:kinds_def)
    thus ?thesis by simp
  qed simp
  with `targetnode y -ys\<rightarrow>* (_Exit_)` obtain y' ys' where "ys = ys'@[y']"
    and "targetnode y -ys'\<rightarrow>* (_Low_)" and "kind y' = (\<lambda>s. True)\<^isub>\<surd>"
    by(fastsimp elim:Exit_path_Low_path)
  with `(_Entry_) = sourcenode y` `valid_edge y`
  have "(_Entry_) -y#ys'\<rightarrow>* (_Low_)" by(fastsimp intro:Cons_path)
  from `as' = y#ys` `ys = ys'@[y']` have "as' = (y#ys')@[y']" by simp
  with `preds (kinds as') s'` have "preds (kinds (y#ys')) s'"
    by(simp add:kinds_def preds_split)
  from `s \<approx>\<^isub>L s'` `(_High_) \<notin> backward_slice (_Low_)`
    `(_Entry_) -x#xs'\<rightarrow>* (_Low_)` `preds (kinds (x#xs')) s`
    `(_Entry_) -y#ys'\<rightarrow>* (_Low_)` `preds (kinds (y#ys')) s'`
  have "transfers (kinds (x#xs')) s \<approx>\<^isub>L transfers (kinds (y#ys')) s'"
    by(rule nonInterferenceSecurity_path_to_Low)
  with `as = x#xs` `xs = xs'@[x']` `kind x' = (\<lambda>s. True)\<^isub>\<surd>`
    `as' = y#ys` `ys = ys'@[y']` `kind y' = (\<lambda>s. True)\<^isub>\<surd>`
  show ?thesis by(simp add:kinds_def transfers_split)
qed


end

text {* The second theorem assumes that we have a operational semantics,
whose evaluations are written @{text "\<langle>c,s\<rangle> \<Rightarrow> \<langle>c',s'\<rangle>"} and which conforms 
to the CFG. The correctness theorem then states that if no high variable
influenced a low variable and the initial states were low equivalent, the
reulting states are again low equivalent: *}


locale NonInterferenceIntra = 
  NonInterferenceIntraGraph sourcenode targetnode kind valid_edge Entry 
    Def Use state_val backward_slice sem identifies Exit H L High Low +
  BackwardSlice_wf sourcenode targetnode kind valid_edge Entry Def Use state_val 
    backward_slice sem identifies
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and backward_slice :: "'node \<Rightarrow> 'node set"
  and sem :: "'com \<Rightarrow> 'state \<Rightarrow> 'com \<Rightarrow> 'state \<Rightarrow> bool" 
    ("((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [0,0,0,0] 81)
  and identifies :: "'node \<Rightarrow> 'com \<Rightarrow> bool" ("_ \<triangleq> _" [51, 0] 80)
  and Exit :: "'node" ("'('_Exit'_')")
  and H :: "'var set" and L :: "'var set" 
  and High :: "'node"  ("'('_High'_')") and Low :: "'node"   ("'('_Low'_')") +
  fixes final :: "'com \<Rightarrow> bool"
  assumes final_edge_Low: "\<lbrakk>final c; n \<triangleq> c\<rbrakk> 
  \<Longrightarrow> \<exists>a. valid_edge a \<and> sourcenode a = n \<and> targetnode a = (_Low_) \<and> kind a = \<Up>id"
begin

text{* The following theorem needs the explicit edge from @{text "(_High_)"}
  to @{text n}. An approach using a @{text "init"} predicate for initial statements,
  being reachable from @{text "(_High_)"} via a @{text "(\<lambda>s. True)\<^isub>\<surd>"} edge,
  does not work as the same statement could be identified by several nodes, some
  initial, some not. E.g., in the program \texttt{while (True) Skip;;Skip}
  two nodes identify this inital statement: the initial node and the node
  within the loop (because of loop unrolling).*}

theorem nonInterferenceSecurity:
  assumes "s\<^isub>1 \<approx>\<^isub>L s\<^isub>2" and "(_High_) \<notin> backward_slice (_Low_)"
  and "valid_edge a" and "sourcenode a = (_High_)" and "targetnode a = n" 
  and "kind a = (\<lambda>s. True)\<^isub>\<surd>" and "n \<triangleq> c" and "final c'"
  and "\<langle>c,s\<^isub>1\<rangle> \<Rightarrow> \<langle>c',s\<^isub>1'\<rangle>" and "\<langle>c,s\<^isub>2\<rangle> \<Rightarrow> \<langle>c',s\<^isub>2'\<rangle>"
  shows "s\<^isub>1' \<approx>\<^isub>L s\<^isub>2'"
proof -
  from High_target_Entry_edge obtain ax where "valid_edge ax"
    and "sourcenode ax = (_Entry_)" and "targetnode ax = (_High_)"
    and "kind ax = (\<lambda>s. True)\<^isub>\<surd>" by blast
  from `n \<triangleq> c` `\<langle>c,s\<^isub>1\<rangle> \<Rightarrow> \<langle>c',s\<^isub>1'\<rangle>`
  obtain n\<^isub>1 as\<^isub>1 where "n -as\<^isub>1\<rightarrow>* n\<^isub>1" and "transfers (kinds as\<^isub>1) s\<^isub>1 = s\<^isub>1'"
    and "preds (kinds as\<^isub>1) s\<^isub>1" and "n\<^isub>1 \<triangleq> c'"
    by(fastsimp dest:fundamental_property)
  from `n -as\<^isub>1\<rightarrow>* n\<^isub>1` `valid_edge a` `sourcenode a = (_High_)` `targetnode a = n`
  have "(_High_) -a#as\<^isub>1\<rightarrow>* n\<^isub>1" by(rule Cons_path)
  from `final c'` `n\<^isub>1 \<triangleq> c'`
  obtain a\<^isub>1 where "valid_edge a\<^isub>1" and "sourcenode a\<^isub>1 = n\<^isub>1" 
    and "targetnode a\<^isub>1 = (_Low_)" and "kind a\<^isub>1 = \<Up>id" by(fastsimp dest:final_edge_Low)
  hence "n\<^isub>1 -[a\<^isub>1]\<rightarrow>* (_Low_)" by(fastsimp intro:path_edge)
  with `(_High_) -a#as\<^isub>1\<rightarrow>* n\<^isub>1` have "(_High_) -(a#as\<^isub>1)@[a\<^isub>1]\<rightarrow>* (_Low_)"
    by(rule path_Append)
  with `valid_edge ax` `sourcenode ax = (_Entry_)` `targetnode ax = (_High_)`
  have "(_Entry_) -ax#((a#as\<^isub>1)@[a\<^isub>1])\<rightarrow>* (_Low_)" by -(rule Cons_path)
  from `kind ax = (\<lambda>s. True)\<^isub>\<surd>` `kind a = (\<lambda>s. True)\<^isub>\<surd>` `preds (kinds as\<^isub>1) s\<^isub>1`
    `kind a\<^isub>1 = \<Up>id` have "preds (kinds (ax#((a#as\<^isub>1)@[a\<^isub>1]))) s\<^isub>1"
    by (simp add:kinds_def preds_split)
  from `n \<triangleq> c` `\<langle>c,s\<^isub>2\<rangle> \<Rightarrow> \<langle>c',s\<^isub>2'\<rangle>`
  obtain n\<^isub>2 as\<^isub>2 where "n -as\<^isub>2\<rightarrow>* n\<^isub>2" and "transfers (kinds as\<^isub>2) s\<^isub>2 = s\<^isub>2'"
    and "preds (kinds as\<^isub>2) s\<^isub>2" and "n\<^isub>2 \<triangleq> c'"
    by(fastsimp dest:fundamental_property)
  from `n -as\<^isub>2\<rightarrow>* n\<^isub>2` `valid_edge a` `sourcenode a = (_High_)` `targetnode a = n`
  have "(_High_) -a#as\<^isub>2\<rightarrow>* n\<^isub>2" by(rule Cons_path)
  from `final c'` `n\<^isub>2 \<triangleq> c'`
  obtain a\<^isub>2 where "valid_edge a\<^isub>2" and "sourcenode a\<^isub>2 = n\<^isub>2" 
    and "targetnode a\<^isub>2 = (_Low_)" and "kind a\<^isub>2 = \<Up>id" by(fastsimp dest:final_edge_Low)
  hence "n\<^isub>2 -[a\<^isub>2]\<rightarrow>* (_Low_)" by(fastsimp intro:path_edge)
  with `(_High_) -a#as\<^isub>2\<rightarrow>* n\<^isub>2` have "(_High_) -(a#as\<^isub>2)@[a\<^isub>2]\<rightarrow>* (_Low_)"
    by(rule path_Append)
  with `valid_edge ax` `sourcenode ax = (_Entry_)` `targetnode ax = (_High_)`
  have "(_Entry_) -ax#((a#as\<^isub>2)@[a\<^isub>2])\<rightarrow>* (_Low_)" by -(rule Cons_path)
  from `kind ax = (\<lambda>s. True)\<^isub>\<surd>` `kind a = (\<lambda>s. True)\<^isub>\<surd>` `preds (kinds as\<^isub>2) s\<^isub>2`
    `kind a\<^isub>2 = \<Up>id` have "preds (kinds (ax#((a#as\<^isub>2)@[a\<^isub>2]))) s\<^isub>2"
    by (simp add:kinds_def preds_split)
  from `s\<^isub>1 \<approx>\<^isub>L s\<^isub>2` `(_High_) \<notin> backward_slice (_Low_)`
    `(_Entry_) -ax#((a#as\<^isub>1)@[a\<^isub>1])\<rightarrow>* (_Low_)` `preds (kinds (ax#((a#as\<^isub>1)@[a\<^isub>1]))) s\<^isub>1`
    `(_Entry_) -ax#((a#as\<^isub>2)@[a\<^isub>2])\<rightarrow>* (_Low_)` `preds (kinds (ax#((a#as\<^isub>2)@[a\<^isub>2]))) s\<^isub>2`
  have "transfers (kinds (ax#((a#as\<^isub>1)@[a\<^isub>1]))) s\<^isub>1 \<approx>\<^isub>L 
        transfers (kinds (ax#((a#as\<^isub>2)@[a\<^isub>2]))) s\<^isub>2"
    by(rule nonInterferenceSecurity_path_to_Low)
  with `kind ax = (\<lambda>s. True)\<^isub>\<surd>` `kind a = (\<lambda>s. True)\<^isub>\<surd>` `kind a\<^isub>1 = \<Up>id` `kind a\<^isub>2 = \<Up>id`
    `transfers (kinds as\<^isub>1) s\<^isub>1 = s\<^isub>1'` `transfers (kinds as\<^isub>2) s\<^isub>2 = s\<^isub>2'`
  show ?thesis by(simp add:kinds_def transfers_split)
qed


end

end

