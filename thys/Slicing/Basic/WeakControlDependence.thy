header {* \isaheader{Weak control dependence} *}

theory WeakControlDependence imports PDG Postdomination begin

subsection {* Dynamic standard control dependence *}

subsubsection {* Definition and some lemmas *}

context StrongPostdomination begin

definition
  dyn_weak_control_dependence :: "'node \<Rightarrow> 'node \<Rightarrow> 'edge list \<Rightarrow> bool" 
  ("_ weakly controls _ via _" [51,0,0])
where dyn_weak_control_dependence_def:"n weakly controls n' via as \<equiv> 
    (\<exists>a a' as'. (as = a#as') \<and> (n' \<notin> set(sourcenodes as)) \<and> (n -as\<rightarrow>* n') \<and>
                   (n' strongly-postdominates (targetnode a)) \<and>
                   (valid_edge a') \<and> (sourcenode a' = n) \<and> 
                   (\<not> n' strongly-postdominates (targetnode a')))"


lemma Exit_not_dyn_weak_control_dependent:
  assumes control:"n weakly controls (_Exit_) via as" shows "False"
proof -
  from control obtain as a as' where path:"n -as\<rightarrow>* (_Exit_)" and as:"as = a#as'"
    and pd:"(_Exit_) postdominates (targetnode a)"
    by(auto simp:dyn_weak_control_dependence_def strong_postdominate_def)
  from path as have "n -[]@a#as'\<rightarrow>* (_Exit_)" by simp
  hence "valid_edge a" by(fastsimp dest:path_split)
  with pd show False by -(rule Exit_no_postdominator,auto)
qed

end

subsubsection {* Instantiate dynamic PDG *}

locale DynWeakControlDependencePDG = 
  StrongPostdomination sourcenode targetnode kind valid_edge Entry Exit +
  CFGExit_wf sourcenode targetnode kind valid_edge Entry Def Use state_val Exit
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and Exit :: "'node" ("'('_Exit'_')")

begin

lemma DynPDG_wcd:
  "DynPDG sourcenode targetnode kind valid_edge (_Entry_) 
          Def Use state_val (_Exit_) dyn_weak_control_dependence"
proof(unfold_locales)
  fix n n' as assume "n weakly controls n' via as"
  show "n' \<noteq> (_Exit_)"
  proof
    assume "n' = (_Exit_)"
    with `n weakly controls n' via as` show False
      by(fastsimp intro:Exit_not_dyn_weak_control_dependent)
  qed
next
  fix n n' as assume "n weakly controls n' via as"
  thus "n -as\<rightarrow>* n' \<and> as \<noteq> []"
    by(fastsimp simp:dyn_weak_control_dependence_def)
qed


end


subsection {* Static weak control dependence *}

subsubsection {* Definition and some lemmas *}

context StrongPostdomination begin

definition 
  weak_control_dependence :: "'node \<Rightarrow> 'node \<Rightarrow> bool" 
  ("_ weakly controls _" [51,0])
where weak_control_dependences_eq:
    "n weakly controls n' \<equiv> \<exists>as. n weakly controls n' via as"

lemma 
  weak_control_dependence_def:"n weakly controls n' = 
    (\<exists>a a' as. (n' \<notin> set(sourcenodes (a#as))) \<and> (n -a#as\<rightarrow>* n') \<and>
                   (n' strongly-postdominates (targetnode a)) \<and>
                   (valid_edge a') \<and> (sourcenode a' = n) \<and> 
                   (\<not> n' strongly-postdominates (targetnode a')))"
by(auto simp:weak_control_dependences_eq dyn_weak_control_dependence_def)


lemma Exit_not_weak_control_dependent:
  "n weakly controls (_Exit_) \<Longrightarrow> False"
by(auto simp:weak_control_dependences_eq 
        intro:Exit_not_dyn_weak_control_dependent)

end


subsubsection {* Instantiate static PDG *}

locale WeakControlDependencePDG = 
  StrongPostdomination sourcenode targetnode kind valid_edge Entry Exit +
  CFGExit_wf sourcenode targetnode kind valid_edge Entry Def Use state_val Exit
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and Exit :: "'node" ("'('_Exit'_')")

begin

lemma PDG_wcd:
  "PDG sourcenode targetnode kind valid_edge (_Entry_) 
       Def Use state_val (_Exit_) weak_control_dependence"
proof(unfold_locales)
  fix n n' assume "n weakly controls n'"
  show "n' \<noteq> (_Exit_)"
  proof
    assume "n' = (_Exit_)"
    with `n weakly controls n'` show False
      by(fastsimp intro:Exit_not_weak_control_dependent)
  qed
next
  fix n n' assume "n weakly controls n'"
  thus "\<exists>as. n -as\<rightarrow>* n' \<and> as \<noteq> []"
    by(fastsimp simp:weak_control_dependence_def)
qed

(*<*)
lemmas PDG_cdep_edge = PDG.PDG_cdep_edge[OF PDG_wcd]
lemmas PDG_path_Nil = PDG.PDG_path_Nil[OF PDG_wcd]
lemmas PDG_path_Append = PDG.PDG_path_Append[OF PDG_wcd]
lemmas PDG_path_CFG_path = PDG.PDG_path_CFG_path[OF PDG_wcd]
lemmas PDG_path_cdep = PDG.PDG_path_cdep[OF PDG_wcd]
lemmas PDG_path_ddep = PDG.PDG_path_ddep[OF PDG_wcd]
lemmas PDG_path_not_inner = PDG.PDG_path_not_inner[OF PDG_wcd]
lemmas PDG_path_Exit = PDG.PDG_path_Exit[OF PDG_wcd]


definition PDG_BS_w :: "'node \<Rightarrow> 'node set" ("PDG'_BS")
  where "PDG_BS n \<equiv> 
  PDG.PDG_BS sourcenode targetnode valid_edge Def Use weak_control_dependence n"

lemma [simp]: "PDG.PDG_BS sourcenode targetnode valid_edge Def Use 
  weak_control_dependence n = PDG_BS n"
  by(simp add:PDG_BS_w_def)

lemmas PDG_BS_def = PDG.PDG_BS_def[OF PDG_wcd,simplified]
lemmas PDG_BS_valid_node = PDG.PDG_BS_valid_node[OF PDG_wcd,simplified]
lemmas Exit_PDG_BS = PDG.Exit_PDG_BS[OF PDG_wcd,simplified]
(*>*)

end

end