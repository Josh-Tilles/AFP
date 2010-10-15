(*  Title:      JinjaThreads/Compiler/J1JVM.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Correctness of Stage: From intermediate language to JVM} *}

theory J1JVM imports J1JVMBisim begin

context J1_JVM_heap_base begin

declare \<tau>move1_\<tau>moves1.simps [simp del]

lemma bisim1_insync_Throw_exec:
  assumes bisim2: "P,e2,Suc V,h \<turnstile> (Throw ad, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
  shows "\<tau>Exec_movet_a P t (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, Suc (Suc (Suc (length (compE2 e1) + pc))), xcp) ([Addr ad], loc, 6 + length (compE2 e1) + length (compE2 e2), None)"
proof -
  from bisim2 have pc: "pc < length (compE2 e2)" and [simp]: "xs = loc" by(auto dest: bisim1_ThrowD)
  let ?pc = "6 + length (compE2 e1) + length (compE2 e2)"
  let ?stk = "Addr ad # drop (size stk - 0) stk"
  from bisim2 have "xcp = \<lfloor>ad\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
  thus ?thesis
  proof
    assume [simp]: "xcp = \<lfloor>ad\<rfloor>"
    have "\<tau>Exec_movet_a P t (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, Suc (Suc (Suc (length (compE2 e1) + pc))), \<lfloor>ad\<rfloor>) (?stk, loc, ?pc, None)"
    proof(rule \<tau>Exect1step[unfolded exec_move_def, OF exec_catch])
      from bisim1_xcp_Some_not_caught[OF bisim2[simplified], of "\<lambda>C M Ts T. compMb2" "Suc (Suc (Suc (length (compE2 e1))))" 0]
      have "match_ex_table (compP2 P) (cname_of h ad) (Suc (Suc (Suc (length (compE2 e1) + pc)))) (compxE2 e2 (Suc (Suc (Suc (length (compE2 e1))))) 0) = None"
	by(simp add: compP2_def)
      thus "match_ex_table (compP2 P) (cname_of h ad) (Suc (Suc (Suc (length (compE2 e1) + pc)))) (compxE2 (sync\<^bsub>V\<^esub> (e1) e2) 0 0) = \<lfloor>(6 + length (compE2 e1) + length (compE2 e2), 0)\<rfloor>"
	using pc
	by(auto simp add: compP2_def match_ex_table_append matches_ex_entry_def nat_number
                dest: match_ex_table_pc_length_compE2)
    qed(insert pc, auto intro: \<tau>move2xcp)
    thus ?thesis by simp
  next
    assume [simp]: "xcp = None"
    with bisim2 obtain pc'
      where "\<tau>Exec_movet_a P t e2 h (stk, loc, pc, None) ([Addr ad], loc, pc', \<lfloor>ad\<rfloor>)"
      and bisim': "P, e2, Suc V, h \<turnstile> (Throw ad, xs) \<leftrightarrow> ([Addr ad], loc, pc', \<lfloor>ad\<rfloor>)" and [simp]: "xs = loc"
      by(auto dest: bisim1_Throw_\<tau>Exec_movet)
    hence "\<tau>Exec_movet_a P t (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, Suc (Suc (Suc (length (compE2 e1) + pc))), None) ([Addr ad], loc, Suc (Suc (Suc (length (compE2 e1) + pc'))), \<lfloor>ad\<rfloor>)"
      by-(rule Insync_\<tau>ExectI)
    also let ?stk = "Addr ad # drop (size [Addr ad] - 0) [Addr ad]"
    from bisim' have pc': "pc' < length (compE2 e2)" by(auto dest: bisim1_ThrowD)
    have "\<tau>Exec_movet_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr ad], loc, Suc (Suc (Suc (length (compE2 e1) + pc'))), \<lfloor>ad\<rfloor>) (?stk, loc, ?pc, None)"
    proof(rule \<tau>Exect1step[unfolded exec_move_def, OF exec_catch])
      from bisim1_xcp_Some_not_caught[OF bisim', of "\<lambda>C M Ts T. compMb2" "Suc (Suc (Suc (length (compE2 e1))))" 0]
      have "match_ex_table (compP2 P) (cname_of h ad) (Suc (Suc (Suc (length (compE2 e1) + pc')))) (compxE2 e2 (Suc (Suc (Suc (length (compE2 e1))))) 0) = None"
	by(simp add: compP2_def)
      thus "match_ex_table (compP2 P) (cname_of h ad) (Suc (Suc (Suc (length (compE2 e1) + pc')))) (compxE2 (sync\<^bsub>V\<^esub> (e1) e2) 0 0) = \<lfloor>(6 + length (compE2 e1) + length (compE2 e2), 0)\<rfloor>"
	using pc'
	by(auto simp add: compP2_def match_ex_table_append matches_ex_entry_def nat_number
                dest: match_ex_table_pc_length_compE2)
    qed(insert pc', auto intro: \<tau>move2xcp)
    finally (tranclp_trans) show ?thesis by simp
  qed
qed

end

primrec sim12_size :: "('a, 'b) exp \<Rightarrow> nat"
  and sim12_sizes :: "('a, 'b) exp list \<Rightarrow> nat"
where
  "sim12_size (new C) = 0"
| "sim12_size (newA T\<lfloor>e\<rceil>) = Suc (sim12_size e)"
| "sim12_size (Cast T e) = Suc (sim12_size e)"
| "sim12_size (e instanceof T) = Suc (sim12_size e)"
| "sim12_size (e \<guillemotleft>bop\<guillemotright> e') = Suc (sim12_size e + sim12_size e')"
| "sim12_size (Val v) = 0"
| "sim12_size (Var V) = 0"
| "sim12_size (V := e) = Suc (sim12_size e)"
| "sim12_size (a\<lfloor>i\<rceil>) = Suc (sim12_size a + sim12_size i)"
| "sim12_size (a\<lfloor>i\<rceil> := e) = Suc (sim12_size a + sim12_size i + sim12_size e)"
| "sim12_size (a\<bullet>length) = Suc (sim12_size a)"
| "sim12_size (e\<bullet>F{D}) = Suc (sim12_size e)"
| "sim12_size (e\<bullet>F{D} := e') = Suc (sim12_size e + sim12_size e')"
| "sim12_size (e\<bullet>M(es)) = Suc (sim12_size e + sim12_sizes es)"
| "sim12_size ({V:T=vo; e}) = Suc (sim12_size e)"
| "sim12_size (sync\<^bsub>V\<^esub>(e) e') = Suc (sim12_size e + sim12_size e')"
| "sim12_size (insync\<^bsub>V\<^esub>(a) e) = Suc (sim12_size e)"
| "sim12_size (e;; e') = Suc (sim12_size e + sim12_size e')"
| "sim12_size (if (e) e1 else e2) = Suc (sim12_size e)"
| "sim12_size (while(b) c) = Suc (Suc (sim12_size b))"
| "sim12_size (throw e) = Suc (sim12_size e)"
| "sim12_size (try e catch(C V) e') = Suc (sim12_size e)"

| "sim12_sizes [] = 0"
| "sim12_sizes (e # es) = sim12_size e + sim12_sizes es"

lemma sim12_sizes_map_Val [simp]:
  "sim12_sizes (map Val vs) = 0"
by(induct vs) simp_all

lemma sim12_sizes_append [simp]:
  "sim12_sizes (es @ es') = sim12_sizes es + sim12_sizes es'"
by(induct es) simp_all

context JVM_heap_base begin

lemma \<tau>Exec_mover_length_compE2_conv [simp]:
  assumes pc: "pc \<ge> length (compE2 e)"
  shows "\<tau>Exec_mover ci P t e h (stk, loc, pc, xcp) s \<longleftrightarrow> s = (stk, loc, pc, xcp)"
proof
  assume "\<tau>Exec_mover ci P t e h (stk, loc, pc, xcp) s"
  thus "s = (stk, loc, pc, xcp)" using pc
    by induct(auto simp add: \<tau>exec_move_def)
qed auto

lemma \<tau>Exec_movesr_length_compE2_conv [simp]:
  assumes pc: "pc \<ge> length (compEs2 es)"
  shows "\<tau>Exec_movesr ci P t es h (stk, loc, pc, xcp) s \<longleftrightarrow> s = (stk, loc, pc, xcp)"
proof
  assume "\<tau>Exec_movesr ci P t es h (stk, loc, pc, xcp) s"
  thus "s = (stk, loc, pc, xcp)" using pc
    by induct(auto simp add: \<tau>exec_moves_def)
qed auto

end

context J1_JVM_heap_base begin

lemma assumes wf: "wf_J1_prog P"
  defines [simp]: "sim_move \<equiv> \<lambda>e e'. if sim12_size e' < sim12_size e then \<tau>Exec_mover_a else \<tau>Exec_movet_a"
  and [simp]: "sim_moves \<equiv> \<lambda>es es'. if sim12_sizes es' < sim12_sizes es then \<tau>Exec_movesr_a else \<tau>Exec_movest_a"
  shows exec_instr_simulates_red1:
  "\<lbrakk> P, E, n, h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp); P,t \<turnstile>1 \<langle>e, (h, xs)\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle> \<rbrakk>
  \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P, E, n, h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
      (if \<tau>move1 P h e
       then h = h' \<and> sim_move e e' P t E h (stk, loc, pc, xcp) (stk'', loc'', pc'', xcp'')
       else \<exists>pc' stk' loc' xcp'. \<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) (stk', loc', pc', xcp') \<and>
                                 exec_move_a P t E h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', pc'', xcp'') \<and>
                                 \<not> \<tau>move2 (compP2 P) h stk' E pc' xcp' \<and>
                                 (call1 e = None \<or> no_call2 E pc \<or> pc' = pc \<and> stk' = stk \<and> loc' = loc \<and> xcp' = xcp))"
  (is "\<lbrakk> _; _ \<rbrakk>
       \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. _ \<and> ?exec ta E e e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''")

  and exec_instr_simulates_reds1:  
  "\<lbrakk> P, Es, n, h \<turnstile> (es, xs) [\<leftrightarrow>] (stk, loc, pc, xcp); P,t \<turnstile>1 \<langle>es, (h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es', (h', xs')\<rangle> \<rbrakk>
  \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P, Es, n, h' \<turnstile> (es', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'') \<and>
      (if \<tau>moves1 P h es
       then h = h' \<and> sim_moves es es' P t Es h (stk, loc, pc, xcp) (stk'', loc'', pc'', xcp'')
       else \<exists>pc' stk' loc' xcp'. \<tau>Exec_movesr_a P t Es h (stk, loc, pc, xcp) (stk', loc', pc', xcp') \<and>
                                 exec_moves_a P t Es h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', pc'', xcp'') \<and> 
                                 \<not> \<tau>moves2 (compP2 P) h stk' Es pc' xcp' \<and>
                                 (calls1 es = None \<or> no_calls2 Es pc \<or> pc' = pc \<and> stk' = stk \<and> loc' = loc \<and> xcp' = xcp))"
  (is "\<lbrakk> _; _ \<rbrakk>
       \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. _ \<and> ?execs ta Es es es' h stk loc pc xcp h' pc'' stk'' loc'' xcp''")
proof(induct arbitrary: e' h' xs' Env T Env' T' and es' h' xs' Env Ts Env' Ts' rule: bisim1_bisims1_inducts_split)
  case (bisim1Call1 obj n obj' xs stk loc pc xcp ps M')
  note IHobj = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>obj',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,obj,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta obj obj' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note IHparam = `\<And>xs es' h' xs' Env Ts Env' Ts'. P,t \<turnstile>1 \<langle>ps,(h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,ps,n,h' \<turnstile> (es', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'') \<and>
                  ?execs ta ps ps es' h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,obj,n,h \<turnstile> (obj', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,ps,n,h \<turnstile> (ps, xs) [\<leftrightarrow>] ([], xs, 0, None)`
  note red = `P,t \<turnstile>1 \<langle>obj'\<bullet>M'(ps),(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from red show ?case
  proof(cases)
    case (Call1Obj E')
    note [simp] = `e' = E'\<bullet>M'(ps)`
      and red = `P,t \<turnstile>1 \<langle>obj',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h obj' = \<tau>move1 P h (obj'\<bullet>M'(ps))" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from red have "call1 (obj'\<bullet>M'(ps)) = call1 obj'" by auto
    moreover from IHobj[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,obj,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta obj obj' E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim `bsoks ps n`
    have "P,obj\<bullet>M'(ps),n,h' \<turnstile> (E'\<bullet>M'(ps), xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1Call1)
    moreover { 
      assume "no_call2 obj pc"
      hence "no_call2 (obj\<bullet>M'(ps)) pc \<or> pc = length (compE2 obj)" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: Call_\<tau>ExecrI1 Call_\<tau>ExectI1 exec_move_CallI1)+
  next
    case (Call1Params es v)
    note [simp] = `obj' = Val v` `e' = Val v\<bullet>M'(es)`
      and red = `P,t \<turnstile>1 \<langle>ps, (h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es, (h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h (obj'\<bullet>M'(ps)) = \<tau>moves1 P h ps" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim1 have s: "xcp = None" "xs = loc"
      and execo: "\<tau>Exec_mover_a P t obj h (stk, loc, pc, xcp) ([v], loc, length (compE2 obj), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (obj\<bullet>M'(ps)) h (stk, loc, pc, xcp) ([v], loc, length (compE2 obj), None)"
      by-(rule Call_\<tau>ExecrI1)
    moreover from IHparam[OF red] obtain ta' pc'' stk'' loc'' xcp''
      where bisim': "P,ps,n,h' \<turnstile> (es, xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'')"
      and exec': "?execs ta ps ps es h [] xs 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (obj\<bullet>M'(ps)) (obj'\<bullet>M'(ps)) (obj'\<bullet>M(es)) h [v] loc (length (compE2 obj)) None h' (length (compE2 obj) + pc'') (stk'' @ [v]) loc'' xcp''"
    proof(cases "\<tau>move1 P h (obj'\<bullet>M'(ps))")
      case True
      with exec' \<tau> have [simp]: "h = h'"
        and e: "sim_moves ps es P t ps h ([], xs, 0, None) (stk'', loc'', pc'', xcp'')" by auto
      from e have "sim_move (obj'\<bullet>M'(ps)) (obj'\<bullet>M'(es)) P t (obj\<bullet>M'(ps)) h ([] @ [v], xs, length (compE2 obj) + 0, None) (stk'' @ [v], loc'', length (compE2 obj) + pc'', xcp'')"
	by(fastsimp dest: Call_\<tau>ExecrI2 Call_\<tau>ExectI2)
      with s True show ?thesis by auto
    next
      case False
      with exec' \<tau> obtain pc' stk' loc' xcp'
	where e: "\<tau>Exec_movesr_a P t ps h ([], xs, 0, None) (stk', loc', pc', xcp')"
	and e': "exec_moves_a P t ps h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>moves2 (compP2 P) h stk' ps pc' xcp'" 
        and call: "calls1 ps = None \<or> no_calls2 ps 0 \<or> pc' = 0 \<and> stk' = [] \<and> loc' = xs \<and> xcp' = None" by auto
      from e have "\<tau>Exec_mover_a P t (obj\<bullet>M'(ps)) h ([] @ [v], xs, length (compE2 obj) + 0, None) (stk' @ [v], loc', length (compE2 obj) + pc', xcp')" by(rule Call_\<tau>ExecrI2)
      moreover from e' have "exec_move_a P t (obj\<bullet>M'(ps)) h (stk' @ [v], loc', length (compE2 obj) + pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'' @ [v], loc'', length (compE2 obj) + pc'', xcp'')"
	by(rule exec_move_CallI2)
      moreover from \<tau>' e' have "\<tau>move2 (compP2 P) h (stk' @ [v]) (obj\<bullet>M'(ps)) (length (compE2 obj) + pc') xcp' \<Longrightarrow> False"
	by(fastsimp simp add: \<tau>move2_iff \<tau>moves2_iff \<tau>instr_stk_drop_exec_moves split: split_if_asm)
      moreover from red have "call1 (obj'\<bullet>M'(ps)) = calls1 ps" by(auto simp add: is_vals_conv)
      moreover have "no_calls2 ps 0 \<Longrightarrow> no_call2 (obj\<bullet>M'(ps)) (length (compE2 obj)) \<or> ps = []" "calls1 [] = None"
        by(auto simp add: no_calls2_def no_call2_def)
      ultimately show ?thesis using False s call
        by(auto simp del: split_paired_Ex call1_calls1.simps) blast
    qed
    moreover from bisim' `bsok obj n`
    have "P,obj\<bullet>M'(ps),n,h' \<turnstile> (Val v\<bullet>M'(es), xs') \<leftrightarrow> ((stk'' @ [v]), loc'', length (compE2 obj) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1CallParams)
    moreover from bisim1 have "pc \<noteq> length (compE2 obj) \<longrightarrow> no_call2 (obj\<bullet>M'(ps)) pc"
      by(auto simp add: no_call2_def dest: bisim_Val_pc_not_Invoke bisim1_pc_length_compE2)
    ultimately show ?thesis using \<tau> execo
      apply(auto simp del: split_paired_Ex call1_calls1.simps split: split_if_asm split del: split_if)
      apply(blast intro: \<tau>Exec_mover_trans|fastsimp elim!: \<tau>Exec_mover_trans simp del: split_paired_Ex call1_calls1.simps)+
      done
  next
    case (Call1ThrowObj a)
    note [simp] = `obj' = Throw a` `ta = \<epsilon>` `e' = Throw a` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h (Throw a\<bullet>M'(ps))" by(rule \<tau>move1CallThrowObj)
    from bisim1 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim1 `bsoks ps n`
      have "P, obj\<bullet>M'(ps), n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1CallThrowObj)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim1 obtain pc'
	where "\<tau>Exec_mover_a P t obj h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
        and bisim': "P, obj, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
        by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (obj\<bullet>M'(ps)) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule Call_\<tau>ExecrI1)
      moreover from bisim' `bsoks ps n`
      have "P, obj\<bullet>M'(ps), n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1CallThrowObj, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  next
    case (Call1ThrowParams vs a es' v)
    note [simp] = `obj' = Val v` `ta = \<epsilon>` `e' = Throw a` `h' = h` `xs' = xs`
      and ps = `ps = map Val vs @ Throw a # es'`
    from bisim1 have [simp]: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t obj h (stk, loc, pc, xcp) ([v], loc, length (compE2 obj), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (obj\<bullet>M'(ps)) h (stk, loc, pc, xcp) ([v], loc, length (compE2 obj), None)"
      by-(rule Call_\<tau>ExecrI1)
    also from bisims1_Throw_\<tau>Exec_movest[OF bisim2[of xs, unfolded ps]]
    obtain pc' where exec': "\<tau>Exec_movest_a P t (map Val vs @ Throw a # es') h ([], xs, 0, None) (Addr a # rev vs, xs, pc', \<lfloor>a\<rfloor>)"
      and bisim': "P,map Val vs @ Throw a # es',n,h \<turnstile> (map Val vs @ Throw a # es', xs) [\<leftrightarrow>] (Addr a # rev vs, xs, pc', \<lfloor>a\<rfloor>)"
      by auto
    from Call_\<tau>ExectI2[OF exec', of "obj" M' v] ps
    have "\<tau>Exec_movet_a P t (obj\<bullet>M'(ps)) h ([v], loc, length (compE2 obj), None) (Addr a # rev vs @ [v], xs, length (compE2 obj) + pc', \<lfloor>a\<rfloor>)" by simp
    also from bisim1_bisims1.bisim1CallThrowParams[OF bisim' `bsok obj n`, of M' v] ps
    have bisim'': "P,obj\<bullet>M'(ps),n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (Addr a # rev vs @ [v], xs, length (compE2 obj) + pc', \<lfloor>a\<rfloor>)" by simp
    moreover have "\<tau>move1 P h (obj'\<bullet>M'(ps))" using ps by(auto intro: \<tau>move1CallThrowParams)
    ultimately show ?thesis by fastsimp
  next
    case (Red1CallExternal a Ta vs va H')
    hence [simp]: "obj' = addr a" "ps = map Val vs"
      "e' = extRet2J (addr a\<bullet>M'(map Val vs)) va" "H' = h'" "xs' = xs"
      and Ta: "typeof_addr h a = \<lfloor>Ta\<rfloor>"
      and iec: "is_external_call P Ta M'"
      and redex: "P,t \<turnstile> \<langle>a\<bullet>M'(vs),h\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>" by auto
    from bisim1 have [simp]: "xs = loc" by(auto dest: bisim_Val_loc_eq_xcp_None)
    have \<tau>: "\<tau>move1 P h (addr a\<bullet>M'(map Val vs)) \<longleftrightarrow>  \<tau>move2 (compP2 P) h (rev vs @ [Addr a]) (obj\<bullet>M'(ps)) (length (compE2 obj) + length (compEs2 ps)) None" using Ta iec
      by(auto simp add: map_eq_append_conv \<tau>move1_\<tau>moves1.simps \<tau>move2_iff compP2_def)
    from bisim1 have s: "xcp = None" "lcl (h, xs) = loc"
      and "\<tau>Exec_mover_a P t obj h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 obj), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (obj\<bullet>M'(ps)) h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 obj), None)"
      by-(rule Call_\<tau>ExecrI1)
    also have "\<tau>Exec_movesr_a P t ps h ([], loc, 0, None) (rev vs, loc, length (compEs2 ps), None)"
      unfolding `ps = map Val vs` by(rule \<tau>Exec_movesr_map_Val)
    from Call_\<tau>ExecrI2[OF this, of obj M' "Addr a"]
    have "\<tau>Exec_mover_a P t (obj\<bullet>M'(ps)) h ([Addr a], loc, length (compE2 obj), None) (rev vs @ [Addr a], loc, length (compE2 obj) + length (compEs2 ps), None)" by simp
    also (rtranclp_trans) from bisim1 have "pc \<le> length (compE2 obj)" by(rule bisim1_pc_length_compE2)
    hence "no_call2 (obj\<bullet>M'(ps)) pc \<or> pc = length (compE2 obj) + length (compEs2 ps)"
      using bisim1 by(auto simp add: no_call2_def neq_Nil_conv dest: bisim_Val_pc_not_Invoke)
    moreover { 
      assume "pc = length (compE2 obj) + length (compEs2 ps)"
      with `\<tau>Exec_mover_a P t obj h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 obj), None)`
      have "stk = rev vs @ [Addr a]" "xcp = None" by auto }
    moreover
    let ?ret = "extRet2JVM (length ps) h' (rev vs @ [Addr a]) loc undefined undefined (length (compE2 obj) + length (compEs2 ps)) [] va"
    let ?stk' = "fst (hd (snd (snd ?ret)))"
    let ?xcp' = "fst ?ret"
    let ?pc' = "snd (snd (snd (snd (hd (snd (snd ?ret))))))"
    from redex have redex': "(ta, va, h') \<in> red_external_aggr (compP2 P) t a M' vs h"
      by -(rule red_external_imp_red_external_aggr, simp add: compP2_def)
    with Ta iec redex'
    have "exec_move_a P t (obj\<bullet>M'(ps)) h (rev vs @ [Addr a], loc, length (compE2 obj) + length (compEs2 ps), None) (extTA2JVM (compP2 P) ta) h' (?stk', loc, ?pc', ?xcp')"
      unfolding exec_move_def
      by-(rule exec_instr,cases va,(force simp add: compP2_def simp del: split_paired_Ex)+)
    moreover have "P,obj\<bullet>M'(ps),n,h' \<turnstile> (extRet2J1 (addr a\<bullet>M'(map Val vs)) va, loc) \<leftrightarrow> (?stk', loc, ?pc', ?xcp')"
    proof(cases va)
      case (RetVal v)
      from `bsok obj n` `bsoks ps n` 
      have "P,obj\<bullet>M'(ps),n,h' \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (obj\<bullet>M'(ps))), None)"
	by-(rule bisim1Val2, simp_all)
      thus ?thesis unfolding RetVal by simp
    next
      case (RetExc ad)
      with `bsok obj n` `bsoks ps n` show ?thesis by(auto intro: bisim1CallThrow)
    next
      case RetStaySame 
      from bisims1_map_Val_append[OF bisims1Nil `bsoks ps n`, of vs P h' loc]
      have "P,map Val vs,n,h' \<turnstile> (map Val vs, loc) [\<leftrightarrow>] (rev vs, loc, length (compEs2 (map Val vs)), None)" by simp
      hence "P,obj\<bullet>M'(map Val vs),n,h' \<turnstile> (addr a\<bullet>M'(map Val vs), loc) \<leftrightarrow> (rev vs @ [Addr a], loc, length (compE2 obj) + length (compEs2 (map Val vs)), None)"
        using `bsok obj n` by(rule bisim1CallParams)
      thus ?thesis using RetStaySame by simp
    qed
    moreover from redex Ta iec
    have "\<tau>move1 P h (addr a\<bullet>M'(map Val vs)) \<Longrightarrow> ta = \<epsilon> \<and> h' = h"
      by(auto simp add: \<tau>move1_\<tau>moves1.simps map_eq_append_conv \<tau>external'_def dest: \<tau>external'_red_external_heap_unchanged \<tau>external'_red_external_TA_empty)
    ultimately show ?thesis using \<tau>
      apply(cases "\<tau>move1 P h (addr a\<bullet>M'(map Val vs) :: expr1)")
      apply(auto simp del: split_paired_Ex simp add: compP2_def)
      apply(blast intro: rtranclp.rtrancl_into_rtrancl rtranclp_into_tranclp1 \<tau>exec_moveI)+
      done
  next
    case (Red1CallNull vs)
    note [simp] = `h' = h` `xs' = xs` `ta = \<epsilon>` `obj' = null` `ps = map Val vs` `e' = THROW NullPointer`
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t obj h (stk, loc, pc, xcp) ([Null], loc, length (compE2 obj), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (obj\<bullet>M'(map Val vs)) h (stk, loc, pc, xcp) ([Null], loc, length (compE2 obj), None)"
      by-(rule Call_\<tau>ExecrI1)
    also have "\<tau>Exec_movesr_a P t (map Val vs) h ([], loc, 0, None) (rev vs, loc, length (compEs2 (map Val vs)), None)"
    proof(cases "vs")
      case Nil thus ?thesis by(auto)
    next
      case Cons 
      with bisims1_refl[of "map Val vs" n P "h" loc, simplified bsoks_def, simplified] show ?thesis
	by -(drule bisims1_Val_\<tau>Exec_moves, auto)
    qed
    from Call_\<tau>ExecrI2[OF this, of obj M' Null]
    have "\<tau>Exec_mover_a P t (obj\<bullet>M'(map Val vs)) h ([Null], loc, length (compE2 obj), None) (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 (map Val vs)), None)" by simp
    also (rtranclp_trans) {
      have "\<tau>move2 (compP2 P) h (rev vs @ [Null]) (obj\<bullet>M'(map Val vs)) (length (compE2 obj) + length (compEs2 (map Val vs))) None"
        by(simp add: \<tau>move2_iff)
      moreover have "exec_move_a P t (obj\<bullet>M'(map Val vs)) h (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 (map Val vs)), None) \<epsilon> h (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 (map Val vs)), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
        unfolding exec_move_def by(cases vs)(auto intro: exec_instr)
      ultimately have "\<tau>Exec_movet_a P t (obj\<bullet>M'(map Val vs)) h  (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 (map Val vs)), None) (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 (map Val vs)), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
        by(auto intro: \<tau>exec_moveI simp add: compP2_def) }
    also have "\<tau>move1 P h (null\<bullet>M'(map Val vs))" by(auto simp add: \<tau>move1_\<tau>moves1.simps map_eq_append_conv)
    moreover from bisim1 have "bsok obj n" by(auto dest: bisim1_bsok)
    hence "P,obj\<bullet>M'(map Val vs),n,h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ((rev vs @ [Null]), loc, length (compE2 obj) + length (compEs2 (map Val vs)), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by-(rule bisim1CallThrow,auto simp add: bsoks_def)
    ultimately show ?thesis using s by(auto simp del: split_paired_Ex)
  qed
next
  case bisim1Val2 thus ?case by fastsimp
next
  case (bisim1New C' n xs)
  have \<tau>: "\<not> \<tau>move1 P h (new C')" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
  from `P,t \<turnstile>1 \<langle>new C',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Red1New a)
    hence "exec_meth_a (compP2 P) [New C'] [] t h ([], xs, 0, None) \<epsilon>\<lbrace>\<^bsub>o\<^esub>NewObj a C'\<rbrace> h' ([Addr a], xs, Suc 0, None)"
      and [simp]: "e' = addr a" "xs' = xs" "ta = \<epsilon>\<lbrace>\<^bsub>o\<^esub>NewObj a C'\<rbrace>"
      by(auto intro!: exec_instr simp add: compP2_def simp del: fun_upd_apply)
    moreover have "P, new C', n, h' \<turnstile> (addr a, xs) \<leftrightarrow> ([Addr a], xs, length (compE2 (new C')), None)"
      by(rule bisim1Val2)(auto)
    moreover have "\<not> \<tau>move2 (compP2 P) h [] (new C') 0 None" by(simp add: \<tau>move2_iff)
    ultimately show ?thesis using \<tau> 
      by(fastsimp simp add: exec_move_def ta_upd_simps)
  next
    case Red1NewFail
    hence "exec_meth_a (compP2 P) [New C'] [] t h ([], xs, 0, None) \<epsilon> h' ([], xs, 0, \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>)"
      and [simp]: "ta = \<epsilon>" "xs' = xs" "e' = THROW OutOfMemory"
      by(auto intro!:exec_instr simp add: compP2_def simp del: fun_upd_apply)
    moreover have "P, new C', n, h' \<turnstile> (THROW OutOfMemory, xs) \<leftrightarrow> ([], xs, 0, \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>)"
      by(rule bisim1NewThrow)
    moreover have "\<not> \<tau>move2 (compP2 P) h [] (new C') 0 None" by(simp add: \<tau>move2_iff)
    ultimately show ?thesis using \<tau> by(fastsimp simp add: exec_move_def)
  qed
next
  case bisim1NewThrow thus ?case by fastsimp
next
  case (bisim1NewArray E n e xs stk loc pc xcp U)
  note IH = `\<And>e' h' xs' Env T Env' T'. \<lbrakk> P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>\<rbrakk>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P,t \<turnstile>1 \<langle>newA U\<lfloor>e\<rceil>,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from red show ?case
  proof cases 
    case (New1ArrayRed ee')
    note [simp] = `e' = newA U\<lfloor>ee'\<rceil>`
      and red = `P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>ee', (h', xs')\<rangle>`
    from red have "\<tau>move1 P h (newA U\<lfloor>e\<rceil>) = \<tau>move1 P h e" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from red have "call1 (newA U\<lfloor>e\<rceil>) = call1 e" by auto
    moreover from IH[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,E,n,h' \<turnstile> (ee', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta E e ee' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim
    have "P,newA U\<lfloor>E\<rceil>,n,h' \<turnstile> (newA U\<lfloor>ee'\<rceil>, xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1NewArray)
    moreover { 
      assume "no_call2 E pc"
      hence "no_call2 (newA U\<lfloor>E\<rceil>) pc" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: NewArray_\<tau>ExecrI NewArray_\<tau>ExectI exec_move_newArrayI)+
  next
    case (Red1NewArray i a)
    note [simp] = `e = Val (Intg i)` `ta = \<epsilon>\<lbrace>\<^bsub>o\<^esub>NewArr a U (nat (sint i))\<rbrace>` `e' = addr a` `xs' = xs`
      and new = `new_arr h U (nat (sint i)) = (h', \<lfloor>a\<rfloor>)`
    from bisim have s: "xcp = None" "xs = loc" by(auto dest: bisim_Val_loc_eq_xcp_None)
    from bisim have "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([Intg i], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (newA U\<lfloor>E\<rceil>) h (stk, loc, pc, xcp) ([Intg i], loc, length (compE2 E), None)"
      by(rule NewArray_\<tau>ExecrI)
    moreover from new `0 <=s i`
    have "exec_move_a P t (newA U\<lfloor>E\<rceil>) h ([Intg i], loc, length (compE2 E), None) \<epsilon>\<lbrace>\<^bsub>o\<^esub>NewArr a U (nat (sint i))\<rbrace> h' ([Addr a], loc, Suc (length (compE2 E)), None)"
      by(auto intro!: exec_instr simp add: compP2_def exec_move_def)
    moreover have "\<tau>move2 (compP2 P) h [Intg i] (newA U\<lfloor>E\<rceil>) (length (compE2 E)) None \<Longrightarrow> False" by(simp add: \<tau>move2_iff)
    moreover have "\<not> \<tau>move1 P h (newA U\<lfloor>Val (Intg i)\<rceil>)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from `bsok E n`
    have "P, newA U\<lfloor>E\<rceil>, n, h' \<turnstile> (addr a, loc) \<leftrightarrow> ([Addr a], loc, length (compE2 (newA U\<lfloor>E\<rceil>)), None)"
      by-(rule bisim1Val2, simp_all)
    ultimately show ?thesis using s by(auto simp del: fun_upd_apply simp add: ta_upd_simps) blast
  next
    case (Red1NewArrayNegative i)
    note [simp] = `e = Val (Intg i)` `e' = THROW NegativeArraySize` `h' = h` `xs' = xs` `ta = \<epsilon>`
    have "\<not> \<tau>move1 P h (newA U\<lfloor>Val (Intg i)\<rceil>)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from bisim have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([Intg i], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    moreover from `i <s 0`
    have "exec_meth_a (compP2 P) (compE2 (newA U\<lfloor>E\<rceil>)) (compxE2 (newA U\<lfloor>E\<rceil>) 0 0) t h ([Intg i], loc, length (compE2 E), None) \<epsilon> h ([Intg i], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt NegativeArraySize\<rfloor>)"
      by -(rule exec_instr, auto simp add: compP2_def)
    moreover have "\<tau>move2 (compP2 P) h [Intg i] (newA U\<lfloor>E\<rceil>) (length (compE2 E)) None \<Longrightarrow> False" by(simp add: \<tau>move2_iff)
    moreover from `bsok E n`
    have "P,newA U\<lfloor>E\<rceil>,n,h \<turnstile> (THROW NegativeArraySize, loc) \<leftrightarrow> ([Intg i], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt NegativeArraySize\<rfloor>)"
      by(auto intro!: bisim1_bisims1.bisim1NewArrayNegative)
    ultimately show ?thesis using s 
      by(auto simp add: exec_move_def)(blast intro: NewArray_\<tau>ExecrI)
  next
    case (Red1NewArrayFail i)
    note [simp] = `e = Val (Intg i)` `e' = THROW OutOfMemory` `xs' = xs` `ta = \<epsilon>`
      and new = `new_arr h U (nat (sint i)) = (h', None)`
    have "\<not> \<tau>move1 P h (newA U\<lfloor>Val (Intg i)\<rceil>)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from bisim have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([Intg i], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    moreover from `0 <=s i` new
    have "exec_meth_a (compP2 P) (compE2 (newA U\<lfloor>E\<rceil>)) (compxE2 (newA U\<lfloor>E\<rceil>) 0 0) t h ([Intg i], loc, length (compE2 E), None) \<epsilon> h' ([Intg i], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>)"
      by -(rule exec_instr, auto simp add: compP2_def)
    moreover have "\<tau>move2 (compP2 P) h [Intg i] (newA U\<lfloor>E\<rceil>) (length (compE2 E)) None \<Longrightarrow> False" by(simp add: \<tau>move2_iff)
    moreover from `bsok E n`
    have "P,newA U\<lfloor>E\<rceil>,n,h' \<turnstile> (THROW OutOfMemory, loc) \<leftrightarrow> ([Intg i], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>)"
      by(auto intro!: bisim1_bisims1.bisim1NewArrayFail)
    ultimately show ?thesis using s by (auto simp add: exec_move_def)(blast intro: NewArray_\<tau>ExecrI)
  next
    case (New1ArrayThrow a)
    note [simp] = `e = Throw a` `h' = h` `xs' = xs` `ta = \<epsilon>` `e' = Throw a`
    have \<tau>: "\<tau>move1 P h (newA U\<lfloor>e\<rceil>)" by(auto intro: \<tau>move1NewArrayThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim have "P,newA U\<lfloor>E\<rceil>, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.bisim1NewArrayThrow)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim obtain pc'
	where "\<tau>Exec_mover_a P t E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (newA U\<lfloor>E\<rceil>) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule NewArray_\<tau>ExecrI)
      moreover from bisim' have "P, newA U\<lfloor>E\<rceil>, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1_bisims1.bisim1NewArrayThrow, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed
next
  case bisim1NewArrayThrow thus ?case by auto
next
  case bisim1NewArrayNegative thus ?case by auto
next
  case bisim1NewArrayFail thus ?case by auto
next
  case (bisim1Cast E n e xs stk loc pc xcp U)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P,t \<turnstile>1 \<langle>Cast U e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from red show ?case
  proof cases
    case (Cast1Red ee')
    note [simp] = `e' = Cast U ee'`
      and red = `P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>ee', (h', xs')\<rangle>`
    from red have "\<tau>move1 P h (Cast U e) = \<tau>move1 P h e" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from red have "call1 (Cast U e) = call1 e" by auto
    moreover from IH[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,E,n,h' \<turnstile> (ee', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta E e ee' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim
    have "P,Cast U E,n,h' \<turnstile> (Cast U ee', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1Cast)
    moreover { 
      assume "no_call2 E pc"
      hence "no_call2 (Cast U E) pc" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: Cast_\<tau>ExecrI Cast_\<tau>ExectI exec_move_CastI)+
  next
    case (Red1Cast c U')
    hence [simp]: "e = Val c" "ta = \<epsilon>" "e' = Val c" "h' = h" "xs' = xs"
      and type: "typeof\<^bsub>h\<^esub> c = \<lfloor>U'\<rfloor>" "P \<turnstile> U' \<le> U" by auto
    from bisim have s: "xcp = None" "xs = loc" by(auto dest: bisim_Val_loc_eq_xcp_None)
    from bisim have "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([c], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (Cast U E) h (stk, loc, pc, xcp) ([c], loc, length (compE2 E), None)"
      by(rule Cast_\<tau>ExecrI)
    moreover from type
    have "exec_meth_a (compP2 P) (compE2 (Cast U E)) (compxE2 (Cast U E) 0 0) t h ([c], loc, length (compE2 E), None) \<epsilon> h' ([c], loc, Suc (length (compE2 E)), None)"
      by(auto intro!: exec_instr simp add: compP2_def)
    moreover have "\<tau>move2 (compP2 P) h [c] (Cast U E) (length (compE2 E)) None" by(simp add: \<tau>move2_iff)
    ultimately have "\<tau>Exec_mover_a P t (Cast U E) h (stk, loc, pc, xcp) ([c], loc, Suc (length (compE2 E)), None)"
      by(fastsimp elim: rtranclp.rtrancl_into_rtrancl intro: \<tau>exec_moveI simp add: exec_move_def compP2_def)
    moreover have "\<tau>move1 P h (Cast U (Val c))" by(rule \<tau>move1CastRed)
    moreover from `bsok E n`
    have "P, Cast U E, n, h' \<turnstile> (Val c, loc) \<leftrightarrow> ([c], loc, length (compE2 (Cast U E)), None)"
      by-(rule bisim1Val2, simp_all)
    ultimately show ?thesis using s by(auto simp add: exec_move_def)
  next
    case (Red1CastFail v U')
    note [simp] = `e = Val v` `e' = THROW ClassCast` `h' = h` `xs' = xs` `ta = \<epsilon>`
    moreover from bisim have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (Cast U E) h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      by(auto elim: Cast_\<tau>ExecrI)
    moreover from `typeof\<^bsub>hp (h, xs)\<^esub> v = \<lfloor>U'\<rfloor>` `\<not> P \<turnstile> U' \<le> U`
    have "exec_meth_a (compP2 P) (compE2 (Cast U E)) (compxE2 (Cast U E) 0 0) t h ([v], loc, length (compE2 E), None) \<epsilon> h ([v], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt ClassCast\<rfloor>)"
      by -(rule exec_instr, auto simp add: compP2_def)
    moreover have "\<tau>move2 (compP2 P) h [v] (Cast U E) (length (compE2 E)) None" by(simp add: \<tau>move2_iff)
    ultimately have "\<tau>Exec_movet_a P t (Cast U E) h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt ClassCast\<rfloor>)"
      by(fastsimp simp add: exec_move_def compP2_def intro: rtranclp_into_tranclp1 \<tau>exec_moveI)
    moreover have "\<tau>move1 P h (Cast U (Val v))" by(rule \<tau>move1CastRed)
    moreover from `bsok E n`
    have "P,Cast U E,n,h \<turnstile> (THROW ClassCast, loc) \<leftrightarrow> ([v], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt ClassCast\<rfloor>)"
      by(auto intro!: bisim1_bisims1.bisim1CastFail)
    ultimately show ?thesis using s by(auto simp add: exec_move_def)
  next
    case (Cast1Throw a)[simp]
    have \<tau>: "\<tau>move1 P h (Cast U e)" by(auto intro: \<tau>move1CastThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim have "P,Cast U E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.bisim1CastThrow)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim obtain pc'
	where "\<tau>Exec_mover_a P t E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (Cast U E) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule Cast_\<tau>ExecrI)
      moreover from bisim' have "P, Cast U E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1_bisims1.bisim1CastThrow, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed
next
  case bisim1CastThrow thus ?case by auto
next
  case bisim1CastFail thus ?case by auto
next
  case (bisim1InstanceOf E n e xs stk loc pc xcp U)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P,t \<turnstile>1 \<langle>e instanceof U,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from red show ?case
  proof cases
    case (InstanceOf1Red ee')
    note [simp] = `e' = ee' instanceof U`
      and red = `P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>ee', (h', xs')\<rangle>`
    from red have "\<tau>move1 P h (e instanceof U) = \<tau>move1 P h e" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from red have "call1 (e instanceof U) = call1 e" by auto
    moreover from IH[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,E,n,h' \<turnstile> (ee', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta E e ee' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim
    have "P,E instanceof U,n,h' \<turnstile> (ee' instanceof U, xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1InstanceOf)
    moreover { 
      assume "no_call2 E pc"
      hence "no_call2 (E instanceof U) pc" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: InstanceOf_\<tau>ExecrI InstanceOf_\<tau>ExectI exec_move_InstanceOfI)+
  next
    case (Red1InstanceOf c U' b)
    hence [simp]: "e = Val c" "ta = \<epsilon>" "e' = Val (Bool (c \<noteq> Null \<and> P \<turnstile> U' \<le> U))" "h' = h" "xs' = xs"
      "b = (c \<noteq> Null \<and> P \<turnstile> U' \<le> U)"
      and type: "typeof\<^bsub>h\<^esub> c = \<lfloor>U'\<rfloor>" by auto
    from bisim have s: "xcp = None" "xs = loc" by(auto dest: bisim_Val_loc_eq_xcp_None)
    from bisim have "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([c], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (E instanceof U) h (stk, loc, pc, xcp) ([c], loc, length (compE2 E), None)"
      by(rule InstanceOf_\<tau>ExecrI)
    moreover from type
    have "exec_meth_a (compP2 P) (compE2 (E instanceof U)) (compxE2 (E instanceof U) 0 0) t h ([c], loc, length (compE2 E), None) \<epsilon> h' ([Bool b], loc, Suc (length (compE2 E)), None)"
      by(auto intro!: exec_instr simp add: compP2_def)
    moreover have "\<tau>move2 (compP2 P) h [c] (E instanceof U) (length (compE2 E)) None" by(simp add: \<tau>move2_iff)
    ultimately have "\<tau>Exec_mover_a P t (E instanceof U) h (stk, loc, pc, xcp) ([Bool b], loc, Suc (length (compE2 E)), None)"
      by(fastsimp elim: rtranclp.rtrancl_into_rtrancl intro: \<tau>exec_moveI simp add: exec_move_def compP2_def)
    moreover have "\<tau>move1 P h ((Val c) instanceof U)" by(rule \<tau>move1InstanceOfRed)
    moreover from `bsok E n`
    have "P, E instanceof U, n, h' \<turnstile> (Val (Bool b), loc) \<leftrightarrow> ([Bool b], loc, length (compE2 (E instanceof U)), None)"
      by-(rule bisim1Val2, simp_all)
    ultimately show ?thesis using s by(auto simp add: exec_move_def)
  next
    case (InstanceOf1Throw a)
    note [simp] = `e = Throw a` `h' = h` `xs' = xs` `ta = \<epsilon>` `e' = Throw a`
    have \<tau>: "\<tau>move1 P h (e instanceof U)" by(auto intro: \<tau>move1InstanceOfThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim have "P,E instanceof U, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.bisim1InstanceOfThrow)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim obtain pc'
	where "\<tau>Exec_mover_a P t E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (E instanceof U) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule InstanceOf_\<tau>ExecrI)
      moreover from bisim' have "P, E instanceof U, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1_bisims1.bisim1InstanceOfThrow, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed
next
  case bisim1InstanceOfThrow thus ?case by auto
next
  case bisim1Val thus ?case by fastsimp
next
  case (bisim1Var V n xs)
  from `P,t \<turnstile>1 \<langle>Var V,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Red1Var v)
    hence "exec_meth_a (compP2 P) [Load V] [] t h ([], xs, 0, None) \<epsilon> h ([v], xs, 1, None)"
      and [simp]: "ta = \<epsilon>" "h' = h" "xs' = xs" "e' = Val v"
      by(auto intro: exec_instr)
    moreover have "\<tau>move2 (compP2 P) h [] (Var V) 0 None" by(simp add: \<tau>move2_iff)
    ultimately have "\<tau>Exec_movet_a P t (Var V) h ([], xs, 0, None) ([v], xs, 1, None)"
      by(auto intro: \<tau>Exect1step simp add: exec_move_def compP2_def)
    moreover have "P, Var V, n, h \<turnstile> (Val v, xs) \<leftrightarrow> ([v], xs, length (compE2 (Var V)), None)"
      by(rule bisim1Val2)(auto)
    moreover have "\<tau>move1 P h (Var V)" by(rule \<tau>move1Var)
    ultimately show ?thesis by(fastsimp)
  qed
next
  case (bisim1BinOp1 e1 n e1' xs stk loc pc xcp e2 bop)
  note IH1 = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e1',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle> 
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e1,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e1 e1' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note IH2 = `\<And>xs e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta e2 e2 e' h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,e1,n,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,e2,n,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,t \<turnstile>1 \<langle>e1' \<guillemotleft>bop\<guillemotright> e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Bin1OpRed1 E')
    note [simp] = `e' = E' \<guillemotleft>bop\<guillemotright> e2`
      and red = `P,t \<turnstile>1 \<langle>e1',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from red have "\<tau>move1 P h (e1' \<guillemotleft>bop\<guillemotright> e2) = \<tau>move1 P h e1'" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from red have "call1 (e1' \<guillemotleft>bop\<guillemotright> e2) = call1 e1'" by auto
    moreover from IH1[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,e1,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta e1 e1' E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim `bsok e2 n`
    have "P,e1\<guillemotleft>bop\<guillemotright>e2,n,h' \<turnstile> (E'\<guillemotleft>bop\<guillemotright>e2, xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1BinOp1)
    moreover { 
      assume "no_call2 e1 pc"
      hence "no_call2 (e1\<guillemotleft>bop\<guillemotright>e2) pc \<or> pc = length (compE2 e1)" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: BinOp_\<tau>ExecrI1 BinOp_\<tau>ExectI1 exec_move_BinOpI1)+
  next
    case (Bin1OpRed2 E' v)
    note [simp] = `e1' = Val v` `e' = Val v \<guillemotleft>bop\<guillemotright> E'`
      and red = `P,t \<turnstile>1 \<langle>e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h (Val v \<guillemotleft>bop\<guillemotright> e2) = \<tau>move1 P h e2" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim1 have s: "xcp = None" "xs = loc"
      and exec1: "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, None) ([v], xs, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    from exec1 have "\<tau>Exec_mover_a P t (e1\<guillemotleft>bop\<guillemotright>e2) h (stk, loc, pc, None) ([v], xs, length (compE2 e1), None)"
      by(rule BinOp_\<tau>ExecrI1)
    moreover
    from IH2[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e2,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e2 e2 E' h [] xs 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (e1\<guillemotleft>bop\<guillemotright>e2) (Val v\<guillemotleft>bop\<guillemotright>e2) (Val v\<guillemotleft>bop\<guillemotright>E') h ([] @ [v]) xs (length (compE2 e1) + 0) None h' (length (compE2 e1) + pc'') (stk'' @ [v]) loc'' xcp''"
    proof(cases "\<tau>move1 P h (Val v \<guillemotleft>bop\<guillemotright> e2)")
      case True
      with exec' \<tau> have [simp]: "h = h'" and e: "sim_move e2 E' P t e2 h ([], xs, 0, None) (stk'', loc'', pc'', xcp'')" by auto
      from e have "sim_move (Val v\<guillemotleft>bop\<guillemotright>e2) (Val v\<guillemotleft>bop\<guillemotright>E') P t (e1 \<guillemotleft>bop\<guillemotright> e2) h ([] @ [v], xs, length (compE2 e1) + 0, None) (stk'' @ [v], loc'', length (compE2 e1) + pc'', xcp'')"
	by(fastsimp dest: BinOp_\<tau>ExecrI2 BinOp_\<tau>ExectI2)
      with True show ?thesis by auto
    next
      case False
      with exec' \<tau> obtain pc' stk' loc' xcp'
	where e: "\<tau>Exec_mover_a P t e2 h ([], xs, 0, None) (stk', loc', pc', xcp')"
	and e': "exec_move_a P t e2 h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 (compP2 P) h stk' e2 pc' xcp'" 
        and call: "call1 e2 = None \<or> no_call2 e2 0 \<or> pc' = 0 \<and> stk' = [] \<and> loc' = xs \<and> xcp' = None" by auto
      from e have "\<tau>Exec_mover_a P t (e1 \<guillemotleft>bop\<guillemotright> e2) h ([] @ [v], xs, length (compE2 e1) + 0, None) (stk' @ [v], loc', length (compE2 e1) + pc', xcp')" by(rule BinOp_\<tau>ExecrI2)
      moreover from e' have "exec_move_a P t (e1 \<guillemotleft>bop\<guillemotright> e2) h (stk' @ [v], loc', length (compE2 e1) + pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'' @ [v], loc'', length (compE2 e1) + pc'', xcp'')"
	by(rule exec_move_BinOpI2)
      moreover from e' have "pc' < length (compE2 e2)" by auto
      with \<tau>' e' have "\<not> \<tau>move2 (compP2 P) h (stk' @ [v]) (e1 \<guillemotleft>bop\<guillemotright> e2) (length (compE2 e1) + pc') xcp'"
        by(auto simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff)
      moreover from red have "call1 (e1'\<guillemotleft>bop\<guillemotright>e2) = call1 e2" by(auto)
      moreover have "no_call2 e2 0 \<Longrightarrow> no_call2 (e1\<guillemotleft>bop\<guillemotright>e2) (length (compE2 e1))"
        by(auto simp add: no_call2_def)
      ultimately show ?thesis using False call
        by(auto simp del: split_paired_Ex call1_calls1.simps) blast
    qed
    moreover from bisim' `bsok e1 n`
    have "P,e1\<guillemotleft>bop\<guillemotright>e2,n,h' \<turnstile> (Val v\<guillemotleft>bop\<guillemotright>E', xs') \<leftrightarrow> ((stk'' @ [v]), loc'', length (compE2 e1) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1BinOp2)
    moreover from bisim1 have "pc \<noteq> length (compE2 e1) \<longrightarrow> no_call2 (e1\<guillemotleft>bop\<guillemotright>e2) pc"
      by(auto simp add: no_call2_def dest: bisim_Val_pc_not_Invoke bisim1_pc_length_compE2)
    ultimately show ?thesis using \<tau> exec1 s
      apply(auto simp del: split_paired_Ex call1_calls1.simps split: split_if_asm split del: split_if)
      apply(blast intro: \<tau>Exec_mover_trans|fastsimp elim!: \<tau>Exec_mover_trans simp del: split_paired_Ex call1_calls1.simps)+
      done
  next
    case (Red1BinOp v1 v2 v)
    note [simp] = `e1' = Val v1` `e2 = Val v2` `ta = \<epsilon>` `e' = Val v` `h' = h` `xs' = xs`
      and binop = `binop bop v1 v2 = \<lfloor>v\<rfloor>`
    have \<tau>: "\<tau>move1 P h (Val v1 \<guillemotleft>bop\<guillemotright> Val v2)" by(rule \<tau>move1BinOp)
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, xcp) ([v1], loc, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (e1\<guillemotleft>bop\<guillemotright>Val v2) h (stk, loc, pc, xcp) ([v1], loc, length (compE2 e1), None)"
      by-(rule BinOp_\<tau>ExecrI1)
    also have "\<tau>move2 (compP2 P) h [v1] (e1 \<guillemotleft>bop\<guillemotright> Val v2) (length (compE2 e1) + 0) None"
      by(rule \<tau>move2BinOp2)(rule \<tau>move2Val)
    with binop have "\<tau>Exec_mover_a P t (e1\<guillemotleft>bop\<guillemotright>Val v2) h ([v1], loc, length (compE2 e1), None) ([v2, v1], loc, Suc (length (compE2 e1)), None)"
      by-(rule \<tau>Execr1step, auto intro!: exec_instr simp add: exec_move_def compP2_def split: bop.split)
    also (rtranclp_trans) from binop
    have "exec_meth_a (compP2 P) (compE2 (e1\<guillemotleft>bop\<guillemotright>Val v2)) (compxE2 (e1\<guillemotleft>bop\<guillemotright>Val v2) 0 0) t
                               h ([v2, v1], loc, Suc (length (compE2 e1)), None) \<epsilon>
                               h ([v], loc, Suc (Suc (length (compE2 e1))), None)"
      by-(rule exec_instr, auto)
    moreover have "\<tau>move2 (compP2 P) h [v2, v1] (e1\<guillemotleft>bop\<guillemotright>Val v2) (Suc (length (compE2 e1))) None" by(simp add: \<tau>move2_iff) 
    ultimately have "\<tau>Exec_mover_a P t (e1 \<guillemotleft>bop\<guillemotright> Val v2) h (stk, loc, pc, xcp) ([v], loc, Suc (Suc (length (compE2 e1))), None)"
      by(fastsimp intro: rtranclp.rtrancl_into_rtrancl \<tau>exec_moveI simp add: exec_move_def compP2_def)
    moreover from `bsok e1 n`
    have "P, e1 \<guillemotleft>bop\<guillemotright> Val v2, n, h \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (e1 \<guillemotleft>bop\<guillemotright> Val v2)), None)"
      by-(rule bisim1Val2,auto)
    ultimately show ?thesis using s \<tau> by auto
  next
    case (Bin1OpThrow1 a)
    note [simp] = `e1' = Throw a` `ta = \<epsilon>` `e' = Throw a` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h (Throw a \<guillemotleft>bop\<guillemotright> e2)" by(rule \<tau>move1BinOpThrow1)
    from bisim1 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim1 bisim1_bsok[OF bisim2]
      have "P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.intros)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim1 obtain pc' where "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, e1, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (e1\<guillemotleft>bop\<guillemotright>e2) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule BinOp_\<tau>ExecrI1)
      moreover from bisim' `bsok e2 n`
      have "P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1BinOpThrow1)
      ultimately show ?thesis using \<tau> by auto
    qed
  next
    case (Bin1OpThrow2 v a)
    note [simp] = `e1' = Val v` `e2 = Throw a` `ta = \<epsilon>` `e' = Throw a` `h' = h` `xs' = xs`
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, xcp) ([v], loc, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (e1\<guillemotleft>bop\<guillemotright>Throw a) h (stk, loc, pc, xcp) ([v], loc, length (compE2 e1), None)"
      by-(rule BinOp_\<tau>ExecrI1)
    also have "\<tau>Exec_mover_a P t (e1\<guillemotleft>bop\<guillemotright>Throw a) h ([v], loc, length (compE2 e1), None) ([Addr a, v], loc, Suc (length (compE2 e1)), \<lfloor>a\<rfloor>)"
      by(rule \<tau>Execr2step)(auto simp add: exec_move_def exec_meth_instr \<tau>move2_iff \<tau>move1_\<tau>moves1.simps)
    also (rtranclp_trans)
    have "P,e1\<guillemotleft>bop\<guillemotright>Throw a,n,h \<turnstile> (Throw a, loc) \<leftrightarrow> ([Addr a] @ [v], loc, (length (compE2 e1) + length (compE2 (addr a))), \<lfloor>a\<rfloor>)"
      by(rule bisim1BinOpThrow2[OF bisim1Throw2 `bsok e1 n`])(simp)
    moreover have "\<tau>move1 P h (e1' \<guillemotleft>bop\<guillemotright> e2)" by(auto intro: \<tau>move1BinOpThrow2)
    ultimately show ?thesis using s by auto
  qed
next
  case (bisim1BinOp2 e2 n e2' xs stk loc pc xcp e1 bop v1)
  note IH2 = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e2 e2' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `\<And>xs. P,e1,n,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,e2,n,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P,t \<turnstile>1 \<langle>Val v1 \<guillemotleft>bop\<guillemotright> e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from red show ?case
  proof cases
    case (Bin1OpRed2 E')
    note [simp] = `e' = Val v1 \<guillemotleft>bop\<guillemotright> E'`
      and red = `P,t \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from IH2[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e2,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e2 e2' E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    from red have \<tau>: "\<tau>move1 P h (Val v1 \<guillemotleft>bop\<guillemotright> e2') = \<tau>move1 P h e2'" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    have "no_call2 e2 pc \<Longrightarrow> no_call2 (e1 \<guillemotleft>bop\<guillemotright> e2) (length (compE2 e1) + pc)" by(auto simp add: no_call2_def)
    hence "?exec ta (e1\<guillemotleft>bop\<guillemotright>e2) (Val v1\<guillemotleft>bop\<guillemotright>e2') (Val v1\<guillemotleft>bop\<guillemotright>E') h (stk @ [v1]) loc (length (compE2 e1) + pc) xcp h' (length (compE2 e1) + pc'') (stk'' @ [v1]) loc'' xcp''"
      using exec' \<tau>
      apply(cases "\<tau>move1 P h (Val v1 \<guillemotleft>bop\<guillemotright> e2')")
      apply(auto)
      apply(blast intro: BinOp_\<tau>ExecrI2 BinOp_\<tau>ExectI2 exec_move_BinOpI2)
      apply(blast intro: BinOp_\<tau>ExecrI2 BinOp_\<tau>ExectI2 exec_move_BinOpI2)
      apply(rule exI conjI BinOp_\<tau>ExecrI2 exec_move_BinOpI2|assumption)+
      apply(fastsimp simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff split: split_if_asm)
      apply(rule exI conjI BinOp_\<tau>ExecrI2 exec_move_BinOpI2|assumption)+
      apply(fastsimp simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff split: split_if_asm)
      apply(rule exI conjI BinOp_\<tau>ExecrI2 exec_move_BinOpI2 rtranclp.rtrancl_refl|assumption)+
      apply(fastsimp simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff split: split_if_asm)+
      done
    moreover from bisim' `bsok e1 n`
    have "P,e1\<guillemotleft>bop\<guillemotright>e2,n,h' \<turnstile> (Val v1\<guillemotleft>bop\<guillemotright>E', xs') \<leftrightarrow> (stk''@[v1], loc'', length (compE2 e1) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1BinOp2)
    ultimately show ?thesis using \<tau> by auto blast+
  next
    case (Red1BinOp v2 v)
    note [simp] = `e2' = Val v2` `ta = \<epsilon>` `e' = Val v` `h' = h` `xs' = xs`
      and binop = `binop bop v1 v2 = \<lfloor>v\<rfloor>`
    have \<tau>: "\<tau>move1 P h (Val v1 \<guillemotleft>bop\<guillemotright> Val v2)" by(rule \<tau>move1BinOp)
    from bisim2 have s: "xcp = None" "xs = loc" 
      and "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, xcp) ([v2], loc, length (compE2 e2), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (e1\<guillemotleft>bop\<guillemotright>e2) h (stk @ [v1], loc, length (compE2 e1) + pc, xcp) ([v2] @ [v1], loc, length (compE2 e1) + length (compE2 e2), None)"
      by-(rule BinOp_\<tau>ExecrI2)
    moreover from binop
    have "exec_move_a P t (e1\<guillemotleft>bop\<guillemotright>e2) h ([v2, v1], loc, length (compE2 e1) + length (compE2 e2), None) \<epsilon>
                                  h ([v], loc, Suc (length (compE2 e1) + length (compE2 e2)), None)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: nth_append split: bop.split)
    moreover have "\<tau>move2 (compP2 P) h [v2, v1] (e1\<guillemotleft>bop\<guillemotright>e2) (length (compE2 e1) + length (compE2 e2)) None"
      by(simp add: \<tau>move2_iff)
    ultimately have "\<tau>Exec_mover_a P t (e1 \<guillemotleft>bop\<guillemotright> e2) h (stk @ [v1], loc, length (compE2 e1) + pc, xcp) ([v], loc, Suc (length (compE2 e1) + length (compE2 e2)), None)"
      by(auto intro: rtranclp.rtrancl_into_rtrancl \<tau>exec_moveI simp add: compP2_def)
    moreover from bisim1_bsok[OF bisim1] `bsok e2 n`
    have "P, e1 \<guillemotleft>bop\<guillemotright> e2, n, h \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (e1 \<guillemotleft>bop\<guillemotright> e2)), None)"
      by-(rule bisim1Val2, auto)
    ultimately show ?thesis using s \<tau> by(auto)
  next
    case (Bin1OpThrow2 a)
    note [simp] = `e2' = Throw a` `ta = \<epsilon>` `h' = h` `xs' = xs` `e' = Throw a`
    have \<tau>: "\<tau>move1 P h (Val v1 \<guillemotleft>bop\<guillemotright> Throw a)" by(rule \<tau>move1BinOpThrow2)
    from bisim2 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim2 `bsok e1 n`
      have "P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk @ [v1], loc, length (compE2 e1) + pc, xcp)"
	by(auto intro: bisim1BinOpThrow2)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim2 obtain pc'
	where "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (e1\<guillemotleft>bop\<guillemotright>e2) h (stk @ [v1], loc, length (compE2 e1) + pc, None) ([Addr a] @ [v1], loc, length (compE2 e1) + pc', \<lfloor>a\<rfloor>)"
	by-(rule BinOp_\<tau>ExecrI2)
      moreover from bisim' bisim1_bsok[OF bisim1]
      have "P, e1\<guillemotleft>bop\<guillemotright>e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a]@[v1], loc, length (compE2 e1) + pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1BinOpThrow2, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case bisim1BinOpThrow1 thus ?case by fastsimp
next
  case bisim1BinOpThrow2 thus ?case by fastsimp
next
  case (bisim1LAss1 E n e xs stk loc pc xcp V)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P,t \<turnstile>1 \<langle>V:=e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from red show ?case
  proof cases
    case (LAss1Red ee')
    note [simp] = `e' = V := ee'`
      and red = `P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>ee', (h', xs')\<rangle>`
    from red have "\<tau>move1 P h (V:=e) = \<tau>move1 P h e" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from red have "call1 (V:=e) = call1 e" by auto
    moreover from IH[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,E,n,h' \<turnstile> (ee', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta E e ee' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim
    have "P,V:=E,n,h' \<turnstile> (V:=ee', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1LAss1)
    moreover { 
      assume "no_call2 E pc"
      hence "no_call2 (V:=E) pc" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: LAss_\<tau>ExecrI LAss_\<tau>ExectI exec_move_LAssI)+
  next
    case (Red1LAss v)
    note [simp] = `e = Val v` `ta = \<epsilon>` `e' = unit` `h' = h` `xs' = xs[V := v]`
      and V = `V < length xs`
    from bisim have s: "xcp = None" "xs = loc" by(auto dest: bisim_Val_loc_eq_xcp_None)
    from bisim have "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (V:=E) h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      by(rule LAss_\<tau>ExecrI)
    moreover have "exec_move_a P t (V:=E) h ([v], loc, length (compE2 E), None) \<epsilon> h ([], loc[V := v], Suc (length (compE2 E)), None)"
      using V s by(auto intro: exec_instr simp add: exec_move_def)
    moreover have "\<tau>move2 (compP2 P) h [v] (V := E) (length (compE2 E)) None" by(simp add: \<tau>move2_iff)
    ultimately have "\<tau>Exec_mover_a P t (V:=E) h (stk, loc, pc, xcp) ([], loc[V := v], Suc (length (compE2 E)), None)"
      by(auto intro: rtranclp.rtrancl_into_rtrancl \<tau>exec_moveI simp add: compP2_def)
    moreover have "\<tau>move1 P h (V := Val v)" by(rule \<tau>move1LAssRed)
    moreover from `bsok E n` have "P, V:=E, n, h \<turnstile> (unit, loc[V := v]) \<leftrightarrow> ([], loc[V := v], Suc (length (compE2 E)), None)"
      by(rule bisim1LAss2)
    ultimately show ?thesis using s by auto
  next
    case (LAss1Throw a)
    note [simp] = `e = Throw a` `h' = h` `xs' = xs` `ta = \<epsilon>` `e' = Throw a`
    have \<tau>: "\<tau>move1 P h (V:=e)" by(auto intro: \<tau>move1LAssThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim have "P, V:=E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)" by(auto intro: bisim1LAssThrow)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim obtain pc'
	where "\<tau>Exec_mover_a P t E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (V:=E) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule LAss_\<tau>ExecrI)
      moreover from bisim' have "P, V:=E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1LAssThrow, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed
next
  case bisim1LAss2 thus ?case by fastsimp
next
  case bisim1LAssThrow thus ?case by fastsimp
next
  case (bisim1AAcc1 a n a' xs stk loc pc xcp i)
  note IH1 = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>a',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,a,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta a a' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note IH2 = `\<And>xs e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>i,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,i,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta i i e' h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,a,n,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,i,n,h \<turnstile> (i, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,t \<turnstile>1 \<langle>a'\<lfloor>i\<rceil>,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (AAcc1Red1 E')
    note [simp] = `e' = E'\<lfloor>i\<rceil>`
      and red = `P,t \<turnstile>1 \<langle>a',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from red have "\<tau>move1 P h (a'\<lfloor>i\<rceil>) = \<tau>move1 P h a'" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from red have "call1 (a'\<lfloor>i\<rceil>) = call1 a'" by auto
    moreover from IH1[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,a,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta a a' E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim `bsok i n`
    have "P,a\<lfloor>i\<rceil>,n,h' \<turnstile> (E'\<lfloor>i\<rceil>, xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1AAcc1)
    moreover { 
      assume "no_call2 a pc"
      hence "no_call2 (a\<lfloor>i\<rceil>) pc \<or> pc = length (compE2 a)" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: AAcc_\<tau>ExecrI1 AAcc_\<tau>ExectI1 exec_move_AAccI1)+
  next
    case (AAcc1Red2 E' v)
    note [simp] = `a' = Val v` `e' = Val v\<lfloor>E'\<rceil>`
      and red = `P,t \<turnstile>1 \<langle>i,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h (Val v\<lfloor>i\<rceil>) = \<tau>move1 P h i" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim1 have s: "xcp = None" "xs = loc"
      and exec1: "\<tau>Exec_mover_a P t a h (stk, loc, pc, None) ([v], xs, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1)
    from exec1 have "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil>) h (stk, loc, pc, None) ([v], xs, length (compE2 a), None)"
      by(rule AAcc_\<tau>ExecrI1)
    moreover
    from IH2[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,i,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta i i E' h [] xs 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (a\<lfloor>i\<rceil>) (Val v\<lfloor>i\<rceil>) (Val v\<lfloor>E'\<rceil>) h ([] @ [v]) xs (length (compE2 a) + 0) None h' (length (compE2 a) + pc'') (stk'' @ [v]) loc'' xcp''"
    proof(cases "\<tau>move1 P h (Val v\<lfloor>i\<rceil>)")
      case True
      with exec' \<tau> have [simp]: "h = h'" and e: "sim_move i E' P t i h ([], xs, 0, None) (stk'', loc'', pc'', xcp'')" by auto
      from e have "sim_move (a\<lfloor>i\<rceil>) (a\<lfloor>E'\<rceil>) P t (a\<lfloor>i\<rceil>) h ([] @ [v], xs, length (compE2 a) + 0, None) (stk'' @ [v], loc'', length (compE2 a) + pc'', xcp'')"
	by(fastsimp dest: AAcc_\<tau>ExecrI2 AAcc_\<tau>ExectI2)
      with True show ?thesis by auto
    next
      case False
      with exec' \<tau> obtain pc' stk' loc' xcp'
	where e: "\<tau>Exec_mover_a P t i h ([], xs, 0, None) (stk', loc', pc', xcp')"
	and e': "exec_move_a P t i h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 (compP2 P) h stk' i pc' xcp'" 
        and call: "call1 i = None \<or> no_call2 i 0 \<or> pc' = 0 \<and> stk' = [] \<and> loc' = xs \<and> xcp' = None" by auto
      from e have "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil>) h ([] @ [v], xs, length (compE2 a) + 0, None) (stk' @ [v], loc', length (compE2 a) + pc', xcp')"
	by(rule AAcc_\<tau>ExecrI2)
      moreover from e' have "exec_move_a P t (a\<lfloor>i\<rceil>) h (stk' @ [v], loc', length (compE2 a) + pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'' @ [v], loc'', length (compE2 a) + pc'', xcp'')"
	by(rule exec_move_AAccI2)
      moreover from e' \<tau>' have "\<not> \<tau>move2 (compP2 P) h (stk' @ [v]) (a\<lfloor>i\<rceil>) (length (compE2 a) + pc') xcp'"
        by(auto simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff)
      moreover have "call1 (a'\<lfloor>i\<rceil>) = call1 i" by simp
      moreover have "no_call2 i 0 \<Longrightarrow> no_call2 (a\<lfloor>i\<rceil>) (length (compE2 a))"
        by(auto simp add: no_call2_def)
      ultimately show ?thesis using False call
        by(auto simp del: split_paired_Ex call1_calls1.simps) blast
    qed
    moreover from bisim' `bsok a n`
    have "P,a\<lfloor>i\<rceil>,n,h' \<turnstile> (Val v\<lfloor>E'\<rceil>, xs') \<leftrightarrow> ((stk'' @ [v]), loc'', length (compE2 a) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1AAcc2)
    moreover from bisim1 have "pc \<noteq> length (compE2 a) \<longrightarrow> no_call2 (a\<lfloor>i\<rceil>) pc"
      by(auto simp add: no_call2_def dest: bisim_Val_pc_not_Invoke bisim1_pc_length_compE2)
    ultimately show ?thesis using \<tau> exec1 s
      apply(auto simp del: split_paired_Ex call1_calls1.simps split: split_if_asm split del: split_if)
      apply(blast intro: \<tau>Exec_mover_trans|fastsimp elim!: \<tau>Exec_mover_trans simp del: split_paired_Ex call1_calls1.simps)+
      done
  next
    case (Red1AAcc A U I v)
    hence [simp]: "a' = addr A" "e' = Val v" "i = Val (Intg I)" "h' = h" "xs' = xs"
                  "ta = \<epsilon>\<lbrace>\<^bsub>o\<^esub>ReadMem A (ACell (nat (sint I))) v\<rbrace>" "h' = h" "xs' = xs"
      and hA: "typeof_addr h A = \<lfloor>Array U\<rfloor>" and I: "0 <=s I" "sint I < int (array_length h A)"
      and read: "heap_read h A (ACell (nat (sint I))) v" by auto
    have \<tau>: "\<not> \<tau>move1 P h (addr A\<lfloor>Val (Intg I)\<rceil>)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t a h (stk, loc, pc, xcp) ([Addr A], loc, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>Val (Intg I)\<rceil>) h (stk, loc, pc, xcp) ([Addr A], loc, length (compE2 a), None)"
      by-(rule AAcc_\<tau>ExecrI1)
    also have "\<tau>move2 (compP2 P) h [Addr A] (a\<lfloor>Val (Intg I)\<rceil>) (length (compE2 a) + 0) None"
      by(rule \<tau>move2AAcc2)(rule \<tau>move2Val)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>Val (Intg I)\<rceil>) h ([Addr A], loc, length (compE2 a), None) ([Intg I, Addr A], loc, Suc (length (compE2 a)), None)"
      by-(rule \<tau>Execr1step, auto intro!: exec_instr simp add: exec_move_def compP2_def)
    also (rtranclp_trans) from hA I read
    have "exec_move_a P t (a\<lfloor>Val (Intg I)\<rceil>) h ([Intg I, Addr A], loc, Suc (length (compE2 a)), None) 
                                           \<epsilon>\<lbrace>\<^bsub>o\<^esub>ReadMem A (ACell (nat (sint I))) v\<rbrace>
                                           h ([v], loc, Suc (Suc (length (compE2 a))), None)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (compP2 P) h [Intg I, Addr A] (a\<lfloor>Val (Intg I)\<rceil>) (Suc (length (compE2 a))) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok a n`
    have "P, a\<lfloor>Val (Intg I)\<rceil>, n, h \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (a\<lfloor>Val (Intg I)\<rceil>)), None)"
      by-(rule bisim1Val2,auto)
    ultimately show ?thesis using s \<tau>
      by(auto simp add: ta_upd_simps) blast
  next
    case (Red1AAccNull v)
    note [simp] = `a' = null` `i = Val v` `ta = \<epsilon>` `e' = THROW NullPointer` `h' = h` `xs' = xs`
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t a h (stk, loc, pc, xcp) ([Null], loc, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1 intro: AAcc_\<tau>ExecrI1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil>) h (stk, loc, pc, xcp) ([Null], loc, length (compE2 a), None)"
      by-(rule AAcc_\<tau>ExecrI1)
    also from bisim2[of loc] have "\<tau>Exec_mover_a P t i h ([], loc, 0, None) ([v], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil>) h ([] @ [Null], loc, length (compE2 a) + 0, None) ([v] @ [Null], loc, length (compE2 a) + length (compE2 i), None)"
      by(rule AAcc_\<tau>ExecrI2)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil>) h ([Null], loc, length (compE2 a), None) ([v, Null], loc, length (compE2 a) + length (compE2 i), None)" by simp
    also (rtranclp_trans) have "exec_move_a P t (a\<lfloor>i\<rceil>) h ([v, Null], loc, length (compE2 a) + length (compE2 i), None) \<epsilon> h ([v, Null], loc, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto)
    moreover have "\<not> \<tau>move2 (compP2 P) h [v, Null] (a\<lfloor>i\<rceil>) (length (compE2 a) + length (compE2 i)) None"
      by(simp add: \<tau>move2_iff)
    moreover have "\<not> \<tau>move1 P h (a'\<lfloor>i\<rceil>)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from `bsok a n` `bsok i n`
    have "P,a\<lfloor>i\<rceil>,n,h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([v, Null], xs, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAccNull)
    ultimately show ?thesis using s by auto blast
  next
    case (Red1AAccBounds A U I)
    hence [simp]: "a' = addr A" "e' = THROW ArrayIndexOutOfBounds" "i = Val (Intg I)"
      "ta = \<epsilon>" "h' = h" "xs' = xs"
      and hA: "typeof_addr h A = \<lfloor>Array U\<rfloor>" and I: "I <s 0 \<or> int (array_length h A) \<le> sint I" by auto
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t a h (stk, loc, pc, xcp) ([Addr A], loc, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil>) h (stk, loc, pc, xcp) ([Addr A], loc, length (compE2 a), None)"
      by-(rule AAcc_\<tau>ExecrI1)
    also from bisim2[of loc] have "\<tau>Exec_mover_a P t i h ([], loc, 0, None) ([Intg I], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil>) h ([] @ [Addr A], loc, length (compE2 a) + 0, None) ([Intg I] @ [Addr A], loc, length (compE2 a) + length (compE2 i), None)"
      by(rule AAcc_\<tau>ExecrI2)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil>) h ([Addr A], loc, length (compE2 a), None) ([Intg I, Addr A], loc, length (compE2 a) + length (compE2 i), None)" by simp
    also (rtranclp_trans) from I hA
    have "exec_move_a P t (a\<lfloor>i\<rceil>) h ([Intg I, Addr A], loc, length (compE2 a) + length (compE2 i), None) \<epsilon> h ([Intg I, Addr A], loc, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Intg I, Addr A] (a\<lfloor>i\<rceil>) (length (compE2 a) + length (compE2 i)) None"
      by(simp add: \<tau>move2_iff)
    moreover have "\<not> \<tau>move1 P h (a'\<lfloor>i\<rceil>)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from `bsok a n` `bsok i n`
    have "P,a\<lfloor>i\<rceil>,n,h \<turnstile> (THROW ArrayIndexOutOfBounds, xs) \<leftrightarrow> ([Intg I, Addr A], xs, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAccBounds)
    ultimately show ?thesis using s by auto blast
  next
    case (AAcc1Throw1 A)
    note [simp] = `a' = Throw A` `ta = \<epsilon>` `e' = Throw A` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h (Throw A\<lfloor>i\<rceil>)" by(rule \<tau>move1AAccThrow1)
    from bisim1 have "xcp = \<lfloor>A\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>A\<rfloor>"
      with bisim1 `bsok i n`
      have "P, a\<lfloor>i\<rceil>, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.intros)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim1 obtain pc' where "\<tau>Exec_mover_a P t a h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and bisim': "P, a, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil>) h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	by-(rule AAcc_\<tau>ExecrI1)
      moreover from bisim' `bsok i n`
      have "P, a\<lfloor>i\<rceil>, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1AAccThrow1)
      ultimately show ?thesis using \<tau> by auto
    qed
  next
    case (AAcc1Throw2 v ad)
    note [simp] = `a' = Val v` `i = Throw ad` `ta = \<epsilon>` `e' = Throw ad` `h' = h` `xs' = xs`
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t a h (stk, loc, pc, xcp) ([v], loc, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>Throw ad\<rceil>) h (stk, loc, pc, xcp) ([v], loc, length (compE2 a), None)"
      by-(rule AAcc_\<tau>ExecrI1)
    also have "\<tau>Exec_mover_a P t (a\<lfloor>Throw ad\<rceil>) h ([v], loc, length (compE2 a), None) ([Addr ad, v], loc, Suc (length (compE2 a)), \<lfloor>ad\<rfloor>)"
      by(rule \<tau>Execr2step)(auto simp add: exec_move_def exec_meth_instr \<tau>move2_iff \<tau>move1_\<tau>moves1.simps)
    also (rtranclp_trans)
    have "P,a\<lfloor>Throw ad\<rceil>,n,h \<turnstile> (Throw ad, loc) \<leftrightarrow> ([Addr ad] @ [v], loc, (length (compE2 a) + length (compE2 (addr ad))), \<lfloor>ad\<rfloor>)"
      by(rule bisim1AAccThrow2[OF bisim1Throw2 `bsok a n`])(simp)
    moreover have "\<tau>move1 P h (a'\<lfloor>Throw ad\<rceil>)" by(auto intro: \<tau>move1AAccThrow2)
    ultimately show ?thesis using s by auto
  qed
next
  case (bisim1AAcc2 i n i' xs stk loc pc xcp a v1)
  note IH2 = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>i',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,i,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta i i' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `\<And>xs. P,a,n,h \<turnstile> (a, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,i,n,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P,t \<turnstile>1 \<langle>Val v1\<lfloor>i'\<rceil>,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from red show ?case
  proof cases
    case (AAcc1Red2 E')
    note [simp] = `e' = Val v1\<lfloor>E'\<rceil>`
      and red = `P,t \<turnstile>1 \<langle>i',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from IH2[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,i,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta i i' E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    from red have \<tau>: "\<tau>move1 P h (Val v1\<lfloor>i'\<rceil>) = \<tau>move1 P h i'" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    have "no_call2 i pc \<Longrightarrow> no_call2 (a\<lfloor>i\<rceil>) (length (compE2 a) + pc)" by(auto simp add: no_call2_def)
    hence "?exec ta (a\<lfloor>i\<rceil>) (Val v1\<lfloor>i'\<rceil>) (Val v1\<lfloor>E'\<rceil>) h (stk @ [v1]) loc (length (compE2 a) + pc) xcp h' (length (compE2 a) + pc'') (stk'' @ [v1]) loc'' xcp''"
      using exec' \<tau>
      apply(cases "\<tau>move1 P h (Val v1\<lfloor>i'\<rceil>)")
      apply(auto)
      apply(blast intro: AAcc_\<tau>ExecrI2 AAcc_\<tau>ExectI2 exec_move_AAccI2)
      apply(blast intro: AAcc_\<tau>ExecrI2 AAcc_\<tau>ExectI2 exec_move_AAccI2)
      apply(rule exI conjI AAcc_\<tau>ExecrI2 exec_move_AAccI2|assumption)+
      apply(fastsimp simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff split: split_if_asm)
      apply(rule exI conjI AAcc_\<tau>ExecrI2 exec_move_AAccI2|assumption)+
      apply(fastsimp simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff split: split_if_asm)
      apply(rule exI conjI AAcc_\<tau>ExecrI2 exec_move_AAccI2 rtranclp.rtrancl_refl|assumption)+
      apply(fastsimp simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff split: split_if_asm)+
      done
    moreover from bisim' `bsok a n`
    have "P,a\<lfloor>i\<rceil>,n,h' \<turnstile> (Val v1\<lfloor>E'\<rceil>, xs') \<leftrightarrow> (stk''@[v1], loc'', length (compE2 a) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1AAcc2)
    ultimately show ?thesis using \<tau> by auto blast+
  next
    case (Red1AAcc A U I v)
    hence [simp]: "v1 = Addr A" "e' = Val v" "i' = Val (Intg I)"
      "ta = \<epsilon>\<lbrace>\<^bsub>o\<^esub>ReadMem A (ACell (nat (sint I))) v\<rbrace>" "h' = h" "xs' = xs"
      and hA: "typeof_addr h A = \<lfloor>Array U\<rfloor>" and I: "0 <=s I" "sint I < int (array_length h A)"
      and read: "heap_read h A (ACell (nat (sint I))) v" by auto
    have \<tau>: "\<not> \<tau>move1 P h (addr A\<lfloor>Val (Intg I)\<rceil>)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t i h (stk, loc, pc, xcp) ([Intg I], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil>) h (stk @ [Addr A], loc, length (compE2 a) + pc, xcp) ([Intg I] @ [Addr A], loc, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAcc_\<tau>ExecrI2)
    moreover from hA I read
    have "exec_move_a P t (a\<lfloor>i\<rceil>) h ([Intg I, Addr A], loc, length (compE2 a) + length (compE2 i), None)
                              \<epsilon>\<lbrace>\<^bsub>o\<^esub>ReadMem A (ACell (nat (sint I))) v\<rbrace>
                              h ([v], loc, Suc (length (compE2 a) + length (compE2 i)), None)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (compP2 P) h [Intg I, Addr A] (a\<lfloor>i\<rceil>) (length (compE2 a) + length (compE2 i)) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok a n` `bsok i n`
    have "P, a\<lfloor>i\<rceil>, n, h \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (a\<lfloor>i\<rceil>)), None)"
      by-(rule bisim1Val2,auto)
    ultimately show ?thesis using s \<tau> by(auto simp add: ta_upd_simps) blast
  next
    case (Red1AAccNull v)
    note [simp] = `v1 = Null` `i' = Val v` `ta = \<epsilon>` `e' = THROW NullPointer` `h' = h` `xs' = xs`
    from bisim2 have [simp]: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t i h (stk, loc, pc, xcp) ([v], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil>) h (stk @ [Null], loc, length (compE2 a) + pc, xcp) ([v] @ [Null], loc, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAcc_\<tau>ExecrI2)
    moreover have "exec_move_a P t (a\<lfloor>i\<rceil>) h ([v, Null], loc, length (compE2 a) + length (compE2 i), None) \<epsilon> h ([v, Null], loc, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto)
    moreover have "\<not> \<tau>move2 (compP2 P) h [v, Null] (a\<lfloor>i\<rceil>) (length (compE2 a) + length (compE2 i)) None"
      by(simp add: \<tau>move2_iff)
    moreover have "\<not> \<tau>move1 P h (null\<lfloor>i'\<rceil>)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from `bsok a n` `bsok i n`
    have "P,a\<lfloor>i\<rceil>,n,h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([v, Null], xs, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAccNull)
    ultimately show ?thesis by auto blast
  next
    case (Red1AAccBounds A U I)
    hence [simp]: "v1 = Addr A" "e' = THROW ArrayIndexOutOfBounds" "i' = Val (Intg I)"
      "ta = \<epsilon>" "h' = h" "xs' = xs"
      and hA: "typeof_addr h A = \<lfloor>Array U\<rfloor>" and I: "I <s 0 \<or> int (array_length h A) \<le> sint I" by auto
    from bisim2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t i h (stk, loc, pc, xcp) ([Intg I], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil>) h (stk @ [Addr A], loc, length (compE2 a) + pc, xcp) ([Intg I] @ [Addr A], loc, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAcc_\<tau>ExecrI2)
    moreover from I hA
    have "exec_move_a P t (a\<lfloor>i\<rceil>) h ([Intg I, Addr A], loc, length (compE2 a) + length (compE2 i), None) \<epsilon> h ([Intg I, Addr A], loc, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Intg I, Addr A] (a\<lfloor>i\<rceil>) (length (compE2 a) + length (compE2 i)) None"
      by(simp add: \<tau>move2_iff)
    moreover have "\<not> \<tau>move1 P h (addr A\<lfloor>i'\<rceil>)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from `bsok a n` `bsok i n`
    have "P,a\<lfloor>i\<rceil>,n,h \<turnstile> (THROW ArrayIndexOutOfBounds, xs) \<leftrightarrow> ([Intg I, Addr A], xs, length (compE2 a) + length (compE2 i), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAccBounds)
    ultimately show ?thesis using s by auto blast
  next
    case (AAcc1Throw2 A)
    note [simp] = `i' = Throw A` `ta = \<epsilon>` `e' = Throw A` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h (Val v1\<lfloor>Throw A\<rceil>)" by(rule \<tau>move1AAccThrow2)
    from bisim2 have "xcp = \<lfloor>A\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>A\<rfloor>"
      with bisim2 `bsok a n`
      have "P, a\<lfloor>i\<rceil>, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> (stk @ [v1], loc, length (compE2 a) + pc, xcp)"
	by(auto intro: bisim1_bisims1.intros)
      thus ?thesis using \<tau> by(auto)
    next
      assume [simp]: "xcp = None"
      with bisim2 obtain pc' where "\<tau>Exec_mover_a P t i h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and bisim': "P, i, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil>) h (stk @ [v1], loc, length (compE2 a) + pc, None) ([Addr A] @ [v1], loc, length (compE2 a) + pc', \<lfloor>A\<rfloor>)"
	by-(rule AAcc_\<tau>ExecrI2)
      moreover from bisim' `bsok a n`
      have "P, a\<lfloor>i\<rceil>, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A] @ [v1], loc, length (compE2 a) + pc', \<lfloor>A\<rfloor>)"
	by(rule bisim1_bisims1.bisim1AAccThrow2)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case bisim1AAccThrow1 thus ?case by auto
next
  case bisim1AAccThrow2 thus ?case by auto
next
  case bisim1AAccNull thus ?case by auto
next
  case bisim1AAccBounds thus ?case by auto
next
  case (bisim1AAss1 a n a' xs stk loc pc xcp i e)
  note IH1 = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>a',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,a,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta a a' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note IH2 = `\<And>xs e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>i,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,i,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta i i e' h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note IH3 = `\<And>xs e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta e e e' h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,a,n,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,i,n,h \<turnstile> (i, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim3 = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,t \<turnstile>1 \<langle>a'\<lfloor>i\<rceil> := e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (AAss1Red1 E')
    note [simp] = `e' = E'\<lfloor>i\<rceil> := e`
      and red = `P,t \<turnstile>1 \<langle>a',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from red have "\<tau>move1 P h (a'\<lfloor>i\<rceil> := e) = \<tau>move1 P h a'" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from red have "call1 (a'\<lfloor>i\<rceil> := e) = call1 a'" by auto
    moreover from IH1[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,a,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta a a' E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim `bsok i n` `bsok e n`
    have "P,a\<lfloor>i\<rceil> := e,n,h' \<turnstile> (E'\<lfloor>i\<rceil> := e, xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1AAss1)
    moreover { 
      assume "no_call2 a pc"
      hence "no_call2 (a\<lfloor>i\<rceil> := e) pc \<or> pc = length (compE2 a)" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: AAss_\<tau>ExecrI1 AAss_\<tau>ExectI1 exec_move_AAssI1)+
  next
    case (AAss1Red2 E' v)
    note [simp] = `a' = Val v` `e' = Val v\<lfloor>E'\<rceil> := e`
      and red = `P,t \<turnstile>1 \<langle>i,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h (Val v\<lfloor>i\<rceil> := e) = \<tau>move1 P h i" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim1 have s: "xcp = None" "xs = loc"
      and exec1: "\<tau>Exec_mover_a P t a h (stk, loc, pc, None) ([v], xs, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1)
    from exec1 have "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk, loc, pc, None) ([v], xs, length (compE2 a), None)"
      by(rule AAss_\<tau>ExecrI1)
    moreover
    from IH2[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,i,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta i i E' h [] xs 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (a\<lfloor>i\<rceil> := e) (Val v\<lfloor>i\<rceil> := e) (Val v\<lfloor>E'\<rceil> := e) h ([] @ [v]) xs (length (compE2 a) + 0) None h' (length (compE2 a) + pc'') (stk'' @ [v]) loc'' xcp''"
    proof(cases "\<tau>move1 P h (Val v\<lfloor>i\<rceil> := e)")
      case True
      with exec' \<tau> have [simp]: "h = h'" and e: "sim_move i E' P t i h ([], xs, 0, None) (stk'', loc'', pc'', xcp'')" by auto
      from e have "sim_move (a\<lfloor>i\<rceil> := e) (a\<lfloor>E'\<rceil> := e) P t (a\<lfloor>i\<rceil> := e) h ([] @ [v], xs, length (compE2 a) + 0, None) (stk'' @ [v], loc'', length (compE2 a) + pc'', xcp'')"
	by(fastsimp dest: AAss_\<tau>ExecrI2 AAss_\<tau>ExectI2)
      with True show ?thesis by auto
    next
      case False
      with exec' \<tau> obtain pc' stk' loc' xcp'
	where e: "\<tau>Exec_mover_a P t i h ([], xs, 0, None) (stk', loc', pc', xcp')"
	and e': "exec_move_a P t i h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 (compP2 P) h stk' i pc' xcp'" 
        and call: "call1 i = None \<or> no_call2 i 0 \<or> pc' = 0 \<and> stk' = [] \<and> loc' = xs \<and> xcp' = None" by auto
      from e have "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([] @ [v], xs, length (compE2 a) + 0, None) (stk' @ [v], loc', length (compE2 a) + pc', xcp')" by(rule AAss_\<tau>ExecrI2)
      moreover from e' have "exec_move_a P t (a\<lfloor>i\<rceil> := e) h (stk' @ [v], loc', length (compE2 a) + pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'' @ [v], loc'', length (compE2 a) + pc'', xcp'')"
	by(rule exec_move_AAssI2)
      moreover from e' have "pc' < length (compE2 i)" by(auto elim: exec_meth.cases)
      with \<tau>' e' have "\<not> \<tau>move2 (compP2 P) h (stk' @ [v]) (a\<lfloor>i\<rceil> := e) (length (compE2 a) + pc') xcp'"
        by(auto simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff)
      moreover from red have "call1 (a'\<lfloor>i\<rceil> := e) = call1 i" by auto
      moreover have "no_call2 i 0 \<Longrightarrow> no_call2 (a\<lfloor>i\<rceil> := e) (length (compE2 a))"
        by(auto simp add: no_call2_def)
      ultimately show ?thesis using False call
        by(auto simp del: split_paired_Ex call1_calls1.simps) blast
    qed
    moreover from bisim' `bsok a n` `bsok e n`
    have "P,a\<lfloor>i\<rceil> := e,n,h' \<turnstile> (Val v\<lfloor>E'\<rceil> := e, xs') \<leftrightarrow> ((stk'' @ [v]), loc'', length (compE2 a) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1AAss2)
    moreover from bisim1 have "pc \<noteq> length (compE2 a) \<longrightarrow> no_call2 (a\<lfloor>i\<rceil> := e) pc"
      by(auto simp add: no_call2_def dest: bisim_Val_pc_not_Invoke bisim1_pc_length_compE2)
    ultimately show ?thesis using \<tau> exec1 s
      apply(auto simp del: split_paired_Ex call1_calls1.simps split: split_if_asm split del: split_if)
      apply(blast intro: \<tau>Exec_mover_trans|fastsimp elim!: \<tau>Exec_mover_trans simp del: split_paired_Ex call1_calls1.simps)+
      done
  next
    case (AAss1Red3 E' v v')
    note [simp] = `i = Val v'` `a' = Val v` `e' = Val v\<lfloor>Val v'\<rceil> := E'`
      and red = `P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h (Val v\<lfloor>Val v'\<rceil> := e) = \<tau>move1 P h e" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim1 have s: "xcp = None" "xs = loc"
      and exec1: "\<tau>Exec_mover_a P t a h (stk, loc, pc, None) ([] @ [v], xs, length (compE2 a) + 0, None)"
      by(auto dest: bisim1Val2D1)
    from exec1 have "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk, loc, pc, None) ([] @ [v], xs, length (compE2 a) + 0, None)"
      by(rule AAss_\<tau>ExecrI1)
    also from bisim2[of xs] 
    have "\<tau>Exec_mover_a P t i h ([], xs, 0, None) ([v'], xs, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([] @ [v], xs, length (compE2 a) + 0, None) ([v'] @ [v], xs, length (compE2 a) + length (compE2 i), None)"
      by(rule AAss_\<tau>ExecrI2)
    also (rtranclp_trans) from IH3[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e e E' h [] xs 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (a\<lfloor>i\<rceil> := e) (Val v\<lfloor>Val v'\<rceil> := e) (Val v\<lfloor>Val v'\<rceil> := E') h ([] @ [v', v]) xs (length (compE2 a) + length (compE2 i) + 0) None h' (length (compE2 a) + length (compE2 i) + pc'') (stk'' @ [v', v]) loc'' xcp''"
    proof(cases "\<tau>move1 P h (Val v\<lfloor>Val v'\<rceil> := e)")
      case True
      with exec' \<tau> have [simp]: "h = h'" and e: "sim_move e E' P t e h ([], xs, 0, None) (stk'', loc'', pc'', xcp'')" by auto
      from e have "sim_move (Val v\<lfloor>Val v'\<rceil> := e) (Val v\<lfloor>Val v'\<rceil> := E') P t (a\<lfloor>i\<rceil> := e) h ([] @ [v', v], xs, length (compE2 a) + length (compE2 i) + 0, None) (stk'' @ [v', v], loc'', length (compE2 a) + length (compE2 i) + pc'', xcp'')"
	by(fastsimp dest: AAss_\<tau>ExectI3 AAss_\<tau>ExecrI3 simp del: compE2_compEs2.simps)
      with True show ?thesis by auto
    next
      case False
      with exec' \<tau> obtain pc' stk' loc' xcp'
	where e: "\<tau>Exec_mover_a P t e h ([], xs, 0, None) (stk', loc', pc', xcp')"
	and e': "exec_move_a P t e h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 (compP2 P) h stk' e pc' xcp'" 
        and call: "call1 e = None \<or> no_call2 e 0 \<or> pc' = 0 \<and> stk' = [] \<and> loc' = xs \<and> xcp' = None" by auto
      from e have "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([] @ [v', v], xs, length (compE2 a) + length (compE2 i) + 0, None) (stk' @ [v', v], loc', length (compE2 a) + length (compE2 i) + pc', xcp')" by(rule AAss_\<tau>ExecrI3)
      moreover from e' have "exec_move_a P t (a\<lfloor>i\<rceil> := e) h (stk' @ [v', v], loc', length (compE2 a) + length (compE2 i) + pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'' @ [v', v], loc'', length (compE2 a) + length (compE2 i) + pc'', xcp'')"
	by(rule exec_move_AAssI3)
      moreover from e' \<tau>'
      have "\<not> \<tau>move2 (compP2 P) h (stk' @ [v', v]) (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + pc') xcp'"
        by(auto simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff)
      moreover have "call1 (a'\<lfloor>i\<rceil> := e) = call1 e" by simp
      moreover have "no_call2 e 0 \<Longrightarrow> no_call2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i))"
        by(auto simp add: no_call2_def)
      ultimately show ?thesis using False call
        by(auto simp del: split_paired_Ex call1_calls1.simps) blast
    qed
    moreover from bisim' `bsok a n` `bsok i n`
    have "P,a\<lfloor>i\<rceil> := e,n,h' \<turnstile> (Val v\<lfloor>Val v'\<rceil> := E', xs') \<leftrightarrow> ((stk'' @ [v', v]),  loc'', length (compE2 a) + length (compE2 i) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1AAss3) 
    moreover from bisim1 have "pc \<noteq> length (compE2 a) + length (compE2 i) \<longrightarrow> no_call2 (a\<lfloor>i\<rceil> := e) pc"
      by(auto simp add: no_call2_def dest: bisim_Val_pc_not_Invoke bisim1_pc_length_compE2)
    ultimately show ?thesis using \<tau> exec1 s
      apply(auto simp del: split_paired_Ex call1_calls1.simps split: split_if_asm split del: split_if)
      apply(blast intro: \<tau>Exec_mover_trans|fastsimp elim!: \<tau>Exec_mover_trans simp del: split_paired_Ex call1_calls1.simps)+
      done
  next
    case (Red1AAss A U I v U')
    hence [simp]: "a' = addr A" "e' = unit" "i = Val (Intg I)"
      "ta = \<epsilon>\<lbrace>\<^bsub>o\<^esub>WriteMem A (ACell (nat (sint I))) v\<rbrace>" "xs' = xs" "e = Val v"
      and hA: "typeof_addr h A = \<lfloor>Array U\<rfloor>" and I: "0 <=s I" "sint I < int (array_length h A)" 
      and v: "typeof\<^bsub>h\<^esub> v = \<lfloor>U'\<rfloor>" "P \<turnstile> U' \<le> U"
      and h': "heap_write h A (ACell (nat (sint I))) v h'" by auto
    have \<tau>: "\<not> \<tau>move1 P h (AAss (addr A) (Val (Intg I)) (Val v))" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t a h (stk, loc, pc, xcp) ([] @ [Addr A], loc, length (compE2 a) + 0, None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk, loc, pc, xcp) ([] @ [Addr A], loc, length (compE2 a) + 0, None)"
      by-(rule AAss_\<tau>ExecrI1)
    also from bisim2[of loc]
    have "\<tau>Exec_mover_a P t i h ([], loc, 0, None) ([Intg I], loc, length (compE2 i) + 0, None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([] @ [Addr A], loc, length (compE2 a) + 0, None) ([Intg I] @ [Addr A], loc, length (compE2 a) + (length (compE2 i) + 0), None)"
      by(rule AAss_\<tau>ExecrI2)
    also (rtranclp_trans) have "[Intg I] @ [Addr A] = [] @ [Intg I, Addr A]" by simp
    also note add_assoc[symmetric]
    also from bisim3[of loc] have "\<tau>Exec_mover_a P t e h ([], loc, 0, None) ([v], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None) ([v] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by(rule AAss_\<tau>ExecrI3)
    also (rtranclp_trans) from hA I v h'
    have "exec_move_a P t (a\<lfloor>i\<rceil> := e) h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)
                                 \<epsilon>\<lbrace>\<^bsub>o\<^esub>WriteMem A (ACell (nat (sint I))) v\<rbrace>
                                 h' ([], loc, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: compP2_def is_Ref_def)
    moreover have "\<tau>move2 (compP2 P) h [v, Intg I, Addr A] (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (unit, loc) \<leftrightarrow> ([], loc, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None)"
      by(rule bisim1_bisims1.bisim1AAss4)
    ultimately show ?thesis using s \<tau> by(auto simp add: ta_upd_simps) blast
  next
    case (Red1AAssNull v v')
    note [simp] = `a' = null` `e' = THROW NullPointer` `i = Val v` `xs' = xs` `ta = \<epsilon>` `h' = h` `e = Val v'`
    have \<tau>: "\<not> \<tau>move1 P h (AAss null (Val v) (Val v'))" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t a h (stk, loc, pc, xcp) ([] @ [Null], loc, length (compE2 a) + 0, None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk, loc, pc, xcp) ([] @ [Null], loc, length (compE2 a) + 0, None)"
      by-(rule AAss_\<tau>ExecrI1)
    also from bisim2[of loc] have "\<tau>Exec_mover_a P t i h ([], loc, 0, None) ([v], loc, length (compE2 i) + 0, None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([] @ [Null], loc, length (compE2 a) + 0, None) ([v] @ [Null], loc, length (compE2 a) + (length (compE2 i) + 0), None)"
      by(rule AAss_\<tau>ExecrI2)
    also (rtranclp_trans) have "[v] @ [Null] = [] @ [v, Null]" by simp
    also note add_assoc[symmetric]
    also from bisim3[of loc] have "\<tau>Exec_mover_a P t e h ([], loc, 0, None) ([v'], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([] @ [v, Null], loc, length (compE2 a) + length (compE2 i) + 0, None) ([v'] @ [v, Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by(rule AAss_\<tau>ExecrI3)
    also (rtranclp_trans)
    have "exec_move_a P t (a\<lfloor>i\<rceil> := e) h ([v', v, Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h ([v', v, Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (compP2 P) h [v', v, Null] (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([v', v, Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssNull)
    ultimately show ?thesis using s \<tau> by auto blast
  next
    case (Red1AAssBounds A U I v)
    hence [simp]: "a' = addr A" "e' = THROW ArrayIndexOutOfBounds" "i = Val (Intg I)" "xs' = xs" "ta = \<epsilon>" "h' = h" "e = Val v"
      and hA: "typeof_addr h A = \<lfloor>Array U\<rfloor>" and I: "I <s 0 \<or> int (array_length h A) \<le> sint I" by auto
    have \<tau>: "\<not> \<tau>move1 P h (AAss (addr A) i e)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t a h (stk, loc, pc, xcp) ([] @ [Addr A], loc, length (compE2 a) + 0, None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk, loc, pc, xcp) ([] @ [Addr A], loc, length (compE2 a) + 0, None)"
      by-(rule AAss_\<tau>ExecrI1)
    also from bisim2[of loc] 
    have "\<tau>Exec_mover_a P t i h ([], loc, 0, None) ([Intg I], loc, length (compE2 i) + 0, None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([] @ [Addr A], loc, length (compE2 a) + 0, None) ([Intg I] @ [Addr A], loc, length (compE2 a) + (length (compE2 i) + 0), None)"
      by(rule AAss_\<tau>ExecrI2)
    also (rtranclp_trans) have "[Intg I] @ [Addr A] = [] @ [Intg I, Addr A]" by simp
    also note add_assoc[symmetric]
    also from bisim3[of loc]
    have "\<tau>Exec_mover_a P t e h ([], loc, 0, None) ([v], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None) ([v] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by(rule AAss_\<tau>ExecrI3)
    also (rtranclp_trans) from hA I
    have "exec_move_a P t (a\<lfloor>i\<rceil> := e) h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (compP2 P) h [v, Intg I, Addr A] (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW ArrayIndexOutOfBounds, loc) \<leftrightarrow> ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssBounds)
    ultimately show ?thesis using s \<tau> by auto blast
  next
    case (Red1AAssStore A U I v U')
    hence [simp]: "a' = addr A" "e' = THROW ArrayStore" "i = Val (Intg I)" "xs' = xs" "ta = \<epsilon>" "h' = h" "e = Val v"
      and hA: "typeof_addr h A = \<lfloor>Array U\<rfloor>" and I: "0 <=s I" "sint I < int (array_length h A)" 
      and U: "\<not> P \<turnstile> U' \<le> U" "typeof\<^bsub>h\<^esub> v = \<lfloor>U'\<rfloor>" by auto
    have \<tau>: "\<not> \<tau>move1 P h (AAss (addr A) i e)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t a h (stk, loc, pc, xcp) ([] @ [Addr A], loc, length (compE2 a) + 0, None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk, loc, pc, xcp) ([] @ [Addr A], loc, length (compE2 a) + 0, None)"
      by-(rule AAss_\<tau>ExecrI1)
    also from bisim2[of loc] 
    have "\<tau>Exec_mover_a P t i h ([], loc, 0, None) ([Intg I], loc, length (compE2 i) + 0, None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([] @ [Addr A], loc, length (compE2 a) + 0, None) ([Intg I] @ [Addr A], loc, length (compE2 a) + (length (compE2 i) + 0), None)"
      by(rule AAss_\<tau>ExecrI2)
    also (rtranclp_trans) have "[Intg I] @ [Addr A] = [] @ [Intg I, Addr A]" by simp
    also note add_assoc[symmetric]
    also from bisim3[of loc] 
    have "\<tau>Exec_mover_a P t e h ([], loc, 0, None) ([v], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None) ([v] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by(rule AAss_\<tau>ExecrI3)
    also (rtranclp_trans) from hA I U
    have "exec_move_a P t (a\<lfloor>i\<rceil> := e) h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                  h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def compP2_def)
    moreover have "\<tau>move2 (compP2 P) h [v, Intg I, Addr A] (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW ArrayStore, loc) \<leftrightarrow> ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssStore)
    ultimately show ?thesis using s \<tau> by auto blast
  next
    case (AAss1Throw1 A)
    hence [simp]: "a' = Throw A" "ta = \<epsilon>" "e' = Throw A" "h' = h" "xs' = xs" by auto
    have \<tau>: "\<tau>move1 P h (Throw A\<lfloor>i\<rceil> := e)" by(rule \<tau>move1AAssThrow1)
    from bisim1 have "xcp = \<lfloor>A\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>A\<rfloor>"
      with bisim1 `bsok i n` `bsok e n`
      have "P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.intros)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim1 obtain pc' where "\<tau>Exec_mover_a P t a h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and bisim': "P, a, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	by-(rule AAss_\<tau>ExecrI1)
      moreover from bisim' `bsok i n` `bsok e n`
      have "P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1AAssThrow1)
      ultimately show ?thesis using \<tau> by auto
    qed
  next
    case (AAss1Throw2 v ad)
    note [simp] = `a' = Val v` `i = Throw ad` `ta = \<epsilon>` `e' = Throw ad` `h' = h` `xs' = xs`
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t a h (stk, loc, pc, xcp) ([v], loc, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>Throw ad\<rceil> := e) h (stk, loc, pc, xcp) ([v], loc, length (compE2 a), None)"
      by-(rule AAss_\<tau>ExecrI1)
    also have "\<tau>Exec_mover_a P t (a\<lfloor>Throw ad\<rceil>:=e) h ([v], loc, length (compE2 a), None) ([Addr ad, v], loc, Suc (length (compE2 a)), \<lfloor>ad\<rfloor>)"
      by(rule \<tau>Execr2step)(auto simp add: exec_move_def exec_meth_instr \<tau>move2_iff \<tau>move1_\<tau>moves1.simps)
    also (rtranclp_trans)
    have "P,a\<lfloor>Throw ad\<rceil>:=e,n,h \<turnstile> (Throw ad, loc) \<leftrightarrow> ([Addr ad] @ [v], loc, (length (compE2 a) + length (compE2 (addr ad))), \<lfloor>ad\<rfloor>)"
      by(rule bisim1AAssThrow2[OF bisim1Throw2 `bsok a n` `bsok e n`])(simp)
    moreover have "\<tau>move1 P h (a'\<lfloor>Throw ad\<rceil>:=e)" by(auto intro: \<tau>move1AAssThrow2)
    ultimately show ?thesis using s by auto
  next
    case (AAss1Throw3 va vi ad)
    note [simp] = `a' = Val va` `i = Val vi` `e = Throw ad` `ta = \<epsilon>` `e' = Throw ad` `h' = h` `xs' = xs`
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t a h (stk, loc, pc, xcp) ([va], loc, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := Throw ad) h (stk, loc, pc, xcp) ([va], loc, length (compE2 a), None)"
      by-(rule AAss_\<tau>ExecrI1)
    also from bisim2[of loc] have "\<tau>Exec_mover_a P t i h ([], loc, 0, None) ([vi], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    from AAss_\<tau>ExecrI2[OF this, of a e va]
    have "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := Throw ad) h ([va], loc, length (compE2 a), None) ([vi, va], loc, length (compE2 a) + length (compE2 i), None)" by simp
    also (rtranclp_trans)
    have "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil>:=Throw ad) h ([vi, va], loc, length (compE2 a) + length (compE2 i), None) ([Addr ad, vi, va], loc, Suc (length (compE2 a) + length (compE2 i)), \<lfloor>ad\<rfloor>)"
      by(rule \<tau>Execr2step)(auto simp add: exec_move_def exec_meth_instr \<tau>move2_iff \<tau>move1_\<tau>moves1.simps)
    also (rtranclp_trans)
    have "P,a\<lfloor>i\<rceil>:=Throw ad,n,h \<turnstile> (Throw ad, loc) \<leftrightarrow> ([Addr ad] @ [vi, va], loc, (length (compE2 a) + length (compE2 i) + length (compE2 (addr ad))), \<lfloor>ad\<rfloor>)"
      by(rule bisim1AAssThrow3[OF bisim1Throw2 `bsok a n` `bsok i n`])(simp)
    moreover have "\<tau>move1 P h (AAss a' (Val vi) (Throw ad))" by(auto intro: \<tau>move1AAssThrow3)
    ultimately show ?thesis using s by auto
  qed
next
  case (bisim1AAss2 i n i' xs stk loc pc xcp a e v1)
  note IH2 = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>i',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,i,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta i i' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note IH3 = `\<And>xs e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta e e e' h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note bisim2 = `P,i,n,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim1 = `\<And>xs. P,a,n,h \<turnstile> (a, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim3 = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,t \<turnstile>1 \<langle>Val v1\<lfloor>i'\<rceil> := e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (AAss1Red2 E')
    note [simp] = `e' = Val v1\<lfloor>E'\<rceil> := e`
      and red = `P,t \<turnstile>1 \<langle>i',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h (Val v1\<lfloor>i'\<rceil> := e) = \<tau>move1 P h i'" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from IH2[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,i,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta i i' E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (a\<lfloor>i\<rceil> := e) (Val v1\<lfloor>i'\<rceil> := e) (Val v1\<lfloor>E'\<rceil> := e) h (stk @ [v1]) loc (length (compE2 a) + pc) xcp h' (length (compE2 a) + pc'') (stk'' @ [v1]) loc'' xcp''"
    proof(cases "\<tau>move1 P h (Val v1\<lfloor>i'\<rceil> := e)")
      case True
      with exec' \<tau> have [simp]: "h = h'" and e: "sim_move i' E' P t i h (stk, loc, pc, xcp) (stk'', loc'', pc'', xcp'')" by auto
      from e have "sim_move (Val v1\<lfloor>i'\<rceil> := e) (Val v1\<lfloor>E'\<rceil> := e) P t (a\<lfloor>i\<rceil> := e) h (stk @ [v1], loc, length (compE2 a) + pc, xcp) (stk'' @ [v1], loc'', length (compE2 a) + pc'', xcp'')"
	by(fastsimp dest: AAss_\<tau>ExecrI2 AAss_\<tau>ExectI2 simp del: compE2_compEs2.simps)
      with True show ?thesis by auto
    next
      case False
      with exec' \<tau> obtain pc' stk' loc' xcp'
	where e: "\<tau>Exec_mover_a P t i h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
	and e': "exec_move_a P t i h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 (compP2 P) h stk' i pc' xcp'" 
        and call: "call1 i' = None \<or> no_call2 i pc \<or> pc' = pc \<and> stk' = stk \<and> loc' = loc \<and> xcp' = xcp" by auto
      from e have "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk @ [v1], loc, length (compE2 a) + pc, xcp) (stk' @ [v1], loc', length (compE2 a) + pc', xcp')" by(rule AAss_\<tau>ExecrI2)
      moreover from e' have "exec_move_a P t (a\<lfloor>i\<rceil> := e) h (stk' @ [v1], loc', length (compE2 a) + pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'' @ [v1], loc'', length (compE2 a) + pc'', xcp'')"
	by(rule exec_move_AAssI2)
      moreover from e' have "pc' < length (compE2 i)" by(auto elim: exec_meth.cases)
      with \<tau>' e' have "\<not> \<tau>move2 (compP2 P) h (stk' @ [v1]) (a\<lfloor>i\<rceil> := e) (length (compE2 a) + pc') xcp'"
        by(auto simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff)
      moreover from red have "call1 (Val v1\<lfloor>i'\<rceil> := e) = call1 i'" by auto
      moreover have "no_call2 i pc \<Longrightarrow> no_call2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + pc)"
        by(auto simp add: no_call2_def)
      ultimately show ?thesis using False call by(auto simp del: split_paired_Ex call1_calls1.simps) 
    qed
    moreover from bisim' `bsok a n` `bsok e n`
    have "P,a\<lfloor>i\<rceil> := e,n,h' \<turnstile> (Val v1\<lfloor>E'\<rceil> := e, xs') \<leftrightarrow> ((stk'' @ [v1]),  loc'', length (compE2 a) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1AAss2)
    ultimately show ?thesis
      apply(auto simp del: split_paired_Ex call1_calls1.simps split: split_if_asm split del: split_if)
      apply(blast intro: \<tau>Exec_mover_trans)+
      done
  next
    case (AAss1Red3 E' v')
    note [simp] = `i' = Val v'` `e' = Val v1\<lfloor>Val v'\<rceil> := E'`
      and red = `P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h (Val v1\<lfloor>Val v'\<rceil> := e) = \<tau>move1 P h e"
      by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim2 have s: "xcp = None" "xs = loc"
      and exec1: "\<tau>Exec_mover_a P t i h (stk, loc, pc, xcp) ([v'], xs, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk @ [v1], loc, length (compE2 a) + pc, xcp) ([v'] @ [v1], xs, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAss_\<tau>ExecrI2)
    moreover from IH3[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e e E' h [] xs 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (a\<lfloor>i\<rceil> := e) (Val v1\<lfloor>Val v'\<rceil> := e) (Val v1\<lfloor>Val v'\<rceil> := E') h ([] @ [v', v1]) xs (length (compE2 a) + length (compE2 i) + 0) None h' (length (compE2 a) + length (compE2 i) + pc'') (stk'' @ [v', v1]) loc'' xcp''"
    proof(cases "\<tau>move1 P h (Val v1\<lfloor>Val v'\<rceil> := e)")
      case True
      with exec' \<tau> have [simp]: "h = h'"
        and e: "sim_move e E' P t e h ([], xs, 0, None) (stk'', loc'', pc'', xcp'')" by auto
      from e have "sim_move (Val v1\<lfloor>Val v'\<rceil> := e) (Val v1\<lfloor>Val v'\<rceil> := E') P t (a\<lfloor>i\<rceil> := e) h ([] @ [v', v1], xs, length (compE2 a) + length (compE2 i) + 0, None) (stk'' @ [v', v1], loc'', length (compE2 a) + length (compE2 i) + pc'', xcp'')"
	by(fastsimp dest: AAss_\<tau>ExectI3 AAss_\<tau>ExecrI3 simp del: compE2_compEs2.simps)
      with True show ?thesis by auto
    next
      case False
      with exec' \<tau> obtain pc' stk' loc' xcp'
	where e: "\<tau>Exec_mover_a P t e h ([], xs, 0, None) (stk', loc', pc', xcp')"
	and e': "exec_move_a P t e h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 (compP2 P) h stk' e pc' xcp'" 
        and call: "call1 e = None \<or> no_call2 e 0 \<or> pc' = 0 \<and> stk' = [] \<and> loc' = xs \<and> xcp' = None" by auto
      from e have "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([] @ [v', v1], xs, length (compE2 a) + length (compE2 i) + 0, None) (stk' @ [v', v1], loc', length (compE2 a) + length (compE2 i) + pc', xcp')" by(rule AAss_\<tau>ExecrI3)
      moreover from e' have "exec_move_a P t (a\<lfloor>i\<rceil> := e) h (stk' @ [v', v1], loc', length (compE2 a) + length (compE2 i) + pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'' @ [v', v1], loc'', length (compE2 a) + length (compE2 i) + pc'', xcp'')"
	by(rule exec_move_AAssI3)
      moreover from e' \<tau>' have "\<not> \<tau>move2 (compP2 P) h (stk' @ [v', v1]) (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + pc') xcp'"
        by(auto simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff)
      moreover from red have "call1 (Val v1\<lfloor>Val v'\<rceil> := e) = call1 e" by auto
      moreover have "no_call2 e 0 \<Longrightarrow> no_call2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i))"
        by(auto simp add: no_call2_def)
      ultimately show ?thesis using False call by(auto simp del: split_paired_Ex call1_calls1.simps) blast 
    qed
    moreover from bisim' `bsok a n` `bsok i n`
    have "P,a\<lfloor>i\<rceil> := e,n,h' \<turnstile> (Val v1\<lfloor>Val v'\<rceil> := E', xs') \<leftrightarrow> ((stk'' @ [v', v1]),  loc'', length (compE2 a) + length (compE2 i) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1AAss3)
    moreover from bisim2 have "pc \<noteq> length (compE2 i) \<longrightarrow> no_call2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + pc)"
      by(auto simp add: no_call2_def dest: bisim_Val_pc_not_Invoke bisim1_pc_length_compE2)
    ultimately show ?thesis using \<tau> exec1 s
      apply(auto simp del: split_paired_Ex call1_calls1.simps split: split_if_asm split del: split_if)
      apply(blast intro: \<tau>Exec_mover_trans|fastsimp elim!: \<tau>Exec_mover_trans simp del: split_paired_Ex call1_calls1.simps)+
      done
  next
    case (Red1AAss A U I v U')
    hence [simp]: "v1 = Addr A" "e' = unit" "i' = Val (Intg I)"
      "ta = \<epsilon>\<lbrace>\<^bsub>o\<^esub>WriteMem A (ACell (nat (sint I))) v\<rbrace>" "xs' = xs" "e = Val v"
      and hA: "typeof_addr h A = \<lfloor>Array U\<rfloor>" and I: "0 <=s I" "sint I < int (array_length h A)"
      and v: "typeof\<^bsub>h\<^esub> v = \<lfloor>U'\<rfloor>" "P \<turnstile> U' \<le> U"
      and h': "heap_write h A (ACell (nat (sint I))) v h'" by auto
    have \<tau>: "\<not> \<tau>move1 P h (AAss (addr A) (Val (Intg I)) (Val v))" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t i h (stk, loc, pc, xcp) ([Intg I], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk @ [Addr A], loc, length (compE2 a) + pc, xcp) ([Intg I] @ [Addr A], loc, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAss_\<tau>ExecrI2)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk @ [Addr A], loc, length (compE2 a) + pc, xcp) ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None)" by simp
    also from bisim3[of loc] have "\<tau>Exec_mover_a P t e h ([], loc, 0, None) ([v], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None) ([v] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by(rule AAss_\<tau>ExecrI3)
    also (rtranclp_trans) from hA I v h'
    have "exec_move_a P t (a\<lfloor>i\<rceil> := e) h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)
                                 \<epsilon>\<lbrace>\<^bsub>o\<^esub>WriteMem A (ACell (nat (sint I))) v\<rbrace>
                                 h' ([], loc, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: compP2_def is_Ref_def)
    moreover have "\<tau>move2 (compP2 P) h [v, Intg I, Addr A] (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (unit, loc) \<leftrightarrow> ([], loc, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None)"
      by(rule bisim1_bisims1.bisim1AAss4)
    ultimately show ?thesis using s \<tau> by(auto simp add: ta_upd_simps) blast
  next
    case (Red1AAssNull v v')
    note [simp] = `v1 = Null` `e' = THROW NullPointer` `i' = Val v` `xs' = xs` `ta = \<epsilon>` `h' = h` `e = Val v'`
    have \<tau>: "\<not> \<tau>move1 P h (AAss null (Val v) (Val v'))" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t i h (stk, loc, pc, xcp) ([v], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk @ [Null], loc, length (compE2 a) + pc, xcp) ([v] @ [Null], loc, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAss_\<tau>ExecrI2)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk @ [Null], loc, length (compE2 a) + pc, xcp) ([] @ [v, Null], loc, length (compE2 a) + length (compE2 i) + 0, None)" by simp
    also from bisim3[of loc] have "\<tau>Exec_mover_a P t e h ([], loc, 0, None) ([v'], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([] @ [v, Null], loc, length (compE2 a) + length (compE2 i) + 0, None) ([v'] @ [v, Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by(rule AAss_\<tau>ExecrI3)
    also (rtranclp_trans)
    have "exec_move_a P t (a\<lfloor>i\<rceil> := e) h ([v', v, Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h ([v', v, Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (compP2 P) h [v', v, Null] (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([v', v, Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssNull)
    ultimately show ?thesis using s \<tau> by auto blast
  next
    case (Red1AAssBounds A U I v)
    hence [simp]: "v1 = Addr A" "e' = THROW ArrayIndexOutOfBounds" "i' = Val (Intg I)" "xs' = xs" "ta = \<epsilon>" "h' = h" "e = Val v"
      and hA: "typeof_addr h A = \<lfloor>Array U\<rfloor>" and I: "I <s 0 \<or> int (array_length h A) \<le> sint I" by auto
    have \<tau>: "\<not> \<tau>move1 P h (addr A\<lfloor>i'\<rceil> := e)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t i h (stk, loc, pc, xcp) ([Intg I], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk @ [Addr A], loc, length (compE2 a) + pc, xcp) ([Intg I] @ [Addr A], loc, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAss_\<tau>ExecrI2)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk @ [Addr A], loc, length (compE2 a) + pc, xcp) ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None)" by simp
    also from bisim3[of loc] have "\<tau>Exec_mover_a P t e h ([], loc, 0, None) ([v], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None) ([v] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by(rule AAss_\<tau>ExecrI3)
    also (rtranclp_trans) from hA I
    have "exec_move_a P t (a\<lfloor>i\<rceil> := e) h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (compP2 P) h [v, Intg I, Addr A] (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW ArrayIndexOutOfBounds, loc) \<leftrightarrow> ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssBounds)
    ultimately show ?thesis using s \<tau> by auto blast
  next
    case (Red1AAssStore A U I v U')
    hence [simp]: "v1 = Addr A" "e' = THROW ArrayStore" "i' = Val (Intg I)" "xs' = xs" "ta = \<epsilon>" "h' = h" "e = Val v"
      and hA: "typeof_addr h A = \<lfloor>Array U\<rfloor>" and I: "0 <=s I" "sint I < int (array_length h A)" 
      and U: "\<not> P \<turnstile> U' \<le> U" "typeof\<^bsub>h\<^esub> v = \<lfloor>U'\<rfloor>" by auto
    have \<tau>: "\<not> \<tau>move1 P h (addr A\<lfloor>i'\<rceil> := e)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t i h (stk, loc, pc, xcp) ([Intg I], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk @ [Addr A], loc, length (compE2 a) + pc, xcp) ([Intg I] @ [Addr A], loc, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAss_\<tau>ExecrI2)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk @ [Addr A], loc, length (compE2 a) + pc, xcp) ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None)" by simp
    also from bisim3[of loc] 
    have "\<tau>Exec_mover_a P t e h ([], loc, 0, None) ([v], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h ([] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + 0, None) ([v] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by(rule AAss_\<tau>ExecrI3)
    also (rtranclp_trans) from hA I U
    have "exec_move_a P t (a\<lfloor>i\<rceil> := e) h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>)"
      unfolding exec_move_def by- (rule exec_instr, auto simp add: is_Ref_def compP2_def)
    moreover have "\<tau>move2 (compP2 P) h [v, Intg I, Addr A] (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW ArrayStore, loc) \<leftrightarrow> ([v, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssStore)
    ultimately show ?thesis using s \<tau> by auto fast
  next
    case (AAss1Throw2 A)
    note [simp] = `i' = Throw A` `ta = \<epsilon>` `e' = Throw A` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h (Val v1\<lfloor>Throw A\<rceil> := e)" by(rule \<tau>move1AAssThrow2)
    from bisim2 have "xcp = \<lfloor>A\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>A\<rfloor>"
      with bisim2 `bsok a n` `bsok e n`
      have "P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> (stk @ [v1], loc, length (compE2 a) + pc, xcp)"
	by(auto intro: bisim1_bisims1.intros)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim2 obtain pc' where "\<tau>Exec_mover_a P t i h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and bisim': "P, i, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk @ [v1], loc, length (compE2 a) + pc, None) ([Addr A] @ [v1], loc, length (compE2 a) + pc', \<lfloor>A\<rfloor>)"
	by-(rule AAss_\<tau>ExecrI2)
      moreover from bisim' `bsok a n` `bsok e n`
      have "P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A] @ [v1], loc, length (compE2 a) +  pc', \<lfloor>A\<rfloor>)"
	by(rule bisim1_bisims1.bisim1AAssThrow2)
      ultimately show ?thesis using \<tau> by auto
    qed
  next
    case (AAss1Throw3 vi ad)
    note [simp] = `i' = Val vi` `e = Throw ad` `ta = \<epsilon>` `e' = Throw ad` `h' = h` `xs' = xs`
    from bisim2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t i h (stk, loc, pc, xcp) ([vi], loc, length (compE2 i), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := Throw ad) h (stk @ [v1], loc, length (compE2 a) + pc, xcp) ([vi] @ [v1], loc, length (compE2 a) + length (compE2 i), None)"
      by-(rule AAss_\<tau>ExecrI2)
    also have "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil>:=Throw ad) h ([vi] @ [v1], loc, length (compE2 a) + length (compE2 i), None) ([Addr ad, vi, v1], loc, Suc (length (compE2 a) + length (compE2 i)), \<lfloor>ad\<rfloor>)"
      by(rule \<tau>Execr2step)(auto simp add: exec_move_def exec_meth_instr \<tau>move2_iff \<tau>move1_\<tau>moves1.simps)
    also (rtranclp_trans)
    have "P,a\<lfloor>i\<rceil>:=Throw ad,n,h \<turnstile> (Throw ad, loc) \<leftrightarrow> ([Addr ad] @ [vi, v1], loc, (length (compE2 a) + length (compE2 i) + length (compE2 (addr ad))), \<lfloor>ad\<rfloor>)"
      by(rule bisim1AAssThrow3[OF bisim1Throw2 `bsok a n` `bsok i n`])(simp)
    moreover have "\<tau>move1 P h (AAss (Val v1) (Val vi) (Throw ad))" by(auto intro: \<tau>move1AAssThrow3)
    ultimately show ?thesis using s by auto
  qed auto
next
  case (bisim1AAss3 e n ee xs stk loc pc xcp a i v v')
  note IH3 = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>ee,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e ee e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim3 = `P,e,n,h \<turnstile> (ee, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  from `P,t \<turnstile>1 \<langle>Val v\<lfloor>Val v'\<rceil> := ee,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (AAss1Red3 E')
    note [simp] = `e' = Val v\<lfloor>Val v'\<rceil> := E'`
      and red = `P,t \<turnstile>1 \<langle>ee,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h (Val v\<lfloor>Val v'\<rceil> := ee) = \<tau>move1 P h ee" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from IH3[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e ee E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have "no_call2 e pc \<Longrightarrow> no_call2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) +  pc)" 
      by(auto simp add: no_call2_def)
    hence "?exec ta (a\<lfloor>i\<rceil> := e) (Val v\<lfloor>Val v'\<rceil> := ee) (Val v\<lfloor>Val v'\<rceil> := E') h (stk @ [v', v]) loc (length (compE2 a) + length (compE2 i) + pc) xcp h' (length (compE2 a) + length (compE2 i) + pc'') (stk'' @ [v', v]) loc'' xcp''"
      using exec' \<tau>
      apply(cases "\<tau>move1 P h (Val v\<lfloor>Val v'\<rceil> := ee)")
      apply(auto)
      apply(blast intro: AAss_\<tau>ExecrI3 AAss_\<tau>ExectI3 exec_move_AAssI3)
      apply(blast intro: AAss_\<tau>ExecrI3 AAss_\<tau>ExectI3 exec_move_AAssI3)
      apply(rule exI conjI AAss_\<tau>ExecrI3 exec_move_AAssI3|assumption)+
      apply(fastsimp simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff split: split_if_asm)
      apply(rule exI conjI AAss_\<tau>ExecrI3 exec_move_AAssI3|assumption)+
      apply(fastsimp simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff split: split_if_asm)
      apply(rule exI conjI AAss_\<tau>ExecrI3 exec_move_AAssI3 rtranclp.rtrancl_refl|assumption)+
      apply(fastsimp simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff split: split_if_asm)+
      done
    moreover from bisim' `bsok a n` `bsok i n`
    have "P,a\<lfloor>i\<rceil> := e,n,h' \<turnstile> (Val v\<lfloor>Val v'\<rceil> := E', xs') \<leftrightarrow> (stk''@[v',v], loc'', length (compE2 a) + length (compE2 i) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1AAss3)
    ultimately show ?thesis using \<tau> by auto blast+
  next
    case (Red1AAss A U I V U')
    hence [simp]: "v = Addr A" "e' = unit" "v' = Intg I" "xs' = xs" "ee = Val V"
      "ta = \<epsilon>\<lbrace>\<^bsub>o\<^esub>WriteMem A (ACell (nat (sint I))) V\<rbrace>"
      and hA: "typeof_addr h A = \<lfloor>Array U\<rfloor>" and I: "0 <=s I" "sint I < int (array_length h A)" 
      and v: "typeof\<^bsub>h\<^esub> V = \<lfloor>U'\<rfloor>" "P \<turnstile> U' \<le> U"
      and h': "heap_write h A (ACell (nat (sint I))) V h'" by auto
    have \<tau>: "\<not> \<tau>move1 P h (AAss (addr A) (Val (Intg I)) (Val V))" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim3 have s: "xcp = None" "xs = loc"
      and exec1: "\<tau>Exec_mover_a P t e h (stk, loc, pc, xcp) ([V], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + pc, xcp) ([V] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by-(rule AAss_\<tau>ExecrI3)
    moreover from hA I v h'
    have "exec_move_a P t (a\<lfloor>i\<rceil> := e) h ([V, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) 
                                 \<epsilon>\<lbrace>\<^bsub>o\<^esub>WriteMem A (ACell (nat (sint I))) V\<rbrace>
                                 h' ([], loc, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None)"
     unfolding exec_move_def by-(rule exec_instr, auto simp add: compP2_def is_Ref_def)
    moreover have "\<tau>move2 (compP2 P) h [V, Intg I, Addr A] (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (unit, loc) \<leftrightarrow> ([], loc, Suc (length (compE2 a) + length (compE2 i) + length (compE2 e)), None)"
      by(rule bisim1_bisims1.bisim1AAss4)
    ultimately show ?thesis using s \<tau> by(auto simp add: ta_upd_simps) blast
  next
    case (Red1AAssNull V')
    note [simp] = `v = Null` `e' = THROW NullPointer` `xs' = xs` `ta = \<epsilon>` `h' = h` `ee = Val V'`
    have \<tau>: "\<not> \<tau>move1 P h (AAss null (Val v') (Val V'))" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim3 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t e h (stk, loc, pc, xcp) ([V'], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk @ [v', Null], loc, length (compE2 a) + length (compE2 i) + pc, xcp) ([V'] @ [v', Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by-(rule AAss_\<tau>ExecrI3)
    moreover
    have "exec_move_a P t (a\<lfloor>i\<rceil> := e) h ([V', v', Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h ([V', v', Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (compP2 P) h [V', v', Null] (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([V', v', Null], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssNull)
    ultimately show ?thesis using s \<tau> by auto blast
  next
    case (Red1AAssBounds A U I V)
    hence [simp]: "v = Addr A" "e' = THROW ArrayIndexOutOfBounds" "v' = Intg I" "xs' = xs" "ta = \<epsilon>" "h' = h" "ee = Val V"
      and hA: "typeof_addr h A = \<lfloor>Array U\<rfloor>" and I: "I <s 0 \<or> int (array_length h A) \<le> sint I" by auto
    have \<tau>: "\<not> \<tau>move1 P h (addr A\<lfloor>Val (Intg I)\<rceil> := ee)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim3 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t e h (stk, loc, pc, xcp) ([V], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + pc, xcp) ([V] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by-(rule AAss_\<tau>ExecrI3)
    moreover from hA I
    have "exec_move_a P t (a\<lfloor>i\<rceil> := e) h ([V, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h ([V, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (compP2 P) h [V, Intg I, Addr A] (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW ArrayIndexOutOfBounds, loc) \<leftrightarrow> ([V, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssBounds)
    ultimately show ?thesis using s \<tau> by auto blast
  next 
    case (Red1AAssStore A U I V U')
    hence [simp]: "v = Addr A" "e' = THROW ArrayStore" "v' = Intg I" "xs' = xs" "ta = \<epsilon>" "h' = h" "ee = Val V"
      and hA: "typeof_addr h A = \<lfloor>Array U\<rfloor>" and I: "0 <=s I" "sint I < int (array_length h A)" 
      and U: "\<not> P \<turnstile> U' \<le> U" "typeof\<^bsub>h\<^esub> V = \<lfloor>U'\<rfloor>" by auto
    have \<tau>: "\<not> \<tau>move1 P h (addr A\<lfloor>Val (Intg I)\<rceil> := ee)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim3 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t e h (stk, loc, pc, xcp) ([V], loc, length (compE2 e), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + pc, xcp) ([V] @ [Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None)"
      by-(rule AAss_\<tau>ExecrI3)
    moreover from hA I U
    have "exec_move_a P t (a\<lfloor>i\<rceil> := e) h ([V, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), None) \<epsilon>
                                 h ([V, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>)"
      unfolding exec_move_def by-(rule exec_instr, auto simp add: is_Ref_def compP2_def)
    moreover have "\<tau>move2 (compP2 P) h [V, Intg I, Addr A] (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok a n` `bsok i n` `bsok e n`
    have "P, a\<lfloor>i\<rceil> := e, n, h' \<turnstile> (THROW ArrayStore, loc) \<leftrightarrow> ([V, Intg I, Addr A], loc, length (compE2 a) + length (compE2 i) + length (compE2 e), \<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>)"
      by(rule bisim1_bisims1.bisim1AAssStore)
    ultimately show ?thesis using s \<tau> by auto blast
  next
    case (AAss1Throw3 A)
    note [simp] = `ee = Throw A` `ta = \<epsilon>` `e' = Throw A` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h (AAss (Val v) (Val v') (Throw A))" by(rule \<tau>move1AAssThrow3)
    from bisim3 have "xcp = \<lfloor>A\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>A\<rfloor>"
      with bisim3 `bsok a n` `bsok i n`
      have "P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> (stk @ [v', v], loc, length (compE2 a) + length (compE2 i) + pc, xcp)"
	by(auto intro: bisim1_bisims1.intros)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim3 obtain pc' where "\<tau>Exec_mover_a P t e h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and bisim': "P, e, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (a\<lfloor>i\<rceil> := e) h (stk @ [v', v], loc, length (compE2 a) + length (compE2 i) + pc, None) ([Addr A] @ [v', v], loc, length (compE2 a) + length (compE2 i) + pc', \<lfloor>A\<rfloor>)"
	by-(rule AAss_\<tau>ExecrI3)
      moreover from bisim' `bsok a n` `bsok i n`
      have "P, a\<lfloor>i\<rceil> := e, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A] @ [v', v], loc, length (compE2 a) +  length (compE2 i) + pc', \<lfloor>A\<rfloor>)"
	by(rule bisim1_bisims1.bisim1AAssThrow3)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case bisim1AAssThrow1 thus ?case by auto
next
  case bisim1AAssThrow2 thus ?case by auto
next
  case bisim1AAssThrow3 thus ?case by auto
next
  case bisim1AAssNull thus ?case by auto
next
  case bisim1AAssStore thus ?case by auto
next
  case bisim1AAssBounds thus ?case by auto
next
  case bisim1AAss4 thus ?case by auto
next
  case (bisim1ALength a n a' xs stk loc pc xcp)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>a',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,a,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta a a' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,a,n,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P,t \<turnstile>1 \<langle>a'\<bullet>length,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from red show ?case
  proof cases
    case (ALength1Red ee')
    note [simp] = `e' = ee'\<bullet>length`
      and red = `P,t \<turnstile>1 \<langle>a',(h, xs)\<rangle> -ta\<rightarrow> \<langle>ee', (h', xs')\<rangle>`
    from red have "\<tau>move1 P h (a'\<bullet>length) = \<tau>move1 P h a'" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover have "call1 (a'\<bullet>length) = call1 a'" by auto
    moreover from IH[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,a,n,h' \<turnstile> (ee', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta a a' ee' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim
    have "P,a\<bullet>length,n,h' \<turnstile> (ee'\<bullet>length, xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1ALength)
    moreover { 
      assume "no_call2 a pc"
      hence "no_call2 (a\<bullet>length) pc" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: ALength_\<tau>ExecrI ALength_\<tau>ExectI exec_move_ALengthI)+
  next
    case (Red1ALength A U)
    hence [simp]: "a' = addr A" "ta = \<epsilon>" "e' = Val (Intg (word_of_int (int (array_length h A))))"
      "h' = h" "xs' = xs"
      and hA: "typeof_addr h A = \<lfloor>Array U\<rfloor>" by auto
    from bisim have s: "xcp = None" "xs = loc" by(auto dest: bisim_Val_loc_eq_xcp_None)
    from bisim have "\<tau>Exec_mover_a P t a h (stk, loc, pc, xcp) ([Addr A], loc, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<bullet>length) h (stk, loc, pc, xcp) ([Addr A], loc, length (compE2 a), None)"
      by(rule ALength_\<tau>ExecrI)
    moreover from hA
    have "exec_move_a P t (a\<bullet>length) h ([Addr A], loc, length (compE2 a), None) \<epsilon> h' ([Intg (word_of_int (int (array_length h A)))], loc, Suc (length (compE2 a)), None)"
      by(auto intro!: exec_instr simp add: is_Ref_def exec_move_def)
    moreover have "\<tau>move2 (compP2 P) h [Addr A] (a\<bullet>length) (length (compE2 a)) None \<Longrightarrow> False" by(simp add: \<tau>move2_iff)
    moreover have "\<not> \<tau>move1 P h (addr A\<bullet>length)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from `bsok a n`
    have "P, a\<bullet>length, n, h' \<turnstile> (Val (Intg (word_of_int (int (array_length h A)))), loc) \<leftrightarrow> ([Intg (word_of_int (int (array_length h A)))], loc, length (compE2 (a\<bullet>length)), None)"
      by-(rule bisim1Val2, auto)
    ultimately show ?thesis using s by(auto) blast
  next
    case Red1ALengthNull
    note [simp] = `a' = null` `e' = THROW NullPointer` `h' = h` `xs' = xs` `ta = \<epsilon>`
    have "\<not> \<tau>move1 P h (null\<bullet>length)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from bisim have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t a h (stk, loc, pc, xcp) ([Null], loc, length (compE2 a), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (a\<bullet>length) h (stk, loc, pc, xcp) ([Null], loc, length (compE2 a), None)"
      by-(rule ALength_\<tau>ExecrI)
    moreover have "exec_move_a P t (a\<bullet>length) h ([Null], loc, length (compE2 a), None) \<epsilon> h ([Null], loc, length (compE2 a), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by -(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<tau>move2 (compP2 P) h [Null] (a\<bullet>length) (length (compE2 a)) None \<Longrightarrow> False" by(simp add: \<tau>move2_iff)
    moreover from `bsok a n`
    have "P,a\<bullet>length,n,h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([Null], loc, length (compE2 a), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro!: bisim1_bisims1.bisim1ALengthNull)
    ultimately show ?thesis using s by auto blast
  next
    case (ALength1Throw A)
    note [simp] = `a' = Throw A` `h' = h` `xs' = xs` `ta = \<epsilon>` `e' = Throw A`
    have \<tau>: "\<tau>move1 P h (Throw A\<bullet>length)" by(auto intro: \<tau>move1ALengthThrow)
    from bisim have "xcp = \<lfloor>A\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>A\<rfloor>"
      with bisim have "P,a\<bullet>length, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.bisim1ALengthThrow)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim obtain pc'
	where "\<tau>Exec_mover_a P t a h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	and bisim': "P, a, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (a\<bullet>length) h (stk, loc, pc, None) ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	by-(rule ALength_\<tau>ExecrI)
      moreover from bisim' have "P, a\<bullet>length, n, h \<turnstile> (Throw A, xs) \<leftrightarrow> ([Addr A], loc, pc', \<lfloor>A\<rfloor>)"
	by-(rule bisim1_bisims1.bisim1ALengthThrow, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed
next
  case bisim1ALengthThrow thus ?case by auto
next
  case bisim1ALengthNull thus ?case by auto
next
  case (bisim1FAcc E n e xs stk loc pc xcp F D)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P,t \<turnstile>1 \<langle>e\<bullet>F{D},(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from red show ?case
  proof cases
    case (FAcc1Red ee')
    note [simp] = `e' = ee'\<bullet>F{D}`
      and red = `P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>ee', (h', xs')\<rangle>`
    from red have "\<tau>move1 P h (e\<bullet>F{D}) = \<tau>move1 P h e" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover have "call1 (e\<bullet>F{D}) = call1 e" by auto
    moreover from IH[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,E,n,h' \<turnstile> (ee', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta E e ee' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim
    have "P,E\<bullet>F{D},n,h' \<turnstile> (ee'\<bullet>F{D}, xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1FAcc)
    moreover { 
      assume "no_call2 E pc"
      hence "no_call2 (E\<bullet>F{D}) pc" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: FAcc_\<tau>ExecrI FAcc_\<tau>ExectI exec_move_FAccI)+
  next
    case (Red1FAcc a v)
    hence [simp]: "e = addr a" "ta = \<epsilon>\<lbrace>\<^bsub>o\<^esub>ReadMem a (CField D F) v\<rbrace>" "e' = Val v" "h' = h" "xs' = xs"
      and read: "heap_read h a (CField D F) v" by auto
    from bisim have s: "xcp = None" "xs = loc" by(auto dest: bisim_Val_loc_eq_xcp_None)
    from bisim have "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (E\<bullet>F{D}) h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 E), None)"
      by(rule FAcc_\<tau>ExecrI)
    moreover from read 
    have "exec_move_a P t (E\<bullet>F{D}) h ([Addr a], loc, length (compE2 E), None) 
                     \<epsilon>\<lbrace>\<^bsub>o\<^esub>ReadMem a (CField D F) v\<rbrace> h' ([v], loc, Suc (length (compE2 E)), None)"
      unfolding exec_move_def by(auto intro!: exec_instr)
    moreover have "\<tau>move2 (compP2 P) h [Addr a] (E\<bullet>F{D}) (length (compE2 E)) None \<Longrightarrow> False" by(simp add: \<tau>move2_iff)
    moreover have "\<not> \<tau>move1 P h (addr a\<bullet>F{D})" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from `bsok E n`
    have "P, E\<bullet>F{D}, n, h' \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (E\<bullet>F{D})), None)"
      by-(rule bisim1Val2, simp_all)
    ultimately show ?thesis using s by(auto simp add: ta_upd_simps) blast
  next
    case Red1FAccNull
    note [simp] = `e = null` `e' = THROW NullPointer` `h' = h` `xs' = xs` `ta = \<epsilon>`
    have "\<not> \<tau>move1 P h (null\<bullet>F{D})" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from bisim have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([Null], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (E\<bullet>F{D}) h (stk, loc, pc, xcp) ([Null], loc, length (compE2 E), None)"
      by-(rule FAcc_\<tau>ExecrI)
    moreover
    have "exec_move_a P t (E\<bullet>F{D}) h ([Null], loc, length (compE2 E), None) \<epsilon> h ([Null], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by -(rule exec_instr, auto simp add: compP2_def dest: sees_field_idemp)
    moreover have "\<tau>move2 (compP2 P) h [Null] (E\<bullet>F{D}) (length (compE2 E)) None \<Longrightarrow> False" by(simp add: \<tau>move2_iff)
    moreover from `bsok E n`
    have "P,E\<bullet>F{D},n,h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([Null], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro!: bisim1_bisims1.bisim1FAccNull)
    ultimately show ?thesis using s by auto blast
  next
    case (FAcc1Throw a)
    note [simp] = `e = Throw a` `h' = h` `xs' = xs` `ta = \<epsilon>` `e' = Throw a`
    have \<tau>: "\<tau>move1 P h (e\<bullet>F{D})" by(auto intro: \<tau>move1FAccThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim have "P,E\<bullet>F{D}, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.bisim1FAccThrow)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim obtain pc'
	where "\<tau>Exec_mover_a P t E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (E\<bullet>F{D}) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule FAcc_\<tau>ExecrI)
      moreover from bisim' have "P, E\<bullet>F{D}, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1_bisims1.bisim1FAccThrow, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed
next
  case bisim1FAccThrow thus ?case by auto
next
  case bisim1FAccNull thus ?case by auto
next
  case (bisim1FAss1 e1 n e1' xs stk loc pc xcp e2 F D)
  note IH1 = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e1',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e1,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e1 e1' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note IH2 = `\<And>xs e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta e2 e2 e' h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,e1,n,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,e2,n,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,t \<turnstile>1 \<langle>e1'\<bullet>F{D} := e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (FAss1Red1 E')
    note [simp] = `e' = E'\<bullet>F{D} := e2`
      and red = `P,t \<turnstile>1 \<langle>e1',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from red have "\<tau>move1 P h (e1'\<bullet>F{D} := e2) = \<tau>move1 P h e1'" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from red have "call1 (e1'\<bullet>F{D} := e2) = call1 e1'" by auto
    moreover from IH1[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,e1,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta e1 e1' E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim `bsok e2 n`
    have "P,e1\<bullet>F{D} := e2,n,h' \<turnstile> (E'\<bullet>F{D} := e2, xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1FAss1)
    moreover { 
      assume "no_call2 e1 pc"
      hence "no_call2 (e1\<bullet>F{D} := e2) pc \<or> pc = length (compE2 e1)" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: FAss_\<tau>ExecrI1 FAss_\<tau>ExectI1 exec_move_FAssI1)+
  next
    case (FAss1Red2 E' v)
    note [simp] = `e1' = Val v` `e' = Val v\<bullet>F{D} := E'`
      and red = `P,t \<turnstile>1 \<langle>e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h (Val v\<bullet>F{D} := e2) = \<tau>move1 P h e2" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim1 have s: "xcp = None" "xs = loc"
      and exec1: "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, None) ([v], xs, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    from exec1 have "\<tau>Exec_mover_a P t (e1\<bullet>F{D} := e2) h (stk, loc, pc, None) ([v], xs, length (compE2 e1), None)"
      by(rule FAss_\<tau>ExecrI1)
    moreover
    from IH2[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e2,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e2 e2 E' h [] xs 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (e1\<bullet>F{D} := e2) (Val v\<bullet>F{D} := e2) (Val v\<bullet>F{D} := E') h ([] @ [v]) xs (length (compE2 e1) + 0) None h' (length (compE2 e1) + pc'') (stk'' @ [v]) loc'' xcp''"
    proof(cases "\<tau>move1 P h (Val v\<bullet>F{D} := e2)")
      case True
      with exec' \<tau> have [simp]: "h = h'" and e: "sim_move e2 E' P t e2 h ([], xs, 0, None) (stk'', loc'', pc'', xcp'')" by auto
      from e have "sim_move (Val v\<bullet>F{D} := e2) (Val v\<bullet>F{D} := E') P t (e1\<bullet>F{D} := e2) h ([] @ [v], xs, length (compE2 e1) + 0, None) (stk'' @ [v], loc'', length (compE2 e1) + pc'', xcp'')"
	by(fastsimp dest: FAss_\<tau>ExecrI2 FAss_\<tau>ExectI2 simp del: compE2_compEs2.simps)
      with True show ?thesis by auto
    next
      case False
      with exec' \<tau> obtain pc' stk' loc' xcp'
	where e: "\<tau>Exec_mover_a P t e2 h ([], xs, 0, None) (stk', loc', pc', xcp')"
	and e': "exec_move_a P t e2 h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 (compP2 P) h stk' e2 pc' xcp'" 
        and call: "call1 e2 = None \<or> no_call2 e2 0 \<or> pc' = 0 \<and> stk' = [] \<and> loc' = xs \<and> xcp' = None" by auto
      from e have "\<tau>Exec_mover_a P t (e1\<bullet>F{D} := e2) h ([] @ [v], xs, length (compE2 e1) + 0, None) (stk' @ [v], loc', length (compE2 e1) + pc', xcp')"
	by(rule FAss_\<tau>ExecrI2)
      moreover from e' have "exec_move_a P t (e1\<bullet>F{D} := e2) h (stk' @ [v], loc', length (compE2 e1) + pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'' @ [v], loc'', length (compE2 e1) + pc'', xcp'')"
	by(rule exec_move_FAssI2)
      moreover from e' have "pc' < length (compE2 e2)" by(auto elim: exec_meth.cases)
      with \<tau>' e' have "\<not> \<tau>move2 (compP2 P) h (stk' @ [v]) (e1\<bullet>F{D} := e2) (length (compE2 e1) + pc') xcp'"
        by(auto simp add: \<tau>move2_iff \<tau>instr_stk_drop_exec_move)
      moreover have "call1 (e1'\<bullet>F{D} := e2) = call1 e2" by simp
      moreover have "no_call2 e2 0 \<Longrightarrow> no_call2 (e1\<bullet>F{D} := e2) (length (compE2 e1))"
        by(auto simp add: no_call2_def)
      ultimately show ?thesis using False call
        by(auto simp del: split_paired_Ex call1_calls1.simps) blast
    qed
    moreover from bisim' `bsok e1 n`
    have "P,e1\<bullet>F{D} := e2,n,h' \<turnstile> (Val v\<bullet>F{D} := E', xs') \<leftrightarrow> ((stk'' @ [v]), loc'', length (compE2 e1) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1FAss2)
    moreover from bisim1 have "pc \<noteq> length (compE2 e1) \<longrightarrow> no_call2 (e1\<bullet>F{D} := e2) pc"
      by(auto simp add: no_call2_def dest: bisim_Val_pc_not_Invoke bisim1_pc_length_compE2)
    ultimately show ?thesis using \<tau> exec1 s
      apply(auto simp del: split_paired_Ex call1_calls1.simps split: split_if_asm split del: split_if)
      apply(blast intro: \<tau>Exec_mover_trans|fastsimp elim!: \<tau>Exec_mover_trans simp del: split_paired_Ex call1_calls1.simps)+
      done
  next
    case (Red1FAss a v)
    note [simp] = `e1' = addr a` `e2 = Val v` `ta = \<epsilon>\<lbrace>\<^bsub>o\<^esub>WriteMem a (CField D F) v\<rbrace>` `e' = unit` `xs' = xs`
      and "write" = `heap_write h a (CField D F) v h'`
    have \<tau>: "\<not> \<tau>move1 P h (e1'\<bullet>F{D} := e2)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (e1\<bullet>F{D} := e2) h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 e1), None)"
      by-(rule FAss_\<tau>ExecrI1)
    also have "\<tau>move2 (compP2 P) h [Addr a] (e1\<bullet>F{D} := Val v) (length (compE2 e1)) None" by(simp add: \<tau>move2_iff)
    hence "\<tau>Exec_mover_a P t (e1\<bullet>F{D} := e2) h ([Addr a], loc, length (compE2 e1), None) ([v, Addr a], loc, Suc (length (compE2 e1)), None)"
      by-(rule \<tau>Execr1step, auto intro!: exec_instr simp add: exec_move_def compP2_def)
    also (rtranclp_trans) from "write"
    have "exec_move_a P t (e1\<bullet>F{D} := e2) h ([v, Addr a], loc, Suc (length (compE2 e1)), None) \<epsilon>\<lbrace>\<^bsub>o\<^esub>WriteMem a (CField D F) v\<rbrace>
                                      h' ([], loc, Suc (Suc (length (compE2 e1))), None)"
      unfolding exec_move_def by(auto intro!: exec_instr)
    moreover have "\<tau>move2 (compP2 P) h [v, Addr a] (e1\<bullet>F{D} := e2) (Suc (length (compE2 e1))) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok e1 n` `bsok e2 n`
    have "P, e1\<bullet>F{D} := e2, n, h' \<turnstile> (unit, loc) \<leftrightarrow> ([], loc, Suc (length (compE2 e1) + length (compE2 e2)), None)"
      by(rule bisim1_bisims1.bisim1FAss3)
    ultimately show ?thesis using s \<tau> by(auto simp del: fun_upd_apply simp add: ta_upd_simps) blast
  next
    case (Red1FAssNull v)
    note [simp] = `e1' = null` `e2 = Val v` `xs' = xs` `ta = \<epsilon>` `e' = THROW NullPointer` `h' = h`
    have \<tau>: "\<not> \<tau>move1 P h (e1'\<bullet>F{D} := e2)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, xcp) ([Null], loc, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (e1\<bullet>F{D} := e2) h (stk, loc, pc, xcp) ([Null], loc, length (compE2 e1), None)"
      by-(rule FAss_\<tau>ExecrI1)
    also have "\<tau>move2 (compP2 P) h [Null] (e1\<bullet>F{D} := Val v) (length (compE2 e1)) None" by(simp add: \<tau>move2_iff)
    hence "\<tau>Exec_mover_a P t (e1\<bullet>F{D} := e2) h ([Null], loc, length (compE2 e1), None) ([v, Null], loc, Suc (length (compE2 e1)), None)"
      by-(rule \<tau>Execr1step, auto intro!: exec_instr simp add: exec_move_def compP2_def)
    also (rtranclp_trans)
    have "exec_move_a P t (e1\<bullet>F{D} := e2) h ([v, Null], loc, Suc (length (compE2 e1)), None) \<epsilon>
                                      h' ([v, Null], loc, Suc (length (compE2 e1)), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro!: exec_instr simp add: exec_move_def)
    moreover have "\<tau>move2 (compP2 P) h [v, Null] (e1\<bullet>F{D} := e2) (Suc (length (compE2 e1))) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok e1 n` `bsok e2 n`
    have "P, e1\<bullet>F{D} := e2, n, h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([v, Null], loc, length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1_bisims1.bisim1FAssNull)
    ultimately show ?thesis using s \<tau> by(auto simp del: fun_upd_apply) blast
  next
    case (FAss1Throw1 a)
    note [simp] = `e1' = Throw a` `ta = \<epsilon>` `e' = Throw a` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h (Throw a\<bullet>F{D} := e2)" by(rule \<tau>move1FAssThrow1)
    from bisim1 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim1 `bsok e2 n`
      have "P, e1\<bullet>F{D} := e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1_bisims1.intros)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim1 obtain pc' where "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, e1, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (e1\<bullet>F{D} := e2) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule FAss_\<tau>ExecrI1)
      moreover from bisim' `bsok e2 n`
      have "P, e1\<bullet>F{D} := e2, n, h\<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1FAssThrow1)
      ultimately show ?thesis using \<tau> by auto
    qed
  next
    case (FAss1Throw2 v ad)
    note [simp] = `e1' = Val v` `e2 = Throw ad` `e' = Throw ad` `h' = h` `xs' = xs`
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, xcp) ([v], loc, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (e1\<bullet>F{D} := Throw ad) h (stk, loc, pc, xcp) ([v], loc, length (compE2 e1), None)"
      by-(rule FAss_\<tau>ExecrI1)
    also have "\<tau>Exec_mover_a P t (e1\<bullet>F{D} := Throw ad) h ([v], loc, length (compE2 e1), None) ([Addr ad, v], loc, Suc (length (compE2 e1)), \<lfloor>ad\<rfloor>)"
      by(rule \<tau>Execr2step)(auto simp add: exec_move_def exec_meth_instr \<tau>move2_iff \<tau>move1_\<tau>moves1.simps)
    also (rtranclp_trans)
    have "P,e1\<bullet>F{D}:=Throw ad,n,h \<turnstile> (Throw ad, loc) \<leftrightarrow> ([Addr ad] @ [v], loc, (length (compE2 e1) + length (compE2 (addr ad))), \<lfloor>ad\<rfloor>)"
      by(rule bisim1FAssThrow2[OF bisim1Throw2 `bsok e1 n`])(simp)
    moreover have "\<tau>move1 P h (FAss e1' F D (Throw ad))" by(auto intro: \<tau>move1FAssThrow2)
    ultimately show ?thesis using s by auto
  qed
next
  case (bisim1FAss2 e2 n e2' xs stk loc pc xcp e1 F D v1)
  note IH2 = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e2 e2' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `\<And>xs. P,e1,n,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,e2,n,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P,t \<turnstile>1 \<langle>Val v1\<bullet>F{D} := e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from red show ?case
  proof cases
    case (FAss1Red2 E')
    note [simp] = `e' = Val v1\<bullet>F{D} := E'`
      and red = `P,t \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from IH2[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e2,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e2 e2' E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    from red have \<tau>: "\<tau>move1 P h (Val v1\<bullet>F{D} := e2') = \<tau>move1 P h e2'" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    have "no_call2 e2 pc \<Longrightarrow> no_call2 (e1\<bullet>F{D} := e2) (length (compE2 e1) + pc)" by(auto simp add: no_call2_def)
    hence "?exec ta (e1\<bullet>F{D} := e2) (Val v1\<bullet>F{D} := e2') (Val v1\<bullet>F{D} := E') h (stk @ [v1]) loc (length (compE2 e1) + pc) xcp h' (length (compE2 e1) + pc'') (stk'' @ [v1]) loc'' xcp''"
      using exec' \<tau>
      apply(cases "\<tau>move1 P h (Val v1\<bullet>F{D} := e2')")
      apply(auto)
      apply(blast intro: FAss_\<tau>ExecrI2 FAss_\<tau>ExectI2 exec_move_FAssI2)
      apply(blast intro: FAss_\<tau>ExecrI2 FAss_\<tau>ExectI2 exec_move_FAssI2)
      apply(rule exI conjI FAss_\<tau>ExecrI2 exec_move_FAssI2|assumption)+
      apply(fastsimp simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff split: split_if_asm)
      apply(rule exI conjI FAss_\<tau>ExecrI2 exec_move_FAssI2|assumption)+
      apply(fastsimp simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff split: split_if_asm)
      apply(rule exI conjI FAss_\<tau>ExecrI2 exec_move_FAssI2 rtranclp.rtrancl_refl|assumption)+
      apply(fastsimp simp add: \<tau>instr_stk_drop_exec_move \<tau>move2_iff split: split_if_asm)+
      done
    moreover from bisim' `bsok e1 n`
    have "P,e1\<bullet>F{D} := e2,n,h' \<turnstile> (Val v1\<bullet>F{D} := E', xs') \<leftrightarrow> (stk''@[v1], loc'', length (compE2 e1) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1FAss2)
    ultimately show ?thesis using \<tau> by auto blast+
  next
    case (Red1FAss a v)
    note [simp] = `v1 = Addr a` `e2' = Val v` `ta = \<epsilon>\<lbrace>\<^bsub>o\<^esub>WriteMem a (CField D F) v\<rbrace>` `e' = unit` `xs' = xs`
      and ha = `heap_write h a (CField D F) v h'`
    have \<tau>: "\<not> \<tau>move1 P h (addr a\<bullet>F{D} := e2')" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim2 have s: "xcp = None" "xs = loc" 
      and "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, xcp) ([v], loc, length (compE2 e2), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (e1\<bullet>F{D} := e2) h (stk @ [v1], loc, length (compE2 e1) + pc, xcp) ([v] @ [v1], loc, length (compE2 e1) + length (compE2 e2), None)"
      by-(rule FAss_\<tau>ExecrI2)
    moreover from ha
    have "exec_move_a P t (e1\<bullet>F{D} := e2) h ([v, Addr a], loc, length (compE2 e1) + length (compE2 e2), None) \<epsilon>\<lbrace>\<^bsub>o\<^esub>WriteMem a (CField D F) v\<rbrace>
                                      h' ([], loc, Suc (length (compE2 e1) + length (compE2 e2)), None)"
      by(auto intro!: exec_instr simp add: exec_move_def)
    moreover have "\<tau>move2 (compP2 P) h [v, Addr a] (e1\<bullet>F{D} := e2) (length (compE2 e1) + length (compE2 e2)) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok e1 n` `bsok e2 n`
    have "P, e1\<bullet>F{D} := e2, n, h' \<turnstile> (unit, loc) \<leftrightarrow> ([], loc, Suc (length (compE2 e1) + length (compE2 e2)), None)"
      by(rule bisim1_bisims1.bisim1FAss3)
    ultimately show ?thesis using s \<tau> by(auto simp del: fun_upd_apply simp add: ta_upd_simps) blast
  next
    case (Red1FAssNull v)
    note [simp] = `v1 = Null` `e2' = Val v` `xs' = xs` `ta = \<epsilon>` `e' = THROW NullPointer` `h' = h`
    have \<tau>: "\<not> \<tau>move1 P h (null\<bullet>F{D} := e2')" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim2 have s: "xcp = None" "xs = loc" 
      and "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, xcp) ([v], loc, length (compE2 e2), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (e1\<bullet>F{D} := e2) h (stk @ [Null], loc, length (compE2 e1) + pc, xcp) ([v] @ [Null], loc, length (compE2 e1) + length (compE2 e2), None)"
      by-(rule FAss_\<tau>ExecrI2)
    moreover have "exec_move_a P t (e1\<bullet>F{D} := e2) h ([v, Null], loc, length (compE2 e1) + length (compE2 e2), None) \<epsilon>
                                      h' ([v, Null], loc, length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro!: exec_instr simp add: exec_move_def)
    moreover have "\<tau>move2 (compP2 P) h [v, Null] (e1\<bullet>F{D} := e2) (length (compE2 e1) + length (compE2 e2)) None \<Longrightarrow> False"
      by(simp add: \<tau>move2_iff)
    moreover from `bsok e1 n` `bsok e2 n`
    have "P, e1\<bullet>F{D} := e2, n, h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([v, Null], loc, length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1_bisims1.bisim1FAssNull)
    ultimately show ?thesis using s \<tau> by(auto simp del: fun_upd_apply) blast
  next
    case (FAss1Throw2 a)
    note [simp] = `e2' = Throw a` `ta = \<epsilon>` `h' = h` `xs' = xs` `e' = Throw a`
    have \<tau>: "\<tau>move1 P h (FAss (Val v1) F D (Throw a))" by(rule \<tau>move1FAssThrow2)
    from bisim2 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim2 `bsok e1 n`
      have "P, e1\<bullet>F{D} := e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk @ [v1], loc, length (compE2 e1) + pc, xcp)"
	by(auto intro: bisim1FAssThrow2)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim2 obtain pc'
	where "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (e1\<bullet>F{D} := e2) h (stk @ [v1], loc, length (compE2 e1) + pc, None) ([Addr a] @ [v1], loc, length (compE2 e1) + pc', \<lfloor>a\<rfloor>)"
	by-(rule FAss_\<tau>ExecrI2)
      moreover from bisim' `bsok e1 n`
      have "P, e1\<bullet>F{D} := e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a]@[v1], loc, length (compE2 e1) + pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1FAssThrow2, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed auto
next
  case bisim1FAssThrow1 thus ?case by fastsimp
next
  case bisim1FAssThrow2 thus ?case by fastsimp
next
  case bisim1FAssNull thus ?case by fastsimp
next
  case bisim1FAss3 thus ?case by fastsimp
next
  case (bisim1CallParams ps n ps' xs stk loc pc xcp obj M' v)
  note IHparam = `\<And>es' h' xs' Env Ts Env' Ts'. P,t \<turnstile>1 \<langle>ps',(h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,ps,n,h' \<turnstile> (es', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'') \<and>
                 ?execs ta ps ps' es' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `\<And>xs. P,obj,n,h \<turnstile> (obj, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,ps,n,h \<turnstile> (ps', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)`
  note red = `P,t \<turnstile>1 \<langle>Val v\<bullet>M'(ps'),(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from bisim2 `ps \<noteq> []` have ps': "ps' \<noteq> []" by(auto dest: bisims1_lengthD)
  from red show ?case
  proof cases
    case (Call1Params es')
    note [simp] = `e' = Val v\<bullet>M'(es')`
      and red = `P,t \<turnstile>1 \<langle>ps', (h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es', (h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h (Val v\<bullet>M'(ps')) = \<tau>moves1 P h ps'" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from IHparam[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,ps,n,h' \<turnstile> (es', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'')"
      and exec': "?execs ta ps ps' es' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (obj\<bullet>M'(ps)) (Val v\<bullet>M'(ps')) (Val v\<bullet>M'(es')) h (stk @ [v]) loc (length (compE2 obj) + pc) xcp  h' (length (compE2 obj) + pc'') (stk'' @ [v]) loc'' xcp''"
    proof(cases "\<tau>move1 P h (Val v\<bullet>M'(ps'))")
      case True
      with exec' \<tau> show ?thesis by (auto intro: Call_\<tau>ExecrI2 Call_\<tau>ExectI2)
    next
      case False
      with exec' \<tau> obtain pc' stk' loc' xcp'
	where e: "\<tau>Exec_movesr_a P t ps h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
	and e': "exec_moves_a P t ps h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>moves2 (compP2 P) h stk' ps pc' xcp'" 
        and call: "(calls1 ps' = None \<or> no_calls2 ps pc \<or> pc' = pc \<and> stk' = stk \<and> loc' = loc \<and> xcp' = xcp)" by auto
      from e have "\<tau>Exec_mover_a P t (obj\<bullet>M'(ps)) h (stk @ [v], loc, length (compE2 obj) + pc, xcp) (stk' @ [v], loc', length (compE2 obj) + pc', xcp')" by(rule Call_\<tau>ExecrI2)
      moreover from e' have "exec_move_a P t (obj\<bullet>M'(ps)) h (stk' @ [v], loc', length (compE2 obj) + pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'' @ [v], loc'', length (compE2 obj) + pc'', xcp'')"
	by(rule exec_move_CallI2)
      moreover from \<tau>' e' have "\<tau>move2 (compP2 P) h (stk' @ [v]) (obj\<bullet>M'(ps)) (length (compE2 obj) + pc') xcp' \<Longrightarrow> False"
        by(auto simp add: \<tau>move2_iff \<tau>moves2_iff \<tau>instr_stk_drop_exec_moves split: split_if_asm)
      moreover from red have "call1 (Val v\<bullet>M'(ps')) = calls1 ps'" by(auto simp add: is_vals_conv)
      moreover from red have "no_calls2 ps pc \<Longrightarrow> no_call2 (obj\<bullet>M'(ps)) (length (compE2 obj) + pc) \<or> pc = length (compEs2 ps)"
        by(auto simp add: no_call2_def no_calls2_def)
      ultimately show ?thesis using False call e
        by(auto simp del: split_paired_Ex call1_calls1.simps) blast+
    qed
    moreover from bisim' `bsok obj n`
    have "P,obj\<bullet>M'(ps),n,h' \<turnstile> (Val v\<bullet>M'(es'), xs') \<leftrightarrow> ((stk'' @ [v]), loc'', length (compE2 obj) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1CallParams)
    ultimately show ?thesis using \<tau>
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if) blast+
  next
    case (Red1CallNull vs)
    note [simp] = `h' = h` `xs' = xs` `ta = \<epsilon>` `v = Null` `ps' = map Val vs` `e' = THROW NullPointer`
    from bisim2 have length: "length ps = length vs" by(auto dest: bisims1_lengthD)
    have "xs = loc \<and> xcp = None \<and> \<tau>Exec_movesr_a P t ps h (stk, loc, pc, xcp) (rev vs, loc, length (compEs2 ps), None)"
    proof(cases "pc < length (compEs2 ps)")
      case True
      with bisim2 show ?thesis by(auto dest: bisims1_Val_\<tau>Exec_moves)
    next
      case False
      with bisim2 have "pc = length (compEs2 ps)"
	by(auto dest: bisims1_pc_length_compEs2)
      with bisim2 show ?thesis by(auto dest: bisims1_Val_length_compEs2D)
    qed
    hence s: "xs = loc" "xcp = None"
      and "\<tau>Exec_movesr_a P t ps h (stk, loc, pc, xcp) (rev vs, loc, length (compEs2 ps), None)" by auto
    hence "\<tau>Exec_mover_a P t (obj\<bullet>M'(ps)) h (stk @ [Null], loc, length (compE2 obj) + pc, xcp) (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 ps), None)"
      by -(rule Call_\<tau>ExecrI2)
    also {
      from length have "exec_move_a P t (obj\<bullet>M'(ps)) h (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 ps), None) \<epsilon> h (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 ps), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
        unfolding exec_move_def by(cases ps)(auto intro: exec_instr)
      moreover have "\<tau>move2 P h (rev vs @ [Null]) (obj\<bullet>M'(ps)) (length (compE2 obj) + length (compEs2 ps)) None"
        using length by(simp add: \<tau>move2_iff)
      ultimately have "\<tau>Exec_movet_a P t (obj\<bullet>M'(ps)) h (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 ps), None) (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 ps), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
        by(auto intro: \<tau>exec_moveI) }
    also have "\<tau>move1 P h (null\<bullet>M'(map Val vs))"
      by(auto simp add: \<tau>move1_\<tau>moves1.simps map_eq_append_conv)
    moreover from bisim1 bisim2 have "bsok obj n" "bsoks ps n" by(auto dest: bisims1_bsoks bisim1_bsok)
    with length have "P,obj\<bullet>M'(ps),n,h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ((rev vs @ [Null]), loc, length (compE2 obj) + length (compEs2 ps), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by-(rule bisim1CallThrow,auto)
    ultimately show ?thesis using s by auto
  next
    case (Call1ThrowParams vs a es')
    note [simp] =  `ta = \<epsilon>` `e' = Throw a` `ps' = map Val vs @ Throw a # es'` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h (Val v\<bullet>M'(map Val vs @ Throw a # es'))" by(rule \<tau>move1CallThrowParams)
    from bisim2 have [simp]: "xs = loc" and "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisims1_ThrowD)
    from `xcp = \<lfloor>a\<rfloor> \<or> xcp = None` show ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim2 bisim1_bsok[OF bisim1]
      have "P,obj\<bullet>M'(ps),n,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk @ [v], loc, length (compE2 obj) + pc, \<lfloor>a\<rfloor>)"
	by -(rule bisim1CallThrowParams, auto)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim2 obtain pc'
	where exec: "\<tau>Exec_movesr_a P t ps h (stk, loc, pc, None) (Addr a # rev vs, loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, ps, n, h \<turnstile> (map Val vs @ Throw a # es', loc) [\<leftrightarrow>] (Addr a # rev vs, loc, pc', \<lfloor>a\<rfloor>)"
	by(auto dest: bisims1_Throw_\<tau>Exec_movesr)
      from bisim' `bsok obj n`
      have "P,obj\<bullet>M'(ps),n,h \<turnstile> (Throw a, loc) \<leftrightarrow> ((Addr a # rev vs) @ [v], loc, length (compE2 obj) + pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1CallThrowParams, auto)
      with Call_\<tau>ExecrI2[OF exec, of obj M' v] \<tau>
      show ?thesis by auto
    qed
  next
    case (Red1CallExternal a Ta vs va H')
    hence [simp]: "v = Addr a" "ps' = map Val vs" "e' = extRet2J (addr a\<bullet>M'(map Val vs)) va" "H' = h'" "xs' = xs"
      and Ta: "typeof_addr h a = \<lfloor>Ta\<rfloor>"
      and iec: "is_external_call P Ta M'"
      and redex: "P,t \<turnstile> \<langle>a\<bullet>M'(vs),h\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>" by auto
    from bisim2 have [simp]: "xs = loc" by(auto dest: bisims_Val_loc_eq_xcp_None)
    moreover from bisim2 have "length ps = length ps'"
      by(rule bisims1_lengthD)
    hence \<tau>: "\<tau>move1 P h (addr a\<bullet>M'(map Val vs) :: expr1) = \<tau>move2 (compP2 P) h (rev vs @ [Addr a]) (obj\<bullet>M'(ps)) (length (compE2 obj) + length (compEs2 ps)) None"
      using Ta iec by(auto simp add: \<tau>move1_\<tau>moves1.simps map_eq_append_conv \<tau>move2_iff compP2_def)
    obtain s: "xcp = None" "xs = loc"
      and "\<tau>Exec_movesr_a P t ps h (stk, loc, pc, xcp) (rev vs, loc, length (compEs2 ps), None)"
    proof(cases "pc < length (compEs2 ps)")
      case True
      with bisim2 show ?thesis by(auto dest: bisims1_Val_\<tau>Exec_moves intro: that)
    next
      case False
      with bisim2 have "pc = length (compEs2 ps)" by(auto dest: bisims1_pc_length_compEs2)
      with bisim2 show ?thesis by -(rule that, auto dest!: bisims1_pc_length_compEs2D)
    qed
    from Call_\<tau>ExecrI2[OF this(3), of obj M' v]
    have "\<tau>Exec_mover_a P t (obj\<bullet>M'(ps)) h (stk @ [Addr a], loc, length (compE2 obj) + pc, xcp) (rev vs @ [Addr a], loc, length (compE2 obj) + length (compEs2 ps), None)" by simp
    moreover from bisim2 have "pc \<le> length (compEs2 ps)" by(rule bisims1_pc_length_compEs2)
    hence "no_call2 (obj\<bullet>M'(ps)) (length (compE2 obj) + pc) \<or> pc = length (compEs2 ps)"
      using bisim2 by(auto simp add: no_call2_def neq_Nil_conv dest: bisims_Val_pc_not_Invoke)
    moreover { 
      assume "pc = length (compEs2 ps)"
      with `\<tau>Exec_movesr_a P t ps h (stk, loc, pc, xcp) (rev vs, loc, length (compEs2 ps), None)`
      have "stk = rev vs" "xcp = None" by auto }
    moreover
    let ?ret = "extRet2JVM (length ps) h' (rev vs @ [Addr a]) loc undefined undefined (length (compE2 obj) + length (compEs2 ps)) [] va"
    let ?stk' = "fst (hd (snd (snd ?ret)))"
    let ?xcp' = "fst ?ret"
    let ?pc' = "snd (snd (snd (snd (hd (snd (snd ?ret))))))"
    from bisim2 have [simp]: "length ps = length vs" by(auto dest: bisims1_lengthD)
    from redex have redex': "(ta, va, h') \<in> red_external_aggr (compP2 P) t a M' vs h"
      by -(rule red_external_imp_red_external_aggr, simp add: compP2_def)
    with Ta iec
    have "exec_move_a P t (obj\<bullet>M'(ps)) h (rev vs @ [Addr a], loc, length (compE2 obj) + length (compEs2 ps), None) (extTA2JVM (compP2 P) ta) h' (?stk', loc, ?pc', ?xcp')"
      unfolding exec_move_def
      by -(rule exec_instr,cases va,(force simp add: compP2_def is_Ref_def simp del: split_paired_Ex intro: external_WT'.intros)+)
    moreover have "P,obj\<bullet>M'(ps),n,h' \<turnstile> (extRet2J1 (addr a\<bullet>M'(map Val vs)) va, loc) \<leftrightarrow> (?stk', loc, ?pc', ?xcp')"
    proof(cases va)
      case (RetVal v)
      from `bsok obj n` `bsoks ps n` 
      have "P,obj\<bullet>M'(ps),n,h' \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (obj\<bullet>M'(ps))), None)"
	by-(rule bisim1Val2, simp_all)
      thus ?thesis unfolding RetVal by simp
    next
      case (RetExc ad)
      with `bsok obj n` `bsoks ps n` show ?thesis by(auto intro: bisim1CallThrow)
    next
      case RetStaySame
      from bisims1_map_Val_append[OF bisims1Nil `bsoks ps n`, of vs P h' loc]
      have "P,ps,n,h' \<turnstile> (map Val vs, loc) [\<leftrightarrow>] (rev vs, loc, length (compEs2 ps), None)" by simp
      hence "P,obj\<bullet>M'(ps),n,h' \<turnstile> (addr a\<bullet>M'(map Val vs), loc) \<leftrightarrow> (rev vs @ [Addr a], loc, length (compE2 obj) + length (compEs2 ps), None)"
        using `bsok obj n` by(rule bisim1_bisims1.bisim1CallParams)
      thus ?thesis using RetStaySame by simp
    qed
    moreover from redex Ta iec
    have "\<tau>move1 P h (addr a\<bullet>M'(map Val vs) :: expr1) \<Longrightarrow> ta = \<epsilon> \<and> h' = h"
      by(auto simp add: \<tau>move1_\<tau>moves1.simps map_eq_append_conv \<tau>external'_def dest: \<tau>external'_red_external_TA_empty \<tau>external'_red_external_heap_unchanged)
    ultimately show ?thesis using \<tau>
      apply(cases "\<tau>move1 P h (addr a\<bullet>M'(map Val vs) :: expr1)")
      apply(auto simp del: split_paired_Ex simp add: compP2_def)
      apply(blast intro: rtranclp.rtrancl_into_rtrancl rtranclp_into_tranclp1 \<tau>exec_moveI)+
      done
  qed(insert ps', auto)
next
  case bisim1CallThrowObj thus ?case by fastsimp
next
  case bisim1CallThrowParams thus ?case by auto
next
  case bisim1CallThrow thus ?case by fastsimp
next
  case (bisim1BlockSome1 e V Ty v xs e')
  from `P,t \<turnstile>1 \<langle>{V:Ty=\<lfloor>v\<rfloor>; e},(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof(cases)
    case Block1Some
    note [simp] = `ta = \<epsilon>` `e' = {V:Ty=None; e}` `h' = h` `xs' = xs[V := v]`
      and len = `V < length xs`
    from len have exec: "\<tau>Exec_movet_a P t {V:Ty=\<lfloor>v\<rfloor>; e} h ([], xs, 0, None) ([], xs[V := v], Suc (Suc 0), None)"
      by-(rule \<tau>Exect2step, auto intro: exec_instr simp add: exec_move_def \<tau>move2_iff)
    moreover have "P,{V:Ty=\<lfloor>v\<rfloor>; e},V,h \<turnstile> ({V:Ty=None; e}, xs[V := v]) \<leftrightarrow> ([], xs[V := v], Suc (Suc 0), None)"
      by(rule bisim1BlockSome4)(rule bisim1_refl[OF `bsok e (Suc V)`])
    moreover have "\<tau>move1 P h {V:Ty=\<lfloor>v\<rfloor>; e}" by(auto intro: \<tau>move1BlockSome)
    ultimately show ?thesis by auto
  qed
next
  case (bisim1BlockSome2 e V Ty v xs)
  from `P,t \<turnstile>1 \<langle>{V:Ty=\<lfloor>v\<rfloor>; e},(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof(cases)
    case Block1Some
    note [simp] = `ta = \<epsilon>` `e' = {V:Ty=None; e}` `h' = h` `xs' = xs[V := v]`
      and len = `V < length xs`
    from len have exec: "\<tau>Exec_movet_a P t {V:Ty=\<lfloor>v\<rfloor>; e} h ([v], xs, Suc 0, None) ([], xs[V := v], Suc (Suc 0), None)"
      by-(rule \<tau>Exect1step, auto intro: exec_instr \<tau>move2BlockSome2 simp: exec_move_def)
    moreover have "P,{V:Ty=\<lfloor>v\<rfloor>; e},V,h \<turnstile> ({V:Ty=None; e}, xs[V := v]) \<leftrightarrow> ([], xs[V := v], Suc (Suc 0), None)"
      by(rule bisim1BlockSome4)(rule bisim1_refl[OF `bsok e (Suc V)`])
    moreover have "\<tau>move1 P h {V:Ty=\<lfloor>v\<rfloor>; e}" by(auto intro: \<tau>move1BlockSome)
    ultimately show ?thesis by auto
  qed
next
  case (bisim1BlockSome4 E V e xs stk loc pc xcp Ty v)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,Suc V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,E,Suc V,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  from `P,t \<turnstile>1 \<langle>{V:Ty=None; e},(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Block1Red E')
    note [simp] = `e' = {V:Ty=None; E'}`
      and red = `P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h {V:Ty=None; e} = \<tau>move1 P h e" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from IH[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,E,Suc V,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta E e E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have "no_call2 E pc \<Longrightarrow> no_call2 ({V:Ty=\<lfloor>v\<rfloor>; E}) (Suc (Suc pc))" by(auto simp add: no_call2_def)
    hence "?exec ta {V:Ty=\<lfloor>v\<rfloor>; E} {V:Ty=None; e} {V:Ty=None; E'} h stk loc (Suc (Suc pc)) xcp h' (Suc (Suc pc'')) stk'' loc'' xcp''"
      using exec' \<tau>
      by(cases "\<tau>move1 P h {V:Ty=None; e}")(auto, (blast intro: exec_move_BlockSomeI Block_\<tau>ExecrI_Some Block_\<tau>ExectI_Some)+)
    with bisim' \<tau> show ?thesis by auto(blast intro: bisim1_bisims1.bisim1BlockSome4)+
  next
    case (Red1Block u)
    note [simp] = `e = Val u` `ta = \<epsilon>` `e' = Val u` `h' = h` `xs' = xs`
    have "\<tau>move1 P h {V:Ty=None; Val u}" by(rule \<tau>move1BlockRed)
    moreover from bisim have [simp]: "xcp = None" "loc = xs"
      and exec: "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([u], loc, length (compE2 E), None)" by(auto dest: bisim1Val2D1)
    moreover from bisim1_bsok[OF bisim]
    have "P,{V:Ty=\<lfloor>v\<rfloor>; E},V,h \<turnstile> (Val u, xs) \<leftrightarrow> ([u], xs, length (compE2 {V:Ty=\<lfloor>v\<rfloor>; E}), None)"
      by-(rule bisim1Val2, simp_all) 
    ultimately show ?thesis by(fastsimp elim!: Block_\<tau>ExecrI_Some)
  next
    case (Block1Throw a)
    note [simp] = `e = Throw a` `ta = \<epsilon>` `e' = Throw a` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h {V:Ty=None; e}" by(auto intro: \<tau>move1BlockThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim have "P, {V:Ty=\<lfloor>v\<rfloor>; E}, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (Suc pc), xcp)"
	by(auto intro: bisim1BlockThrowSome)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim obtain pc'
	where "\<tau>Exec_mover_a P t E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, Suc V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t {V:Ty=\<lfloor>v\<rfloor>; E} h (stk, loc, Suc (Suc pc), None) ([Addr a], loc, Suc (Suc pc'), \<lfloor>a\<rfloor>)"
	by(auto intro: Block_\<tau>ExecrI_Some)
      moreover from bisim' have "P, {V:Ty=\<lfloor>v\<rfloor>; E}, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, Suc (Suc pc'), \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1BlockThrowSome)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed
next
  case bisim1BlockThrowSome thus ?case by auto
next
  case (bisim1BlockNone E V e xs stk loc pc xcp Ty)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,Suc V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,E,Suc V,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  from `P,t \<turnstile>1 \<langle>{V:Ty=None; e},(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Block1Red E')
    note [simp] = `e' = {V:Ty=None; E'}`
      and red = `P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h {V:Ty=None; e} = \<tau>move1 P h e" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover have "call1 ({V:Ty=None; e}) = call1 e" by auto
    moreover from IH[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,E,Suc V,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta E e E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim
    have "P,{V:Ty=None; E},V,h' \<turnstile> ({V:Ty=None; E'}, xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1BlockNone)
    moreover { 
      assume "no_call2 E pc"
      hence "no_call2 {V:Ty=None; E} pc" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp add: exec_move_BlockNone simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: Block_\<tau>ExecrI_None Block_\<tau>ExectI_None)+
  next
    case (Red1Block u)
    note [simp] = `e = Val u` `ta = \<epsilon>` `e' = Val u` `h' = h` `xs' = xs`
    have "\<tau>move1 P h {V:Ty=None; Val u}" by(rule \<tau>move1BlockRed)
    moreover from bisim have [simp]: "xcp = None" "loc = xs"
      and exec: "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([u], loc, length (compE2 E), None)" by(auto dest: bisim1Val2D1)
    moreover from bisim1_bsok[OF bisim]
    have "P,{V:Ty=None; E},V,h \<turnstile> (Val u, xs) \<leftrightarrow> ([u], xs, length (compE2 {V:Ty=None; E}), None)"
      by-(rule bisim1Val2, simp_all)
    ultimately show ?thesis by(fastsimp intro: Block_\<tau>ExecrI_None)
  next
    case (Block1Throw a)
    note [simp] = `e = Throw a` `ta = \<epsilon>` `e' = Throw a` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h {V:Ty=None; e}" by(auto intro: \<tau>move1BlockThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim have "P, {V:Ty=None; E}, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1BlockThrowNone)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim obtain pc'
	where "\<tau>Exec_mover_a P t E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, Suc V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t {V:Ty=None; E} h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by(auto intro: Block_\<tau>ExecrI_None)
      moreover from bisim' have "P, {V:Ty=None; E}, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1BlockThrowNone)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed
next
  case bisim1BlockThrowNone thus ?case by auto
next
  case (bisim1Sync1 e1 V e1' xs stk loc pc xcp e2)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e1',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e1,V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e1 e1' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,e1,V,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note red = `P,t \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (e1') e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from red show ?case
  proof cases
    case (Synchronized1Red1 E1')
    note [simp] = `e' = sync\<^bsub>V\<^esub> (E1') e2`
      and red = `P,t \<turnstile>1 \<langle>e1', (h, xs)\<rangle> -ta\<rightarrow> \<langle>E1', (h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h (sync\<^bsub>V\<^esub> (e1') e2) = \<tau>move1 P h e1'" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover have "call1 (sync\<^bsub>V\<^esub> (e1') e2) = call1 e1'" by auto
    moreover from IH[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,e1,V,h' \<turnstile> (E1', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta e1 e1' E1' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim `bsok e2 (Suc V)`
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h' \<turnstile> (sync\<^bsub>V\<^esub> (E1') e2, xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1Sync1)
    moreover { 
      assume "no_call2 e1 pc"
      hence "no_call2 (sync\<^bsub>V\<^esub> (e1) e2) pc" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: Sync_\<tau>ExecrI Sync_\<tau>ExectI exec_move_SyncI1)+
  next
    case Synchronized1Null
    note [simp] = `e1' = null` `e' = THROW NullPointer` `ta = \<epsilon>` `h' = h` `xs' = xs[V := Null]` 
      and V = `V < length xs`
    from bisim1 have [simp]: "xcp = None" "xs = loc"
      and exec: "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, xcp) ([Null], loc, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    from Sync_\<tau>ExecrI[OF exec]
    have "\<tau>Exec_mover_a P t (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, pc, xcp) ([Null], loc, length (compE2 e1), None)" by simp
    also from V
    have "\<tau>Exec_mover_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Null], loc, length (compE2 e1), None) ([Null], loc[V := Null], Suc (Suc (length (compE2 e1))), None)"
      by -(rule \<tau>Execr2step,auto intro: exec_instr \<tau>move2_\<tau>moves2.intros simp add: exec_move_def)
    also (rtranclp_trans)
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Null], loc[V := Null], Suc (Suc (length (compE2 e1))), None) \<epsilon>
                        h ([Null], loc[V := Null], Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr) auto
    moreover have "\<not> \<tau>move2 (compP2 P) h [Null] (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (length (compE2 e1)))) None"
      by(simp add: \<tau>move2_iff)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW NullPointer, loc[V := Null]) \<leftrightarrow> ([Null], (loc[V := Null]), Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro: bisim1Sync11)
    moreover have "\<not> \<tau>move1 P h (sync\<^bsub>V\<^esub> (null) e2)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis by auto blast
  next
    case (Lock1Synchronized a)
    note [simp] = `e1' = addr a` `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncLock a\<rbrace>` `e' = insync\<^bsub>V\<^esub> (a) e2` `h' = h` `xs' = xs[V := Addr a]` 
      and V = `V < length xs`
    from bisim1 have [simp]: "xcp = None" "xs = loc"
      and exec: "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    from Sync_\<tau>ExecrI[OF exec]
    have "\<tau>Exec_mover_a P t (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, pc, xcp) ([Addr a], loc, length (compE2 e1), None)" by simp
    also from V
    have "\<tau>Exec_mover_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a], loc, length (compE2 e1), None) ([Addr a], loc[V := Addr a], Suc (Suc (length (compE2 e1))), None)"
      by -(rule \<tau>Execr2step,auto intro: exec_instr \<tau>move2_\<tau>moves2.intros simp add: exec_move_def)
    also (rtranclp_trans)
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a], loc[V := Addr a], Suc (Suc (length (compE2 e1))), None)
                        (\<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncLock a\<rbrace>)
                        h ([], loc[V := Addr a], Suc (Suc (Suc (length (compE2 e1)))), None)"
      unfolding exec_move_def by -(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Addr a] (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (length (compE2 e1)))) None"
      by(simp add: \<tau>move2_iff)
    moreover from bisim1 bisim2 have "bsok e2 (Suc V)" "bsok e1 V"  by(auto dest: bisim1_bsok)
    from bisim1Sync4[OF bisim1_refl, OF this, of P h a "loc[V := Addr a]"]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (insync\<^bsub>V\<^esub> (a) e2, loc[V := Addr a]) \<leftrightarrow> ([], loc[V := Addr a], Suc (Suc (Suc (length (compE2 e1)))), None)" by simp
    moreover have "\<not> \<tau>move1 P h (sync\<^bsub>V\<^esub> (addr a) e2)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis by(auto simp add: nat_number ta_upd_simps) blast
  next
    case (Synchronized1Throw1 a)
    note [simp] = `e1' = Throw a` `ta = \<epsilon>` `e' = Throw a` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h (sync\<^bsub>V\<^esub> (Throw a) e2)" by(rule \<tau>move1SyncThrow)
    from bisim1 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim1 bisim1_bsok[OF bisim2]
      have "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1SyncThrow)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim1 obtain pc'
	where "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, e1, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule Sync_\<tau>ExecrI)
      moreover from bisim' bisim1_bsok[OF bisim2]
      have "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by -(rule bisim1_bisims1.bisim1SyncThrow, auto)
      ultimately show ?thesis using \<tau> by fastsimp
    qed
  qed
next
  case (bisim1Sync2 e1 V e2 v xs)
  note bisim1 = `\<And>xs. P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,t \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (Val v) e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Lock1Synchronized a)
    note [simp] = `v = Addr a` `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncLock a\<rbrace>` `e' = insync\<^bsub>V\<^esub> (a) e2`
      `h' = h` `xs' = xs[V := Addr a]` 
      and V = `V < length xs`
    from V
    have "\<tau>Exec_mover_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a, Addr a], xs, Suc (length (compE2 e1)), None) ([Addr a], xs[V := Addr a], Suc (Suc (length (compE2 e1))), None)"
      by -(rule \<tau>Execr1step,auto intro: exec_instr simp add: \<tau>move2_iff exec_move_def)
    moreover
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a], xs[V := Addr a], Suc (Suc (length (compE2 e1))), None)
                        (\<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncLock a\<rbrace>)
                        h ([], xs[V := Addr a], Suc (Suc (Suc (length (compE2 e1)))), None)"
      unfolding exec_move_def by -(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Addr a] (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (length (compE2 e1)))) None"
      by(simp add: \<tau>move2_iff)
    moreover from bisim1 bisim2 have "bsok e2 (Suc V)" "bsok e1 V"  by(auto dest: bisim1_bsok)
    from bisim1Sync4[OF bisim1_refl, OF this, of P h a "xs[V := Addr a]"]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (insync\<^bsub>V\<^esub> (a) e2, xs[V := Addr a]) \<leftrightarrow> ([], xs[V := Addr a], Suc (Suc (Suc (length (compE2 e1)))), None)" by simp
    moreover have "\<not> \<tau>move1 P h (sync\<^bsub>V\<^esub> (addr a) e2)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis by(auto simp add: nat_number ta_upd_simps) blast
  next
    case Synchronized1Null
    note [simp] = `v = Null` `e' = THROW NullPointer` `ta = \<epsilon>` `h' = h` `xs' = xs[V := Null]`
      and V = `V < length xs`
    from V
    have "\<tau>Exec_mover_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Null, Null], xs, Suc (length (compE2 e1)), None) ([Null], xs[V := Null], Suc (Suc (length (compE2 e1))), None)"
      by -(rule \<tau>Execr1step,auto intro: exec_instr simp add: exec_move_def \<tau>move2_iff)
    also have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Null], xs[V := Null], Suc (Suc (length (compE2 e1))), None) \<epsilon>
                        h ([Null], xs[V := Null], Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr) auto
    moreover have "\<not> \<tau>move2 (compP2 P) h [Null] (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (length (compE2 e1)))) None"
      by(simp add: \<tau>move2_iff)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW NullPointer, xs[V := Null]) \<leftrightarrow> ([Null], (xs[V := Null]), Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro: bisim1Sync11)
    moreover have "\<not> \<tau>move1 P h (sync\<^bsub>V\<^esub> (null) e2)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis by(auto simp add: nat_number) blast
  qed auto
next
  case (bisim1Sync3 e1 V e2 v xs)
  note bisim1 = `\<And>xs. P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,t \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (Val v) e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Lock1Synchronized a)
    note [simp] = `v = Addr a` `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncLock a\<rbrace>` `e' = insync\<^bsub>V\<^esub> (a) e2` `h' = h` `xs' = xs[V := Addr a]` 
      and V = `V < length xs`
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a], xs[V := Addr a], Suc (Suc (length (compE2 e1))), None)
                        (\<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncLock a\<rbrace>)
                        h ([], xs[V := Addr a], Suc (Suc (Suc (length (compE2 e1)))), None)"
      unfolding exec_move_def by -(rule exec_instr, auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Addr a] (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (length (compE2 e1)))) None"
      by(simp add: \<tau>move2_iff)
    moreover from bisim1 bisim2 have "bsok e2 (Suc V)" "bsok e1 V"  by(auto dest: bisim1_bsok)
    from bisim1Sync4[OF bisim1_refl, OF this, of P h a "xs[V := Addr a]"]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (insync\<^bsub>V\<^esub> (a) e2, xs[V := Addr a]) \<leftrightarrow> ([], xs[V := Addr a], Suc (Suc (Suc (length (compE2 e1)))), None)" by simp
    moreover have "\<not> \<tau>move1 P h (sync\<^bsub>V\<^esub> (addr a) e2)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis by(auto simp add: nat_number ta_upd_simps) blast
  next
    case Synchronized1Null
    note [simp] = `v = Null` `e' = THROW NullPointer` `ta = \<epsilon>` `h' = h` `xs' = xs[V := Null]` 
      and V = `V < length xs`
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Null], xs[V := Null], Suc (Suc (length (compE2 e1))), None) \<epsilon>
                        h ([Null], xs[V := Null], Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr) auto
    moreover have "\<not> \<tau>move2 (compP2 P) h [Null] (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (length (compE2 e1)))) None"
      by(simp add: \<tau>move2_iff)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW NullPointer, xs[V := Null]) \<leftrightarrow> ([Null], (xs[V := Null]), Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro: bisim1Sync11)
    moreover have "\<not> \<tau>move1 P h (sync\<^bsub>V\<^esub> (null) e2)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis by(auto simp add: nat_number) blast
  qed auto
next
  case (bisim1Sync4 e2 V e2' xs stk loc pc xcp e1 a)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,Suc V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e2 e2' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim2 = `P,e2,Suc V,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim1 = `\<And>xs. P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note red = `P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from red show ?case
  proof cases
    case (Synchronized1Red2 E')
    note [simp] = `e' = insync\<^bsub>V\<^esub> (a) E'`
      and red = `P,t \<turnstile>1 \<langle>e2', (h, xs)\<rangle> -ta\<rightarrow> \<langle>E', (h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h (insync\<^bsub>V\<^esub> (a) e2') = \<tau>move1 P h e2'" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from IH[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e2,Suc V,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e2 e2' E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have "no_call2 e2 pc \<Longrightarrow> no_call2 (sync\<^bsub>V\<^esub>(e1) e2) (Suc (Suc (Suc (length (compE2 e1) + pc))))"
      by(auto simp add: no_call2_def)
    hence "?exec ta (sync\<^bsub>V\<^esub> (e1) e2) (insync\<^bsub>V\<^esub> (a) e2') (insync\<^bsub>V\<^esub> (a) E') h stk loc (Suc (Suc (Suc (length (compE2 e1) + pc)))) xcp h' (Suc (Suc (Suc (length (compE2 e1) + pc'')))) stk'' loc'' xcp''"
      using exec' \<tau>
      by(cases "\<tau>move1 P h (insync\<^bsub>V\<^esub> (a) e2')")(auto,(blast intro: exec_move_SyncI2 Insync_\<tau>ExecrI Insync_\<tau>ExectI)+)
    moreover from bisim' bisim1_bsok[OF bisim1]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h' \<turnstile> (insync\<^bsub>V\<^esub> (a) E', xs') \<leftrightarrow> (stk'', loc'', (Suc (Suc (Suc (length (compE2 e1) + pc'')))), xcp'')"
      by(auto intro: bisim1_bisims1.bisim1Sync4)
    ultimately show ?thesis using \<tau> by auto blast+
  next
    case (Unlock1Synchronized a' v)
    note [simp] = `e2' = Val v` `e' = Val v` `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a'\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncUnlock a'\<rbrace>` `h' = h` `xs' = xs`
      and V = `V < length xs` and xsV = `xs ! V = Addr a'`
    from bisim2 have [simp]: "xcp = None" "xs = loc"
      and exec: "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, xcp) ([v], loc, length (compE2 e2), None)"
      by(auto dest: bisim1Val2D1)
    let ?pc1 = "(Suc (Suc (Suc (length (compE2 e1) + length (compE2 e2)))))"
    note Insync_\<tau>ExecrI[OF exec, of V e1]
    also from V xsV have "\<tau>Exec_mover_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([v], loc, ?pc1, None) ([Addr a', v], loc, Suc ?pc1, None)"
      by -(rule \<tau>Execr1step,auto simp add: exec_move_def intro: exec_instr \<tau>move2_\<tau>moves2.intros)
    also (rtranclp_trans)
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', v], loc, Suc ?pc1, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a'\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncUnlock a'\<rbrace>) h ([v], loc, Suc (Suc ?pc1), None)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Addr a', v] (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc1) None" by(simp add: \<tau>move2_iff)
    moreover from bisim2 bisim1 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    from bisim1Sync6[OF this, of P h v xs]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (Val v, xs) \<leftrightarrow> ([v], xs, Suc (Suc ?pc1), None)"
      by(auto simp add: nat_number)
    moreover have "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) e2')" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis by(auto simp add: ta_upd_simps) blast
  next
    case (Unlock1SynchronizedNull v)
    note [simp] = `e2' = Val v` `e' = THROW NullPointer` `ta = \<epsilon>` `h' = h` `xs' = xs`
      and V = `V < length xs` and xsV = `xs ! V = Null`
    from bisim2 have [simp]: "xcp = None" "xs = loc"
      and exec: "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, xcp) ([v], loc, length (compE2 e2), None)"
      by(auto dest: bisim1Val2D1)
    let ?pc1 = "(Suc (Suc (Suc (length (compE2 e1) + length (compE2 e2)))))"
    note Insync_\<tau>ExecrI[OF exec, of V e1]
    also from V xsV have "\<tau>Exec_mover_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([v], loc, ?pc1, None) ([Null, v], loc, Suc ?pc1, None)"
      by -(rule \<tau>Execr1step,auto intro: exec_instr \<tau>move2_\<tau>moves2.intros simp add: exec_move_def)
    also (rtranclp_trans)
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Null, v], loc, Suc ?pc1, None) \<epsilon> h ([Null, v], loc, Suc ?pc1, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Null, v] (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc1) None" by(simp add: \<tau>move2_iff)
    moreover from bisim2 bisim1 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    from bisim1Sync12[OF this, of P h xs v]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW NullPointer,xs) \<leftrightarrow> ([Null, v],xs,Suc ?pc1,\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto simp add: nat_number)
    moreover have "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) e2')" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis by auto blast
  next
    case (Unlock1SynchronizedFail a' v)
    note [simp] = `e2' = Val v` `e' = THROW IllegalMonitorState` `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a'\<rbrace>` `xs' = xs` `h' = h`
      and V = `V < length xs` and xsV = `xs ! V = Addr a'`
    from bisim2 have [simp]: "xcp = None" "xs = loc"
      and exec: "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, xcp) ([v], loc, length (compE2 e2), None)"
      by(auto dest: bisim1Val2D1)
    let ?pc1 = "(Suc (Suc (Suc (length (compE2 e1) + length (compE2 e2)))))"
    note Insync_\<tau>ExecrI[OF exec, of V e1]
    also from V xsV have "\<tau>Exec_mover_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([v], loc, ?pc1, None) ([Addr a', v], loc, Suc ?pc1, None)"
      by -(rule \<tau>Execr1step,auto intro: exec_instr \<tau>move2_\<tau>moves2.intros simp add: exec_move_def)
    also (rtranclp_trans)
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', v], loc, Suc ?pc1, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a'\<rbrace>) h ([Addr a', v], loc, Suc ?pc1, \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Addr a', v] (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc1) None" by(simp add: \<tau>move2_iff)
    moreover from bisim2 bisim1 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    from bisim1Sync13[OF this, of P h xs "Addr a'" v]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW IllegalMonitorState,xs) \<leftrightarrow> ([Addr a', v],xs,Suc ?pc1,\<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      by(auto simp add: nat_number)
    moreover have "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) Val v)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis by(auto simp add: ta_upd_simps) blast
  next
    case (Synchronized1Throw2 a' ad)
    note [simp] = `e2' = Throw ad` `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a'\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncUnlock a'\<rbrace>` `e' = Throw ad`
      `h' = h` `xs' = xs` and xsV = `xs ! V = Addr a'` and V = `V < length xs`
    let ?pc = "6 + length (compE2 e1) + length (compE2 e2)"
    let ?stk = "Addr ad # drop (size stk - 0) stk"
    from bisim2 have [simp]: "xs = loc" by(auto dest: bisim1_ThrowD)
    from bisim2
    have "\<tau>Exec_movet_a P t (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, Suc (Suc (Suc (length (compE2 e1) + pc))), xcp) ([Addr ad], loc, ?pc, None)"    
      by(auto intro: bisim1_insync_Throw_exec)
    also from xsV V 
    have "\<tau>Exec_movet_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr ad], loc, ?pc, None) ([Addr a', Addr ad], loc, Suc ?pc, None)"
      by -(rule \<tau>Exect1step,auto intro: exec_instr \<tau>move2Sync7 simp add: exec_move_def)
    also (tranclp_trans)
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', Addr ad], loc, Suc ?pc, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a'\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncUnlock a'\<rbrace>) h ([Addr ad], loc, Suc (Suc ?pc), None)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Addr a', Addr ad] (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc) None" by(simp add: \<tau>move2_iff)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (Throw ad, loc) \<leftrightarrow> ([Addr ad], loc, 8 + length (compE2 e1) + length (compE2 e2), None)"
      by(auto intro: bisim1Sync9)
    moreover have "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) Throw ad)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis by(auto simp add: add_assoc ta_upd_simps)(blast intro: tranclp_into_rtranclp)
  next
    case (Synchronized1Throw2Fail a' ad)
    note [simp] = `e2' = Throw ad` `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a'\<rbrace>` `e' = THROW IllegalMonitorState` `h' = h` `xs' = xs`
      and xsV = `xs ! V = Addr a'` and V = `V < length xs`
    let ?pc = "6 + length (compE2 e1) + length (compE2 e2)"
    let ?stk = "Addr ad # drop (size stk - 0) stk"
    from bisim2 have [simp]: "xs = loc" by(auto dest: bisim1_ThrowD)
    from bisim2
    have "\<tau>Exec_movet_a P t (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, Suc (Suc (Suc (length (compE2 e1) + pc))), xcp) ([Addr ad], loc, ?pc, None)"
      by(auto intro: bisim1_insync_Throw_exec)
    also from xsV V
    have "\<tau>Exec_movet_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr ad], loc, ?pc, None) ([Addr a', Addr ad], loc, Suc ?pc, None)"
      by -(rule \<tau>Exect1step,auto intro: exec_instr \<tau>move2Sync7 simp add: exec_move_def)
    also (tranclp_trans)
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', Addr ad], loc, Suc ?pc, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a'\<rbrace>) h ([Addr a', Addr ad], loc, Suc ?pc, \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Addr a', Addr ad] (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc) None" by(simp add: \<tau>move2_iff)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW IllegalMonitorState, loc) \<leftrightarrow> ([Addr a', Addr ad], loc, 7 + length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      by(auto intro: bisim1Sync14)
    moreover have "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) e2')"  by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis by(auto simp add: add_assoc ta_upd_simps)(blast intro: tranclp_into_rtranclp)
  next
    case (Synchronized1Throw2Null ad)
    note [simp] = `e2' = Throw ad` `ta = \<epsilon>` `e' = THROW NullPointer` `h' = h` `xs' = xs`
      and xsV = `xs ! V = Null` and V = `V < length xs`
    let ?pc = "6 + length (compE2 e1) + length (compE2 e2)"
    let ?stk = "Addr ad # drop (size stk - 0) stk"
    from bisim2 have [simp]: "xs = loc" by(auto dest: bisim1_ThrowD)
    from bisim2
    have "\<tau>Exec_movet_a P t (sync\<^bsub>V\<^esub> (e1) e2) h (stk, loc, Suc (Suc (Suc (length (compE2 e1) + pc))), xcp) ([Addr ad], loc, ?pc, None)"
      by(auto intro: bisim1_insync_Throw_exec)
    also from xsV V 
    have "\<tau>Exec_movet_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr ad], loc, ?pc, None) ([Null, Addr ad], loc, Suc ?pc, None)"
      by -(rule \<tau>Exect1step,auto intro: exec_instr simp add: exec_move_def \<tau>move2_iff)
    also (tranclp_trans)
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Null, Addr ad], loc, Suc ?pc, None) \<epsilon> h ([Null, Addr ad], loc, Suc ?pc, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Null, Addr ad] (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc) None" by(simp add: \<tau>move2_iff)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([Null, Addr ad], loc, 7 + length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro: bisim1Sync15)
    moreover have "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) e2')"  by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis by(auto simp add: add_assoc)(blast intro: tranclp_into_rtranclp)
  qed 
next
  case (bisim1Sync5 e1 V e2 a v xs)
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim1 = `\<And>xs. P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Val v,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Unlock1Synchronized a')
    note [simp] = `e' = Val v` `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a'\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncUnlock a'\<rbrace>` `h' = h` `xs' = xs`
      and V = `V < length xs` and xsV = `xs ! V = Addr a'`
    let ?pc1 = "4 + length (compE2 e1) + length (compE2 e2)"
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', v], xs, ?pc1, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a'\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncUnlock a'\<rbrace>) h ([v], xs, Suc ?pc1, None)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Addr a', v] (sync\<^bsub>V\<^esub> (e1) e2) ?pc1 None" by(simp add: \<tau>move2_iff)
    moreover from bisim2 bisim1 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    from bisim1Sync6[OF this, of P h v xs]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (Val v, xs) \<leftrightarrow> ([v], xs, Suc ?pc1, None)"
      by(auto simp add: nat_number)
    moreover have "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) Val v)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis using xsV by(auto simp add: nat_number ta_upd_simps) blast
  next
    case Unlock1SynchronizedNull
    note [simp] = `e' = THROW NullPointer` `ta = \<epsilon>` `h' = h` `xs' = xs`
      and V = `V < length xs` and xsV = `xs ! V = Null`
    let ?pc1 = "4 + length (compE2 e1) + length (compE2 e2)"
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Null, v], xs, ?pc1, None) \<epsilon> h ([Null, v], xs, ?pc1, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Null, v] (sync\<^bsub>V\<^esub> (e1) e2) ?pc1 None" by(simp add: \<tau>move2_iff)
    moreover from bisim2 bisim1 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    from bisim1Sync12[OF this, of P h xs v]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW NullPointer,xs) \<leftrightarrow> ([Null, v],xs,?pc1,\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto simp add: nat_number)
    moreover have "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) Val v)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis using xsV by(auto simp add: nat_number) blast
  next
    case (Unlock1SynchronizedFail a')
    note [simp] = `e' = THROW IllegalMonitorState` `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a'\<rbrace>` `xs' = xs` `h' = h`
      and V = `V < length xs` and xsV = `xs ! V = Addr a'`
    let ?pc1 = "4 + length (compE2 e1) + length (compE2 e2)"
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', v], xs, ?pc1, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a'\<rbrace>) h ([Addr a', v], xs, ?pc1, \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Addr a', v] (sync\<^bsub>V\<^esub> (e1) e2) ?pc1 None" by(simp add: \<tau>move2_iff)
    moreover from bisim2 bisim1 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    from bisim1Sync13[OF this, of P h xs "Addr a'" v]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW IllegalMonitorState,xs) \<leftrightarrow> ([Addr a', v],xs,?pc1,\<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      by(auto simp add: nat_number)
    moreover have "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) Val v)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis using xsV by(auto simp add: nat_number ta_upd_simps) blast
  qed auto
next
  case bisim1Sync6 thus ?case by auto
next
  case (bisim1Sync7 e1 V e2 a ad xs)
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim1 = `\<And>xs. P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw ad,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Synchronized1Throw2 a')
    note [simp] = `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a'\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncUnlock a'\<rbrace>` `e' = Throw ad` `h' = h` `xs' = xs`
      and xsV = `xs ! V = Addr a'` and V = `V < length xs`
    let ?pc = "6 + length (compE2 e1) + length (compE2 e2)"
    from xsV V
    have "\<tau>Exec_mover_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr ad], xs, ?pc, None) ([Addr a', Addr ad], xs, Suc ?pc, None)"
      by -(rule \<tau>Execr1step,auto intro: exec_instr simp add: exec_move_def \<tau>move2_iff)
    moreover have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', Addr ad], xs, Suc ?pc, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a'\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncUnlock a'\<rbrace>) h ([Addr ad], xs, Suc (Suc ?pc), None)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Addr a', Addr ad] (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc) None" by(simp add: \<tau>move2_iff)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (Throw ad, xs) \<leftrightarrow> ([Addr ad], xs, 8 + length (compE2 e1) + length (compE2 e2), None)"
      by(auto intro: bisim1Sync9)
    moreover have "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) Throw ad)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis by(auto simp add: add_assoc nat_number ta_upd_simps) blast
  next
    case (Synchronized1Throw2Fail a')
    note [simp] = `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a'\<rbrace>` `e' = THROW IllegalMonitorState` `h' = h` `xs' = xs`
      and xsV = `xs ! V = Addr a'` and V = `V < length xs`
    let ?pc = "6 + length (compE2 e1) + length (compE2 e2)"
    from xsV V
    have "\<tau>Exec_mover_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr ad], xs, ?pc, None) ([Addr a', Addr ad], xs, Suc ?pc, None)"
      by -(rule \<tau>Execr1step,auto intro: exec_instr simp add: exec_move_def \<tau>move2_iff)
    moreover have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', Addr ad], xs, Suc ?pc, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a'\<rbrace>) h ([Addr a', Addr ad], xs, Suc ?pc, \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Addr a', Addr ad] (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc) None" by(simp add: \<tau>move2_iff)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW IllegalMonitorState, xs) \<leftrightarrow> ([Addr a', Addr ad], xs, 7 + length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      by(auto intro: bisim1Sync14)
    moreover have "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) Throw ad)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis by(auto simp add: add_assoc ta_upd_simps) blast
  next
    case Synchronized1Throw2Null
    note [simp] = `ta = \<epsilon>` `e' = THROW NullPointer` `h' = h` `xs' = xs`
      and xsV = `xs ! V = Null` and V = `V < length xs`
    let ?pc = "6 + length (compE2 e1) + length (compE2 e2)"
    from xsV V 
    have "\<tau>Exec_mover_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr ad], xs, ?pc, None) ([Null, Addr ad], xs, Suc ?pc, None)"
      by -(rule \<tau>Execr1step,auto intro: exec_instr simp add: exec_move_def \<tau>move2_iff)
    moreover have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Null, Addr ad], xs, Suc ?pc, None) \<epsilon> h ([Null, Addr ad], xs, Suc ?pc, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Null, Addr ad] (sync\<^bsub>V\<^esub> (e1) e2) (Suc ?pc) None" by(simp add: \<tau>move2_iff)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([Null, Addr ad], xs, 7 + length (compE2 e1) + length (compE2 e2), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro: bisim1Sync15)
    moreover have "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) Throw ad)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis by(auto simp add: add_assoc) blast
  qed auto 
next
  case (bisim1Sync8 e1 V e2 a ad xs)
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim1 = `\<And>xs. P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw ad,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Synchronized1Throw2 a')
    note [simp] = `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>a'\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncUnlock a'\<rbrace>` `e' = Throw ad` `h' = h` `xs' = xs`
      and xsV = `xs ! V = Addr a'` and V = `V < length xs`
    let ?pc = "7 + length (compE2 e1) + length (compE2 e2)"
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', Addr ad], xs, ?pc, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a'\<rbrace>\<lbrace>\<^bsub>o\<^esub>SyncUnlock a'\<rbrace>) h ([Addr ad], xs, Suc ?pc, None)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Addr a', Addr ad] (sync\<^bsub>V\<^esub> (e1) e2) ?pc None" by(simp add: \<tau>move2_iff)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (Throw ad, xs) \<leftrightarrow> ([Addr ad], xs, 8 + length (compE2 e1) + length (compE2 e2), None)"
      by(auto intro: bisim1Sync9)
    moreover have "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) Throw ad)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis using xsV by(auto simp add: add_assoc nat_number ta_upd_simps) blast
  next
    case (Synchronized1Throw2Fail a')
    note [simp] = `ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>a'\<rbrace>` `e' = THROW IllegalMonitorState` `h' = h` `xs' = xs` 
      and xsV = `xs ! V = Addr a'` and V = `V < length xs`
    let ?pc = "7 + length (compE2 e1) + length (compE2 e2)"
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Addr a', Addr ad], xs, ?pc, None) (\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a'\<rbrace>) h ([Addr a', Addr ad], xs, ?pc, \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Addr a', Addr ad] (sync\<^bsub>V\<^esub> (e1) e2) ?pc None" by(simp add: \<tau>move2_iff)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW IllegalMonitorState, xs) \<leftrightarrow> ([Addr a', Addr ad], xs, ?pc, \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      by(auto intro: bisim1Sync14)
    moreover have "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) Throw ad)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis using xsV by(auto simp add: add_assoc ta_upd_simps) blast
  next
    case Synchronized1Throw2Null
    note [simp] = `ta = \<epsilon>` `e' = THROW NullPointer` `h' = h` `xs' = xs`
      and xsV = `xs ! V = Null` and V = `V < length xs`
    let ?pc = "7 + length (compE2 e1) + length (compE2 e2)"
    have "exec_move_a P t (sync\<^bsub>V\<^esub> (e1) e2) h ([Null, Addr ad], xs, ?pc, None) \<epsilon> h ([Null, Addr ad], xs, ?pc, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding exec_move_def by(rule exec_instr)(auto simp add: is_Ref_def)
    moreover have "\<not> \<tau>move2 (compP2 P) h [Null, Addr ad] (sync\<^bsub>V\<^esub> (e1) e2) ?pc None" by(simp add: \<tau>move2_iff)
    moreover from bisim1 bisim2 have "bsok e1 V" "bsok e2 (Suc V)" by(auto dest: bisim1_bsok)
    hence "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([Null, Addr ad], xs, ?pc, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(auto intro: bisim1Sync15)
    moreover have "\<not> \<tau>move1 P h (insync\<^bsub>V\<^esub> (a) Throw ad)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    ultimately show ?thesis using xsV by(auto simp add: add_assoc) blast
  qed auto
next
  case bisim1Sync9 thus ?case by auto
next
  case bisim1Sync10 thus ?case by auto
next
  case bisim1Sync11 thus ?case by auto
next
  case bisim1Sync12 thus ?case by auto
next
  case bisim1Sync13 thus ?case by auto
next
  case bisim1Sync14 thus ?case by auto
next
  case bisim1Sync15 thus ?case by auto
next
  case bisim1SyncThrow thus ?case by auto
next
  case (bisim1Seq1 e1 n e1' xs stk loc pc xcp e2)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e1',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e1,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e1 e1' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,e1,n,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,e2,n,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note red = `P,t \<turnstile>1 \<langle>e1';; e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from red show ?case
  proof cases
    case (Seq1Red E')
    note [simp] = `e' = E';;e2`
      and red = `P,t \<turnstile>1 \<langle>e1', (h, xs)\<rangle> -ta\<rightarrow> \<langle>E', (h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h (e1';; e2) = \<tau>move1 P h e1'" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover have "call1 (e1';; e2) = call1 e1'" by auto
    moreover from IH[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,e1,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta e1 e1' E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim `bsok e2 n`
    have "P,e1;; e2,n,h' \<turnstile> (E';; e2, xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1Seq1)
    moreover { 
      assume "no_call2 e1 pc"
      hence "no_call2 (e1;; e2) pc" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: Seq_\<tau>ExecrI1 Seq_\<tau>ExectI1 exec_move_SeqI1)+
  next
    case (Red1Seq v)
    note [simp] = `e1' = Val v` `ta = \<epsilon>` `h' = h` `xs' = xs` `e' = e2`
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, xcp) ([v], loc, length (compE2 e1), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (e1;; e2) h (stk, loc, pc, xcp) ([v], loc, length (compE2 e1), None)"
      by-(rule Seq_\<tau>ExecrI1)
    moreover have "exec_move_a P t (e1;; e2) h ([v], loc, length (compE2 e1), None) \<epsilon> h ([], loc, Suc (length (compE2 e1)), None)"
      unfolding exec_move_def by(rule exec_instr, auto)
    moreover have "\<tau>move2 (compP2 P) h [v] (e1;;e2) (length (compE2 e1)) None" by(simp add: \<tau>move2_iff)
    ultimately have "\<tau>Exec_mover_a P t (e1;; e2) h (stk, loc, pc, xcp) ([], loc, Suc (length (compE2 e1)), None)"
      by(auto intro: rtranclp.rtrancl_into_rtrancl \<tau>exec_moveI simp add: compP2_def)
    moreover from bisim1_refl[of e2 n P h loc] `bsok e1 n` `bsok e2 n`
    have "P, e1;; e2, n, h \<turnstile> (e2, xs) \<leftrightarrow> ([], loc, Suc (length (compE2 e1) + 0), None)"
      unfolding s by-(rule bisim1Seq2, auto)
    moreover have "\<tau>move1 P h (Val v;; e2)" by(rule \<tau>move1SeqRed)
    ultimately show ?thesis by(auto)
  next
    case (Seq1Throw a)
    note [simp] = `e1' = Throw a` `ta = \<epsilon>` `e' = Throw a` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h (Throw a;; e2)" by(rule \<tau>move1SeqThrow)
    from bisim1 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim1 bisim1_bsok[OF bisim2]
      have "P, e1;; e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	by(auto intro: bisim1SeqThrow1)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim1 obtain pc'
	where "\<tau>Exec_mover_a P t e1 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, e1, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (e1;;e2) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule Seq_\<tau>ExecrI1)
      moreover from bisim' bisim1_bsok[OF bisim2]
      have "P, e1;;e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1SeqThrow1, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed
next
  case bisim1SeqThrow1 thus ?case by fastsimp
next
  case (bisim1Seq2 e2 n e2' xs stk loc pc xcp e1)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e2 e2' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim2 = `P,e2,n,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim1 = `\<And>xs. P,e1,n,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note red = `P,t \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from IH[OF red] obtain pc'' stk'' loc'' xcp''
    where bisim': "P,e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
    and exec': "?exec ta e2 e2' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
  have "no_call2 e2 pc \<Longrightarrow> no_call2 (e1;; e2) (Suc (length (compE2 e1) + pc))"
      by(auto simp add: no_call2_def)
  hence "?exec ta (e1;; e2) e2' e' h stk loc (Suc (length (compE2 e1) + pc)) xcp h' (Suc (length (compE2 e1) + pc'')) stk'' loc'' xcp''"
    using exec' by(cases "\<tau>move1 P h e2'")(auto, (blast intro: Seq_\<tau>ExecrI2 Seq_\<tau>ExectI2 exec_move_SeqI2)+)
  moreover from bisim' `bsok e1 n`
  have "P,e1;;e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', Suc (length (compE2 e1) + pc''), xcp'')"
    by(rule bisim1_bisims1.bisim1Seq2)
  ultimately show ?case by(auto split: split_if_asm) blast+
next
  case (bisim1Cond1 E n e xs stk loc pc xcp e1 e2)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim1 = `\<And>xs. P,e1,n,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e2,n,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,t \<turnstile>1 \<langle>if (e) e1 else e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Cond1Red b')
    note [simp] = `e' = if (b') e1 else e2`
      and red = `P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>b',(h', xs')\<rangle>`
    from red have "\<tau>move1 P h (if (e) e1 else e2) = \<tau>move1 P h e" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover have "call1 (if (e) e1 else e2) = call1 e" by auto
    moreover from IH[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,E,n,h' \<turnstile> (b', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta E e b' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim `bsok e1 n` `bsok e2 n`
    have "P,if (E) e1 else e2,n,h' \<turnstile> (if (b') e1 else e2, xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1Cond1)
    moreover { 
      assume "no_call2 E pc"
      hence "no_call2 (if (E) e1 else e2) pc" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: Cond_\<tau>ExecrI1 Cond_\<tau>ExectI1 exec_move_CondI1)+
  next
    case Red1CondT
    note [simp] = `e = true` `e' = e1` `ta = \<epsilon>` `h' = h` `xs' = xs` 
    from bisim have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([Bool True], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (if (E) e1 else e2) h (stk, loc, pc, xcp) ([Bool True], loc, length (compE2 E), None)"
      by-(rule Cond_\<tau>ExecrI1)
    moreover have "exec_move_a P t (if (E) e1 else e2) h ([Bool True], loc, length (compE2 E), None) \<epsilon> h ([], loc, Suc (length (compE2 E)), None)"
      unfolding exec_move_def by(rule exec_instr, auto)
    moreover have "\<tau>move2 (compP2 P) h [Bool True] (if (E) e1 else e2) (length (compE2 E)) None" by(simp add: \<tau>move2_iff)
    ultimately have "\<tau>Exec_movet_a P t (if (E) e1 else e2) h (stk, loc, pc, xcp) ([], loc, Suc (length (compE2 E)), None)"
      by(auto intro: rtranclp_into_tranclp1 \<tau>exec_moveI simp add: compP2_def)
    moreover have "\<tau>move1 P h (if (true) e1 else e2)" by(rule \<tau>move1CondRed)
    moreover from bisim bisim1 bisim2 have "bsok E n" "bsok e1 n" "bsok e2 n" by(auto dest: bisim1_bsok)
    with bisim1_refl[of e1 n P h loc]
    have "P, if (E) e1 else e2, n, h \<turnstile> (e1, xs) \<leftrightarrow> ([], loc, Suc (length (compE2 E) + 0), None)"
      unfolding s by-(rule bisim1CondThen, auto)
    ultimately show ?thesis by (fastsimp)
  next
    case Red1CondF
    note [simp] = `e = false` `e' = e2` `ta = \<epsilon>` `h' = h` `xs' = xs`
    from bisim have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([Bool False], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (if (E) e1 else e2) h (stk, loc, pc, xcp) ([Bool False], loc, length (compE2 E), None)"
      by-(rule Cond_\<tau>ExecrI1)
    moreover have "exec_move_a P t (if (E) e1 else e2) h ([Bool False], loc, length (compE2 E), None) \<epsilon> h ([], loc, Suc (Suc (length (compE2 E) + length (compE2 e1))), None)"
      unfolding exec_move_def by(rule exec_instr)(auto)
    moreover have "\<tau>move2 (compP2 P) h [Bool False] (if (E) e1 else e2) (length (compE2 E)) None" by(rule \<tau>move2CondRed)
    ultimately have "\<tau>Exec_movet_a P t (if (E) e1 else e2) h (stk, loc, pc, xcp) ([], loc, Suc (Suc (length (compE2 E) + length (compE2 e1))), None)"
      by(auto intro: rtranclp_into_tranclp1 \<tau>exec_moveI simp add: compP2_def)
    moreover have "\<tau>move1 P h (if (false) e1 else e2)" by(rule \<tau>move1CondRed)
    moreover from bisim bisim1 bisim2 have "bsok E n" "bsok e1 n" "bsok e2 n" by(auto dest: bisim1_bsok)
    with bisim1_refl[of e2 n P h loc]
    have "P, if (E) e1 else e2, n, h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, (Suc (Suc (length (compE2 E) + length (compE2 e1) + 0))), None)"
      unfolding s by-(rule bisim1CondElse, auto)
    ultimately show ?thesis using s by auto(blast intro: tranclp_into_rtranclp)
  next
    case (Cond1Throw a)
    note [simp] = `e = Throw a` `ta = \<epsilon>` `e' = Throw a` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h (if (Throw a) e1 else e2)" by(rule \<tau>move1CondThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2]
      have "P, if (E) e1 else e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1CondThrow)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim obtain pc'
	where "\<tau>Exec_mover_a P t E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (if (E) e1 else e2) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule Cond_\<tau>ExecrI1)
      moreover from bisim' bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2]
      have "P, if (E) e1 else e2, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1CondThrow, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed
next
  case (bisim1CondThen e1 n e1' xs stk loc pc xcp e e2)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e1',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e1,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e1 e1' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,e1,n,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e2,n,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  from IH[OF `P,t \<turnstile>1 \<langle>e1',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`] obtain pc'' stk'' loc'' xcp''
    where bisim': "P,e1,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
    and exec': "?exec ta e1 e1' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
  have "no_call2 e1 pc \<Longrightarrow> no_call2 (if (e) e1 else e2) (Suc (length (compE2 e) + pc))"
      by(auto simp add: no_call2_def)
    hence "?exec ta (if (e) e1 else e2) e1' e' h stk loc (Suc (length (compE2 e) + pc)) xcp h' (Suc (length (compE2 e) + pc'')) stk'' loc'' xcp''"
    using exec' by(cases "\<tau>move1 P h e1'")(auto, (blast intro: Cond_\<tau>ExecrI2 Cond_\<tau>ExectI2 exec_move_CondI2)+)
  moreover from bisim' `bsok e n` `bsok e2 n`
  have "P,if (e) e1 else e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', Suc (length (compE2 e) + pc''), xcp'')"
    by(rule bisim1_bisims1.bisim1CondThen)
  ultimately show ?case
    by(auto split: split_if_asm) blast+
next
  case (bisim1CondElse e2 n e2' xs stk loc pc xcp e e1)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta e2 e2' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim2 = `P,e2,n,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim1 = `\<And>xs. P,e1,n,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  from IH[OF `P,t \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`] obtain pc'' stk'' loc'' xcp''
    where bisim': "P,e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
    and exec': "?exec ta e2 e2' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
  have "no_call2 e2 pc \<Longrightarrow> no_call2 (if (e) e1 else e2) (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc)))"
      by(auto simp add: no_call2_def)
  hence "?exec ta (if (e) e1 else e2) e2' e' h stk loc (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc))) xcp h' (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc''))) stk'' loc'' xcp''"
    using exec' by(cases "\<tau>move1 P h e2'")(auto, (blast intro: Cond_\<tau>ExecrI3 Cond_\<tau>ExectI3 exec_move_CondI3)+)
  moreover from bisim' `bsok e n` `bsok e1 n`
  have "P,if (e) e1 else e2,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', Suc (Suc (length (compE2 e) + length (compE2 e1) + pc'')), xcp'')"
    by(rule bisim1_bisims1.bisim1CondElse)
  ultimately show ?case
    by(auto split: split_if_asm) blast+
next
  case bisim1CondThrow thus ?case by auto
next
  case (bisim1While1 c n e xs)
  note bisim1 = `\<And>xs. P,c,n,h \<turnstile> (c, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,t \<turnstile>1 \<langle>while (c) e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case Red1While
    note [simp] = `ta = \<epsilon>` `e' = if (c) (e;; while (c) e) else unit` `h' = h` `xs' = xs` 
    have "\<tau>move1 P h (while (c) e)" by(rule \<tau>move1WhileRed)
    moreover from `bsok c n` `bsok e n`
    have "P,while (c) e,n,h \<turnstile> (if (c) (e;; while (c) e) else unit, xs) \<leftrightarrow> ([], xs, 0, None)"
      by(rule bisim1_bisims1.bisim1While3[OF bisim1_refl])
    moreover have "sim12_size (while (c) e) > sim12_size e'" by(simp)
    ultimately show ?thesis by auto
  qed
next
  case (bisim1While3 c n c' xs stk loc pc xcp e)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>c',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,c,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta c c' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,c,n,h \<turnstile> (c', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,t \<turnstile>1 \<langle>if (c') (e;; while (c) e) else unit,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Cond1Red b')
    note [simp] = `e' = if (b') (e;; while (c) e) else unit`
      and red = `P,t \<turnstile>1 \<langle>c',(h, xs)\<rangle> -ta\<rightarrow> \<langle>b',(h', xs')\<rangle>`
    from red have "\<tau>move1 P h (if (c') (e;; while (c) e) else unit) = \<tau>move1 P h c'" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from red have "call1 (if (c') (e;;while (c) e) else unit) = call1 c'" by auto
    moreover from IH[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,c,n,h' \<turnstile> (b', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta c c' b' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim `bsok e n`
    have "P,while (c) e,n,h' \<turnstile> (if (b') (e;; while (c) e) else unit, xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1While3)
    moreover { 
      assume "no_call2 c pc"
      hence "no_call2 (while (c) e) pc" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: While_\<tau>ExecrI1 While_\<tau>ExectI1 exec_move_WhileI1)+
  next
    case Red1CondT
    note [simp] = `c' = true` `e' = e;; while (c) e` `ta = \<epsilon>` `h' = h` `xs' = xs`
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t c h (stk, loc, pc, xcp) ([Bool True], loc, length (compE2 c), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (while (c) e) h (stk, loc, pc, xcp) ([Bool True], loc, length (compE2 c), None)"
      by-(rule While_\<tau>ExecrI1)
    moreover have "exec_move_a P t (while (c) e) h ([Bool True], loc, length (compE2 c), None) \<epsilon> h ([], loc, Suc (length (compE2 c)), None)"
      unfolding exec_move_def by(rule exec_instr, auto)
    moreover have "\<tau>move2 (compP2 P) h [Bool True] (while (c) e) (length (compE2 c)) None" by(simp add: \<tau>move2_iff)
    ultimately have "\<tau>Exec_movet_a P t (while (c) e) h (stk, loc, pc, xcp) ([], loc, Suc (length (compE2 c)), None)"
      by(auto intro: rtranclp_into_tranclp1 \<tau>exec_moveI simp add: compP2_def)
    moreover have "\<tau>move1 P h (if (c') (e;; while (c) e) else unit)" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from bisim1 bisim2 have "bsok c n" "bsok e n" by(auto dest: bisim1_bsok)
    with bisim1_refl[of e n P h loc]
    have "P, while (c) e, n, h \<turnstile> (e;; while (c) e, xs) \<leftrightarrow> ([], loc, Suc (length (compE2 c) + 0), None)"
      unfolding s by-(rule bisim1While4, auto)
    ultimately show ?thesis by (fastsimp)
  next
    case Red1CondF
    note [simp] = `c' = false` `e' = unit` `ta = \<epsilon>` `h' = h` `xs' = xs`
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t c h (stk, loc, pc, xcp) ([Bool False], loc, length (compE2 c), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (while (c) e) h (stk, loc, pc, xcp) ([Bool False], loc, length (compE2 c), None)"
      by-(rule While_\<tau>ExecrI1)
    moreover have "exec_move_a P t (while (c) e) h ([Bool False], loc, length (compE2 c), None) \<epsilon> h ([], loc, Suc (Suc (Suc (length (compE2 c) + length (compE2 e)))), None)"
      by(auto intro!: exec_instr simp add: exec_move_def)
    moreover have "\<tau>move2 (compP2 P) h [Bool False] (while (c) e) (length (compE2 c)) None" by(simp add: \<tau>move2_iff)
    ultimately have "\<tau>Exec_mover_a P t (while (c) e) h (stk, loc, pc, xcp) ([], loc, Suc (Suc (Suc (length (compE2 c) + length (compE2 e)))), None)"
      by(auto intro: rtranclp.rtrancl_into_rtrancl \<tau>exec_moveI simp add: compP2_def)
    moreover have "\<tau>move1 P h (if (false) (e;;while (c) e) else unit)" by(rule \<tau>move1CondRed)
    moreover from bisim1 bisim2 have "bsok c n" "bsok e n" by(auto dest: bisim1_bsok)
    hence "P, while (c) e, n, h \<turnstile> (unit, xs) \<leftrightarrow> ([], loc, (Suc (Suc (Suc (length (compE2 c) + length (compE2 e))))), None)"
      unfolding s by-(rule bisim1While7, auto)
    ultimately show ?thesis using s by auto
  next
    case (Cond1Throw a)
    note [simp] = `c' = Throw a` `ta = \<epsilon>` `e' = Throw a` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h (if (c') (e;; while (c) e) else unit)" by(auto intro: \<tau>move1CondThrow)
    from bisim1 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim1 bisim1_bsok[OF bisim2]
      have "P, while (c) e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1_bisims1.bisim1WhileThrow1)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim1 obtain pc'
	where "\<tau>Exec_mover_a P t c h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, c, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (while (c) e) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule While_\<tau>ExecrI1)
      moreover from bisim' bisim1_bsok[OF bisim2]
      have "P, while (c) e, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule bisim1WhileThrow1, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed 
next
  case (bisim1While4 E n e xs stk loc pc xcp c)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim2 = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim1 = `\<And>xs. P,c,n,h \<turnstile> (c, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,t \<turnstile>1 \<langle>e;; while (c) E,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case (Seq1Red E')
    note [simp] = `e' = E';;while (c) E`
      and red = `P,t \<turnstile>1 \<langle>e, (h, xs)\<rangle> -ta\<rightarrow> \<langle>E', (h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h (e;; while (c) E) = \<tau>move1 P h e" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    with IH[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim: "P,E,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta E e E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (while (c) E) (e;;while (c) E) (E';;while (c) E) h stk loc (Suc (length (compE2 c) + pc)) xcp h' (Suc (length (compE2 c) + pc'')) stk'' loc'' xcp''"
    proof(cases "\<tau>move1 P h (e;; while (c) E)")
      case True
      with exec' show ?thesis using \<tau> by(fastsimp intro: While_\<tau>ExecrI2 While_\<tau>ExectI2)
    next
      case False
      with exec' \<tau> obtain pc' stk' loc' xcp'
	where e: "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
	and e': "exec_move_a P t E h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 (compP2 P) h stk' E pc' xcp'" 
        and call: "(call1 e = None \<or> no_call2 E pc \<or> pc' = pc \<and> stk' = stk \<and> loc' = loc \<and> xcp' = xcp)" by auto
      from e have "\<tau>Exec_mover_a P t (while (c) E) h (stk, loc, Suc (length (compE2 c) + pc), xcp) (stk', loc', Suc (length (compE2 c) + pc'), xcp')" by(rule While_\<tau>ExecrI2)
      moreover
      from e' have "exec_move_a P t (while (c) E) h (stk', loc', Suc (length (compE2 c) + pc'), xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', Suc (length (compE2 c) + pc''), xcp'')"
	by(rule exec_move_WhileI2)
      moreover from \<tau>' e' have "\<not> \<tau>move2 (compP2 P) h stk' (while (c) E) (Suc (length (compE2 c) + pc')) xcp'"
        by(auto simp add: \<tau>move2_iff)
      moreover have "call1 (e;; while (c) E) = call1 e" by simp
      moreover have "no_call2 E pc \<Longrightarrow> no_call2 (while (c) E) (Suc (length (compE2 c) + pc))"
        by(auto simp add: no_call2_def)
      ultimately show ?thesis using False call by(auto simp del: split_paired_Ex call1_calls1.simps)
    qed
    with bisim \<tau> `bsok c n` show ?thesis by auto (blast intro: bisim1_bisims1.bisim1While4)+
  next
    case (Red1Seq v)
    note [simp] = `e = Val v` `ta = \<epsilon>` `e' = while (c) E` `h' = h` `xs' = xs`
    from bisim2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (while (c) E) h (stk, loc, Suc (length (compE2 c) + pc), xcp) ([v], loc, Suc (length (compE2 c) + length (compE2 E)), None)"
      by-(rule While_\<tau>ExecrI2)
    moreover
    have "exec_move_a P t (while (c) E) h ([v], loc, Suc (length (compE2 c) + length (compE2 E)), None) \<epsilon> h ([], loc, Suc (Suc (length (compE2 c) + length (compE2 E))), None)"
      unfolding exec_move_def by(rule exec_instr, auto)
    moreover have "\<tau>move2 (compP2 P) h [v] (while (c) E) (Suc (length (compE2 c) + length (compE2 E))) None" by(simp add: \<tau>move2_iff)
    ultimately have "\<tau>Exec_movet_a P t (while (c) E) h (stk, loc, Suc (length (compE2 c) + pc), xcp) ([], loc, Suc (Suc (length (compE2 c) + length (compE2 E))), None)"
      by(auto intro: rtranclp_into_tranclp1 \<tau>exec_moveI simp add: compP2_def)
    moreover from bisim1 bisim2 have "bsok c n" "bsok E n" by(auto dest: bisim1_bsok)
    hence "P, while (c) E, n, h \<turnstile> (while (c) E, xs) \<leftrightarrow> ([], xs, (Suc (Suc (length (compE2 c) + length (compE2 E)))), None)"
      unfolding s by(auto intro: bisim1While6)
    moreover have "\<tau>move1 P h (e;; while (c) E)" by(auto intro: \<tau>move1SeqRed)
    ultimately show ?thesis using s by(auto)(blast intro: tranclp_into_rtranclp)
  next
    case (Seq1Throw a)
    note [simp] = `e = Throw a` `ta = \<epsilon>` `e' = Throw a` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h (e;; while (c) E)" by(auto intro: \<tau>move1SeqThrow)
    from bisim2 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim2 bisim1_bsok[OF bisim1]
      have "P, while (c) E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (length (compE2 c) + pc), xcp)"
	by(auto intro: bisim1WhileThrow2)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim2 obtain pc'
	where "\<tau>Exec_mover_a P t E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (while (c) E) h (stk, loc, Suc (length (compE2 c) + pc), None) ([Addr a], loc, Suc (length (compE2 c) + pc'), \<lfloor>a\<rfloor>)"
	by-(rule While_\<tau>ExecrI2)
      moreover from bisim' bisim1_bsok[OF bisim1]
      have "P, while (c) E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, Suc (length (compE2 c) + pc'), \<lfloor>a\<rfloor>)"
	by-(rule bisim1WhileThrow2, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed
next
  case (bisim1While6 c n e xs)
  note bisim1 = `\<And>xs. P,c,n,h \<turnstile> (c, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `P,t \<turnstile>1 \<langle>while (c) e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>` show ?case
  proof cases
    case Red1While
    note [simp] = `ta = \<epsilon>` `e' = if (c) (e;; while (c) e) else unit` `h' = h` `xs' = xs`
    have "\<tau>move1 P h (while (c) e)" by(rule \<tau>move1WhileRed)
    moreover from bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2]
    have "P,while (c) e,n,h \<turnstile> (if (c) (e;; while (c) e) else unit, xs) \<leftrightarrow> ([], xs, 0, None)"
      by(rule bisim1_bisims1.bisim1While3[OF bisim1_refl])
    moreover have "\<tau>Exec_movet_a P t (while (c) e) h ([], xs, Suc (Suc (length (compE2 c) + length (compE2 e))), None) ([], xs, 0, None)"
      by(rule \<tau>Exect1step)(auto simp add: exec_move_def \<tau>move2_iff intro: exec_instr)
    ultimately show ?thesis by(fastsimp)
  qed
next
  case bisim1While7 thus ?case by fastsimp
next
  case bisim1WhileThrow1 thus ?case by auto
next
  case bisim1WhileThrow2 thus ?case by auto
next
  case (bisim1Throw1 E n e xs stk loc pc xcp)
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note red = `P,t \<turnstile>1 \<langle>throw e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from red show ?case
  proof cases
    case (Throw1Red E')
    note [simp] = `e' = throw E'`
      and red = `P,t \<turnstile>1 \<langle>e, (h, xs)\<rangle> -ta\<rightarrow> \<langle>E', (h', xs')\<rangle>`
    from red have "\<tau>move1 P h (throw e) = \<tau>move1 P h e" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover have "call1 (throw e) = call1 e" by auto
    moreover from IH[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,E,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta E e E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim
    have "P,throw E,n,h' \<turnstile> (throw E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1Throw1)
    moreover { 
      assume "no_call2 E pc"
      hence "no_call2 (throw E) pc" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: Throw_\<tau>ExecrI Throw_\<tau>ExectI exec_move_ThrowI)+
  next
    case Red1ThrowNull
    note [simp] = `e = null` `ta = \<epsilon>` `e' = THROW NullPointer` `h' = h` `xs' = xs`
    from bisim have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([Null], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (throw E) h (stk, loc, pc, xcp) ([Null], loc, length (compE2 E), None)"
      by-(rule Throw_\<tau>ExecrI)
    also have "\<tau>Exec_movet_a P t (throw E) h ([Null], loc, length (compE2 E), None) ([Null], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule \<tau>Exect1step)(auto intro: exec_instr \<tau>move2_\<tau>moves2.intros simp add: exec_move_def)
    also from bisim have "bsok E n" by(auto dest: bisim1_bsok)
    hence "P, throw E, n, h \<turnstile> (THROW NullPointer, xs) \<leftrightarrow> ([Null], loc, length (compE2 E), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      unfolding s by(rule bisim1ThrowNull)
    moreover have "\<tau>move1 P h (throw e)" by(auto intro: \<tau>move1ThrowNull)
    ultimately show ?thesis by auto
  next
    case (Throw1Throw a)
    note [simp] = `e = Throw a` `ta = \<epsilon>` `e' = Throw a` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h (throw (Throw a))" by(rule \<tau>move1ThrowThrow)
    from bisim have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume "xcp = \<lfloor>a\<rfloor>"
      with bisim show ?thesis using \<tau> by(fastsimp intro: bisim1ThrowThrow)
    next
      assume [simp]: "xcp = None"
      from bisim obtain pc'
	where "\<tau>Exec_mover_a P t E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim: "P, E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and s: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (throw E) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by -(rule Throw_\<tau>ExecrI)
      moreover from bisim have "P, throw E, n, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by(rule bisim1ThrowThrow)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed
next
  case bisim1Throw2 thus ?case by auto
next
  case bisim1ThrowNull thus ?case by auto
next
  case bisim1ThrowThrow thus ?case by auto
next
  case (bisim1Try E V e xs stk loc pc xcp e2 C')
  note IH = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                 ?exec ta E e e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,E,V,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note red = `P,t \<turnstile>1 \<langle>try e catch(C' V) e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from red show ?case
  proof cases
    case (Try1Red E')
    note [simp] = `e' = try E' catch(C' V) e2`
      and red = `P,t \<turnstile>1 \<langle>e, (h, xs)\<rangle> -ta\<rightarrow> \<langle>E', (h', xs')\<rangle>`
    from red have "\<tau>move1 P h (try e catch(C' V) e2) = \<tau>move1 P h e" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover have "call1 (try e catch(C' V) e2) = call1 e" by auto
    moreover from IH[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,E,V,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta E e E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim `bsok e2 (Suc V)`
    have "P,try E catch(C' V) e2,V,h' \<turnstile> (try E' catch(C' V) e2, xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisim1Try)
    moreover { 
      assume "no_call2 E pc"
      hence "no_call2 (try E catch(C' V) e2) pc" by(auto simp add: no_call2_def) }
    ultimately show ?thesis using redo
      by(auto simp del: call1_calls1.simps split: split_if_asm split del: split_if)(blast intro: Try_\<tau>ExecrI1 Try_\<tau>ExectI1 exec_move_TryI1)+
  next
    case (Red1Try v)
    note [simp] = `e = Val v` `ta = \<epsilon>` `e' = Val v` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h (try Val v catch(C' V) e2)" by(rule \<tau>move1TryRed)
    from bisim1 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      and B: "bsok E V" by(auto dest: bisim1Val2D1 bisim1_bsok)
    hence "\<tau>Exec_mover_a P t (try E catch(C' V) e2) h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      by-(rule Try_\<tau>ExecrI1)
    also have "\<tau>Exec_mover_a P t (try E catch(C' V) e2) h ([v], loc, length (compE2 E), None) ([v], loc, length (compE2 (try E catch(C' V) e2)), None)"
      by(rule \<tau>Execr1step)(auto intro: exec_instr simp add: exec_move_def \<tau>move2_iff)
    also (rtranclp_trans) from B bisim1_bsok[OF bisim2]
    have "P, try E catch(C' V) e2, V, h \<turnstile> (Val v, xs) \<leftrightarrow> ([v], xs, length (compE2 (try E catch(C' V) e2)), None)"
      by -(rule bisim1Val2, auto)
    ultimately show ?thesis using s \<tau> by(auto)
  next
    case (Red1TryCatch a D)
    hence [simp]: "e = Throw a" "ta = \<epsilon>" "e' = {V:Class C'=None; e2}" "h' = h" "xs' = xs[V := Addr a]"
      and ha: "typeof_addr h a = \<lfloor>Class D\<rfloor>" and sub: "P \<turnstile> D \<preceq>\<^sup>* C'"
      and V: "V < length xs" by auto
    from bisim1 have [simp]: "xs = loc" and xcp: "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" 
      and B: "bsok E V" by(auto dest: bisim1_ThrowD bisim1_bsok)
    from xcp have "\<tau>Exec_mover_a P t (try E catch(C' V) e2) h (stk, loc, pc, xcp) ([Addr a], loc, Suc (length (compE2 E)), None)"
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim1 have "match_ex_table (compP2 P) (cname_of h a) pc (compxE2 E 0 0) = None"
	by(auto dest: bisim1_xcp_Some_not_caught[where pc'=0] simp add: compP2_def)
      moreover from bisim1 have "pc < length (compE2 E)"
	by(auto dest: bisim1_ThrowD)
      ultimately show ?thesis using ha sub unfolding `xcp = \<lfloor>a\<rfloor>`
	by-(rule \<tau>Execr1step[unfolded exec_move_def, OF exec_catch[where d=0, simplified]],
            auto simp add: \<tau>move2_iff matches_ex_entry_def compP2_def match_ex_table_append_not_pcs cname_of_def)
    next
      assume [simp]: "xcp = None"
      with bisim1 obtain pc' where "\<tau>Exec_mover_a P t E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and s: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (try E catch(C' V) e2) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule Try_\<tau>ExecrI1)
      also from bisim' have "match_ex_table (compP2 P) (cname_of h a) pc' (compxE2 E 0 0) = None"
	by(auto dest: bisim1_xcp_Some_not_caught[where pc'=0] simp add: compP2_def)
      with ha sub bisim1_ThrowD[OF bisim']
      have "\<tau>Exec_mover_a P t (try E catch(C' V) e2) h ([Addr a], loc, pc', \<lfloor>a\<rfloor>) ([Addr a], loc, Suc (length (compE2 E)), None)"
	by-(rule \<tau>Execr1step[unfolded exec_move_def, OF exec_catch[where d=0, simplified]], auto simp add: \<tau>move2_iff matches_ex_entry_def compP2_def match_ex_table_append_not_pcs cname_of_def)
      finally (rtranclp_trans) show ?thesis by simp
    qed
    also let ?pc' = "Suc (length (compE2 E))" from V
    have exec: "\<tau>Exec_movet_a P t (try E catch(C' V) e2) h ([Addr a], loc, ?pc', None) ([], loc[V := Addr a], Suc ?pc', None)"
      by-(rule \<tau>Exect1step[unfolded exec_move_def, OF exec_instr], auto simp add: nth_append intro: \<tau>move2_\<tau>moves2.intros)
    also (rtranclp_tranclp_tranclp) from bisim1_bsok[OF bisim2] B
    have bisim': "P,try E catch(C' V) e2, V, h \<turnstile> ({V:Class C'=None; e2}, xs[V := Addr a]) \<leftrightarrow> ([], loc[V := Addr a], Suc ?pc', None)"
      unfolding `xs = loc` by-(rule bisim1TryCatch2[OF bisim1_refl, simplified], auto)
    moreover have "\<tau>move1 P h (try Throw a catch(C' V) e2)" by(rule \<tau>move1TryThrow)
    ultimately show ?thesis by(auto)(blast intro: tranclp_into_rtranclp)
  next
    case (Red1TryFail a D)
    hence [simp]: "e = Throw a" "ta = \<epsilon>" "e' = Throw a" "h' = h" "xs' = xs"
      and ha: "typeof_addr h a = \<lfloor>Class D\<rfloor>" and sub: "\<not> P \<turnstile> D \<preceq>\<^sup>* C'" by auto
    have \<tau>: "\<tau>move1 P h (try Throw a catch(C' V) e2)" by(rule \<tau>move1TryThrow)
    from bisim1 have [simp]:  "xs = loc" and "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    from bisim1 have pc: "pc \<le> length (compE2 E)" by(rule bisim1_pc_length_compE2)
    from `xcp = \<lfloor>a\<rfloor> \<or> xcp = None` show ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim1 ha sub bisim1_bsok[OF bisim2]
      have "P,try E catch(C' V) e2,V,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1TryFail)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim1 obtain pc' 
	where "\<tau>Exec_mover_a P t E h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, E, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (try E catch(C' V) e2) h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by-(rule Try_\<tau>ExecrI1)
      moreover from bisim' ha sub bisim1_bsok[OF bisim2]
      have "P,try E catch(C' V) e2,V,h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	by(auto intro: bisim1TryFail)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed
next
  case (bisim1TryCatch1 e V a xs stk loc pc D C' e2)
  note bisim1 = `P,e,V,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note IH2 = `\<And>xs e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e2,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,Suc V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta e2 e2 e' h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note ha = `typeof_addr h a = \<lfloor>Class D\<rfloor>`
  note sub = `P \<turnstile> D \<preceq>\<^sup>* C'`
  note red = `P,t \<turnstile>1 \<langle>{V:Class C'=None; e2},(h, xs[V := Addr a])\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from bisim1 have [simp]: "xs = loc" by(auto dest: bisim1_ThrowD)
  from red show ?case
  proof cases
    case (Block1Red E')
    note [simp] = `e' = {V:Class C'=None; E'}`
      and red = `P,t \<turnstile>1 \<langle>e2, (h, xs[V := Addr a])\<rangle> -ta\<rightarrow> \<langle>E', (h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h {V:Class C'=None; e2} = \<tau>move1 P h e2" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    have exec: "\<tau>Exec_mover_a P t (try e catch(C' V) e2) h ([Addr a], xs, Suc (length (compE2 e) + 0), None) ([], xs[V := Addr a], Suc (Suc (length (compE2 e) + 0)), None)"
      by -(rule \<tau>Execr1step, auto simp add: exec_move_def \<tau>move2_iff intro: exec_instr)
    moreover from IH2[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e2,Suc V,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e2 e2 E' h [] (xs[V := Addr a]) 0 None h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (try e catch(C' V) e2) {V:Class C'=None; e2} {V:Class C'=None; E'} h [] (xs[V := Addr a]) (Suc (Suc (length (compE2 e))))  None h' (Suc (Suc (length (compE2 e) + pc''))) stk'' loc'' xcp''"
    proof(cases "\<tau>move1 P h {V:Class C'=None; e2}")
      case True with \<tau> exec' show ?thesis
	by(fastsimp dest: Try_\<tau>ExecrI2 Try_\<tau>ExectI2 simp del: compE2_compEs2.simps)
    next
      case False
      with \<tau> exec' obtain pc' stk' loc' xcp'
	where e: "\<tau>Exec_mover_a P t e2 h ([], xs[V := Addr a], 0, None) (stk', loc', pc', xcp')"
	and e': "exec_move_a P t e2 h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 (compP2 P) h stk' e2 pc' xcp'" 
        and call: "call1 e2 = None \<or> no_call2 e2 0 \<or> pc' = 0 \<and> stk' = [] \<and> loc' = xs[V := Addr a] \<and> xcp' = None" by auto
      from e have "\<tau>Exec_mover_a P t (try e catch(C' V) e2) h ([], xs[V := Addr a], Suc (Suc (length (compE2 e) + 0)), None) (stk', loc', Suc (Suc (length (compE2 e) + pc')), xcp')"
	by(rule Try_\<tau>ExecrI2)
      moreover from e'
      have "exec_move_a P t (try e catch(C' V) e2) h (stk', loc', Suc (Suc (length (compE2 e) + pc')), xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', Suc (Suc (length (compE2 e) + pc'')), xcp'')"
	by(rule exec_move_TryI2)
      moreover from \<tau>' have "\<tau>move2 (compP2 P) h stk' (try e catch(C' V) e2) (Suc (Suc (length (compE2 e) + pc'))) xcp' \<Longrightarrow> False"
	by(simp add: \<tau>move2_iff)
      moreover have "call1 {V:Class C'=None; e2} = call1 e2" by simp
      moreover have "no_call2 e2 0 \<Longrightarrow> no_call2 (try e catch(C' V) e2) (Suc (Suc (length (compE2 e))))"
        by(auto simp add: no_call2_def)
      ultimately show ?thesis using False call by(auto simp del: split_paired_Ex call1_calls1.simps) blast
    qed
    moreover from bisim' bisim1_bsok[OF bisim1]
    have "P, try e catch(C' V) e2, V, h' \<turnstile> ({V:Class C'=None; E'}, xs') \<leftrightarrow> (stk'', loc'', Suc (Suc (length (compE2 e) + pc'')), xcp'')"
      by-(rule bisim1TryCatch2, auto)
    moreover have "no_call2 (try e catch(C' V) e2) (Suc (length (compE2 e)))" by(simp add: no_call2_def)
    ultimately show ?thesis using \<tau> 
      by auto(blast intro: rtranclp_trans rtranclp_tranclp_tranclp)+
  next
    case (Red1Block u)
    note [simp] = `e2 = Val u` `ta = \<epsilon>` `e' = Val u` `h' = h` `xs' = xs[V := Addr a]`
    have "\<tau>Exec_mover_a P t (try e catch(C' V) Val u) h ([Addr a], xs, Suc (length (compE2 e) + 0), None) ([], xs[V := Addr a], Suc (Suc (length (compE2 e) + 0)), None)"
      by -(rule \<tau>Execr1step, auto simp add: exec_move_def \<tau>move2_iff intro: exec_instr)
    also have "\<tau>Exec_mover_a P t (try e catch(C' V) Val u) h ([], xs[V := Addr a], Suc (Suc (length (compE2 e) + 0)), None) ([u], xs[V := Addr a], Suc (Suc (length (compE2 e) + 1)), None)"
      by -(rule Try_\<tau>ExecrI2[OF \<tau>Execr1step[unfolded exec_move_def, OF exec_instr]], auto simp add: \<tau>move2_iff)
    also (rtranclp_trans) from bisim1_bsok[OF bisim1]
    have "P, try e catch(C' V) Val u, V, h \<turnstile> (Val u, xs[V := Addr a]) \<leftrightarrow> ([u], xs[V := Addr a], length (compE2 (try e catch(C' V) Val u)), None)"
      by-(rule bisim1Val2, auto)
    moreover have "\<tau>move1 P h {V:Class C'=None; Val u}" by(rule \<tau>move1BlockRed)
    ultimately show ?thesis by(auto)
  next
    case (Block1Throw a')
    note [simp] = `e2 = Throw a'` `h' = h` `ta = \<epsilon>` `e' = Throw a'` `xs' = xs[V := Addr a]`
    have "\<tau>move1 P h {V:Class C'=None; Throw a'}" by(rule \<tau>move1BlockThrow)
    moreover have "\<tau>Exec_mover_a P t (try e catch(C' V) e2) h ([Addr a], loc, Suc (length (compE2 e)), None)
                                 ([Addr a'], xs', Suc (Suc (Suc (length (compE2 e)))), \<lfloor>a'\<rfloor>)"
      by(rule \<tau>Execr3step)(auto simp add: exec_move_def exec_meth_instr \<tau>move2_iff)
    moreover have "P, try e catch(C' V) Throw a', V, h \<turnstile> (Throw a', xs') \<leftrightarrow> ([Addr a'], xs', Suc (Suc (length (compE2 e) + length (compE2 (addr a')))), \<lfloor>a'\<rfloor>)"
      by(rule bisim1TryCatchThrow)(rule bisim1Throw2, simp_all add: `bsok e V`)
    ultimately show ?thesis by auto
  qed
next
  case (bisim1TryCatch2 e2 V e2' xs stk loc pc xcp e C')
  note bisim2 = `P,e2,Suc V,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim1 = `\<And>xs. P,e,V,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  note IH2 = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e2',(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,e2,Suc V,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta e2 e2' e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note red = `P,t \<turnstile>1 \<langle>{V:Class C'=None; e2'},(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>`
  from red show ?case
  proof cases
    case (Block1Red E')
    note [simp] = `e' = {V:Class C'=None; E'}`
      and red = `P,t \<turnstile>1 \<langle>e2', (h, xs)\<rangle> -ta\<rightarrow> \<langle>E', (h', xs')\<rangle>`
    from red have \<tau>: "\<tau>move1 P h {V:Class C'=None; e2'} = \<tau>move1 P h e2'" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from IH2[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,e2,Suc V,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and exec': "?exec ta e2 e2' E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have "?exec ta (try e catch(C' V) e2) {V:Class C'=None; e2'} {V:Class C'=None; E'} h stk loc (Suc (Suc (length (compE2 e) + pc))) xcp h' (Suc (Suc (length (compE2 e) + pc''))) stk'' loc'' xcp''"
    proof (cases "\<tau>move1 P h {V:Class C'=None; e2'}")
      case True with \<tau> exec' show ?thesis by(auto intro: Try_\<tau>ExecrI2 Try_\<tau>ExectI2)
    next
      case False
      with \<tau> exec' obtain pc' stk' loc' xcp'
	where e: "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
	and e': "exec_move_a P t e2 h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>move2 (compP2 P) h stk' e2 pc' xcp'" 
        and call: "call1 e2' = None \<or> no_call2 e2 pc \<or> pc' = pc \<and> stk' = stk \<and> loc' = loc \<and> xcp' = xcp" by auto
      from e have "\<tau>Exec_mover_a P t (try e catch(C' V) e2) h (stk, loc, Suc (Suc (length (compE2 e) + pc)), xcp) (stk', loc', Suc (Suc (length (compE2 e) + pc')), xcp')"
	by(rule Try_\<tau>ExecrI2)
      moreover from e'
      have "exec_move_a P t (try e catch(C' V) e2) h (stk', loc', Suc (Suc (length (compE2 e) + pc')), xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', Suc (Suc (length (compE2 e) +  pc'')), xcp'')"
	by(rule exec_move_TryI2)
      moreover from \<tau>' have "\<tau>move2 (compP2 P) h stk' (try e catch(C' V) e2) (Suc (Suc (length (compE2 e) + pc'))) xcp' \<Longrightarrow> False"
	by(simp add: \<tau>move2_iff)
      moreover have "call1 {V:Class C'=None; e2'} = call1 e2'" by simp
      moreover have "no_call2 e2 pc \<Longrightarrow> no_call2 (try e catch(C' V) e2) (Suc (Suc (length (compE2 e) + pc)))"
        by(auto simp add: no_call2_def)
      ultimately show ?thesis using False call by(auto simp del: split_paired_Ex call1_calls1.simps)
    qed
    moreover from bisim' bisim1_bsok[OF bisim1]
    have "P, try e catch(C' V) e2, V, h' \<turnstile> ({V:Class C'=None; E'}, xs') \<leftrightarrow> (stk'', loc'', Suc (Suc (length (compE2 e) + pc'')), xcp'')"
      by -(rule bisim1_bisims1.bisim1TryCatch2, auto)
    ultimately show ?thesis using \<tau> by auto blast+
  next
    case (Red1Block u)
    note [simp] = `e2' = Val u` `ta = \<epsilon>` `e' = Val u` `h' = h` `xs' = xs`
    from bisim2 have s: "xcp = None" "xs = loc"
      and "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, xcp) ([u], loc, length (compE2 e2), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_mover_a P t (try e catch(C' V) e2) h (stk, loc, Suc (Suc (length (compE2 e) + pc)), xcp) ([u], loc, Suc (Suc (length (compE2 e) + length (compE2 e2))), None)"
      by -(rule Try_\<tau>ExecrI2)
    moreover from `bsok e V` `bsok e2 (Suc V)`
    have "P, try e catch(C' V) e2, V, h \<turnstile> (Val u, xs) \<leftrightarrow> ([u], xs, length (compE2 (try e catch(C' V) e2)), None)"
      by-(rule bisim1Val2, auto)
    moreover have "\<tau>move1 P h {V:Class C'=None; Val u}" by(rule \<tau>move1BlockRed)
    ultimately show ?thesis using s by auto
  next
    case (Block1Throw a)
    note [simp] = `e2' = Throw a` `ta = \<epsilon>` `e' = Throw a` `h' = h` `xs' = xs`
    have \<tau>: "\<tau>move1 P h {V:Class C'=None; e2'}"  by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    from bisim2 have "xcp = \<lfloor>a\<rfloor> \<or> xcp = None" by(auto dest: bisim1_ThrowD)
    thus ?thesis
    proof
      assume [simp]: "xcp = \<lfloor>a\<rfloor>"
      with bisim2 bisim1_bsok[OF bisim1]
      have "P, try e catch(C' V) e2, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, Suc (Suc (length (compE2 e) + pc)), xcp)"
	by(auto intro: bisim1TryCatchThrow)
      thus ?thesis using \<tau> by(fastsimp)
    next
      assume [simp]: "xcp = None"
      with bisim2 obtain pc' 
	where "\<tau>Exec_mover_a P t e2 h (stk, loc, pc, None) ([Addr a], loc, pc', \<lfloor>a\<rfloor>)"
	and bisim': "P, e2, Suc V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, pc', \<lfloor>a\<rfloor>)" and [simp]: "xs = loc"
	by(auto dest: bisim1_Throw_\<tau>Exec_mover)
      hence "\<tau>Exec_mover_a P t (try e catch(C' V) e2) h (stk, loc, Suc (Suc (length (compE2 e) + pc)), None) ([Addr a], loc, Suc (Suc (length (compE2 e) + pc')), \<lfloor>a\<rfloor>)"
	by-(rule Try_\<tau>ExecrI2)
      moreover from bisim' bisim1_bsok[OF bisim1]
      have "P, try e catch(C' V) e2, V, h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], loc, Suc (Suc (length (compE2 e) + pc')), \<lfloor>a\<rfloor>)"
	by-(rule bisim1TryCatchThrow, auto)
      ultimately show ?thesis using \<tau> by auto
    qed
  qed
next
  case bisim1TryFail thus ?case by auto
next
  case bisim1TryCatchThrow thus ?case by auto
next
  case bisims1Nil thus ?case by(auto elim!: reds1.cases)
next
  case (bisims1List1 E n e xs stk loc pc xcp es)
  note IH1 = `\<And>e' h' xs' Env T Env' T'. P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,E,n,h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'') \<and>
                  ?exec ta E e e' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note IH2 = `\<And>xs es' h' xs' Env Ts Env' Ts'. P,t \<turnstile>1 \<langle>es,(h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,es,n,h' \<turnstile> (es', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'') \<and>
                 ?execs ta es es es' h [] xs 0 None h' pc'' stk'' loc'' xcp''`
  note bisim1 = `P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `\<And>xs. P,es,n,h \<turnstile> (es, xs) [\<leftrightarrow>] ([], xs, 0, None)`
  from `P,t \<turnstile>1 \<langle>e # es,(h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es',(h', xs')\<rangle>` show ?case
  proof cases
    case (List1Red1 E')
    note [simp] = `es' = E' # es`
      and red = `P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -ta\<rightarrow> \<langle>E',(h', xs')\<rangle>`
    from red have \<tau>: "\<tau>moves1 P h (e # es) = \<tau>move1 P h e" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    moreover from IH1[OF red]
    obtain pc'' stk'' loc'' xcp'' where bisim: "P,E,n,h' \<turnstile> (E', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and redo: "?exec ta E e E' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by blast
    from bisim `bsoks es n`
    have "P,E#es,n,h' \<turnstile> (E'#es, xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'')"
      by(rule bisim1_bisims1.bisims1List1)
    moreover { 
      assume "no_call2 E pc"
      hence "no_calls2 (E # es) pc \<or> pc = length (compE2 E)" by(auto simp add: no_call2_def no_calls2_def) }
    moreover from red have "calls1 (e # es) = call1 e" by auto
    ultimately show ?thesis using redo
      apply(auto simp add: exec_move_def exec_moves_def simp del: call1_calls1.simps split: split_if_asm split del: split_if)
      apply(blast intro: \<tau>Exec_mover_\<tau>Exec_movesr \<tau>Exec_movet_\<tau>Exec_movest intro!: bisim1_bisims1.bisims1List1 elim: \<tau>moves2.cases)+
      done
  next
    case (List1Red2 ES' v)
    note [simp] = `es' = Val v # ES'` `e = Val v`
      and red = `P,t \<turnstile>1 \<langle>es,(h, xs)\<rangle> [-ta\<rightarrow>] \<langle>ES',(h', xs')\<rangle>`
    from bisim1 have s: "xs = loc" "xcp = None"
      and exec1: "\<tau>Exec_mover_a P t E h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      by(auto dest: bisim1Val2D1)
    hence "\<tau>Exec_movesr_a P t (E # es) h (stk, loc, pc, xcp) ([v], loc, length (compE2 E), None)"
      by -(rule \<tau>Exec_mover_\<tau>Exec_movesr)
    moreover from IH2[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,es,n,h' \<turnstile> (ES', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'')"
      and exec': "?execs ta es es ES' h [] xs 0 None h' pc'' stk'' loc'' xcp''" by auto
    have \<tau>: "\<tau>moves1 P h (Val v # es) = \<tau>moves1 P h es" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    have "?execs ta (E # es) (Val v # es) (Val v # ES') h [v] xs (length (compE2 E)) None h' (length (compE2 E) +  pc'') (stk'' @ [v]) loc'' xcp''"
    proof(cases "\<tau>moves1 P h (Val v # es)")
      case True with \<tau> exec' show ?thesis
	using append_\<tau>Exec_movesr[of "[v]" "[E]" _ P t es h "[]" xs 0 None stk'' loc'' pc'' xcp'']
	  append_\<tau>Exec_movest[of "[v]" "[E]" _ P t es h "[]" xs 0 None stk'' loc'' pc'' xcp''] by auto 
    next
      case False with \<tau> exec' obtain pc' stk' loc' xcp'
	where e: "\<tau>Exec_movesr_a P t es h ([], xs, 0, None) (stk', loc', pc', xcp')"
	and e': "exec_moves_a P t es h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>moves2 (compP2 P) h stk' es pc' xcp'" 
        and call: "calls1 es = None \<or> no_calls2 es 0 \<or> pc' = 0 \<and> stk' = [] \<and> loc' = xs \<and> xcp' = None" by auto
      from append_\<tau>Exec_movesr[OF _ e, where vs="[v]" and es' = "[E]"]
      have "\<tau>Exec_movesr_a P t (E # es) h ([v], xs, length (compE2 E), None) (stk' @ [v], loc', length (compE2 E) + pc', xcp')" by simp
      moreover from append_exec_moves[OF _ e', of "[v]" "[E]"]
      have "exec_moves_a P t (E # es) h (stk' @ [v], loc', length (compE2 E) + pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'' @ [v], loc'', length (compE2 E) + pc'', xcp'')"
	by simp
      moreover from \<tau>' e'
      have "\<tau>moves2 (compP2 P) h (stk' @ [v]) (E # es) (length (compE2 E) + pc') xcp' \<Longrightarrow> False"
        by(auto simp add: \<tau>moves2_iff \<tau>instr_stk_drop_exec_moves)
      moreover have "calls1 (Val v # es) = calls1 es" by simp
      moreover have "no_calls2 es 0 \<Longrightarrow> no_calls2 (E # es) (length (compE2 E))"
        by(auto simp add: no_calls2_def)
      ultimately show ?thesis using False call by(auto simp del: split_paired_Ex call1_calls1.simps) blast
    qed
    moreover from bisim' bisim1_bsok[OF bisim1]
    have "P,E # es,n,h' \<turnstile> (Val v # ES', xs') [\<leftrightarrow>] (stk'' @ [v], loc'', length (compE2 E) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisims1List2)
    moreover from bisim1 have "pc \<noteq> length (compE2 E) \<longrightarrow> no_calls2 (E # es) pc"
      by(auto simp add: no_calls2_def dest: bisim_Val_pc_not_Invoke bisim1_pc_length_compE2)
    ultimately show ?thesis using \<tau> exec1 s
      apply(auto simp del: split_paired_Ex call1_calls1.simps split: split_if_asm split del: split_if)
      apply(blast intro: \<tau>Exec_movesr_trans|fastsimp elim!: \<tau>Exec_movesr_trans simp del: split_paired_Ex call1_calls1.simps)+
      done
  qed
next
  case (bisims1List2 ES n es xs stk loc pc xcp e v)
  note IH2 = `\<And>es' h' xs' Env Ts Env' Ts'. P,t \<turnstile>1 \<langle>es,(h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es',(h', xs')\<rangle>
             \<Longrightarrow> \<exists>pc'' stk'' loc'' xcp''. P,ES,n,h' \<turnstile> (es', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'') \<and>
                  ?execs ta ES es es' h stk loc pc xcp h' pc'' stk'' loc'' xcp''`
  note bisim1 = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,ES,n,h \<turnstile> (es, xs) [\<leftrightarrow>] (stk, loc, pc, xcp)`
  from `P,t \<turnstile>1 \<langle>Val v # es,(h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es',(h', xs')\<rangle>` show ?case
  proof cases
    case (List1Red2 ES')
    note [simp] = `es' = Val v # ES'`
      and red = `P,t \<turnstile>1 \<langle>es,(h, xs)\<rangle> [-ta\<rightarrow>] \<langle>ES',(h', xs')\<rangle>`
    from IH2[OF red] obtain pc'' stk'' loc'' xcp''
      where bisim': "P,ES,n,h' \<turnstile> (ES', xs') [\<leftrightarrow>] (stk'', loc'', pc'', xcp'')"
      and exec': "?execs ta ES es ES' h stk loc pc xcp h' pc'' stk'' loc'' xcp''" by auto
    have \<tau>: "\<tau>moves1 P h (Val v # es) = \<tau>moves1 P h es" by(auto simp add: \<tau>move1_\<tau>moves1.simps)
    have "?execs ta (e # ES) (Val v # es) (Val v # ES') h (stk @ [v]) loc (length (compE2 e) + pc) xcp h' (length (compE2 e) +  pc'') (stk'' @ [v]) loc'' xcp''"
    proof(cases "\<tau>moves1 P h (Val v # es)")
      case True with \<tau> exec' show ?thesis
	using append_\<tau>Exec_movesr[of "[v]" "[e]" _ P t ES h stk]
	  append_\<tau>Exec_movest[of "[v]" "[e]" _ P t ES h stk] by auto
    next
      case False with \<tau> exec' obtain pc' stk' loc' xcp'
	where e: "\<tau>Exec_movesr_a P t ES h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
	and e': "exec_moves_a P t ES h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'', loc'', pc'', xcp'')"
	and \<tau>': "\<not> \<tau>moves2 (compP2 P) h stk' ES pc' xcp'" 
        and call: "calls1 es = None \<or> no_calls2 ES pc \<or> pc' = pc \<and> stk' = stk \<and> loc' = loc \<and> xcp' = xcp" by auto
      from append_\<tau>Exec_movesr[OF _ e, where vs="[v]" and es' = "[e]"]
      have "\<tau>Exec_movesr_a P t (e # ES) h (stk @ [v], loc, length (compE2 e) + pc, xcp) (stk' @ [v], loc', length (compE2 e) + pc', xcp')" by simp
      moreover from append_exec_moves[OF _ e', of "[v]" "[e]"]
      have "exec_moves_a P t (e # ES) h (stk' @ [v], loc', length (compE2 e) + pc', xcp') (extTA2JVM (compP2 P) ta) h' (stk'' @ [v], loc'', length (compE2 e) + pc'', xcp'')" by simp
      moreover from \<tau>' e'
      have "\<tau>moves2 (compP2 P) h (stk' @ [v]) (e # ES) (length (compE2 e) + pc') xcp' \<Longrightarrow> False"
        by(auto simp add: \<tau>moves2_iff \<tau>instr_stk_drop_exec_moves)
      moreover have "calls1 (Val v # es) = calls1 es" by simp
      moreover have "no_calls2 ES pc \<Longrightarrow> no_calls2 (e # ES) (length (compE2 e) + pc)"
        by(auto simp add: no_calls2_def)
      ultimately show ?thesis using False call by(auto simp del: split_paired_Ex call1_calls1.simps) 
    qed
    moreover from bisim' bisim1_bsok[OF bisim1]
    have "P,e # ES,n,h' \<turnstile> (Val v # ES', xs') [\<leftrightarrow>] (stk'' @ [v], loc'', length (compE2 e) + pc'', xcp'')"
      by(rule bisim1_bisims1.bisims1List2)
    ultimately show ?thesis using \<tau> by auto blast+
  qed auto
qed

end


context J1_JVM_conf_read begin

lemma exec_1_simulates_Red1_\<tau>:
  assumes wf: "wf_J1_prog P"
  and Red1: "P,t \<turnstile>1 \<langle>(e, xs)/exs, h\<rangle> -ta\<rightarrow> \<langle>(e', xs')/exs', h\<rangle>"
  and bisim: "bisim1_list1 t h (e, xs) exs xcp frs"
  and \<tau>: "\<tau>Move1 P h ((e, xs), exs)"
  shows "\<exists>xcp' frs'. (if sim12_size e' < sim12_size e then \<tau>Exec_1_dr else \<tau>Exec_1_dt) (compP2 P) t (xcp, h, frs) (xcp', h, frs') \<and> bisim1_list1 t h (e',xs') exs' xcp' frs'"
proof -
  from wf have wt: "wf_jvm_prog\<^bsub>compTP P\<^esub> (compP2 P)" by(rule wt_compTP_compP2)
  from Red1 show ?thesis
  proof(cases)
    case (red1Red TA)
    note [simp] = `ta = extTA2J1 P TA` `exs' = exs`
      and red = `P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -TA\<rightarrow> \<langle>e',(h, xs')\<rangle>`
    from \<tau> red have \<tau>': "\<tau>move1 P h e" by(auto elim: red1_cases)
    from bisim show ?thesis
    proof(cases)
      case (bl1_Normal stk loc C M pc FRS Ts T body D)
      hence [simp]: "frs = (stk, loc, C, M, pc) # FRS"
	and conf: "compTP P \<turnstile> t: (xcp, h, frs) \<surd>"
	and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = body in D"
	and bisim: "P,blocks1 0 (Class D#Ts) body,0,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	and bisims: "list_all2 (bisim1_fr P h) exs FRS"
	and lenxs: "max_vars e \<le> length xs"
	by auto
      from exec_instr_simulates_red1[OF wf bisim red] \<tau>' obtain pc' stk' loc' xcp'
	where exec: "(if sim12_size e' < sim12_size e then \<tau>Exec_mover_a else \<tau>Exec_movet_a) P t body h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
	and b': "P,blocks1 0 (Class D#Ts) body,0,h \<turnstile> (e', xs') \<leftrightarrow> (stk', loc', pc', xcp')"
	by(auto split: split_if_asm simp del: blocks1.simps)
      from exec sees have "(if sim12_size e' < sim12_size e then \<tau>Exec_1r else \<tau>Exec_1t) (compP2 P) t (xcp, h, frs) (xcp', h, (stk', loc', C, M, pc') # FRS)"
	by(auto intro: \<tau>Exec_mover_\<tau>Exec_1r \<tau>Exec_movet_\<tau>Exec_1t)
      from wt this conf have execd: "(if sim12_size e' < sim12_size e then \<tau>Exec_1_dr else \<tau>Exec_1_dt) (compP2 P) t (xcp, h, frs) (xcp', h, (stk', loc', C, M, pc') # FRS)"
	by(auto intro: \<tau>Exec_1r_\<tau>Exec_1_dr \<tau>Exec_1t_\<tau>Exec_1_dt)
      moreover from wt execd conf
      have "compTP P \<turnstile> t: (xcp', h, (stk', loc', C, M, pc') # FRS) \<surd>"
	by(auto intro: \<tau>Exec_1_dr_preserves_correct_state \<tau>Exec_1_dt_preserves_correct_state split: split_if_asm)
      hence "bisim1_list1 t h (e', xs') exs xcp' ((stk', loc', C, M, pc') # FRS)"
	using sees b' 
      proof
	from red have "max_vars e' \<le> max_vars e" by(rule red1_max_vars)
	with red1_preserves_len[OF red] lenxs
	show "max_vars e' \<le> length xs'" by simp
      qed fact
      hence "bisim1_list1 t h (e',xs') exs' xcp' ((stk', loc', C, M, pc') # FRS)" by simp
      ultimately show ?thesis by blast
    qed(insert red, auto elim: red1_cases)
  next
    case (red1Call a' M' vs' C' Ts' T' body' D')
    hence [simp]: "ta = \<epsilon>"
      and exs' [simp]: "exs' = (e, xs) # exs"
      and e': "e' = blocks1 0 (Class D'#Ts') body'"
      and xs': "xs' = Addr a' # vs' @ replicate (max_vars body') undefined"
      and ha': "typeof_addr h a' = \<lfloor>Class C'\<rfloor>"
      and call: "call1 e = \<lfloor>(a', M', vs')\<rfloor>" by auto
    note sees' = `P \<turnstile> C' sees M': Ts'\<rightarrow>T' = body' in D'`
    note lenvs'Ts' = `length vs' = length Ts'`
    from ha' sees_method_decl_above[OF sees'] 
    have conf: "P,h \<turnstile> Addr a' :\<le> Class D'" by(auto simp add: conf_def)
    note wt = wt_compTP_compP2[OF wf]
    from bisim show ?thesis
    proof(cases)
      case (bl1_Normal stk loc C M pc FRS Ts T body D)
      hence [simp]: "frs = (stk, loc, C, M, pc) # FRS"
        and conf: "compTP P \<turnstile> t: (xcp, h, frs) \<surd>"
        and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = body in D"
        and bisim: "P,blocks1 0 (Class D#Ts) body,0,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
        and bisims: "list_all2 (bisim1_fr P h) exs FRS" 
        and lenxs: "max_vars e \<le> length xs" by auto
      from call bisim have [simp]: "xcp = None" by(cases xcp, auto dest: bisim1_call_xcpNone)
      from bisim have b: "P,blocks1 0 (Class D#Ts) body,0,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, None)" by simp
      from bisim have lenloc: "length xs = length loc" by(rule bisim1_length_xs)
      from sees have sees'': "compP2 P \<turnstile> C sees M:Ts\<rightarrow>T = (max_stack body, max_vars body, compE2 body @ [Return], compxE2 body 0 0) in D"
        unfolding compP2_def compMb2_def Let_def by(rule sees_method_compP)

      from  bisim1_call_\<tau>Exec_move[OF b call, of t] lenxs obtain pc' loc' stk'
        where exec: "\<tau>Exec_mover_a P t body h (stk, loc, pc, None) (rev vs' @ Addr a' # stk', loc', pc', None)"
        and pc': "pc' < length (compE2 body)" and ins: "compE2 body ! pc' = Invoke M' (length vs')"
        and bisim': "P,blocks1 0 (Class D#Ts) body,0,h \<turnstile> (e, xs) \<leftrightarrow> (rev vs' @ Addr a' # stk', loc', pc', None)"
        by(auto simp add: blocks1_max_vars simp del: blocks1.simps)
      let ?f = "(rev vs' @ Addr a' # stk', loc', C, M, pc')"
      from exec sees
      have exec1: "\<tau>Exec_1r (compP2 P) t (None, h, (stk, loc, C, M, pc) # FRS) (None, h, ?f  # FRS)"
        by(rule \<tau>Exec_mover_\<tau>Exec_1r)
      with wt have "\<tau>Exec_1_dr (compP2 P) t (None, h, (stk, loc, C, M, pc) # FRS) (None, h, ?f  # FRS)" using conf
        by(simp)(rule \<tau>Exec_1r_\<tau>Exec_1_dr)
      also with wt have conf': "compTP P \<turnstile> t: (None, h, ?f  # FRS) \<surd>" using conf
        by simp (rule \<tau>Exec_1_dr_preserves_correct_state)
      let ?f' = "([], Addr a' # vs' @ (replicate (max_vars body') undefined), D', M', 0)"
      from pc' ins sees sees' ha'
      have "(\<epsilon>, None, h, ?f' # ?f # FRS) \<in> exec_instr (instrs_of (compP2 P) C M ! pc') (compP2 P) t h (rev vs' @ Addr a' # stk') loc' C M pc' FRS"
        by(auto simp add: compP2_def compMb2_def nth_append split_beta dest: external_call_not_sees_method)
      hence "exec_1 (compP2 P) t (None, h, ?f # FRS) \<epsilon> (None, h, ?f' # ?f # FRS)"
        using exec sees by(simp add: exec_1_iff)
      with conf' have execd: "compP2 P,t \<turnstile> Normal (None, h, ?f # FRS) -\<epsilon>-jvmd\<rightarrow> Normal (None, h, ?f' # ?f # FRS)"
        by(simp add: welltyped_commute[OF wt])
      hence check: "check (compP2 P) (None, h, ?f # FRS)" by(rule jvmd_NormalE)
      have "\<tau>move2 (compP2 P) h (rev vs' @ Addr a' # stk') body pc' None" using pc' ins ha' sees'
        by(auto simp add: \<tau>move2_iff compP2_def dest: external_call_not_sees_method)
      with sees pc' ins have "\<tau>Move2 (compP2 P) (None, h, (rev vs' @ Addr a' # stk', loc', C, M, pc') # FRS)"
        unfolding \<tau>Move2_compP2[OF sees] by(auto simp add: compP2_def compMb2_def)
      with `exec_1 (compP2 P) t (None, h, ?f # FRS) \<epsilon> (None, h, ?f' # ?f # FRS)` check
      have "\<tau>Exec_1_dt (compP2 P) t (None, h, ?f # FRS) (None, h, ?f' # ?f # FRS)" by fastsimp
      also from execd sees'' sees' ins ha' pc' have "compP2 P,h \<turnstile> vs' [:\<le>] Ts'" 
        by(auto simp add: check_def compP2_def split: split_if_asm dest: external_call_not_sees_method elim!: jvmd_NormalE)
      hence lenvs: "length vs' = length Ts'" by(rule list_all2_lengthD)
      from wt execd conf' have "compTP P \<turnstile> t:(None, h, ?f' # ?f # FRS) \<surd>"
        by(rule BV_correct_d_1)
      hence "bisim1_list1 t h (blocks1 0 (Class D'#Ts') body', xs') ((e, xs) # exs) None (?f' # ?f # FRS)"
      proof
        from sees' show "P \<turnstile> D' sees M': Ts'\<rightarrow>T' = body' in D'" by(rule sees_method_idemp)
        from sees_wf_mdecl[OF wf sees'] have "bsok body' (Suc 0 + length Ts')"
	  by(auto simp add: wf_mdecl_def bsok_def intro: WT1_expr_locks)
        hence "bsok (blocks1 0 (Class D'#Ts') body') 0" by(auto simp add: bsok_def)
        thus "P,blocks1 0 (Class D'#Ts') body',0,h \<turnstile> (blocks1 0 (Class D'#Ts') body', xs') \<leftrightarrow>
             ([], Addr a' # vs' @ replicate (max_vars body') undefined, 0, None)"
	  unfolding xs' by(rule bisim1_refl)
        show "max_vars (blocks1 0 (Class D' # Ts') body') \<le> length xs'"
	  unfolding xs' using lenvs by(simp add: blocks1_max_vars)
        from lenxs have "(max_vars e) \<le> length xs" by simp
        with sees bisim' call have "bisim1_fr P h (e, xs) (rev vs' @ Addr a' # stk', loc', C, M, pc')"
	  by(rule bisim1_fr.intros)
        thus "list_all2 (bisim1_fr P h) ((e, xs) # exs)
                        ((rev vs' @ Addr a' # stk', loc', C, M, pc') # FRS)"
	  using bisims by simp
      qed
      moreover have "ta_bisim wbisim1 ta \<epsilon>" by simp
      ultimately show ?thesis
        unfolding `frs = (stk, loc, C, M, pc) # FRS` `xcp = None` e' exs'
        by auto(blast intro: tranclp_into_rtranclp)
    next
      case bl1_finalVal 
      with call show ?thesis by simp
    next
      case bl1_finalThrow
      with call show ?thesis by simp
    qed
  next
    case (red1Return E)
    note [simp] = `exs = (E, xs') # exs'` `ta = \<epsilon>` `e' = inline_call e E`
    note wt = wt_compTP_compP2[OF wf]
    from bisim have bisim: "bisim1_list1 t h (e, xs) ((E, xs') # exs') xcp frs" by simp
    thus ?thesis
    proof cases
      case (bl1_Normal stk loc C M pc FRS Ts T body D)
      hence [simp]: "frs = (stk, loc, C, M, pc) # FRS"
	and conf: "compTP P \<turnstile> t: (xcp, h, frs) \<surd>"
	and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = body in D"
	and bisim: "P,blocks1 0 (Class D#Ts) body,0,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
	and bisims: "list_all2 (bisim1_fr P h) ((E, xs') # exs') FRS" 
	and lenxs: "max_vars e \<le> length xs" by auto
      from bisims obtain f FRS' where [simp]: "FRS = f # FRS'" by(fastsimp simp add: list_all2_Cons1)
      from bisims have "bisim1_fr P h (E, xs') f" by simp
      then obtain C0 M0 Ts0 T0 body0 D0 stk0 loc0 pc0 a' M' vs'
	where [simp]: "f = (stk0, loc0, C0, M0, pc0)"
	and sees0: "P \<turnstile> C0 sees M0:Ts0\<rightarrow>T0=body0 in D0"
	and bisim0: "P,blocks1 0 (Class D0#Ts0) body0,0,h \<turnstile> (E, xs') \<leftrightarrow> (stk0, loc0, pc0, None)"
	and lenxs0: "max_vars E \<le> length xs'"
	and call0: "call1 E = \<lfloor>(a', M', vs')\<rfloor>"
        by cases(auto, fastsimp)
      
      let ?ee = "inline_call e E"
	
      from bisim0 call0 have pc0: "pc0 < length (compE2 (blocks1 0 (Class D0#Ts0) body0))"
        by(rule bisim1_call_pcD)
      hence pc0: "pc0 < length (compE2 body0)" by simp
      with sees_method_compP[OF sees0, where f="\<lambda>C M Ts T. compMb2"]
        sees_method_compP[OF sees, where f="\<lambda>C M Ts T. compMb2"] conf
      obtain ST LT where \<Phi>: "compTP P C0 M0 ! pc0 = \<lfloor>(ST, LT)\<rfloor>"
	and conff: "conf_f (compP (\<lambda>C M Ts T. compMb2) P) h (ST, LT) (compE2 body0 @ [Return]) (stk0, loc0, C0, M0, pc0)"
 	and ins: "(compE2 body0 @ [Return]) ! pc0 = Invoke M (length Ts)"
	by(simp add: correct_state_def)(fastsimp simp add: compP2_def compMb2_def dest: sees_method_fun)
      from bisim1_callD[OF bisim0 call0, of M "length Ts"] ins pc0
      have [simp]: "M' = M" by simp
	
      from `final e` show ?thesis
      proof(cases)
	fix v
	assume [simp]: "e = Val v"
	with bisim have [simp]: "xcp = None" by(auto dest: bisim_Val_loc_eq_xcp_None)
	  
	from bisim1Val2D1[OF bisim[unfolded `xcp = None` `e = Val v`]]
	have "\<tau>Exec_mover_a P t body h (stk, loc, pc, None) ([v], loc, length (compE2 body), None)"
	  and [simp]: "xs = loc" by(auto simp del: blocks1.simps)
	with sees have "\<tau>Exec_1r (compP2 P) t (None, h, (stk, loc, C, M, pc) # FRS) (None, h, ([v], loc, C, M, length (compE2 body)) # FRS)"
	  by-(rule \<tau>Exec_mover_\<tau>Exec_1r)
	with conf wt have "\<tau>Exec_1_dr (compP2 P) t (None, h, (stk, loc, C, M, pc) # FRS) (None, h, ([v], loc, C, M, length (compE2 body)) # FRS)"
	  by(simp)(rule \<tau>Exec_1r_\<tau>Exec_1_dr)
	moreover with conf wt have conf': "compTP P \<turnstile> t:(None, h, ([v], loc, C, M, length (compE2 body)) # FRS) \<surd>"
	  by(simp)(rule \<tau>Exec_1_dr_preserves_correct_state)
	from sees sees0
	have exec: "exec_1 (compP2 P) t (None, h, ([v], loc, C, M, length (compE2 body)) # FRS) \<epsilon> (None, h, (v # drop (Suc (length Ts)) stk0, loc0, C0, M0, Suc pc0) # FRS')"
	  by(simp add: exec_1_iff compP2_def compMb2_def)
	moreover with conf' wt have "compP2 P,t \<turnstile> Normal (None, h, ([v], loc, C, M, length (compE2 body)) # FRS) -\<epsilon>-jvmd\<rightarrow> Normal (None, h, (v # drop (Suc (length Ts)) stk0, loc0, C0, M0, Suc pc0) # FRS')"
	  by(simp add: welltyped_commute)
	hence "check (compP2 P) (None, h, ([v], loc, C, M, length (compE2 body)) # FRS)"
          by(rule jvmd_NormalE)
	moreover have "\<tau>Move2 (compP2 P) (None, h, ([v], loc, C, M, length (compE2 body)) # FRS)"
	  unfolding \<tau>Move2_compP2[OF sees] by(auto)
	ultimately have "\<tau>Exec_1_dt (compP2 P) t (None, h, (stk, loc, C, M, pc) # FRS) (None, h, (v # drop (Suc (length Ts)) stk0, loc0, C0, M0, Suc pc0) # FRS')"
	  by -(erule rtranclp_into_tranclp1,rule \<tau>exec_1_dI)
	moreover from wt conf' exec
	have "compTP P \<turnstile> t:(None, h, (v # drop (Suc (length Ts)) stk0, loc0, C0, M0, Suc pc0) # FRS') \<surd>"
	  by(rule BV_correct_1)
	hence "bisim1_list1 t h (?ee, xs') exs' None ((v # drop (Suc (length Ts)) stk0, loc0, C0, M0, Suc pc0) # FRS')"
	  using sees0
	proof
	  from bisim1_inline_call_Val[OF bisim0 call0, of "length Ts" v] ins pc0
	  show "P,blocks1 0 (Class D0#Ts0) body0,0,h \<turnstile> (?ee, xs') \<leftrightarrow> (v # drop (Suc (length Ts)) stk0, loc0, Suc pc0, None)"
	    by simp
	  from lenxs0 max_vars_inline_call[of e "E"]
	  show "max_vars (inline_call e E) \<le> length xs'" by simp
	  from bisims show "list_all2 (bisim1_fr P h) exs' FRS'" by simp
	qed
	ultimately show ?thesis
	  by -(rule exI conjI|assumption|simp)+
      next
	fix ad
	assume [simp]: "e = Throw ad"
	
	have "\<exists>stk' pc'. \<tau>Exec_mover_a P t body h (stk, loc, pc, xcp) (stk', loc, pc', \<lfloor>ad\<rfloor>) \<and>
                         P,blocks1 0 (Class D#Ts) body,0,h \<turnstile> (Throw ad, loc) \<leftrightarrow> (stk', loc, pc', \<lfloor>ad\<rfloor>)"
	proof(cases xcp)
	  case None[simp]
	  from bisim1_Throw_\<tau>Exec_mover[OF bisim[unfolded None `e = Throw ad`]] obtain pc'
	    where exec: "\<tau>Exec_mover_a P t body h (stk, loc, pc, None) ([Addr ad], loc, pc', \<lfloor>ad\<rfloor>)"
	    and bisim': "P,blocks1 0 (Class D#Ts) body,0,h \<turnstile> (Throw ad, xs) \<leftrightarrow> ([Addr ad], loc, pc', \<lfloor>ad\<rfloor>)"
	    and [simp]: "xs = loc" by(auto simp del: blocks1.simps)
	  thus ?thesis by fastsimp
	next
	  case (Some a')
	  with bisim have "a' = ad" "xs = loc" by(auto dest: bisim1_ThrowD)
	  thus ?thesis using bisim Some by(auto)
	qed
	then obtain stk' pc' where exec: "\<tau>Exec_mover_a P t body h (stk, loc, pc, xcp) (stk', loc, pc', \<lfloor>ad\<rfloor>)"
	  and bisim': "P,blocks1 0 (Class D#Ts) body,0,h \<turnstile> (Throw ad, loc) \<leftrightarrow> (stk', loc, pc', \<lfloor>ad\<rfloor>)" by blast
	with sees have "\<tau>Exec_1r (compP2 P) t (xcp, h, (stk, loc, C, M, pc) # FRS) (\<lfloor>ad\<rfloor>, h, (stk', loc, C, M, pc') # FRS)"
	  by-(rule \<tau>Exec_mover_\<tau>Exec_1r)
	with conf wt have "\<tau>Exec_1_dr (compP2 P) t (xcp, h, (stk, loc, C, M, pc) # FRS) (\<lfloor>ad\<rfloor>, h, (stk', loc, C, M, pc') # FRS)"
	  by(simp)(rule \<tau>Exec_1r_\<tau>Exec_1_dr)
	moreover with conf wt have conf': "compTP P \<turnstile> t: (\<lfloor>ad\<rfloor>, h, (stk', loc, C, M, pc') # FRS) \<surd>"
	  by(simp)(rule \<tau>Exec_1_dr_preserves_correct_state)
	from bisim1_xcp_Some_not_caught[OF bisim', of "\<lambda>C M Ts T. compMb2" 0 0] sees
	have match: "match_ex_table (compP2 P) (cname_of h ad) pc' (ex_table_of (compP2 P) C M) = None"
	  by(simp add: compP2_def compMb2_def)
	hence exec: "exec_1 (compP2 P) t (\<lfloor>ad\<rfloor>, h, (stk', loc, C, M, pc') # FRS) \<epsilon> (\<lfloor>ad\<rfloor>, h, FRS)" by(simp add: exec_1_iff)
	moreover
	with conf' wt have "compP2 P,t \<turnstile> Normal (\<lfloor>ad\<rfloor>, h, (stk', loc, C, M, pc') # FRS) -\<epsilon>-jvmd\<rightarrow> Normal (\<lfloor>ad\<rfloor>, h, FRS)"
	  by(simp add: welltyped_commute)
	hence "check (compP2 P) (\<lfloor>ad\<rfloor>, h, (stk', loc, C, M, pc') # FRS)" by(rule jvmd_NormalE)
	moreover from bisim' have "\<tau>Move2 (compP2 P) (\<lfloor>ad\<rfloor>, h, (stk', loc, C, M, pc') # FRS)"
	  unfolding \<tau>Move2_compP2[OF sees] by(auto dest: bisim1_pc_length_compE2)
	ultimately have "\<tau>Exec_1_dt (compP2 P) t (xcp, h, (stk, loc, C, M, pc) # FRS) (\<lfloor>ad\<rfloor>, h, FRS)"
	  by -(erule rtranclp_into_tranclp1,rule \<tau>exec_1_dI)
	moreover from wt conf' exec
	have "compTP P \<turnstile> t: (\<lfloor>ad\<rfloor>, h, (stk0, loc0, C0, M0, pc0) # FRS') \<surd>"
	  by(simp)(rule BV_correct_1)
	hence "bisim1_list1 t h (?ee, xs') exs' \<lfloor>ad\<rfloor> ((stk0, loc0, C0, M0, pc0) # FRS')"
	  using sees0
	proof
	  from bisim1_inline_call_Throw[OF bisim0 call0] ins pc0
	  show "P,blocks1 0 (Class D0#Ts0) body0,0,h \<turnstile> (?ee, xs') \<leftrightarrow> (stk0, loc0, pc0, \<lfloor>ad\<rfloor>)" by simp
	  from lenxs0 max_vars_inline_call[of e E]
	  show "max_vars ?ee \<le> length xs'" by simp
	  from bisims Cons show "list_all2 (bisim1_fr P h) exs' FRS'" by simp
	qed
	moreover from call0 have "sim12_size (inline_call (Throw ad) E) > 0" by(cases E) simp_all
	ultimately show ?thesis
	  by -(rule exI conjI|assumption|simp)+
      qed
    qed
  qed
qed

lemma exec_1_simulates_Red1_not_\<tau>:
  assumes wf: "wf_J1_prog P"
  and Red1: "P,t \<turnstile>1 \<langle>(e, xs)/exs, h\<rangle> -ta\<rightarrow> \<langle>(e', xs')/exs', h'\<rangle>"
  and bisim: "bisim1_list1 t h (e, xs) exs xcp frs"
  and \<tau>: "\<not> \<tau>Move1 P h ((e, xs), exs)"
  shows "\<exists>xcp' frs'. \<tau>Exec_1_dr (compP2 P) t (xcp, h, frs) (xcp', h, frs') \<and>
           (\<exists>ta' xcp'' frs''. exec_1_d (compP2 P) t (Normal (xcp', h, frs')) ta' (Normal (xcp'', h', frs'')) \<and>
                          \<not> \<tau>Move2 (compP2 P) (xcp', h, frs') \<and> ta_bisim wbisim1 ta ta' \<and>
                  bisim1_list1 t h' (e',xs') exs' xcp'' frs'') \<and>
           (call1 e = None \<or>
            (case frs of Nil \<Rightarrow> False | (stk, loc, C, M, pc) # FRS \<Rightarrow> \<forall>M' n. instrs_of (compP2 P) C M ! pc \<noteq> Invoke M' n) \<or>
            xcp'= xcp \<and> frs' = frs)"
using Red1
proof(cases)
  case (red1Red TA)
  hence [simp]: "ta = extTA2J1 P TA" "exs' = exs"
    and red: "P,t \<turnstile>1 \<langle>e,(h, xs)\<rangle> -TA\<rightarrow> \<langle>e',(h', xs')\<rangle>" by simp_all
  from red have hext: "hext h h'" by(auto dest: red1_hext_incr)
  from \<tau> have \<tau>': "\<not> \<tau>move1 P h e" by(auto intro: \<tau>move1Block)
  note wt = wt_compTP_compP2[OF wf] 
  from bisim show ?thesis
  proof(cases)
    case (bl1_Normal stk loc C M pc FRS Ts T body D)
    hence [simp]: "frs = (stk, loc, C, M, pc) # FRS"
      and conf: "compTP P \<turnstile> t: (xcp, h, frs) \<surd>"
      and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = body in D"
      and bisim: "P,blocks1 0 (Class D#Ts) body,0,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
      and bisims: "list_all2 (bisim1_fr P h) exs FRS" 
      and lenxs: "max_vars e \<le> length xs" by auto

    from exec_instr_simulates_red1[OF wf bisim red] \<tau>'
    obtain pc' stk' loc' xcp' pc'' stk'' loc'' xcp''
      where exec1: "\<tau>Exec_mover_a P t body h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
      and exec2: "exec_move_a P t body h (stk', loc', pc', xcp') (extTA2JVM (compP2 P) TA) h' (stk'', loc'', pc'', xcp'')"
      and \<tau>2: "\<not> \<tau>move2 (compP2 P) h stk' body pc' xcp'"
      and b': "P,blocks1 0 (Class D#Ts) body,0, h' \<turnstile> (e', xs') \<leftrightarrow> (stk'', loc'', pc'', xcp'')"
      and call: "call1 e = None \<or> no_call2 (blocks1 0 (Class D # Ts) body) pc \<or> pc' = pc \<and> stk' = stk \<and> loc' = loc \<and> xcp' = xcp"
      by(fastsimp simp add: exec_move_def simp del: blocks1.simps)
    from exec2 have pc'body: "pc' < length (compE2 body)" by(auto)
    from exec1 sees have exec1': "\<tau>Exec_1r (compP2 P) t (xcp, h, frs) (xcp', h, (stk', loc', C, M, pc') # FRS)"
      by(auto intro: \<tau>Exec_mover_\<tau>Exec_1r)
    with wt have execd: "\<tau>Exec_1_dr (compP2 P) t (xcp, h, frs) (xcp', h, (stk', loc', C, M, pc') # FRS)"
      using conf by(rule \<tau>Exec_1r_\<tau>Exec_1_dr)
    moreover { fix a
      assume [simp]: "xcp' = \<lfloor>a\<rfloor>"
      from exec2 sees_method_compP[OF sees, of "\<lambda>C M Ts T. compMb2"] pc'body
      have "match_ex_table (compP2 P) (cname_of h a) pc' (ex_table_of (compP2 P) C M) \<noteq> None"
	by(auto simp add: exec_move_def compP2_def compMb2_def elim!: exec_meth.cases) }
    note xt = this
    with \<tau>2 sees pc'body have \<tau>2': "\<not> \<tau>Move2 (compP2 P) (xcp', h, (stk', loc', C, M, pc') # FRS)"
      unfolding \<tau>Move2_compP2[OF sees] by(auto simp add: compP2_def compMb2_def \<tau>move2_iff)
    moreover from exec2 sees
    have exec2': "exec_1 (compP2 P) t (xcp', h, (stk', loc', C, M, pc') # FRS) (extTA2JVM (compP2 P) TA) (xcp'', h', (stk'', loc'', C, M, pc'') # FRS)"
      by(rule exec_move_exec_1)
    from wt execd conf have conf': "compTP P \<turnstile> t: (xcp', h, (stk', loc', C, M, pc') # FRS) \<surd>"
      by(rule \<tau>Exec_1_dr_preserves_correct_state)
    with exec2' wt
    have "exec_1_d (compP2 P) t (Normal (xcp', h, (stk', loc', C, M, pc') # FRS)) (extTA2JVM (compP2 P) TA) (Normal (xcp'', h', (stk'', loc'', C, M, pc'') # FRS))"
      by(simp add: welltyped_commute)
    moreover
    from \<tau>2 sees pc'body xt have \<tau>2': "\<not> \<tau>Move2 (compP2 P) (xcp', h, (stk', loc', C, M, pc') # FRS)"
      unfolding \<tau>Move2_compP2[OF sees] by(auto simp add: compP2_def compMb2_def \<tau>move2_iff)
    moreover from wt conf' exec2'
    have conf'': "compTP P \<turnstile> t: (xcp'', h', (stk'', loc'', C, M, pc'') # FRS) \<surd>" by(rule BV_correct_1)
    hence "bisim1_list1 t h' (e', xs') exs xcp'' ((stk'', loc'', C, M, pc'') # FRS)" using sees b'
    proof
      from red1_preserves_len[OF red] red1_max_vars[OF red] lenxs
      show "max_vars e' \<le> length xs'" by simp

      from bisims show "list_all2 (bisim1_fr P h') exs FRS"
	by(rule list_all2_mono)(rule bisim1_fr_hext_mono[OF _ hext])
    qed
    moreover from conf'' have "hconf h'" "preallocated h'" by(auto simp add: correct_state_def)
    with wf red
    have "ta_bisim wbisim1 ta (extTA2JVM (compP2 P) TA)"
      by(auto intro: ta_bisim_red_extTA2J1_extTA2JVM)
    moreover from call sees_method_compP[OF sees, of "\<lambda>C M Ts T. compMb2"]
    have "call1 e = None \<or> (case frs of [] \<Rightarrow> False | (stk, loc, C, M, pc) # FRS \<Rightarrow> \<forall>M' n. instrs_of (compP2 P) C M ! pc \<noteq> Invoke M' n) \<or> xcp' = xcp \<and> (stk', loc', C, M, pc') # FRS = frs"
      by(auto simp add: no_call2_def compP2_def compMb2_def)
    ultimately show ?thesis by -(rule exI conjI|assumption|simp)+
  next
    case bl1_finalVal
    with red show ?thesis by auto
  next
    case bl1_finalThrow
    with red show ?thesis by(auto elim: red1_cases)
  qed
next
  case red1Call
  with \<tau> have False by(auto simp add: synthesized_call_def dest: \<tau>move1_not_call1[where P=P and h=h])
  thus ?thesis ..
next
  case red1Return
  with \<tau> have False by auto
  thus ?thesis ..
qed

end

end