(*  Title:      JinjaThreads/J/SmallProgress.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

header {* \isaheader{Progress of Small Step Semantics} *}
theory Progress
imports
  WellTypeRT
  DefAss
  SmallStep
  "../Common/ExternalCallWF"
  WWellForm
begin

lemma (in J_heap_base) final_addrE [consumes 3, case_names addr Throw]:
  "\<lbrakk> P,E,h \<turnstile> e : T; is_class_type_of T U; final e;
    \<And>a. e = addr a \<Longrightarrow> R;
    \<And>a. e = Throw a \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
apply(auto elim!: final.cases)
apply(case_tac v)
apply auto
done

lemma (in J_heap) finalRefE [consumes 3, case_names null Class Array Throw]:
 "\<lbrakk> P,E,h \<turnstile> e : T; is_refT T; final e;
   e = null \<Longrightarrow> R;
   \<And>a C. \<lbrakk> e = addr a; T = Class C \<rbrakk> \<Longrightarrow> R;
   \<And>a U. \<lbrakk> e = addr a; T = U\<lfloor>\<rceil> \<rbrakk> \<Longrightarrow> R;
   \<And>a. e = Throw a \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
apply(auto simp:final_iff)
apply(case_tac v)
apply(auto elim!: is_refT.cases dest: typeof_addr_eq_Some_conv)
done

theorem (in J_progress) red_progress:
  assumes wf: "wwf_J_prog P" and hconf: "hconf h"
  shows progress: "\<lbrakk> P,E,h \<turnstile> e : T; \<D> e \<lfloor>dom l\<rfloor>; \<not> final e \<rbrakk> \<Longrightarrow> \<exists>e' s' ta. extTA,P,t \<turnstile> \<langle>e,(h,l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>"
  and progresss: "\<lbrakk> P,E,h \<turnstile> es [:] Ts; \<D>s es \<lfloor>dom l\<rfloor>; \<not> finals es \<rbrakk> \<Longrightarrow> \<exists>es' s' ta. extTA,P,t \<turnstile> \<langle>es,(h,l)\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>"
proof (induct arbitrary: l and l rule:WTrt_WTrts.inducts)
  case (WTrtNew C)
  obtain h' ao where h': "new_obj h C = (h', ao)" by(cases "new_obj h C")
  thus ?case using WTrtNew
    by(cases ao)(fastforce intro: RedNewFail RedNew)+
next
  case (WTrtNewArray E e T l)
  have IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h,l)\<rangle> -tas\<rightarrow> \<langle>e', s'\<rangle>"
   and D: "\<D> (newA T\<lfloor>e\<rceil>) \<lfloor>dom l\<rfloor>"
   and ei: "P,E,h \<turnstile> e : Integer" by fact+
  from D have De: "\<D> e \<lfloor>dom l\<rfloor>" by auto
  show ?case
  proof cases 
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v
      assume e [simp]: "e = Val v"
      with ei have "typeof\<^bsub>h\<^esub> v = Some Integer" by fastforce
      hence exei: "\<exists>i. v = Intg i" by fastforce
      then obtain i where v: "v = Intg i" by blast
      thus ?thesis
      proof (cases "0 <=s i")
	case True
        obtain h' ao where "new_arr h T (nat (sint i)) = (h', ao)"
          by(cases "new_arr h T (nat (sint i))")
	thus ?thesis using True `v = Intg i` WTrtNewArray.prems
          by(cases ao)(auto simp del: split_paired_Ex,(blast intro: RedNewArrayFail RedNewArray)+)
      next
	assume "\<not> 0 <=s i"
	hence "i <s 0" by simp
	then have "extTA,P,t \<turnstile> \<langle>newA T\<lfloor>Val(Intg i)\<rceil>,(h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NegativeArraySize,(h, l)\<rangle>"
	  by - (rule RedNewArrayNegative, auto)
	with e v show ?thesis by blast
      qed
    next
      fix exa
      assume e: "e = Throw exa"
      then have "extTA,P,t \<turnstile> \<langle>newA T\<lfloor>Throw exa\<rceil>,(h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw exa,(h, l)\<rangle>"
	by - (rule NewArrayThrow)
      with e show ?thesis by blast
    qed
  next
    assume "\<not> final e"
    with IH De have exes: "\<exists>e' s' ta. extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by simp
    then obtain e' s' ta where "extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by blast
    hence "extTA,P,t \<turnstile> \<langle>newA T\<lfloor>e\<rceil>,(h, l)\<rangle> -ta\<rightarrow> \<langle>newA T\<lfloor>e'\<rceil>,s'\<rangle>" by - (rule NewArrayRed)
    thus ?thesis by blast
  qed
next
  case (WTrtCast E e T U l)
  have wte: "P,E,h \<turnstile> e : T"
   and IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and D: "\<D> (Cast U e) \<lfloor>dom l\<rfloor>" by fact+
  from D have De: "\<D> e \<lfloor>dom l\<rfloor>" by auto
  show ?case
  proof (cases "final e")
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v
      assume ev: "e = Val v"
      with WTrtCast obtain V where thvU: "typeof\<^bsub>h\<^esub> v = \<lfloor>V\<rfloor>" by fastforce
      thus ?thesis
      proof (cases "P \<turnstile> V \<le> U")
	assume "P \<turnstile> V \<le> U"
	with thvU have "extTA,P,t \<turnstile> \<langle>Cast U (Val v),(h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>Val v,(h,l)\<rangle>"
	  by - (rule RedCast, auto)
	with ev show ?thesis by blast
      next
	assume "\<not> P \<turnstile> V \<le> U"
	with thvU have "extTA,P,t \<turnstile> \<langle>Cast U (Val v),(h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW ClassCast,(h,l)\<rangle>"
	  by - (rule RedCastFail, auto)
	with ev show ?thesis by blast
      qed
    next
      fix a
      assume "e = Throw a"
      thus ?thesis by(blast intro!:CastThrow)
    qed
  next
    assume nf: "\<not> final e"
    from IH[OF De nf] show ?thesis by (blast intro:CastRed)
  qed
next
  case (WTrtInstanceOf E e T U l)
  have wte: "P,E,h \<turnstile> e : T"
   and IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and D: "\<D> (e instanceof U) \<lfloor>dom l\<rfloor>" by fact+
  from D have De: "\<D> e \<lfloor>dom l\<rfloor>" by auto
  show ?case
  proof (cases "final e")
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v
      assume ev: "e = Val v"
      with WTrtInstanceOf obtain V where thvU: "typeof\<^bsub>h\<^esub> v = \<lfloor>V\<rfloor>" by fastforce
      hence "extTA,P,t \<turnstile> \<langle>(Val v) instanceof U,(h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>Val (Bool (v \<noteq> Null \<and> P \<turnstile> V \<le> U)),(h,l)\<rangle>"
        by -(rule RedInstanceOf, auto)
      with ev show ?thesis by blast
    next
      fix a
      assume "e = Throw a"
      thus ?thesis by(blast intro!:InstanceOfThrow)
    qed
  next
    assume nf: "\<not> final e"
    from IH[OF De nf] show ?thesis by (blast intro:InstanceOfRed)
  qed
next
  case WTrtVal thus ?case by(simp add:final_iff)
next
  case WTrtVar thus ?case by(fastforce intro:RedVar simp:hyper_isin_def)
next
  case (WTrtBinOp E e1 T1 e2 T2 bop T)
  show ?case
  proof cases
    assume "final e1"
    thus ?thesis
    proof (rule finalE)
      fix v1 assume [simp]: "e1 = Val v1"
      show ?thesis
      proof cases
	assume "final e2"
	thus ?thesis
	proof (rule finalE)
	  fix v2 assume [simp]: "e2 = Val v2"
	  with WTrtBinOp have type: "typeof\<^bsub>h\<^esub> v1 = \<lfloor>T1\<rfloor>" "typeof\<^bsub>h\<^esub> v2 = \<lfloor>T2\<rfloor>" by auto
	  from binop_progress[OF this `P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T`] obtain va
	    where "binop bop v1 v2 = \<lfloor>va\<rfloor>" by blast
	  thus ?thesis by(cases va)(fastforce intro: RedBinOp RedBinOpFail)+
	next
	  fix a assume "e2 = Throw a"
	  thus ?thesis by(fastforce intro:BinOpThrow2)
	qed
      next
	assume "\<not> final e2" with WTrtBinOp show ?thesis
	  by simp (fast intro!:BinOpRed2)
      qed
    next
      fix a assume "e1 = Throw a"
      thus ?thesis by simp (fast intro:BinOpThrow1)
    qed
  next
    assume "\<not> final e1" with WTrtBinOp show ?thesis
      by simp (fast intro:BinOpRed1)
  qed
next
  case (WTrtLAss E V T e T')
  show ?case
  proof cases
    assume "final e" with WTrtLAss show ?thesis
      by(fastforce simp:final_iff intro!:RedLAss LAssThrow)
  next
    assume "\<not> final e" with WTrtLAss show ?thesis
      by simp (fast intro:LAssRed)
  qed
next
  case (WTrtAAcc E a T i l)
  have wte: "P,E,h \<turnstile> a : T\<lfloor>\<rceil>"
   and wtei: "P,E,h \<turnstile> i : Integer"
   and IHa: "\<And>l. \<lbrakk>\<D> a \<lfloor>dom l\<rfloor>; \<not> final a\<rbrakk>
                 \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>a,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and IHi: "\<And>l. \<lbrakk>\<D> i \<lfloor>dom l\<rfloor>; \<not> final i\<rbrakk>
                 \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>i,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and D: "\<D> (a\<lfloor>i\<rceil>) \<lfloor>dom l\<rfloor>" by fact+
  have ref: "is_refT (T\<lfloor>\<rceil>)" by simp
  from D have Da: "\<D> a \<lfloor>dom l\<rfloor>" by simp
  show ?case
  proof (cases "final a")
    assume "final a"
    with wte ref show ?case
    proof (cases rule: finalRefE)
      case null
      thus ?thesis
      proof (cases "final i")
	assume "final i"
	thus ?thesis
	proof (rule finalE)
	  fix v
	  assume i: "i = Val v"
	  have "extTA,P,t \<turnstile> \<langle>null\<lfloor>Val v\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, (h,l)\<rangle>"
	    by(rule RedAAccNull)
	  with i null show ?thesis by blast
	next
	  fix ex
	  assume i: "i = Throw ex"
	  have "extTA,P,t \<turnstile> \<langle>null\<lfloor>Throw ex\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw ex, (h,l)\<rangle>"
	    by(rule AAccThrow2)
	  with i null show ?thesis by blast
	qed
      next
	assume "\<not> final i"
	from WTrtAAcc null show ?thesis
	  by simp
      qed
    next
      case (Array ad U)
      with wte have ty: "typeof_addr h ad = \<lfloor>Array U\<rfloor>" by auto
      thus ?thesis
      proof (cases "final i")
	assume "final i"
	thus ?thesis
	proof(rule finalE)
	  fix v
	  assume [simp]: "i = Val v"
	  with wtei have "typeof\<^bsub>h\<^esub> v = Some Integer" by fastforce
	  hence "\<exists>i. v = Intg i" by fastforce
	  then obtain i where [simp]: "v = Intg i" by blast
	  thus ?thesis
	  proof (cases "i <s 0 \<or> sint i \<ge> int (array_length h ad)")
            case True
	    with WTrtAAcc Array show ?thesis by (fastforce intro: RedAAccBounds)
          next
            case False
            hence "nat (sint i) < array_length h ad"
              by(metis int_le_0_conv linorder_not_less nat_int.Rep_inverse' sint_0 transfer_int_nat_numerals(1) word_sless_alt zless_nat_conj)
            with ty have "P,h \<turnstile> ad@ACell (nat (sint i)) : U" by(auto intro!: addr_loc_type.intros)
            from heap_read_total[OF hconf this]
            obtain v where "heap_read h ad (ACell (nat (sint i))) v" by blast
            with False Array ty show ?thesis by(fastforce intro: RedAAcc)
          qed
	next
	  fix ex
	  assume "i = Throw ex"
	  with WTrtAAcc Array show ?thesis by (fastforce intro: AAccThrow2)
	qed
      next
	assume "\<not> final i"
	with WTrtAAcc Array show ?thesis by (fastforce intro: AAccRed2)
      qed
    next
      fix ex
      assume "a = Throw ex"
      with WTrtAAcc show ?thesis by (fastforce intro: AAccThrow1)
    qed simp
  next
    assume "\<not> final a"
    with WTrtAAcc show ?thesis by (fastforce intro: AAccRed1)
  qed
next
  case (WTrtAAccNT E a i T l)
  have wte: "P,E,h \<turnstile> a : NT"
   and wtei: "P,E,h \<turnstile> i : Integer"
   and IHa: "\<And>l. \<lbrakk>\<D> a \<lfloor>dom l\<rfloor>; \<not> final a\<rbrakk>
                 \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>a,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and IHi: "\<And>l. \<lbrakk>\<D> i \<lfloor>dom l\<rfloor>; \<not> final i\<rbrakk>
                 \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>i,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact+
  have ref: "is_refT NT" by simp
  with WTrtAAccNT have Da: "\<D> a \<lfloor>dom l\<rfloor>" by simp
  thus ?case
  proof (cases "final a")
    case True
    with wte ref show ?thesis
    proof (cases rule: finalRefE)
      case null
      thus ?thesis
      proof (cases "final i")
	assume "final i"
	thus ?thesis
	proof (rule finalE)
	  fix v
	  assume i: "i = Val v"
	  have "extTA,P,t \<turnstile> \<langle>null\<lfloor>Val v\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, (h,l)\<rangle>"
	    by (rule RedAAccNull)
	  with WTrtAAccNT `final a` null `final i` i show ?thesis by blast
	next
	  fix ex
	  assume i: "i = Throw ex"
	  have "extTA,P,t \<turnstile> \<langle>null\<lfloor>Throw ex\<rceil>, (h, l)\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw ex, (h,l)\<rangle>"
	    by(rule AAccThrow2)
	  with WTrtAAccNT `final a` null `final i` i show ?thesis by blast
	qed
      next
	assume "\<not> final i"
	with WTrtAAccNT null show ?thesis
	  by(fastforce intro: AAccRed2)
      qed
    next
      case Throw thus ?thesis by (fastforce intro: AAccThrow1)
    qed simp_all
  next
    case False
    with WTrtAAccNT Da show ?thesis by (fastforce intro:AAccRed1)
  qed
next
  case (WTrtAAss E a T i e T' l)
  have wta: "P,E,h \<turnstile> a : T\<lfloor>\<rceil>"
    and wti: "P,E,h \<turnstile> i : Integer"
    and wte: "P,E,h \<turnstile> e : T'"
    and D: "\<D> (a\<lfloor>i\<rceil> := e) \<lfloor>dom l\<rfloor>"
    and IH1: "\<And>l. \<lbrakk>\<D> a \<lfloor>dom l\<rfloor>; \<not> final a\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>a,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
    and IH2: "\<And>l. \<lbrakk>\<D> i \<lfloor>dom l\<rfloor>; \<not> final i\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>i,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
    and IH3: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact+
  have ref: "is_refT (T\<lfloor>\<rceil>)" by simp
  show ?case
  proof (cases "final a")
    assume fa: "final a"
    with wta ref show ?thesis
    proof(cases rule: finalRefE)
      case null
      show ?thesis
      proof(cases "final i")
	assume "final i"
	thus ?thesis
	proof (rule finalE)
	  fix v
	  assume i: "i = Val v"
	  with wti have "typeof\<^bsub>h\<^esub> v = Some Integer" by fastforce
	  then obtain idx where "v = Intg idx" by fastforce
	  thus ?thesis
	  proof (cases "final e")
	    assume "final e"
	    thus ?thesis
	    proof (rule finalE)
	      fix w
	      assume "e = Val w"
	      with WTrtAAss null show ?thesis by (fastforce intro: RedAAssNull)
	    next
	      fix ex
	      assume "e = Throw ex"
	      with WTrtAAss null show ?thesis by (fastforce intro: AAssThrow3)
	    qed
	  next
	    assume "\<not> final e"
	    with WTrtAAss null show ?thesis by (fastforce intro: AAssRed3)
	  qed
	next
	  fix ex
	  assume "i = Throw ex"
	  with WTrtAAss null show ?thesis by (fastforce intro: AAssThrow2)
	qed
      next
	assume "\<not> final i"
	with WTrtAAss null show ?thesis by (fastforce intro: AAssRed2)
      qed
    next
      case (Array ad U)
      with wta have ty: "typeof_addr h ad = \<lfloor>Array U\<rfloor>" by auto
      thus ?thesis
      proof (cases "final i")
	assume fi: "final i"
	thus ?thesis
	proof (rule finalE)
	  fix v
	  assume ivalv: "i = Val v"
	  with wti have "typeof\<^bsub>h\<^esub> v = Some Integer" by fastforce
	  then obtain idx where vidx: "v = Intg idx" by fastforce
	  thus ?thesis
	  proof (cases "final e")
	    assume fe: "final e"
	    thus ?thesis
	    proof(rule finalE)
	      fix w
	      assume evalw: "e = Val w"
	      show ?thesis
              proof(cases "idx <s 0 \<or> sint idx \<ge> int (array_length h ad)")
                case True
                with ty evalw Array ivalv vidx show ?thesis by(fastforce intro: RedAAssBounds)
              next
                case False
                hence "nat (sint idx) < array_length h ad"
                  by(metis int_le_0_conv linorder_not_less nat_int.Rep_inverse' sint_0 transfer_int_nat_numerals(1) word_sless_alt zless_nat_conj)
                with ty have adal: "P,h \<turnstile> ad@ACell (nat (sint idx)) : U"
                  by(auto intro!: addr_loc_type.intros)
                show ?thesis
                proof(cases "P \<turnstile> T' \<le> U")
                  case True
                  with wte evalw have "P,h \<turnstile> w :\<le> U"
                    by(auto simp add: conf_def)
                  from heap_write_total[OF hconf adal this]
                  obtain h' where h': "heap_write h ad (ACell (nat (sint idx))) w h'" ..
                  with ty False vidx ivalv evalw Array wte True
                  show ?thesis by(fastforce intro: RedAAss)
                next
                  case False
                  with ty vidx ivalv evalw Array wte `\<not> (idx <s 0 \<or> sint idx \<ge> int (array_length h ad))`
                  show ?thesis by(fastforce intro: RedAAssStore)
                qed
              qed
	    next
	      fix ex
	      assume "e = Throw ex"
	      with Array ivalv show ?thesis by (fastforce intro: AAssThrow3)
	    qed
	  next
	    assume "\<not> final e"
	    with WTrtAAss Array fi ivalv vidx show ?thesis by (fastforce intro: AAssRed3)
	  qed
	next
	  fix ex
	  assume "i = Throw ex"
	  with WTrtAAss Array show ?thesis by (fastforce intro: AAssThrow2)
	qed
      next
	assume "\<not> final i"
	with WTrtAAss Array show ?thesis by (fastforce intro: AAssRed2)
      qed
    next
      fix ex
      assume "a = Throw ex"
      with WTrtAAss show ?thesis by (fastforce intro:AAssThrow1)
    qed simp_all
  next
    assume "\<not> final a"
    with WTrtAAss show ?thesis by (fastforce intro: AAssRed1)
  qed
next
  case (WTrtAAssNT E a i e T' l)
  have wta: "P,E,h \<turnstile> a : NT"
    and wti: "P,E,h \<turnstile> i : Integer"
    and wte: "P,E,h \<turnstile> e : T'"
    and D: "\<D> (a\<lfloor>i\<rceil> := e) \<lfloor>dom l\<rfloor>"
    and IH1: "\<And>l. \<lbrakk>\<D> a \<lfloor>dom l\<rfloor>; \<not> final a\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>a,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
    and IH2: "\<And>l. \<lbrakk>\<D> i \<lfloor>dom l\<rfloor>; \<not> final i\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>i,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
    and IH3: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact+
  have ref: "is_refT NT" by simp
  show ?case
  proof (cases "final a")
    assume fa: "final a"
    show ?case
    proof (cases "final i")
      assume fi: "final i"
      show ?case
      proof (cases "final e")
	assume fe: "final e"
	with WTrtAAssNT fa fi show ?thesis
	  by (fastforce simp:final_iff intro: RedAAssNull AAssThrow1 AAssThrow2 AAssThrow3)
      next
	assume "\<not> final e"
	with WTrtAAssNT fa fi show ?thesis
          by (fastforce simp: final_iff intro!:AAssRed3 AAssThrow1 AAssThrow2)
      qed
    next
      assume "\<not> final i"
      with WTrtAAssNT fa show ?thesis
        by (fastforce simp: final_iff intro!:AAssRed2 AAssThrow1)
    qed
  next
    assume "\<not> final a"
    with WTrtAAssNT show ?thesis by (fastforce simp: final_iff intro!:AAssRed1)
  qed
next
  case (WTrtALength E a T l)
  show ?case
  proof(cases "final a")
    case True
    note wta = `P,E,h \<turnstile> a : T\<lfloor>\<rceil>`
    thus ?thesis 
    proof(rule finalRefE[OF _ _ True])
      show "is_refT (T\<lfloor>\<rceil>)" by simp
    next
      assume "a = null"
      thus ?thesis by(fastforce intro: RedALengthNull)
    next
      fix ad U
      assume "a = addr ad" and "T\<lfloor>\<rceil> = U\<lfloor>\<rceil>"
      with wta show ?thesis by(fastforce intro: RedALength)
    next
      fix ad
      assume "a = Throw ad"
      thus ?thesis by (fastforce intro: ALengthThrow)
    qed simp
  next
    case False
    from `\<D> (a\<bullet>length) \<lfloor>dom l\<rfloor>` have "\<D> a \<lfloor>dom l\<rfloor>" by simp
    with False `\<lbrakk>\<D> a \<lfloor>dom l\<rfloor>; \<not> final a\<rbrakk> \<Longrightarrow> \<exists>e' s' ta. extTA,P,t \<turnstile> \<langle>a,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
    obtain e' s' ta where "extTA,P,t \<turnstile> \<langle>a,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by blast
    thus ?thesis by(blast intro: ALengthRed)
  qed
next
  case (WTrtALengthNT E a T l)
  show ?case
  proof(cases "final a")
    case True
    note wta = `P,E,h \<turnstile> a : NT`
    thus ?thesis
    proof(rule finalRefE[OF _ _ True])
      show "is_refT NT" by simp
    next
      assume "a = null"
      thus ?thesis by(blast intro: RedALengthNull)
    next
      fix ad
      assume "a = Throw ad"
      thus ?thesis by(blast intro: ALengthThrow)
    qed simp_all
  next
    case False
    from `\<D> (a\<bullet>length) \<lfloor>dom l\<rfloor>` have "\<D> a \<lfloor>dom l\<rfloor>" by simp
    with False `\<lbrakk>\<D> a \<lfloor>dom l\<rfloor>; \<not> final a\<rbrakk> \<Longrightarrow> \<exists>e' s' ta. extTA,P,t \<turnstile> \<langle>a,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
    obtain e' s' ta where "extTA,P,t \<turnstile> \<langle>a,(h, l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>" by blast
    thus ?thesis by(blast intro: ALengthRed)
  qed
next
  case (WTrtFAcc E e U C F T fm D l)
  have wte: "P,E,h \<turnstile> e : U"
    and icto: "is_class_type_of U C"
   and field: "P \<turnstile> C has F:T (fm) in D" by fact+
  show ?case
  proof cases
    assume "final e"
    with wte icto show ?thesis
    proof (cases rule: final_addrE)
      case (addr a)
      with wte have ty: "typeof_addr h a = \<lfloor>U\<rfloor>" by auto
      with icto field have "P,h \<turnstile> a@CField D F : T" by(auto intro: addr_loc_type.intros)
      from heap_read_total[OF hconf this]
      obtain v where "heap_read h a (CField D F) v" by blast
      with addr ty show ?thesis by(fastforce intro: RedFAcc)
    next
      fix a assume "e = Throw a"
      thus ?thesis by(fastforce intro:FAccThrow)
    qed
  next
    assume "\<not> final e" with WTrtFAcc show ?thesis
      by(fastforce intro!:FAccRed)
  qed
next
  case (WTrtFAccNT E e F D T l)
  show ?case
  proof cases
    assume "final e"  --"@{term e} is @{term null} or @{term throw}"
    with WTrtFAccNT show ?thesis
      by(fastforce simp:final_iff intro: RedFAccNull FAccThrow)
  next
    assume "\<not> final e" --"@{term e} reduces by IH"
    with WTrtFAccNT show ?thesis by simp (fast intro:FAccRed)
  qed
next
  case (WTrtFAss E e1 U C F T fm D e2 T2 l)
  have wte1: "P,E,h \<turnstile> e1 : U"
    and icto: "is_class_type_of U C"
    and field: "P \<turnstile> C has F:T (fm) in D" by fact+
  show ?case
  proof cases
    assume "final e1"
    with wte1 icto show ?thesis
    proof (rule final_addrE)
      fix a assume e1: "e1 = addr a"
      show ?thesis
      proof cases
	assume "final e2"
	thus ?thesis
	proof (rule finalE)
	  fix v assume e2: "e2 = Val v"
          from wte1 field icto e1 have adal: "P,h \<turnstile> a@CField D F : T"
            by(auto intro: addr_loc_type.intros)
          from e2 `P \<turnstile> T2 \<le> T` `P,E,h \<turnstile> e2 : T2`
          have "P,h \<turnstile> v :\<le> T" by(auto simp add: conf_def)
          from heap_write_total[OF hconf adal this] obtain h' 
            where "heap_write h a (CField D F) v h'" ..
          with wte1 field e1 e2 show ?thesis
	    by(fastforce intro: RedFAss)
        next
	  fix a assume "e2 = Throw a"
	  thus ?thesis using e1 by(fastforce intro:FAssThrow2)
	qed
      next
	assume "\<not> final e2" with WTrtFAss `final e1` e1 show ?thesis
	  by simp (fast intro!:FAssRed2)
      qed
    next
      fix a assume "e1 = Throw a"
      thus ?thesis by(fastforce intro:FAssThrow1)
    qed
  next
    assume "\<not> final e1" with WTrtFAss show ?thesis
      by(simp del: split_paired_Ex)(blast intro!:FAssRed1)
  qed
next
  case (WTrtFAssNT E e\<^isub>1 e\<^isub>2 T\<^isub>2 F D l)
  show ?case
  proof cases
    assume "final e\<^isub>1"  --"@{term e\<^isub>1} is @{term null} or @{term throw}"
    show ?thesis
    proof cases
      assume "final e\<^isub>2"  --"@{term e\<^isub>2} is @{term Val} or @{term throw}"
      with WTrtFAssNT `final e\<^isub>1` show ?thesis
	by(fastforce simp:final_iff intro: RedFAssNull FAssThrow1 FAssThrow2)
    next
      assume "\<not> final e\<^isub>2" --"@{term e\<^isub>2} reduces by IH"
      with WTrtFAssNT `final e\<^isub>1` show ?thesis
	by (fastforce  simp:final_iff intro!:FAssRed2 FAssThrow1)
    qed
  next
    assume "\<not> final e\<^isub>1" --"@{term e\<^isub>1} reduces by IH"
    with WTrtFAssNT show ?thesis by (fastforce intro:FAssRed1)
  qed
next
  case (WTrtCall E e U C M Ts T meth D es Ts' l)
  have wte: "P,E,h \<turnstile> e : U" 
    and icto: "is_class_type_of U C" by fact+
  have IHe: "\<And>l. \<lbrakk> \<D> e \<lfloor>dom l\<rfloor>; \<not> final e \<rbrakk>
             \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>" by fact
  have sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = meth in D" by fact
  have wtes: "P,E,h \<turnstile> es [:] Ts'" by fact
  have IHes: "\<And>l. \<lbrakk>\<D>s es \<lfloor>dom l\<rfloor>; \<not> finals es\<rbrakk> \<Longrightarrow> \<exists>es' s' ta. extTA,P,t \<turnstile> \<langle>es,(h, l)\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>" by fact
  have subtype: "P \<turnstile> Ts' [\<le>] Ts" by fact
  have dae: "\<D> (e\<bullet>M(es)) \<lfloor>dom l\<rfloor>" by fact
  show ?case
  proof(cases "final e")
    assume fine: "final e"
    with wte icto show ?thesis
    proof (rule final_addrE)
      fix a assume e_addr: "e = addr a"
      show ?thesis
      proof(cases "\<exists>vs. es = map Val vs")
	assume es: "\<exists>vs. es = map Val vs"
	from wte e_addr have ha: "typeof_addr h a = \<lfloor>U\<rfloor>"  by(auto)
	have "length es = length Ts'" using wtes by(auto simp add: WTrts_conv_list_all2 dest: list_all2_lengthD)
	moreover from subtype have "length Ts' = length Ts" by(auto dest: list_all2_lengthD)
	ultimately have esTs: "length es = length Ts" by(auto)
        show ?thesis
        proof(cases meth)
          case (Some pnsbody)
          with esTs e_addr ha sees subtype es sees_wf_mdecl[OF wf sees] icto
          show ?thesis by(cases pnsbody) (fastforce intro!: RedCall simp:list_all2_def wf_mdecl_def)
        next
          case None
          with sees wf have "D\<bullet>M(Ts) :: T" by(auto intro: sees_wf_native)
          moreover from es obtain vs where vs: "es = map Val vs" ..
          with wtes have tyes: "map typeof\<^bsub>h\<^esub> vs = map Some Ts'" by simp
	  with ha `D\<bullet>M(Ts) :: T` icto sees None
          have "P,h \<turnstile> a\<bullet>M(vs) : T" using subtype by(auto simp add: external_WT'_iff)
          from external_call_progress[OF wf this hconf, of t] obtain ta va h'
	    where "P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>" by blast
	  thus ?thesis using ha icto None sees vs e_addr
            by(fastforce intro: RedCallExternal simp del: split_paired_Ex)
        qed
      next
	assume "\<not>(\<exists>vs. es = map Val vs)"
	hence not_all_Val: "\<not>(\<forall>e \<in> set es. \<exists>v. e = Val v)"
	  by(simp add:ex_map_conv)
	let ?ves = "takeWhile (\<lambda>e. \<exists>v. e = Val v) es"
        let ?rest = "dropWhile (\<lambda>e. \<exists>v. e = Val v) es"
	let ?ex = "hd ?rest" let ?rst = "tl ?rest"
	from not_all_Val have nonempty: "?rest \<noteq> []" by auto
	hence es: "es = ?ves @ ?ex # ?rst" by simp
	have "\<forall>e \<in> set ?ves. \<exists>v. e = Val v" by(fastforce dest:set_takeWhileD)
	then obtain vs where ves: "?ves = map Val vs"
	  using ex_map_conv by blast
	show ?thesis
	proof cases
	  assume "final ?ex"
	  moreover from nonempty have "\<not>(\<exists>v. ?ex = Val v)"
	    by(auto simp:neq_Nil_conv simp del:dropWhile_eq_Nil_conv)
              (simp add:dropWhile_eq_Cons_conv)
	  ultimately obtain b where ex_Throw: "?ex = Throw b"
	    by(fast elim!:finalE)
	  show ?thesis using e_addr es ex_Throw ves
	    by(fastforce intro:CallThrowParams)
	next
	  assume not_fin: "\<not> final ?ex"
	  have "finals es = finals(?ves @ ?ex # ?rst)" using es
	    by(rule arg_cong)
	  also have "\<dots> = finals(?ex # ?rst)" using ves by simp
	  finally have "finals es = finals(?ex # ?rst)" .
	  hence "\<not> finals es" using not_finals_ConsI[OF not_fin] by blast
	  thus ?thesis using e_addr dae IHes  by(fastforce intro!:CallParams)
	qed
      qed
    next
      fix a assume "e = Throw a"
      thus ?thesis by(fast intro!:CallThrowObj)
    qed
  next
    assume "\<not> final e"
    with WTrtCall show ?thesis by(simp del: split_paired_Ex)(blast intro!:CallObj)
  qed
next
  case (WTrtCallNT E e es Ts M T l)
  have wte: "P,E,h \<turnstile> e : NT" by fact
  have IHe: "\<And>l. \<lbrakk> \<D> e \<lfloor>dom l\<rfloor>; \<not> final e \<rbrakk>
             \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"  by fact
  have IHes: "\<And>l. \<lbrakk>\<D>s es \<lfloor>dom l\<rfloor>; \<not> finals es\<rbrakk> \<Longrightarrow> \<exists>es' s' ta. extTA,P,t \<turnstile> \<langle>es,(h, l)\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>" by fact
  have wtes: "P,E,h \<turnstile> es [:] Ts" by fact
  have dae: "\<D> (e\<bullet>M(es)) \<lfloor>dom l\<rfloor>" by fact
  show ?case
  proof(cases "final e")
    assume "final e"
    moreover
    { fix v assume "e = Val v"
      hence "e = null" using WTrtCallNT by simp
      have ?case
      proof cases
	assume "finals es"
	moreover
	{ fix vs assume "es = map Val vs"
	  with WTrtCallNT `e = null` `finals es` have ?thesis by(fastforce intro: RedCallNull) }
	moreover
	{ fix vs a es' assume "es = map Val vs @ Throw a # es'"
	  with WTrtCallNT `e = null` `finals es` have ?thesis by(fastforce intro: CallThrowParams) }
	ultimately show ?thesis by(fastforce simp:finals_def)
      next
	assume "\<not> finals es" --"@{term es} reduces by IH"
	with WTrtCallNT `e = null` show ?thesis by(fastforce intro: CallParams)
      qed
    }
    moreover
    { fix a assume "e = Throw a"
      with WTrtCallNT have ?case by(fastforce intro: CallThrowObj) }
    ultimately show ?thesis by(fastforce simp:final_iff)
  next
    assume "\<not> final e" --"@{term e} reduces by IH"
    with WTrtCallNT show ?thesis by (fastforce intro:CallObj)
  qed
next
  case (WTrtBlock E V T e T' vo l)
  have IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                 \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h,l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>"
   and D: "\<D> {V:T=vo; e} \<lfloor>dom l\<rfloor>" by fact+
  show ?case
  proof cases
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v assume "e = Val v" thus ?thesis by(fast intro:RedBlock)
    next
      fix a assume "e = Throw a"
      thus ?thesis by(fast intro:BlockThrow)
    qed
  next
    assume not_fin: "\<not> final e"
    from D have De: "\<D> e \<lfloor>dom(l(V:=vo))\<rfloor>" by(auto simp add:hyperset_defs)
    from IH[OF De not_fin]
    obtain h' l' e' tas where red: "extTA,P,t \<turnstile> \<langle>e,(h,l(V:=vo))\<rangle> -tas\<rightarrow> \<langle>e',(h',l')\<rangle>"
      by auto
    thus ?thesis by(blast intro: BlockRed)
  qed
next
  case (WTrtSynchronized E o' T e T' l)
  note wto = `P,E,h \<turnstile> o' : T`
  note IHe = `\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e \<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>`
  note wte = `P,E,h \<turnstile> e : T'`
  note IHo = `\<And>l. \<lbrakk>\<D> o' \<lfloor>dom l\<rfloor>; \<not> final o' \<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>o',(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>`
  note refT = `is_refT T`
  note dae = `\<D> (sync(o') e) \<lfloor>dom l\<rfloor>`
  show ?case
  proof(cases "final o'")
    assume fino: "final o'" 
    thus ?thesis
    proof (rule finalE)
      fix v
      assume oval: "o' = Val v"
      with wto refT show ?thesis
      proof(cases "v")
	assume vnull: "v = Null"
	with oval vnull show ?thesis
	  by(fastforce intro: SynchronizedNull)
      next
	fix ad
	assume vaddr: "v = Addr ad"
	thus ?thesis using oval 
	  by(fastforce intro: LockSynchronized)
      qed(auto elim: refTE)
    next
      fix a
      assume othrow: "o' = Throw a"
      thus ?thesis by(fastforce intro: SynchronizedThrow1)
    qed
  next
    assume nfino: "\<not> final o'"
    with dae IHo show ?case by(fastforce intro: SynchronizedRed1)
  qed
next
  case (WTrtInSynchronized E a T e T' l)
  show ?case
  proof(cases "final e")
    case True thus ?thesis
      by(fastforce elim!: finalE intro: UnlockSynchronized SynchronizedThrow2)
  next
    case False 
    moreover from `\<D> (insync(a) e) \<lfloor>dom l\<rfloor>` have "\<D> e \<lfloor>dom l\<rfloor>" by simp
    moreover note IHe = `\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk> \<Longrightarrow> \<exists>e' s' tas. extTA,P,t \<turnstile> \<langle>e,(h, l)\<rangle> -tas\<rightarrow> \<langle>e',s'\<rangle>`
    ultimately show ?thesis by(fastforce intro: SynchronizedRed2)
  qed
next
  case (WTrtSeq E e1 T1 e2 T2 l)
  show ?case
  proof cases
    assume "final e1"
    thus ?thesis
      by(fast elim:finalE intro:intro:RedSeq SeqThrow)
  next
    assume "\<not> final e1" with WTrtSeq show ?thesis
      by(simp del: split_paired_Ex)(blast intro!:SeqRed)
  qed
next
  case (WTrtCond E e e1 T1 e2 T2 T l)
  have wt: "P,E,h \<turnstile> e : Boolean" by fact
  show ?case
  proof cases
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v assume val: "e = Val v"
      then obtain b where v: "v = Bool b" using wt by auto
      show ?thesis
      proof (cases b)
	case True with val v show ?thesis by(fastforce intro:RedCondT)
      next
	case False with val v show ?thesis by(fastforce intro:RedCondF)
      qed
    next
      fix a assume "e = Throw a"
      thus ?thesis by(fast intro:CondThrow)
    qed
  next
    assume "\<not> final e" with WTrtCond show ?thesis
      by simp (fast intro:CondRed)
  qed
next
  case WTrtWhile show ?case by(fast intro:RedWhile)
next
  case (WTrtThrow E e T T' l)
  show ?case
  proof cases
    assume "final e" -- {*Then @{term e} must be @{term throw} or @{term null}*}
    thus ?thesis
    proof(induct rule: finalE)
      case (Val v)
      with `P \<turnstile> T \<le> Class Throwable` `\<not> final (throw e)` `P,E,h \<turnstile> e : T`
      have "v = Null" by(cases v)(auto simp add: final_iff widen_Class)
      thus ?thesis using Val by(fastforce intro: RedThrowNull)
    next
      case (Throw a)
      thus ?thesis by(fastforce intro: ThrowThrow)
    qed
  next
    assume "\<not> final e" -- {*Then @{term e} must reduce*}
    with WTrtThrow show ?thesis by simp (blast intro:ThrowRed)
  qed
next
  case (WTrtTry E e1 T1 V C e2 T2 l)
  have wt1: "P,E,h \<turnstile> e1 : T1" by fact
  show ?case
  proof cases
    assume "final e1"
    thus ?thesis
    proof (rule finalE)
      fix v assume "e1 = Val v"
      thus ?thesis by(fast intro:RedTry)
    next
      fix a
      assume e1_Throw: "e1 = Throw a"
      with wt1 obtain D where ha: "typeof_addr h a = \<lfloor>Class D\<rfloor>"
	by(auto simp add: widen_Class dest: typeof_addr_eq_Some_conv)
      thus ?thesis using e1_Throw
        by(cases "P \<turnstile> D \<preceq>\<^sup>* C")(fastforce intro:RedTryCatch RedTryFail)+
    qed
  next
    assume "\<not> final e1"
    with WTrtTry show ?thesis by simp (fast intro:TryRed)
  qed
next
  case WTrtNil thus ?case by simp
next
  case (WTrtCons E e T es Ts)
  have IHe: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                \<Longrightarrow> \<exists>e' s' ta. extTA,P,t \<turnstile> \<langle>e,(h,l)\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>"
   and IHes: "\<And>l. \<lbrakk>\<D>s es \<lfloor>dom l\<rfloor>; \<not> finals es\<rbrakk>
             \<Longrightarrow> \<exists>es' s' ta. extTA,P,t \<turnstile> \<langle>es,(h,l)\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>"
   and D: "\<D>s (e#es) \<lfloor>dom l\<rfloor>" and not_fins: "\<not> finals(e # es)" by fact+
  have De: "\<D> e \<lfloor>dom l\<rfloor>" and Des: "\<D>s es (\<lfloor>dom l\<rfloor> \<squnion> \<A> e)"
    using D by auto
  show ?case
  proof cases
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v assume e: "e = Val v"
      hence Des': "\<D>s es \<lfloor>dom l\<rfloor>" using De Des by auto
      have not_fins_tl: "\<not> finals es" using not_fins e by simp
      show ?thesis using e IHes[OF Des' not_fins_tl]
	by (blast intro!:ListRed2)
    next
      fix a assume "e = Throw a"
      hence False using not_fins by simp
      thus ?thesis ..
    qed
  next
    assume "\<not> final e"
    with IHe[OF De] show ?thesis by(fast intro!:ListRed1)
  qed
qed

end
