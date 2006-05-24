(*  Title:       CoreC++
    ID:          $Id: SmallStep.thy,v 1.4 2006-05-24 01:09:42 lsf37 Exp $
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

   Based on the Jinja theory J/SmallStep.thy by Tobias Nipkow 
*)


header {* Small Step Semantics *}

theory SmallStep imports Syntax State begin

subsection {* Some pre-definitions *}

consts blocks :: "vname list \<times> ty list \<times> val list \<times> expr \<Rightarrow> expr"
recdef blocks "measure(\<lambda>(Vs,Ts,vs,e). size Vs)"
 "blocks(V#Vs, T#Ts, v#vs, e) = {V:T := Val v; blocks(Vs,Ts,vs,e)}"
 "blocks([],[],[],e) = e"


lemma [simp]:
  "\<lbrakk> size vs = size Vs; size Ts = size Vs \<rbrakk> \<Longrightarrow> fv(blocks(Vs,Ts,vs,e)) = fv e - set Vs"

apply(induct rule:blocks.induct)
apply simp_all
apply blast
done



constdefs
  assigned :: "vname \<Rightarrow> expr \<Rightarrow> bool"
  "assigned V e  \<equiv>  \<exists>v e'. e = (V:= Val v;; e')"


subsection {* The rules *}

consts
  red  :: "prog \<Rightarrow> (env \<times> (expr \<times> state) \<times> (expr \<times> state)) set"
  reds  :: "prog \<Rightarrow> (env \<times> (expr list \<times> state) \<times> (expr list \<times> state)) set"


syntax (xsymbols)
  red :: "prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool"
          ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) \<rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  reds :: "prog \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> bool"
          ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) [\<rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)


translations
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"  ==  "(E,(e,s), e',s') \<in> red P"
  "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>" == "(E,(es,s), es',s') \<in> reds P"

  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>" <= "(E,(e,h,l), e',h',l') \<in> red P"
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>" <= "(E,(e,s), e',h',l') \<in> red P"
  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',s'\<rangle>" <= "(E,(e,h,l), e',s') \<in> red P"
  "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle>" <= "(E,(es,h,l), es',h',l') \<in> reds P"
  "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle>" <= "(E,(es,s), es',h',l') \<in> reds P"
  "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>" <= "(E,(es,h,l), es',s') \<in> reds P"



inductive "red P" "reds P"
intros

RedNew:
  "\<lbrakk> new_Addr h = Some a; h' = h(a\<mapsto>(C,init_obj P C)) \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>new C, (h,l)\<rangle> \<rightarrow> \<langle>ref (a,[C]), (h',l)\<rangle>"

RedNewFail:
  "new_Addr h = None \<Longrightarrow>
  P,E \<turnstile> \<langle>new C, (h,l)\<rangle> \<rightarrow> \<langle>THROW OutOfMemory, (h,l)\<rangle>"

StaticCastRed:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>\<lparr>C\<rparr>e, s\<rangle> \<rightarrow> \<langle>\<lparr>C\<rparr>e', s'\<rangle>"

RedStaticCastNull:
  "P,E \<turnstile> \<langle>\<lparr>C\<rparr>null, s\<rangle> \<rightarrow> \<langle>null,s\<rangle>"

RedStaticUpCast:
  "\<lbrakk> P \<turnstile> Path last Cs to C via Cs'; Ds = Cs@\<^sub>pCs' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>(ref (a,Cs)), s\<rangle> \<rightarrow> \<langle>ref (a,Ds), s\<rangle>"

RedStaticDownCast:
  "\<lbrakk> is_class P C; C \<notin> set Cs' \<rbrakk> 
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>(ref (a,Cs@[C]@Cs')), s\<rangle> \<rightarrow> \<langle>ref (a,Cs@[C]), s\<rangle>"

RedStaticCastFail:
  "\<lbrakk> \<not> P \<turnstile> Path last Cs to C unique; C \<notin> set Cs \<or> \<not> distinct Cs \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>(ref (a,Cs)), s\<rangle> \<rightarrow> \<langle>THROW ClassCast, s\<rangle>"

DynCastRed:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>Cast C e, s\<rangle> \<rightarrow> \<langle>Cast C e', s'\<rangle>"

RedDynCastNull:
  "P,E \<turnstile> \<langle>Cast C null, s\<rangle> \<rightarrow> \<langle>null,s\<rangle>"

RedStaticUpDynCast:
  "\<lbrakk> P \<turnstile> Path last Cs to C via Cs'; Ds = Cs@\<^sub>pCs' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C(ref(a,Cs)),s\<rangle> \<rightarrow> \<langle>ref(a,Ds),s\<rangle>"

RedStaticDownDynCast:
  "\<lbrakk> is_class P C; C \<notin> set Cs' \<rbrakk> 
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C (ref (a,Cs@[C]@Cs')), s\<rangle> \<rightarrow> \<langle>ref (a,Cs@[C]), s\<rangle>"

RedDynCast:
 "\<lbrakk> hp s a = Some(D,S); P \<turnstile> Path D to C via Cs'\<rbrakk> 
   (*P \<turnstile> Path D to C unique \<rbrakk>*)
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C (ref (a,Cs)), s\<rangle> \<rightarrow> \<langle>ref (a,Cs'), s\<rangle>"

RedDynCastFail:
  "\<lbrakk>hp s a = Some(D,S); \<not> P \<turnstile> Path D to C unique;
    \<not> P \<turnstile> Path last Cs to C unique; C \<notin> set Cs \<or> \<not> distinct Cs \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C (ref (a,Cs)), s\<rangle> \<rightarrow> \<langle>null, s\<rangle>"

BinOpRed1:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e \<guillemotleft>bop\<guillemotright> e\<^isub>2, s\<rangle> \<rightarrow> \<langle>e' \<guillemotleft>bop\<guillemotright> e\<^isub>2, s'\<rangle>"

BinOpRed2:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>(Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> e, s\<rangle> \<rightarrow> \<langle>(Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> e', s'\<rangle>"

RedBinOp:
  "binop(bop,v\<^isub>1,v\<^isub>2) = Some v \<Longrightarrow>
  P,E \<turnstile> \<langle>(Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> (Val v\<^isub>2), s\<rangle> \<rightarrow> \<langle>Val v,s\<rangle>"

RedVar:
  "lcl s V = Some v \<Longrightarrow>
  P,E \<turnstile> \<langle>Var V,s\<rangle> \<rightarrow> \<langle>Val v,s\<rangle>"

LAssRed:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>V:=e,s\<rangle> \<rightarrow> \<langle>V:=e',s'\<rangle>"

RedLAss:
  "\<lbrakk>E V = Some T; P \<turnstile> T casts v to v'\<rbrakk> \<Longrightarrow> 
  P,E \<turnstile> \<langle>V:=(Val v),(h,l)\<rangle> \<rightarrow> \<langle>Val v',(h,l(V\<mapsto>v'))\<rangle>"

FAccRed:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<bullet>F{Cs}, s\<rangle> \<rightarrow> \<langle>e'\<bullet>F{Cs}, s'\<rangle>"

RedFAcc:
  "\<lbrakk> hp s a = Some(D,S); Ds = Cs'@\<^sub>pCs; (Ds,fs) \<in> S; fs F = Some v \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>(ref (a,Cs'))\<bullet>F{Cs}, s\<rangle> \<rightarrow> \<langle>Val v,s\<rangle>"

RedFAccNull:
  "P,E \<turnstile> \<langle>null\<bullet>F{Cs}, s\<rangle> \<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

FAssRed1:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<bullet>F{Cs}:=e\<^isub>2, s\<rangle> \<rightarrow> \<langle>e'\<bullet>F{Cs}:=e\<^isub>2, s'\<rangle>"

FAssRed2:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
   P,E \<turnstile> \<langle>Val v\<bullet>F{Cs}:=e, s\<rangle> \<rightarrow> \<langle>Val v\<bullet>F{Cs}:=e', s'\<rangle>"

RedFAss:
"\<lbrakk>h a = Some(D,S); P \<turnstile> (last Cs') has least F:T via Cs;
  P \<turnstile> T casts v to v'; Ds = Cs'@\<^sub>pCs; (Ds,fs) \<in> S\<rbrakk> \<Longrightarrow>
  P,E \<turnstile> \<langle>(ref (a,Cs'))\<bullet>F{Cs}:=(Val v), (h,l)\<rangle> \<rightarrow> \<langle>Val v', (h(a \<mapsto> (D,insert (Ds,fs(F\<mapsto>v')) (S - {(Ds,fs)}))),l)\<rangle>"

RedFAssNull:
  "P,E \<turnstile> \<langle>null\<bullet>F{Cs}:=Val v, s\<rangle> \<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

CallObj:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<bullet>M(es),s\<rangle> \<rightarrow> \<langle>e'\<bullet>M(es),s'\<rangle>"

CallParams:
  "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow>
   P,E \<turnstile> \<langle>(Val v)\<bullet>M(es),s\<rangle> \<rightarrow> \<langle>(Val v)\<bullet>M(es'),s'\<rangle>"

RedCall:
  "\<lbrakk> hp s a = Some(C,S); P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds;
    P \<turnstile> (C,Cs@\<^sub>pDs) selects M = (Ts,T,pns,body) via Cs';
    size vs = size pns; size Ts = size pns;
    new_body = 
     (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>blocks(this#pns,Class(last Cs')#Ts,Ref(a,Cs')#vs,body)
                     | _ \<Rightarrow> blocks(this#pns,Class(last Cs')#Ts,Ref(a,Cs')#vs,body))\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>(ref (a,Cs))\<bullet>M(map Val vs), s\<rangle> \<rightarrow> \<langle>new_body, s\<rangle>"

RedCallNull:
  "P,E \<turnstile> \<langle>null\<bullet>M(map Val vs),s\<rangle> \<rightarrow> \<langle>THROW NullPointer,s\<rangle>"

BlockRedNone:
  "\<lbrakk> P,E(V \<mapsto> T) \<turnstile> \<langle>e, (h,l(V:=None))\<rangle> \<rightarrow> \<langle>e', (h',l')\<rangle>; l' V = None; \<not> assigned V e \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>{V:T; e}, (h,l)\<rangle> \<rightarrow> \<langle>{V:T; e'}, (h',l'(V := l V))\<rangle>"

BlockRedSome:
  "\<lbrakk> P,E(V \<mapsto> T) \<turnstile> \<langle>e, (h,l(V:=None))\<rangle> \<rightarrow> \<langle>e', (h',l')\<rangle>; l' V = Some v;
     \<not> assigned V e \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>{V:T; e}, (h,l)\<rangle> \<rightarrow> \<langle>{V:T := Val v; e'}, (h',l'(V := l V))\<rangle>"

InitBlockRed:
  "\<lbrakk> P,E(V \<mapsto> T) \<turnstile> \<langle>e, (h,l(V\<mapsto>v'))\<rangle> \<rightarrow> \<langle>e', (h',l')\<rangle>; l' V = Some v''; 
     P \<turnstile> T casts v to v' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>{V:T := Val v; e}, (h,l)\<rangle> \<rightarrow> \<langle>{V:T := Val v''; e'}, (h',l'(V := l V))\<rangle>"

RedBlock:
  "P,E \<turnstile> \<langle>{V:T; Val u}, s\<rangle> \<rightarrow> \<langle>Val u, s\<rangle>"

RedInitBlock:
  "P \<turnstile> T casts v to v' \<Longrightarrow> P,E \<turnstile> \<langle>{V:T := Val v; Val u}, s\<rangle> \<rightarrow> \<langle>Val u, s\<rangle>"

SeqRed:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e;;e\<^isub>2, s\<rangle> \<rightarrow> \<langle>e';;e\<^isub>2, s'\<rangle>"

RedSeq:
  "P,E \<turnstile> \<langle>(Val v);;e\<^isub>2, s\<rangle> \<rightarrow> \<langle>e\<^isub>2, s\<rangle>"

CondRed:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>if (e) e\<^isub>1 else e\<^isub>2, s\<rangle> \<rightarrow> \<langle>if (e') e\<^isub>1 else e\<^isub>2, s'\<rangle>"

RedCondT:
  "P,E \<turnstile> \<langle>if (true) e\<^isub>1 else e\<^isub>2, s\<rangle> \<rightarrow> \<langle>e\<^isub>1, s\<rangle>"

RedCondF:
  "P,E \<turnstile> \<langle>if (false) e\<^isub>1 else e\<^isub>2, s\<rangle> \<rightarrow> \<langle>e\<^isub>2, s\<rangle>"

RedWhile:
  "P,E \<turnstile> \<langle>while(b) c, s\<rangle> \<rightarrow> \<langle>if(b) (c;;while(b) c) else unit, s\<rangle>"

ThrowRed:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>throw e, s\<rangle> \<rightarrow> \<langle>throw e', s'\<rangle>"

RedThrowNull:
  "P,E \<turnstile> \<langle>throw null, s\<rangle> \<rightarrow> \<langle>THROW NullPointer, s\<rangle>"

ListRed1:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e#es,s\<rangle> [\<rightarrow>] \<langle>e'#es,s'\<rangle>"

ListRed2:
  "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>Val v # es,s\<rangle> [\<rightarrow>] \<langle>Val v # es',s'\<rangle>"

-- "Exception propagation"

DynCastThrow: "P,E \<turnstile> \<langle>Cast C (Throw r), s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
StaticCastThrow: "P,E \<turnstile> \<langle>\<lparr>C\<rparr>(Throw r), s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
BinOpThrow1: "P,E \<turnstile> \<langle>(Throw r) \<guillemotleft>bop\<guillemotright> e\<^isub>2, s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
BinOpThrow2: "P,E \<turnstile> \<langle>(Val v\<^isub>1) \<guillemotleft>bop\<guillemotright> (Throw r), s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
LAssThrow: "P,E \<turnstile> \<langle>V:=(Throw r), s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
FAccThrow: "P,E \<turnstile> \<langle>(Throw r)\<bullet>F{Cs}, s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
FAssThrow1: "P,E \<turnstile> \<langle>(Throw r)\<bullet>F{Cs}:=e\<^isub>2, s\<rangle> \<rightarrow> \<langle>Throw r,s\<rangle>"
FAssThrow2: "P,E \<turnstile> \<langle>Val v\<bullet>F{Cs}:=(Throw r), s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
CallThrowObj: "P,E \<turnstile> \<langle>(Throw r)\<bullet>M(es), s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
CallThrowParams: "\<lbrakk> es = map Val vs @ Throw r # es' \<rbrakk> 
  \<Longrightarrow> P,E \<turnstile> \<langle>(Val v)\<bullet>M(es), s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
BlockThrow: "P,E \<turnstile> \<langle>{V:T; Throw r}, s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
InitBlockThrow: "P \<turnstile> T casts v to v' 
  \<Longrightarrow> P,E \<turnstile> \<langle>{V:T := Val v; Throw r}, s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
SeqThrow: "P,E \<turnstile> \<langle>(Throw r);;e\<^isub>2, s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
CondThrow: "P,E \<turnstile> \<langle>if (Throw r) e\<^isub>1 else e\<^isub>2, s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"
ThrowThrow: "P,E \<turnstile> \<langle>throw(Throw r), s\<rangle> \<rightarrow> \<langle>Throw r, s\<rangle>"


lemmas red_reds_induct = red_reds.induct [split_format (complete)]

ML_setup {*
  store_thms ("red_reds_inducts", ProjectRule.projections (thm "red_reds_induct"))
*}

inductive_cases [elim!]:
 "P,E \<turnstile> \<langle>V:=e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
 "P,E \<turnstile> \<langle>e1;;e2,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"

declare Cons_eq_map_conv [iff]

lemma "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> True"
and reds_length:"P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> length es = length es'"
by (induct rule: red_reds.inducts) auto


subsection{* The reflexive transitive closure *}

consts
  Red ::  "prog \<Rightarrow> env \<Rightarrow> ((expr      \<times> state) \<times> (expr      \<times> state)) set"
  Reds :: "prog \<Rightarrow> env \<Rightarrow> ((expr list \<times> state) \<times> (expr list \<times> state)) set"

defs
  Red_def: "Red P E \<equiv>  {((e,s),e',s'). P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>}"
  Reds_def:"Reds P E \<equiv> {((es,s),es',s'). P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>}"

lemma[simp]: "((e,s),e',s') \<in> Red P E = P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
by (simp add:Red_def)

lemma[simp]: "((es,s),es',s') \<in> Reds P E = P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>"
by (simp add:Reds_def)



syntax (xsymbols)
  Step :: "prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool"
          ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) \<rightarrow>*/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  Steps :: "prog \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> bool"
          ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) [\<rightarrow>]*/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)

translations
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"  ==  "((e,s), e',s') \<in> (Red P E)\<^sup>*"
  "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle>"  ==  "((es,s), es',s') \<in> (Reds P E)\<^sup>*"

  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow>* \<langle>e',(h',l')\<rangle>" <= "((e,h,l), e',h',l') \<in> (Red P E)\<^sup>*"
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',(h',l')\<rangle>" <= "((e,s), e',h',l') \<in> (Red P E)\<^sup>*"
  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>" <= "((e,h,l), e',s') \<in> (Red P E)\<^sup>*"
  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> [\<rightarrow>]* \<langle>e',(h',l')\<rangle>" <= "((e,h,l), e',h',l') \<in> (Reds P E)\<^sup>*"
  "P,E \<turnstile> \<langle>e,s\<rangle> [\<rightarrow>]* \<langle>e',(h',l')\<rangle>" <= "((e,s), e',h',l') \<in> (Reds P E)\<^sup>*"
  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> [\<rightarrow>]* \<langle>e',s'\<rangle>" <= "((e,h,l), e',s') \<in> (Reds P E)\<^sup>*"


lemma converse_rtrancl_induct_red[consumes 1]:
assumes "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow>* \<langle>e',(h',l')\<rangle>"
and "\<And>e h l. R e h l e h l"
and "\<And>e\<^isub>0 h\<^isub>0 l\<^isub>0 e\<^isub>1 h\<^isub>1 l\<^isub>1 e' h' l'.
       \<lbrakk> P,E \<turnstile> \<langle>e\<^isub>0,(h\<^isub>0,l\<^isub>0)\<rangle> \<rightarrow> \<langle>e\<^isub>1,(h\<^isub>1,l\<^isub>1)\<rangle>; R e\<^isub>1 h\<^isub>1 l\<^isub>1 e' h' l' \<rbrakk> \<Longrightarrow> R e\<^isub>0 h\<^isub>0 l\<^isub>0 e' h' l'"
shows "R e h l e' h' l'"

proof -
  { fix s s'
    assume reds: "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
       and base: "\<And>e s. R e (hp s) (lcl s) e (hp s) (lcl s)"
       and IH: "\<And>e\<^isub>0 s\<^isub>0 e\<^isub>1 s\<^isub>1 e' s'.
           \<lbrakk> P,E \<turnstile> \<langle>e\<^isub>0,s\<^isub>0\<rangle> \<rightarrow> \<langle>e\<^isub>1,s\<^isub>1\<rangle>; R e\<^isub>1 (hp s\<^isub>1) (lcl s\<^isub>1) e' (hp s') (lcl s') \<rbrakk>
           \<Longrightarrow> R e\<^isub>0 (hp s\<^isub>0) (lcl s\<^isub>0) e' (hp s') (lcl s')"
    from reds have "R e (hp s) (lcl s) e' (hp s') (lcl s')"
    proof (induct rule:converse_rtrancl_induct2)
      case refl show ?case by(rule base)
    next
      case (step e\<^isub>0 s\<^isub>0 e s)
      have Red:"((e\<^isub>0,s\<^isub>0),e,s) \<in> Red P E"
	and R:"R e (hp s) (lcl s) e' (hp s') (lcl s')" .
      from IH[OF Red[simplified] R] show ?case .
    qed
    }
  with prems show ?thesis by fastsimp
qed



lemma steps_length:"P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle> \<Longrightarrow> length es = length es'"
by(induct rule:rtrancl_induct2,auto intro:reds_length)


subsection{*Some easy lemmas*}

lemma [iff]: "\<not> P,E \<turnstile> \<langle>[],s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>"
by(blast elim: red_reds.elims)

lemma [iff]: "\<not> P,E \<turnstile> \<langle>Val v,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
by(fastsimp elim: red_reds.elims)

lemma [iff]: "\<not> P,E \<turnstile> \<langle>Throw r,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
by(fastsimp elim: red_reds.elims)


lemma red_lcl_incr: "P,E \<turnstile> \<langle>e,(h\<^isub>0,l\<^isub>0)\<rangle> \<rightarrow> \<langle>e',(h\<^isub>1,l\<^isub>1)\<rangle> \<Longrightarrow> dom l\<^isub>0 \<subseteq> dom l\<^isub>1"
and "P,E \<turnstile> \<langle>es,(h\<^isub>0,l\<^isub>0)\<rangle> [\<rightarrow>] \<langle>es',(h\<^isub>1,l\<^isub>1)\<rangle> \<Longrightarrow> dom l\<^isub>0 \<subseteq> dom l\<^isub>1"
by (induct rule: red_reds_inducts) (auto simp del:fun_upd_apply)


lemma red_lcl_add: "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> (\<And>l\<^isub>0. P,E \<turnstile> \<langle>e,(h,l\<^isub>0++l)\<rangle> \<rightarrow> \<langle>e',(h',l\<^isub>0++l')\<rangle>)"
and "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> (\<And>l\<^isub>0. P,E \<turnstile> \<langle>es,(h,l\<^isub>0++l)\<rangle> [\<rightarrow>] \<langle>es',(h',l\<^isub>0++l')\<rangle>)"
 
proof (induct rule:red_reds_inducts)
  case RedLAss thus ?case by(auto intro:red_reds.intros simp del:fun_upd_apply)
next
  case RedStaticDownCast thus ?case by(fastsimp intro:red_reds.intros)
next
  case RedStaticUpDynCast thus ?case by(fastsimp intro:red_reds.intros)
next
  case RedStaticDownDynCast thus ?case by(fastsimp intro:red_reds.intros)
next
  case RedDynCast thus ?case by(fastsimp intro:red_reds.intros)
next
  case RedDynCastFail thus ?case by(fastsimp intro:red_reds.intros)
next
  case RedFAcc thus ?case by(fastsimp intro:red_reds.intros)
next
  case RedFAss thus ?case by (fastsimp intro:red_reds.intros)
next
  case RedCall thus ?case by (fastsimp intro!:red_reds.RedCall)
next
  (*case RedCallClass thus ?case by(fastsimp intro!:red_reds.intros)
next*)
  case (InitBlockRed E T V e e' h h' l l' v v' v'' l\<^isub>0)
  have IH: "\<And>l\<^isub>0. P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l\<^isub>0 ++ l(V \<mapsto> v'))\<rangle> \<rightarrow> \<langle>e',(h', l\<^isub>0 ++ l')\<rangle>"
    and l'V: "l' V = Some v''" and casts:"P \<turnstile> T casts v to v'" .
  from IH have IH': "P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, (l\<^isub>0 ++ l)(V \<mapsto> v'))\<rangle> \<rightarrow> \<langle>e',(h',l\<^isub>0 ++ l')\<rangle>"
    by simp
  have "(l\<^isub>0 ++ l')(V := (l\<^isub>0 ++ l) V) = l\<^isub>0 ++ l'(V := l V)"
    by(rule ext)(simp add:map_add_def)
  with red_reds.InitBlockRed[OF IH' _ casts] l'V show ?case
    by(simp del:fun_upd_apply)
next
  case (BlockRedNone E T V e e' h h' l l' l\<^isub>0)
  have IH: "\<And>l\<^isub>0. P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l\<^isub>0 ++ l(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l\<^isub>0 ++ l')\<rangle>"
    and l'V: "l' V = None" and unass: "\<not> assigned V e" .
  have "l\<^isub>0(V := None) ++ l(V := None) = (l\<^isub>0 ++ l)(V := None)"
    by(simp add:expand_fun_eq map_add_def)
  hence IH': "P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, (l\<^isub>0++l)(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l\<^isub>0(V := None) ++ l')\<rangle>"
    using IH[of "l\<^isub>0(V := None)"] by simp
  have "(l\<^isub>0(V := None) ++ l')(V := (l\<^isub>0 ++ l) V) = l\<^isub>0 ++ l'(V := l V)"
    by(simp add:expand_fun_eq map_add_def)
  with red_reds.BlockRedNone[OF IH' _ unass] l'V show ?case
    by(simp add: map_add_def)
next
  case (BlockRedSome E T V e e' h h' l l' v l\<^isub>0)
  have IH: "\<And>l\<^isub>0. P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l\<^isub>0 ++ l(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l\<^isub>0 ++ l')\<rangle>"
    and l'V: "l' V = Some v" and unass: "\<not> assigned V e" .
  have "l\<^isub>0(V := None) ++ l(V := None) = (l\<^isub>0 ++ l)(V := None)"
    by(simp add:expand_fun_eq map_add_def)
  hence IH': "P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, (l\<^isub>0++l)(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l\<^isub>0(V := None) ++ l')\<rangle>"
    using IH[of "l\<^isub>0(V := None)"] by simp
  have "(l\<^isub>0(V := None) ++ l')(V := (l\<^isub>0 ++ l) V) = l\<^isub>0 ++ l'(V := l V)"
    by(simp add:expand_fun_eq map_add_def)
  with red_reds.BlockRedSome[OF IH' _ unass] l'V show ?case
    by(simp add:map_add_def)
next
qed (simp_all add:red_reds.intros)



lemma Red_lcl_add:
assumes "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow>* \<langle>e',(h',l')\<rangle>" shows "P,E \<turnstile> \<langle>e,(h,l\<^isub>0++l)\<rangle> \<rightarrow>* \<langle>e',(h',l\<^isub>0++l')\<rangle>"

using prems
proof(induct rule:converse_rtrancl_induct_red)
  case 1 thus ?case by simp
next
  case 2 thus ?case
    by(auto dest: red_lcl_add intro: converse_rtrancl_into_rtrancl simp:Red_def)
qed



lemma 
red_preserves_obj:"\<lbrakk>P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>; h a = Some(D,S)\<rbrakk> 
  \<Longrightarrow> \<exists>S'. h' a = Some(D,S')"
and reds_preserves_obj:"\<lbrakk>P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle>; h a = Some(D,S)\<rbrakk> 
  \<Longrightarrow> \<exists>S'. h' a = Some(D,S')"
by (induct rule:red_reds_inducts) (auto dest:new_Addr_SomeD)

end
