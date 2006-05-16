(* Author: Tobias Nipkow, Daniel Wasserrab *)


header {* \isaheader{Program annotation} *}

theory Annotate imports WellType begin


syntax (output)
  unanFAcc :: "expr \<Rightarrow> vname \<Rightarrow> expr" ("(_\<bullet>_)" [10,10] 90)
  unanFAss :: "expr \<Rightarrow> vname \<Rightarrow> expr \<Rightarrow> expr" ("(_\<bullet>_ := _)" [10,0,90] 90)

translations
  "unanFAcc e F" == "FAcc e F []"
  "unanFAss e F e'" == "FAss e F [] e'"


consts
  Anno :: "prog \<Rightarrow> (env \<times> expr      \<times> expr) set"
  Annos:: "prog \<Rightarrow> (env \<times> expr list \<times> expr list) set"


syntax (xsymbols)
  Anno :: "[prog,env, expr     , expr] \<Rightarrow> bool"
         ("_,_ \<turnstile> _ \<leadsto> _"   [51,0,0,51]50)
  Annos:: "[prog,env, expr list, expr list] \<Rightarrow> bool"
         ("_,_ \<turnstile> _ [\<leadsto>] _" [51,0,0,51]50)


translations
  "P,E \<turnstile> e \<leadsto> e'" == "(E,e,e') \<in> Anno P"
  "P,E \<turnstile> es [\<leadsto>] es'" == "(E,es,es') \<in> Annos P"

inductive "Anno P" "Annos P"
intros
  
AnnoNew: "is_class P C  \<Longrightarrow>  P,E \<turnstile> new C \<leadsto> new C"
AnnoCast: "P,E \<turnstile> e \<leadsto> e' \<Longrightarrow> P,E \<turnstile> Cast C e \<leadsto> Cast C e'"
AnnoStatCast: "P,E \<turnstile> e \<leadsto> e' \<Longrightarrow> P,E \<turnstile> StatCast C e \<leadsto> StatCast C e'"
AnnoVal: "P,E \<turnstile> Val v \<leadsto> Val v"
AnnoVarVar: "E V = \<lfloor>T\<rfloor> \<Longrightarrow> P,E \<turnstile> Var V \<leadsto> Var V"
AnnoVarField: "\<lbrakk> E V = None; E this = \<lfloor>Class C\<rfloor>; P \<turnstile> C has least V:T via Cs \<rbrakk>
               \<Longrightarrow> P,E \<turnstile> Var V \<leadsto> Var this\<bullet>V{Cs}"
AnnoBinOp:
  "\<lbrakk> P,E \<turnstile> e1 \<leadsto> e1';  P,E \<turnstile> e2 \<leadsto> e2' \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 \<leadsto> e1' \<guillemotleft>bop\<guillemotright> e2'"
AnnoLAss:
  "P,E \<turnstile> e \<leadsto> e' \<Longrightarrow> P,E \<turnstile> V:=e \<leadsto> V:=e'"
AnnoFAcc:
  "\<lbrakk> P,E \<turnstile> e \<leadsto> e';  P,E \<turnstile> e' :: Class C;  P \<turnstile> C has least F:T via Cs \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> e\<bullet>F{[]} \<leadsto> e'\<bullet>F{Cs}"
AnnoFAss: "\<lbrakk> P,E \<turnstile> e1 \<leadsto> e1';  P,E \<turnstile> e2 \<leadsto> e2';
             P,E \<turnstile> e1' :: Class C; P \<turnstile> C has least F:T via Cs \<rbrakk>
          \<Longrightarrow> P,E \<turnstile> e1\<bullet>F{[]} := e2 \<leadsto> e1'\<bullet>F{Cs} := e2'"
AnnoCall:
  "\<lbrakk> P,E \<turnstile> e \<leadsto> e';  P,E \<turnstile> es [\<leadsto>] es' \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> Call e M es \<leadsto> Call e' M es'"
AnnoBlock:
  "P,E(V \<mapsto> T) \<turnstile> e \<leadsto> e'  \<Longrightarrow>  P,E \<turnstile> {V:T; e} \<leadsto> {V:T; e'}"
AnnoComp: "\<lbrakk> P,E \<turnstile> e1 \<leadsto> e1';  P,E \<turnstile> e2 \<leadsto> e2' \<rbrakk>
           \<Longrightarrow>  P,E \<turnstile> e1;;e2 \<leadsto> e1';;e2'"
AnnoCond: "\<lbrakk> P,E \<turnstile> e \<leadsto> e'; P,E \<turnstile> e1 \<leadsto> e1';  P,E \<turnstile> e2 \<leadsto> e2' \<rbrakk>
          \<Longrightarrow> P,E \<turnstile> if (e) e1 else e2 \<leadsto> if (e') e1' else e2'"
AnnoLoop: "\<lbrakk> P,E \<turnstile> e \<leadsto> e';  P,E \<turnstile> c \<leadsto> c' \<rbrakk>
          \<Longrightarrow> P,E \<turnstile> while (e) c \<leadsto> while (e') c'"
AnnoThrow: "P,E \<turnstile> e \<leadsto> e'  \<Longrightarrow>  P,E \<turnstile> throw e \<leadsto> throw e'"

AnnoNil: "P,E \<turnstile> [] [\<leadsto>] []"
AnnoCons: "\<lbrakk> P,E \<turnstile> e \<leadsto> e';  P,E \<turnstile> es [\<leadsto>] es' \<rbrakk>
           \<Longrightarrow>  P,E \<turnstile> e#es [\<leadsto>] e'#es'"

end
