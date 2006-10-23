(*  Title:       One procedure
    ID:          $Id: PLang.thy,v 1.1 2006-08-08 23:22:32 nipkow Exp $
    Author:      Tobias Nipkow, 2001/2006
    Maintainer:  Tobias Nipkow
*)

header "Hoare Logics for 1 Procedure"

theory PLang imports Main begin

subsection{* The language *}

typedecl state

types bexp = "state \<Rightarrow> bool"

ML{*DatatypeProp.dtK := 8*}

datatype com = Do "(state \<Rightarrow> state set)"
                    | Semi  com com            ("_; _"  [60, 60] 10)
                    | Cond  bexp com com     ("IF _ THEN _ ELSE _"  60)
                    | While bexp com           ("WHILE _ DO _"  60)
                    | CALL
                    | Local "(state \<Rightarrow> state)" com "(state \<Rightarrow> state \<Rightarrow> state)"
                      ("LOCAL _; _; _" [0,0,60] 60)

text{*\noindent There is only one parameterless procedure in the program. Hence
@{term CALL} does not even need to mention the procedure name. There
is no separate syntax for procedure declarations. Instead we declare a HOL
constant that represents the body of the one procedure in the program.*}

consts body :: com

consts  exec    :: "(state \<times> com \<times> state)set"
abbreviation
 exec' :: "state \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool"  ("_/ -_\<rightarrow>/ _" [50,0,50] 50)
 "s0 -c\<rightarrow> s1  \<equiv>  (s0,c,s1) \<in> exec"

text{*\noindent
As before, command execution is described by transitions
@{prop"s -c\<rightarrow> t"}. The only new rule is the one for @{term CALL} ---
it requires no comment:*}

inductive exec
intros
    Do:     "t \<in> f s \<Longrightarrow> s -Do f\<rightarrow> t"

    Semi:   "\<lbrakk> s0 -c1\<rightarrow> s1; s1 -c2\<rightarrow> s2 \<rbrakk>
            \<Longrightarrow> s0 -c1;c2\<rightarrow> s2"

    IfTrue:  "\<lbrakk> b s;  s -c1\<rightarrow> t \<rbrakk> \<Longrightarrow> s -IF b THEN c1 ELSE c2\<rightarrow> t"
    IfFalse: "\<lbrakk> \<not>b s; s -c2\<rightarrow> t \<rbrakk> \<Longrightarrow> s -IF b THEN c1 ELSE c2\<rightarrow> t"

    WhileFalse: "\<not>b s \<Longrightarrow> s -WHILE b DO c\<rightarrow> s"
    WhileTrue:  "\<lbrakk> b s; s -c\<rightarrow> t; t -WHILE b DO c\<rightarrow> u \<rbrakk>
                \<Longrightarrow> s -WHILE b DO c\<rightarrow> u"

  "s -body\<rightarrow> t \<Longrightarrow> s -CALL\<rightarrow> t"

    Local: "f s -c\<rightarrow> t \<Longrightarrow> s -LOCAL f; c; g\<rightarrow> g s t"


lemma [iff]: "(s -Do f\<rightarrow> t) = (t \<in> f s)"
by(auto elim: exec.elims intro:exec.intros)

lemma [iff]: "(s -c;d\<rightarrow> u) = (\<exists>t. s -c\<rightarrow> t \<and> t -d\<rightarrow> u)"
by(auto elim: exec.elims intro:exec.intros)

lemma [iff]: "(s -IF b THEN c ELSE d\<rightarrow> t) =
              (s -if b s then c else d\<rightarrow> t)"
apply(rule iffI)
 apply(auto elim: exec.elims intro:exec.intros)
apply(auto intro:exec.intros split:split_if_asm)
done

lemma unfold_while:
 "(s -WHILE b DO c\<rightarrow> u) =
  (s -IF b THEN c;WHILE b DO c ELSE Do(\<lambda>s. {s})\<rightarrow> u)"
by(auto elim: exec.elims intro:exec.intros split:split_if_asm)

lemma [iff]: "(s -CALL\<rightarrow> t) = (s -body\<rightarrow> t)"
by(blast elim: exec.elims intro:exec.intros)

lemma [iff]: "(s -LOCAL f; c; g\<rightarrow> u) = (\<exists>t. f s -c\<rightarrow> t \<and> u = g s t)"
by(fastsimp elim: exec.elims intro:exec.intros)

lemma [simp]: "\<not>b s \<Longrightarrow> s -WHILE b DO c\<rightarrow> s"
by(fast intro:exec.intros)

lemma WhileI: "\<lbrakk>b s; s -c\<rightarrow> t; t -WHILE b DO c\<rightarrow> u\<rbrakk> \<Longrightarrow> s -WHILE b DO c\<rightarrow> u"
by(fastsimp elim:exec.WhileTrue)
(*>*)

consts  execn    :: "(state \<times> com \<times> nat \<times> state)set"
abbreviation
 execn' :: "state \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"   ("_/ -_-_\<rightarrow>/ _" [50,0,0,50] 50)
 "s\<^isub>0 -c-n\<rightarrow> s\<^isub>1  \<equiv>  (s\<^isub>0,c,n,s\<^isub>1) \<in> execn"

text{*This semantics turns out not to be fine-grained
enough. The soundness proof for the Hoare logic below proceeds by
induction on the call depth during execution. To make this work we
define a second semantics \mbox{@{prop"s -c-n\<rightarrow> t"}} which expresses that the
execution uses at most @{term n} nested procedure invocations, where
@{term n} is a natural number. The rules are straightforward: @{term
n} is just passed around, except for procedure calls, where it is
decremented: *}

inductive execn
intros
  "t \<in> f s \<Longrightarrow> s -Do f-n\<rightarrow> t"

  "\<lbrakk> s0 -c1-n\<rightarrow> s1; s1 -c2-n\<rightarrow> s2 \<rbrakk> \<Longrightarrow> s0 -c1;c2-n\<rightarrow> s2"

  "\<lbrakk>  b s; s -c1-n\<rightarrow> t \<rbrakk> \<Longrightarrow> s -IF b THEN c1 ELSE c2-n\<rightarrow> t"
  "\<lbrakk> \<not>b s; s -c2-n\<rightarrow> t \<rbrakk> \<Longrightarrow> s -IF b THEN c1 ELSE c2-n\<rightarrow> t"

  (*<*)WhileFalse:(*>*)"\<not>b s \<Longrightarrow> s -WHILE b DO c-n\<rightarrow> s"
  (*<*)WhileTrue:(*>*)"\<lbrakk>b s; s -c-n\<rightarrow> t; t -WHILE b DO c-n\<rightarrow> u\<rbrakk> \<Longrightarrow> s -WHILE b DO c-n\<rightarrow> u"

  "s -body-n\<rightarrow> t \<Longrightarrow> s -CALL-Suc n\<rightarrow> t"

  "f s -c-n\<rightarrow> t \<Longrightarrow> s -LOCAL f; c; g-n\<rightarrow> g s t"


lemma [iff]: "(s -Do f-n\<rightarrow> t) = (t \<in> f s)"
by(auto elim: execn.elims intro:execn.intros)

lemma [iff]: "(s -c1;c2-n\<rightarrow> u) = (\<exists>t. s -c1-n\<rightarrow> t \<and> t -c2-n\<rightarrow> u)"
by(best elim: execn.elims intro:execn.intros)

lemma [iff]: "(s -IF b THEN c ELSE d-n\<rightarrow> t) =
              (s -if b s then c else d-n\<rightarrow> t)"
apply auto
apply(blast elim: execn.elims intro:execn.intros)+
done

lemma [iff]: "(s -CALL- 0\<rightarrow> t) = False"
by(blast elim: execn.elims intro:execn.intros)

lemma [iff]: "(s -CALL-Suc n\<rightarrow> t) = (s -body-n\<rightarrow> t)"
by(blast elim: execn.elims intro:execn.intros)


lemma [iff]: "(s -LOCAL f; c; g-n\<rightarrow> u) = (\<exists>t. f s -c-n\<rightarrow> t \<and> u = g s t)"
by(auto elim: execn.elims intro:execn.intros)


text{*\noindent By induction on @{prop"s -c-m\<rightarrow> t"} we show
monotonicity w.r.t.\ the call depth:*}

lemma exec_mono[rule_format]: "s -c-m\<rightarrow> t \<Longrightarrow> \<forall>n. m \<le> n \<longrightarrow> s -c-n\<rightarrow> t"
apply(erule execn.induct)
         apply(blast)
        apply(blast)
       apply(simp)
      apply(simp)
     apply(simp add:execn.intros)
    apply(blast intro:execn.intros)
   apply(clarify)
   apply(rename_tac m)
   apply(case_tac m)
    apply simp
   apply simp
  apply blast
done

text{*\noindent With the help of this lemma we prove the expected
relationship between the two semantics: *}

lemma exec_iff_execn: "(s -c\<rightarrow> t) = (\<exists>n. s -c-n\<rightarrow> t)"
apply(rule iffI)
apply(erule exec.induct)
           apply blast
          apply clarify
          apply(rename_tac m n)
          apply(rule_tac x = "max m n" in exI)
          apply(fastsimp intro:exec.intros exec_mono simp add:max_def)
         apply fastsimp
        apply fastsimp
       apply(blast intro:execn.intros)
      apply clarify
      apply(rename_tac m n)
      apply(rule_tac x = "max m n" in exI)
      apply(fastsimp elim:execn.WhileTrue exec_mono simp add:max_def)
     apply blast
    apply blast
apply(erule exE, erule execn.induct)
         apply blast
        apply blast
       apply fastsimp
      apply fastsimp
     apply(erule exec.WhileFalse)
    apply(blast intro: exec.intros)
   apply blast
  apply blast
done


lemma while_lemma[rule_format]:
"s -w-n\<rightarrow> t \<Longrightarrow> !b c. w = WHILE b DO c \<and> P s \<and>
                    (!s s'. P s \<and> b s \<and> s -c-n\<rightarrow> s' \<longrightarrow> P s') \<longrightarrow> P t \<and> \<not>b t"
apply(erule execn.induct)
apply clarify+
defer
apply clarify+
apply(subgoal_tac "P t")
apply blast
apply blast
done

lemma while_rule:
 "\<lbrakk>s -WHILE b DO c-n\<rightarrow> t; P s; \<And>s s'. \<lbrakk>P s; b s; s -c-n\<rightarrow> s' \<rbrakk> \<Longrightarrow> P s'\<rbrakk>
  \<Longrightarrow> P t \<and> \<not>b t"
apply(drule while_lemma)
prefer 2 apply assumption
apply blast
done

end