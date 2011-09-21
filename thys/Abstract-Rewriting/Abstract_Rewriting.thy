(*  Title:       Abstract Rewriting
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 Rene Thiemann       <rene.tiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and Rene Thiemann
    License:     LGPL
*)

(*
Copyright 2010 Christian Sternagel and René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

header {* Abstract Rewrite Systems *}

theory Abstract_Rewriting
imports 
  Util 
  "../Transitive-Closure/Transitive_Closure_Impl"
  "../Regular-Sets/Regexp_Method"
begin

text {*
An abstract rewrite system (ARS) is a binary endorelation, i.e.,
a binary relation where domain and codomain coincide.
*}
type_synonym
  'a ars = "('a \<times> 'a) set"

subsection {* Definitions *}

text {*
Two elements are \emph{joinable} (and hence in the joinability relation)
w.r.t.\ @{term "A"}, iff they have a common reduct.
*}
definition
  join :: "'a ars \<Rightarrow> 'a ars"
where
  "join A \<equiv> A^* O (A\<inverse>)^*"

text {*
Two elements are \emph{meetable} (and hence in the meetability relation)
w.r.t.\ @{term "A"}, iff they have a common ancestor.
*}
definition
  meet :: "'a ars \<Rightarrow> 'a ars"
where
  "meet A \<equiv> (A^-1)^* O A^*"

text {*
The \emph{symmetric closure} of a relation allows steps in both directions.
*}
abbreviation
  symcl :: "'a ars \<Rightarrow> 'a ars" ("(_^<->)" [1000] 999)
where
  "A^<-> \<equiv> A \<union> A^-1"

text {*
A \emph{conversion} is a (possibly empty) sequence of steps in the
symmetric closure.
*}
definition
  conversion :: "'a ars \<Rightarrow> 'a ars" ("(_^<->*)" [1000] 999)
where
  "A^<->* \<equiv> (A^<->)^*"

text {*
The set of \emph{normal forms} of an ARS constitutes all the elements
that do not have any successors.
*}
definition
  NF :: "'a ars \<Rightarrow> 'a set"
where
  "NF A \<equiv> {a. A `` {a} = {}}"

definition
  normalizability :: "'a ars \<Rightarrow> 'a ars" ("(_^!)" [1000] 999)
where
  "A^! \<equiv> {(a, b). (a, b) \<in> A^* \<and> b \<in> NF A}"

notation (xsymbols)
  join ("(_\<^sup>\<down>)" [1000] 999) and
  meet ("(_\<^sup>\<up>)" [1000] 999) and
  symcl ("(_\<^sup>\<leftrightarrow>)" [1000] 999) and
  conversion ("(_\<^bsup>\<leftrightarrow>*\<^esup>)" [1000] 999) and
  normalizability ("(_\<^sup>!)" [1000] 999)


lemma no_step: assumes "A `` {a} = {}" shows "a \<in> NF A" using assms by (auto simp: NF_def)

lemma join_I: "(a, c) \<in> A^* \<Longrightarrow> (b, c) \<in> A^* \<Longrightarrow> (a, b) \<in> A\<^sup>\<down>"
by (auto simp: join_def rtrancl_converse)

lemma join_I_left: "(a, b) \<in> A^* \<Longrightarrow> (a, b) \<in> A\<^sup>\<down>" by (auto simp: join_def)

lemma join_I_right: "(b, a) \<in> A^* \<Longrightarrow> (a, b) \<in> A\<^sup>\<down>" by (rule join_I) auto

lemma join_E:
  assumes "(a, b) \<in> A\<^sup>\<down>" obtains c where "(a, c) \<in> A^*" and "(b, c) \<in> A^*"
using assms by (auto simp: join_def rtrancl_converse)

lemma join_D: "(a, b) \<in> A\<^sup>\<down> \<Longrightarrow> \<exists>c. (a, c) \<in> A^* \<and> (b, c) \<in> A^*" by (blast elim: join_E)

lemma meet_I: "(a, b) \<in> A^* \<Longrightarrow> (a, c) \<in> A^* \<Longrightarrow> (b, c) \<in> A\<^sup>\<up>"
by (auto simp: meet_def rtrancl_converse)

lemma meet_E:
  assumes "(b, c) \<in> A\<^sup>\<up>" obtains a where "(a, b) \<in> A^*" and "(a, c) \<in> A^*"
using assms by (auto simp: meet_def rtrancl_converse)

lemma meet_D: "(b, c) \<in> A\<^sup>\<up> \<Longrightarrow> \<exists>a. (a, b) \<in> A^* \<and> (a, c) \<in> A^*" by (blast elim: meet_E)

lemma conversion_I: "(a, b) \<in> (A\<^sup>\<leftrightarrow>)^* \<Longrightarrow> (a, b) \<in> A\<^bsup>\<leftrightarrow>*\<^esup>" by (simp add: conversion_def)

lemma conversion_refl[simp]: "(a, a) \<in> A\<^bsup>\<leftrightarrow>*\<^esup>" by (simp add: conversion_def)

lemma conversion_I': assumes "(a, b) \<in> A^*" shows "(a, b) \<in> A\<^bsup>\<leftrightarrow>*\<^esup>"
using assms proof (induct)
  case base thus ?case by simp
next
  case (step b c)
  hence "(b, c) \<in> A\<^sup>\<leftrightarrow>" by simp
  with `(a, b) \<in> A\<^bsup>\<leftrightarrow>*\<^esup>` show ?case unfolding conversion_def by (rule rtrancl.intros)
qed


lemma rtrancl_comp_trancl_conv: "r^* O r = r^+" by regexp

lemma trancl_mono_set: "r \<subseteq> s \<Longrightarrow> r^+ \<subseteq> s^+"
  using trancl_mono by auto

lemma trancl_o_refl_is_trancl: "r^+ O r^= = r^+" by regexp

lemma conversion_E: "(a, b) \<in> A\<^bsup>\<leftrightarrow>*\<^esup> \<Longrightarrow> ((a, b) \<in> (A\<^sup>\<leftrightarrow>)^* \<Longrightarrow> P) \<Longrightarrow> P"
by (simp add: conversion_def)

text {*
Later declarations are tried first for 'proof' and 'rule,' hence
the ``main'' introduction\,/\.elimination rules for constants should be
declared last.
*}
declare join_I_left[intro]
declare join_I_right[intro]
declare join_I[intro]
declare join_D[dest]
declare join_E[elim]

declare meet_I[intro]
declare meet_D[dest]
declare meet_E[elim]

declare conversion_I'[intro]
declare conversion_I[intro]
declare conversion_E[elim]


lemma conversion_trans: "trans (A\<^bsup>\<leftrightarrow>*\<^esup>)"
unfolding trans_def proof (intro allI impI)
  fix a b c assume "(a, b) \<in> A\<^bsup>\<leftrightarrow>*\<^esup>" and "(b, c) \<in> A\<^bsup>\<leftrightarrow>*\<^esup>"
  thus "(a, c) \<in> A^<->*" unfolding conversion_def
  proof (induct)
    case base thus ?case by simp
  next
    case (step b c')
    from `(b, c') \<in> A\<^sup>\<leftrightarrow>` and `(c', c) \<in> (A\<^sup>\<leftrightarrow>)^*`
      have "(b, c) \<in> (A\<^sup>\<leftrightarrow>)^*" by (rule converse_rtrancl_into_rtrancl)
    with step show ?case by simp
  qed
qed

lemma conversion_sym: "sym (A^<->*)"
unfolding sym_def proof (intro allI impI)
  fix a b assume "(a, b) \<in> A^<->*" thus "(b, a) \<in> A^<->*" unfolding conversion_def
  proof (induct)
    case base thus ?case by simp
  next
    case (step b c)
    hence "(c, b) \<in> A\<^sup>\<leftrightarrow>" by blast
    from `(c, b) \<in> A\<^sup>\<leftrightarrow>` and `(b, a) \<in> (A\<^sup>\<leftrightarrow>)^*`
      show ?case by (rule converse_rtrancl_into_rtrancl)
  qed
qed

lemma rtrancl_join_join:
  assumes "(a, b) \<in> A^*" and "(b, c) \<in> A\<^sup>\<down>" shows "(a, c) \<in> A\<^sup>\<down>"
proof -
  from `(b, c) \<in> A\<^sup>\<down>` obtain b' where "(b, b') \<in> A^*" and "(b', c) \<in> (A\<inverse>)^*"
    unfolding join_def by blast
  with `(a, b) \<in> A^*` have "(a, b') \<in> A^*" by simp
  with `(b', c) \<in> (A\<inverse>)^*` show ?thesis unfolding join_def by blast
qed

lemma join_rtrancl_join:
  assumes "(a, b) \<in> A\<^sup>\<down>" and "(c, b) \<in> A^*" shows "(a, c) \<in> A\<^sup>\<down>"
proof -
  from `(c, b) \<in> A^*` have "(b, c) \<in> (A\<inverse>)^*" unfolding rtrancl_converse by simp
  from `(a, b) \<in> A\<^sup>\<down>` obtain a' where "(a, a') \<in> A^*" and "(a', b) \<in> (A\<inverse>)^*"
    unfolding join_def by best
  with `(b, c) \<in> (A\<inverse>)^*` have "(a', c) \<in> (A\<inverse>)^*" by simp
  with `(a, a') \<in> A^*` show ?thesis unfolding join_def by blast
qed

lemma NF_I: "(\<And>b. (a, b) \<notin> A) \<Longrightarrow> a \<in> NF A" by (auto intro: no_step)

lemma NF_E: "a \<in> NF A \<Longrightarrow> ((a, b) \<notin> A \<Longrightarrow> P) \<Longrightarrow> P" by (auto simp: NF_def)

declare NF_I[intro]
declare NF_E[elim]

lemma NF_no_step: "a \<in> NF A \<Longrightarrow> \<forall>b. (a, b) \<notin> A" by auto

lemma NF_anti_mono: assumes "A \<subseteq> B" shows "NF B \<subseteq> NF A" using assms by auto

lemma NF_iff_no_step: "a \<in> NF A = (\<forall>b. (a, b) \<notin> A)" by auto

lemma NF_no_trancl_step: assumes "a \<in> NF A" shows "\<forall>b. (a, b) \<notin> A^+"
proof -
  from assms have "\<forall>b. (a, b) \<notin> A" by auto
  show ?thesis
  proof (intro allI notI)
    fix b assume "(a, b) \<in> A^+"
    thus False by (induct) (auto simp: `\<forall>b. (a, b) \<notin> A`)
   qed
qed

lemma NF_Id_on_fst_image[simp]: "NF (Id_on (fst ` A)) = NF A" by force

lemma fst_image_NF_Id_on[simp]: "fst ` R = Q \<Longrightarrow> NF (Id_on Q) = NF R" by force

lemma NF_empty[simp]: "NF {} = UNIV" by auto

lemma normalizability_I: "(a, b) \<in> A^* \<Longrightarrow> b \<in> NF A \<Longrightarrow> (a, b) \<in> A^!"
by (simp add: normalizability_def)

lemma normalizability_I': "(a, b) \<in> A^* \<Longrightarrow> (b, c) \<in> A^! \<Longrightarrow> (a, c) \<in> A^!"
by (auto simp add: normalizability_def)

lemma normalizability_E: "(a, b) \<in> A^! \<Longrightarrow> ((a, b) \<in> A^* \<Longrightarrow> b \<in> NF A \<Longrightarrow> P) \<Longrightarrow> P"
by (simp add: normalizability_def)

declare normalizability_I'[intro]
declare normalizability_I[intro]
declare normalizability_E[elim]


subsection {* Properties of ARSs *}

text {*
The following properties on (elements of) ARSs are defined: completeness,
Church-Rosser property, semi-completeness, strong normalization, unique normal forms,
Weak Church-Rosser property, and weak normalization. 
*}

definition
  CR_elt :: "'a ars \<Rightarrow> 'a \<Rightarrow> bool"
where
  "CR_elt A a \<equiv> \<forall>b c. (a, b) \<in> A^* \<and> (a, c) \<in> A^* \<longrightarrow> (b, c) \<in> A\<^sup>\<down>"

definition
  CR :: "'a ars \<Rightarrow> bool"
where
  "CR A \<equiv> \<forall>a. CR_elt A a"

definition
  SN_elt :: "'a ars \<Rightarrow> 'a \<Rightarrow> bool"
where
  "SN_elt A a \<equiv> \<not> (\<exists>S. S 0 = a \<and> (\<forall>i. (S i, S (Suc i)) \<in> A))"

definition
  SN :: "'a ars \<Rightarrow> bool"
where
  "SN A \<equiv> \<forall>a. SN_elt A a"

definition
  UNF_elt :: "'a ars \<Rightarrow> 'a \<Rightarrow> bool"
where
  "UNF_elt A a \<equiv> \<forall>b c. (a, b) \<in> A^! \<and> (a, c) \<in> A^! \<longrightarrow> b = c"

definition
  UNF :: "'a ars \<Rightarrow> bool"
where
  "UNF A \<equiv> \<forall>a. UNF_elt A a"

definition
  WCR_elt :: "'a ars \<Rightarrow> 'a \<Rightarrow> bool"
where
  "WCR_elt A a \<equiv> \<forall>b c. (a, b) \<in> A \<and> (a, c) \<in> A \<longrightarrow> (b, c) \<in> A\<^sup>\<down>"

definition
  WCR :: "'a ars \<Rightarrow> bool"
where
  "WCR A \<equiv> \<forall>a. WCR_elt A a"

definition
  WN_elt :: "'a ars \<Rightarrow> 'a \<Rightarrow> bool"
where
  "WN_elt A a \<equiv> \<exists>b. (a, b) \<in> A^!"

definition
  WN :: "'a ars \<Rightarrow> bool"
where
  "WN A \<equiv> \<forall>a. WN_elt A a"

lemmas CR_defs = CR_def CR_elt_def
lemmas SN_defs = SN_def SN_elt_def
lemmas UNF_defs = UNF_def UNF_elt_def
lemmas WCR_defs = WCR_def WCR_elt_def
lemmas WN_defs = WN_def WN_elt_def

lemma SN_def': "SN A \<equiv> \<not> (\<exists>S. \<forall>i. (S i, S (Suc i)) \<in> A)" by (simp add: SN_defs)

definition
  complete_elt :: "'a ars \<Rightarrow> 'a \<Rightarrow> bool"
where
  "complete_elt A a \<equiv> SN_elt A a \<and> CR_elt A a"

definition
  complete :: "'a ars \<Rightarrow> bool"
where
  "complete A \<equiv> \<forall>a. complete_elt A a"

definition
  semi_complete_elt :: "'a ars \<Rightarrow> 'a \<Rightarrow> bool"
where
  "semi_complete_elt A a \<equiv>  WN_elt A a \<and> CR_elt A a"

definition
  semi_complete :: "'a ars \<Rightarrow> bool"
where
  "semi_complete A \<equiv> \<forall>a. semi_complete_elt A a"

lemmas complete_defs = complete_def complete_elt_def
lemmas semi_complete_defs = semi_complete_def semi_complete_elt_def

text {* Unique normal forms with respect to conversion. *}
definition
  UNC :: "'a ars \<Rightarrow> bool"
where
  "UNC A \<equiv> \<forall>a b. a \<in> NF A \<and> b \<in> NF A \<and> (a, b) \<in> A^<->* \<longrightarrow> a = b"

lemma complete_elt_I:
  "SN_elt A a \<Longrightarrow> CR_elt A a \<Longrightarrow> complete_elt A a"
by (simp add: complete_defs)

lemma complete_elt_E:
  "complete_elt A a \<Longrightarrow> (SN_elt A a \<Longrightarrow> CR_elt A a \<Longrightarrow> P) \<Longrightarrow> P"
by (simp add: complete_defs)

lemma complete_I: "(\<And>a. SN_elt A a) \<Longrightarrow> (\<And>a. CR_elt A a) \<Longrightarrow> complete A"
by (simp add: complete_defs)

lemma complete_I': "(\<And>a. complete_elt A a) \<Longrightarrow> complete A"
by (simp add: complete_defs)

lemma complete_E: "complete A \<Longrightarrow> (SN A \<Longrightarrow> CR A \<Longrightarrow> P) \<Longrightarrow> P"
by (simp add: complete_defs SN_defs CR_defs)

lemma complete_E': "complete A \<Longrightarrow> (complete_elt A a \<Longrightarrow> P) \<Longrightarrow> P"
by (simp add: complete_defs)

lemma complete_E'': "complete A \<Longrightarrow> (SN_elt A a \<Longrightarrow> CR_elt A a \<Longrightarrow> P) \<Longrightarrow> P"
by (simp add: complete_defs)

lemma CR_elt_I:
  "(\<And>b c. (a, b) \<in> A^* \<Longrightarrow> (a, c) \<in> A^* \<Longrightarrow> (b, c) \<in> A\<^sup>\<down>) \<Longrightarrow> CR_elt A a"
by (simp add: CR_defs)

lemma CR_elt_E:
  "CR_elt A a \<Longrightarrow> ((b, c) \<in> A\<^sup>\<down> \<Longrightarrow> P) \<Longrightarrow> ((a, b) \<notin> A^* \<Longrightarrow> P) \<Longrightarrow> ((a, c) \<notin> A^* \<Longrightarrow> P) \<Longrightarrow> P"
unfolding CR_defs by blast

lemma CR_elt_D:
  "CR_elt A a \<Longrightarrow> (a, b) \<in> A^* \<Longrightarrow> (a, c) \<in> A^* \<Longrightarrow> (b, c) \<in> A\<^sup>\<down>"
by (blast elim: CR_elt_E)

lemma CR_I: "(\<And>a. CR_elt A a) \<Longrightarrow> CR A" by (simp add: CR_defs)

lemma CR_I': "(\<And>a b c. (a, b) \<in> A^* \<Longrightarrow> (a, c) \<in> A^* \<Longrightarrow> (b, c) \<in> A\<^sup>\<down>) \<Longrightarrow> CR A"
by (auto simp: CR_defs)

lemma CR_E: "CR A \<Longrightarrow> (CR_elt A a \<Longrightarrow> P) \<Longrightarrow> P"
by (simp add: CR_defs)

lemma CR_E':
  "CR A \<Longrightarrow> ((b, c) \<in> A\<^sup>\<down> \<Longrightarrow> P) \<Longrightarrow> ((a, b) \<notin> A^* \<Longrightarrow> P) \<Longrightarrow> ((a, c) \<notin> A^* \<Longrightarrow> P) \<Longrightarrow> P"
by (auto simp: CR_defs)

lemma CR_D: "CR A \<Longrightarrow> (a, b) \<in> A^* \<Longrightarrow> (a, c) \<in> A^* \<Longrightarrow> (b, c) \<in> A\<^sup>\<down>"
by (blast elim: CR_E')

lemma semi_complete_elt_I[intro]: "WN_elt A a \<Longrightarrow> CR_elt A a \<Longrightarrow> semi_complete_elt A a"
by (simp add: semi_complete_defs)

lemma semi_complete_elt_E[elim]:
  "semi_complete_elt A a \<Longrightarrow> (WN_elt A a \<Longrightarrow> CR_elt A a \<Longrightarrow> P) \<Longrightarrow> P"
by (simp add: semi_complete_defs)

lemma semi_complete_I: "(\<And>a. semi_complete_elt A a) \<Longrightarrow> semi_complete A"
by (simp add: semi_complete_defs)

lemma semi_complete_I': "(\<And>a. WN_elt A a) \<Longrightarrow> (\<And>a. CR_elt A a) \<Longrightarrow> semi_complete A"
by (simp add: semi_complete_defs)

lemma semi_complete_E:
  "semi_complete A \<Longrightarrow> (semi_complete_elt A a \<Longrightarrow> P) \<Longrightarrow> P"
by (simp add: semi_complete_defs)

lemma semi_complete_E':
  "semi_complete A \<Longrightarrow> (WN_elt A a \<Longrightarrow> CR_elt A a \<Longrightarrow> P) \<Longrightarrow> P"
by (simp add: semi_complete_defs)

lemma semi_complete_E'':
  "semi_complete A \<Longrightarrow> (WN A \<Longrightarrow> CR A \<Longrightarrow> P) \<Longrightarrow> P"
by (simp add: semi_complete_defs WN_defs CR_defs)

declare complete_elt_I[intro]
declare complete_elt_E[elim]
declare complete_I'[intro]
declare complete_I[intro]
declare complete_E''[elim]
declare complete_E'[elim]
declare complete_E[elim]

declare CR_elt_I[intro]
declare CR_elt_D[dest]
declare CR_elt_E[elim]
declare CR_I'[intro]
declare CR_I[intro]
declare CR_D[dest]
declare CR_E'[elim]
declare CR_E[elim]

declare semi_complete_I'[intro]
declare semi_complete_I[intro]
declare semi_complete_E''[elim]
declare semi_complete_E'[elim]
declare semi_complete_E[elim]

lemma UNC_I:
  "(\<And>a b. a \<in> NF A \<Longrightarrow> b \<in> NF A \<Longrightarrow> (a, b) \<in> A^<->* \<Longrightarrow> a = b) \<Longrightarrow> UNC A"
by (simp add: UNC_def)

lemma UNC_E:
  "\<lbrakk>UNC A; a = b \<Longrightarrow> P; a \<notin> NF A \<Longrightarrow> P; b \<notin> NF A \<Longrightarrow> P; (a, b) \<notin> A^<->* \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
unfolding UNC_def by blast

lemma UNF_elt_I: "(\<And>b c. (a, b) \<in> A^! \<Longrightarrow> (a, c) \<in> A^! \<Longrightarrow> b = c) \<Longrightarrow> UNF_elt A a"
by (simp add: UNF_defs)

lemma UNF_elt_E:
  "UNF_elt A a \<Longrightarrow> (b = c \<Longrightarrow> P) \<Longrightarrow> ((a, b) \<notin> A^! \<Longrightarrow> P) \<Longrightarrow> ((a, c) \<notin> A^! \<Longrightarrow> P) \<Longrightarrow> P"
unfolding UNF_elt_def by blast

lemma UNF_elt_D:
  "UNF_elt A a \<Longrightarrow> (a, b) \<in> A^! \<Longrightarrow> (a, c) \<in> A^! \<Longrightarrow> b = c"
by (blast elim: UNF_elt_E)

lemma UNF_I:
  "(\<And>a b c. (a, b) \<in> A^! \<Longrightarrow> (a, c) \<in> A^! \<Longrightarrow> b = c) \<Longrightarrow> UNF A"
by (auto simp: UNF_defs)

lemma UNF_I': "(\<And>a. UNF_elt A a) \<Longrightarrow> UNF A" by (simp add: UNF_defs)

lemma UNF_E: "UNF A \<Longrightarrow> (UNF_elt A a \<Longrightarrow> P) \<Longrightarrow> P" unfolding UNF_def by blast

lemma UNF_E': "\<lbrakk>UNF A; b = c \<Longrightarrow> P; (a, b) \<notin> A^! \<Longrightarrow> P; (a, c) \<notin> A^! \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
unfolding UNF_defs by blast

lemma UNF_D: "UNF A \<Longrightarrow> (a, b) \<in> A^! \<Longrightarrow> (a, c) \<in> A^! \<Longrightarrow> b = c"
by (blast elim: UNF_E')

declare UNC_I[intro]
declare UNC_E[elim]

declare UNF_elt_I[intro]
declare UNF_elt_D[dest]
declare UNF_elt_E[elim]

declare UNF_I'[intro]
declare UNF_I[intro]
declare UNF_D[dest]
declare UNF_E'[elim]
declare UNF_E[elim]

lemma SN_elt_I:
  assumes "\<And>S. \<lbrakk>S 0 = a; \<forall>i. (S i, S (Suc i)) \<in> A\<rbrakk> \<Longrightarrow> False" shows "SN_elt A a"
using assms unfolding SN_defs by blast

lemma SN_elt_E:
  assumes "SN_elt A a" and "\<not> (\<exists>S. S 0 = a \<and> (\<forall>i. (S i, S (Suc i)) \<in> A)) \<Longrightarrow> P"
  shows "P"
using assms unfolding SN_defs by simp

lemma not_SN_elt_E:
  assumes "\<not> SN_elt A a" and "\<And>S. \<lbrakk>S 0 = a; \<forall>i. (S i, S (Suc i)) \<in> A\<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms unfolding SN_defs by blast

(* Used by automatic methods like: auto, blast, ... *)
lemma SN_I: "(\<And>a. SN_elt A a) \<Longrightarrow> SN A" by (simp add: SN_defs)

(* This is used by single steps like: proof, rule, ... *)
lemma SN_I':
  assumes "\<And>S. \<forall>i. (S i, S (Suc i)) \<in> A \<Longrightarrow> False" shows "SN A"
using assms unfolding SN_defs by blast

lemma SN_E:
  assumes "SN A" and "SN_elt A a \<Longrightarrow> P" shows "P"
using assms unfolding SN_defs by simp

lemma SN_E':
  assumes "SN A" and "\<not> (\<exists>S. \<forall>i. (S i, S (Suc i)) \<in> A) \<Longrightarrow> P" shows "P"
using assms unfolding SN_defs by simp

lemma not_SN_E:
  assumes "\<not> SN A" and "\<And>S. \<forall>i. (S i, S (Suc i)) \<in> A \<Longrightarrow> P"
  shows "P"
using assms unfolding SN_defs by blast

declare SN_elt_I[intro]
declare SN_elt_E[elim]
declare not_SN_elt_E[Pure.elim, elim]
declare SN_I[intro]
declare SN_I'[Pure.intro, intro]
declare SN_E[elim]
declare SN_E'[elim]
declare not_SN_E[Pure.elim, elim]

lemma SN_imp_irreflexive: assumes "SN r" shows "(l,l) \<notin> r"
proof
  assume in_gr: "(l,l) \<in> r"
  with `SN r` show False unfolding SN_defs by auto
qed


lemma SN_nat_bounded: "SN {(x,y :: nat). x < y \<and> y \<le> b}" (is "SN ?R")
proof 
  fix f
  assume "\<forall> i. (f i, f (Suc i)) \<in> ?R"
  hence steps: "\<And> i. (f i, f (Suc i)) \<in> ?R" ..
  {
    fix i
    have inc: "f 0 + i \<le> f i"
    proof (induct i)
      case 0 thus ?case by auto
    next
      case (Suc i)
      have "f 0 + Suc i \<le> f i + Suc 0" using Suc by simp
      also have "... \<le> f (Suc i)" using steps[of i]
        by auto
      finally show ?case by simp
    qed
  }
  from this[of "Suc b"] steps[of b]
  show False by simp
qed


lemma WCR_elt_I: "(\<And>b c. (a, b) \<in> A \<Longrightarrow> (a,c) \<in> A \<Longrightarrow> (b, c) \<in> A\<^sup>\<down>) \<Longrightarrow> WCR_elt A a"
by (simp add: WCR_defs)

lemma WCR_elt_E:
  "WCR_elt A a \<Longrightarrow> ((b, c) \<in> A\<^sup>\<down> \<Longrightarrow> P) \<Longrightarrow> ((a, b) \<notin> A \<Longrightarrow> P) \<Longrightarrow> ((a, c) \<notin> A \<Longrightarrow> P) \<Longrightarrow> P"
unfolding WCR_elt_def by blast

lemma WCR_elt_D:
  "WCR_elt A a \<Longrightarrow> (a, b) \<in> A \<Longrightarrow> (a, c) \<in> A \<Longrightarrow> (b, c) \<in> A\<^sup>\<down>"
by (blast elim: WCR_elt_E)

lemma WCR_I: "(\<And>a. WCR_elt A a) \<Longrightarrow> WCR A" by (simp add: WCR_defs)

lemma WCR_I': "(\<And>a b c. (a, b) \<in> A \<Longrightarrow> (a, c) \<in> A \<Longrightarrow> (b, c) \<in> A\<^sup>\<down>) \<Longrightarrow> WCR A"
by (auto simp: WCR_defs)

lemma WCR_E: "WCR A \<Longrightarrow> (WCR_elt A a \<Longrightarrow> P) \<Longrightarrow> P"
by (simp add: WCR_defs)

lemma WCR_E':
  "WCR A \<Longrightarrow> ((b, c) \<in> A\<^sup>\<down> \<Longrightarrow> P) \<Longrightarrow> ((a, b) \<notin> A \<Longrightarrow> P) \<Longrightarrow> ((a, c) \<notin> A \<Longrightarrow> P) \<Longrightarrow> P"
unfolding WCR_defs by blast

lemma WCR_D:
  "WCR A \<Longrightarrow> (a, b) \<in> A \<Longrightarrow> (a, c) \<in> A \<Longrightarrow> (b, c) \<in> A\<^sup>\<down>"
by (blast elim: WCR_E')


lemma WN_elt_I: "(a, b) \<in> A^! \<Longrightarrow> WN_elt A a" by (auto simp: WN_defs)

lemma WN_elt_E: "WN_elt A a \<Longrightarrow> (\<And>b. (a, b) \<in> A^! \<Longrightarrow> P) \<Longrightarrow> P"
unfolding WN_defs by blast

lemma WN_elt_D: "WN_elt A a \<Longrightarrow> \<exists>b. (a, b) \<in> A^!"
by (blast elim: WN_elt_E)

lemma WN_I: "(\<And>a. WN_elt A a) \<Longrightarrow> WN A" by (simp add: WN_defs)

lemma WN_E: "WN A \<Longrightarrow> (WN_elt A a \<Longrightarrow> P) \<Longrightarrow> P"
by (simp add: WN_defs)

lemma WN_E': "WN A \<Longrightarrow> (\<And>b. (a, b) \<in> A^! \<Longrightarrow> P) \<Longrightarrow> P"
unfolding WN_defs by blast

lemma WN_D: "WN A \<Longrightarrow> \<exists>b. (a, b) \<in> A^!" by (blast elim: WN_E')

declare WCR_elt_I[intro]
declare WCR_elt_D[dest]
declare WCR_elt_E[elim]

declare WCR_I'[intro]
declare WCR_I[intro]
declare WCR_D[dest]
declare WCR_E'[elim]
declare WCR_E[elim]

declare WN_elt_I[intro]
declare WN_elt_D[dest]
declare WN_elt_E[elim]
declare WN_I[intro]
declare WN_D[dest]
declare WN_E'[elim]
declare WN_E[elim]

definition
  SN_rel :: "'a ars \<Rightarrow> 'a ars \<Rightarrow> 'a ars" 
where
  "SN_rel A B \<equiv> {(a, b) | a b. (a, b) \<in> A \<and> SN_elt B a}"

lemma SN_SN_rel_idemp[simp]: "SN (SN_rel A A)" by (auto simp: SN_rel_def SN_defs)

lemma step_preserves_SN_elt:
  assumes "(a ,b) \<in> A" and "SN_elt A a" shows "SN_elt A b"
proof
  fix S assume "S 0 = b" and seq: "\<forall>i. (S i, S (Suc i)) \<in> A"
  let ?T = "\<lambda>i. case i of 0 \<Rightarrow> a | Suc i \<Rightarrow> S i"
  have "\<forall>i. (?T i, ?T (Suc i)) \<in> A"
  proof
    fix i show "(?T i, ?T (Suc i)) \<in> A"
    proof (cases i)
      case 0 from `(a, b) \<in> A` show ?thesis by (simp add: `S 0 = b` 0)
    next
      case (Suc j)
      from seq have "(S j, S (Suc j)) \<in> A" ..
      thus ?thesis by (simp add: Suc)
    qed
  qed
  moreover have "?T 0 = a" by simp
  ultimately have "\<not> SN_elt A a" unfolding SN_defs by best
  with assms show False by simp
qed

lemma steps_preserve_SN_elt: "(a, b) \<in> A^* \<Longrightarrow> SN_elt A a \<Longrightarrow> SN_elt A b"
by (induct rule: rtrancl.induct) (auto simp: step_preserves_SN_elt)


lemma steps_preserve_SN_elt':
  assumes "(A,B) \<in> R\<^sup>+"
  and "SN_elt R A"
  shows "SN_elt R B"
using steps_preserve_SN_elt[OF trancl_into_rtrancl[OF assms(1)] assms(2)]
by assumption


(* belongs somewhere else *)
lemma subsetI2[Pure.intro]: "(\<And>x y. (x,y) \<in> A \<Longrightarrow> (x,y) \<in> B) \<Longrightarrow> A \<subseteq> B" by auto

lemma SN_rel_trancl_simp[simp]: "(SN_rel A A)^+ = SN_rel (A^+) A" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix a b assume "(a, b) \<in> ?lhs" thus "(a, b) \<in> ?rhs"
      unfolding SN_rel_def by (induct rule: trancl.induct) auto
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix a b assume "(a, b) \<in> ?rhs"
    hence "(a, b) \<in> A^+" and "SN_elt A a" unfolding SN_rel_def by auto
    thus "(a, b) \<in> ?lhs"
    proof (induct rule: trancl.induct)
      case (r_into_trancl x y) thus ?case unfolding SN_rel_def by auto
    next
      case (trancl_into_trancl a b c)
      hence IH: "(a, b) \<in> ?lhs" by auto
      from trancl_into_trancl have "(a, b) \<in> A^*" by auto
      from this and `SN_elt A a` have "SN_elt A b" by (rule steps_preserve_SN_elt)
      with `(b, c) \<in> A` have "(b, c) \<in> ?lhs" unfolding SN_rel_def by auto
      with IH show ?case by simp
    qed
  qed
qed

text {*
Infinite sequences over elements of type @{typ "'a"} are represented by functions
of type @{typ "nat \<Rightarrow> 'a"}.
*}
type_synonym
  'a iseq = "nat \<Rightarrow> 'a"

lemma SN_imp_WN: assumes "SN A" shows "WN A"
proof -
  from `SN A` have "wf (A^-1)" by (simp add: SN_defs wf_iff_no_infinite_down_chain)
  show "WN A"
  proof
    fix a
    show "WN_elt A a" unfolding WN_defs normalizability_def NF_def Image_def
      by (rule wfE_min[OF `wf (A^-1)`, of a "A^* `` {a}", simplified])
        (auto intro: rtrancl_into_rtrancl)
  qed
qed

lemma UNC_imp_UNF:
 assumes "UNC r" shows "UNF r"
proof - {
 fix x y z assume "(x,y) \<in> r^!" and "(x,z) \<in> r^!"
 hence "(x,y) \<in> r^*" and "(x,z) \<in> r^*" and "y \<in> NF r" and "z \<in> NF r" by auto
 hence "(x,y) \<in> r^<->*" and "(x,z) \<in> r^<->*" by (auto intro: conversion_I')
 hence "(z,x) \<in> r^<->*" using conversion_sym unfolding sym_def by best
 with `(x,y) \<in> r^<->*` have "(z,y) \<in> r^<->*" using conversion_trans unfolding trans_def by best
 with `z \<in> NF r` and `y \<in> NF r` have "z = y" using assms by auto
} thus ?thesis by auto
qed

lemma join_NF_imp_eq:
 assumes "(x,y) \<in> r\<^sup>\<down>" and "x \<in> NF r" and "y \<in> NF r"
 shows "x = y"
proof -
 from `(x,y) \<in> r\<^sup>\<down>` obtain z where "(x,z)\<in>r^*" and "(z,y)\<in>(r\<inverse>)^*" unfolding join_def by auto
 hence "(y,z) \<in> r^*" unfolding rtrancl_converse by simp
 from `x \<in> NF r` have "(x,z) \<notin> r^+" using NF_no_trancl_step by best
 hence "x = z" using rtranclD[OF `(x,z) \<in> r^*`] by auto
 from `y \<in> NF r` have "(y,z) \<notin> r^+" using NF_no_trancl_step by best
 hence "y = z" using rtranclD[OF `(y,z) \<in> r^*`] by auto
 with `x = z` show ?thesis by simp
qed

lemma CR_iff_meet_subset_join: "CR r = (r\<^sup>\<up> \<subseteq> r\<^sup>\<down>)"
proof
 assume "CR r" show "r\<^sup>\<up> \<subseteq> r\<^sup>\<down>"
 proof (rule subsetI2)
  fix x y assume "(x,y) \<in> r\<^sup>\<up>"
  then obtain z where "(z,x) \<in> r^*" and "(z,y) \<in> r^*" using meet_D by best
  with `CR r` show "(x,y) \<in> r\<^sup>\<down>" by (auto simp: CR_defs)
 qed
next
 assume "r\<^sup>\<up> \<subseteq> r\<^sup>\<down>" {
  fix x y z assume "(x,y) \<in> r^*" and "(x,z) \<in> r^*"
  hence "(y,z) \<in> r\<^sup>\<up>" unfolding meet_def rtrancl_converse by auto
  with `r\<^sup>\<up> \<subseteq> r\<^sup>\<down>` have "(y,z) \<in> r\<^sup>\<down>" by auto
 } thus "CR r" by (auto simp: CR_defs)
qed

lemma CR_divergence_imp_join:
  assumes "CR r" and "(x,y) \<in> r^*" and "(x,z) \<in> r^*"
  shows "(y,z) \<in> r\<^sup>\<down>"
using assms by auto

lemma join_imp_conversion: "r\<^sup>\<down> \<subseteq> r^<->*"
proof
  fix x z assume "(x,z) \<in> r\<^sup>\<down>"
  then obtain y where "(x,y) \<in> r^*" and "(z,y) \<in> r^*" by auto
  hence "(x,y) \<in> r^<->*" and "(z,y) \<in> r^<->*" by (auto intro: conversion_I')
  from `(z,y) \<in> r^<->*` have "(y,z) \<in> r^<->*" using conversion_sym unfolding sym_def by best
  with `(x,y) \<in> r^<->*` show "(x,z) \<in> r^<->*" using conversion_trans unfolding trans_def by best
qed

lemma meet_imp_conversion: "r\<^sup>\<up> \<subseteq> r^<->*"
proof (rule subsetI2)
  fix y z assume "(y,z) \<in> r\<^sup>\<up>"
  then obtain x where "(x,y) \<in> r^*" and "(x,z) \<in> r^*" by auto
  hence "(x,y) \<in> r^<->*" and "(x,z) \<in> r^<->*" by (auto intro: conversion_I')
  from `(x,y) \<in> r^<->*` have "(y,x) \<in> r^<->*" using conversion_sym unfolding sym_def by best
  with `(x,z) \<in> r^<->*` show "(y,z) \<in> r^<->*" using conversion_trans unfolding trans_def by best
qed

lemma CR_imp_UNF: assumes "CR r" shows "UNF r"
proof - {
fix x y z assume "(x,y) \<in> r^!" and "(x,z) \<in> r^!"
  hence "(x,y) \<in> r^*" and "y \<in> NF r" and "(x,z) \<in> r^*" and "z \<in> NF r"
    unfolding normalizability_def by auto
  from assms and `(x,y) \<in> r^*` and `(x,z) \<in> r^*` have "(y,z) \<in> r\<^sup>\<down>"
    by (rule CR_divergence_imp_join)
  from this and `y \<in> NF r` and `z \<in> NF r` have "y = z" by (rule join_NF_imp_eq)
} thus ?thesis by auto
qed

lemma CR_iff_conversion_imp_join: "CR r = (r^<->* \<subseteq> r\<^sup>\<down>)"
proof (intro iffI subsetI2)
  fix x y assume "CR r" and "(x,y) \<in> r^<->*"
  then obtain n where "(x,y) \<in> (r\<^sup>\<leftrightarrow>)^^n" unfolding conversion_def rtrancl_is_UN_rel_pow by auto
  thus "(x,y) \<in> r\<^sup>\<down>"
  proof (induct n arbitrary: x)
    case 0
    assume "(x,y) \<in> r\<^sup>\<leftrightarrow> ^^ 0" hence "x = y" by simp
    show ?case unfolding `x = y` by auto
  next
    case (Suc n)
    from `(x,y) \<in> r\<^sup>\<leftrightarrow> ^^ Suc n` obtain  z where "(x,z) \<in> r\<^sup>\<leftrightarrow>" and "(z,y) \<in> r\<^sup>\<leftrightarrow> ^^ n"
      using rel_pow_Suc_D2 by best
    with Suc have "(z,y) \<in> r\<^sup>\<down>" by simp
    from `(x,z) \<in> r\<^sup>\<leftrightarrow>` show ?case
    proof
      assume "(x,z) \<in> r" with `(z,y) \<in> r\<^sup>\<down>` show ?thesis by (auto intro: rtrancl_join_join)
    next
      assume "(x,z) \<in> r^-1"
      hence "(z,x) \<in> r^*" by simp
      from `(z,y) \<in> r\<^sup>\<down>` obtain z' where "(z,z') \<in> r^*" and "(y,z') \<in> r^*" by auto
      from `CR r` and `(z,x) \<in> r^*` and `(z,z') \<in> r^*` have "(x,z') \<in> r\<^sup>\<down>"
        by (rule CR_divergence_imp_join)
      then obtain x' where "(x,x') \<in> r^*" and "(z',x') \<in> r^*" by auto
      with `(y,z') \<in> r^*` show ?thesis by auto
    qed
  qed
next
  assume "r^<->* \<subseteq> r\<^sup>\<down>" thus "CR r" unfolding CR_iff_meet_subset_join
    using meet_imp_conversion by auto
qed

lemma CR_imp_conversion_iff_join: assumes "CR r" shows "r^<->* = r\<^sup>\<down>"
proof
  show "r^<->* \<subseteq> r\<^sup>\<down>" using CR_iff_conversion_imp_join assms by auto
next
  show "r\<^sup>\<down> \<subseteq> r^<->*" by (rule join_imp_conversion)
qed

lemma join_sym: "sym (A\<^sup>\<down>)" unfolding sym_def by auto

lemma CR_join_left_I:
  assumes "CR r" and "(x,y) \<in> r^*" and "(x,z) \<in> r\<^sup>\<down>" shows "(y,z) \<in> r\<^sup>\<down>"
proof -
  from `(x,z) \<in> r\<^sup>\<down>` obtain x' where "(x,x') \<in> r^*" and "(z,x') \<in> r\<^sup>\<down>" by auto
  from `CR r` and `(x,x') \<in> r^*` and `(x,y) \<in> r^*` have "(x,y) \<in> r\<^sup>\<down>" by auto
  hence "(y,x) \<in> r\<^sup>\<down>" using join_sym unfolding sym_def by best
  from `CR r` have "r^<->* = r\<^sup>\<down>" by (rule CR_imp_conversion_iff_join)
  from `(y,x) \<in> r\<^sup>\<down>` and `(x,z) \<in> r\<^sup>\<down>` show ?thesis using conversion_trans
    unfolding trans_def `r^<->* = r\<^sup>\<down>`[symmetric] by best
qed

lemma CR_join_right_I:
 assumes "CR r" and "(x,y) \<in> r\<^sup>\<down>" and "(y,z) \<in> r^*" shows "(x,z) \<in> r\<^sup>\<down>"
proof -
  have "r^<->* = r\<^sup>\<down>" by (rule CR_imp_conversion_iff_join[OF `CR r`])
  from `(y,z) \<in> r^*` have "(y,z) \<in> r^<->*" by (auto intro: conversion_I')
  with `(x,y) \<in> r\<^sup>\<down>` show ?thesis unfolding `r^<->* = r\<^sup>\<down>`[symmetric] using conversion_trans
    unfolding trans_def by fast
qed

lemma NF_not_suc: assumes "(x,y) \<in> r^*" and "x \<in> NF r" shows "x = y"
proof -
  from `x \<in> NF r` have "\<forall>y. (x,y) \<notin> r" using NF_no_step by auto
  hence "x \<notin> Domain r" unfolding Domain_def by simp
  from `(x,y) \<in> r^*` show ?thesis unfolding Not_Domain_rtrancl[OF `x \<notin> Domain r`] by simp
qed

lemma semi_complete_imp_conversion_iff_same_NF:
  assumes "semi_complete r"
  shows "((x,y) \<in> r^<->*) = (\<forall>u v. (x,u) \<in> r^! \<and> (y,v) \<in> r^! \<longrightarrow> u = v)"
proof -
  from assms have "WN r" and "CR r" unfolding semi_complete_defs by auto
  hence "r^<->* = r\<^sup>\<down>" using CR_imp_conversion_iff_join by auto
  show ?thesis
  proof
    assume "(x,y) \<in> r^<->*"
    from `(x,y) \<in> r^<->*` have "(x,y) \<in> r\<^sup>\<down>" unfolding `r^<->* = r\<^sup>\<down>` .
    show "\<forall>u v. (x,u) \<in> r^! \<and> (y,v) \<in> r^! \<longrightarrow> u = v"
    proof (intro allI impI, elim conjE)
      fix u v assume "(x,u) \<in> r^!" and "(y,v) \<in> r^!"
      hence "(x,u) \<in> r^*" and "(y,v) \<in> r^*" and "u \<in> NF r" and "v \<in> NF r" by auto
      from `CR r` and `(x,u) \<in> r^*` and `(x,y) \<in> r\<^sup>\<down>` have "(u,y) \<in> r\<^sup>\<down>"
        by (auto intro: CR_join_left_I)
      hence "(y,u) \<in> r\<^sup>\<down>" using join_sym unfolding sym_def by best
      with `(x,y) \<in> r\<^sup>\<down>` have "(x,u) \<in> r\<^sup>\<down>" unfolding `r^<->* = r\<^sup>\<down>`[symmetric]
        using conversion_trans unfolding trans_def by best
      from `CR r` and `(x,y) \<in> r\<^sup>\<down>` and `(y,v) \<in> r^*` have "(x,v) \<in> r\<^sup>\<down>"
        by (auto intro: CR_join_right_I)
      hence "(v,x) \<in> r\<^sup>\<down>" using join_sym unfolding sym_def by best
      with `(x,u) \<in> r\<^sup>\<down>` have "(v,u) \<in> r\<^sup>\<down>" unfolding `r^<->* = r\<^sup>\<down>`[symmetric]
        using conversion_trans unfolding trans_def by best
      then obtain v' where "(v,v') \<in> r^*" and "(u,v') \<in> r^*" by auto
      from `(u,v') \<in> r^*` and `u \<in> NF r` have "u = v'" by (rule NF_not_suc)
      from `(v,v') \<in> r^*` and `v \<in> NF r` have "v = v'" by (rule NF_not_suc)
      thus "u = v" unfolding `u = v'` by simp
    qed
  next
    assume equal_NF:"\<forall>u v. (x,u) \<in> r^! \<and> (y,v) \<in> r^! \<longrightarrow> u = v"
    from `WN r` obtain u where "(x,u) \<in> r^!" by best
    from `WN r` obtain v where "(y,v) \<in> r^!" by best
    from `(x,u) \<in> r^!` and `(y,v) \<in> r^!` have "u = v" using equal_NF by simp
    from `(x,u) \<in> r^!` and `(y,v) \<in> r^!` have "(x,v) \<in> r^*" and "(y,v) \<in> r^*"
      unfolding `u = v` by auto
    hence "(x,v) \<in> r^<->*" and "(y,v) \<in> r^<->*" by (auto intro: conversion_I')
    from `(y,v) \<in> r^<->*` have "(v,y) \<in> r^<->*" using conversion_sym unfolding sym_def by best
    with `(x,v) \<in> r^<->*` show "(x,y) \<in> r^<->*" using conversion_trans unfolding trans_def by best
  qed
qed

lemma CR_imp_UNC: assumes "CR r" shows "UNC r"
proof - {
  fix x y assume "x \<in> NF r" and "y \<in> NF r" and "(x,y) \<in> r^<->*"
  have "r^<->* = r\<^sup>\<down>" by (rule CR_imp_conversion_iff_join[OF assms])
  from `(x,y) \<in> r^<->*` have "(x,y) \<in> r\<^sup>\<down>" unfolding `r^<->* = r\<^sup>\<down>` by simp
  then obtain x' where "(x,x') \<in> r^*" and "(y,x') \<in> r^*" by best
  from `(x,x') \<in> r^*` and `x \<in> NF r` have "x = x'" by (rule NF_not_suc)
  from `(y,x') \<in> r^*` and `y \<in> NF r` have "y = x'" by (rule NF_not_suc)
  hence "x = y" unfolding `x = x'` by simp
} thus ?thesis by auto
qed

lemma WN_UNF_imp_CR: assumes "WN r" and "UNF r" shows "CR r"
proof - {
  fix x y z assume "(x,y) \<in> r^*" and "(x,z) \<in> r^*"
  from assms obtain y' where "(y,y') \<in> r^!" unfolding WN_defs by best
  with `(x,y) \<in> r^*` have "(x,y') \<in> r^!" by (auto intro: normalizability_I')
  from assms obtain z' where "(z,z') \<in> r^!" unfolding WN_defs by best
  with `(x,z) \<in> r^*` have "(x,z') \<in> r^!" by (auto intro: normalizability_I')
  with `(x,y') \<in> r^!` have "y' = z'" using `UNF r` unfolding UNF_defs by auto
  from `(y,y') \<in> r^!` and `(z,z') \<in> r^!` have "(y,z) \<in> r\<^sup>\<down>" unfolding `y' = z'` by auto
} thus ?thesis by (auto intro: CR_I')
qed

definition diamond :: "'a ars \<Rightarrow> bool" ("\<diamond>") where "\<diamond> r \<equiv> (r\<inverse> O r) \<subseteq> (r O r\<inverse>)"

lemma diamond_I[intro]: "(r\<inverse> O r) \<subseteq> (r O r\<inverse>) \<Longrightarrow> \<diamond> r" unfolding diamond_def by simp

lemma diamond_E[elim]: "\<diamond> r \<Longrightarrow> ((r\<inverse> O r) \<subseteq> (r O r\<inverse>) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding diamond_def by simp

lemma diamond_imp_semi_confluence: assumes "\<diamond> r" shows "(r\<inverse> O r^*) \<subseteq> r\<^sup>\<down>"
proof (rule subsetI2)
  fix y z assume "(y,z) \<in>  r\<inverse> O r^*"
  then obtain x where "(x,y) \<in> r" and "(x,z) \<in> r^*" by best
  then obtain n where "(x,z) \<in> r^^n" using rtrancl_imp_UN_rel_pow by best
  with `(x,y) \<in> r` show "(y,z) \<in> r\<^sup>\<down>"
  proof (induct n arbitrary: x z y)
    case 0 thus ?case by auto
  next
    case (Suc n)
    from `(x,z) \<in> r^^Suc n` obtain x' where "(x,x') \<in> r" and "(x',z) \<in> r^^n"
      using rel_pow_Suc_D2 by best
    with `(x,y) \<in> r` have "(y,x') \<in> (r\<inverse> O r)" by auto
    with `\<diamond> r` have "(y,x') \<in> (r O r\<inverse>)" by auto
    then obtain y' where "(x',y') \<in> r" and "(y,y') \<in> r" by best
    with Suc and `(x',z) \<in> r^^n` have "(y',z) \<in> r\<^sup>\<down>" by auto
    with `(y,y') \<in> r` show ?case by (auto intro: rtrancl_join_join)
  qed
qed

lemma semi_confluence_imp_CR: assumes "(r\<inverse> O r^*) \<subseteq> r\<^sup>\<down>" shows "CR r"
proof - {
  fix x y z assume "(x,y) \<in> r^*" and "(x,z) \<in> r^*"
  then obtain n where "(x,z) \<in> r^^n" using rtrancl_imp_UN_rel_pow by best
  with `(x,y) \<in> r^*` have "(y,z) \<in> r\<^sup>\<down>"
  proof (induct n arbitrary: x y z)
    case 0 thus ?case by auto
  next
    case (Suc n)
    from `(x,z) \<in> r^^Suc n` obtain x' where "(x,x') \<in> r" and "(x',z) \<in> r^^n"
      using rel_pow_Suc_D2 by best
    from `(x,x') \<in> r` and `(x,y) \<in> r^*` have "(x',y) \<in> (r\<inverse> O r^* )" by auto
    with assms have "(x',y) \<in> r\<^sup>\<down>" by auto
    then obtain y' where "(x',y') \<in> r^*" and "(y,y') \<in> r^*" by best
    with Suc and `(x',z) \<in> r^^n` have "(y',z) \<in> r\<^sup>\<down>" by simp
    then obtain u where "(z,u) \<in> r^*" and "(y',u) \<in> r^*" by best
    from `(y,y') \<in> r^*` and `(y',u) \<in> r^*` have "(y,u) \<in> r^*" by auto
    with `(z,u) \<in> r^*` show ?case by best
  qed
} thus ?thesis by (auto intro: CR_I')
qed
 
lemma diamond_imp_CR: assumes "\<diamond> r" shows "CR r"
  using assms by (rule diamond_imp_semi_confluence[THEN semi_confluence_imp_CR])

lemma diamond_imp_CR':
  assumes "\<diamond> s" and "r \<subseteq> s" and "s \<subseteq> r^*" shows "CR r"
  unfolding CR_iff_meet_subset_join
proof -
  from `\<diamond> s` have "CR s" by (rule diamond_imp_CR)
  hence "s\<^sup>\<up> \<subseteq> s\<^sup>\<down>" unfolding CR_iff_meet_subset_join by simp
  from `r \<subseteq> s` have "r^* \<subseteq> s^*" by (rule rtrancl_mono)
  from `s \<subseteq> r^*` have "s^* \<subseteq> (r^*)^*" by (rule rtrancl_mono)
  hence "s^* \<subseteq> r^*" by simp
  with `r^* \<subseteq> s^*` have "r^* = s^*" by simp
  show "r\<^sup>\<up> \<subseteq> r\<^sup>\<down>" unfolding meet_def join_def rtrancl_converse `r^* = s^*`
    unfolding rtrancl_converse[symmetric] meet_def[symmetric]
      join_def[symmetric] by (rule `s\<^sup>\<up> \<subseteq> s\<^sup>\<down>`)
qed

lemma SN_imp_minimal:
  assumes "SN A"
  shows "\<forall>Q x. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (z, y) \<in> A \<longrightarrow> y \<notin> Q)"
proof (rule ccontr)
  assume "\<not> (\<forall>Q x. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (z, y) \<in> A \<longrightarrow> y \<notin> Q))"
  then obtain Q x where "x \<in> Q" and "\<forall>z\<in>Q. \<exists>y. (z, y) \<in> A \<and> y \<in> Q" by auto
  hence "\<forall>z. \<exists>y. z \<in> Q \<longrightarrow> (z, y) \<in> A \<and> y \<in> Q" by auto
  hence "\<exists>f. \<forall>x. x \<in> Q \<longrightarrow> (x, f x) \<in> A \<and> f x \<in> Q" by (rule choice)
  then obtain f where a:"\<forall>x. x \<in> Q \<longrightarrow> (x,f x) \<in> A \<and> f x \<in> Q" (is "\<forall>x. ?P x") by best
  let ?S = "\<lambda>i. (f ^^ i) x"
  have "?S 0 = x" by simp
  have "\<forall>i. (?S i, ?S (Suc i)) \<in> A \<and> ?S (Suc i) \<in> Q"
  proof
    fix i show "(?S i, ?S (Suc i)) \<in> A \<and> ?S (Suc i) \<in> Q"
      by (induct i) (auto simp: `x \<in> Q` a)
  qed
  with `?S 0 = x` have "\<exists>S. S 0 = x \<and> (\<forall>i. (S i, S (Suc i)) \<in> A)" by fast
  with assms show False by auto
qed

lemma SN_elt_imp_elt_minimal:
  assumes "SN_elt r x"
  shows "\<forall>Q. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (z,y) \<in> r \<longrightarrow> y \<notin> Q)"
proof (rule ccontr)
  assume "\<not>(\<forall>Q. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (z,y) \<in> r \<longrightarrow> y \<notin> Q))"
  then obtain Q where "x \<in> Q" and "\<forall>z\<in>Q. \<exists>y. (z,y) \<in> r \<and> y \<in> Q" by auto
  hence "\<forall>z. \<exists>y. z \<in> Q \<longrightarrow> (z,y) \<in> r \<and> y \<in> Q" by auto
  hence "\<exists>f. \<forall>x. x \<in> Q \<longrightarrow> (x,f x) \<in> r \<and> f x \<in> Q" by (rule choice)
  then obtain f where a: "\<forall>x. x \<in> Q \<longrightarrow> (x,f x) \<in> r \<and> f x \<in> Q" (is "\<forall>x. ?P x") by best
  let ?S = "\<lambda>i. (f ^^ i) x"
  have "?S 0 = x" by simp
  have "\<forall>i. (?S i,?S(Suc i)) \<in> r \<and> ?S(Suc i) \<in> Q"
  proof
    fix i show "(?S i,?S(Suc i)) \<in> r \<and> ?S(Suc i) \<in> Q" by (induct i) (auto simp:`x \<in> Q` a)
  qed
  with `?S 0 = x` have "\<exists>S. S 0 = x \<and> (\<forall>i. (S i,S(Suc i)) \<in> r)" by fast
  with assms show False by auto
qed

lemma minimal_imp_wf:
  assumes "\<forall>Q x. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (z,y) \<in> r \<longrightarrow> y \<notin> Q)"
  shows "wf(r\<inverse>)"
proof (rule ccontr)
  assume "\<not> wf(r\<inverse>)"
  hence "\<exists>P. (\<forall>x. (\<forall>y. (x,y) \<in> r \<longrightarrow> P y) \<longrightarrow> P x) \<and> (\<exists>x. \<not> P x)" unfolding wf_def by simp
  then obtain P x where suc:"\<forall>x. (\<forall>y. (x,y) \<in> r \<longrightarrow> P y) \<longrightarrow> P x" and "\<not> P x" by auto
  let ?Q = "{x. \<not> P x}"
  from `\<not> P x` have "x \<in> ?Q" by simp
  from assms have "\<forall>x. x \<in> ?Q \<longrightarrow> (\<exists>z\<in>?Q. \<forall>y. (z,y) \<in> r \<longrightarrow> y \<notin> ?Q)" by (rule allE[where x = ?Q])
  with `x \<in> ?Q` obtain z where "z \<in> ?Q" and min:" \<forall>y. (z,y) \<in> r \<longrightarrow> y \<notin> ?Q" by best
  from `z \<in> ?Q` have "\<not> P z" by simp
  with suc obtain y where "(z,y) \<in> r" and "\<not> P y" by best
  hence "y \<in> ?Q" by simp
  with `(z,y) \<in> r` and min show False by simp
qed

lemmas SN_imp_wf = SN_imp_minimal[THEN minimal_imp_wf]

lemma wf_imp_SN: assumes "wf (A\<inverse>)" shows "SN A"
proof - {
  fix a
  let ?P = "\<lambda>a. \<not>(\<exists>S. S 0 = a \<and> (\<forall>i. (S i,S(Suc i)) \<in> A))"
  from `wf (A\<inverse>)` have "?P a"
  proof induct
    case (less a)
    hence IH: "\<And>b. (a,b) \<in> A \<Longrightarrow> ?P b" by auto
    show "?P a"
    proof (rule ccontr)
      assume "\<not> ?P a"
      then obtain S where "S 0 = a" and "\<forall>i. (S i,S(Suc i)) \<in> A" by auto
      hence "(S 0, S 1) \<in> A" by auto
      with IH have "?P (S 1)" unfolding `S 0 = a` by auto
      with `\<forall>i. (S i, S (Suc i)) \<in> A` show False by auto
    qed
  qed
  hence "SN_elt A a" unfolding SN_defs .
} thus ?thesis by auto
qed

lemma SN_iff_wf: "SN A = wf (A\<inverse>)" by (auto simp: SN_imp_wf wf_imp_SN)

lemma SN_induct:
assumes sn: "SN A" and step: "\<And>a. (\<And>b. (a,b) \<in> A \<Longrightarrow> P b) \<Longrightarrow> P a"
shows "P a"
using sn unfolding SN_iff_wf proof induct
  case (less a)
  with step show ?case by best
qed

(* The same as well-founded induction, but in the 'correct' direction. *)
lemmas SN_induct_rule = SN_induct[consumes 1, case_names IH, induct pred: SN]

(* and now SN_elt induction *)
lemma SN_elt_induct[consumes 1, case_names IH]:
  assumes SN: "SN_elt R s" and imp: "\<And>t. (\<And>u. (t, u) \<in> R \<Longrightarrow> P u) \<Longrightarrow> P t"
  shows "P s"
proof -
  let ?R = "SN_rel R R"
  let ?P = "\<lambda> t. SN_elt R t \<longrightarrow> P t"
  have "SN_elt R s \<longrightarrow> P s"
  proof (rule SN_induct[OF SN_SN_rel_idemp[of R], of ?P])
    fix a
    assume ind: "\<And> b. (a,b) \<in> ?R \<Longrightarrow> SN_elt R b \<longrightarrow> P b"
    show "SN_elt R a \<longrightarrow> P a"
    proof
      assume SN: "SN_elt R a"
      show "P a"
      proof (rule imp)
        fix b
        assume "(a,b) \<in> R"
        with SN step_preserves_SN_elt[OF this SN]
        show "P b" using ind[of b] unfolding SN_rel_def by auto
      qed
    qed
  qed
  with SN show ?thesis by simp
qed

(* link SN_elt to acc / accp *)
lemma accp_imp_SN_elt: assumes "accp g x" shows "SN_elt {(y,z). g z y} x"
using assms
proof (induct rule: accp.induct)
  case (accI x)
  show ?case
  proof
    fix f
    assume x: "f 0 = x" and steps: "\<forall> i. (f i, f (Suc i)) \<in> {a. (\<lambda>(y,z). g z y) a}"
    hence "g (f 1) x" by auto
    from accI(2)[OF this] steps x show False unfolding SN_elt_def by auto
  qed
qed

lemma SN_elt_imp_accp: assumes "SN_elt {(y,z). g z y} x" shows "accp g x"
using assms
proof (induct rule: SN_elt_induct) 
  case (IH x)
  show ?case
  proof
    fix y
    assume "g y x"
    with IH show "accp g y" by simp
  qed
qed

lemma SN_elt_conv_accp: "SN_elt {(y,z). g z y} = accp g"
  by (intro ext iffI, rule SN_elt_imp_accp, simp, rule accp_imp_SN_elt, simp)

lemma SN_elt_conv_acc: "SN_elt {(y,z). (z,y) \<in> r} = (\<lambda>x. x \<in> acc r)"
  unfolding SN_elt_conv_accp using accp_acc_eq .

lemma acc_imp_SN_elt: assumes "x \<in> acc r" shows "SN_elt {(y,z). (z,y) \<in> r} x"
  using assms
  unfolding SN_elt_conv_acc .

lemma SN_elt_imp_acc: assumes "SN_elt {(y,z). (z,y) \<in> r} x" shows "x \<in> acc r"
  using assms
  unfolding SN_elt_conv_acc .


subsection {* Newman's Lemma *}


lemma rtrancl_len_E[elim]: assumes "(x,y) \<in> r^*" obtains n where "(x,y) \<in> r^^n"
using rtrancl_imp_UN_rel_pow[OF assms] by best

lemma rel_pow_Suc_E2'[elim]:
assumes "(x,z) \<in> A^^Suc n" obtains y where "(x,y) \<in> A" and "(y,z) \<in> A^*"
proof -
  assume assm: "\<And>y. (x,y) \<in> A \<Longrightarrow> (y,z) \<in> A^* \<Longrightarrow> thesis"
  from rel_pow_Suc_E2[OF assms] obtain y where "(x,y) \<in> A" and "(y,z) \<in> A^^n" by auto
  hence "(y,z) \<in> A^*" using rel_pow_imp_rtrancl by auto
  from assm[OF `(x,y) \<in> A` this] show thesis .
qed

(*
The proof proceeds according to the following diagram:

x -->  s  -->* y
| WCR  |* IH   |*
t -->* u  -->* v 
|*     IH      |*
z ---------->* w
*)
lemma Newman: assumes "SN r" and "WCR r" shows "CR r"
proof
  fix x
  from `SN r` show "CR_elt r x"
  proof induct
    case (IH x) show ?case
    proof
      fix y z assume "(x,y) \<in> r^*" and "(x,z) \<in> r^*"
      from `(x,y) \<in> r^*` obtain m where "(x,y) \<in> r^^m" ..
      from `(x,z) \<in> r^*` obtain n where "(x,z) \<in> r^^n" ..
      show "(y,z) \<in> r\<^sup>\<down>"
      proof (cases n)
        case 0
        from `(x,z) \<in> r^^n` have eq: "x = z" by (simp add: 0)
        from `(x,y) \<in> r^*` show ?thesis unfolding eq ..
      next
        case (Suc n')
        from `(x,z) \<in> r^^n`[unfolded Suc] obtain t where "(x,t) \<in> r" and "(t,z) \<in> r^*" ..
        show ?thesis
        proof (cases m)
          case 0
          from `(x,y) \<in> r^^m` have eq: "x = y" by (simp add: 0)
          from `(x,z) \<in> r^*` show ?thesis unfolding eq ..
        next
          case (Suc m')
          from `(x,y) \<in> r^^m`[unfolded Suc] obtain s where "(x,s) \<in> r" and "(s,y) \<in> r^*" ..
          from `WCR r` and `(x,s) \<in> r` and `(x,t) \<in> r` have "(s,t) \<in> r\<^sup>\<down>" by auto
          then obtain u where "(s,u) \<in> r^*" and "(t,u) \<in> r^*" ..
          from IH[OF `(x,s) \<in> r`] have "CR_elt r s" .
          from this and `(s,u) \<in> r^*` and `(s,y) \<in> r^*` have "(u,y) \<in> r\<^sup>\<down>" by auto
          then obtain v where "(u,v) \<in> r^*" and "(y,v) \<in> r^*" ..
          from IH[OF `(x,t) \<in> r`] have "CR_elt r t" .
          moreover from `(t,u) \<in> r^*` and `(u,v) \<in> r^*` have "(t,v) \<in> r^*" by auto
          ultimately have "(z,v) \<in> r\<^sup>\<down>" using `(t,z) \<in> r^*` by auto
          then obtain w where "(z,w) \<in> r^*" and "(v,w) \<in> r^*" ..
          from `(y,v) \<in> r^*` and `(v,w) \<in> r^*` have "(y,w) \<in> r^*" by auto
          with `(z,w) \<in> r^*` show ?thesis by auto
        qed
      qed
    qed
  qed
qed
  
lemma all_reducts_SN_elt_imp_SN_elt:
  assumes "(\<And>b. (a, b) \<in> A \<Longrightarrow> SN_elt A b)"
  shows "SN_elt A a"
proof
  fix S assume "S 0 = a" and seq: "\<forall>i. (S i, S (Suc i)) \<in> A"
  hence "(S 0, S (Suc 0)) \<in> A" by auto
  with assms have "SN_elt A (S (Suc 0))" by (simp add: `S 0 = a`)
  moreover have "\<not> SN_elt A (S (Suc 0))"
  proof -
    have "S (Suc 0) = S (Suc 0)" ..
    moreover from seq have "\<forall>i. (S (Suc i), S (Suc (Suc i))) \<in> A" by simp
    ultimately show ?thesis by auto
  qed
  ultimately show False by simp
qed

lemma SN_elt_iff_all_reducts_SN_elt:
  "SN_elt R a = (\<forall> b. (a,b) \<in> R \<longrightarrow> SN_elt R b)" (is "?l = ?r")
proof
  assume ?l
  from step_preserves_SN_elt[OF _ this] show ?r by simp
next
  assume ?r
  thus ?l using all_reducts_SN_elt_imp_SN_elt by blast
qed


lemma SN_imp_SN_trancl: "SN R \<Longrightarrow> SN (R^+)"
unfolding SN_iff_wf by (rule wf_converse_trancl)

lemma SN_trancl_imp_SN: assumes "SN (R^+)" shows "SN R"
proof (rule ccontr)
  assume "\<not> SN R"
  then obtain s where "\<forall>i. (s i,s(Suc i)) \<in> R" unfolding SN_defs by auto
  hence "\<forall>i. (s i,s(Suc i)) \<in> R^+" by auto
  hence "\<not> SN(R^+)" unfolding SN_defs by auto
  with assms show False by simp
qed

lemma SN_trancl_SN_conv: "SN(R^+) = SN R"
  using SN_trancl_imp_SN[of R] SN_imp_SN_trancl[of R] by blast


(* --> HOL/Relation.thy (in Isabelle) *)
lemma converse_inv_image[simp]: "(inv_image R f)^-1 = inv_image (R^-1) f"
  unfolding inv_image_def converse_def by auto

lemma SN_inv_image: "SN R \<Longrightarrow> SN(inv_image R f)" unfolding SN_iff_wf by simp

lemma SN_subset: "SN R \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> SN R'" unfolding SN_defs by blast

lemma iseq_imp_condensed_iseq:
  assumes "\<forall>i. (S i, S (Suc i)) \<in> A" shows "\<forall>j>0. (S i, S (i + j)) \<in> A^^j"
proof (intro allI impI)
  fix j::nat assume "j > 0"
  thus "(S i, S (i + j)) \<in> A^^j"
  proof (induct j)
    case 0 show ?case by simp
  next
    case (Suc j) thus ?case
    proof (cases "j = 0")
      case True show ?thesis unfolding True using assms by simp
    next
      case False
      hence "j > 0" by simp
      with Suc have "(S i, S (i + j)) \<in> A^^j" by simp
      moreover from assms have "(S (i + j), S (Suc (i + j))) \<in> A" by simp
      ultimately show ?thesis by auto
    qed
  qed
qed
 
lemma SN_pow_imp_SN: assumes "SN (A^^Suc n)" shows "SN A"
proof (rule ccontr)
  assume "\<not> SN A"
  then obtain S where "\<forall>i. (S i, S(Suc i)) \<in> A" unfolding SN_defs by auto
  from iseq_imp_condensed_iseq[OF this]
    have step: "\<And>i. (S i, S (i + (Suc n))) \<in> A^^Suc n" by force
  let ?T = "\<lambda>i. S (i * (Suc n))"
  have "\<forall>i. (?T i, ?T (Suc i)) \<in> A^^Suc n"
  proof
    fix i show "(?T i, ?T (Suc i)) \<in> A^^Suc n" unfolding mult_Suc
      using step[of "i * Suc n"] unfolding add_commute .
  qed
  hence "\<not> SN (A^^Suc n)" unfolding SN_defs by best
  with assms show False by simp
qed

(* TODO: move to Isabelle Library? *)
lemma pow_Suc_subset_trancl: "R^^(Suc n) \<subseteq> R^+"
using trancl_power[of _ R] by blast

lemma SN_imp_SN_pow: assumes "SN R" shows "SN(R^^Suc n)"
  using SN_subset[where R="R^+",OF SN_imp_SN_trancl[OF assms] pow_Suc_subset_trancl] by simp
  
(* needed in HOL/Wellfounded.thy *)
lemma SN_pow: "SN R \<longleftrightarrow> SN(R ^^ Suc n)"
  by (rule iffI,rule SN_imp_SN_pow,assumption,rule SN_pow_imp_SN,assumption)

lemma SN_elt_trancl_imp_SN_elt:
  assumes "SN_elt (R\<^sup>+) a"
  shows "SN_elt R a"
using assms by (cases "\<exists>S. S 0 = a \<and> (\<forall>i. (S i, S (Suc i)) \<in> R)") auto

lemma SN_elt_imp_SN_elt_trancl: assumes "SN_elt A t" shows "SN_elt (A^+) t"
using assms proof (rule contrapos_pp)
  let ?A = "SN_rel A A"
  assume "\<not> SN_elt (A^+) t"
  then obtain S where "S 0 = t" and S: "\<forall>i. (S i, S(Suc i)) \<in> A^+"
    unfolding SN_elt_def by auto
  have "SN ?A" by (rule SN_SN_rel_idemp)
  hence "SN (?A^+)" by (rule SN_imp_SN_trancl)
  have "\<forall>i. (t, S i) \<in> A^*"
  proof
    fix i show "(t, S i) \<in> A^*"
    proof (induct i)
      case 0 show ?case unfolding `S 0 = t` by simp
    next
      case (Suc i)
      from S have "(S i, S(Suc i)) \<in> A^+" by simp
      with Suc show ?case by auto
    qed
  qed
  with assms have "\<forall>i. SN_elt A (S i)"
    using steps_preserve_SN_elt[of t _ A] by auto
  with S have "\<forall>i. (S i, S (Suc i)) \<in> ?A^+"
    unfolding SN_rel_trancl_simp unfolding SN_rel_def by auto
  hence "\<not> SN_elt (?A^+) t" unfolding `S 0 = t`[symmetric] unfolding SN_defs by auto
  with `SN (?A^+)` have "False" unfolding SN_defs by simp
  thus "\<not> SN_elt A t" by simp
qed

lemma SN_elt_trancl_is_SN_elt: "SN_elt (r^+) = SN_elt r"
  by (rule ext, insert SN_elt_trancl_imp_SN_elt[of r] SN_elt_imp_SN_elt_trancl[of r], auto)

text {* Restrict an ARS to elements of a given set. *}
definition
  "restrict" :: "'a ars \<Rightarrow> 'a set \<Rightarrow> 'a ars"
where
  "restrict r S \<equiv> {(x, y). x \<in> S \<and> y \<in> S \<and> (x, y) \<in> r}"

lemma SN_elt_restrict:
  assumes "SN_elt r x" shows "SN_elt (restrict r S) x" (is "SN_elt ?r x")
proof (rule ccontr)
  assume "\<not> SN_elt ?r x"
  hence "\<exists>S. S 0 = x \<and> (\<forall>i. (S i,S(Suc i)) \<in> ?r)" by auto
  hence "\<exists>S. S 0 = x \<and> (\<forall>i. (S i,S(Suc i)) \<in> r)" unfolding restrict_def by auto
  with `SN_elt r x` show False by auto
qed

lemma SN_restrict: "SN r \<Longrightarrow> SN(restrict r S)"
using SN_elt_restrict unfolding SN_def by best

lemma restrict_rtrancl: "(restrict r S)^* \<subseteq> r^*" (is "?r^* \<subseteq> r^*")
proof - {
  fix x y assume "(x,y) \<in> ?r^*" hence "(x,y) \<in> r^*" unfolding restrict_def by induct auto
} thus ?thesis by auto
qed

lemma WCR_SN_elt_imp_CR_elt: assumes "WCR r" and "SN_elt r x" shows "CR_elt r x"
proof -
  let ?S = "{y. (x,y) \<in> r^*}"
  let ?r = "restrict r ?S"
  have "\<forall>x. SN_elt ?r x"
  proof
    fix y have "y \<notin> ?S \<or> y \<in> ?S" by simp 
    thus "SN_elt ?r y"
    proof
      assume "y \<notin> ?S" thus ?thesis unfolding restrict_def by auto
    next
      assume "y \<in> ?S"
      hence "(x,y) \<in> r^*" by simp
      hence "SN_elt r y" using `SN_elt r x` by (rule steps_preserve_SN_elt)
      thus ?thesis by (rule SN_elt_restrict)
    qed
  qed
  hence "SN ?r" by auto
  {
    fix x y assume "(x,y) \<in> r^*" and "x \<in> ?S" and "y \<in> ?S"
    then obtain n where "(x,y) \<in> r^^n" and "x \<in> ?S" and "y \<in> ?S"
      using rtrancl_imp_UN_rel_pow by best
    hence "(x,y) \<in> ?r^*"
    proof (induct n arbitrary: x y)
      case 0 thus ?case by simp
    next
      case (Suc n)
      from `(x,y) \<in> r^^Suc n` obtain x' where "(x,x') \<in> r" and "(x',y) \<in> r^^n"
        using rel_pow_Suc_D2 by best
      hence "(x,x') \<in> r^*" by simp
      with `x \<in> ?S` have "x' \<in> ?S" by auto
      with Suc and `(x',y) \<in> r^^n` have "(x',y) \<in> ?r^*" by simp
      from `(x,x') \<in> r` and `x \<in> ?S` and `x' \<in> ?S` have "(x,x') \<in> ?r"
        unfolding restrict_def by simp
      with `(x',y) \<in> ?r^*` show ?case by simp
    qed
  }
  hence a:"\<forall>x y. (x,y) \<in> r^* \<and> x \<in> ?S \<and> y \<in> ?S \<longrightarrow> (x,y) \<in> ?r^*" by simp
  {
    fix x' y z assume "(x',y) \<in> ?r" and "(x',z) \<in> ?r"
    hence "x' \<in> ?S" and "y \<in> ?S" and "z \<in> ?S" and "(x',y) \<in> r" and "(x',z) \<in> r"
      unfolding restrict_def by auto
    with `WCR r` have "(y,z) \<in> r\<^sup>\<down>" by auto
    then obtain u where "(y,u) \<in> r^*" and "(z,u) \<in> r^*" by auto
    from `x' \<in> ?S` have "(x,x') \<in> r^*" by simp
    from `(x',y) \<in> r` have "(x',y) \<in> r^*" by auto
    with `(y,u) \<in> r^*` have "(x',u) \<in> r^*" by auto
    with `(x,x') \<in> r^*` have "(x,u) \<in> r^*" by simp
    hence "u \<in> ?S" by simp
    from `y \<in> ?S` and `u \<in> ?S` and `(y,u) \<in> r^*` have "(y,u) \<in> ?r^*" using a by auto
    from `z \<in> ?S` and `u \<in> ?S` and `(z,u) \<in> r^*` have "(z,u) \<in> ?r^*" using a by auto
    with `(y,u) \<in> ?r^*` have "(y,z) \<in> ?r\<^sup>\<down>" by auto
  }
  hence "WCR ?r" by (auto intro: WCR_I')
  have "CR ?r" using Newman[OF `SN ?r` `WCR ?r`] by simp
  {
    fix y z assume "(x,y) \<in> r^*" and "(x,z) \<in> r^*"
    hence "y \<in> ?S" and "z \<in> ?S" by auto
    have "x \<in> ?S" by simp
    from a and `(x,y) \<in> r^*` and `x \<in> ?S` and `y \<in> ?S` have "(x,y) \<in> ?r^*" by simp
    from a and `(x,z) \<in> r^*` and `x \<in> ?S` and `z \<in> ?S` have "(x,z) \<in> ?r^*" by simp
    with `CR ?r` and `(x,y) \<in> ?r^*` have "(y,z) \<in> ?r\<^sup>\<down>" by auto
    then obtain u where "(y,u) \<in> ?r^*" and "(z,u) \<in> ?r^*" by best
    hence "(y,u) \<in> r^*" and "(z,u) \<in> r^*" using restrict_rtrancl by auto
    hence "(y,z) \<in> r\<^sup>\<down>" by auto
  }
  thus ?thesis by auto
qed

lemma rtrancl_imp_seq:
  assumes "(x,y) \<in> r^*"
  shows "\<exists>S n. S 0 = x \<and> S n = y \<and> (\<forall>i<n. (S i,S(Suc i)) \<in> r)"
using assms proof (induct)
   case base thus ?case by auto
next
  case (step y z)
  then obtain S n where "S 0 = x" and "S n = y" and seq: "\<forall>i<n. (S i,S(Suc i)) \<in> r" by auto
  let ?m = "Suc n"
  let ?S = "\<lambda>i. if i = ?m then z else S i"
  have "?S ?m = z" by simp
  from `S 0 = x` have "?S 0 = x" by simp
  from seq have seq': "\<forall>i<n. (?S i,?S(Suc i)) \<in> r" by auto
  with `S n = y` and `(y,z) \<in> r` have "\<forall>i<?m. (?S i,?S(Suc i)) \<in> r" by auto
  with `?S 0 = x` and `?S ?m = z` show ?case by best
qed

lemma SN_elt_imp_normalizability: assumes "SN_elt r x" shows "\<exists>y. (x,y) \<in> r^!"
proof (rule ccontr)
  assume "\<not>(\<exists>y. (x,y) \<in> r^!)"
  hence A: "\<forall>y. (x,y) \<in> r^* \<longrightarrow> y \<notin> NF r" by auto
  hence "x \<notin> NF r" by auto
  let ?Q = "{z. (x,z) \<in> r^* \<and> z \<notin> NF r}"
  have "x \<in> ?Q" using `x \<notin> NF r` by simp
  have "\<forall>z\<in>?Q. \<exists>y. (z,y) \<in> r \<and> y \<in> ?Q"
  proof
    fix z assume "z \<in> ?Q"
    hence "(x,z) \<in> r^*" and "z \<notin> NF r" by auto
    then obtain u where "(z,u) \<in> r" by auto
    with `(x,z) \<in> r^*` have "(x,u) \<in> r^*" by simp
    with A have "u \<notin> NF r" by simp
    with `(z,u) \<in> r` and `(x,u) \<in> r^*`
    show "\<exists>y. (z,y) \<in> r \<and> y \<in> ?Q" by auto
  qed
  with `x \<in> ?Q` have "x \<in> ?Q \<and> (\<forall>z\<in>?Q. \<exists>y. (z,y) \<in> r \<and> y \<in> ?Q)" by auto
  hence "\<exists>Q. x \<in> Q \<and> (\<forall>z\<in>Q. \<exists>y. (z,y) \<in> r \<and> y \<in> Q)" by (rule exI[where x = "?Q"])
  hence "\<not>(\<forall>Q. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (z,y) \<in> r \<longrightarrow> y \<notin> Q))" by simp
  with SN_elt_imp_elt_minimal[of r x] have "\<not> SN_elt r x" by auto
  with assms show False by simp
qed


subsection {* Commutation *}

definition commute :: "'a ars \<Rightarrow> 'a ars \<Rightarrow> bool"
where "commute r s \<equiv> ((r\<inverse>)^* O s^*) \<subseteq> (s^* O (r\<inverse>)^*)"

lemma CR_iff_self_commute: "CR r = commute r r"
  unfolding commute_def CR_iff_meet_subset_join meet_def join_def
  by simp

(* --> belongs somewhere else *)
lemma rtrancl_imp_rtrancl_UN: 
  assumes "(x,y) \<in> r^*" and "r \<in> I"
  shows "(x,y) \<in> (\<Union>r\<in>I. r)^*" (is "(x,y) \<in> ?r^*")
using assms proof induct
  case base thus ?case by simp
next
  case (step y z)
  hence "(x,y) \<in> ?r^*" by simp
  from `(y,z) \<in> r` and `r \<in> I` have "(y,z) \<in> ?r^*" by auto
  with `(x,y) \<in> ?r^*` show ?case by auto
qed

definition
  quasi_commute :: "'a ars \<Rightarrow> 'a ars \<Rightarrow> bool"
where
  "quasi_commute r s \<equiv> (s O r) \<subseteq> r O (r \<union> s)^*"

lemma rtrancl_union_subset_rtrancl_union_trancl: "(r \<union> s^+)^* = (r \<union> s)^*"
proof
  show "(r \<union> s^+)^* \<subseteq> (r \<union> s)^*"
  proof (rule subsetI2)
    fix x y assume "(x,y) \<in> (r \<union> s^+)^*"
    thus "(x,y) \<in> (r \<union> s)^*"
    proof (induct)
      case base thus ?case by auto
    next
      case (step y z)
      hence "(y,z) \<in> r \<or> (y,z) \<in> s^+" by auto
      hence "(y,z) \<in> (r \<union> s)^*"
      proof
        assume "(y,z) \<in> r" thus ?thesis by auto
      next
        assume "(y,z) \<in> s^+"
        hence "(y,z) \<in> s^*" by auto
        hence "(y,z) \<in> r^* \<union> s^*" by auto
        thus ?thesis using rtrancl_Un_subset by auto
      qed
      with `(x,y) \<in> (r \<union> s)^*` show ?case by simp
    qed
  qed
next
  show "(r \<union> s)^* \<subseteq> (r \<union> s^+)^*"
  proof (rule subsetI2)
    fix x y assume "(x,y) \<in> (r \<union> s)^*"
    thus "(x,y) \<in> (r \<union> s^+)^*"
    proof (induct)
      case base thus ?case by auto
    next
      case (step y z)
      hence "(y,z) \<in> (r \<union> s^+)^*" by auto
      with `(x,y) \<in> (r \<union> s^+)^*` show ?case by auto
    qed
  qed
qed

lemma qc_imp_qc_trancl: assumes "quasi_commute r s" shows "quasi_commute r (s^+)"
unfolding quasi_commute_def proof (rule subsetI2)
  fix x z assume "(x,z) \<in> s^+ O r"
  then obtain y where "(x,y) \<in> s^+" and "(y,z) \<in> r" by best
  thus "(x,z) \<in> r O (r \<union> s^+)^*"
  proof (induct arbitrary: z)
    case (base y)
    hence "(x,z) \<in> (s O r)" by auto
    with assms have "(x,z) \<in> r O (r \<union> s)^*" unfolding quasi_commute_def by auto
    thus ?case using rtrancl_union_subset_rtrancl_union_trancl by auto
  next
    case (step a b)
    hence "(a,z) \<in> (s O r)" by auto
    with assms have "(a,z) \<in> r O (r \<union> s)^*" unfolding quasi_commute_def by auto
    then obtain u where "(a,u) \<in> r" and "(u,z) \<in> (r \<union> s)^*" by best
    hence "(u,z) \<in> (r \<union> s^+)^*" using rtrancl_union_subset_rtrancl_union_trancl by auto
    from `(a,u) \<in> r` and step have "(x,u) \<in> r O (r \<union> s^+)^*" by auto
    then obtain v where "(x,v) \<in> r" and "(v,u) \<in> (r \<union> s^+)^*" by best
    with `(u,z) \<in> (r \<union> s^+)^*` have "(v,z) \<in> (r \<union> s^+)^*" by auto
    with `(x,v) \<in> r` show ?case by auto
  qed
qed

lemma steps_reflect_SN_elt:
  assumes "\<not> SN_elt A b" and "(a, b) \<in> A^*"
  shows "\<not> SN_elt A a"
using steps_preserve_SN_elt[of a b A] and assms by auto

lemma iseq_not_SN_elt:
   assumes "\<forall>i. (S i, S (Suc i)) \<in> r" shows "\<not> SN_elt r (S i)"
proof -
  let ?S = "\<lambda>j. S (i + j)"
  have "?S 0 = S i" by simp
  have "\<forall>i. (?S i, ?S (Suc i)) \<in> r" using assms by auto
  with `?S 0 = S i` have "?S 0 = S i \<and> (\<forall>i. (?S i,?S(Suc i)) \<in> r)" by auto
  hence "\<exists>T. T 0 = S i \<and> (\<forall>i. (T i,T(Suc i)) \<in> r)" by best
  thus "\<not> SN_elt r (S i)" unfolding SN_elt_def by auto
qed

lemma quasi_commute_imp_SN:
  assumes "SN r" and "SN s" and "quasi_commute r s"
  shows "SN (r \<union> s)"
proof -
  have "quasi_commute r (s^+)" by (rule qc_imp_qc_trancl[OF `quasi_commute r s`])
  let ?B = "{a. \<not> SN_elt (r \<union> s) a}"
  {
    assume "\<not> SN(r \<union> s)"
    then obtain a where "a \<in> ?B" unfolding SN_defs by best
    from `SN r` have "\<forall>Q x. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (z,y) \<in> r \<longrightarrow> y \<notin> Q)"
      by (rule SN_imp_minimal)
    hence "\<forall>x. x \<in> ?B \<longrightarrow> (\<exists>z\<in>?B. \<forall>y. (z,y) \<in> r \<longrightarrow> y \<notin> ?B)" by (rule spec[where x = ?B])
    with `a \<in> ?B` obtain b where "b \<in> ?B" and min: "\<forall>y. (b,y) \<in> r \<longrightarrow> y \<notin> ?B" by auto
    from `b \<in> ?B` obtain S where "S 0 = b" and
      seq: "\<forall>i. (S i,S(Suc i)) \<in> r \<union> s" unfolding SN_elt_def by auto
    let ?S = "\<lambda>i. S(Suc i)"
    have "?S 0 = S 1" by simp
    from seq have "\<forall>i. (?S i,?S(Suc i)) \<in> r \<union> s" by auto
    with `?S 0 = S 1` have "\<not> SN_elt (r \<union> s) (S 1)" unfolding SN_elt_def by auto
    from `S 0 = b` and seq have "(b,S 1) \<in> r \<union> s" by auto
    with min and `\<not> SN_elt (r \<union> s) (S 1)` have "(b,S 1) \<in> s" by auto
    let ?i = "LEAST i. (S i,S(Suc i)) \<notin> s"
    {
      assume "\<forall>i. (S i,S(Suc i)) \<in> s"
      with `S 0 = b` have "\<not> SN_elt s b" unfolding SN_elt_def by auto
      with `SN s` have False unfolding SN_def by auto
    }
    hence ex: "\<exists>i. (S i,S(Suc i)) \<notin> s" by auto
    hence "(S ?i,S(Suc ?i)) \<notin> s" by (rule LeastI_ex)
    with seq have "(S ?i,S(Suc ?i)) \<in> r" by auto
    have ini: "\<forall>i<?i. (S i,S(Suc i)) \<in> s" using not_less_Least by auto
    {
      fix i assume "i < ?i" hence "(b,S(Suc i)) \<in> s^+"
      proof (induct i)
        case 0 thus ?case using `(b,S 1) \<in> s` and `S 0 = b` by auto
      next
        case (Suc k)
      hence "(b,S(Suc k)) \<in> s^+" and "Suc k < ?i" by auto
      with `\<forall>i<?i. (S i,S(Suc i)) \<in> s` have "(S(Suc k),S(Suc(Suc k))) \<in> s" by fast
      with `(b,S(Suc k)) \<in> s^+` show ?case by auto
    qed
    }
    hence pref: "\<forall>i<?i. (b,S(Suc i)) \<in> s^+" by auto
    from `(b,S 1) \<in> s` and `S 0 = b` have "(S 0,S(Suc 0)) \<in> s" by auto
    {
      assume "?i = 0"
      from ex have "(S ?i,S(Suc ?i)) \<notin> s" by (rule LeastI_ex)
      with `(S 0,S(Suc 0)) \<in> s` have False unfolding `?i = 0` by simp
    }
    hence "0 < ?i" by auto
    then obtain j where "?i =  Suc j" unfolding gr0_conv_Suc by best
    with ini have "(S(?i-Suc 0),S(Suc(?i-Suc 0))) \<in> s" by auto
    with pref have "(b,S(Suc j)) \<in> s^+" unfolding `?i = Suc j` by auto
    hence "(b,S ?i) \<in> s^+" unfolding `?i = Suc j` by auto
    with `(S ?i,S(Suc ?i)) \<in> r` have "(b,S(Suc ?i)) \<in> (s^+ O r)" by auto
    with `quasi_commute r (s^+)` have "(b,S(Suc ?i)) \<in> r O (r \<union> s^+)^*"
      unfolding quasi_commute_def by auto
    then obtain c where "(b,c) \<in> r" and "(c,S(Suc ?i)) \<in> (r \<union> s^+)^*" by best
    from `(b,c) \<in> r` have "(b,c) \<in> (r \<union> s)^*" by auto
    from iseq_not_SN_elt[where r = "r \<union> s" and S = S]
      and seq have "\<not> SN_elt (r \<union> s) (S(Suc ?i))" by auto
    from `(c,S(Suc ?i)) \<in> (r \<union> s^+)^*` have "(c,S(Suc ?i)) \<in> (r \<union> s)^*"
      unfolding rtrancl_union_subset_rtrancl_union_trancl by auto
    with steps_reflect_SN_elt[of "r \<union> s"]
      and `\<not> SN_elt (r \<union> s) (S(Suc ?i))` have "\<not> SN_elt (r \<union> s) c" by auto
    hence "c \<in> ?B" by simp
    with `(b,c) \<in> r` and min have False by auto
  }
  thus ?thesis by auto
qed


subsection {* Strong Normalization *}

lemma non_strict_into_strict:
  assumes compat: "NS O S \<subseteq> S"
  and steps: "(s,t) \<in> (NS^*) O S"
  shows "(s,t) \<in> S"
using steps proof
  fix x u z
  assume "(s,t) = (x,z)" and "(x,u) \<in> NS^*" and "(u,z) \<in> S"
  hence "(s,u) \<in> NS^*" and "(u,t) \<in> S" by auto
  thus ?thesis
  proof (induct rule:rtrancl.induct)
    case (rtrancl_refl x) thus ?case .
  next
    case (rtrancl_into_rtrancl a b c)
    with compat show ?case by auto
  qed
qed

lemma comp_trancl: assumes "R O S \<subseteq> S" shows "R O S^+ \<subseteq> S^+"
proof (rule subsetI2)
  fix w z assume "(w,z) \<in> R O S^+"
  then obtain x where R_step: "(w,x) \<in> R" and S_seq: "(x,z) \<in> S^+" by best
  from tranclD[OF S_seq] obtain y where S_step: "(x,y) \<in> S" and S_seq': "(y,z) \<in> S^*" by auto
  from R_step and S_step have "(w,y) \<in> R O S" by auto
  with assms have "(w,y) \<in> S" by auto
  with S_seq' show "(w,z) \<in> S^+" by simp
qed

lemma comp_rtrancl_trancl:
  assumes comp: "R O S \<subseteq> S"
    and seq: "(s,t) \<in> (R \<union> S)^* O S"
  shows "(s,t) \<in> S^+"
using seq proof
  fix x u z
  assume "(s,t) = (x,z)" and "(x,u) \<in> (R \<union> S)^*" and "(u,z) \<in> S"
  hence "(s,u) \<in> (R \<union> S)^*" and "(u,t) \<in> S^+" by auto
  thus ?thesis
  proof (induct rule: rtrancl.induct)
    case (rtrancl_refl x) thus ?case .
  next
    case (rtrancl_into_rtrancl a b c)
    hence "(b,c) \<in> R \<union> S" by simp
    thus ?case
    proof
      assume "(b,c) \<in> S"
      with rtrancl_into_rtrancl
      have "(b,t) \<in> S^+" by simp
      with rtrancl_into_rtrancl show ?thesis by simp
    next
      assume "(b,c) \<in> R"
      with comp_trancl[OF comp] rtrancl_into_rtrancl
      show ?thesis by auto
    qed
  qed
qed

lemma iseq_imp_steps:
fixes i j :: nat
assumes seq: "\<forall>i. (s i, s (Suc i)) \<in> A"
  and "j \<ge> i"
shows "(s i, s j) \<in> A^*"
using `j \<ge> i` proof (induct j)
  case 0 thus ?case by simp
next
  case (Suc j)
  show ?case
  proof (cases "i = Suc j")
    case True show ?thesis by (simp add: True)
  next
    case False
    with Suc have "(s i, s j) \<in> A^*" by simp
    moreover from seq have "(s j, s (Suc j)) \<in> A^*" by auto
    ultimately show ?thesis by simp
  qed
qed

lemma trancl_union_right: fixes r::"'a ars" shows "r^+ \<subseteq> (s \<union> r)^+"
proof (rule subsetI2)
  fix x y assume "(x,y) \<in> r^+" thus "(x,y) \<in> (s \<union> r)^+"
  proof (induct)
    case base thus ?case by auto
  next
    case (step a b)
    hence "(a,b) \<in> (s \<union> r)^+" by auto
    with `(x,a) \<in> (s \<union> r)^+` show ?case by auto
  qed
qed

lemma SN_rel_subset: "SN_rel R S \<subseteq> R"
proof (rule subsetI2)
  fix a b assume "(a,b) \<in> SN_rel R S" thus "(a,b) \<in> R" unfolding SN_rel_def by simp
qed

lemma first_step: assumes C: "C = A \<union> B" and steps: "(x,y) \<in> C^*"
  and Bstep: "(y,z) \<in> B"
  shows "\<exists> y. (x,y) \<in> A^* O B"
  using steps
proof (induct rule: converse_rtrancl_induct)
  case base
  show ?case using Bstep by auto
next 
  case (step u x)
  from step(1)[unfolded C] 
  show ?case
  proof
    assume "(u,x) \<in> B"
    thus ?thesis by auto
  next
    assume ux: "(u,x) \<in> A"
    from step(3) obtain y where "(x,y) \<in> A^* O B" by auto
    then obtain z where "(x,z) \<in> A^*" and step: "(z,y) \<in> B" by auto
    with ux have "(u,z) \<in> A^*" by auto
    with step have "(u,y) \<in> A^* O B" by auto
    thus ?thesis by auto
  qed
qed

lemma first_step_O: assumes C: "C = A \<union> B" and steps: "(x,y) \<in> C^* O B"
  shows "\<exists> y. (x,y) \<in> A^* O B"
proof -
  from steps obtain z where "(x,z) \<in> C^*" and "(z,y) \<in> B" by auto
  from first_step[OF C this] show ?thesis .
qed

lemma firstStep: assumes LSR: "L = S \<union> R" and xyL: "(x,y) \<in> L^*"
  shows "(x,y) \<in> R^* \<or> (x,y) \<in> R^* O S O L^*"
proof (cases "(x,y) \<in> R^*")
  case True
  thus ?thesis by simp
next
  case False 
  let ?SR = "S \<union> R"
  from xyL and LSR have "(x,y) \<in> ?SR^*" by simp
  from this and False have "(x,y) \<in> R^* O S O ?SR^*" 
  proof (induct rule: rtrancl_induct)
    case base thus ?case by simp
  next
    case (step y z)
    thus ?case
    proof (cases "(x,y) \<in> R^*")
      case False with step have "(x,y) \<in> R^* O S O ?SR^*" by simp
      from this obtain u where xu: "(x,u) \<in> R^* O S" and uy: "(u,y) \<in> ?SR^*" by force
      from `(y,z) \<in> ?SR` have "(y,z) \<in> ?SR^*" by auto
      with uy have "(u,z) \<in> ?SR^*" by (rule rtrancl_trans)
      with xu show ?thesis by auto
    next
      case True 
      have "(y,z) \<in> S" 
      proof (rule ccontr)
	assume "(y,z) \<notin> S" with `(y,z) \<in> ?SR` have "(y,z) \<in> R" by auto
	with True  have "(x,z) \<in> R^*"  by auto
	with `(x,z) \<notin> R^*` show False ..
      qed
      with True show ?thesis by auto
    qed
  qed
  with LSR show ?thesis by simp
qed  

lemma union_iseq_SN_elt_imp_first_step:
  assumes "\<forall>i. (t i, t (Suc i)) \<in> (R \<union> S)" and "SN_elt S (t 0)"
  shows "\<exists>i. (t i, t (Suc i)) \<in> R \<and> (\<forall>j<i. (t j, t (Suc j)) \<in> S \<and> (t j, t (Suc j)) \<notin> R)"
proof -
  from `SN_elt S (t 0)` obtain i where "(t i, t (Suc i)) \<notin> S" by blast
  with assms have "(t i, t (Suc i)) \<in> R" (is "?P i") by auto
  let ?i = "Least ?P"
  from `?P i` have "?P ?i" by (rule LeastI)
  have "\<forall>j<?i. (t j, t (Suc j)) \<notin> R" using not_less_Least by auto
  moreover with assms have "\<forall>j<?i. (t j, t (Suc j)) \<in> S" by best
  ultimately have "\<forall>j<?i. (t j, t (Suc j)) \<in> S \<and> (t j, t (Suc j)) \<notin> R" by best
  with `?P ?i` show ?thesis by best
qed

lemma non_strict_ending:
  assumes seq: "\<forall>i. (t i,t(Suc i)) \<in> R \<union> S"
    and comp: "R O S \<subseteq> S"
    and SN: "SN_elt S (t 0)"
  shows "\<exists>j. \<forall>i\<ge>j. (t i,t(Suc i)) \<in> R - S" (is ?thesis)
proof (rule ccontr)
  assume "\<not> ?thesis"
  with seq have "\<forall>j.\<exists>i. i\<ge>j \<and> (t i,t(Suc i)) \<in> S" by blast
  from choice[OF this] obtain f where S_steps: "\<forall>i. i\<le>f i \<and> (t(f i),t(Suc(f i))) \<in> S" ..
  let ?t = "\<lambda>i. t (((Suc \<circ> f)^^i) 0)"
  have S_seq: "\<forall>i. (t i,t(Suc(f i))) \<in> S^+"
  proof
    fix i
    from S_steps have leq: "i\<le>f i" and step: "(t(f i),t(Suc(f i))) \<in> S" by auto
    from iseq_imp_steps[OF seq leq] have "(t i,t(f i)) \<in> (R \<union> S)^*" by simp
    with step have "(t i,t(Suc(f i))) \<in> (R \<union> S)^* O S" by auto
    from comp_rtrancl_trancl[OF comp this] show "(t i,t(Suc(f i))) \<in> S^+" .
  qed
  hence "\<forall>i. (?t i,?t(Suc i)) \<in> S^+" by simp
  moreover have "SN_elt (S^+) (?t 0)" using SN_elt_imp_SN_elt_trancl[OF SN] by simp
  ultimately show False unfolding SN_defs by best
qed

lemma SN_elt_subset:
  assumes "SN_elt R' x" and "rR' \<subseteq> R'" shows "SN_elt rR' x" unfolding SN_elt_def
proof-
  from assms have noS: "\<not>(\<exists>S. S 0 = x \<and> (\<forall>i. (S i, S (Suc i)) \<in> R'))" unfolding SN_elt_def
    by simp
  show " \<not> (\<exists>S. S 0 = x \<and> (\<forall>i. (S i, S (Suc i)) \<in> rR'))"
  proof(rule notI)
    assume "\<exists>S. S 0 = x \<and> (\<forall>i. (S i, S (Suc i)) \<in> rR')"
    then obtain S where "S 0 = x" and "\<forall>i. (S i, S (Suc i)) \<in> rR'" by auto
    with `rR' \<subseteq> R'` have "\<forall>i. (S i, S (Suc i)) \<in> R'" by auto
    with `S 0 = x` have "\<exists> S. (S 0 = x) \<and> (\<forall>i. (S i, S (Suc i)) \<in> R')" by auto
    with noS show False ..
  qed
qed

lemmas SN_elt_mono = SN_elt_subset


lemma rtrancl_fun_conv:
  "((s,t) \<in> R^*) = (\<exists> f n. f 0 = s \<and> f n = t \<and> (\<forall> i < n. (f i, f (Suc i)) \<in> R))"
  unfolding rtrancl_is_UN_rel_pow using rel_pow_fun_conv[where R = R]
  by auto


lemma rtrancl_imp_rel_pow': "(x,y) \<in> R^* \<Longrightarrow> \<exists>n. (x,y) \<in> ((R::'a ars) ^^ n)"
  unfolding rtrancl_is_UN_rel_pow by auto

lemma compat_tr_compat: assumes "NS O S \<subseteq> S" shows "NS^* O S \<subseteq> S"
  using non_strict_into_strict[where S = S and NS = NS] assms by blast

lemma right_comp_S[simp]:
  assumes "(x, y) \<in> S O (S O S^* O NS^* \<union> NS^*)"
  shows "(x, y) \<in> (S O S^* O NS^*)"
proof-
  from assms have "(x, y) \<in> (S O S O S^* O NS^*) \<union> (S O NS^*)" by auto
  hence  xy:"(x, y) \<in> (S O (S O S^*) O NS^*) \<union> (S O NS^*)" by auto
  have "S O S^* \<subseteq> S^*" by auto
  with xy have "(x, y) \<in> (S O S^* O NS^*) \<union> (S O NS^*)" by auto
  then show "(x, y) \<in> (S O S^* O NS^*)" by auto
qed

lemma compatible_SN:
  assumes SN: "SN S"
  and compat: "NS O S \<subseteq> S" 
  shows "SN (S O S^* O NS^*)" (is "SN ?A")
proof
  fix F assume seq: "\<forall>i. (F i, F (Suc i)) \<in> ?A"
  from compat compat_tr_compat have tr_compat: "NS^* O S \<subseteq> S" by blast
  have "\<forall> i. (\<exists> y z. (F i, y)  \<in> S \<and> (y, z)  \<in> S^* \<and> (z, F (Suc i)) \<in> NS^*)"
  proof
    fix i
    from seq have "(F i,F (Suc i)) \<in> (S O S^* O NS^*)" by auto
    thus "\<exists> y z. (F i, y)  \<in> S \<and> (y, z)  \<in> S^* \<and> (z, F (Suc i)) \<in> NS^*"
      unfolding rel_comp_def using mem_Collect_eq by auto
  qed
  hence "\<exists> f. (\<forall> i. (\<exists> z. (F i, f i)  \<in> S \<and> ((f i, z)  \<in> S^*) \<and>(z, F (Suc i)) \<in> NS^*))"
    by (rule choice)
  then obtain f
    where "\<forall> i. (\<exists> z. (F i, f i)  \<in> S \<and> ((f i, z)  \<in> S^*) \<and>(z, F (Suc i)) \<in> NS^*)" ..
  hence "\<exists> g. \<forall> i. (F i, f i)  \<in> S \<and> (f i, g i)  \<in> S^* \<and> (g i, F (Suc i)) \<in> NS^*"
    by (rule choice)
  then obtain g where "\<forall> i. (F i, f i)  \<in> S \<and> (f i, g i)  \<in> S^* \<and> (g i, F (Suc i)) \<in> NS^*" ..
  hence "\<forall> i. (f i, g i)  \<in> S^* \<and> (g i, F (Suc i)) \<in> NS^* \<and> (F (Suc i), f (Suc i))  \<in> S"
    by auto
  hence "\<forall> i. (f i, g i)  \<in> S^* \<and> (g i, f (Suc i))  \<in> S" unfolding rel_comp_def
    using tr_compat by auto
  hence all:"\<forall> i. (f i, g i)  \<in> S^* \<and> (g i, f (Suc i))  \<in> S^+" by auto
  have "\<forall> i. (f i, f (Suc i))  \<in> S^+"
  proof
    fix i
    from all have "(f i, g i)  \<in> S^* \<and> (g i, f (Suc i))  \<in> S^+" ..
    thus "(f i, f (Suc i))  \<in> S^+" using transitive_closure_trans by auto
  qed
  hence "\<exists> x. ((f 0) = x) \<and> (\<forall>i. (f i, f (Suc i)) \<in> S^+)" by auto
  then obtain x where "((f 0) = x) \<and> (\<forall>i. (f i, f (Suc i)) \<in> S^+)" by auto
  hence "\<exists> f. ((f 0) = x) \<and> (\<forall>i. (f i, f (Suc i)) \<in> S^+)" by auto
  hence "\<not> SN_elt (S^+) x" by auto
  hence "\<not> SN (S^+)" unfolding SN_defs by auto
  hence wfSconv:"\<not> wf ((S^+)\<inverse>)" using SN_iff_wf by auto
  from SN have "wf (S\<inverse>)" using SN_imp_wf[where?r=S] by simp
  with wf_converse_trancl wfSconv show False by auto
qed

lemma compatible_rtrancl_split:
  assumes compat: "NS O S \<subseteq> S"
   and steps: "(x, y) \<in> (NS \<union> S)^*"
  shows "(x, y) \<in> S O S^* O NS^* \<union> NS^*"
proof-
  from steps have "\<exists> n. (x, y) \<in> (NS \<union> S)^^n" using rtrancl_imp_rel_pow'[where ?R="NS \<union> S"] by auto
  then obtain n where "(x, y) \<in> (NS \<union> S)^^n" by auto
  thus "(x, y) \<in>  S O S^* O NS^* \<union> NS^*"
  proof (induct n arbitrary: x, simp)
    case (Suc m)
    assume "(x, y) \<in> (NS \<union> S)^^(Suc m)"
    hence "\<exists> z. (x, z) \<in> (NS \<union> S) \<and> (z, y) \<in> (NS \<union> S)^^m" using rel_pow_Suc_D2[where ?R="NS \<union> S"] by auto
    then obtain z where xz:"(x, z) \<in> (NS \<union> S)" and zy:"(z, y) \<in> (NS \<union> S)^^m" by auto
    with Suc have zy:"(z, y) \<in>  S O S^* O NS^* \<union> NS^*" by auto
    thus "(x, y) \<in>  S O S^* O NS^* \<union> NS^*"
    proof (cases "(x, z) \<in> NS")
      case True
      from compat compat_tr_compat have trCompat: "NS^* O S \<subseteq> S" by blast
      from zy True have "(x, y) \<in> (NS O S O S^* O NS^*) \<union> (NS O NS^*)" by auto
      hence "(x, y) \<in> ((NS O S) O S^* O NS^*) \<union> (NS O NS^*)" by auto
      hence "(x, y) \<in> ((NS^* O S) O S^* O NS^*) \<union> (NS O NS^*)" by auto
      with trCompat have xy:"(x, y) \<in> (S O S^* O NS^*) \<union> (NS O NS^*)" by auto
      have "NS O NS^* \<subseteq> NS^*" by auto
      with xy show "(x, y) \<in> (S O S^* O NS^*) \<union> NS^*" by auto
    next
      case False
      with xz have xz:"(x, z) \<in> S" by auto
      with zy have "(x, y) \<in> S O (S O S^* O NS^* \<union> NS^*)" by auto
      thus "(x, y) \<in> (S O S^* O NS^*) \<union> NS^*" using right_comp_S by simp
    qed
  qed
qed

lemma compatible_conv:
  assumes compat: "NS O S \<subseteq> S" 
  shows "(NS \<union> S)^* O S O (NS \<union> S)^* = S O S^* O NS^*" 
proof -
  let ?NSuS = "NS \<union> S"
  let ?NSS = "S O S^* O NS^*"
  let ?midS = "?NSuS^* O S O ?NSuS^*"
  have one: "?NSS \<subseteq> ?midS" by regexp 
  have "?NSuS^* O S \<subseteq> (?NSS \<union> NS^*) O S"
    using compatible_rtrancl_split[where S = S and NS = NS] compat by blast
  also have "\<dots> \<subseteq> ?NSS O S \<union> NS^* O S" by auto
  also have "\<dots> \<subseteq> ?NSS O S \<union> S" using compat compat_tr_compat[where S = S and NS = NS] by auto
  also have "\<dots> \<subseteq> S O ?NSuS^*" by regexp
  finally have "?midS \<subseteq> S O ?NSuS^* O ?NSuS^*" by blast
  also have "\<dots> \<subseteq> S O ?NSuS^*" by regexp
  also have "\<dots> \<subseteq> S O (?NSS \<union> NS^*)"
    using compatible_rtrancl_split[where S = S and NS = NS] compat by blast
  also have "\<dots> \<subseteq> ?NSS" by regexp
  finally have two: "?midS \<subseteq> ?NSS" . 
  from one two show ?thesis by auto 
qed

lemma compatible_SN': 
  assumes compat: "NS O S \<subseteq> S" and SN: "SN S"
  shows "SN((NS \<union> S)^* O S O (NS \<union> S)^*)"
using compatible_conv[where S = S and NS = NS] 
  compatible_SN[where S = S and NS = NS] assms by force

lemma rtrancl_diff_decomp:
 assumes "(x, y) \<in> A^* - B^*"
 shows "(x, y) \<in> A^* O (A - B) O A^*"
proof-
 from assms have A: "(x, y) \<in> A^*" and B:"(x, y) \<notin> B^*" by auto
 from A have "\<exists> k. (x, y) \<in> A^^k" by (rule rtrancl_imp_rel_pow')
 then obtain k where Ak:"(x, y) \<in> A^^k" by auto
 from Ak B show "(x, y) \<in> A^* O (A - B) O A^*"
 proof (induct k arbitrary: x)
 case 0
  with `(x, y) \<notin> B^*` 0 show ?case using ccontr by auto
 next
 case (Suc i)
  hence B:"(x, y) \<notin> B^*" and ASk:"(x, y) \<in> A ^^ Suc i" by auto
  from ASk have "\<exists>z. (x, z) \<in> A \<and> (z, y) \<in> A ^^ i" using rel_pow_Suc_D2[where ?R=A] by auto
  then obtain z where xz:"(x, z) \<in> A" and "(z, y) \<in> A ^^ i" by auto
  hence zy:"(z, y) \<in> A^*" using rel_pow_imp_rtrancl by auto
  from xz show "(x, y) \<in> A^* O (A - B) O A^*"
  proof (cases "(x, z) \<in> B")
   case False
    with xz zy show "(x, y) \<in> A\<^sup>* O (A - B) O A\<^sup>*" by auto
   next
   case True
    hence "(x, z) \<in> B^*" by auto
    have "\<lbrakk>(x, z) \<in> B^*; (z, y) \<in> B^*\<rbrakk> \<Longrightarrow> (x, y) \<in> B^*" using rtrancl_trans[where ?r=B and ?a=x and ?b=z] by auto
    with  `(x, z) \<in> B^*` `(x, y) \<notin> B^*` have "(z, y) \<notin> B^*" by auto
    with Suc `(z, y) \<in> A ^^ i` have "(z, y) \<in> A^* O (A - B) O A^*" by auto
    with xz have xy:"(x, y) \<in> A O A\<^sup>* O (A - B) O A\<^sup>*" by auto
    have "A O A\<^sup>* O (A - B) O A\<^sup>* \<subseteq> A\<^sup>* O (A - B) O A\<^sup>*" by regexp
    from this xy show "(x, y) \<in> A\<^sup>* O (A - B) O A\<^sup>*" using subsetD[where ?A="A O A\<^sup>* O (A - B) O A\<^sup>*"] by auto
  qed
 qed
qed

lemma SN_empty[simp]: "SN {}" by auto


lemma SN_elt_weakening:
  assumes "SN_elt R1 a"
  shows "SN_elt (R1 \<inter> R2) a"
proof-
{
  assume "\<exists>S. S 0 = a \<and> (\<forall>i. (S i, S (Suc i)) \<in> R1 \<inter> R2)"
  then obtain S where
    S0: "S 0 = a" and
    SN: "\<forall>i. (S i, S (Suc i)) \<in> (R1 \<inter> R2)"
  by auto
  from SN have SN': "\<forall>i. (S i, S (Suc i)) \<in> R1" by simp
  with S0 and assms have "False" by auto
}
thus ?thesis by auto
qed

lemma SN_weakening:
  assumes "SN R1"
  shows "SN (R1 \<inter> R2)"
using SN_elt_weakening and assms
unfolding SN_def by metis


(* an explicit version of infinite reduction *)
definition ideriv :: "'a ars \<Rightarrow> 'a ars \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
where "ideriv R S as \<equiv> (\<forall> i. (as i, as (Suc i)) \<in> R \<union> S) \<and> (INFM i. (as i,as (Suc i)) \<in> R)"

lemma ideriv_mono: "R \<subseteq> R' \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> ideriv R S as \<Longrightarrow> ideriv R' S' as"
  unfolding ideriv_def INFM_nat by blast


fun
  shift :: "'a iseq \<Rightarrow> nat \<Rightarrow> 'a iseq"
where
  "shift f j = (\<lambda> i. f (i+j))"

lemma ideriv_split: assumes ideriv: "ideriv R S as"
  and nideriv: "\<not> ideriv (D \<inter> (R \<union> S)) (R \<union> S - D) as"
  shows "\<exists> i. ideriv (R - D) (S - D) (shift as i)"
proof -
  have RS: "R - D \<union> (S - D) = R \<union> S - D" by auto
  from ideriv[unfolded ideriv_def]
  have as: "\<And> i. (as i, as (Suc i)) \<in> R \<union> S"
    and inf: "INFM i. (as i, as (Suc i)) \<in> R" by auto
  show ?thesis
  proof (cases "INFM i. (as i, as (Suc i)) \<in> D \<inter> (R \<union> S)")
    case True
    have "ideriv (D \<inter> (R \<union> S)) (R \<union> S - D) as"
      unfolding ideriv_def
      using as True  by auto
    with nideriv show ?thesis ..
  next
    case False
    from False[unfolded INFM_nat]
    obtain i where Dn: "\<And> j. i < j \<Longrightarrow> (as j, as (Suc j)) \<notin> D \<inter> (R \<union> S)"
      by auto
    from Dn as have as: "\<And> j. i < j \<Longrightarrow> (as j, as (Suc j)) \<in> R \<union> S - D" by auto
    show ?thesis
    proof (rule exI[of _ "Suc i"], unfold ideriv_def RS, insert as, intro conjI, simp, unfold INFM_nat, intro allI)
      fix m
      from inf[unfolded INFM_nat] obtain j where j: "j > Suc i + m" and R: "(as j, as (Suc j)) \<in> R" by auto
      with as[of j] have RD: "(as j, as (Suc j)) \<in> R - D" by auto      
      show "\<exists> j > m. (shift as (Suc i) j, shift as (Suc i) (Suc j)) \<in> R - D"
        by (rule exI[of _ "j - Suc i"], insert j RD, auto)
    qed
  qed
qed

lemma ideriv_SN: assumes SN: "SN S"
  and compat: "NS O S \<subseteq> S"
  and R: "R \<subseteq> NS \<union> S"
  shows "\<not> ideriv (S \<inter> R) (R - S) as"
proof
  assume "ideriv (S \<inter> R) (R - S) as"
  with R have steps: "\<forall> i. (as i, as (Suc i)) \<in> NS \<union> S" and inf: "INFM i. (as i, as (Suc i)) \<in> S \<inter> R" unfolding ideriv_def by auto
  from non_strict_ending[OF steps compat] SN
  obtain i where i: "\<And> j. j \<ge> i \<Longrightarrow> (as j, as (Suc j)) \<in> NS - S" by auto
  from inf[unfolded INFM_nat] obtain j where "j > i" and "(as j, as (Suc j)) \<in> S" by auto
  with i[of j] show False by auto
qed

lemma Infm_shift: "(INFM i. P (shift f n i)) = (INFM i. P (f i))" (is "?S = ?O")
proof 
  assume ?S
  show ?O
    unfolding INFM_nat_le 
  proof
    fix m
    from `?S`[unfolded INFM_nat_le]
    obtain k where k: "k \<ge> m" and p: "P (shift f n k)" by auto
    show "\<exists> k \<ge> m. P (f k)"
      by (rule exI[of _ "k + n"], insert k p, auto)
  qed
next
  assume ?O
  show ?S
    unfolding INFM_nat_le 
  proof
    fix m
    from `?O`[unfolded INFM_nat_le]
    obtain k where k: "k \<ge> m + n" and p: "P (f k)" by auto
    show "\<exists> k \<ge> m. P (shift f n k)"
      by (rule exI[of _ "k - n"], insert k p, auto)
  qed
qed

subsection {* Relative Rewriting *}

type_synonym 'a rel_ars = "'a ars \<times> 'a ars"

fun
  rel_step :: "'a rel_ars \<Rightarrow> 'a ars"
where
  "rel_step (R, S) = S^* O R O S^*"

definition
  rel_SN :: "'a rel_ars \<Rightarrow> bool"
where
  "rel_SN RS \<equiv> SN (rel_step RS)"

fun
  rel_SN_alt :: "'a rel_ars \<Rightarrow> bool"
where
  "rel_SN_alt (R, S) = (\<forall>(f::nat \<Rightarrow> 'a).
    (\<forall>i. (f i, f (Suc i)) \<in> R \<union> S) \<longrightarrow> \<not> (INFM j. (f j, f (Suc j)) \<in> R))"

lemma rel_SN_to_rel_SN_alt: "rel_SN (R, S) \<Longrightarrow> rel_SN_alt (R, S)"
proof (unfold rel_SN_def)
  assume SN: "SN (rel_step (R,S))"
  show ?thesis
  proof (simp only: rel_SN_alt.simps, intro allI impI)
    fix f
    assume steps: "\<forall> i. (f i, f (Suc i)) \<in> R \<union> S"
    obtain r where  r: "\<And> j. r j \<equiv>  (f j, f (Suc j)) \<in> R" by auto
    show "\<not> (INFM j. (f j, f (Suc j)) \<in> R)"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence ih: "infinite_hits r" unfolding infinite_hits_def r by blast
      obtain r_index where "r_index = infinite_hits.index r" by simp
      with infinite_hits.index_p[OF ih] infinite_hits.index_ordered[OF ih] infinite_hits.index_not_p_between[OF ih] 
      have r_index: "\<And> i. r (r_index i) \<and> r_index i < r_index (Suc i) \<and> (\<forall> j. r_index i < j \<and> j < r_index (Suc i) \<longrightarrow> \<not> r j)" by auto
      obtain g where g: "\<And> i. g i \<equiv> f (r_index i)" ..
      {
        fix i
        let ?ri = "r_index i"
        let ?rsi = "r_index (Suc i)"
        from r_index have isi: "?ri < ?rsi" by auto
        obtain ri rsi where ri: "ri = ?ri" and rsi: "rsi = ?rsi" by auto
        with r_index[of i] steps have inter: "\<And> j. ri < j \<and> j < rsi \<Longrightarrow> (f j, f (Suc j)) \<in> S" unfolding r by auto
        from ri isi rsi have risi: "ri < rsi" by simp                      
        {
          fix n
          assume "Suc n \<le> rsi - ri"
          hence "(f (Suc ri), f (Suc (n + ri))) \<in> S^*"
          proof (induct n, simp)
            case (Suc n)
            hence stepps: "(f (Suc ri), f (Suc (n+ri))) \<in> S^*" by simp
            have "(f (Suc (n+ri)), f (Suc (Suc n + ri))) \<in> S"
              using inter[of "Suc n + ri"] Suc(2) by auto
            with stepps show ?case by simp
          qed
        }
        from this[of "rsi - ri - 1"] risi have 
          "(f (Suc ri), f rsi) \<in> S^*" by simp
        with ri rsi have ssteps: "(f (Suc ?ri), f ?rsi) \<in> S^*" by simp
        with r_index[of i] have "(f ?ri, f ?rsi) \<in> R O S^*" unfolding r by auto
        hence "(g i, g (Suc i)) \<in> S^* O R O S^*" using rtrancl_refl unfolding g by auto           
      } 
      hence "\<not> SN (S^* O R O S^*)" unfolding SN_defs by blast
      with SN show False unfolding rel_step.simps by simp
    qed
  qed
qed


lemma rtrancl_list_conv:  "((s,t) \<in> R^*) = 
  (\<exists> list.  last (s # list) = t \<and> (\<forall> i. i < length list \<longrightarrow> ((s # list) ! i, (s # list) ! Suc i) \<in> R))" (is "?l = ?r")
proof 
  assume ?r
  then obtain list where "last (s # list) = t \<and> (\<forall> i. i < length list \<longrightarrow> ((s # list) ! i, (s # list) ! Suc i) \<in> R)" ..
  thus ?l
  proof (induct list arbitrary: s, simp)
    case (Cons u ll)
    hence "last (u # ll) = t \<and> (\<forall> i. i < length ll \<longrightarrow> ((u # ll) ! i, (u # ll) ! Suc i) \<in> R)" by auto
    from Cons(1)[OF this] have rec: "(u,t) \<in> R^*" .
    from Cons have "(s, u) \<in> R" by auto
    with rec show ?case by auto
  qed
next
  assume ?l
  from rtrancl_imp_seq[OF this]
  obtain S n where s: "S 0 = s" and t: "S n = t" and steps: "\<forall> i<n. (S i, S (Suc i)) \<in> R" by auto
  let ?list = "map (\<lambda> i. S (Suc i)) [0 ..< n]"
  show ?r
  proof (rule exI[of _ ?list], intro conjI, 
      cases n, simp add: s[symmetric] t[symmetric], simp add: t[symmetric]) 
    show "\<forall> i < length ?list. ((s # ?list) ! i, (s # ?list) ! Suc i) \<in> R" 
    proof (intro allI impI)
      fix i
      assume i: "i < length ?list"
      thus "((s # ?list) ! i, (s # ?list) ! Suc i) \<in> R"
      proof (cases i, simp add: s[symmetric] steps)
        case (Suc j)
        with i steps show ?thesis by simp
      qed
    qed
  qed
qed
        
lemma rel_SN_alt_to_rel_SN : "rel_SN_alt (R,S) \<Longrightarrow> rel_SN (R,S)"
proof (unfold rel_SN_def)
  assume SN: "rel_SN_alt (R,S)"
  show "SN (rel_step (R,S))"
  proof
    fix f
    assume  "\<forall> i. (f i, f (Suc i)) \<in> rel_step (R,S)"
    hence steps: "\<And> i. (f i, f (Suc i)) \<in> S^* O R O S^*" by auto
    let ?prop = "\<lambda> i ai bi. (f i, bi) \<in> S^* \<and> (bi, ai) \<in> R \<and> (ai, f (Suc (i))) \<in> S^*"
    {
      fix i
      from steps obtain bi ai where "?prop i ai bi" by blast
      hence "\<exists> ai bi. ?prop i ai bi" by blast
    }
    hence "\<forall> i. \<exists> bi ai. ?prop i ai bi" by blast
    from choice[OF this] obtain b where "\<forall> i. \<exists> ai. ?prop i ai (b i)" by blast
    from choice[OF this] obtain a where steps: "\<And> i. ?prop i (a i) (b i)" by blast
    let ?prop = "\<lambda> i li. (b i, a i) \<in> R \<and> (\<forall> j < length li. ((a i # li) ! j, (a i # li) ! Suc j) \<in> S) \<and> last (a i # li) = b (Suc i)"
    {
      fix i
      from steps[of i] steps[of "Suc i"] have "(a i, f (Suc i)) \<in> S^*" and "(f (Suc i), b (Suc i)) \<in> S^*" by auto
      from rtrancl_trans[OF this] steps[of i] have R: "(b i, a i) \<in> R" and S: "(a i, b (Suc i)) \<in> S^*" by blast+
      from S[unfolded rtrancl_list_conv] obtain li where "last (a i # li) = b (Suc i) \<and> (\<forall> j < length li. ((a i # li) ! j, (a i # li) ! Suc j) \<in> S)" ..
      with R have "?prop i li" by blast
      hence "\<exists> li. ?prop i li" ..
    }
    hence "\<forall> i. \<exists> li. ?prop i li" ..
    from choice[OF this] obtain l where steps: "\<And> i. ?prop i (l i)" by auto
    let ?p = "\<lambda> i. ?prop i (l i)"
    from steps have steps: "\<And> i. ?p i" by blast
    let ?l = "\<lambda> i. a i # l i"    
    let ?l' = "\<lambda> i. length (?l i)"
    let ?g = "\<lambda> i. inf_concat_simple ?l' i"
    obtain g where g: "\<And> i. g i = (let (ii,jj) = ?g i in ?l ii ! jj)" by auto    
    have len: "\<And> i j n. ?g n = (i,j) \<Longrightarrow> j < length (?l i)"
    proof -
      fix i j n
      assume n: "?g n = (i,j)"
      show "j < length (?l i)" 
      proof (cases n)
        case 0
        with n have "j = 0" by auto
        thus ?thesis by simp
      next
        case (Suc nn)
        obtain ii jj where nn: "?g nn = (ii,jj)" by (cases "?g nn", auto)
        show ?thesis 
        proof (cases "Suc jj < length (?l ii)")
          case True
          with nn Suc have "?g n = (ii, Suc jj)" by auto
          with n True show ?thesis by simp
        next
          case False 
          with nn Suc have "?g n = (Suc ii, 0)" by auto
          with n show ?thesis by simp
        qed
      qed
    qed      
    have gsteps: "\<And> i. (g i, g (Suc i)) \<in> R \<union> S"
    proof -
      fix n
      obtain i j where n: "?g n = (i, j)" by (cases "?g n", auto)
      show "(g n, g (Suc n)) \<in> R \<union> S"
      proof (cases "Suc j < length (?l i)")
        case True
        with n have "?g (Suc n) = (i, Suc j)" by auto
        with n have gn: "g n = ?l i ! j" and gsn: "g (Suc n) = ?l i ! (Suc j)" unfolding g by auto
        thus ?thesis using steps[of i] True by auto
      next
        case False
        with n have "?g (Suc n) = (Suc i, 0)" by auto
        with n have gn: "g n = ?l i ! j" and gsn: "g (Suc n) = a (Suc i)" unfolding g by auto
        from gn len[OF n] False have "j = length (?l i) - 1" by auto
        with gn have gn: "g n = last (?l i)" using last_conv_nth[of "?l i"] by auto
        from gn gsn show ?thesis using steps[of i] steps[of "Suc i"] by auto
      qed
    qed
    have infR:  "INFM j. (g j, g (Suc j)) \<in> R" unfolding INFM_nat_le
    proof
      fix n
      obtain i j where n: "?g n = (i,j)" by (cases "?g n", auto)
      from len[OF n] have j: "j < ?l' i" .
      let ?k = "?l' i - 1 - j"
      obtain k where k: "k = j + ?k" by auto
      from j k have k2: "k = ?l' i - 1" and k3: "j + ?k < ?l' i" by auto
      from inf_concat_simple_add[OF n, of ?k, OF k3] 
      have gnk: "?g (n + ?k) = (i, k)" by (simp only: k)
      hence "g (n + ?k) = ?l i ! k" unfolding g by auto
      hence gnk2: "g (n + ?k) = last (?l i)" using last_conv_nth[of "?l i"] k2 by auto
      from k2 gnk have "?g (Suc (n+?k)) = (Suc i, 0)" by auto
      hence gnsk2: "g (Suc (n+?k)) = a (Suc i)" unfolding g by auto
      from steps[of i] steps[of "Suc i"] have main: "(g (n+?k), g (Suc (n+?k))) \<in> R" 
        by (simp only: gnk2 gnsk2)
      show "\<exists> j \<ge> n. (g j, g (Suc j)) \<in> R" 
        by (rule exI[of _ "n + ?k"], auto simp: main[simplified])
    qed      
    from SN[unfolded rel_SN_alt.simps] gsteps infR show False by blast 
  qed
qed


lemma rel_SN_conv : "rel_SN = rel_SN_alt"
  by (intro ext, clarify, intro iffI, rule rel_SN_to_rel_SN_alt, simp, rule rel_SN_alt_to_rel_SN, simp)

lemma rel_SN_alt_r_empty : "rel_SN_alt ({}, S)"
unfolding rel_SN_alt.simps by auto

lemma rel_SN_alt_s_empty : "rel_SN_alt (R, {}) = SN R"
unfolding rel_SN_alt.simps SN_defs by auto

lemma rel_step_mono: assumes "R \<subseteq> R'" and "S \<subseteq> S'"
  shows "rel_step (R,S) \<subseteq> rel_step (R',S')" using assms rtrancl_mono unfolding rel_step.simps by blast


lemma rel_SN_mono': "R \<subseteq> R' \<Longrightarrow> S \<subseteq> R' \<union> S' \<Longrightarrow> rel_SN (R',S') \<Longrightarrow> rel_SN (R,S)"
  unfolding rel_SN_conv rel_SN_alt.simps INFM_nat_le by blast

lemma rel_SN_mono: assumes R: "R \<subseteq> R'" and S: "S \<subseteq> S'"
  and SN: "rel_SN (R',S')"
  shows "rel_SN (R,S)"
using SN
unfolding rel_SN_def using SN_subset[OF _ rel_step_mono[OF R S]]  by blast

lemmas rel_SN_alt_mono = rel_SN_mono[unfolded rel_SN_conv]

declare rel_SN_alt.simps[simp del]
declare rel_step.simps[simp del]

lemma rel_SN_imp_SN : assumes "rel_SN (R,S)" shows  "SN R"
proof
  fix f
  assume "\<forall> i. (f i, f (Suc i)) \<in> R"
  hence "\<And> i. (f i, f (Suc i)) \<in> rel_step (R, S)" unfolding rel_step.simps by blast  
  thus False using assms unfolding rel_SN_def SN_defs by blast
qed


lemma rel_step_trancl_conv : "(rel_step (R,S))^+ = ((R \<union> S))^* O R O ((R \<union> S))^*" (is "_ = ?RS^* O ?R O _")
proof
  show "?RS^* O ?R O ?RS^* \<subseteq> (rel_step (R,S))^+"
  proof(clarify, simp)
    fix x1 x2 x3 x4
    assume x12: "(x1,x2) \<in> ((R \<union> S))^*" and x23: "(x2,x3) \<in> R" and x34: "(x3,x4) \<in> ((R \<union> S))^*"
    let ?S = "S^*"
    {
      fix x y z
      assume "(y,z) \<in> ((R \<union> S))^*"
      hence "(x,y) \<in> rel_step (R,S) \<longrightarrow> (x,z) \<in> (rel_step (R,S))^+"
      proof (induct)
        case base
        show ?case by auto
      next
        case (step u z)
        show ?case
        proof
          assume "(x,y) \<in> rel_step (R,S)"
          with step have nearly: "(x,u) \<in> (rel_step (R,S))^+" by simp
          from step(2)
          show "(x,z) \<in> (rel_step (R,S))^+"
          proof
            assume "(u,z) \<in> R"
            hence "(u,z) \<in> rel_step (R,S)" unfolding rel_step.simps by auto
            with nearly show ?thesis by auto
          next
            assume uz: "(u,z) \<in> S"
            from nearly[unfolded trancl_unfold_right]
            obtain v where xv: "(x,v) \<in> (rel_step (R,S))^*" and vu: "(v,u) \<in> rel_step (R,S)" by auto
            from vu obtain w where vw: "(v,w) \<in> ?S O R" and wu: "(w,u) \<in> ?S" unfolding rel_step.simps by auto
            from wu uz have wz: "(w,z) \<in> ?S" by auto
            with vw have vz: "(v,z) \<in> rel_step (R,S)" unfolding rel_step.simps by auto
            with xv show ?thesis by auto
          qed
        qed
      qed
    } note steps_right = this
    from x23 have "(x2,x3) \<in> rel_step (R,S)" unfolding rel_step.simps by auto
    from mp[OF steps_right[OF x34] this] have x24: "(x2,x4) \<in> (rel_step (R,S))^+" .
    with x12 show "(x1,x4) \<in> (rel_step (R,S))^+" 
    proof (induct arbitrary: x4, simp)
      case (step y z) 
      from step(2)
      have "(y,x4) \<in> (rel_step (R,S))^+"
      proof
        assume "(y,z) \<in> R"
        hence "(y,z) \<in> rel_step (R,S)" unfolding rel_step.simps by auto
        with step(4) show ?thesis by auto
      next
        assume yz: "(y,z) \<in> S"
        from step(4)[unfolded trancl_unfold_left]
        obtain v where zv: "(z,v) \<in> rel_step (R,S)" and vx4: "(v,x4) \<in> (rel_step (R,S))^*" by auto
        from zv obtain w where zw: "(z,w) \<in> ?S" and wv: "(w,v) \<in> R O ?S" unfolding rel_step.simps by auto
        from yz zw have "(y,w) \<in> ?S" by auto
        with wv have "(y,v) \<in> rel_step (R,S)" unfolding rel_step.simps by auto
        with vx4 show ?thesis by auto
      qed
      from step(3)[OF this] show ?case .
    qed
  qed 
next
  have S: "S^* \<subseteq> ?RS^*" by (rule rtrancl_mono[of S "R \<union> S", simplified])
  have R: "R \<subseteq> ?RS^*" by auto
  show "(rel_step (R,S))^+ \<subseteq> ?RS^* O ?R O ?RS^*"
    unfolding rel_step.simps
  proof
    fix x y
    assume "(x,y) \<in> (S^* O R O S^*)^+"
    thus "(x,y) \<in> ?RS^* O ?R O ?RS^*"
    proof (induct)
      case (base y)
      thus ?case using S by blast 
    next
      case (step y z)
      from step(2) have "(y,z) \<in> ?RS^* O ?RS^* O ?RS^*" using R S by blast
      hence "(y,z) \<in> ?RS^*" by auto
      with step (3) show ?case by force
    qed
  qed
qed

lemma rel_step_Id: "rel_step (R,S \<union> Id) = rel_step (R,S)"
  by (simp add: rel_step.simps)

lemma rel_SN_Id:
  shows "rel_SN (R,S \<union> Id) = rel_SN (R,S)"
unfolding rel_SN_def by (simp only: rel_step_Id)


lemma rel_step_rtrancl: "rel_step (R,S^*) = rel_step (R,S)"
  unfolding rel_step.simps rtrancl_idemp by simp

lemma rel_SN_empty[simp]: "rel_SN (R,{}) = SN R"
  unfolding rel_SN_def rel_step.simps by auto

lemma rel_SN_ideriv: "rel_SN (R,S) = (\<not> (\<exists> as. ideriv R S as))" (is "?L = ?R")
proof
  assume ?L
  show ?R
  proof
    assume "\<exists> as. ideriv R S as"
    then obtain as where id: "ideriv R S as" by auto
    note id = id[unfolded ideriv_def]
    from `?L`[unfolded rel_SN_conv rel_SN_alt.simps, THEN spec[of _ as]]
      id obtain i where i: "\<And> j. j \<ge> i \<Longrightarrow> (as j, as (Suc j)) \<notin> R" by auto
    with id[unfolded INFM_nat, THEN conjunct2, THEN spec[of _ "Suc i"]] show False by auto
  qed
next
  assume ?R
  show ?L
    unfolding rel_SN_conv rel_SN_alt.simps 
  proof(intro allI impI)
    fix as
    assume "\<forall> i. (as i, as (Suc i)) \<in> R \<union> S"
    with `?R`[unfolded ideriv_def] have "\<not> (INFM i. (as i, as (Suc i)) \<in> R)" by auto
    from this[unfolded INFM_nat] obtain i where i: "\<And> j. i < j \<Longrightarrow> (as j, as (Suc j)) \<notin> R" by auto
    show "\<not> (INFM j. (as j, as (Suc j)) \<in> R)" unfolding INFM_nat using i by blast
  qed
qed


lemma rel_SN_map: fixes R Rw R' Rw' :: "'a ars" 
  defines A: "A \<equiv> R' \<union> Rw'"
  assumes SN: "rel_SN (R',Rw')" 
  and R: "\<And> s t. (s,t) \<in> R \<Longrightarrow> (f s, f t) \<in> A^* O R' O A^*"
  and Rw: "\<And> s t. (s,t) \<in> Rw \<Longrightarrow> (f s, f t) \<in> A^*"
  shows "rel_SN (R,Rw)" 
  unfolding rel_SN_def
proof
  fix g
  assume steps: "\<forall> i. (g i, g (Suc i)) \<in> rel_step (R, Rw)"
  let ?f = "\<lambda>i. (f (g i))"
  obtain h where h: "h = ?f" by auto
  {
    fix i
    let ?m = "\<lambda> (x,y). (f x, f y)"
    {
      fix s t
      assume "(s,t) \<in> Rw^*"
      hence "?m (s,t) \<in> A^*"
      proof (induct)
        case base show ?case by simp
      next
        case (step t u)
        from Rw[OF step(2)] step(3)
        show ?case by auto
      qed
    } note Rw = this
    from steps have "(g i, g (Suc i)) \<in> rel_step (R,Rw)" ..
    from this[unfolded rel_step.simps]
    obtain s t where gs: "(g i,s) \<in> Rw^*" and st: "(s,t) \<in> R" and tg: "(t, g (Suc i)) \<in> Rw^*" by auto
    from Rw[OF gs] R[OF st] Rw[OF tg]
    have step: "(?f i, ?f (Suc i)) \<in> A^* O (A^* O R' O A^*) O A^*"
      by auto
    have "(?f i, ?f (Suc i)) \<in> A^* O R' O A^*"
      by (rule set_mp[OF _ step], regexp)
    hence "(h i, h (Suc i)) \<in> (rel_step (R',Rw'))^+"
      unfolding A h rel_step_trancl_conv .
  }
  hence "\<not> SN ((rel_step (R',Rw'))^+)" by auto
  with SN_imp_SN_trancl[OF SN[unfolded rel_SN_def]]
  show False by simp
qed

datatype rel_SN_ext_type = top_s | top_ns | normal_s | normal_ns

fun rel_SN_ext_step :: "'a ars \<Rightarrow> 'a ars \<Rightarrow> 'a ars \<Rightarrow> 'a ars \<Rightarrow> rel_SN_ext_type \<Rightarrow> 'a ars"
  where "rel_SN_ext_step P Pw R Rw top_s = P"
      | "rel_SN_ext_step P Pw R Rw top_ns = Pw"
      | "rel_SN_ext_step P Pw R Rw normal_s = R"
      | "rel_SN_ext_step P Pw R Rw normal_ns = Rw"

(* relative termination with four relations as required in DP-framework *)
definition rel_SN_ext :: "'a ars \<Rightarrow> 'a ars \<Rightarrow> 'a ars \<Rightarrow> 'a ars \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "rel_SN_ext P Pw R Rw M \<equiv> (\<not> (\<exists> f t. 
       (\<forall> i. (f i, f (Suc i)) \<in> rel_SN_ext_step P Pw R Rw (t i))
     \<and> (\<forall> i. M (f i))
     \<and> (INFM i. t i \<in> {top_s,top_ns})
     \<and> (INFM i. t i \<in> {top_s,normal_s})))"

lemma rel_SN_ext_trans: fixes P Pw R Rw :: "'a ars" and M :: "'a \<Rightarrow> bool"
  defines M': "M' \<equiv> {(s,t). M t}"
  defines A: "A \<equiv> (P \<union> Pw \<union> R \<union> Rw) \<inter> M'"
  assumes "rel_SN_ext P Pw R Rw M" 
  shows "rel_SN_ext (A^* O (P \<inter> M') O A^*) (A^* O ((P \<union> Pw) \<inter> M') O A^*) (A^* O ((P \<union> R) \<inter> M') O A^*) (A^*) M" (is "rel_SN_ext ?P ?Pw ?R ?Rw M")
proof (rule ccontr)
  let ?relt = "rel_SN_ext_step ?P ?Pw ?R ?Rw"
  let ?rel = "rel_SN_ext_step P Pw R Rw" 
  assume "\<not> ?thesis"
  from this[unfolded rel_SN_ext_def]
  obtain f ty
    where steps: "\<And> i. (f i, f (Suc i)) \<in> ?relt (ty i)" 
    and min: "\<And> i. M (f i)"
    and inf1: "INFM i. ty i \<in> {top_s, top_ns}"
    and inf2: "INFM i. ty i \<in> {top_s, normal_s}"
    by auto
  let ?Un = "\<lambda> tt. \<Union> ?rel ` tt"
  let ?UnM = "\<lambda> tt. (\<Union> ?rel ` tt) \<inter> M'"
  let ?A = "?UnM {top_s,top_ns,normal_s,normal_ns}"
  let ?P' = "?UnM {top_s}"
  let ?Pw' = "?UnM {top_s,top_ns}"
  let ?R' = "?UnM {top_s,normal_s}"
  let ?Rw' = "?UnM {top_s,top_ns,normal_s,normal_ns}"
  have A: "A = ?A" unfolding A by auto
  have P: "(P \<inter> M') = ?P'" by auto
  have Pw: "(P \<union> Pw) \<inter> M' = ?Pw'" by auto
  have R: "(P \<union> R) \<inter> M' = ?R'" by auto
  have Rw: "A = ?Rw'" unfolding A ..
  {
    fix s t tt
    assume m: "M s" and st: "(s,t) \<in> ?UnM tt"
    hence "\<exists> typ \<in> tt. (s,t) \<in> ?rel typ \<and> M s \<and> M t" unfolding M' by auto
  } note one_step = this
  let ?seq = "\<lambda> s t g n ty. s = g 0 \<and> t = g n \<and> (\<forall> i < n. (g i, g (Suc i)) \<in> ?rel (ty i)) \<and> (\<forall> i \<le> n. M (g i))"
  {
    fix s t
    assume m: "M s" and st: "(s,t) \<in> A^*"
    from st[unfolded rtrancl_fun_conv]
    obtain g n where g0: "g 0 = s" and gn: "g n = t" and steps: "\<And> i. i < n \<Longrightarrow> (g i, g (Suc i)) \<in> ?A" unfolding A by auto
    {
      fix i
      assume "i \<le> n"
      have "M (g i)"
      proof (cases i)
        case 0
        show ?thesis unfolding 0 g0 by (rule m)
      next
        case (Suc j)
        with `i \<le> n` have "j < n" by auto
        from steps[OF this] show ?thesis unfolding Suc M' by auto
      qed
    } note min = this
    {
      fix i
      assume i: "i < n" hence i': "i \<le> n" by auto
      from i' one_step[OF min steps[OF i]]
      have "\<exists> ty. (g i, g (Suc i)) \<in> ?rel ty" by blast
    }
    hence "\<forall> i. (\<exists> ty. i < n \<longrightarrow> (g i, g (Suc i)) \<in> ?rel ty)" by auto
    from choice[OF this]
    obtain tt where steps: "\<And> i. i < n \<Longrightarrow> (g i, g (Suc i)) \<in> ?rel (tt i)" by auto
    from g0 gn steps min
    have "?seq s t g n tt" by auto
    hence "\<exists> g n tt. ?seq s t g n tt" by blast
  } note A_steps = this
  let ?seqtt = "\<lambda> s t tt g n ty. s = g 0 \<and> t = g n \<and> n > 0 \<and> (\<forall> i<n. (g i, g (Suc i)) \<in> ?rel (ty i)) \<and> (\<forall> i \<le> n. M (g i)) \<and> (\<exists> i < n. ty i \<in> tt)"
  {
    fix s t tt
    assume m: "M s" and st: "(s,t) \<in> A^* O ?UnM tt O A^*"
    then obtain u v where su: "(s,u) \<in> A^*" and uv: "(u,v) \<in> ?UnM tt" and vt: "(v,t) \<in> A^*"
      by auto
    from A_steps[OF m su] obtain g1 n1 ty1 where seq1: "?seq s u g1 n1 ty1" by auto
    from uv have "M v" unfolding M' by auto
    from A_steps[OF this vt] obtain g2 n2 ty2 where seq2: "?seq v t g2 n2 ty2" by auto
    from seq1 have "M u" by auto
    from one_step[OF this uv] obtain ty where ty: "ty \<in> tt" and uv: "(u,v) \<in> ?rel ty" by auto
    let ?g = "\<lambda> i. if i \<le> n1 then g1 i else g2 (i - (Suc n1))"
    let ?ty = "\<lambda> i. if i < n1 then ty1 i else if i = n1 then ty else ty2 (i - (Suc n1))"
    let ?n = "Suc (n1 + n2)"
    have ex: "\<exists> i < ?n. ?ty i \<in> tt"
      by (rule exI[of _ n1], simp add: ty)
    have steps: "\<forall> i < ?n. (?g i, ?g (Suc i)) \<in> ?rel (?ty i)"
    proof (intro allI impI)
      fix i
      assume "i < ?n"
      show "(?g i, ?g (Suc i)) \<in> ?rel (?ty i)"
      proof (cases "i \<le> n1")
        case True
        with seq1 seq2 uv show ?thesis by auto
      next
        case False
        hence "i = Suc n1 + (i - Suc n1)" by auto
        then obtain k where i: "i = Suc n1 + k" by auto
        with `i < ?n` have "k < n2" by auto
        thus ?thesis using seq2 unfolding i by auto
      qed
    qed
    from steps seq1 seq2 ex 
    have seq: "?seqtt s t tt ?g ?n ?ty" by auto
    have "\<exists> g n ty. ?seqtt s t tt g n ty" 
      by (intro exI, rule seq)
  } note A_tt_A = this
  let ?tycon = "\<lambda> ty1 ty2 tt ty' n. ty1 = ty2 \<longrightarrow> (\<exists>i < n. ty' i \<in> tt)"
  let ?seqt = "\<lambda> i ty g n ty'. f i = g 0 \<and> f (Suc i) = g n \<and> (\<forall> j < n. (g j, g (Suc j)) \<in> ?rel (ty' j)) \<and> (\<forall> j \<le> n. M (g j)) 
                \<and> (?tycon (ty i) top_s {top_s} ty' n)
                \<and> (?tycon (ty i) top_ns {top_s,top_ns} ty' n)
                \<and> (?tycon (ty i) normal_s {top_s,normal_s} ty' n)"
  {
    fix i
    have "\<exists> g n ty'. ?seqt i ty g n ty'"
    proof (cases "ty i")
      case top_s
      from steps[of i, unfolded top_s] 
      have "(f i, f (Suc i)) \<in> ?P" by auto
      from A_tt_A[OF min this[unfolded P]]
      show ?thesis unfolding top_s by auto
    next
      case top_ns
      from steps[of i, unfolded top_ns] 
      have "(f i, f (Suc i)) \<in> ?Pw" by auto
      from A_tt_A[OF min this[unfolded Pw]]
      show ?thesis unfolding top_ns by auto
    next
      case normal_s
      from steps[of i, unfolded normal_s] 
      have "(f i, f (Suc i)) \<in> ?R" by auto
      from A_tt_A[OF min this[unfolded R]]
      show ?thesis unfolding normal_s by auto
    next
      case normal_ns
      from steps[of i, unfolded normal_ns] 
      have "(f i, f (Suc i)) \<in> ?Rw" by auto
      from A_steps[OF min this]
      show ?thesis unfolding normal_ns by auto
    qed
  }
  hence "\<forall> i. \<exists> g n ty'. ?seqt i ty g n ty'" by auto
  from choice[OF this] obtain g where "\<forall> i. \<exists> n ty'. ?seqt i ty (g i) n ty'" by auto
  from choice[OF this] obtain n where "\<forall> i. \<exists> ty'. ?seqt i ty (g i) (n i) ty'" by auto
  from choice[OF this] obtain ty' where "\<forall> i. ?seqt i ty (g i) (n i) (ty' i)" by auto
  hence partial: "\<And> i. ?seqt i ty (g i) (n i) (ty' i)" ..
  (* it remains to concatenate all these finite sequences to an infinite one *)
  let ?ind = "inf_concat n"
  let ?g = "\<lambda> k. (\<lambda> (i,j). g i j) (?ind k)"
  let ?ty = "\<lambda> k. (\<lambda> (i,j). ty' i j) (?ind k)"
  have inf: "INFM i. 0 < n i"
    unfolding INFM_nat_le
  proof (intro allI)
    fix m
    from inf1[unfolded INFM_nat_le]
    obtain k where k: "k \<ge> m" and ty: "ty k \<in> {top_s, top_ns}" by auto
    show "\<exists> k \<ge> m. 0 < n k"
    proof (intro exI conjI, rule k)
      from partial[of k] ty show "0 < n k" by (cases "n k", auto)
    qed
  qed
  note bounds = inf_concat_bounds[OF inf]
  note inf_Suc = inf_concat_Suc[OF inf]
  note inf_mono = inf_concat_mono[OF inf]
  have "\<not> rel_SN_ext P Pw R Rw M"
    unfolding rel_SN_ext_def simp_thms
  proof (rule exI[of _ ?g], rule exI[of _ ?ty], intro conjI allI)
    fix k
    obtain i j where ik: "?ind k = (i,j)" by force
    from bounds[OF this] have j: "j < n i" by auto
    show "M (?g k)" unfolding ik using partial[of i] j by auto
  next
    fix k
    obtain i j where ik: "?ind k = (i,j)" by force
    from bounds[OF this] have j: "j < n i" by auto
    from partial[of i] j have step: "(g i j, g i (Suc j)) \<in> ?rel (ty' i j)" by auto
    obtain i' j' where isk: "?ind (Suc k) = (i',j')" by force
    have i'j': "g i' j' = g i (Suc j)"
    proof (rule inf_Suc[OF _ ik isk])
      fix i
      from partial[of i]
      have "g i (n i) = f (Suc i)" by simp
      also have "... = g (Suc i) 0" using partial[of "Suc i"] by simp
      finally show "g i (n i) = g (Suc i) 0" .
    qed
    show "(?g k, ?g (Suc k)) \<in> ?rel (?ty k)"
      unfolding ik isk split i'j'
      by (rule step)
  next
    show "INFM i. ?ty i \<in> {top_s, top_ns}"
      unfolding INFM_nat_le
    proof (intro allI)
      fix k
      obtain i j where ik: "?ind k = (i,j)" by force      
      from inf1[unfolded INFM_nat] obtain i' where i': "i' > i" and ty: "ty i' \<in> {top_s, top_ns}" by auto
      from partial[of i'] ty obtain j' where j': "j' < n i'" and ty': "ty' i' j' \<in> {top_s, top_ns}" by auto      
      from inf_concat_surj[of _ n, OF j'] obtain k' where ik': "?ind k' = (i',j')" ..        
      from inf_mono[OF ik ik' i'] have k: "k \<le> k'" by simp
      show "\<exists> k' \<ge> k. ?ty k' \<in> {top_s, top_ns}"
        by (intro exI conjI, rule k, unfold ik' split, rule ty')
    qed
  next
    show "INFM i. ?ty i \<in> {top_s, normal_s}"
      unfolding INFM_nat_le
    proof (intro allI)
      fix k
      obtain i j where ik: "?ind k = (i,j)" by force      
      from inf2[unfolded INFM_nat] obtain i' where i': "i' > i" and ty: "ty i' \<in> {top_s, normal_s}" by auto
      from partial[of i'] ty obtain j' where j': "j' < n i'" and ty': "ty' i' j' \<in> {top_s, normal_s}" by auto
      from inf_concat_surj[of _ n, OF j'] obtain k' where ik': "?ind k' = (i',j')" ..
      from inf_mono[OF ik ik' i'] have k: "k \<le> k'" by simp
      show "\<exists> k' \<ge> k. ?ty k' \<in> {top_s, normal_s}"
        by (intro exI conjI, rule k, unfold ik' split, rule ty')
    qed
  qed
  with assms show False by auto
qed


lemma rel_SN_ext_map: fixes P Pw R Rw P' Pw' R' Rw' :: "'a ars" and M M' :: "'a \<Rightarrow> bool"
  defines Ms: "Ms \<equiv> {(s,t). M' t}"
  defines A: "A \<equiv> (P' \<union> Pw' \<union> R' \<union> Rw') \<inter> Ms"
  assumes SN: "rel_SN_ext P' Pw' R' Rw' M'" 
  and P: "\<And> s t. M s \<Longrightarrow> M t \<Longrightarrow> (s,t) \<in> P \<Longrightarrow> (f s, f t) \<in> (A^* O (P' \<inter> Ms) O A^*) \<and> I t"
  and Pw: "\<And> s t. M s \<Longrightarrow> M t \<Longrightarrow> (s,t) \<in> Pw \<Longrightarrow> (f s, f t) \<in> (A^* O ((P' \<union> Pw') \<inter> Ms) O A^*) \<and> I t"
  and R: "\<And> s t. I s \<Longrightarrow> M s \<Longrightarrow> M t \<Longrightarrow> (s,t) \<in> R \<Longrightarrow> (f s, f t) \<in> (A^* O ((P' \<union> R') \<inter> Ms) O A^*) \<and> I t"
  and Rw: "\<And> s t. I s \<Longrightarrow> M s \<Longrightarrow> M t \<Longrightarrow> (s,t) \<in> Rw \<Longrightarrow> (f s, f t) \<in> A^* \<and> I t"
  shows "rel_SN_ext P Pw R Rw M" 
proof -
  note SN = rel_SN_ext_trans[OF SN]
  let ?P = "(A^* O (P' \<inter> Ms) O A^*)"
  let ?Pw = "(A^* O ((P' \<union> Pw') \<inter> Ms) O A^*)"
  let ?R = "(A^* O ((P' \<union> R') \<inter> Ms) O A^*)"
  let ?Rw = "A^*"
  let ?relt = "rel_SN_ext_step ?P ?Pw ?R ?Rw"
  let ?rel = "rel_SN_ext_step P Pw R Rw" 
  show ?thesis 
  proof (rule ccontr)
    assume "\<not> ?thesis"
    from this[unfolded rel_SN_ext_def]
    obtain g ty
      where steps: "\<And> i. (g i, g (Suc i)) \<in> ?rel (ty i)" 
      and min: "\<And> i. M (g i)"
      and inf1: "INFM i. ty i \<in> {top_s, top_ns}"
      and inf2: "INFM i. ty i \<in> {top_s, normal_s}"
      by auto
    from inf1[unfolded INFM_nat] obtain k where k: "ty k \<in> {top_s, top_ns}" by auto
    let ?k = "Suc k"
    let ?i = "shift id ?k"
    let ?f = "\<lambda> i. f (shift g ?k i)"
    let ?ty = "shift ty ?k"
    {
      fix i
      assume ty: "ty i \<in> {top_s,top_ns}"
      note m = min[of i] 
      note ms = min[of "Suc i"]
      from P[OF m ms]
        Pw[OF m ms]
        steps[of i]
        ty
      have "(f (g i), f (g (Suc i))) \<in> ?relt (ty i) \<and> I (g (Suc i))"
        by (cases "ty i", auto)
    } note stepsP = this
    {
      fix i
      assume I: "I (g i)"
      note m = min[of i] 
      note ms = min[of "Suc i"]
      from P[OF m ms]
        Pw[OF m ms]
        R[OF I m ms]
        Rw[OF I m ms]
        steps[of i]
      have "(f (g i), f (g (Suc i))) \<in> ?relt (ty i) \<and> I (g (Suc i))"
        by (cases "ty i", auto)
    } note stepsI = this
    {
      fix i
      have "I (g (?i i))"
      proof (induct i)
        case 0
        show ?case using stepsP[OF k] by simp
      next
        case (Suc i)
        from stepsI[OF Suc] show ?case by simp
      qed
    } note I = this
    have "\<not> rel_SN_ext ?P ?Pw ?R ?Rw M'"
      unfolding rel_SN_ext_def simp_thms
    proof (rule exI[of _ ?f], rule exI[of _ ?ty], intro allI conjI)
      fix i
      show "(?f i, ?f (Suc i)) \<in> ?relt (?ty i)"
        using stepsI[OF I[of i]] by auto
    next
      show "INFM i. ?ty i \<in> {top_s, top_ns}"
        unfolding Infm_shift[of "\<lambda>i. i \<in> {top_s,top_ns}" ty ?k]
        by (rule inf1)
    next
      show "INFM i. ?ty i \<in> {top_s, normal_s}"
        unfolding Infm_shift[of "\<lambda>i. i \<in> {top_s,normal_s}" ty ?k]
        by (rule inf2)
    next
      fix i
      have A: "A \<subseteq> Ms" unfolding A by auto
      from rtrancl_mono[OF this] have As: "A^* \<subseteq> Ms^*" by auto
      have PM: "?P \<subseteq> Ms^* O Ms O Ms^*" using As by auto
      have PwM: "?Pw \<subseteq> Ms^* O Ms O Ms^*" using As by auto
      have RM: "?R \<subseteq> Ms^* O Ms O Ms^*" using As by auto
      have RwM: "?Rw \<subseteq> Ms^*" using As by auto
      from PM PwM RM have "?P \<union> ?Pw \<union> ?R \<subseteq> Ms^* O Ms O Ms^*" (is "?PPR \<subseteq> _") by auto
      also have "... \<subseteq> Ms^+" by regexp
      also have "... = Ms"
      proof
        have "Ms^+ \<subseteq> Ms^* O Ms" by regexp
        also have "... \<subseteq> Ms" unfolding Ms by auto
        finally show "Ms^+ \<subseteq> Ms" .
      qed regexp
      finally have PPR: "?PPR \<subseteq> Ms" .
      show "M' (?f i)"
      proof (induct i)
        case 0
        from stepsP[OF k] k
        have "(f (g k), f (g (Suc k))) \<in> ?PPR" by (cases "ty k", auto)
        with PPR show ?case unfolding Ms by simp blast
      next
        case (Suc i)
        show ?case
        proof (cases "?ty i = normal_ns")
          case False
          hence "?ty i \<in> {top_s,top_ns,normal_s}"
            by (cases "?ty i", auto)
          with stepsI[OF I[of i]] have "(?f i, ?f (Suc i)) \<in> ?PPR"
            by auto
          from set_mp[OF PPR this] have "(?f i, ?f (Suc i)) \<in> Ms" .
          thus ?thesis unfolding Ms by auto
        next
          case True
          with stepsI[OF I[of i]] have "(?f i, ?f (Suc i)) \<in> ?Rw" by auto
          with RwM have mem: "(?f i, ?f (Suc i)) \<in> Ms^*" by auto
          thus ?thesis
          proof (cases)
            case base
            with Suc show ?thesis by simp
          next
            case step
            thus ?thesis unfolding Ms by simp
          qed
        qed
      qed
    qed
    with SN
    show False unfolding A Ms by simp
  qed
qed

(* and a version where it is assumed that f always preserves M and that R' and Rw' preserve M' *)
lemma rel_SN_ext_map_min: fixes P Pw R Rw P' Pw' R' Rw' :: "'a ars" and M M' :: "'a \<Rightarrow> bool"
  defines Ms: "Ms \<equiv> {(s,t). M' t}"
  defines A: "A \<equiv> P' \<inter> Ms \<union> Pw' \<inter> Ms \<union> R' \<union> Rw'"
  assumes SN: "rel_SN_ext P' Pw' R' Rw' M'" 
  and M: "\<And> t. M t \<Longrightarrow> M' (f t)"
  and M': "\<And> s t. M' s \<Longrightarrow> (s,t) \<in> R' \<union> Rw' \<Longrightarrow> M' t"
  and P: "\<And> s t. M s \<Longrightarrow> M t \<Longrightarrow> M' (f s) \<Longrightarrow> M' (f t) \<Longrightarrow> (s,t) \<in> P \<Longrightarrow> (f s, f t) \<in> (A^* O (P' \<inter> Ms) O A^*) \<and> I t"
  and Pw: "\<And> s t. M s \<Longrightarrow> M t \<Longrightarrow> M' (f s) \<Longrightarrow> M' (f t) \<Longrightarrow> (s,t) \<in> Pw \<Longrightarrow> (f s, f t) \<in> (A^* O (P' \<inter> Ms \<union> Pw' \<inter> Ms) O A^*) \<and> I t"
  and R: "\<And> s t. I s \<Longrightarrow> M s \<Longrightarrow> M t \<Longrightarrow> M' (f s) \<Longrightarrow> M' (f t) \<Longrightarrow> (s,t) \<in> R \<Longrightarrow> (f s, f t) \<in> (A^* O (P' \<inter> Ms \<union> R') O A^*) \<and> I t"
  and Rw: "\<And> s t. I s \<Longrightarrow> M s \<Longrightarrow> M t \<Longrightarrow> M' (f s) \<Longrightarrow> M' (f t) \<Longrightarrow> (s,t) \<in> Rw \<Longrightarrow> (f s, f t) \<in> A^* \<and> I t"
  shows "rel_SN_ext P Pw R Rw M"  
proof -
  let ?Ms = "{(s,t). M' t}"
  let ?A = "(P' \<union> Pw' \<union> R' \<union> Rw') \<inter> ?Ms"
  {
    fix s t
    assume s: "M' s" and "(s,t) \<in> A" 
    with M'[OF s, of t] have "(s,t) \<in> ?A \<and> M' t" unfolding Ms A by auto
  } note Aone = this
  {
    fix s t
    assume s: "M' s" and steps: "(s,t) \<in> A^*"
    from steps have "(s,t) \<in> ?A^* \<and> M' t"
    proof (induct)
      case base from s show ?case by simp
    next
      case (step t u)
      note one = Aone[OF step(3)[THEN conjunct2] step(2)] 
      from step(3) one
      have steps: "(s,u) \<in> ?A^* O ?A" by blast      
      have "(s,u) \<in> ?A^*" 
        by (rule set_mp[OF _ steps], regexp)
      with one show ?case by simp
    qed
  } note Amany = this      
  let ?P = "(A^* O (P' \<inter> Ms) O A^*)"
  let ?Pw = "(A^* O (P' \<inter> Ms \<union> Pw' \<inter> Ms) O A^*)"
  let ?R = "(A^* O (P' \<inter> Ms \<union> R') O A^*)"
  let ?Rw = "A^*"
  let ?P' = "(?A^* O (P' \<inter> ?Ms) O ?A^*)"
  let ?Pw' = "(?A^* O ((P' \<union> Pw') \<inter> ?Ms) O ?A^*)"
  let ?R' = "(?A^* O ((P' \<union> R') \<inter> ?Ms) O ?A^*)"
  let ?Rw' = "?A^*"
  show ?thesis 
  proof (rule rel_SN_ext_map[OF SN])
    fix s t
    assume s: "M s" and t: "M t" and step: "(s,t) \<in> P"
    from P[OF s t M[OF s] M[OF t] step]
    have "(f s, f t) \<in> ?P" and I: "I t"  by auto
    then obtain u v where su: "(f s, u) \<in> A^*" and uv: "(u,v) \<in> P' \<inter> Ms"
      and vt: "(v,f t) \<in> A^*" by auto
    from Amany[OF M[OF s] su] have su: "(f s, u) \<in> ?A^*" and u: "M' u" by auto
    from uv have v: "M' v" unfolding Ms by auto
    from Amany[OF v vt] have vt: "(v, f t) \<in> ?A^*" by auto
    from su uv vt I 
    show "(f s, f t) \<in> ?P' \<and> I t" unfolding Ms by auto
  next
    fix s t
    assume s: "M s" and t: "M t" and step: "(s,t) \<in> Pw"
    from Pw[OF s t M[OF s] M[OF t] step]
    have "(f s, f t) \<in> ?Pw" and I: "I t"  by auto
    then obtain u v where su: "(f s, u) \<in> A^*" and uv: "(u,v) \<in> P' \<inter> Ms \<union> Pw' \<inter> Ms"
      and vt: "(v,f t) \<in> A^*" by auto
    from Amany[OF M[OF s] su] have su: "(f s, u) \<in> ?A^*" and u: "M' u" by auto
    from uv have uv: "(u,v) \<in> (P' \<union> Pw') \<inter> ?Ms" and v: "M' v" unfolding Ms 
      by auto
    from Amany[OF v vt] have vt: "(v, f t) \<in> ?A^*" by auto
    from su uv vt I 
    show "(f s, f t) \<in> ?Pw' \<and> I t"  by auto
  next
    fix s t
    assume I: "I s" and s: "M s" and t: "M t" and step: "(s,t) \<in> R"
    from R[OF I s t M[OF s] M[OF t] step]
    have "(f s, f t) \<in> ?R" and I: "I t"  by auto
    then obtain u v where su: "(f s, u) \<in> A^*" and uv: "(u,v) \<in> P' \<inter> Ms \<union> R'"
      and vt: "(v,f t) \<in> A^*" by auto
    from Amany[OF M[OF s] su] have su: "(f s, u) \<in> ?A^*" and u: "M' u" by auto
    from uv M'[OF u, of v] have uv: "(u,v) \<in> (P' \<union> R') \<inter> ?Ms" and v: "M' v" unfolding Ms 
      by auto
    from Amany[OF v vt] have vt: "(v, f t) \<in> ?A^*" by auto
    from su uv vt I 
    show "(f s, f t) \<in> ?R' \<and> I t"  by auto
  next
    fix s t
    assume I: "I s" and s: "M s" and t: "M t" and step: "(s,t) \<in> Rw"
    from Rw[OF I s t M[OF s] M[OF t] step]
    have steps: "(f s, f t) \<in> ?Rw" and I: "I t"  by auto
    from Amany[OF M[OF s] steps] I
    show "(f s, f t) \<in> ?Rw' \<and> I t"  by auto
  qed
qed


end
