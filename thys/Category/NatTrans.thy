(*  Title:       Category theory using Isar and Locales
    ID:          $Id: NatTrans.thy,v 1.5 2005-10-20 18:43:32 nipkow Exp $
    Author:      Greg O'Keefe, June, July, August 2003
*)

(* define natural transformation, prove that the identity arrow function is one *)
theory NatTrans
imports Functors
begin

section{* Natural Transformations *}

(* guess the third axiom is implied by the fifth *)
locale natural_transformation = two_cats + var F + var G + var u +
  assumes "Functor F : AA \<longrightarrow> BB"
  and "Functor G : AA \<longrightarrow> BB"
  and "u : ob AA \<rightarrow> ar BB"
  and "u \<in> extensional (ob AA)"
  and "\<forall>A\<in>Ob. u A \<in> Hom\<^sub>2 (F\<^sub>\<o> A) (G\<^sub>\<o> A)" 
  and "\<forall>A\<in>Ob. \<forall>B\<in>Ob. \<forall>f\<in>Hom A B. (G\<^sub>\<a> f) \<bullet>\<^sub>2 (u A) = (u B) \<bullet>\<^sub>2 (F\<^sub>\<a> f)"

syntax
  "_nt" :: "[  ('o1 \<Rightarrow> 'a1),
  ('o1,'a1,'o2,'a2,'mf)functor_scheme,
  ('o1,'a1,'o2,'a2,'mf)functor_scheme,
  ('o1,'a1,'m1)category_scheme, 
  ('o2,'a2,'m2)category_scheme] \<Rightarrow> bool" ("_ : _ \<Rightarrow> _ in Func '(_ , _ ')" [81])
translations
  "u : F \<Rightarrow> G in Func(AA,BB)" \<rightleftharpoons> "natural_transformation AA BB F G u"

(* is this doing what I think its doing? *)
locale endoNT = natural_transformation + one_cat

theorem (in endoNT) id_restrict_natural:
  "(\<lambda>A\<in>Ob. Id A) : (id_func AA) \<Rightarrow> (id_func AA) in Func(AA,AA)"
proof (intro natural_transformation.intro natural_transformation_axioms.intro 
    two_cats_axioms.intro ballI)
  show "(\<lambda>A\<in>Ob. Id A) : Ob \<rightarrow> Ar"
    by (rule funcsetI) auto
  show "(\<lambda>A\<in>Ob. Id A) \<in> extensional (Ob)"
    by (rule restrict_extensional)
  fix A 
  assume A_object: "A \<in> Ob" 
  hence "Id A \<in> Hom A A" ..
  with A_object 
  show "(\<lambda>X\<in>Ob. Id X) A \<in> Hom ((id_func AA)\<^sub>\<o> A)  ((id_func AA)\<^sub>\<o> A)"
    by (simp add: id_func_def) 
  fix B and f
  assume B_object: "B \<in> Ob" 
    and "f \<in> Hom A B"
  hence "f \<in> Ar" and "A = Dom f" and "B = Cod f" and "Dom f \<in> Ob" and "Cod f \<in> Ob"
    by (simp_all add: hom_def)
  thus "(id_func AA)\<^sub>\<a> f \<bullet> (\<lambda>A\<in>Ob. Id A) A
    = (\<lambda>A\<in>Ob. Id A) B \<bullet> (id_func AA)\<^sub>\<a> f"
    by (simp add:  id_func_def)
qed (simp_all, assumption, assumption, rule id_func_functor, rule id_func_functor)

end