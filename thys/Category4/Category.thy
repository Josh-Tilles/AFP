theory Category
imports "~~/src/HOL/Library/FuncSet"
begin

record ('o, 'm) Category =
  Obj :: "'o set" ("obj\<index>" 70)
  Mor :: "'m set" ("mor\<index>" 70)
  Dom :: "'m \<Rightarrow> 'o" ("dom\<index> _" [80] 70)
  Cod :: "'m \<Rightarrow> 'o" ("cod\<index> _" [80] 70)
  Id  :: "'o \<Rightarrow> 'm" ("id\<index> _" [80] 75)
  Comp :: "'m \<Rightarrow> 'm \<Rightarrow> 'm" (infixl ";;\<index>" 70)

(* Records are defined surprisingly late in the HOL hierarchy of dependencies.
Would it be possible to use more fundamental mechanisms? *)
locale AltCategory =
  fixes Obj :: "'o set"
    and Mor :: "'m set"
    and Dom :: "'m \<Rightarrow> 'o"
    and Cod :: "'m \<Rightarrow> 'o"
    and Id  :: "'o \<Rightarrow> 'm"
    and Comp :: "'m \<Rightarrow> 'm \<Rightarrow> 'm"

definition
  MapsTo :: "('o, 'm, 'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> bool" ("_ maps\<index> _ to _" [60, 60, 60] 65) where
  "MapsTo CC f X Y \<equiv> f \<in> Mor CC \<and> Dom CC f = X \<and> Cod CC f = Y"

(* The three conditions seem a little awkward. Are there any
benefits to putting them into a locale? *)
locale AltMapsTo =
  fixes CC :: "('o, 'm, 'a) Category_scheme"
    and f :: 'm
    and X :: 'o
    and Y :: 'o
  assumes "f \<in> Mor CC"
      and "Dom CC f = X"
      and "Cod CC f = Y"

definition
  CompDefined :: "('o, 'm, 'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> bool" (infixl "\<approx>>\<index>" 65) where
  "CompDefined CC f g \<equiv> f \<in> Mor CC \<and> g \<in> Mor CC \<and> Cod CC f = Dom CC g"
  
(* @TODO is there a way to utilize `inductive` to get definitions `CompDefined` and/or `MapsTo` that are nicer to work with? (See "Logic-free reasoning in Isabelle/HOL") *)

locale ExtCategory =
  fixes C :: "('o, 'm, 'a) Category_scheme" (structure)
  assumes CdomExt: "(Dom C) \<in> extensional (Mor C)"
      and CcodExt: "(Cod C) \<in> extensional (Mor C)"
      and CidExt:  "(Id C) \<in> extensional (Obj C)"
      and CcompExt: "(split (Comp C)) \<in> extensional { (f, g) | f g . f \<approx>> g}"

locale Category = ExtCategory +
  assumes Cdom: "f \<in> mor \<Longrightarrow> dom f \<in> obj"
      and Ccod: "f \<in> mor \<Longrightarrow> cod f \<in> obj"
      and Cidm (*[dest]*): "X \<in> obj \<Longrightarrow> (id X) maps X to X"
      and Cidl: "f \<in> mor \<Longrightarrow> id (dom f) ;; f = f"
      and Cidr: "f \<in> mor \<Longrightarrow> f ;; id (cod f) = f"
      and Cassoc: "\<lbrakk>f \<approx>> g; g \<approx>> h\<rbrakk> \<Longrightarrow> (f ;; g) ;; h = f ;; (g ;; h)"
      and Ccompt: "\<lbrakk>f maps X to Y; g maps Y to Z\<rbrakk> \<Longrightarrow> (f ;; g) maps X to Z"

definition
  MakeCat :: "('o, 'm, 'a) Category_scheme \<Rightarrow> ('o, 'm, 'a) Category_scheme" where
  "MakeCat C \<equiv> \<lparr>
    Obj = Obj C,
    Mor = Mor C,
    Dom = restrict (Dom C) (Mor C),
    Cod = restrict (Cod C) (Mor C),
    Id  = restrict (Id C) (Obj C),
    Comp = \<lambda> f g . (restrict (split (Comp C)) {(f,g) | f g. f \<approx>>\<^bsub>C\<^esub> g}) (f, g),
    \<dots> = Category.more C
  \<rparr>"

lemma MakeCatMapsTo: 
  assumes "f maps\<^bsub>C\<^esub> X to Y"
  shows "f maps\<^bsub>MakeCat C\<^esub> X to Y"
  using assms
  apply (unfold MakeCat_def)
  apply (unfold MapsTo_def)
  apply simp
  done

(* @TODO
is there a way to represent a local proof strategy? Like, all of these "MakeCat" lemmas are proved the exact same way. *)

lemma MakeCatComp:
  assumes "f \<approx>>\<^bsub>C\<^esub> g"
  shows "f ;;\<^bsub>MakeCat C\<^esub> g = f ;;\<^bsub>C\<^esub> g"
  using assms
  apply (unfold MakeCat_def)
  apply simp
  done

lemma MakeCatId:
  assumes "X \<in> obj\<^bsub>C\<^esub>"
  shows "id\<^bsub>C\<^esub> X = id\<^bsub>MakeCat C\<^esub> X"
  using assms
  apply (unfold MakeCat_def)
  apply simp
  done

lemma MakeCatObj: "obj\<^bsub>MakeCat C\<^esub> = obj\<^bsub>C\<^esub>"
  apply (unfold MakeCat_def)
  apply simp
  done

lemma MakeCatMor: "mor\<^bsub>MakeCat C\<^esub> = mor\<^bsub>C\<^esub>"
  apply (unfold MakeCat_def)
  apply simp
  done


lemma MakeCatDom: "f \<in> mor\<^bsub>C\<^esub> \<Longrightarrow> dom\<^bsub>C\<^esub> f = dom\<^bsub>MakeCat C\<^esub> f"
by (simp add: MakeCat_def)

lemma MakeCatCod: "f \<in> mor\<^bsub>C\<^esub> \<Longrightarrow> cod\<^bsub>C\<^esub> f = cod\<^bsub>MakeCat C\<^esub> f"
by (simp add: MakeCat_def)


lemma MakeCatCompDef: "f \<approx>>\<^bsub>MakeCat C\<^esub> g = f \<approx>>\<^bsub>C\<^esub> g"
by (auto simp add: CompDefined_def MakeCat_def)

lemma MakeCatComp2: "f \<approx>>\<^bsub>MakeCat C\<^esub> g \<Longrightarrow> f ;;\<^bsub>MakeCat C\<^esub> g = f ;;\<^bsub>C\<^esub> g"
by (simp add: MakeCatCompDef MakeCatComp)


lemma ExtCategoryMakeCat: "ExtCategory (MakeCat C)" sorry

lemma MakeCat: 
  assumes "Category_axioms C"
  shows "Category (MakeCat C)"
sorry

lemma (in Category) MapsToE (*[elim]*):
  assumes "f maps X to Y"
    and "\<lbrakk>f \<in> mor; dom f = X; cod f = Y\<rbrakk> \<Longrightarrow> R"
  shows "R"
using assms by (unfold MapsTo_def) (elim conjE)

lemma (in Category) MapsToI (*[intro]*):
  assumes "f \<in> mor"
    and "dom f = X"
    and "cod f = Y"
  shows "f maps X to Y"
(*
  unfolding MapsTo_def
  using assms by iprover
*)
apply (unfold MapsTo_def)
apply (intro conjI)
using assms(1) apply assumption
using assms(2) apply assumption
using assms(3) apply assumption
done

lemma (in Category) CompDefinedE (*[elim]*):
  assumes "f \<approx>> g"
      and "\<lbrakk>f \<in> mor; g \<in> mor; cod f = dom g\<rbrakk> \<Longrightarrow> R"
  shows "R"
using assms by (unfold CompDefined_def) (elim conjE)

lemma (in Category) CompDefinedI (*[intro]*):
  assumes "f \<in> mor"
    and "g \<in> mor"
    and "cod f = dom g"
  shows "f \<approx>> g"
using assms unfolding CompDefined_def by iprover


    
lemma "\<lbrakk>a=b; c=b\<rbrakk> \<Longrightarrow> a=c"

oops

lemma (in Category) MapsToCompI:
  assumes "f \<approx>> g"
  shows "(f ;; g) maps (dom f) to (cod g)"
proof (rule Ccompt) (* taking the route of MapsToI, in this circumstance, leads to a world of hurt *)
  from assms have "f \<in> mor" and "g \<in> mor" and "cod f = dom g" by (simp_all only: CompDefined_def)
  let ?X = "dom f" and ?Y = "cod f" and ?Z = "cod g"
  show "f maps ?X to ?Y" using `f \<in> mor` by (rule expand_dom_cod)
  have "g maps (dom g) to (cod g)" using `g \<in> mor` by (rule expand_dom_cod)
  with `cod f = dom g` show "g maps ?Y to ?Z" by (rule forw_subst)
qed

lemma (in Category) MapsToCompDef:
  assumes "f maps X to Y" and "g maps Y to Z"
  shows "f \<approx>> g"
proof (rule CompDefinedI)
  from `f maps X to Y` show "f \<in> mor" by (rule MapsToE)
  from `g maps Y to Z` show "g \<in> mor" by (rule MapsToE)
  have "cod f = Y" using `f maps X to Y` by (rule MapsToE)
  moreover have "dom g = Y" using `g maps Y to Z` by (rule MapsToE)
  ultimately show "cod f = dom g" by (rule trans_sym)
qed

lemma (in Category) MapsToMorCodDom:
  assumes "f \<approx>> g"
  shows "f;;g \<in> mor" and "dom (f;;g) = dom f" and "cod (f;;g) = cod g"
oops

lemma (in Category) MapsToMor:
  assumes "f \<approx>> g"
  shows "f;;g \<in> mor"
proof -
  from `f \<approx>> g` have "(f;;g) maps (dom f) to (cod g)" by (rule MapsToCompI)
  thus "f;;g \<in> mor" by (rule MapsToE)
qed
  
lemma (in Category) MapsToDom:
  assumes "f \<approx>> g"
  shows "dom (f;;g) = dom f"
proof -
  from `f \<approx>> g` have "(f;;g) maps (dom f) to (cod g)" by (rule MapsToCompI)
  thus "dom (f;;g) = dom f" by (rule MapsToE)
qed

lemma (in Category) MapsToCod:
  assumes "f \<approx>> g"
  shows "cod (f;;g) = cod g"
proof -
  from `f \<approx>> g` have "(f;;g) maps (dom f) to (cod g)" by (rule MapsToCompI)
  thus "cod (f;;g) = cod g" by (rule MapsToE)
qed

  

lemma (in Category) CatIdDom [simp]:
  assumes "X \<in> obj"
  shows "dom (id X) = X"
proof -
  from `X \<in> obj` have "(id X) maps X to X" by (rule Cidm)
  thus "dom (id X) = X" by (rule MapsToE)
qed

lemma (in Category) CatIdCod [simp]:
  assumes "X \<in> obj"
  shows "cod (id X) = X"
proof -
  from `X \<in> obj` have "(id X) maps X to X" by (rule Cidm)
  thus "cod (id X) = X" by (rule MapsToE)
qed

lemma (in Category) o_is_m:
  assumes "X \<in> obj"
  shows "id X \<in> mor"
proof -
  from `X \<in> obj` have "(id X) maps X to X" by (rule Cidm)
  thus "id X \<in> mor" by (rule MapsToE)
qed



lemma (in Category) MapsToObj:
  assumes "f maps X to Y"
  shows "X \<in> obj" and "Y \<in> obj"
oops

lemma (in Category) MapsToDomObj:
  assumes "f maps X to Y"
  shows "X \<in> obj"
proof -
  have "f \<in> mor" and "dom f = X" using assms by (auto elim: MapsToE)
  from `f \<in> mor` have "dom f \<in> obj" by (rule Cdom)
  with `dom f = X` show "X \<in> obj" by (rule subst)
qed

(* just for kicks and giggles, I "implemented" these two proofs in contrasting ways. *)

lemma (in Category) MapsToCodObj:
  assumes "f maps X to Y"
  shows "Y \<in> obj"
proof -
  from assms have "f \<in> mor" and "cod f = Y" by (simp_all only: MapsTo_def)
  have "cod f \<in> obj" using `f \<in> mor` by (rule Ccod)
  then show "Y \<in> obj" using `cod f = Y` by (rule back_subst)
qed

(* @TODO in there a way to define a sufficient predicate for injectivity? *)
lemma (in Category) IdInj:
  assumes "X \<in> obj" and "Y \<in> obj" and "id X = id Y"
  shows "X = Y"
proof -
  from `X \<in> obj` have "(id X) maps X to X" by (rule Cidm)
  with `id X = id Y` have "(id Y) maps X to X" by (rule subst)
  hence "dom (id Y) = X" by (rule MapsToE)
  also have "dom (id Y) = Y" using `Y \<in> obj` by (rule CatIdDom)
  finally show "X = Y" by (rule sym)
qed 

lemma "inj_on (Id C) (Obj C)"
apply (rule inj_onI)
sorry



lemma (in Category) CompDefComp:
  assumes "f \<approx>> g" and "g \<approx>> h"
  shows "f \<approx>> (g ;; h)" and "(f ;; g) \<approx>> h"
proof -
  show "f \<approx>> (g ;; h)"
  proof (rule CompDefinedI)
    from `f \<approx>> g` show "f \<in> mor" by (rule CompDefinedE)
    from `g \<approx>> h` show "g;;h \<in> mor" by (rule MapsToMor) (* MapsToMorDomCod *)
    from `g \<approx>> h` (* @TODO ugly, redundant *)
      have "dom g = dom (g;;h)" by (rule MapsToDom[THEN sym]) (* also ugly *)
    
    from `f \<approx>> g` have "cod f = dom g" by (rule CompDefinedE)
    also from `g \<approx>> h` have "\<dots> = dom (g;;h)" by (simp only: MapsToDom)
    finally show "cod f = dom (g;;h)" .
  qed
  show "f ;; g \<approx>> h" (* what follows is a different way of proving something VERY similar. *)
  proof (rule CompDefinedI)
    show "f;;g \<in> mor" using `f \<approx>> g` by (rule MapsToMor)
    show "h \<in> mor" using `g \<approx>> h` by (rule CompDefinedE)
    show "cod (f;;g) = dom h"
    proof -
      have "cod (f;;g) = cod g" using `f \<approx>> g` by (simp only: MapsToCod)
      also have "\<dots> = dom h" using `g \<approx>> h` by (rule CompDefinedE)
      finally show ?thesis .
    qed
  qed
qed

lemma (in Category) CatIdInMor:
  assumes "X \<in> obj"
  shows "id X \<in> mor"
proof -
  have "(id X) maps X to X" using assms by (rule Cidm)
  thus "(id X) \<in> mor" by (rule MapsToE)
qed

lemma (in Category) MapsToId:
  assumes "X \<in> obj"
  shows "id X \<approx>> id X"
(* we could do `proof (rule CompDefinedI)`, but what feels more mathematically natural to me is to use MapsToCompDef *)
proof -
  let ?A = "X" and ?B = "X" and ?C = "X"
  from `X \<in> obj` have "(id X) maps ?A to ?B" by (rule Cidm)
  moreover have "(id X) maps ?B to ?C" using assms by (rule Cidm)
  ultimately show "(id X) \<approx>> (id X)" by (rule MapsToCompDef)
qed


lemmas (in Category) Simps = Cdom Ccod Cidm Cidl Cidr MapsToCompI IdInj MapsToId

section "break"
section "Sections and Retractions, Monomorphisms and Epimorphisms"
section "Inversions and Isomorphisms"

lemma (in Category) LeftRightInvUniq:
  shows False
oops

lemmas (in Category) CatIdDomCod = CatIdDom CatIdCod

lemma (in Category) CatIdCompId:
  assumes "X \<in> obj"
  shows "id X ;; id X = id X"
proof -
thm Cidr
oops

lemma (in Category) AltCidr:
  assumes "f maps A to B"
  shows "f ;; (id B) = f"
proof -
  have "f \<in> mor" using assms by (rule MapsToE)
  hence "f ;; (id (cod f)) = f" by (rule Cidr)
  thus "f ;; (id B) = f"
  proof -
    have "cod f = B" using `f maps A to B` by (rule MapsToE)
    with `f ;; (id (cod f)) = f` show ?thesis by (rule back_subst)
  qed
qed

lemma (in Category) CatIdCompId:
  assumes "X \<in> obj"
  shows "id X ;; id X = id X"
proof -
  from `X \<in> obj` have "id X maps X to X" by (rule Cidm)
  thus ?thesis by (rule AltCidr)
qed

lemma (in Category) CatIdUniqR:
  assumes iota: "\<iota> maps X to X"
  and     rid: "\<forall>f. f \<approx>> \<iota> \<longrightarrow> f ;; \<iota> = f"
  shows "id X = \<iota>"
proof -
  have "\<iota> = id X ;; \<iota>" sorry (* rule Cidl *)
  also have "\<dots> = id X" sorry (* rule rid *)
  finally show "id X = \<iota>" by (rule sym)
(* qed *)
oops

lemma (in Category) CatIdUniqR:
  assumes iota: "\<iota> maps X to X"
  and     rid: "\<forall>f. f \<approx>> \<iota> \<longrightarrow> f ;; \<iota> = f"
  shows "id X = \<iota>"
proof -
  from rid have "id X \<approx>> \<iota> \<longrightarrow> id X ;; \<iota> = id X" by (rule allE)
  moreover have "id X \<approx>> \<iota>"
  proof -
    from iota have "X \<in> obj" by (rule MapsToDomObj)
    hence "(id X) maps X to X" by (rule Cidm)
    moreover note iota
    ultimately show "id X \<approx>> \<iota>" by (rule MapsToCompDef)
  qed
  ultimately have "id X ;; \<iota> = id X" by (rule mp)
  hence "id X = id X ;; \<iota>" by (rule sym)
  also have "\<dots> = \<iota>" sorry (* rule Cidl *)
  ultimately

oops

lemma (in Category) AltCidl:
  assumes "f maps A to B"
  shows "(id A) ;; f = f"
sorry

lemma (in Category) CatIdUniqR:
  assumes iota: "\<iota> maps X to X"
  and     rid: "\<forall>f. f \<approx>> \<iota> \<longrightarrow> f ;; \<iota> = f"
  shows "id X = \<iota>"
proof -
  from rid have "id X \<approx>> \<iota> \<longrightarrow> id X ;; \<iota> = id X" by (rule allE)
  moreover have "id X \<approx>> \<iota>"
  proof -
    from iota have "X \<in> obj" by (rule MapsToDomObj)
    hence "(id X) maps X to X" by (rule Cidm)
    moreover note iota
    ultimately show "id X \<approx>> \<iota>" by (rule MapsToCompDef)
  qed
  ultimately have "id X ;; \<iota> = id X" by (rule mp)
  hence "id X = id X ;; \<iota>" by (rule sym)
  also have "\<dots> = \<iota>" using iota by (rule AltCidl)
  finally show "id X = \<iota>"
    apply (rule trans)
    apply (rule refl)
    done
qed




(* ... *)

definition inverse :: "('o, 'm, 'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> 'm" ("Cinv\<index> _" [70]) where
  "inverse C f \<equiv> THE g . inverse_rel C f g"

(* ... *)

lemma (in Category) IsoCompose:
  assumes "f \<approx>> g" and "ciso f" and "ciso g"
  shows "ciso (f ;; g)" and "Cinv (f;;g) = (Cinv g) ;; (Cinv f)"
proof -
  show "Cinv (f ;; g) = (Cinv g) ;; (Cinv f)"
  
  have "ciso (f ;; g) \<longleftrightarrow> (\<exists>h. cinv (f;;g) h)"
    apply (unfold isomorphism_def)
    apply (rule refl)
    done
  moreover have "\<dots>"
  (* proof (intro exI inverse_relI) *) sorry
  from `ciso f` obtain finv where "cinv f finv"
    apply (unfold isomorphism_def)
    apply (erule exE)
    apply assumption (* weird step *)
    done
  
  apply (unfold isomorphism_def)
proof -
  
oops

(* Exercise II.1.T *)
lemma (in Category)
  assumes "f \<approx>> g" and "ciso f" and "ciso g"
  shows "ciso (f ;; g)"
  apply (unfold isomorphism_def)
  apply (rule exI)
  apply (rule inverse_relI)
oops (* it's not worth separating into two lemmas because you can't really prove the exercise without constructing the content of the second lemma *)

(*
declare Category.Cidm [dest]
declare Category.MapsToE[elim]
declare Category.MapsToI[intro]
declare Category.CompDefinedE[elim]
(* declare Category.CompDefinedI[intro] *)
declare Category.inverse_relE[elim]
declare (in Category) Cidm [dest]
declare (in Category) MapsToE[elim]
declare (in Category) MapsToI[intro]
declare (in Category) CompDefinedE[elim]
(* declare (in Category) CompDefinedI[intro] *)
declare (in Category) inverse_relE[elim]
(* in Topoi book, right? *)
*)
lemma (in Category)
  assumes "f \<approx>> g" and "ciso f" and "ciso g"
  shows "Cinv (f ;; g) = (Cinv g) ;; (Cinv f)"
  apply (subst inverse_def)
  using [[rule_trace]] apply rule (* I think it's `HOL.the_equality` *)
    apply (rule inverse_relI)
        apply (rule CompDefinedI)
        oops

lemma (in Category) temporary_name_2:
  assumes "f \<approx>> g" shows "(f;;g) \<in> mor"
proof -
  from assms have "(f;;g) maps (dom f) to (cod g)" by (rule MapsToCompI)
  thus "(f;;g) \<in> mor" by (rule MapsToE)
qed

lemma (in Category) "dom g = cod (Cinv g)" and "cod g = dom (Cinv g)"
oops

lemma (in Category) Exercise_10__Article_II:
  assumes "f \<approx>> g" and "ciso f" and "ciso g"
  shows "Cinv (f;;g) = (Cinv g) ;; (Cinv f)"
proof -
  have "(Cinv (f;;g) = (Cinv g) ;; (Cinv f)) \<longleftrightarrow> ((THE h . cinv (f;;g) h) = (Cinv g) ;; (Cinv f))"
    unfolding inverse_def
    by (rule refl)
  moreover have "(THE h . cinv (f;;g) h) = (Cinv g) ;; (Cinv f)"
  proof (rule the_equality)
    show "cinv (f;;g) ((Cinv g) ;; (Cinv f))"
    proof (rule inverse_relI)
      show "f;;g \<approx>> (Cinv g) ;; (Cinv f)"
      proof (rule CompDefinedI)
        note `f \<approx>> g`
        thus "(f;;g) \<in> mor" by (rule temporary_name_2)
        have "(Cinv g) \<approx>> (Cinv f)" sorry
        thus "((Cinv g) ;; (Cinv f)) \<in> mor" by (rule temporary_name_2)
        show "cod (f ;; g) = dom ((Cinv g) ;; (Cinv f))"
        proof -
          note `f \<approx>> g` 
          hence "cod (f ;; g) = cod g" by (rule MapsToCod)
oops

(* ... *)
lemma (in Category)
  assumes "ciso f"
  shows "\<exists>!g. cinv f g"
sorry

definition (in Category)
  "inverses f g \<longleftrightarrow> f ;; g = id (dom f) \<and> g ;; f = id (cod f)"
lemma (in Category) "inverses f g \<Longrightarrow> inverses g f" unfolding inverses_def oops

definition
  UnitCategory :: "(unit, unit) Category" where
  "UnitCategory \<equiv> MakeCat \<lparr>
    Obj = { () },
    Mor = { () },
    Dom = (\<lambda>f. () ),
    Cod = (\<lambda>f. () ),
    Id = (\<lambda>f. () ),
    Comp = (\<lambda> f g . () )
  \<rparr>"

lemma (* [simp] *) "Category UnitCategory"
sorry

definition
  OppositeCategory :: "('o,'m,'a) Category_scheme \<Rightarrow> ('o,'m,'a) Category_scheme" ("Op _" [65] 65) where
  "OppositeCategory C \<equiv> \<lparr>
    Obj = Obj C,
    Mor = Mor C,
    Dom = Cod C,
    Cod = Dom C,
    Id = Id C,
    Comp = (\<lambda>f g. g ;;\<^bsub>C\<^esub> f),
    \<dots> = Category.more C
   \<rparr>"

lemma OpCatOpCat: "Op (Op C) = C"
sorry

definition "idempotent f \<longleftrightarrow> f = f \<circ> f"
lemma "idempotent OppositeCategory"
  apply (unfold idempotent_def)
  apply (rule ext)
  apply (unfold comp_def)
  apply (rule OpCatOpCat)
  oops

  
end

