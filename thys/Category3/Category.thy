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

definition
  MapsTo :: "('o, 'm, 'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> bool" ("_ maps\<index> _ to _" [60, 60, 60] 65) where
  "MapsTo CC f X Y \<equiv> f \<in> Mor CC \<and> Dom CC f = X \<and> Cod CC f = Y"

definition
  CompDefined :: "('o, 'm, 'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> bool" (infixl "\<approx>>\<index>" 65) where
  "CompDefined CC f g \<equiv> f \<in> Mor CC \<and> g \<in> Mor CC \<and> Cod CC f = Dom CC g"

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
      Obj = Obj C , 
      Mor = Mor C , 
      Dom = restrict (Dom C) (Mor C) , 
      Cod = restrict (Cod C) (Mor C) , 
      Id  = restrict (Id C) (Obj C) , 
      Comp = \<lambda> f g . (restrict (split (Comp C)) {(f,g) | f g . f \<approx>>\<^bsub>C\<^esub> g})(f, g), 
      \<dots> = Category.more C
  \<rparr>"

lemma MakeCatMapsTo:
  assumes "f maps\<^bsub>C\<^esub> X to Y"
  shows "f maps\<^bsub>MakeCat C\<^esub> X to Y"
sorry

lemma MakeCatComp:
  assumes "f \<approx>>\<^bsub>C\<^esub> g"
  shows "f ;;\<^bsub>MakeCat C\<^esub> g = f ;;\<^bsub>C\<^esub> g"
sorry

lemma MakeCatId:
  assumes "X \<in> obj\<^bsub>C\<^esub>"
  shows "id\<^bsub>C\<^esub> X = id\<^bsub>MakeCat C\<^esub> X"
sorry

lemma MakeCatObj: "obj\<^bsub>MakeCat C\<^esub> = obj\<^bsub>C\<^esub>"
sorry

lemma MakeCatMor: "mor\<^bsub>MakeCat C\<^esub> = mor\<^bsub>C\<^esub>"
sorry

lemma MakeCatDom:
  assumes "f \<in> mor\<^bsub>C\<^esub>"
  shows "dom\<^bsub>C\<^esub> f = dom\<^bsub>MakeCat C\<^esub> f"
sorry

lemma MakeCatCod:
  assumes "f \<in> mor\<^bsub>C\<^esub>"
  shows "cod\<^bsub>C\<^esub> f = cod\<^bsub>MakeCat C\<^esub> f"
sorry


lemma MakeCatCompDef: "f \<approx>>\<^bsub>MakeCat C\<^esub> g \<longleftrightarrow> f \<approx>>\<^bsub>C\<^esub> g"
sorry

lemma MakeCatComp2:
  assumes "f \<approx>>\<^bsub>MakeCat C\<^esub> g"
  shows "f ;;\<^bsub>MakeCat C\<^esub> g = f ;;\<^bsub>C\<^esub> g"
sorry


lemma ExtCategoryMakeCat: "ExtCategory (MakeCat C)"
sorry

lemma MakeCat:
  assumes "Category_axioms C"
  shows "Category (MakeCat C)"
sorry


lemma MapsToE (*[elim]*):
  assumes "f maps\<^bsub>C\<^esub> X to Y"
    and "\<lbrakk>f \<in> mor\<^bsub>C\<^esub>; dom\<^bsub>C\<^esub> f = X; cod\<^bsub>C\<^esub> f = Y\<rbrakk> \<Longrightarrow> R"
  shows "R"
sorry

lemma MapsToI (*[intro]*):
  assumes "f \<in> mor\<^bsub>C\<^esub>"
    and "dom\<^bsub>C\<^esub> f = X"
    and "cod\<^bsub>C\<^esub> f = Y"
  shows "f maps\<^bsub>C\<^esub> X to Y"
sorry

lemma CompDefinedE (*[elim]*):
  assumes "f \<approx>>\<^bsub>C\<^esub> g"
      and "\<lbrakk>f \<in> mor\<^bsub>C\<^esub> ; g \<in> mor\<^bsub>C\<^esub> ; cod\<^bsub>C\<^esub> f = dom\<^bsub>C\<^esub> g\<rbrakk> \<Longrightarrow> R"
  shows "R"
sorry

lemma CompDefinedI (*[intro]*):
  assumes "f \<in> mor\<^bsub>C\<^esub>"
    and "g \<in> mor\<^bsub>C\<^esub>"
    and "cod\<^bsub>C\<^esub> f = dom\<^bsub>C\<^esub> g"
  shows "f \<approx>>\<^bsub>C\<^esub> g"
sorry

lemma (in Category) MapsToCompI:
  assumes "f \<approx>> g"
  shows "(f ;; g) maps (dom f) to (cod g)"
sorry


lemma MapsToCompDef:
  assumes "f maps\<^bsub>C\<^esub> X to Y" and "g maps\<^bsub>C\<^esub> Y to Z"
  shows "f \<approx>>\<^bsub>C\<^esub> g"
sorry


lemma (in Category) MapsToMorDomCod: 
  assumes "f \<approx>> g" 
  shows "f;;g \<in> mor" and "dom (f;;g) = dom f" and "cod (f;;g) = cod g"
sorry


lemma (in Category) MapsToObj: 
  assumes "f maps X to Y"
  shows "X \<in> obj" and "Y \<in> obj"
sorry


lemma (in Category) IdInj: 
  assumes "X \<in> obj" and "Y \<in> obj" and "id X = id Y"
  shows   "X = Y"
sorry


lemma (in Category) CompDefComp:
  assumes "f \<approx>> g" and "g \<approx>> h"
  shows "f \<approx>> (g ;; h)" and "(f ;; g) \<approx>> h"
sorry


lemma (in Category) CatIdInMor:
  assumes "X \<in> obj"
  shows "id X \<in> mor"
sorry

lemma (in Category) MapsToId:
  assumes "X \<in> obj"
  shows "id X \<approx>> id X"
sorry


lemmas (in Category) Simps = Cdom Ccod Cidm Cidl Cidr MapsToCompI IdInj MapsToId

lemma (in Category) LeftRightInvUniq: 
  assumes 0: "h \<approx>> f" and  z: "f \<approx>> g"
  assumes 1: "f ;; g = id (dom f)" 
  and     2: "h ;; f = id (cod f)"
  shows   "h = g"
sorry


lemma (in Category) CatIdDomCod:
  assumes "X \<in> obj"
  shows "dom (id X) = X" and "cod (id X) = X"
sorry


lemma (in Category) CatIdCompId:
  assumes "X \<in> obj"
  shows   "id X ;; id X = id X"
sorry


(*lemmas (in Category) simps2 = simps CatIdCompId Cassoc CatIdDomCod*)

lemma (in Category) CatIdUniqR: 
  assumes iota: "\<iota> maps X to X"
  and     rid:  "\<forall> f . f \<approx>> \<iota> \<longrightarrow> f ;; \<iota> = f"
  shows "id X = \<iota>"
sorry

  
definition
  inverse_rel :: "('o, 'm, 'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> bool" ("cinv\<index> _ _" 60) where
  "inverse_rel C f g \<equiv> (f \<approx>>\<^bsub>C\<^esub> g) \<and> (f ;;\<^bsub>C\<^esub> g) = (id\<^bsub>C\<^esub> (dom\<^bsub>C\<^esub> f)) \<and> (g ;;\<^bsub>C\<^esub> f) = (id\<^bsub>C\<^esub> (cod\<^bsub>C\<^esub> f))"

definition 
  isomorphism :: "('o, 'm, 'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> bool" ("ciso\<index> _" [70]) where
  "isomorphism C f \<equiv> \<exists> g . inverse_rel C f g"

lemma (in Category) Inverse_relI:
  assumes "f \<approx>> g"
      and "f ;; g = id (dom f)"
      and "g ;; f = id (cod f)"
  shows "cinv f g"
sorry

lemma (in Category) Inverse_relE (*[elim]*):
  assumes "cinv f g"
      and "\<lbrakk>f \<approx>> g; f ;; g = id (dom f); g ;; f = id (cod f)\<rbrakk> \<Longrightarrow> P"
  shows "P"
sorry

lemma (in Category) Inverse_relSym: 
  assumes "cinv f g"
  shows   "cinv g f"
sorry


lemma (in Category) InverseUnique: 
  assumes 1: "cinv f g"
  and     2: "cinv f h"
  shows   "g = h"
sorry


lemma (in Category) InvId:
  assumes "X \<in> obj"
  shows "cinv (id X) (id X)"
sorry

    
definition
  inverse :: "('o, 'm, 'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> 'm" ("Cinv\<index> _" [70]) where
  "inverse C f \<equiv> THE g . inverse_rel C f g"

lemma (in Category) inv2Inv:
  assumes "cinv f g"
  shows   "ciso f" and "Cinv f = g"
sorry


lemma (in Category) iso2Inv:
  assumes "ciso f"
  shows   "cinv f (Cinv f)"
sorry


lemma (in Category) InvInv:
  assumes "ciso f" 
  shows   "ciso (Cinv f)" and "(Cinv (Cinv f)) = f"
sorry


lemma (in Category) InvIsMor:
  assumes "cinv f g"
  shows "f \<in> mor \<and> g \<in> mor"
sorry

lemma (in Category) IsoIsMor:
  assumes "ciso f"
  shows "f \<in> mor"
sorry

lemma (in Category) InvDomCod:
  assumes "ciso f"
  shows "dom (Cinv f) = cod f" and "cod (Cinv f) = dom f" and "Cinv f \<in> mor"
sorry


lemma (in Category) IsoCompInv:
  assumes "ciso f"
  shows "f \<approx>> Cinv f"
sorry

lemma (in Category) InvCompIso:
  assumes "ciso f"
  shows "Cinv f \<approx>> f"
sorry

lemma (in Category) IsoInvId1:
  assumes "ciso f"
  shows "(Cinv f) ;; f = (id (cod f))"
sorry

lemma (in Category) IsoInvId2:
  assumes "ciso f"
  shows "f ;; (Cinv f) = (id (dom f))"
sorry

lemma (in Category) IsoCompDef:
  assumes 1: "f \<approx>> g" and 2: "ciso f" and 3: "ciso g"
  shows "(Cinv g) \<approx>> (Cinv f)"
sorry


lemma (in Category) IsoCompose: 
  assumes 1: "f \<approx>> g" and 2: "ciso f" and 3: "ciso g"
  shows "ciso (f ;; g)" and "Cinv (f ;; g) = (Cinv g) ;; (Cinv f)"
sorry


definition "ObjIso C A B \<equiv> \<exists> k . (k maps\<^bsub>C\<^esub> A to B) \<and> ciso\<^bsub>C \<^esub>k"

definition 
  UnitCategory :: "(unit, unit) Category" where
  "UnitCategory = MakeCat \<lparr>
      Obj = { () } ,
      Mor = { () } ,
      Dom = (\<lambda>f. () ) ,
      Cod = (\<lambda>f. () ) ,
      Id = (\<lambda>f. () ) ,
      Comp = (\<lambda>f g. () )
  \<rparr>"

lemma (*[simp]:*) "Category UnitCategory"
sorry


definition 
  OppositeCategory :: "('o, 'm, 'a) Category_scheme \<Rightarrow> ('o, 'm, 'a) Category_scheme" ("Op _" [65] 65) where
  "OppositeCategory C \<equiv> \<lparr>
      Obj = Obj C , 
      Mor = Mor C , 
      Dom = Cod C , 
      Cod = Dom C , 
      Id  = Id C , 
      Comp = (\<lambda>f g. g ;;\<^bsub>C\<^esub> f), 
      \<dots> = Category.more C
  \<rparr>"

lemma OpCatOpCat: "Op (Op C) = C"
sorry


lemma OpCatCatAx:
  assumes "Category_axioms C"
  shows "Category_axioms (Op C)"
sorry

lemma OpCatCatExt:
  assumes "ExtCategory C"
  shows "ExtCategory (Op C)"
sorry

lemma OpCatCat:
  assumes "Category C"
  shows "Category (Op C)"
sorry


lemma MapsToOp:
  assumes "f maps\<^bsub>C\<^esub> X to Y"
  shows "f maps\<^bsub>Op C\<^esub> Y to X"
sorry

lemma MapsToOpOp:
  assumes "f maps\<^bsub>Op C\<^esub>X to Y"
  shows "f maps\<^bsub>C\<^esub> Y to X"
sorry

lemma CompDefOp:
  assumes "f \<approx>>\<^bsub>C\<^esub> g"
  shows "g \<approx>>\<^bsub>Op C\<^esub> f"
sorry

end
