theory AltCategory
imports Category
begin

(* Records are defined surprisingly late in the HOL hierarchy of dependencies.
Would it be possible to use more fundamental mechanisms? *)
locale AltCategory =
  fixes Obj :: "'o set"
    and Mor :: "'m set"
    and Dom :: "'m \<Rightarrow> 'o"
    and Cod :: "'m \<Rightarrow> 'o"
    and Id  :: "'o \<Rightarrow> 'm"
    and Comp :: "'m \<Rightarrow> 'm \<Rightarrow> 'm"

(* The three conditions of the `MapsTo` definition seem a little awkward. Are there any
benefits to putting them into a locale? *)
locale AltMapsTo =
  fixes CC :: "('o, 'm, 'a) Category_scheme"
    and f :: 'm
    and X :: 'o
    and Y :: 'o
  assumes "f \<in> Mor CC"
      and "Dom CC f = X"
      and "Cod CC f = Y"

inductive AltAltMapsTo :: "('o, 'm, 'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> bool" where
  "\<lbrakk>f \<in> Mor CC; Dom CC f = X; Cod CC f = Y\<rbrakk> \<Longrightarrow> AltAltMapsTo CC f X Y"
(* Now we don't have to worry about the boilerplate MapsToI & MapsToE, right? *)

inductive AltCompDefined where
  "\<lbrakk>f \<in> Mor CC; g \<in> Mor CC; Cod CC f = Dom CC g\<rbrakk> \<Longrightarrow> AltCompDefined CC f g"
  
lemma (in Category) expand_dom_cod: "f \<in> mor \<Longrightarrow> f maps (dom f) to (cod f)"
  apply (rule MapsToI)
      apply assumption
    apply (rule refl)
  apply (rule refl)
done

lemma (in Category) temporary_name_1: "f \<approx>> g \<Longrightarrow> (f ;; g) maps (dom f) to (cod g)"
  apply (unfold CompDefined_def)
  apply (erule conjE)
  apply (erule conjE)
  apply (unfold MapsTo_def)
  apply (rule conjI)
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


lemma "inj_on (Id C) (Obj C)"
apply (rule inj_onI)
sorry

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

lemmas (in Category) Inverse_relE = inverse_relE
lemmas (in Category) Inverse_relI = inverse_relI

lemma (in Category)
  assumes "cinv f g" and "f maps A to B"
  shows "g maps B to A"
sorry

lemma (in Category)
  assumes "cinv f g"
  shows "dom f = cod g" and "cod f = dom g"
sorry


lemma (in Category) AltInverse_relI:
  assumes "f maps A to B" and "g maps B to A"
  assumes "f ;; g = id A" and "g ;; f = id B"
  shows "cinv f g"
sorry

lemma (in Category) AltInvIsMor:
  assumes "cinv f g"
  shows "f \<in> mor" and "g \<in> mor"
sorry

context Category
begin
  definition "monic f \<longleftrightarrow> (\<forall> g h. g;;f = h;;f \<longrightarrow> g=h)"
  definition "epic f \<longleftrightarrow> (\<forall> g h. f;;g = f;;h \<longrightarrow> g=h)"
  definition "Iso f \<longleftrightarrow> (\<exists> g. f;;g = id (dom f) \<and> g;;f = id (cod f))"
  
(* @TODO the `inductive` question is probably even more applicable here *)

lemma IsoI:
  assumes "f;;g = id (dom f)"
    and "g;;f = id (cod f)"
  shows "Iso f"
unfolding Iso_def
using assms
apply auto
done

lemma IsoI':
  assumes "f maps A to B" and "g maps B to A"
      and "f ;; g = id A" and "g ;; f = id B"
  shows "Iso f"
sorry

lemma [simp]:
  assumes "X \<in> obj"
  shows "dom (id X) = X"
proof -
  from `X \<in> obj` have "id X maps X to X" by (rule Cidm)
  oops

lemma
  assumes "X \<in> obj"
  shows "Iso (id X)"
proof (rule IsoI[where ?g="id X"])
  have "(id X) ;; (id X) = id X" apply (rule Cidr)
oops
end

definition inverse1 :: "('o, 'm, 'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> bool" where
 "inverse1 C f g \<longleftrightarrow> (let A = Dom C f in
                       let B = Cod C f in
                        (Comp C f g) = Id C A \<and> (Comp C g f) = Id C B)"

definition (in Category)
  "invertible f \<longleftrightarrow> (\<exists>g. f;;g = id (dom f) \<and> g;;f = id (cod f))"

locale isoLocaleDef = Category +
  fixes A and B
  fixes f and g
  assumes "f maps A to B" and "g maps B to A"
  assumes "f ;; g = id A" and "g ;; f = id B"


thm Category.invertible_def
thm Category.isoLocaleDef_axioms_def

definition (in Category)
  "retractible f \<longleftrightarrow> True" (* @TODO *)

lemma (in Category)
  assumes "X \<in> obj"
  shows "Iso (id X)"
proof -
  have "dom (id X) = X"
    apply (rule Cidm)
apply (unfold invertible_def)
apply rule
apply rule
proof -
let ?g = "id X"
let ?s = "dom (id X)" and ?t = "dom (id X)"
show "id X ;; ?g = id ?s" apply (auto simp add: MapsTo_def CompDefined_def)
oops
