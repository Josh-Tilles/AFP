(* modeled after Greg O'Keefe's Category stuff *)
theory Cat
imports Category
begin

(* @TODO establish Isabelle-level morphisms between the two styles of CT definitions? *)

definition hom :: "[('o, 'm, 'a) Category_scheme, 'o, 'o] \<Rightarrow> 'm set"
  ("Hom\<index> _ _" [81, 81] 80) where
"hom CC A B \<equiv> {f. f \<in> Mor CC \<and> Dom CC f = A \<and> Cod CC f = B}"

(* originally a local axiom of `category` *)
lemma (in Category) category___id_hom:
  "A \<in> obj \<Longrightarrow> id A \<in> Hom A A"
oops

(* @TODO see also `comp_types` and `comp_associative` *)
(* comp_types maps to Ccompt and comp_associative maps to Cassoc *)

(* compI maps to `MapsToDom` and `MapsToCod` *)

(* And I don't think `Hom` is necessary (at least not yet) because of the `MapsTo` definition *)
(* and a few of the lemmas are simplified as a result of the CompDefined definition *)

(* SetCat.thy *)
section "Set is a Category"

record ('a, 'b) set_arrow =
  set_dom :: "'a set"
  set_func :: "('a \<Rightarrow> 'b) + ('a \<times> 'b)"
  set_cod :: "'b set"

definition acceptable_as_function :: "('a \<times> 'b) set \<Rightarrow> bool" where
  "acceptable_as_function r \<equiv> True"

definition acceptable_as_function2 :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "acceptable_as_function2 r s \<equiv> True"

definition acceptable_as_function3 :: "('a \<times> 'b) set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "acceptable_as_function3 r s \<equiv> True"

definition acceptable_as_function4 :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "acceptable_as_function4 r sDom sCod \<equiv> (keys r) = sDom \<and> (vals r) \<subseteq> sCod \<and> single_valued r"

(*
definition set_arrow :: "'c set \<Rightarrow> 'c set_arrow \<Rightarrow> bool" where
"set_arrow U f   \<longleftrightarrow>   set_dom f \<subseteq> U  \<and>  set_cod f \<subseteq> U  \<and>  set_func f \<in> (set_dom f) \<rightarrow> (set_cod f)  \<and>  set_func f \<in> (extensional (set_dom f))"
*)
(* the explicit "universe" parameter isn't a limitation: we could always just pass in (or infer??) UNIV *)

(* using "morphism" instead of "arrow" because the record declaration already provides a `set_arrow.cases` fact, which conflicts with what `inductive` wants to do. *)
inductive set_morphism :: "'c set \<Rightarrow> ('c, 'c) set_arrow \<Rightarrow> bool" where
  "\<lbrakk>set_dom f \<subseteq> U;  set_cod f \<subseteq> U;
    Inl(set_func f) \<in> (set_dom f) \<rightarrow> (set_cod f);
    Inl(set_func f) \<in> (extensional (set_dom f));
    Inr(set_func f) \<rbrakk>
   \<Longrightarrow> set_morphism U f"

definition set_id :: "'c set \<Rightarrow> 'c set \<Rightarrow> ('c, 'c) set_arrow" where
  "set_id U \<equiv> (\<lambda>s \<in> Pow U. \<lparr>set_dom = s, set_func = \<lambda>x\<in>s. x, set_cod = s\<rparr>)"

definition
  set_comp :: "[('c, 'c) set_arrow, ('c, 'c) set_arrow] \<Rightarrow> ('c, 'c) set_arrow"
(infix "\<odot>" 70)
  where
  "set_comp g f \<equiv>
   \<lparr>
    set_dom = set_dom f,
    set_func = compose (set_dom f) (set_func g) (set_func f),
    set_cod = set_cod g
   \<rparr>"

definition set_cat :: "'c set \<Rightarrow> ('c set, ('c, 'c) set_arrow) Category" where
  "set_cat U \<equiv>
   \<lparr>
    Obj = Pow U,
    Mor = {f. set_morphism U f},
    Dom = set_dom,
    Cod = set_cod,
    Id = set_id U,
    Comp = set_comp
   \<rparr>"

subsection "Simple Rules and Lemmas"

lemma set_id_left:
  assumes "f \<in> Mor (set_cat U)"
  shows "set_id U (set_cod f) \<odot> f = f"
sorry

lemma set_id_right:
  assumes "f \<in> Mor (set_cat U)"
  shows "f \<odot> (set_id U (set_dom f)) = f"
sorry

lemma set_id_hom:
  assumes "A \<in> Obj (set_cat U)"
  shows "Id (set_cat U) A maps\<^bsub>set_cat U\<^esub> A to A"
sorry

locale setcat_tmp =
  fixes U :: "'a set"
  (* U_as_cat := set_cat U (structure) *)
begin
  definition "UU \<equiv> set_cat U"
end

lemma set_comp_types (* @TODO *)
  oops

lemma set_comp_associative (* @TODO *)
  oops

theorem set_cat_cat: "Category (set_cat U)"
oops

theorem "Category (MakeCat (set_cat U))"
proof -
  have "Category_axioms (set_cat U)" sorry
  thus ?thesis by (auto simp add: MakeCat set_cat_def)
qed




record 'c swe_arrow =
  swe_dom :: "('c set \<times> 'c set_arrow)"
  swe_func :: "'c \<Rightarrow> 'c"
  swe_cod :: "('c set \<times> 'c set_arrow)"

definition swe_id :: "'c set \<Rightarrow> ('c set \<times> 'c set_arrow) \<Rightarrow> 'c swe_arrow" where
  "swe_id U s \<equiv> (if (fst s) \<in> Pow U then \<lparr>swe_dom = s, swe_func = \<lambda>x. (if x \<in> (fst s) then x else undefined), swe_cod = s\<rparr> else undefined)"

inductive swe_morphism :: "'c set \<Rightarrow> 'c swe_arrow \<Rightarrow> bool" where
  "\<lbrakk> fst (swe_dom f) \<subseteq> U; fst (swe_cod f) \<subseteq> U;
    swe_func f \<in> (fst (swe_dom f)) \<rightarrow> (fst (swe_cod f));
    swe_func f \<in> (extensional (fst (swe_dom f)));
    (swe_func f) \<circ> (set_func (snd (swe_dom f))) = (set_func (snd (swe_cod f))) \<circ> (swe_func f)\<rbrakk>
   \<Longrightarrow> swe_morphism U f"

definition
  swe_comp :: "['c swe_arrow, 'c swe_arrow] \<Rightarrow> 'c swe_arrow"
(infix "\<odot>" 70)
  where
  "swe_comp g f \<equiv>
   \<lparr>
    swe_dom = swe_dom f,
    swe_func = compose (fst (swe_dom f)) (swe_func g) (swe_func f),
    swe_cod = swe_cod g
   \<rparr>"

definition SWE' :: "'c set \<Rightarrow> ( ('c set \<times> 'c set_arrow), 'c swe_arrow) Category" where
  "SWE' U \<equiv>
   \<lparr>
    Obj = {(x, g). x \<in> Pow U \<and> set_morphism U g},
    Mor = {f. swe_morphism U f},
    Dom = swe_dom,
    Cod = swe_cod,
    Id = swe_id U,
    Comp = swe_comp
   \<rparr>"

locale SetCat' = (* Category + *)
  fixes universe :: "'c set"
    and UU :: "('c set, 'c set_arrow) Category" (structure)
  defines "UU \<equiv> set_cat universe"
  (* defines UU \<equiv> MakeCat (set_cat universe) *)

record 'c Set_With_Endomorphism = 
  Carrier :: "'c set" ("carrier\<index>" 70)
  Action :: "'c set_arrow" ("action\<index>" 70)

(* alternatively, could just add an assumption to a set_morphism that the dom = cod, right? *)

record 'c SWE_arrow =
  SWE_dom :: "'c Set_With_Endomorphism"
  SWE_func :: "'c \<Rightarrow> 'c"
  SWE_cod :: "'c Set_With_Endomorphism"

definition SWE_id :: "'c set \<Rightarrow> 'c Set_With_Endomorphism \<Rightarrow> 'c SWE_arrow" where
  "SWE_id U s \<equiv> if (Carrier s) \<in> Pow U then \<lparr>SWE_dom = s, SWE_func = \<lambda>x. if x \<in> (Carrier s) then x else undefined, SWE_cod = s\<rparr> else undefined"

definition
  SWE_comp :: "['c SWE_arrow, 'c SWE_arrow] \<Rightarrow> 'c SWE_arrow"
(infix "\<odot>" 70)
  where
  "SWE_comp g f \<equiv>
   \<lparr>
    SWE_dom = SWE_dom f,
    SWE_func = compose (Carrier (SWE_dom f)) (SWE_func g) (SWE_func f),
    SWE_cod = SWE_cod g
   \<rparr>"

definition SWE :: "'c set \<Rightarrow> ('c Set_With_Endomorphism, 'c SWE_arrow) Category" where
  "SWE U \<equiv>
   \<lparr>
    Obj = {x :: 'c Set_With_Endomorphism. Carrier x \<subseteq> U \<and> set_morphism (Action x) },
    Mor = {f. SWE_morphism U f},
    Dom = SWE_dom,
    Cod = SWE_cod,
    Id = SWE_id U,
    Comp = SWE_comp
   \<rparr>"
   
   
   
   
record ('d, 'a) Graph =
  Dots :: "'d set" ("dots\<index>")
  Arrows :: "'a set" ("arrows\<index>")
  Source :: "'a \<Rightarrow> 'd" ("source\<index> _" 1)
  Target :: "'a \<Rightarrow> 'd" ("target\<index> _" 1)

record ('d1, 'd2, 'a1, 'a2) GraphMap =
  DomainGraph :: "('d1, 'a1) Graph"
  CodomainGraph :: "('d2, 'a2) Graph"
  DotsMap :: "'d1 \<Rightarrow> 'd2"
  ArrowsMap :: "'a1 \<Rightarrow> 'a2"

record ('d, 'a) GraphMap2 =
  DomainGraph2 :: "('d, 'a) Graph"
  CodomainGraph2 :: "('d, 'a) Graph"
  DotsMap2 :: "'d set_arrow" (* SetMorphism *)
  ArrowsMap2 :: "'a set_arrow" (* SetMorphism *)

record 'c Graph3 =
  Dots3 :: "'c set"
  Arrows3 :: "'c set"
  Source3 :: "'c \<Rightarrow> 'c"
  Target3 :: "'c \<Rightarrow> 'c"

record 'c GraphMap3 =
  DomainGraph3 :: "'c Graph3"
  CodomainGraph3 :: "'c Graph3"
  DotsMap3 :: "'c set_arrow"
  ArrowsMap3 :: "'c set_arrow"

definition GraphMap :: "'d set \<Rightarrow> 'a set \<Rightarrow> ('d, 'a) GraphMap2 \<Rightarrow> bool" where
  "GraphMap D A f \<longleftrightarrow>
  (set_dom (DotsMap2 f)) \<subseteq> D
  \<and> (set_cod (DotsMap2 f)) \<subseteq> D
  \<and> (set_dom (ArrowsMap2 f)) \<subseteq> A
  \<and> (set_cod (ArrowsMap2 f)) \<subseteq> A
  \<and> (set_func (DotsMap2 f)) \<in> (Dots (DomainGraph2 f)) \<rightarrow> (Dots (CodomainGraph2 f))
  \<and> (set_func (ArrowsMap2 f)) \<in> (Arrows (DomainGraph2 f)) \<rightarrow> (Arrows (CodomainGraph2 f))
  \<and> (set_func (DotsMap2 f)) \<in> (extensional (Dots (DomainGraph2 f)))
  \<and> (set_func (ArrowsMap2 f)) \<in> (extensional (Arrows (DomainGraph2 f)))

  \<and> (set_func (DotsMap2 f)) \<circ> (Source (DomainGraph2 f)) = (Source (CodomainGraph2 f)) \<circ> (set_func (ArrowsMap2 f))
  \<and> (set_func (DotsMap2 f)) \<circ> (Target (DomainGraph2 f)) = (Target (CodomainGraph2 f)) \<circ> (set_func (ArrowsMap2 f))"

inductive set_morphism :: "'c set \<Rightarrow> 'c set_arrow \<Rightarrow> bool" where
  "\<lbrakk>set_dom f \<subseteq> U;  set_cod f \<subseteq> U;
    set_func f \<in> (set_dom f) \<rightarrow> (set_cod f);
    set_func f \<in> (extensional (set_dom f))\<rbrakk>
   \<Longrightarrow> set_morphism U f"

locale SWE = SetCat +
  assumes "\<lbrakk> \<rbrakk> \<Longrightarrow> F maps A_n_g to B_n_h"
  
locale SWE_Category = LSCategory +
  assumes "(f maps X to Y) \<Longrightarrow> (Action X) |o| f = f |o| (Action Y)"
term SWE_Category_axioms

