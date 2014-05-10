theory CM
imports Category
begin

locale Cone1 = Category +
  fixes exL assumes left_morphism: "exL \<in> mor"
  fixes exR assumes right_morphism: "exR \<in> mor"
  assumes sharedSource: "dom exL = dom exR"

abbreviation (in Cone1) "objL \<equiv> cod exL"
abbreviation (in Cone1) "objR \<equiv> cod exR"
abbreviation (in Cone1) "sourceObj \<equiv> dom exL" (* arbitrarily chose exL over exR *)

(* 
locale Product = Cone1 +
  (* "UMP" stands for "Universal Mapping Property" *)
  assumes UMP: "\<forall> f g. (Cone f g \<and> (cod f = cod exL) \<and> (cod g = cod exR)) \<longrightarrow> \<exists> h. h maps "
*)

locale Cone2 = Category +
  fixes sourceObj assumes "sourceObj \<in> obj"
  fixes exL assumes "exL \<in> mor" and "dom exL = sourceObj"
  fixes exR assumes "exR \<in> mor" and "dom exR = sourceObj"

abbreviation (in Cone2) "objL \<equiv> cod exL"
abbreviation (in Cone2) "objR \<equiv> cod exR"

locale Product = Cone2 +
  (* "UMP" stands for "Universal Mapping Property" *)
  assumes UMP: "\<forall> X f g. (Cone2 C X f g \<and> (cod f = cod exL) \<and> (cod g = cod exR)) \<longrightarrow> (\<exists>! h. h maps X to sourceObj \<and> h;;exL = f \<and> h;;exR = g)"

definition (in Category) Ctimes where
  "Ctimes A B \<equiv> \<some> X. \<exists> \<pi>\<^sub>A \<pi>\<^sub>B. (cod \<pi>\<^sub>A = A \<and> cod \<pi>\<^sub>B = B \<and> Product C X \<pi>\<^sub>A \<pi>\<^sub>B)"

locale Has_Products = Category +
  assumes "\<forall> A B. (A \<in> obj \<and> B \<in> obj) \<longrightarrow> (\<exists> X ex1 ex2. ex1 maps X to A \<and> ex2 maps X to B \<and> Product C X ex1 ex2)"
  assumes HasEm: "\<And> A B. \<lbrakk>A\<in>obj; B\<in>obj\<rbrakk> \<Longrightarrow> (\<exists> X ex1 ex2. ex1 maps X to A \<and> ex2 maps X to B \<and> Product C X ex1 ex2)"

locale Cocone2 = Category +
  fixes targetObj assumes "targetObj \<in> obj"
  fixes inL assumes "inL \<in> mor" and "cod inL = targetObj"
  fixes inR assumes "inR \<in> mor" and "cod inR = targetObj"

abbreviation (in Cocone2) "objL \<equiv> dom inL"
abbreviation (in Cocone2) "objR \<equiv> dom inR"

locale Coproduct = Cocone2 +
  assumes UMP: "\<forall> X f g. (Cocone2 C X f g \<and> (dom f = dom inL) \<and> (dom g = dom inR)) \<longrightarrow> (\<exists>! h. h maps targetObj to X \<and> inL;;h = f \<and> inR;;h = g)"

definition (in Category) Cplus where
  "Cplus A B \<equiv> \<some> X. \<exists> j1 j2. (dom j1 = A \<and> dom j2 = B \<and> Coproduct C X j1 j2)"

locale Has_Coproducts = Category +
  assumes "\<forall> A B. (A \<in> obj \<and> B \<in> obj) \<longrightarrow> (\<exists> X j1 j2. j1 maps A to X \<and> j2 maps B to X \<and> Coproduct C X j1 j2)"

locale Has_Both = Has_Products + Has_Coproducts

lemma (in Has_Both)
  assumes "X \<in> obj" and "B1 \<in> obj" and "B2 \<in> obj"
  shows "\<exists> f. f maps (Cplus (Ctimes X B1) (Ctimes X B2)) to (Ctimes X (Cplus B1 B2))"
(* In order to show ?thesis, find two maps: one from `(Cplus (Ctimes X B1) (Ctimes X B2))` to `X` and one to `(Cplus B1 B2)` *)
oops

lemma (in Has_Products) CproductConstructor:
  assumes "f1 maps X to A" and "f2 maps X to B"
  obtains f where "f maps X to (Ctimes A B)"
proof -
  obtain AB and pr1 and pr2 where "pr1 maps AB to A" and "pr2 maps AB to B" and "Product C AB pr1 pr2"
    apply (unfold MapsTo_def)
    apply (unfold Product_def)
    apply (unfold Product_axioms_def)
    apply (unfold Cone2_def)
    apply (unfold Cone2_axioms_def)
    apply (unfold Category_def Category_axioms_def ExtCategory_def extensional_def CompDefined_def)
apply auto

  thm HasEm
apply (unfold Ctimes_def)
 
