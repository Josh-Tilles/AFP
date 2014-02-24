(*  Title:      Sort.thy
    Author:     Danijela Petrovi\'c, Facylty of Mathematics, University of Belgrade *)

header {* Verification of functional Selection Sort *}

theory SelectionSort_Functional
imports RemoveMax
begin

subsection {* Defining data structure *}

text{* Selection sort works with list and that is the reason why {\em
  Collection} should be interpreted as list. *}

interpretation Collection "[]" "\<lambda> l. l = []" id multiset_of
by (unfold_locales, auto)

subsection {* Defining function remove\_max *}

text{* The following is definition of {\em remove\_max} function. 
The idea is very well known -- assume that the maximum element is the
first one and then compare with each element of the list. Function
{\em f} is one step in iteration, it compares current maximum {\em m}
with one element {\em x}, if it is bigger then {\em m} stays current
maximum and {\em x} is added in the resulting list, otherwise {\em x}
is current maximum and {\em m} is added in the resulting
list.
*}

fun f where "f (m, l) x = (if x \<ge> m then (x, m#l) else (m, x#l))"

definition remove_max where
  "remove_max l = foldl f (hd l, []) (tl l)"

lemma max_Max_commute: 
  "finite A \<Longrightarrow> max (Max (insert m A)) x = max m (Max (insert x A))"
  apply (cases "A = {}", simp)  
  by (metis Max_insert min_max.sup_commute min_max.sup_left_commute)

text{* The function really returned the
maximum value. *}

lemma remove_max_max_lemma:
  shows "fst (foldl f (m, t) l) =  Max (set (m # l))"
using assms
proof (induct l arbitrary: m t rule: rev_induct)
  case (snoc x xs)
  let ?a = "foldl f (m, t) xs"
  let ?m' = "fst ?a" and ?t' = "snd ?a"
  have "fst (foldl f (m, t) (xs @ [x])) = max ?m' x"
    by (cases ?a) (auto simp add: max_def)
  thus ?case
    using snoc
    by (simp add: max_Max_commute)
qed simp

lemma remove_max_max:
  assumes "l \<noteq> []" "(m, l') = remove_max l"
  shows "m = Max (set l)"
using assms
unfolding remove_max_def
using remove_max_max_lemma[of "hd l" "[]" "tl l"]
using fst_conv[of m l']
by simp

text{* Nothing new is added in the list and noting is deleted
from the list except the maximum element. *}

lemma remove_max_multiset_of_lemma:
  assumes "(m, l') = foldl f (m', t') l"
  shows "multiset_of (m # l') = multiset_of (m' # t' @ l)"
using assms
proof (induct l arbitrary: l' m m' t' rule: rev_induct)
  case (snoc x xs)
  let ?a = "foldl f (m', t') xs"
  let ?m' = "fst ?a" and ?t' = "snd ?a"
  have "multiset_of (?m' # ?t') = multiset_of (m' # t' @ xs)"
    using snoc(1)[of ?m' ?t' m' t']
    by simp
  thus ?case
    using snoc(2)
    apply (cases "?a")
    apply (auto split: split_if_asm, (simp add: union_lcomm union_commute)+) 
    by (metis union_assoc)
qed simp

lemma remove_max_multiset_of:
  assumes "l \<noteq> []" "(m, l') = remove_max l" 
  shows "multiset_of l' + {#m#} = multiset_of l"
using assms
unfolding remove_max_def
using remove_max_multiset_of_lemma[of m l' "hd l" "[]" "tl l"]
by auto

definition ssf_ssort' where
  [simp, code del]: "ssf_ssort' = RemoveMax.ssort' (\<lambda> l. l = []) remove_max"
definition ssf_ssort where 
  [simp, code del]: "ssf_ssort = RemoveMax.ssort (\<lambda> l. l = []) id remove_max"

interpretation SSRemoveMax: 
  RemoveMax "[]" "\<lambda> l. l = []" id multiset_of remove_max "\<lambda> _. True" 
  where
 "RemoveMax.ssort' (\<lambda> l. l = []) remove_max = ssf_ssort'" and
 "RemoveMax.ssort (\<lambda> l. l = []) id remove_max = ssf_ssort"
using remove_max_max
by (unfold_locales, auto simp add: remove_max_multiset_of)


  
end
