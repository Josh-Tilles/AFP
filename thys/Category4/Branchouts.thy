theory Branchouts
imports Category
begin

definition mon2cat :: "'a::monoid_add \<Rightarrow> ('a, 'a) Category" where
  "mon2cat U \<equiv> 
   \<lparr> Obj = 0,
     Mor = U,
     
  "

definition preorder2cat :: "'a::preorder \<Rightarrow> ('a, 'a \<Rightarrow> 'a) Category" where
  "preorder2cat U \<equiv>
   \<lparr> Obj = U,
     "

(* try going from a set-of-ordered-pairs-as-preorder to a category.
like "('a * 'a) set \<Rightarrow> ('a, 'a \<Rightarrow> 'a) Category "
