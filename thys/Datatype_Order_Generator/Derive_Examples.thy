(*  Title:       Deriving class instances for datatypes
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2013 René Thiemann

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

header Examples

theory Derive_Examples
imports 
  Derive
  Rat
begin

subsection "Register standard existing types"

derive linorder list
derive linorder sum
derive linorder prod

text {* For registering container-classes, we are not restricted to datatypes. *}

derive ceq rat
derive (no) cenum rat
derive (collect) set_impl rat

subsection "Support of function types in combination with containers"

text {* \texttt{derive (no) ceq fun} does not work, since fun is already registered.
Therefore, we use an isomorphic copy. *}

typedef ('a,'b)FUN = "UNIV :: ('a \<Rightarrow> 'b)set" by auto
derive (no) ceq FUN
derive (no) cenum FUN
derive (no) corder FUN
derive (collect) set_impl FUN

subsection "Without nested recursion"

datatype 'a bintree = BEmpty | BNode "'a bintree" 'a "'a bintree"
derive linorder bintree
derive hashable bintree
derive countable bintree
derive (no) cenum bintree
derive ceq bintree
derive corder bintree
derive (dlist) set_impl bintree (* one can also pick other choices than dlist like rbt, collect, ... *)

subsection "Using other datatypes"

datatype nat_list_list = NNil | CCons "nat list" nat_list_list
derive linorder nat_list_list
derive hashable nat_list_list
derive countable nat_list_list
derive (no) cenum nat_list_list
derive ceq nat_list_list
derive corder nat_list_list
derive (rbt) set_impl nat_list_list

subsection "Explicit mutual recursion"

datatype 'a mtree = MEmpty | MNode 'a "'a mtree_list"
  and 'a mtree_list = MNil | MCons "'a mtree" "'a mtree_list"
derive linorder mtree
derive hashable mtree
derive countable mtree
derive (no) cenum mtree
derive ceq mtree
derive corder mtree
derive (choose) set_impl mtree

subsection "Implicit mutual recursion"

datatype 'a tree = Empty | Node 'a "'a tree list"
derive linorder tree
derive hashable tree
derive countable tree
derive (no) cenum tree
derive ceq tree
derive corder tree 
derive (collect) set_impl tree


datatype 'a ttree = TEmpty | TNode 'a "'a ttree list tree"
derive linorder ttree
derive hashable ttree
derive countable ttree
derive (no) cenum ttree
derive ceq ttree
derive corder ttree
derive (monad) set_impl ttree

subsection "Examples from IsaFoR"

datatype ('f,'v)"term" = Var 'v | Fun 'f "('f,'v)term list"
datatype ('f, 'l) lab =
  Lab "('f, 'l) lab" 'l
| FunLab "('f, 'l) lab" "('f, 'l) lab list"
| UnLab 'f
| Sharp "('f, 'l) lab"

derive linorder "term"
derive linorder lab
derive countable "term"
derive countable lab
derive hashable "term"
derive hashable lab
derive (no) cenum "term"
derive ceq "term"
derive corder "term"
derive (rbt) set_impl "term"
derive (no) cenum lab
derive ceq lab
derive corder lab
derive (dlist) set_impl lab

subsection "A complex datatype"
text {*
The following datatype has nested indirect recursion, mutual recursion and
uses other datatypes.
*}

datatype ('a,'b)complex = 
  C1 nat "'a ttree" 
| C2 "('a,'b)complex list tree tree" 'b "('a,'b)complex" "('a,'b)complex2 ttree list"
and ('a,'b)complex2 = D1 "('a,'b)complex ttree"

derive linorder complex
derive hashable complex
derive countable complex
derive (no) cenum complex
derive ceq complex
derive corder complex
derive (dlist) set_impl complex

end
