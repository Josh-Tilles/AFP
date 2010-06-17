(*  ID:          $Id: DPC0Expressions.thy,v 1.3 2008-03-07 15:23:43 lsf37 Exp $
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

header {* SHORTENED! Parallel expressions in DPC/Hoare. *}

theory DPC0Expressions imports Main begin

definition p_not :: "bool list => bool list"
  where "p_not = map Not"

notation (xsymbols)
  p_not   ("\<not>\<^sub>p")

definition elem_wise :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list"
  where "elem_wise f xs ys = map (\<lambda> (x, y). f x y) (zip xs ys)"

definition
  p_and  :: "bool list => bool list => bool list"  (infixl "pand"  35)
  where "p_and = elem_wise op&"

notation (xsymbols)
  p_and  (infixl "\<and>\<^sub>p"  35)

end
