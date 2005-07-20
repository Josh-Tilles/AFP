(* Title: UnivSpec.thy
   Author: Nicole Rauch
*)

header {* The Universal Specification *}

theory UnivSpec = JML :

text {* This theory contains the Isabelle formalization of the
program-dependent specification. This theory has to be provided by the user.
In later versions of Jive, one may be able to generate it from JML model
classes.
*}

constdefs
aCounter :: "Value \<Rightarrow> Store \<Rightarrow> JavaInt"

"aCounter x s == if x ~= nullV & (alive x s) & typeof x = CClassT CounterImpl then
  aI ( s@@(x..CounterImpl'value) )
 else arbitrary"

end
