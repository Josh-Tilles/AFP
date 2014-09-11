(*<*)
(*
   Title:  Theory ArithExtras.thy (FOCUS streams)
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*)
(*>*)

header "Theory ArithExtras.thy"

theory ArithExtras 
imports Main 
begin 

datatype_new natInf = Fin nat 
                | Infty                     ("\<infinity>")
primrec
nat2inat :: "nat list \<Rightarrow> natInf list"
where
  "nat2inat [] = []" |
  "nat2inat (x#xs) = (Fin x) # (nat2inat xs)"

end