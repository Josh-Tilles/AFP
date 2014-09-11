(*
   Title: Theory  Secrecy_types.thy
   Author:    Maria Spichkova <maria.spichkova at rmit.edu.au>, 2014
*)

header {* Auxiliary data types *}

theory Secrecy_types
imports Main
begin

-- "We assume disjoint sets: Data of data values,"
-- "Secrets of unguessable values, Keys - set of cryptographic  keys."  
-- "Based on these sets, we specify the sets EncType of encryptors that may be"
-- "used for encryption or decryption, and Expression of expression items."
-- "The specification (component) identifiers should be listed in the set specID,"
-- "the channel indentifiers should be listed in the set chanID." 

datatype_new Keys = CKey | CKeyP | SKey | SKeyP | genKey 
datatype_new Secrets = secretD | N | NA
type_synonym Var  = "nat"
type_synonym Data = "nat"
datatype_new KS          = kKS Keys | sKS Secrets
datatype_new EncType  = kEnc Keys | vEnc Var
datatype_new specID = sComp1 | sComp2 | sComp3 | sComp4
datatype_new Expression = kE Keys | sE Secrets | dE Data | idE specID 
datatype_new chanID = ch1 | ch2   | ch3  | ch4

primrec Expression2KSL:: "Expression list \<Rightarrow> KS list" 
where
   "Expression2KSL [] = []" |
   "Expression2KSL (x#xs) = 
     ((case x of (kE m) \<Rightarrow> [kKS m] 
                  | (sE m) \<Rightarrow> [sKS m] 
                  | (dE m) \<Rightarrow> [] 
                  | (idE m) \<Rightarrow> []) @ Expression2KSL xs) "

primrec KS2Expression:: "KS \<Rightarrow> Expression" 
where
  "KS2Expression (kKS m) = (kE m)"  |
  "KS2Expression (sKS m) = (sE m)"

end