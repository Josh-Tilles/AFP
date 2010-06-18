(*  ID:         $Id: RegExp.thy,v 1.5 2004-08-19 10:54:14 nipkow Exp $
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

header "Regular expressions"

theory Regular_Exp
imports Regular_Set
begin

datatype 'a rexp =
  Zero |
  One |
  Atom 'a |
  Plus "('a rexp)" "('a rexp)" |
  Times "('a rexp)" "('a rexp)" |
  Star "('a rexp)"

primrec lang :: "'a rexp => 'a list set" where
"lang Zero = {}" |
"lang One = {[]}" |
"lang (Atom a) = {[a]}" |
"lang (Plus el er) = (lang el) Un (lang er)" |
"lang (Times el er) = conc (lang el) (lang er)" |
"lang (Star e) = star(lang e)"

primrec atoms :: "'a rexp \<Rightarrow> 'a set"
where
"atoms Zero = {}" |
"atoms One = {}" |
"atoms (Atom a) = {a}" |
"atoms (Plus r s) = atoms r \<union> atoms s" |
"atoms (Times r s) = atoms r \<union> atoms s" |
"atoms (Star r) = atoms r"

end
