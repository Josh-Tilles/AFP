(*  ID:         $Id: RegExp.thy,v 1.2 2004-03-31 14:06:03 lsf37 Exp $
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

header "Regular expressions"

theory RegExp = RegSet:

datatype 'a rexp = Empty
                 | Atom 'a
                 | Or   "('a rexp)" "('a rexp)"
                 | Conc "('a rexp)" "('a rexp)"
                 | Star "('a rexp)"

consts lang :: "'a rexp => 'a list set"
primrec
"lang Empty = {}"
"lang (Atom a) = {[a]}"
"lang (Or el er) = (lang el) Un (lang er)"
"lang (Conc el er) = RegSet.conc (lang el) (lang er)"
"lang (Star e) = RegSet.star(lang e)"

end
