(* Title:     HOL/MiniML/Maybe.thy
   ID:        $Id: Maybe.thy,v 1.5 2004-08-16 16:35:18 nipkow Exp $
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen
*)

header "Universal error monad"

theory Maybe
import Main
begin

constdefs
  option_bind :: "['a option, 'a => 'b option] => 'b option"
  "option_bind m f == case m of None => None | Some r => f r"

syntax "@option_bind" :: "[pttrns,'a option,'b] => 'c" ("(_ := _;//_)" 0)
translations "P := E; F" == "option_bind E (%P. F)"


-- "constructor laws for @{text option_bind}"
lemma option_bind_Some: "option_bind (Some s) f = (f s)"
apply (unfold option_bind_def)
apply (simp (no_asm))
done

lemma option_bind_None: "option_bind None f = None"
apply (unfold option_bind_def)
apply (simp (no_asm))
done

declare option_bind_Some [simp] option_bind_None [simp]

-- "expansion of @{text option_bind}"
lemma split_option_bind: "P(option_bind res f) =  
          ((res = None --> P None) & (!s. res = Some s --> P(f s)))"
apply (unfold option_bind_def)
apply (rule option.split)
done

lemma option_bind_eq_None: 
  "((option_bind m f) = None) = ((m=None) | (? p. m = Some p & f p = None))"
apply (simp (no_asm) split add: split_option_bind)
done

declare option_bind_eq_None [simp]

lemma rotate_Some: "(y = Some x) = (Some x = y)"
apply ( simp (no_asm) add: eq_sym_conv)
done

end
