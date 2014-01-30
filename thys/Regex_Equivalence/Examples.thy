(*  Author: Tobias Nipkow, Dmitriy Traytel *)

header {* Some Tests *}

(*<*)
theory Examples
imports Regex_Equivalence
begin
(*>*)

section {* Examples *}

(*<*)
text{* Test: B(n) = (One + a + aa + · · · + a^n-1 ) (a^n)^* = a^* (see Asperti) *}
(*>*)

fun pow where
  "pow 0 = One"
| "pow (Suc 0) = Atom True"
| "pow (Suc n) = Times (Atom True) (pow n)"

fun pow_left where
  "pow_left 0 = One"
| "pow_left (Suc 0) = Atom True"
| "pow_left (Suc n) = Times (pow_left n) (Atom True)"

fun Sum where
  "Sum f 0 = f 0"
| "Sum f (Suc n) = Plus (f (Suc n)) (Sum f n)"

definition "B n = (Times (Sum pow (n - 1)) (Star (pow n)), Star (Atom True))"
definition "B_left n = (Times (Sum pow_left (n - 1)) (Star (pow_left n)), Star (Atom True))"

definition "seq_left n r = foldr (\<lambda>r s. Times s r) (replicate n r) One"
definition "seq n r = foldr Times (replicate n r) One"
definition "re_left n = Times (seq_left n (Plus (Atom True) One)) (seq_left n (Atom True))"
definition "re n = Times (seq n (Plus (Atom True) One)) (seq n (Atom True))"
definition "M n = (re_left n, replicate n True)"

lemma "split match_brz (M 128)" by eval
lemma "split match_brzq (M 128)" by eval
lemma "split match_n (M 64)" by eval
lemma "split match_p (M 64)" by eval
lemma "split match_pn (M 64)" by eval
lemma "split match_a (M 512)" by eval
lemma "split match_b (M 512)" by eval
lemma "split match_a2 (M 2048)" by eval
lemma "split match_b2 (M 2048)" by eval


lemma "split check_eqv_brz (B 32)" by eval
lemma "split check_eqv_brzq (B 16)" by eval
lemma "split check_eqv_n (B 256)" by eval
lemma "split check_eqv_p (B 256)" by eval
lemma "split check_eqv_b (B 256)" by eval
lemma "split check_eqv_a (B 256)" by eval
lemma "split check_eqv_b2 (B 256)" by eval
lemma "split check_eqv_a2 (B 256)" by eval

(*<*)
end
(*>*)
