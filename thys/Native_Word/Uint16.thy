(*  Title:      Uint16.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

header {* Unsigned words of 16 bits *}

theory Uint16 imports
  Word_Misc
  Bits_Integer
begin

text {*
  Restriction for ML code generation:
  This theory assumes that the ML system provides a Word16
  implementation (mlton does, but PolyML 5.5 does not).
  Therefore, the code setup lives in the target @{text SML_word}
  rather than @{text SML}.  This ensures that code generation still
  works as long as @{text "uint16"} is not involved.
  For the target @{text SML} itself, no special code generation 
  for this type is set up. Nevertheless, it should work by emulation via @{typ "16 word"} 
  if the theory @{text Code_Target_Bits_Int} is imported.

  Restriction for OCaml code generation:
  OCaml does not provide an int16 type, so no special code generation 
  for this type is set up.
*}

declare Quotient_prod[transfer_rule]

section {* Type definition and primitive operations *}

typedef uint16 = "UNIV :: 16 word set" ..

setup_lifting type_definition_uint16

text {* Use an abstract type for code generation to disable pattern matching on @{term Abs_uint16}. *}
declare Rep_uint16_inverse[code abstype]

declare Quotient_uint16[transfer_rule]

instantiation uint16 :: "{neg_numeral, Divides.div, comm_monoid_mult, comm_ring}" begin
lift_definition zero_uint16 :: uint16 is "0" .
lift_definition one_uint16 :: uint16 is "1" .
lift_definition plus_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" is "op +" .
lift_definition minus_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" is "op -" .
lift_definition uminus_uint16 :: "uint16 \<Rightarrow> uint16" is uminus .
lift_definition times_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" is "op *" .
lift_definition div_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" is "op div" .
lift_definition mod_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" is "op mod" .
instance by default (transfer, simp add: algebra_simps)+
end

instantiation uint16 :: linorder begin
lift_definition less_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> bool" is "op <" .
lift_definition less_eq_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> bool" is "op \<le>" .
instance by(default)(transfer, simp add: less_le_not_le linear)+
end

lemmas [code] = less_uint16.rep_eq less_eq_uint16.rep_eq

instantiation uint16 :: bitss begin
lift_definition bitNOT_uint16 :: "uint16 \<Rightarrow> uint16" is bitNOT .
lift_definition bitAND_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" is bitAND .
lift_definition bitOR_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" is bitOR .
lift_definition bitXOR_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" is bitXOR .
lift_definition test_bit_uint16 :: "uint16 \<Rightarrow> nat \<Rightarrow> bool" is test_bit .
lift_definition set_bit_uint16 :: "uint16 \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> uint16" is set_bit .
lift_definition set_bits_uint16 :: "(nat \<Rightarrow> bool) \<Rightarrow> uint16" is "set_bits" .
lift_definition lsb_uint16 :: "uint16 \<Rightarrow> bool" is lsb .
lift_definition shiftl_uint16 :: "uint16 \<Rightarrow> nat \<Rightarrow> uint16" is shiftl .
lift_definition shiftr_uint16 :: "uint16 \<Rightarrow> nat \<Rightarrow> uint16" is shiftr .
lift_definition msb_uint16 :: "uint16 \<Rightarrow> bool" is msb .
instance ..
end

lemmas [code] = test_bit_uint16.rep_eq lsb_uint16.rep_eq msb_uint16.rep_eq

instantiation uint16 :: equal begin
lift_definition equal_uint16 :: "uint16 \<Rightarrow> uint16 \<Rightarrow> bool" is "equal_class.equal" .
instance by default(transfer, simp add: equal_eq)
end

lemmas [code] = equal_uint16.rep_eq

instantiation uint16 :: size begin
lift_definition size_uint16 :: "uint16 \<Rightarrow> nat" is "size" .
instance ..
end

lemmas [code] = size_uint16.rep_eq

lift_definition sshiftr_uint16 :: "uint16 \<Rightarrow> nat \<Rightarrow> uint16" (infixl ">>>" 55) is sshiftr .

lift_definition uint16_of_int :: "int \<Rightarrow> uint16" is "word_of_int" .

text {* Use pretty numerals from integer for pretty printing *}

lift_definition Uint16 :: "integer \<Rightarrow> uint16" is "word_of_int" .

lemma Rep_uint16_numeral [simp]: "Rep_uint16 (numeral n) = numeral n"
by(induction n)(simp_all add: one_uint16_def Abs_uint16_inverse numeral.simps plus_uint16_def)

lemma Rep_uint16_neg_numeral [simp]: "Rep_uint16 (neg_numeral n) = neg_numeral n"
by(simp only: neg_numeral_def uminus_uint16_def)(simp add: Abs_uint16_inverse)

context begin interpretation lifting_syntax .

lemma [transfer_rule]: "(op = ===> cr_uint16 ===> op =) (\<lambda>n m. cr_uint16 m n) op ="
by(auto 4 3 simp add: cr_uint16_def Rep_uint16_inject)

lemma uint16_neg_numeral_transfer [transfer_rule]:
  "(op = ===> cr_uint16) neg_numeral neg_numeral"
by(auto simp add: cr_uint16_def)

lemma numeral_uint16_transfer [transfer_rule]:
  "(fun_rel op = cr_uint16) numeral numeral"
by(auto simp add: cr_uint16_def)

end

lemma numeral_uint16 [code_unfold]: "numeral n = Uint16 (numeral n)"
by transfer simp

lemma neg_numeral_uint16 [code_unfold]: "neg_numeral n = Uint16 (neg_numeral n)"
by transfer(simp add: cr_uint16_def)

lemma Abs_uint16_numeral [code_post]: "Abs_uint16 (numeral n) = numeral n"
by(induction n)(simp_all add: one_uint16_def numeral.simps plus_uint16_def Abs_uint16_inverse)

lemma Abs_uint16_0 [code_post]: "Abs_uint16 0 = 0"
by(simp add: zero_uint16_def)

lemma Abs_uint16_1 [code_post]: "Abs_uint16 1 = 1"
by(simp add: one_uint16_def)

section {* Code setup *}

code_printing code_module Uint16 \<rightharpoonup> (SML_word)
{*(* Test that words can handle numbers between 0 and 15 *)
val _ = if 4 <= Word.wordSize then () else raise (Fail ("wordSize less than 4"));

structure Uint16 : sig
  val set_bit : Word16.word -> IntInf.int -> bool -> Word16.word
  val shiftl : Word16.word -> IntInf.int -> Word16.word
  val shiftr : Word16.word -> IntInf.int -> Word16.word
  val shiftr_signed : Word16.word -> IntInf.int -> Word16.word
  val test_bit : Word16.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word16.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word16.orb (x, mask)
     else Word16.andb (x, Word16.notb mask)
  end

fun shiftl x n =
  Word16.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word16.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word16.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word16.andb (x, Word16.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word16.fromInt 0

end; (* struct Uint16 *)*}
code_reserved SML_word Uint16

code_printing code_module Uint16 \<rightharpoonup> (Haskell)
{*import qualified Data.Word;
import qualified Data.Int;

type Int16 = Data.Int.Int16;

type Word16 = Data.Word.Word16;*}
code_reserved Haskell Uint16

text {* Scala provides unsigned 16-bit numbers as Char. *}

code_printing code_module Uint16 \<rightharpoonup> (Scala)
{*object Uint16 {

def set_bit(x: Char, n: BigInt, b: Boolean) : Char =
  if (b)
    (x | (1.toChar << n.intValue)).toChar
  else
    (x & (1.toChar << n.intValue).unary_~).toChar

def shiftl(x: Char, n: BigInt) : Char = (x << n.intValue).toChar

def shiftr(x: Char, n: BigInt) : Char = (x >>> n.intValue).toChar

def shiftr_signed(x: Char, n: BigInt) : Char = (x.toShort >> n.intValue).toChar

def test_bit(x: Char, n: BigInt) : Boolean = (x & (1.toChar << n.intValue)) != 0

} /* object Uint16 */*}
code_reserved Scala Uint16

text {* 
  Avoid @{term Abs_uint16} in generated code, use @{term Rep_uint16'} instead. 
  The symbolic implementations for code\_simp use @{term Rep_uint16}.

  The new destructor @{term Rep_uint16'} is executable.
  As the simplifier is given the [code abstract] equations literally, 
  we cannot implement @{term Rep_uint16} directly, because that makes code\_simp loop.

  If code generation raises Match, some equation probably contains @{term Rep_uint16} 
  ([code abstract] equations for @{typ uint16} may use @{term Rep_uint16} because
  these instances will be folded away.)
*}

definition Rep_uint16' where [simp]: "Rep_uint16' = Rep_uint16"

lemma Rep_uint16'_code [code]: "Rep_uint16' x = (BITS n. x !! n)"
unfolding Rep_uint16'_def by transfer simp

lemma [code, code del]: "term_of_class.term_of = (term_of_class.term_of :: uint16 \<Rightarrow> _)" ..

lemma term_of_uint16_code [code]:
  defines "TR \<equiv> typerep.Typerep" and "bit0 \<equiv> STR ''Numeral_Type.bit0''" shows
  "term_of_class.term_of x = 
   Code_Evaluation.App (Code_Evaluation.Const (STR ''Uint16.Abs_uint16'') (TR (STR ''fun'') [TR (STR ''Word.word'') [TR bit0 [TR bit0 [TR bit0 [TR bit0 [TR (STR ''Numeral_Type.num1'') []]]]]], TR (STR ''Uint16.uint16'') []]))
       (term_of_class.term_of (Rep_uint16' x))"
by(simp add: term_of_anything)

lemma Uin16_code [code abstract]: "Rep_uint16 (Uint16 i) = word_of_int (int_of_integer_symbolic i)"
unfolding Uint16_def int_of_integer_symbolic_def by(simp add: Abs_uint16_inverse)

code_printing
  type_constructor uint16 \<rightharpoonup>
  (SML_word) "Word16.word" and
  (Haskell) "Uint16.Word16" and
  (Scala) "Char"
| constant Uint16 \<rightharpoonup>
  (SML_word) "Word16.fromInt" and
  (Haskell) "(Prelude.fromInteger _ :: Uint16.Word16)" and
  (Scala) "_.charValue"
| constant "0 :: uint16" \<rightharpoonup>
  (SML_word) "(Word16.fromInt 0)" and
  (Haskell) "(0 :: Uint16.Word16)" and
  (Scala) "0"
| constant "1 :: uint16" \<rightharpoonup>
  (SML_word) "(Word16.fromInt 1)" and
  (Haskell) "(1 :: Uint16.Word16)" and
  (Scala) "1"
| constant "plus :: uint16 \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.+ ((_), (_))" and
  (Haskell) infixl 6 "+" and
  (Scala) "(_ +/ _).toChar"
| constant "uminus :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.~" and
  (Haskell) "negate" and
  (Scala) "(- _).toChar"
| constant "minus :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.- ((_), (_))" and
  (Haskell) infixl 6 "-" and
  (Scala) "(_ -/ _).toChar"
| constant "times :: uint16 \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.* ((_), (_))" and
  (Haskell) infixl 7 "*" and
  (Scala) "(_ */ _).toChar"
| constant "HOL.equal :: uint16 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML_word) "!((_ : Word16.word) = _)" and
  (Haskell) infix 4 "==" and
  (Scala) infixl 5 "=="
| class_instance uint16 :: equal \<rightharpoonup> (Haskell) -
| constant "less_eq :: uint16 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML_word) "Word16.<= ((_), (_))" and
  (Haskell) infix 4 "<=" and
  (Scala) infixl 4 "<="
| constant "less :: uint16 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML_word) "Word16.< ((_), (_))" and
  (Haskell) infix 4 "<" and
  (Scala) infixl 4 "<"
| constant "bitNOT :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.notb" and
  (Haskell) "Data'_Bits.complement" and
  (Scala) "_.unary'_~.toChar"
| constant "bitAND :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.andb ((_),/ (_))" and
  (Haskell) infixl 7 "Data_Bits..&." and
  (Scala) "(_ & _).toChar"
| constant "bitOR :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.orb ((_),/ (_))" and
  (Haskell) infixl 5 "Data_Bits..|." and
  (Scala) "(_ | _).toChar"
| constant "bitXOR :: uint16 \<Rightarrow> _" \<rightharpoonup>
  (SML_word) "Word16.xorb ((_),/ (_))" and
  (Haskell) "Data'_Bits.xor" and
  (Scala) "(_ ^ _).toChar"

definition uint16_div :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" 
where "uint16_div x y = (if y = 0 then undefined (op div :: uint16 \<Rightarrow> _) x (0 :: uint16) else x div y)"

definition uint16_mod :: "uint16 \<Rightarrow> uint16 \<Rightarrow> uint16" 
where "uint16_mod x y = (if y = 0 then undefined (op mod :: uint16 \<Rightarrow> _) x (0 :: uint16) else x mod y)"

context includes undefined_transfer begin

lemma div_uint16_code [code]: "x div y = (if y = 0 then 0 else uint16_div x y)"
unfolding uint16_div_def by transfer(simp add: word_div_def)

lemma mod_uint16_code [code]: "x mod y = (if y = 0 then x else uint16_mod x y)"
unfolding uint16_mod_def by transfer(simp add: word_mod_def)

lemma uint16_div_code [code abstract]:
  "Rep_uint16 (uint16_div x y) =
  (if y = 0 then Rep_uint16 (undefined (op div :: uint16 \<Rightarrow> _) x (0 :: uint16)) else Rep_uint16 x div Rep_uint16 y)"
unfolding uint16_div_def by transfer simp

lemma uint16_mod_code [code abstract]:
  "Rep_uint16 (uint16_mod x y) =
  (if y = 0 then Rep_uint16 (undefined (op mod :: uint16 \<Rightarrow> _) x (0 :: uint16)) else Rep_uint16 x mod Rep_uint16 y)"
unfolding uint16_mod_def by transfer simp

end

code_printing constant uint16_div \<rightharpoonup>
  (SML_word) "Word16.div ((_), (_))" and
  (Haskell) "Prelude.div" and
  (Scala) "(_ '/ _).toChar"
| constant uint16_mod \<rightharpoonup>
  (SML_word) "Word16.mod ((_), (_))" and
  (Haskell) "Prelude.mod" and
  (Scala) "(_ % _).toChar"

definition uint16_test_bit :: "uint16 \<Rightarrow> integer \<Rightarrow> bool"
where [code del]:
  "uint16_test_bit x n =
  (if n < 0 \<or> 15 < n then undefined (test_bit :: uint16 \<Rightarrow> _) x n
   else x !! (nat_of_integer n))"

lemma test_bit_uint16_code [code]:
  "test_bit x n \<longleftrightarrow> n < 16 \<and> uint16_test_bit x (integer_of_nat n)"
unfolding uint16_test_bit_def
including undefined_transfer by transfer(auto cong: conj_cong dest: test_bit_size simp add: word_size)

lemma uint16_test_bit_code [code]:
  "uint16_test_bit w n =
  (if n < 0 \<or> 15 < n then undefined (test_bit :: uint16 \<Rightarrow> _) w n else Rep_uint16 w !! nat_of_integer n)"
unfolding uint16_test_bit_def by(simp add: test_bit_uint16.rep_eq)

code_printing constant uint16_test_bit \<rightharpoonup>
  (SML_word) "Uint16.test'_bit" and
  (Haskell) "Data'_Bits.testBitBounded" and
  (Scala) "Uint16.test'_bit"

definition uint16_set_bit :: "uint16 \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint16"
where [code del]:
  "uint16_set_bit x n b =
  (if n < 0 \<or> 15 < n then undefined (set_bit :: uint16 \<Rightarrow> _) x n b
   else set_bit x (nat_of_integer n) b)"

lemma set_bit_uint16_code [code]:
  "set_bit x n b = (if n < 16 then uint16_set_bit x (integer_of_nat n) b else x)"
including undefined_transfer unfolding uint16_set_bit_def
by(transfer)(auto cong: conj_cong simp add: not_less set_bit_beyond word_size)

lemma uint16_set_bit_code [code abstract]:
  "Rep_uint16 (uint16_set_bit w n b) = 
  (if n < 0 \<or> 15 < n then Rep_uint16 (undefined (set_bit :: uint16 \<Rightarrow> _) w n b)
   else set_bit (Rep_uint16 w) (nat_of_integer n) b)"
including undefined_transfer unfolding uint16_set_bit_def by transfer simp

code_printing constant uint16_set_bit \<rightharpoonup>
  (SML_word) "Uint16.set'_bit" and
  (Haskell) "Data'_Bits.setBitBounded" and
  (Scala) "Uint16.set'_bit"

lift_definition uint16_set_bits :: "(nat \<Rightarrow> bool) \<Rightarrow> uint16 \<Rightarrow> nat \<Rightarrow> uint16" is set_bits_aux .

lemma uint16_set_bits_code [code]:
  "uint16_set_bits f w n =
  (if n = 0 then w 
   else let n' = n - 1 in uint16_set_bits f ((w << 1) OR (if f n' then 1 else 0)) n')"
by(transfer fixing: n)(cases n, simp_all)

lemma set_bits_uint16 [code]:
  "(BITS n. f n) = uint16_set_bits f 0 16"
by transfer(simp add: set_bits_conv_set_bits_aux)


lemma lsb_code [code]: fixes x :: uint16 shows "lsb x = x !! 0"
by transfer(simp add: word_lsb_def word_test_bit_def)


definition uint16_shiftl :: "uint16 \<Rightarrow> integer \<Rightarrow> uint16"
where [code del]:
  "uint16_shiftl x n = (if n < 0 \<or> 16 \<le> n then undefined (shiftl :: uint16 \<Rightarrow> _) x n else x << (nat_of_integer n))"

lemma shiftl_uint16_code [code]: "x << n = (if n < 16 then uint16_shiftl x (integer_of_nat n) else 0)"
including undefined_transfer unfolding uint16_shiftl_def
by transfer(simp add: not_less shiftl_zero_size word_size)

lemma uint16_shiftl_code [code abstract]:
  "Rep_uint16 (uint16_shiftl w n) =
  (if n < 0 \<or> 16 \<le> n then Rep_uint16 (undefined (shiftl :: uint16 \<Rightarrow> _) w n)
   else Rep_uint16 w << nat_of_integer n)"
including undefined_transfer unfolding uint16_shiftl_def by transfer simp

code_printing constant uint16_shiftl \<rightharpoonup>
  (SML_word) "Uint16.shiftl" and
  (Haskell) "Data'_Bits.shiftlBounded" and
  (Scala) "Uint16.shiftl"

definition uint16_shiftr :: "uint16 \<Rightarrow> integer \<Rightarrow> uint16"
where [code del]:
  "uint16_shiftr x n = (if n < 0 \<or> 16 \<le> n then undefined (shiftr :: uint16 \<Rightarrow> _) x n else x >> (nat_of_integer n))"

lemma shiftr_uint16_code [code]: "x >> n = (if n < 16 then uint16_shiftr x (integer_of_nat n) else 0)"
including undefined_transfer unfolding uint16_shiftr_def
by transfer(simp add: not_less shiftr_zero_size word_size)

lemma uint16_shiftr_code [code abstract]:
  "Rep_uint16 (uint16_shiftr w n) =
  (if n < 0 \<or> 16 \<le> n then Rep_uint16 (undefined (shiftr :: uint16 \<Rightarrow> _) w n)
   else Rep_uint16 w >> nat_of_integer n)"
including undefined_transfer unfolding uint16_shiftr_def by transfer simp

code_printing constant uint16_shiftr \<rightharpoonup>
  (SML_word) "Uint16.shiftr" and
  (Haskell) "Data'_Bits.shiftrBounded" and
  (Scala) "Uint16.shiftr"

definition uint16_sshiftr :: "uint16 \<Rightarrow> integer \<Rightarrow> uint16"
where [code del]:
  "uint16_sshiftr x n =
  (if n < 0 \<or> 16 \<le> n then undefined sshiftr_uint16 x n else sshiftr_uint16 x (nat_of_integer n))"

lemma sshiftr_beyond: fixes x :: "'a :: len word" shows
  "size x \<le> n \<Longrightarrow> x >>> n = (if x !! (size x - 1) then -1 else 0)"
by(rule word_eqI)(simp add: nth_sshiftr word_size)

lemma sshiftr_uint16_code [code]:
  "x >>> n = 
  (if n < 16 then uint16_sshiftr x (integer_of_nat n) else if x !! 15 then -1 else 0)"
including undefined_transfer unfolding uint16_sshiftr_def
by transfer (simp add: not_less sshiftr_beyond word_size)

lemma uint16_sshiftr_code [code abstract]:
  "Rep_uint16 (uint16_sshiftr w n) =
  (if n < 0 \<or> 16 \<le> n then Rep_uint16 (undefined sshiftr_uint16 w n)
   else Rep_uint16 w >>> nat_of_integer n)"
including undefined_transfer unfolding uint16_sshiftr_def by transfer simp

code_printing constant uint16_sshiftr \<rightharpoonup>
  (SML_word) "Uint16.shiftr'_signed" and
  (Haskell) 
    "(Prelude.fromInteger (Prelude.toInteger (Data'_Bits.shiftrBounded (Prelude.fromInteger (Prelude.toInteger _) :: Uint16.Int16) _)) :: Uint16.Word16)" and
  (Scala) "Uint16.shiftr'_signed"

lemma uint16_msb_test_bit: "msb x \<longleftrightarrow> (x :: uint16) !! 15"
by transfer(simp add: msb_nth)

lemma msb_uint16_code [code]: "msb x \<longleftrightarrow> uint16_test_bit x 15"
by(simp add: uint16_test_bit_def uint16_msb_test_bit)

lemma uint16_of_int_code [code]: "uint16_of_int i = (BITS n. i !! n)"
by transfer(simp add: word_of_int_conv_set_bits test_bit_int_def[abs_def])

section {* Tests *}

definition test_uint16 where
  "test_uint16 \<longleftrightarrow>
  (([ 0x10001, -1, -65535, 0xFFFF, 0x1234
    , 0x5A AND 0x36
    , 0x5A OR 0x36
    , 0x5A XOR 0x36
    , NOT 0x5A
    , 5 + 6, -5 + 6, -6 + 5, -5 + -6, 0xFFFF + 1
    , 5 - 3, 3 - 5
    , 5 * 3, -5 * 3, -5 * -4, 0x1234 * 0x8765
    , 5 div 3, -5 div 3, -5 div -3, 5 div -3
    , 5 mod 3, -5 mod 3, -5 mod -3, 5 mod -3
    , set_bit 5 4 True, set_bit -5 2 True, set_bit 5 0 False, set_bit -5 1 False
    , set_bit 5 32 True, set_bit 5 32 False, set_bit -5 32 True, set_bit -5 32 False
    , 1 << 2, -1 << 3, 1 << 16, 1 << 0
    , 100 >> 3, -100 >> 3, 100 >> 16, -100 >> 16
    , 100 >>> 3, -100 >>> 3, 100 >>> 16, -100 >>> 16] :: uint16 list)
   =
    [ 1, 65535, 1, 65535, 4660
    , 18
    , 126
    , 108
    , 65445
    , 11, 1, 65535, 65525, 0
    , 2, 65534
    , 15, 65521, 20, 39556
    , 1, 21843, 0, 0
    , 2, 2, 65531, 5
    , 21, 65535, 4, 65529
    , 5, 5, 65531, 65531
    , 4, 65528, 0, 1
    , 12, 8179, 0, 0
    , 12, 65523, 0, 65535]) \<and>
  ([ (0x5 :: uint16) = 0x5, (0x5 :: uint16) = 0x6
   , (0x5 :: uint16) < 0x5, (0x5 :: uint16) < 0x6, (-5 :: uint16) < 6, (6 :: uint16) < -5
   , (0x5 :: uint16) \<le> 0x5, (0x5 :: uint16) \<le> 0x4, (-5 :: uint16) \<le> 6, (6 :: uint16) \<le> -5 
   , (0x7FFF :: uint16) < 0x8000, (0xFFFF :: uint16) < 0, (0x8000 :: uint16) < 0x7FFF
   , (0x7FFF :: uint16) !! 0, (0x7FFF :: uint16) !! 15, (0x8000 :: uint16) !! 15, (0x8000 :: uint16) !! 16
   ]
  =
   [ True, False
   , False, True, False, True
   , True, False, False, True
   , True, False, False
   , True, False, True, False
   ]
  )"

export_code test_uint16 checking Haskell? Scala
export_code test_uint16 in SML_word

notepad begin
have test_uint16 by code_simp
have test_uint16 by normalization
end

hide_const test_uint16
hide_fact test_uint16_def
no_notation sshiftr_uint16 (infixl ">>>" 55)

end
