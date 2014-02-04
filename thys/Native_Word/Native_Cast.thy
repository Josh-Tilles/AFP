(*  Title:      Native_Cast.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

header {* Conversions between unsigned words and between char *}

theory Native_Cast imports
  "~~/src/HOL/Library/Code_Char"
  Uint8
  Uint16
  Uint32
begin

text {* Setup @{const integer_of_char} for symbolic evaluation 
  %This should actually be done in @{theory Code_Char}.
*}

declare integer_of_char_def [code del]

lemma integer_of_nat_0: "integer_of_nat 0 = 0"
by transfer simp

lemma integer_of_nat_1: "integer_of_nat 1 = 1"
by transfer simp

lemma integer_of_nat_numeral:
  "integer_of_nat (numeral n) = numeral n"
by transfer simp

lemmas integer_of_char_code [code] =
  nat_of_char_simps[
    THEN arg_cong[where f="integer_of_nat"],
    unfolded integer_of_nat_numeral integer_of_nat_1 integer_of_nat_0,
    folded fun_cong[OF integer_of_char_def, unfolded o_apply]]

lemma char_of_integer_code [code]:
  "char_of_integer n = enum_class.enum ! (nat_of_integer n mod 256)"
by(simp add: char_of_integer_def char_of_nat_def)


text {* Auxiliary stuff *}

context begin interpretation lifting_syntax .

lemma char_of_integer_transfer [transfer_rule]:
  "(pcr_integer ===> op =) (\<lambda>n. char_of_nat (nat n)) char_of_integer"
by(simp add: integer.pcr_cr_eq cr_integer_def fun_rel_def char_of_integer_def nat_of_integer_def)

lemma integer_of_char_transfer [transfer_rule]:
  "(op = ===> pcr_integer) (\<lambda>n. int (nat_of_char n)) integer_of_char"
by(simp add: integer.pcr_cr_eq cr_integer_def fun_rel_def integer_of_char_def)

end

lemma integer_of_char_char_of_integer [simp]:
  "0 \<le> x \<Longrightarrow> integer_of_char (char_of_integer x) = x mod 256"
unfolding integer_of_char_def char_of_integer_def o_apply nat_of_char_of_nat
by transfer(auto dest: nat_mod_distrib[of _ 256, symmetric])

lemma char_of_integer_integer_of_char [simp]:
  "char_of_integer (integer_of_char x) = x"
by(simp add: integer_of_char_def char_of_integer_def)

lemma int_lt_numeral [simp]: "int x < numeral n \<longleftrightarrow> x < numeral n"
by (metis nat_numeral zless_nat_eq_int_zless)

lemma int_of_integer_ge_0: "0 \<le> int_of_integer x \<longleftrightarrow> 0 \<le> x"
by transfer simp

lemma integer_of_char_ge_0 [simp]: "0 \<le> integer_of_char x"
by transfer simp


section {* Conversions between @{typ uint8} and @{typ char} *}

definition uint8_of_char :: "char \<Rightarrow> uint8"
where "uint8_of_char = Uint8 \<circ> integer_of_char"

definition char_of_uint8 :: "uint8 \<Rightarrow> char"
where "char_of_uint8 = char_of_integer \<circ> integer_of_int \<circ> uint \<circ> Rep_uint8'"

lemma uint8_of_char_char_of_uint8 [simp]:
  "uint8_of_char (char_of_uint8 x) = x"
apply(simp add: uint8_of_char_def char_of_uint8_def)
apply transfer
apply(simp add: mod_pos_pos_trivial uint_bounded[where ?'a=8, simplified])
done

lemma char_of_uint8_uint8_of_char [simp]:
  "char_of_uint8 (uint8_of_char x) = x"
proof -
  have "char_of_uint8 (uint8_of_char x) = 
    char_of_integer (of_int (int_of_integer (integer_of_char x) mod 256))"
    by(simp add: uint8_of_char_def char_of_uint8_def Uint8.rep_eq uint_word_of_int)
  also { have "int_of_integer (integer_of_char x) < 256"
      by transfer(simp add: nat_of_char_less_256) }
  hence "\<dots> = x"
    by(simp add: semiring_numeral_div_class.mod_less int_of_integer_ge_0)
  finally show ?thesis .
qed

code_printing code_module Native_Casts \<rightharpoonup> (Haskell)
{*import qualified Data.Char;

ord :: Char -> Int;
ord = Data.Char.ord;

chr :: Int -> Char;
chr = Data.Char.chr;
*}
code_reserved Haskell Native_Casts

code_printing constant uint8_of_char \<rightharpoonup>
  (SML) "Word8.fromInt (Char.ord _)" and
  (Haskell) "(Prelude.fromIntegral (Native'_Casts.ord _) :: Uint8.Word8)" and
  (Scala) "_.toByte"
| constant char_of_uint8 \<rightharpoonup>
  (SML) "Char.chr (Word8.toInt _)" and
  (Haskell) "Native'_Casts.chr (Prelude.fromIntegral _)" and
  (Scala) "((_).toInt & 0xFF).toChar"

section {* Conversion between native words *}

lift_definition uint8_of_uint32 :: "uint32 \<Rightarrow> uint8" is ucast .
lift_definition uint8_of_uint16 :: "uint16 \<Rightarrow> uint8" is ucast .

lift_definition uint16_of_uint8 :: "uint8 \<Rightarrow> uint16" is ucast .
lift_definition uint16_of_uint32 :: "uint32 \<Rightarrow> uint16" is ucast .

lift_definition uint32_of_uint8 :: "uint8 \<Rightarrow> uint32" is ucast .
lift_definition uint32_of_uint16 :: "uint16 \<Rightarrow> uint32" is ucast .

code_printing
  constant uint8_of_uint16 \<rightharpoonup>
  (SML_word) "Word8.fromLarge (Word16.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint8.Word8)" and
  (Scala) "_.toByte"
| constant uint8_of_uint32 \<rightharpoonup>
  (SML) "Word8.fromLarge (Word32.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint8.Word8)" and
  (Scala) "_.toByte"
| constant uint16_of_uint8 \<rightharpoonup>
  (SML_word) "Word16.fromLarge (Word8.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint16.Word16)" and
  (Scala) "((_).toInt & 0xFF).toChar"
| constant uint16_of_uint32 \<rightharpoonup>
  (SML_word) "Word16.fromLarge (Word32.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint16.Word16)" and
  (Scala) "_.toChar"
| constant uint32_of_uint8 \<rightharpoonup>
  (SML) "Word32.fromLarge (Word8.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint32.Word32)" and
  (Scala) "((_).toInt & 0xFF)"
| constant uint32_of_uint16 \<rightharpoonup>
  (SML) "Word32.fromLarge (Word16.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint32.Word32)" and
  (Scala) "(_).toInt"

text {* 
  Use @{const Abs_uint8'} etc. instead of @{const Rep_uint8} in code equations
  for conversion functions to avoid exceptions during code generation when the
  target language provides only some of the uint types.
*}

lemma uint8_of_uint16_code [code]:
  "uint8_of_uint16 x = Abs_uint8' (ucast (Rep_uint16' x))"
by transfer simp

lemma uint8_of_uint32_code [code]:
  "uint8_of_uint32 x = Abs_uint8' (ucast (Rep_uint32' x))"
by transfer simp

lemma uint16_of_uint8_code [code]:
  "uint16_of_uint8 x = Abs_uint16' (ucast (Rep_uint8' x))"
by transfer simp

lemma uint16_of_uint32_code [code]:
  "uint16_of_uint32 x = Abs_uint16' (ucast (Rep_uint32' x))"
by transfer simp

lemma uint32_of_uint8_code [code]:
  "uint32_of_uint8 x = Abs_uint32' (ucast (Rep_uint8' x))"
by transfer simp

lemma uint32_of_uint16_code [code]:
  "uint32_of_uint16 x = Abs_uint32' (ucast (Rep_uint16' x))"
by transfer simp

section {* Tests *}

definition test_casts :: bool
where "test_casts \<longleftrightarrow>
  map uint8_of_char [CHR ''a'', Char Nibble0 Nibble0, Char NibbleF NibbleF] = [97, 0, 255] \<and>
  map char_of_uint8 [65, 0, 255] = [CHR ''A'', Char Nibble0 Nibble0, Char NibbleF NibbleF] \<and>
  map uint8_of_uint32 [10, 0, 0xFE, 0xFFFFFFFF] = [10, 0, 0xFE, 0xFF] \<and>
  map uint32_of_uint8 [10, 0, 0xFF] = [10, 0, 0xFF]"

definition test_casts' :: bool
where "test_casts' \<longleftrightarrow>
  map uint8_of_uint16 [10, 0, 0xFE, 0xFFFF] = [10, 0, 0xFE, 0xFF] \<and>
  map uint16_of_uint8 [10, 0, 0xFF] = [10, 0, 0xFF] \<and>
  map uint16_of_uint32 [10, 0, 0xFFFE, 0xFFFFFFFF] = [10, 0, 0xFFFE, 0xFFFF] \<and>
  map uint32_of_uint16 [10, 0, 0xFFFF] = [10, 0, 0xFFFF]"

export_code test_casts checking SML Haskell? Scala
export_code test_casts' checking Haskell? Scala

notepad begin
have test_casts by eval
have test_casts by normalization
have test_casts by code_simp
have test_casts' by normalization
have test_casts' by code_simp
end
ML {* val true = @{code test_casts} *}

hide_const test_casts test_casts'
hide_fact test_casts_def test_casts'_def

end