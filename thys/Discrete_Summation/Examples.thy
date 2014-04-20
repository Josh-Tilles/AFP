
(* Author: Florian Haftmann, TU Muenchen *)

header {* Simple examples *}

theory Examples
imports Summation_Conversion
begin

ML {*
  Summation.conv @{context}
  @{cterm "\<Sigma> (\<lambda>q::rat. q ^ Suc (Suc (Suc 0)) + 3) 0 j"}
*}

ML {*
  Summation.conv @{context}
  @{cterm "\<Sigma> (\<lambda>x::real. x ^ Suc (Suc (Suc 0)) + 3) 0 j"}
*}

ML {*
  Summation.conv @{context}
  @{cterm "\<Sigma> (\<lambda>k::int. k ^ Suc (Suc (Suc 0)) + 3) 0 j"}
*}

end