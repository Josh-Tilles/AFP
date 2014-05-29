header {* Stutter Invariance of next-free LTL Formula *}
theory LTL_Stutter
imports LTL "../Stuttering_Equivalence/PLTL"
begin
  text {* This theory builds on the AFP-entry by Stephan Merz *}

  text {* Get rid of overlapping notation *}
  no_notation PLTL.holds_of ("_ \<Turnstile> _" [70,70] 40)

  hide_const (open) PLTL.false PLTL.atom PLTL.implies PLTL.next PLTL.until
  hide_const (open) PLTL.not PLTL.true PLTL.or PLTL.and 
  hide_const (open) PLTL.eventually PLTL.always

  no_notation Samplers.suffix ("_[_ ..]" [80, 15] 80)
  hide_const (open) Samplers.suffix
  hide_fact (open) Samplers.suffix_def

  lemma PLTL_suffix_cnv[simp]: "Samplers.suffix = (\<lambda>w i. suffix i w)"
    apply (intro ext)
    unfolding Samplers.suffix_def Words.suffix_def ..

  hide_const (open) PLTL.next_free

  primrec ltl_next_free :: "'a ltl \<Rightarrow> bool" where
    "ltl_next_free LTLTrue \<longleftrightarrow> True"
  | "ltl_next_free LTLFalse \<longleftrightarrow> True"
  | "ltl_next_free (LTLProp _) \<longleftrightarrow> True"
  | "ltl_next_free (LTLNeg \<phi>) \<longleftrightarrow> ltl_next_free \<phi>"
  | "ltl_next_free (LTLAnd \<phi> \<psi>) \<longleftrightarrow> ltl_next_free \<phi> \<and> ltl_next_free \<psi>"
  | "ltl_next_free (LTLOr \<phi> \<psi>) \<longleftrightarrow> ltl_next_free \<phi> \<and> ltl_next_free \<psi>"
  | "ltl_next_free (LTLNext _) \<longleftrightarrow> False"
  | "ltl_next_free (LTLUntil \<phi> \<psi>) \<longleftrightarrow> ltl_next_free \<phi> \<and> ltl_next_free \<psi>"
  | "ltl_next_free (LTLRelease \<phi> \<psi>) \<longleftrightarrow> ltl_next_free \<phi> \<and> ltl_next_free \<psi>"

  text {* Conversion between the two LTL formalizations *}

  primrec cnv :: "'a LTL.ltl \<Rightarrow> 'a set PLTL.pltl" where
    "cnv LTLTrue = PLTL.true"
  | "cnv LTLFalse = PLTL.false"
  | "cnv (LTLProp a) = PLTL.atom (op \<in> a)"
  | "cnv (LTLNeg \<phi>) = PLTL.not (cnv \<phi>)"
  | "cnv (LTLAnd \<phi> \<psi>) = PLTL.and (cnv \<phi>) (cnv \<psi>)"
  | "cnv (LTLOr \<phi> \<psi>) = PLTL.or (cnv \<phi>) (cnv \<psi>)"
  | "cnv (LTLNext \<phi>) = PLTL.next (cnv \<phi>)"
  | "cnv (LTLUntil \<phi> \<psi>) = PLTL.until (cnv \<phi>) (cnv \<psi>)"
  | "cnv (LTLRelease \<phi> \<psi>) 
    = PLTL.not (PLTL.until (PLTL.not (cnv \<phi>)) (PLTL.not (cnv \<psi>)))"

  lemma PLTL_holds_of_cnv[simp]: "PLTL.holds_of r (cnv \<phi>) \<longleftrightarrow> ltl_semantics r \<phi>"
    by (induction \<phi> arbitrary: r) simp_all

  lemma PLTL_next_free_cnv[simp]: "PLTL.next_free (cnv \<phi>) \<longleftrightarrow> ltl_next_free \<phi>"
    by (induction \<phi>) auto


  theorem next_free_stutter_invariant: 
    assumes next_free: "ltl_next_free \<phi>"
    assumes eq: "r \<approx> r'"
    shows "r \<Turnstile> \<phi> \<longleftrightarrow> r' \<Turnstile> \<phi>"
    -- {* A next free formula cannot distinguish between 
      stutter-equivalent runs. *}
  proof -
    {
      fix r r'
      assume eq: "r \<approx> r'" and holds: "r \<Turnstile> \<phi>"
      hence "holds_of r (cnv \<phi>)" by simp
      
      from next_free_stutter_invariant[of "cnv \<phi>"] next_free 
      have "PLTL.stutter_invariant (cnv \<phi>)" by simp
      from stutter_invariantD[OF this eq] holds have "r' \<Turnstile> \<phi>" by simp
    } note aux=this
    
    from aux[of r r'] aux[of r' r] eq stutter_equiv_sym[OF eq] show ?thesis
      by blast
  qed

end
