(* Author: Tobias Nipkow, Daniel Wasserrab 
   Extracted from the Jinja theory Common/TypeRel.thy by Tobias Nipkow *)

header {* Relations between CoreC++ types *}

theory TypeRel imports SubObj begin

subsection {* The subtype relation *}


consts
  widen   :: "prog \<Rightarrow> (ty \<times> ty) set"  -- "widening"


syntax (xsymbols)
  widen   :: "prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ \<le> _"   [71,71,71] 70)
  widens  :: "prog \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> bool" ("_ \<turnstile> _ [\<le>] _" [71,71,71] 70)


translations
  "P \<turnstile> T \<le> T'"  ==  "(T,T') \<in> widen P"
  "P \<turnstile> Ts [\<le>] Ts'"  ==  "list_all2 (fun_of (widen P)) Ts Ts'"

inductive "widen P"
intros
  widen_refl[iff]: "P \<turnstile> T \<le> T"
  widen_subcls:    "P \<turnstile> Path C to D unique \<Longrightarrow> P \<turnstile> Class C \<le> Class D"
  widen_null[iff]: "P \<turnstile> NT \<le> Class C"

lemma [iff]: "(P \<turnstile> T \<le> Void) = (T = Void)"
by (auto elim: widen.elims)

lemma [iff]: "(P \<turnstile> T \<le> Boolean) = (T = Boolean)"
by (auto elim: widen.elims)

lemma [iff]: "(P \<turnstile> T \<le> Integer) = (T = Integer)"
by (auto elim: widen.elims)

lemma [iff]: "(P \<turnstile> Void \<le> T) = (T = Void)"
by (auto elim: widen.elims)

lemma [iff]: "(P \<turnstile> Boolean \<le> T) = (T = Boolean)"
by (auto elim: widen.elims)

lemma [iff]: "(P \<turnstile> Integer \<le> T) = (T = Integer)"
by (auto elim: widen.elims)


lemma [iff]: "(P \<turnstile> T \<le> NT) = (T = NT)"

apply(cases T) apply auto
apply (ind_cases "P \<turnstile> T \<le> T'")
apply auto
done


lemmas widens_refl [iff] = rel_list_all2_refl [OF widen_refl]
lemmas widens_Cons [iff] = rel_list_all2_Cons1 [of "widen P", standard]




end
