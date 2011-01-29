(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* \isaheader{Hash maps implementation} *}
theory HashMap_Impl
imports Main "common/Misc" ListMapImpl RBTMapImpl HashCode
begin
text_raw {*\label{thy:HashMap}*}

text {*
  This theory implements hashmaps. This uses the abbreviations hm,h.

  We use a red-black tree instead of an indexed array. This
  has the disadvantage of being more complex, however we need not bother
  about a fixed-size array and rehashing if the array becomes too full.

  The entries of the red-black tree are lists of (key,value) pairs.
*}

subsection {* Abstract Hashmap *}
text {*
  We first specify the behavior of our hashmap on the level of maps.
  We will then show that our implementation based on hashcode-map and bucket-map 
  is a correct implementation of this specification.
*}
types 
  ('k,'v) abs_hashmap = "hashcode \<rightharpoonup> ('k \<rightharpoonup> 'v)"

  -- "Map entry of map by function"
abbreviation "map_entry k f m == m(k := f (m k))"


  -- "Invariant: Buckets only contain entries with the right hashcode and there are no empty buckets"
definition ahm_invar:: "('k::hashable,'v) abs_hashmap \<Rightarrow> bool" 
  where "ahm_invar m == 
    (\<forall>hc cm k. m hc = Some cm \<and> k\<in>dom cm \<longrightarrow> hashcode k = hc) \<and> 
    (\<forall>hc cm. m hc = Some cm \<longrightarrow> cm \<noteq> empty)"



  -- "Abstract a hashmap to the corresponding map"
definition ahm_\<alpha> where
  "ahm_\<alpha> m k == case m (hashcode k) of 
    None \<Rightarrow> None |
    Some cm \<Rightarrow> cm k"

  -- "Lookup an entry"
definition ahm_lookup :: "'k::hashable \<Rightarrow> ('k,'v) abs_hashmap \<Rightarrow> 'v option" 
  where "ahm_lookup k m == (ahm_\<alpha> m) k"

  -- "The empty hashmap"
definition ahm_empty :: "('k::hashable,'v) abs_hashmap" 
  where "ahm_empty = empty"

  -- "Update/insert an entry"
definition ahm_update where
  "ahm_update k v m ==
    case m (hashcode k) of
      None \<Rightarrow> m (hashcode k \<mapsto> [k \<mapsto> v]) |
      Some cm \<Rightarrow> m (hashcode k \<mapsto> cm (k \<mapsto> v))
  "

  -- "Delete an entry"
definition ahm_delete where 
  "ahm_delete k m == map_entry (hashcode k) 
    (\<lambda>v. case v of 
      None \<Rightarrow> None | 
      Some bm \<Rightarrow> (
        if bm |` (- {k}) = empty then
          None
        else
          Some ( bm |` (- {k}))
      )
    ) m
  "

definition ahm_isEmpty where
  "ahm_isEmpty m == m=Map.empty"

text {*
  Now follow correctness lemmas, that relate the hashmap operations to
  operations on the corresponding map. Those lemmas are named op\_correct, where
  op is the operation.
*}

lemma ahm_invarI: "\<lbrakk> 
  !!hc cm k. \<lbrakk>m hc = Some cm; k\<in>dom cm\<rbrakk> \<Longrightarrow> hashcode k = hc;
  !!hc cm. \<lbrakk> m hc = Some cm \<rbrakk> \<Longrightarrow> cm \<noteq> empty
  \<rbrakk> \<Longrightarrow> ahm_invar m"
  by (unfold ahm_invar_def) blast

lemma ahm_invarD: "\<lbrakk> ahm_invar m; m hc = Some cm; k\<in>dom cm \<rbrakk> \<Longrightarrow> hashcode k = hc"
  by (unfold ahm_invar_def) blast

lemma ahm_invarDne: "\<lbrakk> ahm_invar m; m hc = Some cm \<rbrakk> \<Longrightarrow> cm \<noteq> empty"
  by (unfold ahm_invar_def) blast

lemma ahm_invar_bucket_not_empty[simp]: 
  "ahm_invar m \<Longrightarrow> m hc \<noteq> Some Map.empty"
  by (auto dest: ahm_invarDne)

lemmas ahm_lookup_correct = ahm_lookup_def

lemma ahm_empty_correct: 
  "ahm_\<alpha> ahm_empty = empty"
  "ahm_invar ahm_empty"
  apply (rule ext)
  apply (unfold ahm_empty_def) 
  apply (auto simp add: ahm_\<alpha>_def intro: ahm_invarI split: option.split)
  done


lemma ahm_update_correct: 
  "ahm_\<alpha> (ahm_update k v m) = ahm_\<alpha> m (k \<mapsto> v)"
  "ahm_invar m \<Longrightarrow> ahm_invar (ahm_update k v m)"
  apply (rule ext)
  apply (unfold ahm_update_def)
  apply (auto simp add: ahm_\<alpha>_def split: option.split)
  apply (rule ahm_invarI)
  apply (auto dest: ahm_invarD ahm_invarDne split: split_if_asm)
  apply (rule ahm_invarI)
  apply (auto dest: ahm_invarD split: split_if_asm)
  apply (drule (1) ahm_invarD)
  apply auto
  done

lemma fun_upd_apply_ne: "x\<noteq>y \<Longrightarrow> (f(x:=v)) y = f y"
  by simp

lemma cancel_one_empty_simp: "m |` (-{k}) = Map.empty \<longleftrightarrow> dom m \<subseteq> {k}"
proof
  assume "m |` (- {k}) = Map.empty"
  hence "{} = dom (m |` (-{k}))" by auto
  also have "\<dots> = dom m - {k}" by auto
  finally show "dom m \<subseteq> {k}" by blast
next
  assume "dom m \<subseteq> {k}"
  hence "dom m - {k} = {}" by auto
  hence "dom (m |` (-{k})) = {}" by auto
  thus "m |` (-{k}) = Map.empty" by (simp only: dom_empty_simp)
qed
  
lemma ahm_delete_correct: 
  "ahm_\<alpha> (ahm_delete k m) = (ahm_\<alpha> m) |` (-{k})"
  "ahm_invar m \<Longrightarrow> ahm_invar (ahm_delete k m)"
  apply (rule ext)
  apply (unfold ahm_delete_def)
  apply (auto simp add: ahm_\<alpha>_def Let_def Map.restrict_map_def 
              split: option.split)[1]
  apply (drule_tac x=x in fun_cong)
  apply (auto)[1]
  apply (rule ahm_invarI)
  apply (auto split: split_if_asm option.split_asm dest: ahm_invarD)
  apply (drule (1) ahm_invarD)
  apply (auto simp add: restrict_map_def split: split_if_asm option.split_asm)
  done

lemma ahm_isEmpty_correct: "ahm_invar m \<Longrightarrow> ahm_isEmpty m \<longleftrightarrow> ahm_\<alpha> m = Map.empty"
proof
  assume "ahm_invar m" "ahm_isEmpty m"
  thus "ahm_\<alpha> m = Map.empty"
    by (auto simp add: ahm_isEmpty_def ahm_\<alpha>_def intro: ext)
next
  assume I: "ahm_invar m" 
    and E: "ahm_\<alpha> m = Map.empty"

  show "ahm_isEmpty m"
  proof (rule ccontr)
    assume "\<not>ahm_isEmpty m"
    then obtain hc bm where MHC: "m hc = Some bm"
      by (unfold ahm_isEmpty_def)
         (blast elim: nempty_dom dest: domD)
    from ahm_invarDne[OF I, OF MHC] obtain k v where
      BMK: "bm k = Some v"
      by (blast elim: nempty_dom dest: domD)
    from ahm_invarD[OF I, OF MHC] BMK have [simp]: "hashcode k = hc"
      by auto
    hence "ahm_\<alpha> m k = Some v"
      by (simp add: ahm_\<alpha>_def MHC BMK)
    with E show False by simp
  qed
qed

lemmas ahm_correct = ahm_empty_correct ahm_lookup_correct ahm_update_correct 
                     ahm_delete_correct ahm_isEmpty_correct

  -- "Bucket entries correspond to map entries"
lemma ahm_be_is_e:
  assumes I: "ahm_invar m"
  assumes A: "m hc = Some bm" "bm k = Some v"
  shows "ahm_\<alpha> m k = Some v"
  using A
  apply (auto simp add: ahm_\<alpha>_def split: option.split dest: ahm_invarD[OF I])
  apply (frule ahm_invarD[OF I, where k=k])
  apply auto
  done

  -- "Map entries correspond to bucket entries"
lemma ahm_e_is_be: "\<lbrakk>
  ahm_\<alpha> m k = Some v; 
  !!bm. \<lbrakk>m (hashcode k) = Some bm; bm k = Some v \<rbrakk> \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P"
  by (unfold ahm_\<alpha>_def)
     (auto split: option.split_asm)

subsection {* Concrete Hashmap *}
text {*
  In this section, we define the concrete hashmap that is made from the 
  hashcode map and the bucket map.

  We then show the correctness of the operations w.r.t. the abstract hashmap, and
  thus, indirectly, w.r.t. the corresponding map.
*}

types
  ('k,'v) hm_impl = "(hashcode, ('k,'v) lm) rm"

subsubsection "Operations"

  -- "Auxiliary function: Apply function to value of an entry"
definition rm_map_entry 
  :: "hashcode \<Rightarrow> ('v option \<Rightarrow> 'v option) \<Rightarrow> (hashcode, 'v) rm \<Rightarrow> (hashcode,'v) rm" 
  where 
  "rm_map_entry k f m ==
      case rm_lookup k m of
        None \<Rightarrow> (
          case f None of 
            None \<Rightarrow> m |
            Some v \<Rightarrow> rm_update k v m
        ) |
        Some v \<Rightarrow> (
          case f (Some v) of
            None \<Rightarrow> rm_delete k m |
            Some v' \<Rightarrow> rm_update k v' m
        )
    "

  -- "Empty hashmap"
definition empty :: "('k :: hashable, 'v) hm_impl" where "empty == rm_empty"

  -- "Update/insert entry"
definition update :: "'k::hashable \<Rightarrow> 'v \<Rightarrow> ('k,'v) hm_impl \<Rightarrow> ('k,'v) hm_impl"
  where 
  "update k v m == 
   let hc = hashcode k in
     case rm_lookup hc m of
       None \<Rightarrow> rm_update hc (lm_sng k v) m |
       Some bm \<Rightarrow> rm_update hc (lm_update k v bm) m" 

  -- "Lookup value by key"
definition lookup :: "'k::hashable \<Rightarrow> ('k,'v) hm_impl \<Rightarrow> 'v option" where
  "lookup k m ==
   case rm_lookup (hashcode k) m of
     None \<Rightarrow> None |
     Some lm \<Rightarrow> lm_lookup k lm"

  -- "Delete entry by key"
definition delete :: "'k::hashable \<Rightarrow> ('k,'v) hm_impl \<Rightarrow> ('k,'v) hm_impl" where
  "delete k m ==
   rm_map_entry (hashcode k) 
     (\<lambda>v. case v of 
       None \<Rightarrow> None | 
       Some lm \<Rightarrow> (
         let lm' = lm_delete k lm 
         in  if lm_isEmpty lm' then None else Some lm'
       )
     ) m"

  -- "Select arbitrary entry"
definition sel :: "('k::hashable,'v) hm_impl \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> 'r option) \<Rightarrow> 'r option" 
  where "sel m f == rm_sel m (\<lambda>hc lm. lm_sel lm f)"

  -- "Emptiness check"
definition "isEmpty == rm_isEmpty"

  -- "Iterator"
definition "iterate f m \<sigma>0 ==
  rm_iterate (\<lambda>hc lm \<sigma>. 
    lm_iterate f lm \<sigma>
  ) m \<sigma>0
"

  -- "Interruptible iterator"
definition "iteratei c f m \<sigma>0 ==
  rm_iteratei c (\<lambda>hc lm \<sigma>. 
    lm_iteratei c f lm \<sigma>
  ) m \<sigma>0
"

subsubsection "Correctness w.r.t. Abstract HashMap"
text {*
  The following lemmas establish the correctness of the operations w.r.t. the 
  abstract hashmap.

  They have the naming scheme op\_correct', where op is the name of the 
  operation.
*}

  -- "Abstract concrete hashmap to abstract hashmap"
definition hm_\<alpha>' where "hm_\<alpha>' m == \<lambda>hc. case rm_\<alpha> m hc of
  None \<Rightarrow> None |
  Some lm \<Rightarrow> Some (lm_\<alpha> lm)"

  -- "Invariant for concrete hashmap: 
    The hashcode-map and bucket-maps satisfy their invariants and
    the invariant of the corresponding abstract hashmap is satisfied.
  "

definition "invar m == ahm_invar (hm_\<alpha>' m)"


lemma rm_map_entry_correct:
  "rm_\<alpha> (rm_map_entry k f m) = (rm_\<alpha> m)(k := f (rm_\<alpha> m k))"
  apply (auto 
    simp add: rm_map_entry_def rm.delete_correct rm.lookup_correct rm.update_correct
    split: option.split)
  apply (auto simp add: Map.restrict_map_def fun_upd_def intro: ext)
  done


lemma empty_correct': 
  "hm_\<alpha>' empty = ahm_empty"
  "invar empty"
by(simp_all add: hm_\<alpha>'_def empty_def ahm_empty_def rm_correct invar_def ahm_invar_def)

lemma lookup_correct': 
  "invar m \<Longrightarrow> lookup k m = ahm_lookup k (hm_\<alpha>' m)"
  apply (unfold lookup_def invar_def)
  apply (auto split: option.split 
              simp add: ahm_lookup_def ahm_\<alpha>_def hm_\<alpha>'_def 
                        rm_correct lm_correct)
  done

lemma update_correct': 
  "invar m \<Longrightarrow> hm_\<alpha>' (update k v m) = ahm_update k v (hm_\<alpha>' m)"
  "invar m \<Longrightarrow> invar (update k v m)"
proof -
  assume "invar m"
  thus "hm_\<alpha>' (update k v m) = ahm_update k v (hm_\<alpha>' m)"
    apply (unfold invar_def)
    apply (rule ext)
    apply (auto simp add: update_def ahm_update_def hm_\<alpha>'_def Let_def 
                          rm_correct lm_correct 
                split: option.split)
    done
  thus "invar m \<Longrightarrow> invar (update k v m)"
    by (simp add: invar_def ahm_update_correct)
qed

lemma delete_correct':
  "invar m \<Longrightarrow> hm_\<alpha>' (delete k m) = ahm_delete k (hm_\<alpha>' m)"
  "invar m \<Longrightarrow> invar (delete k m)"
proof -
  assume "invar m"
  thus "hm_\<alpha>' (delete k m) = ahm_delete k (hm_\<alpha>' m)"
    apply (unfold invar_def)
    apply (rule ext)
    apply (auto simp add: delete_def ahm_delete_def hm_\<alpha>'_def rm_map_entry_correct
                          rm_correct lm_correct Let_def 
                split: option.split option.split_asm)
    done
  thus "invar (delete k m)" using `invar m`
    by (simp add: ahm_delete_correct invar_def)
qed

lemma isEmpty_correct':
  "invar hm \<Longrightarrow> isEmpty hm \<longleftrightarrow> ahm_\<alpha> (hm_\<alpha>' hm) = Map.empty"
apply (simp add: isEmpty_def rm.isEmpty_correct invar_def
                 ahm_isEmpty_correct[unfolded ahm_isEmpty_def, symmetric])
by (auto simp add: hm_\<alpha>'_def ahm_\<alpha>_def fun_eq_iff split: option.split_asm)

lemma sel_correct':
  assumes "invar hm"
  shows "\<lbrakk> sel hm f = Some r; \<And>u v. \<lbrakk> ahm_\<alpha> (hm_\<alpha>' hm) u = Some v; f u v = Some r \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  and "\<lbrakk> sel hm f = None; ahm_\<alpha> (hm_\<alpha>' hm) u = Some v \<rbrakk> \<Longrightarrow> f u v = None"
proof -
  assume sel: "sel hm f = Some r"
    and P: "\<And>u v. \<lbrakk>ahm_\<alpha> (hm_\<alpha>' hm) u = Some v; f u v = Some r\<rbrakk> \<Longrightarrow> P"
  from `invar hm` have IA: "ahm_invar (hm_\<alpha>' hm)" by(simp add: invar_def)
  from TrueI sel obtain hc lm where "rm_\<alpha> hm hc = Some lm"
    and "lm_sel lm f = Some r"
    unfolding sel_def by(rule rm.sel_someE)
  from TrueI `lm_sel lm f = Some r`
  obtain k v where "lm_\<alpha> lm k = Some v" "f k v = Some r"
    by(rule lm.sel_someE)
  from `rm_\<alpha> hm hc = Some lm` have "hm_\<alpha>' hm hc = Some (lm_\<alpha> lm)"
    by(simp add: hm_\<alpha>'_def)
  with IA have "ahm_\<alpha> (hm_\<alpha>' hm) k = Some v" using `lm_\<alpha> lm k = Some v`
    by(rule ahm_be_is_e)
  thus P using `f k v = Some r` by(rule P)
next
  assume sel: "sel hm f = None" 
    and \<alpha>: "ahm_\<alpha> (hm_\<alpha>' hm) u = Some v"
  from `invar hm` have IA: "ahm_invar (hm_\<alpha>' hm)" by(simp add: invar_def)
  from \<alpha> obtain lm where \<alpha>_u: "hm_\<alpha>' hm (hashcode u) = Some lm"
    and "lm u = Some v" by (rule ahm_e_is_be)
  from \<alpha>_u obtain lmc where "rm_\<alpha> hm (hashcode u) = Some lmc" "lm = lm_\<alpha> lmc" 
    by(auto simp add: hm_\<alpha>'_def split: option.split_asm)
  with `lm u = Some v` have "lm_\<alpha> lmc u = Some v" by simp
  from TrueI sel `rm_\<alpha> hm (hashcode u) = Some lmc`
  have "lm_sel lmc f = None" unfolding sel_def by(rule rm.sel_noneD)
  with TrueI show "f u v = None" using `lm_\<alpha> lmc u = Some v` by(rule lm.sel_noneD)
qed

lemma iterate_correct':
  assumes invar: "invar hm"
  and I: "I (dom (ahm_\<alpha> (hm_\<alpha>' hm))) \<sigma>0"
  and step: "\<And>k v it \<sigma>. \<lbrakk>k \<in> it; ahm_\<alpha> (hm_\<alpha>' hm) k = Some v; it \<subseteq> dom (ahm_\<alpha> (hm_\<alpha>' hm)); I it \<sigma> \<rbrakk> \<Longrightarrow> I (it - {k}) (f k v \<sigma>)"
  shows "I {} (iterate f hm \<sigma>0)"
unfolding iterate_def
proof(rule rm.iterate_rule_P)
  show True ..
next
  have "{k \<in> dom (ahm_\<alpha> (hm_\<alpha>' hm)). hashcode k \<in> dom (rm_\<alpha> hm)} = dom (ahm_\<alpha> (hm_\<alpha>' hm))"
    by (auto simp add: hm_\<alpha>'_def ahm_\<alpha>_def split: option.split_asm)
  thus "I {k\<in>dom (ahm_\<alpha> (hm_\<alpha>' hm)). hashcode k \<in> dom (rm_\<alpha> hm)} \<sigma>0" using I by simp
next
  fix \<sigma>
  assume "I {k \<in> dom (ahm_\<alpha> (hm_\<alpha>' hm)). hashcode k \<in> {}} \<sigma>"
  thus "I {} \<sigma>" by simp
next
  fix hc lm it \<sigma>
  assume "hc \<in> it" "rm_\<alpha> hm hc = Some lm" "it \<subseteq> dom (rm_\<alpha> hm)"
    and I: "I {k \<in> dom (ahm_\<alpha> (hm_\<alpha>' hm)). hashcode k \<in> it} \<sigma>"
  let ?A = "{k\<in>dom (ahm_\<alpha> (hm_\<alpha>' hm)). hashcode k \<in> it - {hc}}"
  let ?B = "\<lambda>it2. {k\<in>dom (ahm_\<alpha> (hm_\<alpha>' hm)). hashcode k = hc \<and> k\<in>it2}"
  let ?I = "\<lambda>it2 \<sigma>. I (?A \<union> ?B it2) \<sigma>"
  from TrueI show "I ?A (lm_iterate f lm \<sigma>)" 
  proof(rule lm.iterate_rule_P)
    have "?A \<union> ?B (dom (lm_\<alpha> lm)) = {k \<in> dom (ahm_\<alpha> (hm_\<alpha>' hm)). hashcode k \<in> it}"
      using `hc \<in> it` `rm_\<alpha> hm hc = Some lm`
      by (auto simp add: hm_\<alpha>'_def ahm_\<alpha>_def split: option.split_asm)
    with I show "?I (dom (lm_\<alpha> lm)) \<sigma>" by simp
  next
    fix \<sigma>
    assume "?I {} \<sigma>" thus "I ?A \<sigma>" by simp
  next
    fix k v it' \<sigma>'
    assume "k \<in> it'" "lm_\<alpha> lm k = Some v" "it' \<subseteq> dom (lm_\<alpha> lm)"
      and "?I it' \<sigma>'"
    hence hc: "hashcode k = hc" using invar `it \<subseteq> dom (rm_\<alpha> hm)` `rm_\<alpha> hm hc = Some lm`
      by(auto simp add: invar_def ahm_invar_def hm_\<alpha>'_def split: option.split_asm)
    hence eq: "?A \<union> ?B (it' - {k}) = ?A \<union> ?B it' - {k}" by auto

    have "k \<in> ?A \<union> ?B it'" "ahm_\<alpha> (hm_\<alpha>' hm) k = Some v"
      using `k \<in> it'` `rm_\<alpha> hm hc = Some lm` `lm_\<alpha> lm k = Some v` hc 
      by(auto simp add: ahm_\<alpha>_def hm_\<alpha>'_def)
    thus "?I (it' - {k}) (f k v \<sigma>')" unfolding eq
      by(rule step[OF _ _ _ `?I it' \<sigma>'`]) auto
  qed
qed

lemma iteratei_correct':
  fixes c f I hm
  defines "I' == \<lambda>it \<sigma>. I {k\<in>dom (ahm_\<alpha> (hm_\<alpha>' hm)). hashcode k \<in> it} \<sigma> \<or> (\<exists>it'\<subseteq>dom (ahm_\<alpha> (hm_\<alpha>' hm)). it'\<noteq>{} \<and> \<not>c \<sigma> \<and> I it' \<sigma>)"
  assumes invar: "invar hm"
  and I: "I (dom (ahm_\<alpha> (hm_\<alpha>' hm))) \<sigma>0"
  and step: "\<And>k v it \<sigma>. \<lbrakk>c \<sigma>; k \<in> it; ahm_\<alpha> (hm_\<alpha>' hm) k = Some v; it \<subseteq> dom (ahm_\<alpha> (hm_\<alpha>' hm)); I it \<sigma>\<rbrakk> \<Longrightarrow> I (it - {k}) (f k v \<sigma>)"
  shows "I {} (iteratei c f hm \<sigma>0) \<or>
        (\<exists>it\<subseteq>dom (ahm_\<alpha> (hm_\<alpha>' hm)). it \<noteq> {} \<and> \<not> c (iteratei c f hm \<sigma>0) \<and> I it (iteratei c f hm \<sigma>0))"
unfolding iteratei_def
proof(rule rm.iteratei_rule_P[where I=I'])
  show True ..
next
  have "{k \<in> dom (ahm_\<alpha> (hm_\<alpha>' hm)). hashcode k \<in> dom (rm_\<alpha> hm)} = dom (ahm_\<alpha> (hm_\<alpha>' hm))"
    by (auto simp add: hm_\<alpha>'_def ahm_\<alpha>_def split: option.split_asm)
  with I show "I' (dom (rm_\<alpha> hm)) \<sigma>0" unfolding I'_def by simp
next
  fix \<sigma>
  assume "I' {} \<sigma>"
  thus "I {} \<sigma> \<or> (\<exists>it. it \<subseteq> dom (ahm_\<alpha> (hm_\<alpha>' hm)) \<and> it \<noteq> {} \<and> \<not> c \<sigma> \<and> I it \<sigma>)"
    by(simp add: I'_def)
next
  fix \<sigma> it
  assume it: "it \<subseteq> dom (rm_\<alpha> hm)" "it \<noteq> {}" "\<not> c \<sigma>" 
    and I': "I' it \<sigma>"
  from I' show "I {} \<sigma> \<or> (\<exists>it. it \<subseteq> dom (ahm_\<alpha> (hm_\<alpha>' hm)) \<and> it \<noteq> {} \<and> \<not> c \<sigma> \<and> I it \<sigma>)"
    unfolding I'_def
  proof
    assume "I {k \<in> dom (ahm_\<alpha> (hm_\<alpha>' hm)). hashcode k \<in> it} \<sigma>"
    thus ?thesis using it
      by(auto intro: exI[where x="{k \<in> dom (ahm_\<alpha> (hm_\<alpha>' hm)). hashcode k \<in> it}"])
  next
    assume "\<exists>it'\<subseteq>dom (ahm_\<alpha> (hm_\<alpha>' hm)). it' \<noteq> {} \<and> \<not> c \<sigma> \<and> I it' \<sigma>"
    thus ?thesis using it by auto
  qed
next
  fix hc lm it \<sigma>
  assume it: "c \<sigma>" "hc \<in> it" "rm_\<alpha> hm hc = Some lm" "it \<subseteq> dom (rm_\<alpha> hm)"
    and I': "I' it \<sigma>"
  let ?A = "{k\<in>dom (ahm_\<alpha> (hm_\<alpha>' hm)). hashcode k \<in> it - {hc}}"
  let ?B = "\<lambda>it2. {k\<in>dom (ahm_\<alpha> (hm_\<alpha>' hm)). hashcode k = hc \<and> k\<in>it2}"
  let ?I' = "\<lambda>it2 \<sigma>. I (?A \<union> ?B it2) \<sigma>"
  from TrueI
  show "I' (it - {hc}) (lm_iteratei c f lm \<sigma>)"
  proof(rule lm.iteratei_rule_P)
    have "?A \<union> ?B (dom (lm_\<alpha> lm)) = {k \<in> dom (ahm_\<alpha> (hm_\<alpha>' hm)). hashcode k \<in> it}"
      using `hc\<in>it` `rm_\<alpha> hm hc = Some lm`
      by (auto simp add: hm_\<alpha>'_def ahm_\<alpha>_def split: option.split_asm)
    thus "?I' (dom (lm_\<alpha> lm)) \<sigma>" using I' it by(simp add: I'_def)
  next
    fix \<sigma>
    assume "?I' {} \<sigma>"
    thus "I' (it - {hc}) \<sigma>" unfolding I'_def by(simp)
  next
    fix \<sigma> it'
    assume it': "it' \<subseteq> dom (lm_\<alpha> lm)" "it' \<noteq> {}" "\<not> c \<sigma>" "?I' it' \<sigma>"

    have 1: "?A \<union> ?B it' \<subseteq> dom (ahm_\<alpha> (hm_\<alpha>' hm))" by auto
    from it' obtain k where KITA: "k\<in>it'" by auto
    with it' obtain v where AUX1: "lm_\<alpha> lm k = Some v" by auto
    from `rm_\<alpha> hm hc = Some lm` have AUX2: "hm_\<alpha>' hm hc = Some (lm_\<alpha> lm)" by (simp add: hm_\<alpha>'_def)
    from ahm_invarD[OF invar[unfolded invar_def], OF AUX2, of k] AUX1
    have [simp]: "hashcode k = hc" by auto
    have "ahm_\<alpha> (hm_\<alpha>' hm) k = Some v"
      by (simp add: ahm_\<alpha>_def AUX1 AUX2)
    with KITA have "k\<in> ?A \<union> ?B it'" by auto
    hence 2: "?A \<union> ?B it' \<noteq> {}" by blast
    from `\<not> c \<sigma>` `?I' it' \<sigma>` 1 2 show "I' (it - {hc}) \<sigma>"
      unfolding I'_def by blast
  next
    fix k v it' \<sigma>
    assume it: "c \<sigma>" "k \<in> it'" "lm_\<alpha> lm k = Some v" "it' \<subseteq> dom (lm_\<alpha> lm)"
      and I: "?I' it' \<sigma>"

    have [simp]: "hashcode k = hc"
      using `lm_\<alpha> lm k = Some v` `hc \<in> it` `rm_\<alpha> hm hc = Some lm` invar
      by(auto simp add: invar_def ahm_invar_def hm_\<alpha>'_def split: option.split_asm)
    hence eq: "?A \<union> ?B (it' - {k}) = ?A \<union> ?B it' - {k}" by auto
    
    from it `rm_\<alpha> hm hc = Some lm`
    have "k \<in> ?A \<union> ?B it'" "ahm_\<alpha> (hm_\<alpha>' hm) k = Some v"
      by(auto simp add: ahm_\<alpha>_def hm_\<alpha>'_def)
    with `c \<sigma>` show "?I' (it' - {k}) (f k v \<sigma>)" unfolding eq
      by(rule step[OF _ _ _ _ I]) auto
  qed
qed  

lemmas hm_correct' = empty_correct' lookup_correct' update_correct' 
                     delete_correct' isEmpty_correct' iterate_correct'
                     sel_correct' iteratei_correct'
lemmas hm_invars = empty_correct'(2) update_correct'(2) 
                   delete_correct'(2)

hide_const (open) empty invar lookup update delete sel isEmpty iterate iteratei

end