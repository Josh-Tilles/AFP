theory InvertibleMaps
imports Category
begin

definition inverse_rel :: "('o, 'm, 'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> bool" ("cinv\<index> _ _" 60) where
  "inverse_rel C f g \<equiv> (f \<approx>>\<^bsub>C\<^esub> g) \<and> (f ;;\<^bsub>C\<^esub> g) = (id\<^bsub>C\<^esub> (dom\<^bsub>C\<^esub> f)) \<and> (g ;;\<^bsub>C\<^esub> f) = (id\<^bsub>C\<^esub> (cod\<^bsub>C\<^esub> f))"

lemma (in Category) inverse_relI:
  assumes "f \<approx>> g"
      and "f ;; g = id (dom f)"
      and "g ;; f = id (cod f)"
  shows "cinv f g"
  unfolding inverse_rel_def using assms by (intro conjI)
(*unfolding inverse_rel_def using assms by simp*)

lemma (in Category) inverse_relE (*[elim]*):
  assumes "cinv f g"
      and "\<lbrakk>f \<approx>> g; f ;; g = id (dom f); g ;; f = id (cod f)\<rbrakk> \<Longrightarrow> P"
  shows P
(*using assms by (simp only: inverse_rel_def)*)
(*using assms unfolding inverse_rel_def by simp*)
  using assms unfolding inverse_rel_def by (elim conjE)

lemmas (in Category) Inverse_relE = inverse_relE
lemmas (in Category) Inverse_relI = inverse_relI

lemma (in Category)
  assumes "cinv f g" and "f maps A to B"
  shows "g maps B to A"
sorry

lemma (in Category)
  assumes "cinv f g"
  shows "dom f = cod g" and "cod f = dom g"
sorry



(* Essentially Exercise II.1.S, right? *)
lemma (in Category) inverse_relSym:
  assumes "cinv f g"
  shows "cinv g f"
proof (rule inverse_relI)
  have "f \<approx>> g" using `cinv f g` by (rule inverse_relE)
  show "g \<approx>> f"
  proof (rule CompDefinedI)
    from `f \<approx>> g` show "g \<in> mor" by (rule CompDefinedE)
    from `f \<approx>> g` show "f \<in> mor" by (rule CompDefinedE)
    have "cod g = cod (f ;; g)" using `f \<approx>> g` by (rule MapsToCod[THEN sym])
    also have "\<dots> = cod (id (dom f))"
    proof -
      have "f;;g = id (dom f)" using `cinv f g` by (rule inverse_relE)
      thus "cod (f;;g) = cod (id (dom f))" by (rule arg_cong)
    qed
    also have "\<dots> = dom f"
    proof (rule CatIdCod)
      from `f \<in> mor` show "dom f \<in> obj" by (rule Cdom)
    qed
    finally show "cod g = dom f" .
  qed
  
  show "g ;; f = id (dom g)"
  proof -
    have "g ;; f = id (cod f)" using `cinv f g` by (rule inverse_relE)
    also have "id (cod f) = id (dom g)"
    proof - (* using `arg_cong` won't work here *)
      from `f \<approx>> g` have "cod f = dom g" by (rule CompDefinedE)
      thus "id (cod f) = id (dom g)" by (rule arg_cong)
    qed
    finally show "g;;f = id (dom g)" .
  qed
  
  from `cinv f g` have "f;;g = id (dom f)" by (rule inverse_relE)
  moreover have "\<dots> = id (cod g)"
  proof -
    from `g \<approx>> f` have "dom f = cod g"
      apply (rule CompDefinedE)
      apply (rule sym)
      apply assumption
      done
    thus "id (dom f) = id (cod g)" by (rule arg_cong)
  qed
  ultimately show "f;;g = id (cod g)" by (rule trans)
qed

(* Exercise II.2 *)
lemma (in Category) InverseUnique:
  assumes "cinv f g" and "cinv f h"
  shows "g = h"
proof -
  have       "g = id (dom g) ;; g" (* Cidl *)
  proof -
    have "g \<in> mor" using `cinv f g`
      apply (rule inverse_relE)
      apply (erule CompDefinedE)
      apply assumption
      done
    hence "id (dom g) ;; g = g" by (rule Cidl)
    thus "g = id (dom g) ;; g" by (rule sym)
  qed
  also have "\<dots> = id (cod f) ;; g"
  proof -
    have "dom g = cod f" using `cinv f g`
      apply (rule inverse_relE)
      apply (erule CompDefinedE)
      apply (rule sym)
      apply assumption
      done
    thus "id (dom g) ;; g = id (cod f) ;; g" by (rule arg_cong)
  qed
  also have "\<dots> = (h ;; f) ;; g" sorry
  also have "\<dots> = h ;; (f ;; g)" apply (rule Cassoc) sorry
  also have "\<dots> = h ;; (id (dom f))" sorry
  also have "\<dots> = h ;; (id (cod h))" sorry
  also have "\<dots> = h" (* Cidr *) sorry
  finally show "g = h" .
qed

(*
definition (in Category) "inverse_rel f g \<longleftrightarrow> (f \<approx>> g) \<and> f;;g = id (dom f) \<and> g;;f = id (cod f)"
notation ...
*)

definition isomorphism :: "('o, 'm, 'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> bool" ("ciso\<index> _" [70]) where
  "isomorphism C f \<equiv> \<exists>g. inverse_rel C f g"

lemma (in Category) Article_II__Exercise_3_a:
  assumes "ciso f"
  shows "(h ;; f = k ;; f) \<longrightarrow> h = k"
oops

(* author refers to it as a "cancellation law" *)
lemma (in Category) Article_II__Exercise_3_a:
  assumes "ciso f"
(*  fixes h k *)
  assumes "h ;; f = k ;; f"
  shows "h = k"
proof -
  have "h = h ;; id (dom h)" sorry
  also have "\<dots> = h ;; (f ;; (Cinv f))" sorry
  also have "\<dots> = (h ;; f) ;; (Cinv f)" sorry
  also have "\<dots> = (k ;; f) ;; (Cinv f)" sorry
  also have "\<dots> = k ;; (f ;; (Cinv f))" sorry
  also have "\<dots> = k ;; (id (dom k))" sorry
  also have "\<dots> = k" sorry
  finally show "h = k" .
  oops (* maybe I'll follow the paper a bit more first *)

(* Exercise *)
theorem (in Category) InvId:
  assumes "X \<in> obj"
  shows "cinv (id X) (id X)"
proof (rule inverse_relI)
  from assms show "id X \<approx>> id X" by (rule MapsToId)
next
  have "dom (id X) = X" using `X \<in> obj` by (rule CatIdDom)
  hence "id (dom (id X)) = id X" by (rule arg_cong)
  hence "id (dom (id X)) = id X ;; id X"
  proof -
    from `X \<in> obj` have "id X ;; id X = id X" by (rule CatIdCompId)
    with `id (dom (id X)) = id X` show ?thesis by (rule trans_sym)
  qed
  thus "id X ;; id X = id (dom (id X))" by (rule sym)
next
  have "id X ;; id X = id X" using `X \<in> obj` by (rule CatIdCompId)
  also have "\<dots> = id (cod (id X))"
  proof -
    have "cod (id X) = X" using `X \<in> obj` by (rule CatIdCod)
    hence "id (cod (id X)) = id X" by (rule arg_cong)
    thus "id X = id (cod (id X))" by (rule sym)
  qed
  finally show "id X ;; id X = id (cod (id X))" .
qed

lemma (in Category) AltInverse_relI:
  assumes "f maps A to B" and "g maps B to A"
  assumes "f ;; g = id A" and "g ;; f = id B"
  shows "cinv f g"
sorry

theorem (in Category) InvId:
  assumes "X \<in> obj"
  shows "cinv (id X) (id X)"
proof (rule inverse_relI)
proof (rule IsoI[where ?g="id X"])
  have "id X = id (cod (id X))"
    apply (subst CatIdCod)
    using assms apply assumption
    apply (rule refl)
    done
  have "id X = id (dom (id X))"
    apply (subst CatIdDom) 
    using assms apply assumption
    apply (rule refl)
    done
  have "id (dom (id X)) ;; id X = id X"
  proof (rule Cidl)
    from `X \<in> obj` have "(id X) maps X to X" by (rule Cidm)
    thus "id X \<in> mor" by (rule MapsToE)
  qed
  hence iii: "id X ;; id X = id X" by (subst `id X = id (dom (id X))`)
  thus "id X ;; id X = id (dom (id X))"
    apply (subst sym[OF `id X = id (dom (id X))`])
    apply assumption
    done
  from iii show "id X ;; id X = id (cod (id X))"
    apply (subst sym[OF `id X = id (cod (id X))`])
    apply assumption
    done
qed
  
