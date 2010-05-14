(*
 * The worker/wrapper transformation, following Gill and Hutton.
 * (C)opyright 2009, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

(*<*)
theory WorkerWrapperNew
imports HOLCF LFPFusion WorkerWrapper
begin
(*>*)

section{* A totally-correct fusion rule *}
text{*
\label{sec:ww-fixed}

Taking inspiration from the counterexample of
\S\ref{sec:unwrap-strict}, we can show that if @{term "unwrap"} is
strict then fusion is totally correct. *}

lemma
  fixes w :: "'b \<rightarrow> 'a"
  fixes u :: "'a \<rightarrow> 'b"
  assumes us: "u\<cdot>\<bottom> = \<bottom>"
      and ww: "w oo u = ID"
      and wb: "u oo b oo w = b' oo u oo w"
  shows "fix\<cdot>(u oo b oo w) = fix\<cdot>(b')"
proof -
  let ?P = "\<lambda>xy. fst xy = snd xy \<and> u\<cdot>(w\<cdot>(fst xy)) = fst xy"
  let ?F = "\<Lambda> xy. ((u oo b oo w)\<cdot>(fst xy), b'\<cdot>(snd xy))"
  have "?P (fix\<cdot>?F)"
  proof(induct rule: fix_ind)
    case 2 with retraction_strict us ww show ?case
      by (bestsimp simp add: expand_cfun_eq)
  next
    case (3 xy) thus ?case
      using ww
      apply (simp add: expand_cfun_eq)
      using wb
      apply (bestsimp simp add: expand_cfun_eq)
      done
  qed simp
  thus ?thesis
    using fix_cprod[where F="?F"]
    by (simp add: cfcomp1 eta_cfun)
qed

text{* The second version is a generalisation: not all recursive calls
have to be fusable. *}

lemma worker_wrapper_fusion_new:
  fixes w :: "'b \<rightarrow> 'a"
  fixes u :: "'a \<rightarrow> 'b"
  assumes us: "u\<cdot>\<bottom> = \<bottom>"
      and ww: "w oo u = ID"
      and wb: "u oo b oo w = (\<Lambda> r. b'\<cdot>r\<cdot>(u\<cdot>(w\<cdot>r)))"
  shows "fix\<cdot>(u oo b oo w) = (\<mu> r. b'\<cdot>r\<cdot>r)"
proof -
  let ?P = "\<lambda>xy. fst xy = snd xy \<and> u\<cdot>(w\<cdot>(fst xy)) = fst xy"
  let ?F = "\<Lambda> xy. ((u oo b oo w)\<cdot>(fst xy), b'\<cdot>(snd xy)\<cdot>(snd xy))"
  have "?P (fix\<cdot>?F)"
  proof(induct rule: fix_ind)
    case 2 with retraction_strict us ww show ?case
      by (bestsimp simp add: expand_cfun_eq)
  next
    case 3 thus ?case
      using ww
      apply (simp add: expand_cfun_eq)
      using wb
      apply (bestsimp simp add: expand_cfun_eq)
      done
  qed simp
  thus ?thesis
    using fix_cprod[where F="?F"]
    by (simp add: cfcomp1)
qed

text{* One might hope to show this result using @{text
"lfp_fusion"}. The best I have managed to do is to show that fusion
works in the context of the worker generated by @{text
"worker_wrapper_id"}. In other words, I have shown that a rule where
the worker/wrapper transformation and fusion are combined is sound. *}

lemma worker_wrapper_new:
  fixes F :: "'b \<rightarrow> 'b"
  assumes wu: "wrap oo unwrap = (ID :: 'a \<rightarrow> 'a)"
      and abs: "unwrap\<cdot>\<bottom> = \<bottom>"
      and Fb: "F oo (unwrap oo wrap) = unwrap oo G oo wrap"
  shows "fix\<cdot>G = wrap\<cdot>(fix\<cdot>F)"
proof -
  from Fb have "(F oo unwrap oo (wrap oo unwrap)) = unwrap oo G oo (wrap oo unwrap)"
    by (simp add: assoc_oo)
  with wu have "F oo unwrap = unwrap oo G" by simp
  with abs have "unwrap\<cdot>(fix\<cdot>G) = fix\<cdot>F"
    by - (rule lfp_fusion, simp)
  hence "(wrap oo unwrap)\<cdot>(fix\<cdot>G) = wrap\<cdot>(fix\<cdot>F)" by simp
  with wu show ?thesis by simp
qed

text{* As above, this is readily generalised to handle fusion or not
at each recursive call. The proof is a more involved application of
@{text "lfp_fusion"}. Note that $\mu\_.\_$ is the least-fixed-point
operator. *}

lemma worker_wrapper_general:
  fixes F :: "'b \<rightarrow> 'b \<rightarrow> 'b"
  assumes ww: "wrap oo unwrap = (ID :: 'a \<rightarrow> 'a)"
      and unwraps: "unwrap\<cdot>\<bottom> = \<bottom>"
      and Fb: "(\<Lambda> r. F\<cdot>r\<cdot>((unwrap oo wrap)\<cdot>r)) = unwrap oo G oo wrap"
  shows "fix\<cdot>G = wrap\<cdot>(\<mu> r. F\<cdot>r\<cdot>r)"
proof -
  from Fb have "(\<Lambda> r. F\<cdot>r\<cdot>((unwrap oo wrap)\<cdot>r)) oo unwrap = unwrap oo G oo (wrap oo unwrap)"
    by (simp add: assoc_oo)
  hence "(\<Lambda> r. F\<cdot>(unwrap\<cdot>r)\<cdot>((unwrap oo (wrap oo unwrap))\<cdot>r)) = unwrap oo G oo (wrap oo unwrap)"
    by (simp add: cfcomp1)
  with ww have "(\<Lambda> r. F\<cdot>(unwrap\<cdot>r)\<cdot>(unwrap\<cdot>r)) = unwrap oo G" by simp
  hence "(\<Lambda> r. F\<cdot>r\<cdot>r) oo unwrap = unwrap oo G" by (simp add: cfcomp1)
  with unwraps have "unwrap\<cdot>(fix\<cdot>G) = (\<mu> r. F\<cdot>r\<cdot>r)"
    by - (rule lfp_fusion, simp)
  hence "(wrap oo unwrap)\<cdot>(fix\<cdot>G) = wrap\<cdot>(\<mu> r. F\<cdot>r\<cdot>r)" by simp
  with ww show ?thesis by simp
qed

text{* The following sections are mechanisations of the examples by
\citet{GillHutton:2009}. *}

(*<*)
end
(*>*)
