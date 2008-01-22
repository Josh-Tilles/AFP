(*  ID:         $Id: QEpres.thy,v 1.3 2008-01-14 11:34:42 nipkow Exp $
    Author:     Tobias Nipkow, 2007
*)

theory QEpres
imports PresArith
begin

subsection{*DNF-based quantifier elimination*}

fun hd_coeff1 :: "int \<Rightarrow> atom \<Rightarrow> atom" where
"hd_coeff1 m (Le i (k#ks)) =
   (let m' = m div (abs k) in Le (m'*i) (sgn k # (m' *\<^sub>s ks)))" |
"hd_coeff1 m (Dvd d i (k#ks)) =
   (let m' = m div k in Dvd (m'*d) (m'*i) (1 # (m' *\<^sub>s ks)))" |
"hd_coeff1 m (NDvd d i (k#ks)) =
   (let m' = m div k in NDvd (m'*d) (m'*i) (1 # (m' *\<^sub>s ks)))"

(* all hd-coeffs are nonzero! *)
definition
"hd_coeffs1 as =
 (let m = zlcms(map hd_coeff as)
  in Dvd m 0 [1] # map (hd_coeff1 m) as)"

lemma I_hd_coeff1_mult: assumes "m>0"
shows "\<lbrakk> hd_coeff a \<noteq> 0; hd_coeff a dvd m \<rbrakk> \<Longrightarrow>
 I\<^isub>Z (hd_coeff1 m a) (m*x#e) = I\<^isub>Z a (x#e)"
proof(induct a)
  case (Le i ks)
  then obtain k js where [simp]: "ks = k#js" by(auto simp: split:list.splits)
  let ?d = "m div \<bar>k\<bar>"
  from Le have "\<bar>k\<bar> dvd m" by(simp add: IntDiv.zdvd_abs1)
  hence "?d > 0" using pos_imp_zdiv_pos_iff Le `m>0` by(simp add:zdvd_imp_le)
  have 1: "k*(x*?d) = sgn k * x * m"
  proof -
    have "k*(x*?d) = (sgn k * abs k) * (x * ?d)" by(simp only: mult_sgn_abs)
    also have "\<dots> = sgn k * x * (abs k * ?d)" by simp
    also have "\<dots> = sgn k * x * m" using zdvd_mult_div_cancel[OF `\<bar>k\<bar> dvd m`]
      by(simp add:ring_simps)
    finally show ?thesis .
  qed
  have "I\<^isub>Z (hd_coeff1 m (Le i ks)) (m*x#e) \<longleftrightarrow>
       (i*?d \<le> sgn k * m*x + ?d * \<langle>js,e\<rangle>)"
    by(simp add: ring_simps iprod_assoc)
  also have "\<dots> \<longleftrightarrow> ?d*i \<le> ?d * (k*x + \<langle>js,e\<rangle>)" using 1
    by(simp (no_asm_simp) add:ring_simps)
  also have "\<dots> \<longleftrightarrow> i \<le> k*x + \<langle>js,e\<rangle>" using `?d>0`
    by(simp add: mult_compare_simps)
  finally show ?case by(simp)
next
  case (Dvd d i ks)
  then obtain k js where [simp]: "ks = k#js" by(auto split:list.splits)
  let ?m' = "m div k"
  from Dvd have "k dvd m" by simp
  hence "?m' \<noteq> 0" using zdiv_eq_0_iff Dvd `m>0`
    by(simp add:linorder_not_less zdvd_imp_le)
  have 1: "k*(x*?m') = x * m"
  proof -
    have "k*(x*?m') = x*(k*?m')" by(simp add:ring_simps)
    also have "\<dots> = x*m" using zdvd_mult_div_cancel[OF `k dvd m`]
      by(simp add:ring_simps)
    finally show ?thesis .
  qed
  have "I\<^isub>Z (hd_coeff1 m (Dvd d i ks)) (m*x#e) \<longleftrightarrow>
       (?m'*d dvd ?m'*i + m*x + ?m' * \<langle>js,e\<rangle>)"
    by(simp add: ring_simps iprod_assoc)
  also have "\<dots> \<longleftrightarrow> ?m'*d dvd ?m' * (i + k*x + \<langle>js,e\<rangle>)" using 1
    by(simp (no_asm_simp) add:ring_simps)
  also have "\<dots> \<longleftrightarrow> d dvd i + k*x + \<langle>js,e\<rangle>" using `?m'\<noteq>0` by(simp)
  finally show ?case by(simp add:ring_simps)
next
  case (NDvd d i ks)
  then obtain k js where [simp]: "ks = k#js" by(auto split:list.splits)
  let ?m' = "m div k"
  from NDvd have "k dvd m" by simp
  hence "?m' \<noteq> 0" using zdiv_eq_0_iff NDvd `m>0`
    by(simp add:linorder_not_less zdvd_imp_le)
  have 1: "k*(x*?m') = x * m"
  proof -
    have "k*(x*?m') = x*(k*?m')" by(simp add:ring_simps)
    also have "\<dots> = x*m" using zdvd_mult_div_cancel[OF `k dvd m`]
      by(simp add:ring_simps)
    finally show ?thesis .
  qed
  have "I\<^isub>Z (hd_coeff1 m (NDvd d i ks)) (m*x#e) \<longleftrightarrow>
       \<not>(?m'*d dvd ?m'*i + m*x + ?m' * \<langle>js,e\<rangle>)"
    by(simp add: ring_simps iprod_assoc)
  also have "\<dots> \<longleftrightarrow> \<not> ?m'*d dvd ?m' * (i + k*x + \<langle>js,e\<rangle>)" using 1
    by(simp (no_asm_simp) add:ring_simps)
  also have "\<dots> \<longleftrightarrow> \<not> d dvd i + k*x + \<langle>js,e\<rangle>" using `?m'\<noteq>0` by(simp)
  finally show ?case by(simp add:ring_simps)
qed

lemma I_hd_coeffs1:
assumes 0: "\<forall>a\<in>set as. hd_coeff a \<noteq> 0" shows
  "(\<exists>x. \<forall>a \<in> set(hd_coeffs1 as). I\<^isub>Z a (x#e)) =
   (\<exists>x. \<forall>a \<in> set as. I\<^isub>Z a (x#e))" (is "?B = ?A")
proof -
  let ?m = "zlcms(map hd_coeff as)"
  have "?m>0" using 0 by(simp add:zlcms_pos)
  have "?A = (\<exists>x. \<forall>a \<in> set as. I\<^isub>Z (hd_coeff1 ?m a) (?m*x#e))"
    by (simp add:I_hd_coeff1_mult[OF `?m>0`] dvd_zlcms 0)
  also have "\<dots> = (\<exists>x. ?m dvd x+0 \<and> (\<forall>a \<in> set as. I\<^isub>Z (hd_coeff1 ?m a) (x#e)))"
    by(rule unity_coeff_ex[THEN meta_eq_to_obj_eq])
  finally show ?thesis by(simp add:hd_coeffs1_def)
qed


abbreviation "is_dvd a \<equiv> case a of Le _ _ \<Rightarrow> False | _ \<Rightarrow> True"

definition
"qe_pres as =
 (let ds = filter is_dvd as; (d::int) = zlcms(map divisor ds); ls = lbounds as
  in if ls = []
     then Disj [0..d - 1] (\<lambda>n. list_conj(map (Atom \<circ> asubst n []) ds))
     else
     Disj ls (\<lambda>(li,lks).
       Disj [0..d - 1] (\<lambda>n.
         list_conj(map (Atom \<circ> asubst (li + n) (-lks)) as))))"
text{* \noindent Note the optimization in the case @{prop"ls = []"}: only the
divisibility atoms are tested, not the inequalities. This complicates
the proof. *}

lemma I_cyclic:
assumes "is_dvd a" and "hd_coeff a = 1" and "i mod divisor a = j mod divisor a"
shows "I\<^isub>Z a (i#e) = I\<^isub>Z a (j#e)"
proof (cases a)
  case (Dvd d l ks)
  with `hd_coeff a = 1` obtain ks' where [simp]: "ks = 1#ks'"
    by(simp split:list.splits)
  have "(l + (i + \<langle>ks',e\<rangle>)) mod d = (l + (j + \<langle>ks',e\<rangle>)) mod d" (is "?l=?r")
  proof -
    have "?l = (l mod d + (i + \<langle>ks',e\<rangle>) mod d) mod d"
      by(rule zmod_zadd1_eq)
    also have "(i + \<langle>ks',e\<rangle>) mod d = (i mod d + \<langle>ks',e\<rangle> mod d) mod d"
      by(rule zmod_zadd1_eq)
    also have "i mod d = j mod d"
      using `i mod divisor a = j mod divisor a` Dvd by simp
    also have "(j mod d + \<langle>ks',e\<rangle> mod d) mod d = (j + \<langle>ks',e\<rangle>) mod d"
      by(rule zmod_zadd1_eq[symmetric])
    also have "(l mod d + (j + \<langle>ks',e\<rangle>) mod d) mod d = ?r"
      by(rule zmod_zadd1_eq[symmetric])
    finally show ?thesis .
  qed               
  thus ?thesis using Dvd by (simp add:zdvd_iff_zmod_eq_0)
next
  case (NDvd d l ks)
  with `hd_coeff a = 1` obtain ks' where [simp]: "ks = 1#ks'"
    by(simp split:list.splits)
  have "(l + (i + \<langle>ks',e\<rangle>)) mod d = (l + (j + \<langle>ks',e\<rangle>)) mod d" (is "?l=?r")
  proof -
    have "?l = (l mod d + (i + \<langle>ks',e\<rangle>) mod d) mod d"
      by(rule zmod_zadd1_eq)
    also have "(i + \<langle>ks',e\<rangle>) mod d = (i mod d + \<langle>ks',e\<rangle> mod d) mod d"
      by(rule zmod_zadd1_eq)
    also have "i mod d = j mod d"
      using `i mod divisor a = j mod divisor a` NDvd by simp
    also have "(j mod d + \<langle>ks',e\<rangle> mod d) mod d = (j + \<langle>ks',e\<rangle>) mod d"
      by(rule zmod_zadd1_eq[symmetric])
    also have "(l mod d + (j + \<langle>ks',e\<rangle>) mod d) mod d = ?r"
      by(rule zmod_zadd1_eq[symmetric])
    finally show ?thesis .
  qed
  thus ?thesis using NDvd by (simp add:zdvd_iff_zmod_eq_0)
next
  case Le thus ?thesis using `is_dvd a` by simp
qed

lemma I_qe_pres:
assumes norm: "\<forall>a \<in> set as. divisor a \<noteq> 0"
and hd: "\<forall>a \<in> set as. hd_coeff_is1 a"
shows "Z.I (qe_pres as) xs = (\<exists>x. \<forall>a\<in> set as. I\<^isub>Z a (x#xs))"
proof -
  let ?lbs = "lbounds as"
  let ?ds = "filter is_dvd as"
  let ?lcm = "zlcms(map divisor ?ds)"
  let ?Ds = "{a \<in> set as. is_dvd a}"
  let ?Us = "{a \<in> set as. case a of Le _ (k#_) \<Rightarrow> k < 0 | _ \<Rightarrow> False}"
  let ?Ls = "{a \<in> set as. case a of Le _ (k#_) \<Rightarrow> k > 0 | _ \<Rightarrow> False}"
  have as: "set as = ?Ds \<union> ?Ls \<union> ?Us" (is "_ = ?S")
  proof -
    { fix x assume "x \<in> set as"
      hence "x \<in> ?S" using hd by (cases x)(auto split:list.splits) }
    moreover
    { fix x assume "x \<in> ?S"
      hence "x \<in> set as" by auto }
    ultimately show ?thesis by blast
  qed
  have 1: "\<forall>a \<in> ?Ds. hd_coeff a = 1" using hd by(fastsimp split:atom.splits)
  show ?thesis  (is "?QE = (\<exists>x. ?P x)")
  proof
    assume "?QE"
    { assume "?lbs = []"
      with `?QE` obtain n where "n < ?lcm" and
	A: "\<forall>a \<in> ?Ds. I\<^isub>Z a (n#xs)" using 1
	by(auto simp:IZ_asubst qe_pres_def)
      have "?Ls = {}" using `?lbs = []` set_lbounds[of as]
	by (auto simp add:filter_empty_conv split:atom.split list.split)
      have "\<exists>x. ?P x"
      proof cases
	assume "?Us = {}"
	with `?Ls = {}` have "set as = ?Ds" using as by(simp (no_asm_use))blast
	hence "?P n" using A by auto
	thus ?thesis ..
      next
	assume "?Us \<noteq> {}"
	let ?M = "{\<langle>tl ks, xs\<rangle> - i|ks i. Le i ks \<in> ?Us}" let ?m = "Min ?M"
	have "finite ?M"
	proof -
	  have "finite ( (\<lambda>Le i ks \<Rightarrow> \<langle>tl ks, xs\<rangle> - i) `
                         {a\<in>set as. \<exists>i k ks. k<0 \<and> a = Le i (k#ks)} )"
	    (is "finite ?B")
	    by simp
	  also have "?B = ?M" using hd
	    by(fastsimp simp:image_def neq_Nil_conv split:atom.splits list.splits)
          finally show ?thesis by auto
	qed
	have "?M \<noteq> {}"
	proof -
	  from `?Us \<noteq> {}` obtain i k ks where "Le i (k#ks) \<in> ?Us \<and> k<0"
	    by (fastsimp split:atom.splits list.splits)
	  thus ?thesis by auto
	qed
	let ?k = "(n - ?m) div ?lcm + 1" let ?x = "n - ?k * ?lcm"
	have "\<forall>a \<in> ?Ds. I\<^isub>Z a (?x # xs)"
	proof (intro allI ballI)
	  fix a assume "a \<in> ?Ds"
	  let ?d = "divisor a"
	  have 2: "?d dvd ?lcm" using `a \<in> ?Ds` by(simp add:dvd_zlcms)
	  have "?x mod ?d = n mod ?d" (is "?l = ?r")
	  proof -
	    have "?l = (?r - ((?k * ?lcm) mod ?d)) mod ?d"
	      by(rule zmod_zdiff1_eq)
	    also have "(?k * ?lcm) mod ?d = 0"
	      by(simp add: zdvd_iff_zmod_eq_0[symmetric] zdvd_zmult[OF 2])
	    finally show ?thesis by simp
	  qed
	  thus "I\<^isub>Z a (?x#xs)" using A I_cyclic[of a n ?x] `a \<in> ?Ds` 1 by auto
	qed
	moreover
	have "\<forall>a\<in> ?Us. I\<^isub>Z a (?x#xs)"
	proof
	  fix a assume "a \<in> ?Us"
	  then obtain l ks where [simp]: "a = Le l (-1#ks)" using hd
	    by(fastsimp split:atom.splits list.splits)
	  have "?m \<le> \<langle>ks,xs\<rangle> - l"
	    using Min_le_iff[OF `finite ?M` `?M \<noteq> {}`] `a \<in> ?Us` by fastsimp
	  moreover have "(n - ?m) mod ?lcm < ?lcm"
	    by(simp add: pos_mod_bound[OF zlcms_pos] norm)
	  ultimately show "I\<^isub>Z a (?x#xs)"
	    by(simp add:zmult_div_cancel ring_simps)
	qed
	moreover
	have "set as = ?Ds \<union> ?Us" using as `?Ls = {}`
	  by (simp (no_asm_use)) blast
	ultimately have "?P(?x)" by auto
	thus ?thesis ..
      qed }
    moreover
    { assume "?lbs \<noteq> []"
      with `?QE` obtain il ksl m
	where "\<forall>a\<in>set as. I\<^isub>Z (asubst (il + m) ksl a) xs"
	by(auto simp:qe_pres_def)
      hence "?P(il + m + \<langle>ksl,xs\<rangle>)" by(simp add:IZ_asubst)
      hence "\<exists>x. ?P x" .. }
    ultimately show "\<exists>x. ?P x" by blast
  next
    assume "\<exists>x. ?P x" then obtain x where x: "?P x" ..
    show ?QE
    proof cases
      assume "?lbs = []"
      moreover
      have "\<exists>x. 0 \<le> x \<and> x < ?lcm \<and> (\<forall>a \<in> ?Ds. I\<^isub>Z a (x # xs))"
	(is "\<exists>x. ?P x")
      proof
	{ fix a assume "a \<in> ?Ds"
	  hence "I\<^isub>Z a ((x mod ?lcm) # xs) = I\<^isub>Z a (x # xs)" using 1
	    by (fastsimp del:iffI intro: I_cyclic
	        simp: zmod_zmod_cancel dvd_zlcms) }
	thus "?P(x mod ?lcm)" using x norm by(simp add: zlcms_pos)
      qed
      ultimately show ?thesis by (auto simp:qe_pres_def IZ_asubst)
    next
      assume "?lbs \<noteq> []"
      let ?L = "{i - \<langle>ks,xs\<rangle> |ks i. (i,ks) \<in> set(lbounds as)}"
      let ?lm = "Max ?L"
      let ?n = "(x - ?lm) mod ?lcm"
      have "finite ?L"
      proof -
	have "finite((\<lambda>(i,ks). i-\<langle>ks,xs\<rangle>) ` set(lbounds as) )" (is "finite ?B")
	  by simp
	also have "?B = ?L" by auto
	finally show ?thesis by auto
      qed
      moreover have "?L \<noteq> {}" using `?lbs \<noteq> []`
	by(fastsimp simp:neq_Nil_conv)
      ultimately have "?lm \<in> ?L" by(rule Max_in)
      then obtain li lks where "(li,lks)\<in> set ?lbs" and lm: "?lm = li-\<langle>lks,xs\<rangle>"
	by blast
      moreover
      have n: "0 \<le> ?n \<and> ?n < ?lcm" using norm by(simp add:zlcms_pos)
      moreover
      { fix a assume "a \<in> set as"
	with x have "I\<^isub>Z a (x # xs)" by blast
	have "I\<^isub>Z a ((li + ?n - \<langle>lks,xs\<rangle>) # xs)"
	proof -
	  { assume "a \<in> ?Ls"
	    then obtain i ks where [simp]: "a = Le i (1#ks)" using hd
	      by(fastsimp split:atom.splits list.splits)
	    from `a \<in> ?Ls` have "i-\<langle>ks,xs\<rangle> \<in> ?L" by(fastsimp simp:set_lbounds)
	    hence "i-\<langle>ks,xs\<rangle> \<le> li - \<langle>lks,xs\<rangle>"
	      using lm[symmetric] `finite ?L` `?L \<noteq> {}` by auto
	    hence ?thesis using n by simp arith }
	  moreover
	  { assume "a \<in> ?Us"
	    then obtain i ks where [simp]: "a = Le i (-1#ks)" using hd
	      by(fastsimp split:atom.splits list.splits)
	    have "Le li (1#lks) \<in> set as" using `(li,lks) \<in> set ?lbs` hd
	      by(auto simp:set_lbounds)
	    hence "li - \<langle>lks,xs\<rangle> \<le> x" using x by auto
            moreover hence "(x - ?lm) mod ?lcm \<le> x - ?lm"
	      using lm by(simp add: zmod_le_nonneg_dividend)
	    ultimately
	    have ?thesis using `I\<^isub>Z a (x # xs)` lm by auto }
	  moreover
	  { assume "a \<in> ?Ds"
	    have ?thesis
	    proof(rule I_cyclic[THEN iffD2, OF _ _ _ `I\<^isub>Z a (x # xs)`])
	      show "is_dvd a" using `a \<in> ?Ds` by simp
	      show "hd_coeff a = 1" using `a \<in> ?Ds` hd
		by(fastsimp split:atom.splits list.splits)
	      have "li + (x-?lm) mod ?lcm - \<langle>lks,xs\<rangle> = ?lm + (x-?lm) mod ?lcm"
		using lm by arith
	      hence "(li + (x-?lm) mod ?lcm - \<langle>lks,xs\<rangle>) mod divisor a =
		     (?lm + (x-?lm) mod ?lcm) mod divisor a" by (simp only:)
	      also have "\<dots> =
	(?lm mod divisor a + (x-?lm) mod ?lcm mod divisor a) mod divisor a"
		by(rule zmod_zadd1_eq)
	      also have
	"\<dots> = (?lm mod divisor a + (x-?lm) mod divisor a) mod divisor a"
		using `is_dvd a` `a\<in> set as`
		by(simp add: zmod_zmod_cancel dvd_zlcms)
	      also have "\<dots> = (?lm + (x-?lm)) mod divisor a"
		by(rule zmod_zadd1_eq[symmetric])
	      also have "\<dots> = x mod divisor a" by simp
	      finally
	      show "(li + ?n - \<langle>lks,xs\<rangle>) mod divisor a = x mod divisor a"
		using norm by(auto simp:pos_mod_sign zlcms_pos)
	    qed }
	  ultimately show ?thesis using `a \<in> set as` as by blast
	qed
      }
      ultimately show ?thesis using `?lbs \<noteq> []`
	by (simp (no_asm_simp) add:qe_pres_def IZ_asubst split_def)
           (force simp del:int_nat_eq)
    qed
  qed
qed

lemma  divisors_hd_coeffs1:
assumes div0: "\<forall>a\<in>set as. divisor a \<noteq> 0" and hd0: "\<forall>a\<in>set as. hd_coeff a \<noteq> 0"
and a: "a\<in>set (hd_coeffs1 as)" shows "divisor a \<noteq> 0"
proof -
  let ?m = "zlcms(map hd_coeff as)"
  from a have "a = Dvd ?m 0 [1] \<or> (\<exists>b \<in> set as. a = hd_coeff1 ?m b)"
    (is "?A \<or> ?B")
    by(auto simp:hd_coeffs1_def)
  thus ?thesis
  proof
    assume ?A thus ?thesis using hd0 by(auto)
  next
    assume ?B
    then obtain b where "b \<in> set as" and [simp]: "a = hd_coeff1 ?m b" ..
    hence b: "hd_coeff b \<noteq> 0" "divisor b \<noteq> 0" using div0 hd0 by auto
    show ?thesis
    proof (cases b)
      case (Le i ks) thus ?thesis using b by(auto split:list.splits)
    next
      case (Dvd d i ks)[simp]
      then obtain k ks' where [simp]: "ks = k#ks'" using b
	by(auto split:list.splits)
      have k: "k \<in> set(map hd_coeff as)" using `b \<in> set as` by force
      have "zlcms (map hd_coeff as) div k \<noteq> 0"
	using b hd0 dvd_zlcms[OF k]
	by(auto simp add:dvd_def)
      thus ?thesis using b by (simp)
    next
      case (NDvd d i ks)[simp]
      then obtain k ks' where [simp]: "ks = k#ks'" using b
	by(auto split:list.splits)
      have k: "k \<in> set(map hd_coeff as)" using `b \<in> set as` by force
      have "zlcms (map hd_coeff as) div k \<noteq> 0"
	using b hd0 dvd_zlcms[OF k]
	by(auto simp add:dvd_def)
      thus ?thesis using b by (simp)
    qed
  qed
qed

lemma hd_coeff_is1_hd_coeffs1:
assumes hd0: "\<forall>a\<in>set as. hd_coeff a \<noteq> 0"
and a: "a\<in>set (hd_coeffs1 as)" shows "hd_coeff_is1 a"
proof -
  let ?m = "zlcms(map hd_coeff as)"
  from a have "a = Dvd ?m 0 [1] \<or> (\<exists>b \<in> set as. a = hd_coeff1 ?m b)"
    (is "?A \<or> ?B")
    by(auto simp:hd_coeffs1_def)
  thus ?thesis
  proof
    assume ?A thus ?thesis using hd0 by simp
  next
    assume ?B
    then obtain b where "b \<in> set as" and [simp]: "a = hd_coeff1 ?m b" ..
    hence b: "hd_coeff b \<noteq> 0" using hd0 by auto
    show ?thesis using b
      by (cases b) (auto simp: sgn_if split:list.splits)
  qed
qed


lemma I_qe_pres_o:
 "\<lbrakk> \<forall>a \<in> set as. divisor a \<noteq> 0; \<forall>a\<in>set as. hd_coeff a \<noteq> 0 \<rbrakk> \<Longrightarrow>
  Z.I ((qe_pres \<circ> hd_coeffs1) as) e = (\<exists>x. \<forall>a\<in> set as. I\<^isub>Z a (x#e))"
apply(simp)
apply(subst I_qe_pres)
  apply(simp add: divisors_hd_coeffs1)
 apply(simp add: hd_coeff_is1_hd_coeffs1)
using I_hd_coeffs1 apply(simp)
done

definition "pres_qe = Z.lift_dnf_qe (qe_pres \<circ> hd_coeffs1)"

lemma qfree_qe_pres_o: "qfree ((qe_pres \<circ> hd_coeffs1) as)"
by(auto simp:qe_pres_def intro!:qfree_list_disj)


lemma normal_qe_pres_o:
  "\<forall>a \<in> set as. hd_coeff a \<noteq> 0 \<and> divisor a \<noteq> 0 \<Longrightarrow>
   Z.normal ((qe_pres \<circ> hd_coeffs1) as)"
apply(auto simp:qe_pres_def Z.normal_def
   dest!:atoms_list_disjE atoms_list_conjE)

apply(simp add: hd_coeffs1_def)
 apply(erule disjE) apply fastsimp
apply (clarsimp)
apply(case_tac xa)
  apply(case_tac list) apply fastsimp apply simp
 apply(case_tac list) apply fastsimp
 apply simp
 apply(erule disjE) prefer 2 apply fastsimp
 apply(simp add:zdiv_eq_0_iff)
 apply(erule disjE) apply fastsimp
 apply(subgoal_tac "\<forall>i\<in> set(map hd_coeff as). i \<noteq> 0")
  prefer 2 apply simp
 apply(erule disjE) prefer 2 apply (metis linorder_not_le zlcms_pos)
 apply(subgoal_tac "a \<in> set(map hd_coeff as)")
  prefer 2 apply force
 apply (metis elem_le_zlcms linorder_not_le)
apply(case_tac list) apply fastsimp
apply simp
apply(erule disjE) prefer 2 apply fastsimp
apply(simp add:zdiv_eq_0_iff)
apply(erule disjE) apply fastsimp
apply(subgoal_tac "\<forall>i\<in> set(map hd_coeff as). i \<noteq> 0")
 prefer 2 apply simp
apply(erule disjE) prefer 2 apply (metis linorder_not_le zlcms_pos)
apply(subgoal_tac "a \<in> set(map hd_coeff as)")
 prefer 2 apply force
apply (metis elem_le_zlcms linorder_not_le)

apply(simp add: hd_coeffs1_def)
apply(erule disjE) apply fastsimp
apply (clarsimp)
apply(case_tac xa)
  apply(case_tac list) apply fastsimp apply simp
 apply(case_tac list) apply fastsimp
 apply simp
 apply(erule disjE) prefer 2 apply fastsimp
 apply(simp add:zdiv_eq_0_iff)
 apply(erule disjE) apply fastsimp
 apply(subgoal_tac "\<forall>i\<in> set(map hd_coeff as). i \<noteq> 0")
  prefer 2 apply simp
 apply(erule disjE) prefer 2 apply (metis linorder_not_le zlcms_pos)
 apply(subgoal_tac "a \<in> set(map hd_coeff as)")
  prefer 2 apply force
 apply (metis elem_le_zlcms linorder_not_le)
apply(case_tac list) apply fastsimp
apply simp
apply(erule disjE) prefer 2 apply fastsimp
apply(simp add:zdiv_eq_0_iff)
apply(erule disjE) apply fastsimp
apply(subgoal_tac "\<forall>i\<in> set(map hd_coeff as). i \<noteq> 0")
 prefer 2 apply simp
apply(erule disjE) prefer 2 apply (metis linorder_not_le zlcms_pos)
apply(subgoal_tac "a \<in> set(map hd_coeff as)")
 prefer 2 apply force
apply (metis elem_le_zlcms linorder_not_le)
done

theorem I_pres_qe: "Z.normal \<phi> \<Longrightarrow>  Z.I (pres_qe \<phi>) xs = Z.I \<phi> xs"
by(simp add:pres_qe_def Z.I_lift_dnf_qe_anormal I_qe_pres_o qfree_qe_pres_o normal_qe_pres_o del:o_apply)

theorem qfree_pres_qe: "qfree (pres_qe f)"
by(simp add:pres_qe_def Z.qfree_lift_dnf_qe qfree_qe_pres_o del:o_apply)

end