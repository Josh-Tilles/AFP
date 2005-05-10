(*  Title:      RSAPSS/RSAPSS.thy
    ID:         $Id: RSAPSS.thy,v 1.1 2005-05-10 16:13:46 nipkow Exp $
    Author:     Christina Lindenberg, Kai Wirt, Technische Universit�t Darmstadt
    Copyright:  2005 - Technische Universit�t Darmstadt 
*)

header "RSS-PSS encoding and decoding operation" 

theory RSAPSS
imports EMSAPSS Cryptinverts
begin

text {* We define the RSA-PSS signature and verification operations. Moreover we
  show, that messages signed with RSA-PSS can always be verified
  *}

consts rsapss_sign:: "bv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bv" (* Input: message (an bv), private key, RSA modulus; Output: signature (an bv)*)
       rsapss_sign_help1:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bv"
       rsapss_verify:: "bv \<Rightarrow> bv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" (* Input:  Message, Signature to be verified (an bv), public key, RSA modulus; Output: valid or invalid signature *)

defs

  rsapss_sign:
  "rsapss_sign m e n == if (emsapss_encode m (length (nat_to_bv n) - 1)) = [] 
                          then []
			  else (rsapss_sign_help1 (bv_to_nat (emsapss_encode m (length (nat_to_bv n) - 1)) ) e n)"

  rsapss_sign_help1:
  "rsapss_sign_help1 em_nat e n == nat_to_bv_length (rsa_crypt(em_nat, e, n)) (length (nat_to_bv n))"

  rsapss_verify:
  "rsapss_verify m s d n == if (length s) \<noteq> length(nat_to_bv n)
                            then False
                            else let em = nat_to_bv_length (rsa_crypt ((bv_to_nat s), d, n)) ((roundup (length(nat_to_bv n) - 1) 8) * 8) in emsapss_decode m em (length(nat_to_bv n) - 1)"

lemma length_emsapss_encode [rule_format]: "emsapss_encode m x \<noteq> [] \<longrightarrow> length (emsapss_encode m x) = roundup x 8 * 8"
  apply (simp add: emsapss_encode)
  apply (simp add: emsapss_encode_help1)
  apply (simp add: emsapss_encode_help2)
  apply (simp add: emsapss_encode_help3)
  apply (simp add: emsapss_encode_help4)
  apply (simp add: emsapss_encode_help5)
  apply (simp add: emsapss_encode_help6)
  apply (simp add: emsapss_encode_help7)
  apply (simp add: emsapss_encode_help8)
  apply (simp add: maskedDB_zero)
  apply (simp add: length_generate_DB)
  apply (simp add: sha1len)
  apply (simp add: bvxor)
  apply (simp add: length_generate_PS)
  apply (simp add: length_bv_prepend)
  apply (simp add: MGF)
  apply (simp add: MGF1)
  apply (simp add: length_MGF2)
  apply (simp add: sha1len)
  apply (simp add: length_generate_DB)
  apply (simp add: length_generate_PS)
  apply (simp add: BC)
  apply (simp add: max_min)
  apply (insert roundup_ge_emBits [of x 8])
  apply (safe)
by (simp)+

lemma bv_to_nat_emsapss_encode_le: "emsapss_encode m x \<noteq> [] \<Longrightarrow> bv_to_nat (emsapss_encode m x) < 2^(roundup x 8 * 8)" 
  apply (insert length_emsapss_encode [of m x])
  apply (insert bv_to_nat_upper_range [of "emsapss_encode m x"])
by (simp)

lemma length_helper1: shows "length
  (bvxor
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))
  (MGF (sha1 (generate_M' (sha1 m) salt))
  (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))))@
  sha1 (generate_M' (sha1 m) salt) @ BC)
  = length 
  (bvxor
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))
  (MGF (sha1 (generate_M' (sha1 m) salt))
  (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))))) + 168"
proof -
  have a: "length BC = 8" by (simp add: BC)
  have b: "length (sha1 (generate_M' (sha1 m) salt)) = 160" by (simp add: sha1len)
  have c: "\<And> a b c. length (a@b@c) = length a + length b + length c" by simp
  from a and b show ?thesis using c by simp 
qed

lemma MGFLen_helper: "MGF z l ~= [] \<Longrightarrow> l <= 2^32*(length (sha1 z))"
proof (case_tac "2^32*length (sha1 z) < l")
  assume x: "MGF z l ~= []"
  assume a: "2 ^ 32 * length (sha1 z) < l" 
  hence "MGF z l = []" 
  proof (case_tac "l=0")
    assume "l=0"
    thus "MGF z l = []" by (simp add: MGF)
  next
    assume "l~=0"
    hence "(l = 0 \<or> 2^32*length(sha1 z) < l) = True" using a by fast
    thus "MGF z l = []" apply (simp only: MGF) by simp
  qed
  thus ?thesis using x by simp
next
  assume "\<not> 2 ^ 32 * length (sha1 z) < l" 
  thus ?thesis by simp
qed

lemma length_helper2: assumes p: "p \<in> prime" and q: "q \<in> prime" 
                      and mgf: "(MGF (sha1 (generate_M' (sha1 m) salt))
  (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt))))))) ~= []" 
  and len: "length (sha1 M) + sLen + 16 \<le> (length (nat_to_bv (p * q))) - Suc 0"
  shows "length
  (
  (bvxor
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))
  (MGF (sha1 (generate_M' (sha1 m) salt))
  (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt))))))))
  ) = (roundup (length (nat_to_bv (p * q)) - Suc 0) 8) * 8 - 168"
proof -
  have a: "length (MGF (sha1 (generate_M' (sha1 m) salt))
  (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt))))))) = (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt))))))"
  proof -
    have "0 < (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt))))))" by (simp add: generate_DB)
    moreover have "(length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))) \<le> 2^32 * length (sha1 (sha1 (generate_M' (sha1 m) salt)))" using mgf and MGFLen_helper by simp
    ultimately show ?thesis using length_MGF by simp
  qed
  have b: "length (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt))))) = ((roundup ((length (nat_to_bv (p * q))) - Suc 0) 8) * 8 - 168)"
  proof -
    have "0 <= (length (nat_to_bv (p * q))) - Suc 0" 
    proof -
      from p have p2: "1<p" by (simp add: prime_def)
      moreover from q have "1<q" by (simp add: prime_def)
      ultimately have "p<p*q" by simp
      hence "1<p*q" using p2 by arith
      thus ?thesis using len_nat_to_bv_pos by simp
    qed  
    thus ?thesis using solve_length_generate_DB using len by simp
  qed
  have c: "length (bvxor
    (generate_DB
    (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
    (length (sha1 (generate_M' (sha1 m) salt)))))
    (MGF (sha1 (generate_M' (sha1 m) salt))
    (length
    (generate_DB
    (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
    (length (sha1 (generate_M' (sha1 m) salt)))))))) =
    roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8 - 168" using a and b and length_bvxor by simp
 then show ?thesis by simp
qed

lemma emBits_roundup_cancel: "emBits mod 8 ~= 0 \<Longrightarrow> (roundup emBits 8)*8 - emBits = 8-(emBits mod 8)"
apply (auto simp add: roundup)
by (arith)

lemma emBits_roundup_cancel2: "emBits mod 8 ~=0 \<Longrightarrow> (roundup emBits 8) * 8 - (8-(emBits mod 8)) = emBits"
by (auto simp add: roundup)

lemma length_bound: "\<lbrakk>emBits mod 8 ~=0; 8 <= (length maskedDB)\<rbrakk> \<Longrightarrow> length (remzero ((maskedDB_zero maskedDB emBits)@a@b)) <= length (maskedDB@a@b) - (8-(emBits mod 8))"
proof -
  assume a: "emBits mod 8 ~=0"
  assume len: "8 <= (length maskedDB)"
  have b:" \<And> a. length (remzero a) <= length a"
  proof -
    fix a
    show "length (remzero a) <= length a"
    proof (induct a)
      show "(length (remzero [])) <= length []" by (simp)
    next
      case (Cons hd tl)
      show "(length (remzero (hd#tl))) <= length (hd#tl)"
      proof (cases hd)
	assume "hd=\<zero>"
	hence "remzero (hd#tl) = remzero tl" by simp
	thus ?thesis using Cons by simp
      next
	assume "hd=\<one>"
	hence "remzero (hd#tl) = hd#tl" by simp
	thus ?thesis by simp
      qed
    qed
  qed
  from len show "length (remzero (maskedDB_zero maskedDB emBits @ a @ b)) \<le> length (maskedDB @ a @ b) - (8 - emBits mod 8)"
  proof -
    have "remzero(bv_prepend ((roundup emBits 8) * 8 - emBits)
      \<zero> (drop ((roundup emBits 8)*8 - emBits) maskedDB)@a@b) = remzero ((drop ((roundup emBits 8)*8 -emBits) maskedDB)@a@b)" using remzero_replicate by (simp add: bv_prepend)
    moreover from emBits_roundup_cancel have "roundup emBits 8 * 8 - emBits = 8 - emBits mod 8" using a by simp
    moreover have "length ((drop (8-emBits mod 8) maskedDB)@a@b) = length (maskedDB@a@b) - (8-emBits mod 8)" 
    proof -
      show ?thesis using length_drop[of "(8-emBits mod 8)" maskedDB] 
      proof (simp)
	have "0 <= emBits mod 8" by simp
	hence "8-(emBits mod 8) <= 8" by simp
	thus  "length maskedDB + emBits mod 8 - 8 + (length a + length b) =
	  length maskedDB + (length a + length b) + emBits mod 8 - 8" using len by arith
      qed
    qed
    ultimately show ?thesis using b[of "(drop ((roundup emBits 8)*8 - emBits) maskedDB)@a@b"] by (simp add: maskedDB_zero)
  qed
qed

lemma length_bound2: "8<=length ( (bvxor
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))
  (MGF (sha1 (generate_M' (sha1 m) salt))
  (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))))))" 
proof -
  have "8 <= length (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))" by (simp add: generate_DB)
  thus ?thesis using length_bvxor_bound by simp
qed

lemma length_helper: assumes p: "p \<in> prime" and q: "q \<in> prime" and x: "(length (nat_to_bv (p * q)) - Suc 0) mod 8 ~= 0" and mgf: "(MGF (sha1 (generate_M' (sha1 m) salt))
  (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt))))))) ~= []"  
  and len: "length (sha1 M) + sLen + 16 \<le> (length (nat_to_bv (p * q))) - Suc 0"
  shows "length
  (remzero
  (maskedDB_zero
  (bvxor
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))
  (MGF (sha1 (generate_M' (sha1 m) salt))
  (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt))))))))
  (length (nat_to_bv (p * q)) - Suc 0) @
  sha1 (generate_M' (sha1 m) salt) @ BC))
  < length (nat_to_bv (p * q))"
proof -
  from mgf have round: "168 <= roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8"
  proof (simp only: sha1len sLen)
    from len have "160 + sLen +16 \<le> length (nat_to_bv (p * q)) - Suc 0" by (simp add: sha1len)
    hence len1: "176 <= length (nat_to_bv (p * q)) - Suc 0" by simp
    have "length (nat_to_bv (p*q)) - Suc 0 <= (roundup (length (nat_to_bv (p * q)) - Suc 0) 8) * 8" apply (simp only: roundup)
    proof (case_tac "(length (nat_to_bv (p*q)) - Suc 0) mod 8 = 0")
	assume len2: "(length (nat_to_bv (p * q)) - Suc 0) mod 8 = 0" 
	hence "(if (length (nat_to_bv (p * q)) - Suc 0) mod 8 = 0 then (length (nat_to_bv (p * q)) - Suc 0) div 8 else (length (nat_to_bv (p * q)) - Suc 0) div 8 + 1) * 8 = (length (nat_to_bv (p * q)) - Suc 0) div 8 * 8" by simp
	moreover have "(length (nat_to_bv (p * q)) - Suc 0) div 8 * 8 = (length (nat_to_bv (p * q)) - Suc 0)" using len2 by (auto simp add: div_mod_equality[of "length (nat_to_bv (p * q)) - Suc 0" 8 0])
	ultimately show "length (nat_to_bv (p * q)) - Suc 0
    \<le> (if (length (nat_to_bv (p * q)) - Suc 0) mod 8 = 0 then (length (nat_to_bv (p * q)) - Suc 0) div 8 else (length (nat_to_bv (p * q)) - Suc 0) div 8 + 1) * 8" by simp
      next
	assume len2: "(length (nat_to_bv (p*q)) - Suc 0) mod 8 ~= 0"
	hence "(if (length (nat_to_bv (p * q)) - Suc 0) mod 8 = 0 then (length (nat_to_bv (p * q)) - Suc 0) div 8 else (length (nat_to_bv (p * q)) - Suc 0) div 8 + 1) * 8 = ((length (nat_to_bv (p * q)) - Suc 0) div 8 + 1) * 8" by simp
	moreover have "length (nat_to_bv (p*q)) - Suc 0 <= ((length (nat_to_bv (p*q)) - Suc 0) div 8 + 1)*8"
	proof (auto)
	  have "length (nat_to_bv (p * q)) - Suc 0 = (length (nat_to_bv (p * q)) - Suc 0) div 8 * 8 + (length (nat_to_bv (p * q)) - Suc 0) mod 8" by (simp add: div_mod_equality[of "length (nat_to_bv (p * q)) - Suc 0" 8 0])
	  moreover have "(length (nat_to_bv (p * q)) - Suc 0) mod 8 < 8" by simp
	  ultimately show "length (nat_to_bv (p * q)) - Suc 0 \<le> 8 + (length (nat_to_bv (p * q)) - Suc 0) div 8 * 8" by arith
	qed
	ultimately show "length (nat_to_bv (p * q)) - Suc 0
    \<le> (if (length (nat_to_bv (p * q)) - Suc 0) mod 8 = 0 then (length (nat_to_bv (p * q)) - Suc 0) div 8 else (length (nat_to_bv (p * q)) - Suc 0) div 8 + 1) * 8" by simp
      qed
    thus "168 \<le> roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8" using len1 by simp
  qed
  from x have a: "length
    (remzero
    (maskedDB_zero
    (bvxor
    (generate_DB
    (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
    (length (sha1 (generate_M' (sha1 m) salt)))))
    (MGF (sha1 (generate_M' (sha1 m) salt))
    (length
    (generate_DB
    (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
    (length (sha1 (generate_M' (sha1 m) salt))))))))
    (length (nat_to_bv (p * q)) - Suc 0) @
    sha1 (generate_M' (sha1 m) salt) @ BC)) <= length ((bvxor
    (generate_DB
    (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
    (length (sha1 (generate_M' (sha1 m) salt)))))
    (MGF (sha1 (generate_M' (sha1 m) salt))
    (length
    (generate_DB
    (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
    (length (sha1 (generate_M' (sha1 m) salt)))))))) @
    sha1 (generate_M' (sha1 m) salt) @ BC) - (8 - (length (nat_to_bv (p*q)) - Suc 0) mod 8)" using length_bound and length_bound2 by simp
  have b: " length (bvxor (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt)))))
             (MGF (sha1 (generate_M' (sha1 m) salt)) (length (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt))))))) @
            sha1 (generate_M' (sha1 m) salt) @ BC) =  length (bvxor (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt)))))
             (MGF (sha1 (generate_M' (sha1 m) salt)) (length (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt)))))))) +168" using length_helper1 by simp
  have c: "length (bvxor (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt)))))
           (MGF (sha1 (generate_M' (sha1 m) salt)) (length (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt)))))))) = 
            (roundup (length (nat_to_bv (p * q)) - Suc 0) 8) * 8 - 168" using p and q and length_helper2 and mgf and len by simp
  from a and b and c have " length (remzero (maskedDB_zero
                    (bvxor (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt)))))
                      (MGF (sha1 (generate_M' (sha1 m) salt))
                        (length (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt))))))))
                    (length (nat_to_bv (p * q)) - Suc 0) @
                   sha1 (generate_M' (sha1 m) salt) @ BC)) <=  roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8 - 168 +168 - (8 - (length (nat_to_bv (p * q)) - Suc 0) mod 8)" by simp 
  hence "length (remzero (maskedDB_zero
                    (bvxor (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt)))))
                      (MGF (sha1 (generate_M' (sha1 m) salt))
                        (length (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt))))))))
                    (length (nat_to_bv (p * q)) - Suc 0) @
                   sha1 (generate_M' (sha1 m) salt) @ BC)) <= roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8 - (8 - (length (nat_to_bv (p * q)) - Suc 0) mod 8)" using round by simp
  moreover have "  roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8 - (8 - (length (nat_to_bv (p * q)) - Suc 0) mod 8) = (length (nat_to_bv (p*q))-Suc 0)" using x and emBits_roundup_cancel2 by simp
  moreover have "0<length (nat_to_bv (p*q))" 
  proof -
    from p have s: "1<p" by (simp add: prime_def)
    moreover from q have "1<q" by (simp add: prime_def)
    ultimately have "p<p*q" by simp 
    hence "1<p*q" using s by arith
    thus ?thesis using len_nat_to_bv_pos by simp
  qed
  ultimately show ?thesis by arith
qed

lemma length_emsapss_smaller_pq: "\<lbrakk>p \<in> prime; q \<in> prime; emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0) \<noteq> []; (length (nat_to_bv (p * q)) - Suc 0) mod 8 ~= 0\<rbrakk> \<Longrightarrow>  length (remzero (emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0))) < length (nat_to_bv (p*q))"
proof -
  assume a: "emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0) \<noteq> []"
  assume p: "p \<in> prime" and q: "q \<in> prime"
  assume x: "(length (nat_to_bv (p * q)) - Suc 0) mod 8 ~= 0"
  have b: " emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0)= emsapss_encode_help1 (sha1 m)
    (length (nat_to_bv (p * q)) - Suc 0)"
  proof (simp only: emsapss_encode)
    from a show "(if ((2^64 \<le> length m) \<or> (2^32 * 160 < (length (nat_to_bv (p*q)) - Suc 0)))
      then []
      else (emsapss_encode_help1 (sha1 m) (length (nat_to_bv (p*q))- Suc 0))) = (emsapss_encode_help1 (sha1 m) (length (nat_to_bv (p*q)) - Suc 0))" by (auto simp add: emsapss_encode)
  qed
  have c: "length (remzero (emsapss_encode_help1 (sha1 m) (length (nat_to_bv (p * q)) - Suc 0))) < length (nat_to_bv (p*q))"
  proof (simp only: emsapss_encode_help1) 
     from a and b have d: "(if ((length (nat_to_bv (p * q)) - Suc 0) < (length (sha1 m) + sLen + 16))
      then []
      else (emsapss_encode_help2 (generate_M' (sha1 m) salt)
      (length (nat_to_bv (p * q)) - Suc 0))) = (emsapss_encode_help2 ((generate_M' (sha1 m)) salt) (length (nat_to_bv (p*q)) - Suc 0))" by (auto simp add: emsapss_encode emsapss_encode_help1)
     from d have len: "length (sha1 m) + sLen + 16 <= (length (nat_to_bv (p*q))) - Suc 0"
     proof (case_tac "length (nat_to_bv (p * q)) - Suc 0 < length (sha1 m) + sLen + 16")
       assume "length (nat_to_bv (p * q)) - Suc 0 < length (sha1 m) + sLen + 16"
       hence len1: "(if length (nat_to_bv (p * q)) - Suc 0 < length (sha1 m) + sLen + 16 then []
      else emsapss_encode_help2 (generate_M' (sha1 m) salt) (length (nat_to_bv (p * q)) - Suc 0)) = []" by simp
       assume len2:  "(if length (nat_to_bv (p * q)) - Suc 0 < length (sha1 m) + sLen + 16 then []
      else emsapss_encode_help2 (generate_M' (sha1 m) salt) (length (nat_to_bv (p * q)) - Suc 0)) =
     emsapss_encode_help2 (generate_M' (sha1 m) salt) (length (nat_to_bv (p * q)) - Suc 0)"
       from len1 and len2 and a and b show "length (sha1 m) + sLen + 16 \<le> length (nat_to_bv (p * q)) - Suc 0" by (auto simp add: emsapss_encode emsapss_encode_help1)
     next
       assume "\<not> length (nat_to_bv (p * q)) - Suc 0 < length (sha1 m) + sLen + 16"
       thus "length (sha1 m) + sLen + 16 \<le> length (nat_to_bv (p * q)) - Suc 0" by simp
     qed
    have e: "length (remzero (emsapss_encode_help2 (generate_M' (sha1 m) salt)
   (length (nat_to_bv (p * q)) - Suc 0))) < length (nat_to_bv (p * q))"
      proof (simp only: emsapss_encode_help2)
	show "length
	  (remzero
	  (emsapss_encode_help3 (sha1 (generate_M' (sha1 m) salt))
          (length (nat_to_bv (p * q)) - Suc 0)))
	  < length (nat_to_bv (p * q))"
	proof (simp add: emsapss_encode_help3 emsapss_encode_help4 emsapss_encode_help5)
	  show "length
	    (remzero
	    (emsapss_encode_help6
            (generate_DB
            (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
            (length (sha1 (generate_M' (sha1 m) salt)))))
            (MGF (sha1 (generate_M' (sha1 m) salt))
            (length
            (generate_DB
            (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
            (length (sha1 (generate_M' (sha1 m) salt)))))))
            (sha1 (generate_M' (sha1 m) salt))
            (length (nat_to_bv (p * q)) - Suc 0)))
	    < length (nat_to_bv (p * q))"
	  proof (simp only: emsapss_encode_help6)
	    from a and b and d have mgf: "MGF (sha1 (generate_M' (sha1 m) salt))
              (length
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt)))))) ~=
              []" by (auto simp add: emsapss_encode emsapss_encode_help1 emsapss_encode_help2 emsapss_encode_help3 emsapss_encode_help4 emsapss_encode_help5 emsapss_encode_help6)
            from a and b and d have f: "(if MGF (sha1 (generate_M' (sha1 m) salt))
              (length
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt)))))) =
              []
              then []
              else (emsapss_encode_help7
              (bvxor
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt)))))
              (MGF (sha1 (generate_M' (sha1 m) salt))
              (length
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt))))))))
              (sha1 (generate_M' (sha1 m) salt))
              (length (nat_to_bv (p * q)) - Suc 0))) = (emsapss_encode_help7
              (bvxor
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt)))))
              (MGF (sha1 (generate_M' (sha1 m) salt))
              (length
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt))))))))
              (sha1 (generate_M' (sha1 m) salt))
              (length (nat_to_bv (p * q)) - Suc 0))" by (auto simp add: emsapss_encode emsapss_encode_help1 emsapss_encode_help2 emsapss_encode_help3 emsapss_encode_help4 emsapss_encode_help5 emsapss_encode_help6)
	    have "length (remzero (emsapss_encode_help7
	      (bvxor
	      (generate_DB
	      (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt)))))
	      (MGF (sha1 (generate_M' (sha1 m) salt))
	      (length
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt))))))))
	      (sha1 (generate_M' (sha1 m) salt)) (length (nat_to_bv (p * q)) - Suc 0))) < length (nat_to_bv (p * q))"
	    proof (simp add: emsapss_encode_help7 emsapss_encode_help8)
	      from p and q and x show " length
		(remzero
		(maskedDB_zero
		(bvxor
		(generate_DB
		(generate_PS (length (nat_to_bv (p * q)) - Suc 0)
		(length (sha1 (generate_M' (sha1 m) salt)))))
		(MGF (sha1 (generate_M' (sha1 m) salt))
		(length
		(generate_DB
                (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
                (length (sha1 (generate_M' (sha1 m) salt))))))))
		(length (nat_to_bv (p * q)) - Suc 0) @
		sha1 (generate_M' (sha1 m) salt) @ BC))
		< length (nat_to_bv (p * q))" using "length_helper" and len and mgf by simp
	    qed
	    then show "length
	      (remzero
	      (if MGF (sha1 (generate_M' (sha1 m) salt))
              (length
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt)))))) =
              []
              then []
              else emsapss_encode_help7
              (bvxor
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt)))))
              (MGF (sha1 (generate_M' (sha1 m) salt))
              (length
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt))))))))
              (sha1 (generate_M' (sha1 m) salt))
              (length (nat_to_bv (p * q)) - Suc 0)))
	      < length (nat_to_bv (p * q))" using f by simp
	  qed
	qed
      qed
    from d and e show "length
      (remzero
      (if length (nat_to_bv (p * q)) - Suc 0 < length (sha1 m) + sLen + 16
      then []
      else emsapss_encode_help2 (generate_M' (sha1 m) salt)
      (length (nat_to_bv (p * q)) - Suc 0)))
      < length (nat_to_bv (p * q))" by simp
  qed
  from b and c show ?thesis by simp
qed

lemma bv_to_nat_emsapss_smaller_pq: assumes a: "p \<in> prime" and b: "q \<in> prime" and pneq: "p ~= q" and c: "emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0) \<noteq> []" shows "bv_to_nat (emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0)) < p*q"
proof -
  from a and b and c show ?thesis
  proof (case_tac "8 dvd ((length (nat_to_bv (p * q))) - Suc 0)")
    assume d: "8 dvd ((length (nat_to_bv (p * q))) - Suc 0)"
    hence "2 ^ (roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8) < p*q"
    proof -
      from d have e: "roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8 = length (nat_to_bv (p * q)) - Suc 0" using rnddvd by simp
      have "p*q = bv_to_nat (nat_to_bv (p*q))" by simp
      hence "2 ^ (length (nat_to_bv (p * q)) - Suc 0) < p*q"
      proof -
	have "0<p*q"
	proof -
	  have "0<p" using a by (simp add: prime_def, arith)
	  moreover have "0<q" using b by (simp add: prime_def, arith)
	  ultimately show ?thesis by simp
	qed
	moreover have "2^(length (nat_to_bv (p*q)) - Suc 0) ~= p*q" 
	proof (case_tac "2^(length (nat_to_bv (p*q)) - Suc 0) = p*q")
	  assume "2^(length (nat_to_bv (p*q)) - Suc 0) = p*q"
	  then have "p=q" using a and b and prime_equal by simp
	  thus ?thesis using pneq by simp
	next
	  assume "2^(length (nat_to_bv (p*q)) - Suc 0) ~= p*q"
	  thus ?thesis by simp
	qed
	ultimately show ?thesis using len_lower_bound[of "p*q"] by (simp)
      qed
      thus ?thesis using e by simp
    qed
    moreover from c have "bv_to_nat (emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0)) < 2 ^ (roundup (length (nat_to_bv (p * q)) - Suc 0)8 * 8 )" 
      using bv_to_nat_emsapss_encode_le [of m "(length (nat_to_bv (p * q)) - Suc 0)"] by auto
    ultimately show ?thesis by simp
  next
    assume y: "~(8 dvd (length (nat_to_bv (p*q)) - Suc 0))"
    thus ?thesis
    proof -
      from y have x: "~((length (nat_to_bv (p * q)) - Suc 0) mod 8 = 0)" by (simp add: dvd_eq_mod_eq_0)
      from remzeroeq have d: "bv_to_nat (emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0)) = bv_to_nat (remzero (emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0)))" by simp
      from a and b and c and x and length_emsapss_smaller_pq[of p q m] have "bv_to_nat (remzero (emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0))) < bv_to_nat (nat_to_bv (p*q))" using length_lower[of "remzero (emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0))" "nat_to_bv (p * q)"] and prime_hd_non_zero[of p q] by (auto)
      thus "bv_to_nat (emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0)) < p * q" using d and bv_nat_bv by simp
    qed
  qed
qed

lemma rsa_pss_verify: "\<lbrakk> p \<in> prime; q \<in> prime; p \<noteq> q; n = p*q; e*d mod ((pred p)*(pred q)) = 1; rsapss_sign m e n \<noteq> []; s = rsapss_sign m e n \<rbrakk> \<Longrightarrow> rsapss_verify m s d n = True" 
  apply (simp only: rsapss_sign rsapss_verify)
  apply (simp only: rsapss_sign_help1)
  apply (auto)
  apply (simp add: length_nat_to_bv_length)
  apply (simp add: Let_def)
  apply (simp add:  bv_to_nat_nat_to_bv_length)
  apply (insert length_emsapss_encode [of m "(length (nat_to_bv (p * q)) - Suc 0)"])
  apply (insert bv_to_nat_emsapss_smaller_pq [of p q m])
  apply (simp add: cryptinverts)
  apply (insert length_emsapss_encode [of m "(length (nat_to_bv (p * q)) - Suc 0)"])
  apply (insert nat_to_bv_length_bv_to_nat [of "emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0)" "roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8"])
by (simp add: verify)

end
