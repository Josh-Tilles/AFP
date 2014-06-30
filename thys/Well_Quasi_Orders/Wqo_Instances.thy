(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Instances of Well-Quasi-Orders *}

theory Wqo_Instances
imports Kruskal_New
begin


subsection {* The Option Type is Well-Quasi-Ordered *}

instantiation option :: (wqo) wqo
begin
definition "x \<le> y \<longleftrightarrow> option_le (op \<le>) x y"
definition "(x :: 'a option) < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"

instance
  by (rule class.wqo.of_class.intro)
     (auto simp: less_eq_option_def [abs_def] less_option_def [abs_def])
end


subsection {* The Sum Type is Well-Quasi-Ordered *}

instantiation sum :: (wqo, wqo) wqo
begin
definition "x \<le> y \<longleftrightarrow> sum_le (op \<le>) (op \<le>) x y"
definition "(x :: 'a + 'b) < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"

instance
  by (rule class.wqo.of_class.intro)
     (auto simp: less_eq_sum_def [abs_def] less_sum_def [abs_def])
end


subsection {* Pairs are Well-Quasi-Ordered *}

text {*If types @{typ "'a"} and @{typ "'b"} are well-quasi-ordered by @{text "P"}
and @{text "Q"}, then pairs of type @{typ "'a \<times> 'b"} are well-quasi-ordered by
the pointwise combination of @{text P} and @{text Q}.*}

instantiation prod :: (wqo, wqo) wqo
begin
definition "p \<le> q \<longleftrightarrow> prod_le (op \<le>) (op \<le>) p q"
definition "(p :: 'a \<times> 'b) < q \<longleftrightarrow> p \<le> q \<and> \<not> (q \<le> p)"

instance
  by (rule class.wqo.of_class.intro)
     (auto simp: less_eq_prod_def [abs_def] less_prod_def [abs_def])
end


subsection {* Lists are Well-Quasi-Ordered *}

text {*If the type @{typ "'a"} is well-quasi-ordered by @{text "P"}, then
lists of type @{typ "'a list"} are well-quasi-ordered by the homeomorphic
embedding relation.*}

instantiation list :: (wqo) wqo
begin
definition "xs \<le> ys \<longleftrightarrow> list_emb (op \<le>) xs ys"
definition "(xs :: 'a list) < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> (ys \<le> xs)"

instance
  by (rule class.wqo.of_class.intro)
     (auto simp: less_eq_list_def [abs_def] less_list_def [abs_def])
end

end

