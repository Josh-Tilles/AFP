theory "CValue-Nominal"
imports CValue "Nominal-Utils" "Nominal-HOLCF"
begin

instantiation C :: pure
begin
  definition "p \<bullet> (c::C) = c"
instance by default (auto simp add: permute_C_def)
end
instance C :: pcpo_pt
  by default (simp add: pure_permute_id)


instantiation CValue' :: pure
begin
  definition "p \<bullet> (v::CValue') = v"
instance
  apply default
  apply (auto simp add: permute_CValue'_def)
  done
end

instance CValue' :: pcpo_pt
  by default (simp add: pure_permute_id)

end
