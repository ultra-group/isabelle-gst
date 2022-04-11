theory mOrd
  imports Ordinal_Model_Base
begin

context Ordinal_Model begin

lemma mordI :
  assumes i:"i : Ord"
  shows "<ord, i> : mOrd"
  unfolding mOrd_def
proof (rule intI)
  show "<ord, i> : M"
    using mI[OF i ord_tierI_eq[OF i]] .
  thus "<ord, i> :\<^enum> ord" 
    using partI_pair[OF m_pair] by auto
qed

lemma mord_m :
  "i : mOrd \<Longrightarrow> i : M"
  unfolding mOrd_def by unfold_typs 

lemma ord_m :
  "i : Ord \<Longrightarrow> <ord, i> : M"
  using mord_m[OF mordI] .

lemma ord_snd_eq' : 
  "i : Ord \<Longrightarrow> snd <ord, i> = i"
  using mpair_snd_eq[OF ord_m] .

lemma ord_snd_eq :
  "i' : Ord \<Longrightarrow> i = <ord, i'> \<Longrightarrow> snd i = i'"
  using ord_snd_eq' by auto

lemma mordE :
  assumes i:"i : mOrd"
  obtains i' where "i' : Ord" "i = <ord, i'>" 
proof -
  have "i : M" "i :\<^enum> ord" 
    using i unfolding mOrd_def 
    by (auto dest: intE)
  then obtain i' where i':"i = <ord, i'>" 
    using partE by metis
  then obtain j x where "j : Ord"
     "i' \<in> Variants ord j x" 
    using m_cases_pair \<open>i : M\<close> 
      zero_ord succ_ord limit_ord
    by metis
  hence "i' : Ord" "i = <ord, i'>" 
    using variants_ord_mem i' by auto
  thus ?thesis ..
qed

lemma mord_snd_ord :
  "i : mOrd \<Longrightarrow> snd i : Ord"
  using mordE ord_snd_eq by metis
 
lemma mordD :
  assumes "<ord, i> : mOrd"
  shows "i : Ord"
  using mord_snd_ord[OF assms] 
  unfolding mpair_snd_eq[OF mord_m[OF assms]] .

lemma mord_snd_eq :
  "<ord, i'> : mOrd \<Longrightarrow> snd <ord,i'> = i'" 
  using ord_snd_eq[OF mordD] by auto

lemmas mord_pair_inject = 
  mpair_inject(2)[OF mord_m[OF mordI] mord_m[OF mordI]]

end
end