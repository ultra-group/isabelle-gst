theory Ordinal_Model_Base
  imports "../../ModelKit/ModelComponents"
begin

context ModelBase begin
ML \<open>val ord_model = mcomp 
 { name = "Ordinal_Model", 
   deps = [], 
   variant = SOME (vari 
    { tag_name = "ord",
      vcases = 
        (@{term \<open>{0}\<close>}, 
         @{term "(\<lambda>j x. {j}) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"}, 
         @{term "(\<lambda>\<mu> f. {\<mu>}) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"}),
      alpha_typ = @{term \<open>Ord\<close>},
      excludes_formulas = [@{prop \<open>\<not> Excluded ord <ord, j>\<close>}]})} \<close>
end
local_setup \<open>snd o (mk_mcomp_class ord_model)\<close>

context Ordinal_Model 
begin
(*MOVE ME*)
lemmas zero_ord = zero_typ

definition mOrd :: \<open>'a \<Rightarrow> bool\<close>
  where "mOrd \<equiv> M \<triangle> \<^enum> ord"

definition mlt :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<lless>\<close> 50)
  where "i \<lless> j \<equiv> i : mOrd \<and> j : mOrd \<and> snd i < snd j"

definition mzero :: \<open>'a\<close> (\<open>m0\<close>)
  where "m0 \<equiv> <ord,0>"

definition msucc' :: \<open>'a \<Rightarrow> 'a\<close>
  where "msucc' j \<equiv> <ord, succ (snd j)>"

definition msucc :: \<open>'a \<Rightarrow> 'a\<close>
  where "msucc j \<equiv> if j : mOrd then msucc' j 
                               else Ordinal_Model_mdefault"

definition momega :: \<open>'a\<close> (\<open>m\<omega>\<close>)
  where "m\<omega> \<equiv> <ord, \<omega>>"

definition mLimit :: \<open>'a \<Rightarrow> bool\<close>
  where "mLimit j \<equiv> j : mOrd \<and> snd j : Limit"

theorem variants_ord_cases :
  shows "Variants ord 0 x = {0}"
    and "j : Ord   \<Longrightarrow> Variants ord (succ j) x = {succ j}"
    and "\<mu> : Limit \<Longrightarrow> Variants ord \<mu> f = {\<mu>}"
  using v_ord_0 v_ord_succ v_ord_limit by auto

corollary variants_ord :
  assumes j : "j : Ord"
  shows "Variants ord j x = {j}"
  by (rule ord_cases[OF j], 
      use variants_ord_cases in auto)

corollary variants_ord_mem : 
  assumes j : "j : Ord"
  shows "i \<in> Variants ord j x \<Longrightarrow> i = j"
  unfolding variants_ord[OF j]
     sng_iff[OF ord_setmem[OF j]] .
  
lemma ord_tierI_cases :
  shows "<ord, 0> \<in> Tier 0"
    and "j : Ord   \<Longrightarrow> <ord,succ j> \<in> Tier (succ j)"
    and "u : Limit \<Longrightarrow> <ord, u> \<in> Tier u"
 using tier0I[OF ord_tag] tier_succI2[OF ord_tag] tier_limI2[OF ord_tag]   
       variants_ord sng_iff[OF ord_setmem] zero_ord succ_ord limit_ord 
 by auto

lemma ord_tierI_eq :
  assumes i : "i : Ord"
    shows "<ord, i> \<in> Tier i"
  by (rule ord_cases[OF i], 
      use ord_tierI_cases in auto) 

lemma ord_tierI :
  assumes i : "i : Ord" and j : "j : Ord"
      and ij: "i \<le> j"
    shows "<ord, i> \<in> Tier j"
  by (rule leqE[OF i j ij],
      use ord_tierI_eq[OF i] tier_increasing[OF i j] in auto)
    
lemma ord_tierD : 
  assumes i : "i : Ord" and j : "j : Ord"
  shows "<ord,i> \<in> Tier j \<Longrightarrow> i \<le> j"
proof (induct rule: trans_induct3[OF j])
  case 1
  hence "i \<in> Variants ord 0 \<emptyset>" 
    using tier0D(2) by simp
  hence "i = 0" 
    using variants_ord_mem[OF zero_ord] by simp
  then show ?case 
    using leq_zero_iff[OF i] by auto
next
  case ih:(2 j)
  show ?case 
  proof (rule tier_succE_pair[OF ih(1) ih(3)])
    assume "<ord,i> \<in> Tier j"
    hence "i \<le> j" using ih(2) by simp
    thus "i \<le> succ j" 
      using leq_succ_iff[OF i ih(1)] by auto
  next
    assume "i \<in> Variants ord (succ j) (Tier j \<ominus> ord)"
    hence "i = succ j" 
      using variants_ord_mem[OF succ_ord[OF ih(1)]] by auto
    thus "i \<le> succ j" 
      using leqI2[OF i succ_ord[OF ih(1)]] by auto
  qed
next
  case ih:(3 \<mu>)
  show ?case 
  proof (rule tier_limE_pair[OF ih(1) ih(3)])
    fix j 
    assume j:"j : Ord" "j < \<mu>"
       and ij:"<ord,i> \<in> Tier j"
    hence "i \<le> j" 
      using ih(2) by auto 
    thus "i \<le> \<mu>" 
      using leqI1[OF j(1) limit_ord[OF ih(1)] j(2)]
            leq_trans2[OF i j(1) limit_ord[OF ih(1)]] 
      by auto
  next
    assume "i \<in> Variants ord \<mu> (\<lambda>j<\<mu>. Tier j \<ominus> ord)"
    hence "i = \<mu>" 
      using variants_ord_mem[OF limit_ord[OF ih(1)]] by auto
    thus "i \<le> \<mu>" 
      by (rule leqI2[OF i limit_ord[OF ih(1)]])
  qed
qed      

lemma ord_tier_iff : 
  assumes i : "i : Ord" and j : "j : Ord"
    shows "<ord, i> \<in> Tier j \<longleftrightarrow> i \<le> j"
  using ord_tierI[OF i j] ord_tierD[OF i j] 
  by auto



end
end