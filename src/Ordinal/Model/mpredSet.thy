theory mpredSet
  imports OrdRec_Model_Base
begin

context OrdRec_Model begin

lemma mpredset_eq :
  assumes j : "j : mOrd"
  shows "mpredSet j = <set, ord \<oplus> predSet (snd j)>"
  unfolding mpredSet_def mpredSet'_def 
  using assms by auto

lemma mpredset_msetof :
  assumes j : "j : mOrd"
  shows "mpredSet j : mSetOf mOrd"
  unfolding mpredset_eq[OF j]
proof (rule msetofI, rule msetI)
  obtain j' where 
    j' : "j' : Ord" and j_eq: "j = <ord,j'>" 
    using mordE[OF j] .
  have "ord \<oplus> predSet (snd j) \<subseteq> Tier j' \<ominus> set"
    unfolding j_eq ord_snd_eq'[OF j']
  proof
    fix i assume "i \<in> ord \<oplus> predSet j'"
    then obtain i' where 
      i': "i' : Ord" "i' < j'" and "i = <ord, i'>" 
     using tmapE[OF tag_pmem[OF ord_tag] predset_set[OF j']] 
           predsetD[OF j'] by metis
    thus "i \<in> Tier j' \<ominus> set"
      using ord_tierI[OF i'(1) j' leqI1[OF i'(1) j']] 
        exsetI[OF tier_set[OF j']] excluded_ord_1
      by auto
  qed
  thus "<set, ord \<oplus> predSet (snd j)> : M" 
    using mI_mset

end