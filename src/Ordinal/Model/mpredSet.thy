theory mpredSet
  imports OrdRec_Model_Base
begin

context OrdRec_Model begin

lemma mpredset_eq :
  assumes j : "j : mOrd"
  shows "mpredSet j = <set, ord \<oplus> predSet (snd j)>"
  unfolding mpredSet_def mpredSet'_def 
  using assms by auto

lemmas tmap_ord_set = tmap_set[OF tag_pmem[OF ord_tag]]

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
        exsetI[OF tier_set[OF j']] not_excluded_set_mord
      by auto
  qed
  thus "<set, ord \<oplus> predSet (snd j)> : M" 
    using mI_mset[OF j' tmap_set[OF 
            tag_pmem[OF ord_tag] predset_set[OF j']]]
    unfolding ord_snd_eq[OF j' j_eq] by auto
  fix b assume 
    "b m <set, ord \<oplus> predSet (snd j)>"
  hence "b \<in> ord \<oplus> predSet (snd j)"
    using mmemD by auto
 then obtain i' where 
    i': "i' : Ord" "i' < j'" and "b = <ord, i'>" 
   using tmapE[OF tag_pmem[OF ord_tag] predset_set[OF j']] 
         predsetD[OF j']
   unfolding ord_snd_eq[OF j' j_eq] by metis
  thus "b : mOrd" using mordI by auto
qed

lemma mpredset_iff : 
  assumes i : "i : mOrd" and j : "j : mOrd"
   shows "i \<lless> j \<longleftrightarrow> i m mpredSet j"
proof -
  obtain i' j' where
  i': "i' : Ord" "i = <ord, i'>" and
  j': "j' : Ord" "j = <ord, j'>"
  using mordE[OF i] mordE[OF j] by metis
  show ?thesis 
    unfolding mpredset_eq[OF j] 
proof (rule, rule mmemI)
  assume ij: "i \<lless> j"
  show "\<langle>set,ord \<oplus> predSet (\<pi> j)\<rangle> : mSet"
    using msetof_mset[OF mpredset_msetof[OF j]]
    unfolding mpredset_eq[OF j] .
  show "i \<in> ord \<oplus> predSet (\<pi> j)"
    using tmapI[OF tag_pmem[OF ord_tag] 
                   predset_set[OF mord_snd_ord[OF j]]
            predsetI[OF i'(1) mord_snd_ord[OF j]]] mltD ij
   unfolding ord_snd_eq[OF j']
   unfolding i' j' by auto
next
  assume "i m <set, ord \<oplus> predSet (snd j)>"
  hence "i \<in> ord \<oplus> predSet (snd j)" 
    using mmemD by auto
  hence "i' \<in> predSet j'"
    unfolding ord_snd_eq[OF j'] i'
      tmap_iff[OF tag_pmem[OF ord_tag] 
        predset_set[OF j'(1)] ord_setmem[OF i'(1)]].
  hence "i' < j'"
    using predsetD[OF j'(1) ] by auto
  thus "i \<lless> j" 
    unfolding i' j' 
    using mltI[OF i'(1) j'(1)] by auto
  qed
qed

theorem mpredset_ax :
  "m\<forall>j : mOrd. m\<forall>i : mOrd. i \<lless> j \<longleftrightarrow> i m mpredSet j"
  unfolding mtall_def mall_def 
  using mpredset_iff by auto

theorem mpredset_rsp : 
  "mpredSet j : M"
  using mset_m[OF msetof_mset[OF mpredset_msetof]]
        OrdRec_Model_mdefault_m
  unfolding mpredSet_def by auto

end  
end