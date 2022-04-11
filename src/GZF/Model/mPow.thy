theory mPow
  imports mMem
begin

context GZF_Model begin

lemma mPow_eq : 
  assumes "x : mSet"
  shows "m\<P> x = <set, set \<oplus> \<P> (snd x)>"
  unfolding mPow_def mPow'_def
  using assms
  by auto

lemma mpow_typ : "m\<P> : mSet \<rightarrow> mSetOf mSet"
proof (rule funI, unfold mPow_eq, rule msetofI, rule msetI)
  fix x assume "x : mSet"
  then obtain x' 
    where x' : "x = <set,x'>" "x' : Set" 
    by (rule msetE)
  then obtain j 
    where j : "j : Ord" and "<set,x'> \<in> Tier j" 
    using mE[OF mset_m[OF \<open>x : mSet\<close>]] by auto
  hence x'_sub:"x' \<subseteq> Tier j \<ominus> set" 
    using tierD_mset[OF j tier_succI1[OF j]] by auto
  
  have "set \<oplus> \<P> x' \<subseteq> Tier (succ j) \<ominus> set"  
  proof (rule, erule tmapE[OF tag_pmem[OF set_tag] pow_set[OF x'(2)]],
         rule exsetI[OF tier_set[OF succ_ord[OF j]]])
    fix y y' assume "y' \<in> \<P> x'" "y = <set,y'>"
    hence "y' \<subseteq> Tier j \<ominus> set" "y' : Set"
      using subset_trans[OF powD[OF x'(2)] x'_sub]
            pow_mem[OF \<open>x' : Set\<close>] by auto
    thus "y \<in> Tier (succ j)" using tierI_mset[OF j] \<open>y = <set,y'>\<close> by auto
    show "\<not> Excluded set y" 
      using excluded_set_1
      unfolding \<open>y = <set,y'>\<close> by auto
  qed

  thus "<set, set \<oplus> \<P> (snd x)> : M"
    unfolding x'(1) mset_snd_eq'[OF x'(2)]
  by (rule mI[OF succ_ord[OF succ_ord[OF j]] 
    tierI_mset[OF succ_ord[OF j] tmap_set[OF tag_pmem[OF set_tag] pow_set[OF x'(2)]]]])
(*  by (rule mI[OF succ_ord[OF succ_ord[OF j]] tierI_mset[OF succ_ord[OF j]]]) *)

  fix b assume "b m <set, set \<oplus> \<P> (snd x)>"
  hence "b \<in> set \<oplus> \<P> x'" 
    using mmemD
    unfolding x'(1) mset_snd_eq'[OF x'(2)] by auto
  then obtain b' where "b = <set,b'>" "b' \<in> \<P> x'" 
    by (rule tmapE[OF tag_pmem[OF set_tag] pow_set[OF x'(2)]])
  hence "b' \<subseteq> Tier j \<ominus> set" "b' : Set" 
    using subset_trans[OF powD[OF x'(2)] x'_sub]
          pow_mem[OF \<open>x' : Set\<close>] by auto
  thus "b : mSet" 
    using msetI[OF mI_mset[OF j]] \<open>b = <set,b'>\<close> by auto
qed

lemmas mpow_mset = funE[OF mpow_typ]

lemma msubsetI :
  assumes "\<And>b. b m x \<Longrightarrow> b m y"
  shows "mSubset x y"
  using assms
  unfolding mSubset_def by auto

lemma msubsetD :
  assumes xy : "mSubset x y"
      and b  : "b m x"  
    shows "b m y"
 using assms mmem_m
 unfolding mSubset_def mall_def by auto

lemma mpowI :
  assumes x : "x : mSet" and y : "y : mSet" 
      and xy:"mSubset x y"
    shows "x m m\<P> y"
  unfolding mPow_eq[OF y]
proof (rule msetE[OF x], rule msetE[OF y])
  fix x' y' 
  assume x':"x = <set, x'>" "x' : Set"
     and y':"y = <set, y'>" "y' : Set"
  
  show "x m <set, set \<oplus> \<P> (snd y)>"
    unfolding y' mset_snd_eq'[OF y'(2)] x'
  proof (rule mmemI)
    show "\<langle>set,set \<oplus> \<P> y'\<rangle> : mSet"
      using msetof_mset[OF funE[OF mpow_typ y]] mPow_eq[OF y]
      unfolding  y' mset_snd_eq'[OF y'(2)] 
      by auto
  next 
    have "x' \<subseteq> y'"
    proof
      fix a assume "a \<in> x'"
      hence "a m x" using mmemI_eq[OF x x'(1)] by auto
      hence "a m y" using msubsetD[OF xy] by auto
      thus "a \<in> y'" using mmemD_eq[OF y'(1)] by auto
    qed      
    hence "x' \<in> \<P> y'"
      using powI x' y' by auto
    thus "<set, x'> \<in> set \<oplus> \<P> y'"
      using tmapI[OF tag_pmem[OF set_tag] pow_set[OF y'(2)]] 
      by auto
  qed
qed

lemma mpowD : 
  assumes x : "x : mSet" and y : "y : mSet" 
      and pow : "x m m\<P> y"
    shows "mSubset x y"
proof (rule msetE[OF x], rule msetE[OF y])
  fix x' y' 
  assume x':"x = <set, x'>" "x' : Set"
     and y':"y = <set, y'>" "y' : Set"
  
  from pow have "<set,x'> \<in> set \<oplus> \<P> y'"
    using mmemD mPow_eq[OF y]
    unfolding y' mset_snd_eq'[OF y'(2)] x' by auto
  hence "x' \<in> \<P> y'" 
    using tmap_iff[OF tag_pmem[OF set_tag] pow_set[OF y'(2)] set_setmem[OF x'(2)]]   
    by auto
  hence "x' \<subseteq> y'" 
    using powD[OF y'(2)] by auto
  thus "mSubset x y"
    unfolding 
      mSubset_def 
      mmem_iff_eq[OF x x'(1)] 
      mmem_iff_eq[OF y y'(1)] 
    by auto
qed

lemma mpow_iff :
  assumes "x : mSet" "y : mSet"
  shows "x m m\<P> y \<longleftrightarrow> mSubset x y"
  using mpowI mpowD assms by auto

theorem msubset_eq :
  "mSubset x y = (m\<forall>a. a m x \<longrightarrow> a m y)"
  unfolding mall_def tall_def mSubset_def
  using mmem_m by auto

theorem mpow_ax : 
  "m\<forall>x : mSet. m\<forall>z : mSet. z m m\<P> x \<longleftrightarrow> mSubset z x" 
  unfolding mtall_def tall_def mall_def
  using mpow_iff by auto

theorem mpow_rsp :
  "x : M \<Longrightarrow> m\<P> x : M"
  using mset_m[OF msetof_mset[OF mpow_mset]]
        GZF_Model_mdefault_m
  unfolding mPow_def by auto

end
end