theory mfspace
  imports mdom_mran
begin

context Function_Model begin

definition mfspace' :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where "mfspace' x y \<equiv> 
    <set, { <func, f> | f \<in> (snd x \<ominus> func) \<midarrow>p\<rightarrow> (snd y \<ominus> func) }>"

definition mfspace :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where "mfspace x y \<equiv> if x : mSet \<and> y : mSet 
                         then mfspace' x y 
                         else Function_Model_mdefault"

lemma mfspace_eq : 
  assumes x : "x : mSet" and y : "y : mSet"
    shows "mfspace x y \<equiv> 
    <set, { <func, f> | f \<in> (snd x \<ominus> func) \<midarrow>p\<rightarrow> (snd y \<ominus> func) }>"
  unfolding mfspace_def mfspace'_def
  using assms by auto

lemma mfspace_typ : 
  "mfspace : mSet \<rightarrow> mSet \<rightarrow> mSetOf mFunc"
proof (rule funI, rule funI, rule msetofI)
  thm mI_mset ex_func_set ex_func_set_subset
  fix x y assume 
    x : "x : mSet" and y : "y : mSet"
  then obtain i x' j y' where
    i : "i : Ord" and x_eq : "x = <set, x'>" and 
    x' : "x' : Set" and "x' \<subseteq> Tier i \<ominus> set" and
    j : "j : Ord" and y_eq : "y = <set,y'>" and
    y' : "y' : Set" and "y' \<subseteq> Tier j \<ominus> set"
    using mE_mset[OF mset_m] msetE by (metis)
  then obtain k where 
    k : "k : Ord" and "x' \<subseteq> Tier k" "y' \<subseteq> Tier k" 
    sorry
  hence 
    x'_sub : "x' \<ominus> func \<subseteq> Tier k \<ominus> func" and
    y'_sub : "y' \<ominus> func \<subseteq> Tier k \<ominus> func"
    using ex_subset3[OF x' tier_set[OF k], of func]
          ex_subset3[OF y' tier_set[OF k], of func]
    by auto
  
  have f_mem:"\<And>f. f \<in> { <func, f'> | f' \<in> (x' \<ominus> func) \<midarrow>p\<rightarrow> (y' \<ominus> func) } \<Longrightarrow> 
    f \<in> Tier (succ k) \<ominus> set \<and> f : mFunc"
  proof (rule, rule exsetI[OF tier_set[OF succ_ord[OF k]]])
    fix f assume 
      "f \<in> { <func, f'> | f' \<in> (x' \<ominus> func) \<midarrow>p\<rightarrow> (y' \<ominus> func) }"
    then obtain f' where
      f : "f = <func, f'>" and "f' \<in> (x' \<ominus> func) \<midarrow>p\<rightarrow> (y' \<ominus> func)"
      using repfunE[OF setof_set[OF fspace_setof[OF exset_set[OF x'] exset_set[OF y']]]]
      by metis
    hence "f' : Function" "dom f' \<subseteq> x' \<ominus> func" "ran f' \<subseteq> y' \<ominus> func" 
      using fspace_mem[OF exset_set[OF x'] exset_set[OF y']] 
            fspaceD[OF exset_set[OF x'] exset_set[OF y']] by auto
    thus "f \<in> Tier (succ k)"
      unfolding f
      using tierI_mfunc[OF k] subset_trans[OF _ x'_sub] subset_trans[OF _ y'_sub]
      by auto
    thus "f : mFunc"
      using mfuncI[OF mI[OF succ_ord[OF k]]]
      unfolding f by auto
    show "\<not> Excluded set f"
      using func_set_excluded func_not_excluded
      unfolding f subtyp_def has_ty_def by auto
  qed
  thus "mfspace x y : mSet"
    using msetI[OF mI_mset[OF succ_ord[OF k] 
      repfun_set[OF setof_set[OF 
        fspace_setof[OF exset_set[OF x', of func] exset_set[OF y', of func]]]] subsetI]]
    unfolding mfspace_eq[OF x y] 
    unfolding mset_snd_eq'[OF x'] mset_snd_eq'[OF y'] x_eq y_eq
    by auto
   
  fix f assume "f m mfspace x y"
  thus "f : mFunc"
    unfolding mfspace_eq[OF x y]
    unfolding x_eq y_eq mset_snd_eq'[OF x'] mset_snd_eq'[OF y']
    using f_mem mmemD by auto
qed

lemmas mfspace_msetof = funE[OF funE[OF mfspace_typ]]

lemma mfspace_typ_ax : 
  "m\<forall>x0. x0 : mSet \<longrightarrow> (m\<forall>x1. x1 : mSet \<longrightarrow> mfspace x0 x1 : mSetOf mFunc)"
  unfolding mall_def tall_def
  using mfspace_msetof by auto

lemma mfspace_iff :
  assumes x : "x : mSet" and y : "y : mSet"
      and f : "f : mFunc"
    shows "f m mfspace x y \<longleftrightarrow> mSubset (mdom f) x \<and> mSubset (mran f) y "
proof (auto)
  assume "f m mfspace x y"
  hence "f \<in> {<func, f'> | f' \<in> (snd x \<ominus> func) \<midarrow>p\<rightarrow> (snd y \<ominus> func)}"
    unfolding mfspace_eq[OF x y]
    using mmemD by auto
  then obtain f' where 
    "f = <func, f'>" "f' \<in> (snd x \<ominus> func) \<midarrow>p\<rightarrow> (snd y \<ominus> func)"
    using repfunE[OF setof_set[OF 
      fspace_setof[OF exset_set[OF mset_snd_set] exset_set[OF mset_snd_set], OF x y]]]
    by metis
  hence "dom f' \<subseteq> snd x \<ominus> func" "ran f' \<subseteq> snd y \<ominus> func"
    using fspaceD[OF exset_set[OF mset_snd_set] exset_set[OF mset_snd_set], OF x y]
    by auto
  hence dom:"dom (snd f) \<subseteq> snd x" and ran: "ran (snd f) \<subseteq> snd y"
    using mfunc_snd_eq f
      ex_subset2[OF dom_set[OF mfunc_snd_func[OF f]] mset_snd_set[OF x]]
      ex_subset2[OF ran_set[OF mfunc_snd_func[OF f]] mset_snd_set[OF y]]
    unfolding \<open>f = <func,f'>\<close>
    by auto
  show "mSubset (mdom f) x" 
  by (rule msubsetI, unfold mdom_eq[OF f], drule mmemD, 
      unfold mMem_def, use dom x in auto)
  show "mSubset (mran f) y" 
  by (rule msubsetI, unfold mran_eq[OF f], drule mmemD, 
      unfold mMem_def, use ran y in auto)
next
  obtain f' j where
    f' : "f' : Function" and f_eq : "f = <func, f'>" and
    j : "j : Ord" and dom :"dom f' \<subseteq> Tier j \<ominus> func" and 
    ran : "ran f' \<subseteq> Tier j \<ominus> func"
    using mfuncE2[OF f] .

  assume x_sub:"mSubset (mdom f) x" and y_sub: "mSubset (mran f) y"
  have "dom (snd f) \<subseteq> snd x" "ran (snd f) \<subseteq> snd y"
    using msubsetD[OF x_sub] msubsetD[OF y_sub] mmemI mMem_def
      mdom_mset[OF f] mran_mset[OF f]
    unfolding mdom_eq[OF f] mran_eq[OF f] 
    by auto
  hence "dom f' \<subseteq> snd x" "ran f' \<subseteq> snd y"
    using mfunc_snd_eq f 
    unfolding f_eq by auto
  hence "dom f' \<subseteq> snd x \<ominus> func" "ran f' \<subseteq> snd y \<ominus> func" 
    using dom ran
    unfolding Subset_def
      exset_iff[OF mset_snd_set[OF x]]
      exset_iff[OF mset_snd_set[OF y]]
      exset_iff[OF tier_set[OF j]] by auto
  hence "f' \<in> (snd x \<ominus> func) \<midarrow>p\<rightarrow> (snd y \<ominus> func)"
    using fspaceI[OF exset_set[OF mset_snd_set[OF x]],
                  OF exset_set[OF mset_snd_set[OF y]], OF f']
    by auto
  hence "f \<in> { <func, f'> | f' \<in> (snd x \<ominus> func) \<midarrow>p\<rightarrow> (snd y \<ominus> func)}"
    using repfunI[OF setof_set[OF fspace_setof],
                  OF exset_set[OF mset_snd_set[OF x]],
                  OF exset_set[OF mset_snd_set[OF y]]]
          pair_smem[OF m_pair[OF mfunc_m[OF f]]]
    unfolding f_eq by auto
  thus "f m mfspace x y"
    using mmemI msetof_mset[OF mfspace_msetof[OF x y]]
    unfolding mfspace_eq[OF x y] by auto
qed

lemma mfspace_ax :
  "m\<forall>x : mSet. m\<forall>y : mSet. m\<forall>f : mFunc.
    (f m mfspace x y) = (mSubset (mdom f) x \<and> mSubset (mran f) y)"
  unfolding mtall_def mall_def tall_def
  using mfspace_iff by auto

theorem mfspace_rsp : 
  "x : M \<Longrightarrow> y : M \<Longrightarrow> mfspace x y : M"
  using mset_m[OF msetof_mset[OF mfspace_msetof]] Function_Model_mdefault_m
  unfolding mfspace_def by auto


end
end