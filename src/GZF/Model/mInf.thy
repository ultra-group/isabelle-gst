theory mInf
  imports mUnion
begin

context GZF_Model begin

subsection \<open>Empty Set\<close>

lemma memp_mset : "m\<emptyset> : mSet"
  unfolding mEmp_def
proof (rule msetI, rule mI_mset[OF zero_typ emp_set])
  show "\<emptyset> \<subseteq> Tier 0 \<ominus> set" 
    using empty_subsetI[OF tier_set[OF zero_typ]] 
    by auto
qed

lemma memp_empty : "\<not> b m m\<emptyset>"
  using mmem_iff memp_mset
  unfolding mEmp_def 
  by auto

lemma memp_ax : 
  "m\<forall>b. \<not> b m m\<emptyset>"
  using memp_empty by auto

subsection \<open>Successor Operation\<close>

lemma msng_mset : 
  assumes x: "x : mSet"
  shows "<set, {x}> : mSet"
proof (rule msetI)
  obtain j where 
    j : "j : Ord" and xj :"x \<in> Tier j"
    by (metis mE[OF mset_m[OF x]])
  hence "{x} \<subseteq> Tier j \<ominus> set"
    using sng_subset[OF mset_smem[OF x] tier_ex_set[OF j]]
          exsetI[OF tier_set[OF j] xj not_excluded_mset[OF x]] by auto
  thus "<set, {x}> : M"
    by (rule mI_mset[OF j sng_set[OF mset_smem[OF x]]])
qed

lemma mupair_msetof :
  assumes x : "x : mSet" and y : "y : mSet"
  shows "<set, {x,y}> : mSetOf mSet"
proof (rule setof_msetof)
  obtain i j where 
    "i : Ord" "x \<in> Tier i" 
    "j : Ord" "y \<in> Tier j"
    using mE[OF mset_m] x y by metis
  then obtain k where 
    k : "k : Ord" and xk : "x \<in> Tier k" and yk : "y \<in> Tier k"
    by (metis greatest_tier)
  hence "{x,y} \<subseteq> Tier k \<ominus> set" 
    using upair_subset[OF mset_smem mset_smem tier_ex_set[OF k]] x y
          exsetI[OF tier_set[OF k] _ not_excluded_mset] by metis
  thus "<set, {x,y}> : mSet" 
    using msetI[OF mI_mset[OF k upair_set[OF mset_smem mset_smem]]] 
          x y by metis  
  show "{x,y} : SetOf mSet"
    using setofI[OF upair_set[OF mset_smem[OF x] mset_smem[OF y]]] 
          upairE[OF mset_smem[OF x] mset_smem[OF y]] x y by auto
qed

lemmas mcons_msetof = mupair_msetof[OF _ msng_mset]
lemmas mcons_mset = msetof_mset[OF mcons_msetof]

lemma mSucc_eq : 
  assumes "x : mSet"
  shows "mSucc x = mUnion <set, {x, <set, {x}>}>"
  unfolding mSucc_def mSucc'_def mUnion'_def
  using mUnion_eq[OF mcons_msetof] assms by auto

lemma msucc_typ :
  "mSucc : mSet \<rightarrow> mSet" 
  by (rule funI, unfold mSucc_eq, rule munion_mset, 
      metis mcons_msetof)

lemmas msucc_mset = funE[OF msucc_typ]

lemma msucc_iff :
  assumes x : "x : mSet"
  shows "y m mSucc x \<longleftrightarrow> (y m x \<or> y = x)"
  unfolding mSucc_eq[OF x] munion_iff[OF mcons_msetof[OF x x]]
proof (rule, erule exE, erule conjE)
  fix z assume "z m <set, {x, <set, {x}>}>"
  hence z:"z \<in> {x, <set, {x}>}" 
    using mmem_iff_eq[OF mcons_mset[OF x x]] by auto
  assume yz : "y m z" 
  show "y m x \<or> y = x" 
  proof (rule upairE[OF mset_smem[OF x] mset_smem[OF msng_mset[OF x]] z])
    assume "z = x" thus "y m x \<or> y = x" 
      using yz by simp
  next
    assume "z = <set,{x}>" 
    hence "y \<in> {x}" 
      using yz mmem_iff_eq[OF msng_mset[OF x]] by auto
    thus "y m x \<or> y = x" 
      unfolding sng_iff[OF mset_smem[OF x]] ..
  qed
next
  assume "y m x \<or> y = x"
  thus "\<exists>z. z m \<langle>set,{x,\<langle>set,{x}\<rangle>}\<rangle> \<and> y m z"
  proof 
   assume "y m x" 
   moreover have "x m <set, {x, <set,{x}>}>" 
    using mmem_iff[OF mcons_mset[OF x x]]
          upairI1[OF mset_smem[OF x] mset_smem[OF msng_mset[OF x]]] by auto
   ultimately show "\<exists>z. z m <set, {x, <set,{x}>}> \<and> y m z"
    by auto
  next
    assume "y = x"
    hence "y m <set, {x}>"
      unfolding mmem_iff[OF msng_mset[OF x]]
      using sngI[OF mset_smem[OF x]] by auto
    moreover have "<set, {x}> m <set, {x, <set,{x}>}>"
      unfolding mmem_iff[OF mcons_mset[OF x x]]
          using upairI2[OF mset_smem[OF x] mset_smem[OF msng_mset[OF x]]] .
    ultimately show "\<exists>z. z m <set, {x, <set,{x}>}> \<and> y m z"
      by auto
  qed
qed

lemma msucc_ax : 
  "m\<forall>x:mSet. m\<forall>b. (b m mSucc x) = (b m x \<or> b = x)"
  unfolding mtall_def
  using msucc_iff by auto


subsection \<open>Model infinity witness\<close>

lemma Theta_lim_smem : 
  assumes \<mu>:"\<mu> : Limit" and tj:"\<forall>j : Ord. j < \<mu> \<longrightarrow> \<Theta> j : mSet"
  shows "\<Theta> : (predSet \<mu>) \<leadsto> SetMem"
proof (rule mem_funI)
  fix j assume "j \<in> predSet \<mu>" 
  hence "j : Ord" "j < \<mu>" 
    using predsetD[OF limit_ord[OF \<mu>]] by auto
  thus "\<Theta> j : SetMem"
    using tj mset_smem by auto
qed

(* lemma Theta_lim_fmem :
  assumes \<mu>:"\<mu> : Limit" and tj:"\<forall>j : Ord. j < \<mu> \<longrightarrow> \<Theta> j : mSet"
  shows "\<Theta> : (predSet \<mu>) \<leadsto> FunMem"
  by (rule mem_funI, rule smem_fmem,
      erule mem_funE[OF Theta_lim_smem[OF \<mu> tj]]) *)

lemma theta_tier : 
 assumes i:"j : Ord"
   shows "\<Theta> j : mSet ""\<Theta> j \<in> Tier (succ j)"
proof (induct rule: trans_induct3[OF i])
  have t0:"\<Theta> 0 = m\<emptyset>"
    unfolding ord_to_mvnord_def 
    using ordrec_0 by auto
  thus "\<Theta> 0 : mSet"
    using memp_mset  by auto 
  show "\<Theta> 0 \<in> Tier (succ 0)" 
    unfolding t0 mEmp_def 
    using tierI_mset[OF zero_typ emp_set] empty_subsetI[OF tier_ex_set[OF zero_typ]]
    by auto
next
  fix j assume j:"j : Ord" "\<Theta> j : mSet" "\<Theta> j \<in> Tier (succ j)"
  hence tj:"\<Theta> j \<in> Tier (succ j) \<ominus> set"
    using exsetI[OF tier_set[OF succ_ord[OF j(1)]] _ not_excluded_mset] by auto
  have tsucc:"\<Theta> (succ j) = mSucc (\<Theta> j)"
    unfolding ord_to_mvnord_def ordrec_succ[OF j(1)] ..
  thus "\<Theta> (succ j) : mSet"
    using msucc_mset[OF j(2)] by auto
  show "\<Theta> (succ j) \<in> Tier (succ (succ j))"
    unfolding tsucc
  proof (rule msetE[OF msucc_mset[OF j(2)]])
    fix x' assume x':"mSucc (\<Theta> j) = <set,x'>" "x' : Set"
    show "mSucc (\<Theta> j) \<in> Tier (succ (succ j))"
    proof (unfold x'(1), rule tierI_mset[OF succ_ord[OF j(1)] x'(2)], rule)
      fix a assume "a \<in> x'"
      hence "a m <set, x'>" 
        using x' mmem_iff_eq[OF msucc_mset[OF j(2)]] by auto
      hence "a m (\<Theta> j) \<or> a = \<Theta> j"
        using x'(1) msucc_iff[OF j(2)] by auto
      thus "a \<in> Tier (succ j) \<ominus> set"
      proof (rule)
        from msetE[OF j(2)] obtain y' where y':"\<Theta> j = <set, y'>" "y' : Set" by auto
        assume "a m (\<Theta> j)" 
        hence "a \<in> Tier j \<ominus> set"
           using mmem_tier[OF j(1)] j(3) unfolding y' by auto
        thus "a \<in> Tier (succ j) \<ominus> set" 
          using ex_subset1[OF tier_set[OF j(1)] tier_set[OF succ_ord[OF j(1)]] 
                              tier_subset_succ[OF j(1)] subset_refl] by auto
      next 
        assume "a = \<Theta> j"
        thus "a \<in> Tier (succ j) \<ominus> set" using tj by auto
      qed
    qed
  qed
next
  fix \<mu> assume u:"\<mu> : Limit" and tj:"\<forall>j : Ord. j < \<mu> \<longrightarrow> \<Theta> j : mSet \<and> \<Theta> j \<in> Tier (succ j)"
  hence t_mset: "\<forall>j : Ord. j < \<mu> \<longrightarrow> \<Theta> j : mSet" by auto
  have tu:"\<Theta> \<mu> = <set, { \<Theta> j | j < \<mu>}>"
    unfolding ord_to_mvnord_def ordrec_lim[OF u] 
      repfun_ordrec_lim_restrict[OF u] .. 
    
  have tfun:"(\<lambda>j<\<mu>. \<Theta> j) : Function" 
    using lam_fun[OF lim_predset_set[OF u]] by auto
  show "\<Theta> \<mu> \<in> Tier (succ \<mu>)" unfolding tu 
  proof (rule tierI_mset[OF limit_ord[OF u]])
    show "{ \<Theta> j | j < \<mu> } : Set" 
      using repfun_lim_set[OF u] by auto
    
    show "{ \<Theta> j | j < \<mu> } \<subseteq> Tier \<mu> \<ominus> set"
    proof (rule, erule repfunE[OF lim_predset_set[OF u]], 
           drule predsetD[OF limit_ord[OF u]], auto)
      fix i assume "i : Ord" "i < \<mu>"
      moreover hence "\<Theta> i : mSet" "\<Theta> i \<in> Tier (succ i)"
        using tj by auto
      ultimately have "\<Theta> i \<in> Tier \<mu>"
        using tier_limI1[OF u succ_ord limit_lt_succ[OF u]] 
        by auto
      thus "\<Theta> i \<in> Tier \<mu> \<ominus> set"
        using exsetI[OF tier_set[OF limit_ord[OF u]]]
              not_excluded_mset[OF \<open>\<Theta> i : mSet\<close>] by auto
    qed
  qed        
  thus "\<Theta> \<mu> : mSet"  
    using msetI[OF mI[OF succ_ord[OF limit_ord[OF u]]]]
    unfolding tu by metis
qed

lemma theta_lam_fun :
  assumes u:"\<mu> : Limit" 
  shows "(\<lambda>j<\<mu>. \<Theta> j) : Function" 
    using lam_fun[OF lim_predset_set[OF u]] by auto

lemma Theta_lim_setfun :
  assumes u:"\<mu> : Limit" 
  shows "\<Theta> : (predSet \<mu>) \<leadsto> SetMem" 
proof (rule mem_funI)
 fix j assume j:"j \<in> predSet \<mu>" 
 hence "j : Ord" "j < \<mu>" 
   using predsetD[OF limit_ord[OF u]] by auto
 thus "\<Theta> j : SetMem" using theta_tier mset_smem by auto
qed

(* lemma theta_fmem :
  assumes \<mu>:"\<mu> : Limit"
  shows "\<Theta> : (predSet \<mu>) \<leadsto> FunMem"
  using theta_tier Theta_lim_fmem[OF \<mu>] by auto *)


lemma Theta_eq :
  "\<Theta> \<omega> = <set, {\<Theta> i | i < \<omega>}>" 
   unfolding ordrec_lim[OF omega_typ] ord_to_mvnord_def
             repfun_ordrec_lim_restrict[OF omega_typ] ..

lemma minf_mset : "mInf : mSet"
  unfolding mInf_def 
  using theta_tier(1)[OF omega_ord] by simp

lemma minf_iff : "b m mInf \<longleftrightarrow> (\<exists>i<\<omega>. b = \<Theta> i)"
  using 
    mmem_iff_eq[OF minf_mset]
  unfolding 
    mInf_def Theta_eq 
  using
    repfun_iff[OF predset_set[OF omega_ord]]
    ord_ex_iff[OF omega_ord]
    mset_smem[OF theta_tier(1)] 
 by auto

lemma minf_msetof : 
  "mInf : mSetOf mSet"
proof (rule msetofI[OF minf_mset])
  fix b assume "b m mInf"
  thus "b : mSet"
    unfolding minf_iff
    using theta_tier by auto
qed

lemma memp_mem_minf : 
  "mEmp m mInf"
  unfolding minf_iff
proof (rule texI[OF zero_typ], auto)
  show "0 < \<omega>" 
    using omega_zero .
  show "m\<emptyset> = \<Theta> 0" 
    unfolding ord_to_mvnord_def
    using ordrec_0 by auto
qed

lemma msucc_mem_minf : 
  assumes x:"x m mInf"
  shows "mSucc x m mInf"
  unfolding minf_iff
proof -
  from x obtain i where
    i : "i : Ord" "i < \<omega>" "x = \<Theta> i"
    using minf_iff by auto
  hence "mSucc x = \<Theta> (succ i)"
    unfolding ord_to_mvnord_def
    using ordrec_succ[OF i(1)] by auto
  thus "\<exists>j: Ord. j < \<omega> \<and> mSucc x = \<Theta> j"
    using succ_ord omega_succ i by auto
qed

lemma minf_ax :
  "mEmp m mInf \<and> (m\<forall>a. a m mInf \<longrightarrow> mSucc a m mInf)" 
  using memp_mem_minf msucc_mem_minf by auto

theorem memp_rsp : 
  "m\<emptyset> : M"
  using mset_m[OF memp_mset] .

theorem msucc_rsp : 
  "x : M \<Longrightarrow> mSucc x : M"
  using mset_m[OF msucc_mset] GZF_Model_mdefault_m
  unfolding mSucc_def
  by auto

theorem minf_rsp : 
  "mInf : M"
  using mset_m[OF minf_mset] .

end
end
