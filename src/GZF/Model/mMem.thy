theory mMem
  imports mSet 
begin

context GZF_Model begin

thm mMem_def

lemma mmemI :
  assumes 
    x' : "<set,x'> : mSet" and a : "a \<in> x'" 
  shows "a m <set, x'>"
  unfolding 
    mMem_def mset_snd_eq[OF x']
  using 
    assms 
  by auto

lemma mmemI_eq :
  assumes x : "x : mSet" "x = <set, x'>" 
      and a : "a \<in> x'" 
    shows "a m x"
  using mmemI[OF _ a] x by auto

lemma mmem_mset :
  "a m x \<Longrightarrow> x : mSet"
  unfolding mMem_def by auto

lemma mmemD :
  assumes a : "a m <set, x'>"
    shows "a \<in> x'"
  using 
    a mset_snd_eq
  unfolding 
    mMem_def 
  by auto

lemma mmemD_eq :
  assumes x : "x = <set, x'>" 
      and a : "a m x"
    shows "a \<in> x'"
  using a mset_snd_eq
  unfolding mMem_def x by auto

lemma mmemE : 
  assumes a : "a m x"
  obtains x' where "x = <set,x'>" "a \<in> x'"
  by (rule msetE[OF mmem_mset[OF a]],
      use mmemD a in auto)
        
lemma mmem_iff : 
  assumes x : "<set,x'> : mSet"
  shows "a m <set,x'> \<longleftrightarrow> a \<in> x'"
  using 
    mmemI[OF x] mmemD 
  by auto

lemma mmem_iff_eq : 
  assumes x: "x : mSet" "x = <set, x'>"
  shows "a m x \<longleftrightarrow> a \<in> x'"
  using mmem_iff x by auto
  
lemma mmem_tier :
  assumes j : "j : Ord" and x : "<set,x'> \<in> Tier (succ j)" 
      and a : "a m <set,x'>" 
    shows "a \<in> Tier j \<ominus> set"
 using 
  tierD_mset[OF j x] mmemD[OF a] 
 by auto

lemma mmem_m :
  assumes b : "b m x"
    shows "b : M"
proof (rule msetE[OF mmem_mset[OF b]], rule mE[OF mset_m[OF mmem_mset[OF b]]])
  fix x' i assume x:"x = <set,x'>" "x' : Set" "i : Ord" "x \<in> Tier i"
  hence "<set,x'> \<in> Tier (succ i)" using tier_succI1 by auto
  thus "b : M" using mI[OF _ exsetD1[OF tier_set mmem_tier]] b x by auto
qed
 
lemma msetofI :
  assumes "x : mSet" "\<And>b. b m x \<Longrightarrow> b : P"
  shows "x : mSetOf P"
  using assms
  unfolding mSetOf_def has_ty_def 
  by auto

lemma msetof_mset :
  assumes "x : mSetOf P"
  shows "x : mSet"
  using assms 
  unfolding mSetOf_def has_ty_def by auto

lemma msetof_mmem :
  assumes "x : mSetOf P" "b m x"
  shows "b : P"
  using assms mmem_m 
  unfolding mSetOf_def mall_def tall_def has_ty_def by auto

lemma msetof_iff :
  "x : mSetOf P \<longleftrightarrow> x : mSet \<and> (\<forall>b. b m x \<longrightarrow> b : P)"
  using mmem_m
  unfolding mSetOf_def mall_def tall_def has_ty_def by auto

lemma msetof_cong : "\<And>fun1 fun2. (\<And>x. x : M \<Longrightarrow> fun1 x = fun2 x) 
    \<Longrightarrow> (\<And>x. x : M \<Longrightarrow> mSetOf fun1 x = mSetOf fun2 x)"
 unfolding mSetOf_def mall_def tall_def has_ty_def 
          by auto


lemma msetmemI :
  assumes "b m x"
  shows "b : mSetMem" 
  using assms mset_m mmem_mset
  unfolding mSetMem_def has_ty_def mtex_def mex_def tex_def by auto

lemma msetmem_iff : 
  "b : mSetMem \<longleftrightarrow> (\<exists>x. b m x)"
  using msetmemI 
  unfolding mSetMem_def has_ty_def mtex_def mex_def tex_def by auto

lemma mset_pair_setof : 
  assumes x : "<set, x'> : mSetOf P" 
  shows "x' : SetOf P"
proof (rule setofI)
 from msetof_mset[OF x] have x_mset:"<set,x'> : mSet" by auto
 thus "x' : Set" using mset_pair_set[OF mset_m] by auto
 fix b assume "b \<in> x'"
 hence "b m <set,x'>" using mmemI[OF x_mset] by auto
 thus "b : P" using msetof_mmem[OF x] by auto
qed 

lemma setof_msetof :
  assumes x : "<set,x'> : mSet" 
      and x' : "x' : SetOf P"
    shows "<set, x'> : mSetOf P"
proof (rule msetofI[OF x])
  fix b 
  assume "b m <set,x'>" thus "b : P"
    unfolding mmem_iff[OF x]
    using setof_mem[OF x'] by auto
qed

lemma msetofE : 
  assumes x : "x : mSetOf P" 
  obtains x' where "x = <set,x'>" "x' : SetOf P"
  by (rule msetE[OF msetof_mset[OF x]], 
      metis mset_pair_setof x)

text \<open>Axiom of Extensionality\<close>
lemma mset_eq_iff :
  assumes x : "x : mSet" and y : "y : mSet"
      and iff : "\<forall>a. a m x \<longleftrightarrow> a m y"
    shows "x = y"
proof -
  obtain x' y' 
   where x': "x = <set,x'>" "x' : Set" 
     and y': "y = <set,y'>" "y' : Set" 
    by (metis msetE x y)
  hence "x' = y'" 
    using equality_iffI iff mmem_iff x y 
    by auto  
  thus "x = y" 
    unfolding x'(1) y'(1) by auto
qed 

theorem mext_ax :
  "m\<forall>x : mSet. m\<forall>y : mSet. 
    (m\<forall>a. a m x \<longleftrightarrow> a m y) \<longrightarrow> x = y"
  unfolding mall_def mtall_def tall_def
  using mset_eq_iff mmem_m by meson

lemma msmem_smem : 
  assumes b : "b : mSetMem" 
  shows "b : SetMem"
proof - 
  from b mmem_mset obtain x where 
    x : "x : mSet" and b : "b m x"
    unfolding msetmem_iff[of b] tex_def by auto
  then obtain x' where x' : "x = <set, x'>" "x' : Set"
    using msetE by auto
  hence bx:"b \<in> x'" using mmemD b by auto
  thus "b : SetMem" using setmemI[OF x'(2)] by auto
qed

lemma msmem_m :
  assumes b:"b : mSetMem"
  shows "b : M"
proof -
  from b mmem_mset obtain x where 
    x:"x : mSet" and bx:"b m x" 
    unfolding msetmem_iff tex_def by auto
  thus "b : M"
    using mmem_m by auto
qed

lemma msmem_not_excluded :
  assumes b:"b : mSetMem"
  shows "\<not> Excluded set b"
proof -
  from b obtain x where 
    x:"x : mSet" and bx:"b m x" 
    using msetmem_iff mmem_mset unfolding tex_def by auto
  obtain x' where "x = <set,x'>" "b \<in> x'"
    by (rule msetE[OF x], metis mmemD bx)
  then obtain j where "j : Ord" and "<set,x'> \<in> Tier (succ j)"
    using tier_succI1 mE[OF mset_m[OF x]] by metis
  hence "x' \<subseteq> Tier j \<ominus> set"
    using tierD_mset by auto
  thus "\<not> Excluded set b"
    using exsetD2[OF tier_set[OF \<open>j : Ord\<close>]] \<open>b \<in> x'\<close> by auto
qed

lemma not_excluded_msmem :
  assumes b : "b : M" and b_ex  : "\<not> Excluded set b"
  shows "b : mSetMem"
proof (rule msetmemI[of _ \<open><set, {b}>\<close>], rule mmemI)
  from b obtain j where 
    j:"j : Ord" and bx:"b \<in> Tier j" 
    using mE by auto
  moreover hence "b : SetMem"
    using setmemI[OF tier_set[OF j] bx] by auto
  moreover thus "b \<in> {b}"
    using sng_iff by auto
  ultimately have "{b} \<subseteq> Tier j \<ominus> set"
    using sng_iff exsetI[OF tier_set[OF j] _ b_ex] by auto
  hence "<set, {b}> \<in> Tier (succ j)"
    using tierI_mset[OF j sng_set[OF \<open>b : SetMem\<close>]] by auto
  thus "<set, {b}> : mSet"
    using msetI[OF mI[OF succ_ord[OF j]]] by auto
qed


end
end