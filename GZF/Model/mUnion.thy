theory mUnion
  imports mMem
begin

context GZF_Model begin

lemma mUnion_eq : 
  assumes x : "x : mSetOf mSet"
  shows "m\<Union> x = <set, \<Union> y \<in> snd x. snd y>"
  unfolding mUnion_def mUnion'_def
  using x by auto

lemma munion_typ : 
  "m\<Union> : mSetOf mSet \<rightarrow> mSet" 
proof (rule funI, unfold mUnion_eq, rule msetI)
  fix x assume x_setof:"x : mSetOf mSet"
  hence x : "x : mSet" and x_mem : "\<forall>b. b m x \<longrightarrow> b : mSet" 
    using msetof_iff by auto
  then obtain x' where 
    x':"x = <set,x'>" "x' : Set" using msetE by metis
  then obtain j where 
   j: "j : Ord" "<set,x'> \<in> Tier j"
    using mE[OF mset_m[OF x]] by auto
  hence "<set,x'> \<in> Tier (succ (succ j))" 
    using tier_succI1 succ_ord by auto
  hence x'_sub : "x' \<subseteq> Tier (succ j)" 
    using tierD_mset[OF succ_ord[OF j(1)]] ex_subset2[OF x'(2) tier_set[OF succ_ord[OF j(1)]]] by auto
  have x'_mem : "\<forall>y. y \<in> x' \<longrightarrow> y : mSet"
    using x_mem mmem_iff_eq[OF x x'(1)] 
    unfolding x' by auto
    
  have "\<Union> {snd y | y \<in> snd x} \<subseteq> Tier j \<ominus> set"
    unfolding x'(1) mset_snd_eq'[OF x'(2)]  
  proof
    fix b assume "b \<in> \<Union> {snd y | y \<in> x'}"
    then obtain y where "b \<in> snd y" "y \<in> x'" 
      using repfun_union[OF _ snd_replfun] mset_pair_setof x_setof x' by auto
    hence "y : mSet" "y \<in> Tier (succ j)" 
      using x'_sub x'_mem by auto
    moreover then obtain y' where y':"y = <set,y'>" "y' : Set" 
      using msetE by auto
    ultimately have "y' \<subseteq> Tier j \<ominus> set" using tierD_mset[OF j(1)] by auto
    thus "b \<in> Tier j \<ominus> set" using \<open>b \<in> snd y\<close> y' mset_snd_eq' by auto
  qed
  moreover have "\<Union> {snd y | y \<in> snd x} : Set"
    using union_set[OF repfun_setof[OF _ snd_replfun]] 
          mset_pair_setof x_setof x' mset_snd_eq' by auto
  ultimately show "<set, \<Union> {snd y | y \<in> snd x}> : M" 
    using mI_mset[OF j(1)] by auto 
qed

lemmas munion_mset = funE[OF munion_typ]

lemma munionI : 
  assumes x : "x : mSetOf mSet" 
      and y : "y m x" 
      and a : "a m y"
    shows "a m m\<Union> x"
proof (rule msetE[OF msetof_mset[OF x]])
  fix x' assume x':"x = <set,x'>" "x' : Set"
  obtain y' where y': "y = <set, y'>" "y' : Set" 
    using msetE[OF msetof_mmem[OF x y]] by auto
  have x'_setof : "x' : SetOf mSet"
    using mset_pair_setof x' x by auto

     thm mmemI_eq[OF munion_mset[OF x]]
  show "a m m\<Union> x"
  proof (rule mmemI_eq[OF munion_mset[OF x]],
         unfold mUnion_eq[OF x], simp)
    
    from a have "a \<in> snd y" 
      using mmemD_eq[OF y'(1) a] mmem_mset[OF a] mset_snd_eq y' by auto
    moreover have "y \<in> x'" 
      using mmemD_eq[OF x'(1) y]   by auto
    ultimately show "a \<in> \<Union> { snd y | y \<in> snd x }"
      unfolding mset_snd_eq'[OF x'(2)] x'(1)
      using repfun_union[OF x'(2) snd_replfun[OF x'_setof]] 
      by auto
   qed
qed

lemma munionE : 
  assumes x : "x : mSetOf mSet"
      and a : "a m m\<Union> x"
  obtains y where "y m x" "a m y"
proof (rule msetofE[OF x])
  fix x' assume x':"x = <set,x'>" "x' : SetOf mSet"
  hence "a \<in> \<Union> RepFun x' \<pi>"
    using a mmemD mUnion_eq[OF x]
    unfolding x' mset_snd_eq'[OF setof_set[OF x'(2)]]  by auto
  then obtain y where "y \<in> x'" "a \<in> snd y" 
    using repfun_union[OF setof_set[OF x'(2)] snd_replfun[OF x'(2)]]
    by auto
  then obtain y' where "y = <set,y'>" "y' : Set" "a \<in> y'"
    using msetE[OF setof_mem[OF x'(2)]] mset_snd_eq' by metis
  
  have "x : mSet" using msetof_mset[OF x] .
  have "y m x" "a m y" 
    using mmemI_eq[OF \<open>x : mSet\<close> x'(1) \<open>y \<in> x'\<close>]
          mmemI[OF msetI[OF mmem_m] \<open>a \<in> y'\<close>] \<open>y = <set,y'>\<close>
    by auto
  thus ?thesis ..
qed

lemma munion_iff : 
  assumes x : "x : mSetOf mSet"
  shows "b m m\<Union> x \<longleftrightarrow> (\<exists>y. y m x \<and> b m y)"
  using munionI[OF x] munionE[OF x] by metis

theorem munion_ax :
  "m\<forall>x : mSetOf mSet. m\<forall>b. b m m\<Union> x \<longleftrightarrow> (m\<exists>y. y m x \<and> b m y)"
  unfolding mtall_def mall_def tall_def mex_def tex_def
  using munion_iff mmem_m by blast

theorem munion_rsp : 
  "x : M \<Longrightarrow> m\<Union> x : M"
  using mset_m[OF munion_mset] GZF_Model_mdefault_m 
  unfolding mUnion_def by auto
  
end
end