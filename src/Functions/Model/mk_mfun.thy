theory mk_mfun
  imports mapp
begin

declare [[names_short = true]]

context Function_Model begin

definition mFunMem :: \<open>'a \<Rightarrow> bool\<close>
  where "mFunMem b \<equiv> m\<exists>f : mFunc. m\<exists>c. mapp f b c \<or> mapp f c b"

lemma mfmemI :
  assumes f : "f : mFunc" 
      and "mapp f b c \<or> mapp f c b"
    shows "b : mFunMem" 
  using assms mfunc_m mapp_m
  unfolding mFunMem_def has_ty_def mtex_def mex_def tex_def by blast

lemma mfmemE : 
  assumes "b : mFunMem"
  obtains f c 
    where "f : mFunc" "mapp f b c \<or> mapp f c b"
  using assms 
  unfolding mFunMem_def has_ty_def mtex_def mex_def tex_def by blast

lemma mfmem_m :
  assumes b : "b : mFunMem"
    shows "b : M"
  by (rule mfmemE[OF b], use mapp_m in auto)

lemma mfmem_fmem :
  assumes b : "b : mFunMem"
  shows "b : FunMem"
proof (rule mfmemE[OF b])
  fix f c assume  
    f : "f : mFunc" and
    bc : "mapp f b c \<or> mapp f c b"
  hence 
    "snd f : Function" 
    "app (snd f) b c \<or> app (snd f) c b"
    using mfunc_snd_func mappD by auto
  thus "b : FunMem"
    using funmemI1 funmemI2 by auto
qed

lemma mfmem_ex :
  assumes b : "b : mFunMem"
  shows "\<not> Excluded func b"
proof (rule mfmemE[OF b])
  fix f c assume
    f : "f : mFunc" and mapp : "mapp f b c \<or> mapp f c b"
  then obtain f' j where
    f' : "f' : Function" and "f = <func, f'>"
    "j : Ord" and dom_ran : "dom f' \<subseteq> Tier j \<ominus> func" "ran f' \<subseteq> Tier j \<ominus> func"
    using mfuncE2 by auto
  hence "app f' b c \<or> app f' c b"
    using mapp mappD_pair f by auto
  hence "b \<in> dom f' \<or> b \<in> ran f'"
    using domI[OF f'] ranI[OF f'] by auto
  thus "\<not> Excluded func b"
    using exsetD2[OF tier_set[OF \<open>j : Ord\<close>]] dom_ran by auto
qed

lemma ex_mfmem :
  assumes b : "b : M" and b_ex : "\<not> Excluded func b"
      and b_fmem : "b : FunMem"
  shows "b : mFunMem"
proof (rule mfmemI[of \<open><func, \<lambda>c\<in>{b}. c>\<close>])
  let ?f = "<func, \<lambda>c\<in>{b}. c>"
  from b obtain j where 
    j:"j : Ord" and bx:"b \<in> Tier j" 
    using mE by auto
   hence 
    b_smem : "b : SetMem" and sng_fmem :"{b} : SetOf FunMem"
    using setmemI[OF tier_set[OF j] bx] sng_setof[OF _ b_fmem] by auto
  hence sng_lam_fun: "(\<lambda>c\<in>{b}. c) : Function"
    using lam_fun[OF sng_set[OF b_smem]] by auto
  hence memfun:"(\<lambda>c. c) : {b} \<leadsto> FunMem"
    using mem_funI setof_mem[OF sng_fmem] by auto
  hence dom_ran :"dom (\<lambda>c\<in>{b}. c) = {b}" "ran (\<lambda>c\<in>{b}. c) = {c | c \<in> {b}}"
    using lam_dom[OF sng_fmem] lam_ran[OF sng_fmem]
    by auto
  have "dom (\<lambda>c\<in>{b}. c) \<subseteq> Tier j \<ominus> func" "ran (\<lambda>c\<in>{b}. c) \<subseteq> Tier j \<ominus> func"
    unfolding dom_ran Subset_def  
    using repfunE[OF sng_set[OF b_smem]] sng_iff[OF b_smem] bx 
      exsetI[OF tier_set[OF j] _ b_ex] by (metis, metis)
  thus f:"?f : mFunc"
    using mfuncI[OF mI_mfunc[OF j sng_lam_fun]] by auto
  show "mapp \<langle>func,\<lambda>c\<in>{b}. c\<rangle> b b \<or> mapp \<langle>func,\<lambda>c\<in>{b}. c\<rangle> b b"
    unfolding mapp_def mfunc_snd_eq[OF f]
     lam_iff[OF sng_set[OF b_smem]] sng_iff[OF b_smem]
    using b_fmem by auto
qed

definition mFunPred :: \<open>['a, ['a,'a] \<Rightarrow> bool] \<Rightarrow> bool\<close>
  where "mFunPred x P \<equiv> m\<forall>b : mFunMem. b m x \<longrightarrow> (m\<exists>\<^sub>\<le>\<^sub>1 c : mFunMem. P b c)"

lemma mfpred_fpred : 
  assumes x : "x : mSet" and P : "P : mFunPred x"
    shows "(\<lambda>a b. P a b \<and> a : mFunMem \<and> b : mFunMem) : FunPred (snd x)"
proof (rule funpredI, unfold tuniq_def, rule, auto)
  fix b c d assume 
    b : "b : FunMem" "b : mFunMem" and "b \<in> snd x" and
    c : "c : FunMem" "c : mFunMem" "P b c" and
    d : "d : FunMem" "d : mFunMem" "P b d" 
  hence "b m x"
    using x unfolding mMem_def   
    by auto
  hence "m\<exists>\<^sub>\<le>\<^sub>1 c : mFunMem. P b c"
    using P  mmem_m b
    unfolding mFunPred_def has_ty_def mtall_def mall_def tall_def by auto
  thus "c = d"
    using c d mfmem_m
    unfolding mtuniq_def muniq_def tuniq_def Uniq_def by blast
qed
  
definition mk_mfun' :: \<open>['a, ['a,'a] \<Rightarrow> bool] \<Rightarrow> 'a\<close>
  where "mk_mfun' x P \<equiv> <func, mkfun (snd x) (\<lambda>a b. P a b \<and> a : mFunMem \<and> b : mFunMem)>"

definition mk_mfun :: \<open>['a, ['a,'a] \<Rightarrow> bool] \<Rightarrow> 'a\<close>
  where "mk_mfun x P \<equiv> if x : mSet \<and> P : mFunPred x
                       then mk_mfun' x P 
                       else Function_Model_mdefault"

lemma mk_mfun_eq :
  assumes "x : mSet" "P : mFunPred x"
  shows "mk_mfun x P = <func, mkfun (snd x) (\<lambda>a b. P a b \<and> a : mFunMem \<and> b : mFunMem)>"
  using assms 
  unfolding mk_mfun_def mk_mfun'_def
  by auto

lemma mk_mfun_typ :
  "mk_mfun : (\<Pi> x : mSet. mFunPred x \<rightarrow> mFunc)" 
proof (rule depfunI, rule funI, unfold mk_mfun_eq, rule mfuncI)
  fix x P assume
    x : "x : mSet" and P : "P : mFunPred x"
  define P' where "P' \<equiv> (\<lambda>a b. P a b \<and> a : mFunMem \<and> b : mFunMem)"
  let ?f = "mkfun (snd x) P'"
  have x' : "snd x : Set" and P' : "P' : FunPred (snd x)"
    unfolding P'_def
    using mset_snd_set[OF x] mfpred_fpred[OF x P] by auto
  hence f:"?f : Function"
    using mkfun_fun by auto
  hence app:"\<And>b c. app ?f b c \<Longrightarrow> b : mFunMem \<and> c : mFunMem"
    using mkfun_iff[OF x' P']  
    unfolding P'_def by auto
  hence "dom ?f : SetOf M" and "ran ?f : SetOf M"
    using setofI[OF dom_set[OF f]] setofI[OF ran_set[OF f]] 
          domE[OF f] ranE[OF f] mfmem_m by (meson, meson)
  then obtain i j where
    i : "i : Ord" and "dom ?f \<subseteq> Tier i" and
    j : "j : Ord" and "ran ?f \<subseteq> Tier j"
    using setof_m_tier by metis
  then obtain k where
    k : "k : Ord" and dom_ran :
    "dom ?f \<subseteq> Tier k" "ran ?f \<subseteq> Tier k"
    using linear_leq[OF i j] tier_increasing_leq[OF i j] tier_increasing_leq[OF j i]
          subset_trans by meson
  hence "dom ?f \<subseteq> Tier k \<ominus> func" "ran ?f \<subseteq> Tier k \<ominus> func"
    using domE[OF f] ranE[OF f] app
          exsetI[OF tier_set[OF k] _ mfmem_ex] 
    unfolding Subset_def by (meson, meson)
  thus "<func, mkfun (snd x) (\<lambda>a b. P a b \<and> a : mFunMem \<and> b : mFunMem)> : M"
    using mI_mfunc[OF k f]
    unfolding P'_def by auto
qed

lemmas mk_mfun_mfunc = funE[OF depfunE[OF mk_mfun_typ]]

lemma mk_mfun_typ_ax : 
  "m\<forall>x. x : mSet \<longrightarrow> (\<forall>P. P : mFunPred x \<longrightarrow> mk_mfun x P : mFunc)"
  using mk_mfun_mfunc
  unfolding mall_def tall_def by auto
  
lemma mk_mfun_iff :
  assumes x : "x : mSet" 
      and P : "P : mFunPred x"
    shows "mapp (mk_mfun x P) b c \<longleftrightarrow> 
      (b m x \<and> P b c \<and> b : mFunMem \<and> c : mFunMem)"
proof -
  define P' where "P' \<equiv> (\<lambda>a b. P a b \<and> a : mFunMem \<and> b : mFunMem)"
  from mk_mfun_mfunc[OF x P] have 
    f : "mk_mfun x P : mFunc" .
  have x':"snd x : Set" and P':"P' : FunPred (snd x)"
    using mset_snd_set[OF x] mfpred_fpred[OF x P] 
    unfolding P'_def by auto
  hence "mkfun (snd x) P' : Function"
    using mkfun_fun by auto
  
  show ?thesis
  proof (auto)
    assume "mapp (mk_mfun x P) b c"
    hence "app (mkfun (snd x) P') b c"
      using mfunc_snd_eq f
      unfolding mapp_def mk_mfun_eq[OF x P] P'_def
      by auto
    thus "b m x" "P b c" "b : mFunMem" "c : mFunMem"
      using mkfun_iff[OF x' P'] x
      unfolding P'_def mMem_def by auto
  next
    assume "b m x" "P b c" "b : mFunMem" "c : mFunMem"
    hence "app (mkfun (snd x) P') b c"
      using mkfun_iff[OF x' P'] mfmem_fmem
      unfolding P'_def mMem_def by auto
    thus "mapp (mk_mfun x P) b c"
      using mfunc_snd_eq f
      unfolding mapp_def mk_mfun_eq[OF x P] P'_def
      by auto
  qed
qed

lemma mk_mfun_ax : 
  "m\<forall>s : mSet. \<forall>P : mFunPred s. m\<forall>x y.
    mapp (mk_mfun s P) x y \<longleftrightarrow> (x m s \<and> P x y \<and> x : mFunMem \<and> y : mFunMem)"
  unfolding mtall_def mall_def tall_def
  using mk_mfun_iff by auto  
    
lemma mk_mfun_cong' : 
  assumes x : "x : mSet" 
      and P : "P : mFunPred x" 
      and Q : "Q : mFunPred x"
      and iff : "\<And>a b. a : M \<Longrightarrow> b : M \<Longrightarrow> P a b \<longleftrightarrow> Q a b" 
    shows "mk_mfun' x P = mk_mfun' x Q"
    unfolding mk_mfun'_def mk_mfun'_def
proof (rule pair_eqI[OF refl])
  have x' : "snd x : Set" and 
       P' : "(\<lambda>a b. P a b \<and> a : mFunMem \<and> b : mFunMem) : FunPred (snd x)" and
       Q' : "(\<lambda>a b. Q a b \<and> a : mFunMem \<and> b : mFunMem) : FunPred (snd x)"
    using mset_snd_set[OF x] mfpred_fpred[OF x P] mfpred_fpred[OF x Q] by auto
  show "mkfun (\<pi> x) (\<lambda>a b. P a b \<and> a : mFunMem \<and> b : mFunMem) =
        mkfun (\<pi> x) (\<lambda>a b. Q a b \<and> a : mFunMem \<and> b : mFunMem)"
  by (rule fun_eqI[OF mkfun_fun[OF x' P'] mkfun_fun[OF x' Q']],
      unfold mkfun_iff[OF x' P'] mkfun_iff[OF x' Q'], use mfmem_m iff in auto)
qed    

lemma mk_mfun_m : 
  "mk_mfun x P : M"
  using mfunc_m[OF mk_mfun_mfunc] Function_Model_mdefault_m
  unfolding mk_mfun_def by auto

lemma mfpred_cong :
  assumes "\<And>a b. a : M \<Longrightarrow> b : M \<Longrightarrow> P a b = Q a b"
  shows "mFunPred x P = mFunPred x Q"
  using assms  unfolding mFunPred_def has_ty_def 
      mtuniq_def muniq_def tuniq_def Uniq_def 
      mtall_def mall_def tall_def by blast
  
lemma mk_mfun_cong :
  assumes iff:"\<And>a b. a : M \<Longrightarrow> b : M \<Longrightarrow> P a b \<longleftrightarrow> Q a b" 
    shows "mk_mfun x P = mk_mfun x Q"
proof -
  have pq:"P : mFunPred x \<longleftrightarrow> Q : mFunPred x"
    using mfpred_cong iff
    unfolding has_ty_def by blast
  thus ?thesis
    unfolding mk_mfun_def
    using mk_mfun_cong' iff by auto
qed

theorem mk_mfun_rsp : 
  assumes "x : M" and iff : "\<And>x y. x : M \<Longrightarrow> y : M \<Longrightarrow> P x y \<longleftrightarrow> Q x y"
  shows "mk_mfun x P : M \<and> (mk_mfun x P = mk_mfun x Q)"
  using mk_mfun_m mk_mfun_cong iff by blast

end
end