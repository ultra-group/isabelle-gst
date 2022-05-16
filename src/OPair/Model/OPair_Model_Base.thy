theory OPair_Model_Base
  imports "../CartProd" "../../ModelKit/ModelComponents"
begin 

context ModelBase begin
ML \<open>val pair_model = mcomp 
  { name = "OPair_Model",
    deps = mcomps [],
    variant = SOME (vari
      { tag_name = "opair",
          vcases =
            (\<^term>\<open>\<emptyset>\<close>,
             \<^term>\<open>(\<lambda>_ y. y \<times> y) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>,
             \<^term>\<open>(\<lambda>_ _. \<emptyset>) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a \<close>),
       alpha_typ = \<^term>\<open>Pair\<close> }),
    excludes_formulas = 
      [("opair_not_excluded", \<^prop>\<open>\<not> Excluded opair <opair,p'>\<close>)] }\<close>
end

local_setup \<open>snd o (mk_mcomp_class pair_model)\<close>

context OPair_Model begin

definition mPair :: \<open>'a \<Rightarrow> bool\<close>
  where \<open>mPair \<equiv> M \<triangle> (\<^enum> opair)\<close>

definition mpair' :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where "mpair' b c \<equiv> <opair, <b,c>>"

(*Redefine as b : M \<and> \<not> Excluded b opair *)
definition mPairMem :: \<open>'a \<Rightarrow> bool\<close>
  where "mPairMem \<equiv> M \<oslash> opair"

definition mpair :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where "mpair x y \<equiv> 
    if \<not> x : mPairMem then 
      if \<not> OPair_Model_mdefault : mPair 
      then OPair_Model_mdefault else x 
    else
      if \<not> y : mPairMem then
        if \<not> OPair_Model_mdefault : mPair 
        then OPair_Model_mdefault else y
      else mpair' x y"

lemma mpair_eq :
  assumes "b : mPairMem" "c : mPairMem"
    shows "mpair b c = <opair, <b,c>>"
  unfolding mpair_def mpair'_def using assms by auto

theorem variants_opair : 
  shows "Variants opair 0 \<emptyset> = \<emptyset>"
    and "j : Ord   \<Longrightarrow> Variants opair (succ j) y = y \<times> y"
    and "u : Limit \<Longrightarrow> Variants opair u f = \<emptyset>"
 using v_opair_0 v_opair_succ v_opair_limit by auto

theorem tierI_mpair :
  assumes j : "j : Ord"
      and b : "b \<in> Tier j \<ominus> opair" 
      and c : "c \<in> Tier j \<ominus> opair"  
    shows "mpair' b c \<in> Tier (succ j)" 
    unfolding mpair'_def
proof -
  have "<b,c> \<in> (Tier j \<ominus> opair) \<times> (Tier j \<ominus> opair)"
    using cprodI[OF tier_ex_set[OF j, of opair] 
                    tier_ex_set[OF j, of opair] b c]
    by auto
  hence "<b,c> \<in> Variants opair (succ j) (Tier j \<ominus> opair)"
    unfolding variants_opair(2)[OF j] .
  thus "<opair, <b,c>> \<in> Tier (succ j)"
    using tier_succI2[OF opair_tag j] by auto
qed

theorem tierD_mpair :
  assumes j : "j : Ord"
      and bc : "<opair,<b,c>> \<in> Tier (succ j)"
    shows "b \<in> Tier j \<ominus> opair \<and> c \<in> Tier j \<ominus> opair"
proof (rule tier_succE_pair[OF j bc])
  show "\<langle>opair,\<langle>b,c\<rangle>\<rangle> \<in> Tier j \<Longrightarrow>
    b \<in> Tier j \<ominus> opair \<and> c \<in> Tier j \<ominus> opair"
  proof (induct rule: trans_induct3[OF j])
    case 1
    then show ?case
      using tier0D(2) variants_opair(1) by auto
  next
    case IH:(2 j)
    show ?case
    proof (rule tier_succE_pair[OF IH(1,3)])
      assume "<opair,<b,c>> \<in> Tier j"
      hence "b \<in> Tier j \<ominus> opair \<and> c \<in> Tier j \<ominus> opair"
        using IH(2) by auto
      thus "b \<in> Tier (succ j) \<ominus> opair \<and>
            c \<in> Tier (succ j) \<ominus> opair"
          using tier_ex_subset_succ[OF IH(1)] by auto
    next
      assume "<b,c> \<in> Variants opair (succ j) (Tier j \<ominus> opair)"
      hence "b \<in> (Tier j \<ominus> opair) \<and> c \<in> (Tier j \<ominus> opair)"
        unfolding variants_opair(2)[OF IH(1)] 
        using cprodD1 cprodD2 tier_ex_set[OF IH(1), of opair] by auto
      thus "b \<in> (Tier (succ j) \<ominus> opair) \<and> c \<in> (Tier (succ j) \<ominus> opair)"
        using tier_ex_subset_succ[OF IH(1), of opair] by auto
    qed
  next
    case IH:(3 \<mu>)
    show ?case 
    proof (rule tier_limE_pair[OF IH(1,3)])
      fix j assume 
        "j : Ord" "j < \<mu>" "<opair, <b,c>> \<in> Tier j"
      hence "b \<in> Tier j \<ominus> opair \<and> c \<in> Tier j \<ominus> opair"
        using IH(2) by auto
      thus "b \<in> Tier \<mu> \<ominus> opair \<and> c \<in> Tier \<mu> \<ominus> opair"
        using tier_limit_ex_subset[OF IH(1) \<open>j : Ord\<close> \<open>j < \<mu>\<close>] by auto
    next
      show "\<langle>b,c\<rangle> \<in> Variants opair \<mu> (\<lambda>j<\<mu>. Tier j \<ominus> opair) \<Longrightarrow>
              b \<in> Tier \<mu> \<ominus> opair \<and> c \<in> Tier \<mu> \<ominus> opair" 
      unfolding variants_opair(3)[OF IH(1)] by auto
    qed  
  qed
next
  assume "\<langle>b,c\<rangle> \<in> Variants opair (succ j) (Tier j \<ominus> opair)"
  thus "b \<in> (Tier j \<ominus> opair) \<and> c \<in> (Tier j \<ominus> opair)"
    unfolding variants_opair(2)[OF j] 
    using cprodD1 cprodD2 tier_ex_set[OF j, of opair] by auto
qed

lemma tierE_mpair : 
  assumes j : "j : Ord"
      and p : "<opair, p'> \<in> Tier (succ j)" 
  obtains b c where 
    "p' = <b,c>" "b \<in> Tier j \<ominus> opair" "c \<in> Tier j \<ominus> opair"
proof - 
  from tier_mem_depsum[OF succ_ord[OF j] p] 
    have "<opair, p'> : (\<Sigma> i : Tag. \<alpha> i)" .
  hence "p' : Pair"
    using alpha_opair depsumD_pair by metis
  then obtain b c where 
    p':"p' = <b,c>" using proj_eq by metis
  moreover have 
    "b \<in> Tier j \<ominus> opair" "c \<in> Tier j \<ominus> opair"      
    using tierD_mpair[OF j] p 
    unfolding p' by auto
  ultimately show ?thesis ..
qed 

ML \<open>val mOPair =
  mk_msig [] "mOPair" \<^class>\<open>OPair\<close>
  ["mPair", "mpair", "mPairMem", "OPair_Model_mdefault"] \<^context>\<close>

lemma mpmemI :
  assumes "j : Ord" "b \<in> Tier j \<ominus> opair"
    shows "b : mPairMem" 
  using assms mI_ex
  unfolding mPairMem_def by auto

lemma mpmemE : 
  assumes "b : mPairMem"
  obtains j 
    where "j : Ord" "b \<in> Tier j \<ominus> opair"
  using assms unfolding mPairMem_def by (blast elim: mE_ex)

lemma mPair_mpmem : "p : mPair \<Longrightarrow> p : mPairMem" 
proof -
  assume "p : mPair"
  then obtain i p' where 
    "i : Ord" "p \<in> Tier i" "p = <opair, p'>"
    using mE partE
    unfolding mPair_def inter_ty_def has_ty_def by metis
  hence "p \<in> Tier i \<ominus> opair"
    using exsetI[OF tier_set[OF \<open>i : Ord\<close>], of _ opair]  
          opair_not_excluded by auto
  thus "p : mPairMem"
    using mpmemI[OF \<open>i : Ord\<close>] by simp
qed

lemma mpair_mpmem : 
  assumes "mpair b c : mPair"
  shows "b : mPairMem \<and> c : mPairMem"
proof (rule ccontr, auto)
  assume b:"\<not> b : mPairMem"
  hence "\<not> mpair b c : mPair"
    using mPair_mpmem
    unfolding mpair_def by auto
  thus "False" using assms ..
next
  assume b:"\<not> c : mPairMem"
  hence "\<not> mpair b c : mPair"
    using mPair_mpmem
    unfolding mpair_def by auto
  thus "False" using assms ..
qed

corollary mpmem_m : 
  "b : mPairMem \<Longrightarrow> b : M" 
  unfolding mPairMem_def
  by (rule extypD1)

lemma mpair_m :
  "p : mPair \<Longrightarrow> p : M"
  unfolding mPair_def by (rule intE1)

lemma mpairI :
  assumes "<opair, p'> : M"
  shows "<opair,p'> : mPair"
  using assms partI m_pair
  unfolding mPair_def inter_ty_def has_ty_def by auto
  
corollary mpmem_pmem :
  "b : mPairMem \<Longrightarrow> b : PairMem"
  using m_pair[OF mpmem_m] pair_pairmem proj_eq' by metis

theorem mpair_typ :
  "mpair : mPairMem \<rightarrow> mPairMem \<rightarrow> mPair \<triangle> mPairMem"
proof (rule funI, rule funI, rule intI)
  fix b c assume 
    b:"b : mPairMem" and c:"c : mPairMem"
  then obtain i j where
    ij : "i : Ord" "j : Ord"
    and "b \<in> Tier i \<ominus> opair" "c \<in> Tier j \<ominus> opair"
    using mpmemE by metis
  then obtain k where
    "k : Ord" "b \<in> Tier k \<ominus> opair" "c \<in> Tier k \<ominus> opair"
    using greatest_tier[OF ij] exset_iff[OF tier_set] by metis
  hence p : "mpair b c \<in> Tier (succ k)"
    using tierI_mpair 
    unfolding mpair_eq[OF b c] mpair'_def by auto
  hence "mpair b c : M" "mpair b c :\<^enum> opair"
    using mI[OF succ_ord[OF \<open>k : Ord\<close>]] 
          partI_pair[OF m_pair] 
    unfolding mpair_eq[OF b c] by auto 
  thus "mpair b c : mPair"
    unfolding mPair_def by (rule intI)
   
  let ?p = "mpair b c"
  have "?p \<in> Tier (succ k) \<ominus> opair"
    using exsetI[OF tier_set[OF succ_ord[OF \<open>k : Ord\<close>]] p] 
          opair_not_excluded 
    unfolding mpair_eq[OF b c] by auto
  thus "?p : mPairMem"
    using mpmemI[OF succ_ord[OF \<open>k : Ord\<close>]] by simp
qed

corollary mpair_typ_ax :
  "m\<forall>x. x : mPairMem \<longrightarrow> (m\<forall>x. x : mPairMem \<longrightarrow>
    mpair x x : mPair \<triangle> mPairMem)"
   using mpair_typ
   unfolding fun_ty_def mall_def tall_def has_ty_def 
   by auto

lemma mpair_iff :
  assumes b : "b : mPairMem" and c : "c : mPairMem"
      and u : "u : mPairMem" and v : "v : mPairMem"
  shows "mpair b c = mpair u v \<longleftrightarrow> (b = u \<and> c = v)"
proof -
  have 
    "<b,c> : Pair" "<u,v> : Pair"
    using mpmem_pmem pair_pair assms by auto
  moreover hence 
    "<opair, <b,c>> : Pair" "<opair,<u,v>> : Pair"
    using pair_pair[OF tag_pmem[OF opair_tag] pair_pmem] by auto
  ultimately show ?thesis
    unfolding mpair_eq[OF b c] mpair_eq[OF u v]
    by (simp add: pair_iff_eq) 
qed

corollary mpair_iff_ax :
  "m\<forall>a : mPairMem. m\<forall>b : mPairMem.
    m\<forall>c : mPairMem. m\<forall>d : mPairMem.
      (mpair a b = mpair c d) = (a = c \<and> b = d)"
  using mpair_iff 
  unfolding mtall_def mall_def by auto
 
lemma mpair_proj :
  assumes "p : mPair"
  obtains b c where 
    "b : mPairMem" "c : mPairMem ""p = mpair b c"
proof -
  from assms have "p : M" "p :\<^enum> opair" 
    unfolding mPair_def by unfold_typs
  then obtain j p' where 
    j : "j : Ord" and p : "p \<in> Tier j" and
    p_eq : "p = <opair,p'>"
    using mE partE by metis
  hence "<opair, p'> \<in> Tier (succ j)"
    using tier_succI1 by auto
  then obtain b c where
    "p' = <b,c>" "b \<in> Tier j \<ominus> opair" "c \<in> Tier j \<ominus> opair" 
    using tierE_mpair[OF j] by metis
  hence bc : "b : mPairMem" "c : mPairMem"
    using mpmemI[OF j] by auto
  moreover hence "p = mpair b c"
    using p_eq
    unfolding mpair_eq[OF bc] \<open>p' = <b,c>\<close> by auto
  ultimately show ?thesis ..
qed

corollary mpair_proj_ax :
  "m\<forall>p : mPair. m\<exists>a b. p = mpair a b"
  unfolding mtall_def mall_def mex_def tex_def
  by (auto, erule mpair_proj, use mpmem_m in auto)

theorem mpmem_ax :
  "m\<forall>b. mPairMem b = (m\<exists>p : mPair. m\<exists>c. p = mpair b c \<or> p = mpair c b)" 
proof (rule, rule)
  fix b let ?p = "mpair b b"
  assume b_pmem : "mPairMem b"
  then obtain j where 
    j: "j : Ord" and b:"b \<in> Tier j \<ominus> opair"
    using mpmemE unfolding has_ty_def by auto
  hence "mpair' b b \<in> Tier (succ j)" 
    using tierI_mpair by auto
  hence "?p \<in> Tier (succ j)"
    using mpair_eq b_pmem 
    unfolding mpair'_def has_ty_def by auto
  hence "?p : M" "?p : mPair" "b : M"
    using mpair_eq mpairI b_pmem mI[OF succ_ord[OF j]] mpmem_m
    unfolding has_ty_def by auto
  thus "(m\<exists>p : mPair. m\<exists>c. p = mpair b c \<or> p = mpair c b)"
    unfolding mtex_def mex_def tex_def by blast
next
  fix b assume "b : M" 
    "m\<exists>p : mPair. m\<exists>c. p = mpair b c \<or> p = mpair c b"
  then obtain p c where 
    "p : mPair" "c : M" "p = mpair b c \<or> p = mpair c b"
    unfolding mtex_def mex_def tex_def by auto
  thus "mPairMem b"
    using mpair_mpmem
    unfolding has_ty_def by auto
qed
      
translate_axioms mOPair_axioms : mOPair
  by (rule mpair_typ_ax, rule mpair_iff_ax, 
      rule mpair_proj_ax, rule mpmem_ax)

end