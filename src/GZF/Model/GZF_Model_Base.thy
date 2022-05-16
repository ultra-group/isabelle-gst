theory GZF_Model_Base
  imports "../../ModelKit/ModelComponents"
begin

hide_const set ZFC_in_HOL.set

context ModelBase' begin
ML \<open>val set_model = mcomp
 { name = "GZF_Model", 
   deps = mcomps [], 
   variant = SOME (vari 
    { tag_name = "set",
      vcases = 
        (@{term \<open>\<emptyset>\<close>}, 
         @{term "(\<lambda>_ x. \<P> x) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"}, 
         @{term "(\<lambda>_ _. \<emptyset>) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"}),
       alpha_typ = @{term "Set"}
    }),
  excludes_formulas =
    [("not_set_excluded_mset", @{prop \<open>\<not> Excluded set <set, x'>\<close>})]
 }\<close>
end
local_setup \<open>snd o (mk_mcomp_class set_model)\<close>

lemma gzf_model_case_typ :
  assumes j : "j : Ord" and x : "x : Set" 
  shows "caseof_ord \<emptyset> (\<P> x) \<emptyset> j : SetOf Set"
  by (rule case_ordE[OF j], 
      use emp_set pow_setof[OF x] emp_setof in auto)

context GZF_Model begin

definition mSet :: \<open>'a \<Rightarrow> bool\<close>
  where "mSet \<equiv> M \<triangle> (\<^enum> set)"

definition mMem :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>m\<close> 50) 
where "x m y \<equiv> y : mSet \<and> x \<in> snd y"

definition mSetMem :: \<open>'a \<Rightarrow> bool\<close>
  where "mSetMem b \<equiv> m\<exists>x : mSet. b m x"

definition mSubset :: \<open>['a, 'a] \<Rightarrow> bool\<close>
  where "mSubset x y \<equiv> m\<forall>a. a m x \<longrightarrow> a m y"

definition mSetOf :: \<open>['a \<Rightarrow> bool, 'a] \<Rightarrow> bool\<close>
  where "mSetOf P x \<equiv> x : mSet \<and> (m\<forall>b. b m x \<longrightarrow> b : P)"

definition mReplPred :: \<open>['a, ['a,'a] \<Rightarrow> bool] \<Rightarrow> bool\<close>
  where "mReplPred x P \<equiv> m\<forall>a. a m x \<longrightarrow> (m\<exists>\<^sub>\<le>\<^sub>1 b : mSetMem. P a b)" 

definition mUnion' :: \<open>'a \<Rightarrow> 'a\<close> 
  where "mUnion' x \<equiv> <set, \<Union> y \<in> snd x. snd y>"

definition mUnion :: \<open>'a \<Rightarrow> 'a\<close> (\<open>m\<Union>\<close>)
  where "m\<Union> x \<equiv> if x : mSetOf mSet then mUnion' x
                                    else GZF_Model_mdefault"

definition mPow' :: \<open>'a \<Rightarrow> 'a\<close> 
  where "mPow' x \<equiv> <set, set \<oplus> \<P> (snd x)>"

definition mPow :: \<open>'a \<Rightarrow> 'a\<close> (\<open>m\<P>\<close>)
  where "m\<P> x \<equiv> if x : mSet then mPow' x 
                            else GZF_Model_mdefault"

definition mEmp :: \<open>'a\<close> (\<open>m\<emptyset>\<close>)
  where "mEmp = <set, \<emptyset>>" 

definition mSucc' :: \<open>'a \<Rightarrow> 'a\<close>
  where "mSucc' x = mUnion' <set, {x, <set, {x}>}>"

definition mSucc :: \<open>'a \<Rightarrow> 'a\<close> 
  where "mSucc x \<equiv> if x : mSet then mSucc' x
                      else GZF_Model_mdefault"

definition ord_to_mvnord :: \<open>'a \<Rightarrow> 'a\<close> (\<open>\<Theta>\<close>)
  where \<open>\<Theta> \<equiv> OrdRec (\<lambda>\<mu> f. <set, {f j | j < \<mu>}>) (\<lambda>_ x. mSucc x) m\<emptyset>\<close>

definition mInf :: \<open>'a\<close>
  where \<open>mInf \<equiv> \<Theta> \<omega>\<close>

definition mRepl' :: \<open>['a, ['a,'a] \<Rightarrow> bool] \<Rightarrow> 'a\<close> 
  where "mRepl' x P \<equiv> <set, { b | \<exists> a \<in> snd x. P a b \<and> b : mSetMem }>" 

definition mRepl :: \<open>['a, ['a,'a] \<Rightarrow> bool] \<Rightarrow> 'a\<close> (\<open>m\<R>\<close>)
  where "m\<R> x P \<equiv> if x : mSet \<and> P : mReplPred x 
                    then mRepl' x P else GZF_Model_mdefault"

theorem variants_set :
  shows "Variants set 0 \<emptyset> = \<emptyset>"
    and "j : Ord   \<Longrightarrow> Variants set (succ j) x = \<P> x"
    and "\<mu> : Limit \<Longrightarrow> Variants set \<mu> f = \<emptyset>"
  using v_set_0 v_set_succ v_set_limit by auto

theorem tierI_mset :
  assumes j : "j : Ord" and x' : "x' : Set"
      and x'_sub: "x' \<subseteq> Tier j \<ominus> set"
    shows "<set,x'> \<in> Tier (succ j)"
proof -
  have "x' \<in> \<P> (Tier j \<ominus> set)" 
    by (rule powI[OF x' tier_ex_set[OF j] x'_sub])
  hence "x' \<in> Variants set (succ j) (Tier j \<ominus> set)"
    unfolding variants_set(2)[OF j] by assumption
  thus "<set,x'> \<in> Tier (succ j)" 
    by (rule tier_succI2[OF set_tag j])
qed


theorem tierD_mset : 
  assumes j : "j : Ord" 
      and x : "<set,x'> \<in> Tier (succ j)"
    shows "x' \<subseteq> Tier j \<ominus> set"
proof (rule tier_succE_pair[OF j x]) 
  show "<set,x'> \<in> Tier j \<Longrightarrow> x' \<subseteq> Tier j \<ominus> set"
  proof (induct rule: trans_induct3[OF j])
    case 1 then show ?case 
      using tier0D(2) variants_set(1) by auto
  next
    case IH:(2 j)
    show ?case 
    proof (rule tier_succE_pair[OF IH(1,3)])
      assume "<set,x'> \<in> Tier j"
      hence "x' \<subseteq> Tier j \<ominus> set" using IH(2) by auto
      thus "x' \<subseteq> Tier (succ j) \<ominus> set"  
        using subset_trans[OF _ tier_ex_subset_succ[OF IH(1)]] by auto
    next
      assume "x' \<in> Variants set (succ j) (Tier j \<ominus> set)"
      hence "x' \<subseteq> Tier j \<ominus> set" 
        unfolding variants_set(2)[OF IH(1)] 
        using powD[OF tier_ex_set[OF IH(1)]] by auto
      thus "x' \<subseteq> Tier (succ j) \<ominus> set"  
        using subset_trans[OF _ tier_ex_subset_succ[OF IH(1)]] by auto
    qed
  next
    case IH:(3 \<mu>)
    show ?case 
    proof (rule tier_limE_pair[OF \<open>\<mu> : Limit\<close> \<open><set,x'> \<in> Tier \<mu>\<close>])
      fix j assume "j : Ord" "j < \<mu>" "<set,x'> \<in> Tier j"
      hence "x' \<subseteq> Tier j \<ominus> set" using IH(2) by auto 
      thus "x' \<subseteq> Tier \<mu> \<ominus> set" 
        using subset_trans[OF _ tier_limit_ex_subset[OF \<open>\<mu> : Limit\<close> \<open>j : Ord\<close> \<open>j < \<mu>\<close>]] by auto
    next
      show "x' \<in> Variants set \<mu> (\<lambda>j<\<mu>. Tier j \<ominus> set) \<Longrightarrow> x' \<subseteq> Tier \<mu> \<ominus> set"
        unfolding variants_set(3)[OF \<open>\<mu> : Limit\<close>] by auto
    qed
  qed
next
  assume "x' \<in> Variants set (succ j) (Tier j \<ominus> set)"
  thus "x' \<subseteq> Tier j \<ominus> set" 
    unfolding variants_set(2)[OF j] 
    using powD[OF tier_ex_set[OF j]] by auto
qed

theorem mI_mset :
  assumes j: "j : Ord" and x':"x' : Set"
      and x'_sub : "x' \<subseteq> Tier j \<ominus> set"
    shows "<set,x'> : M"
  using mI[OF succ_ord[OF j]] tierI_mset[OF j x' x'_sub] by auto

theorem mE_mset : 
  assumes x : "<set,x'> : M"
  obtains j where "j : Ord" "x' \<subseteq> Tier j \<ominus> set"
proof (rule m_cases_pair[OF x], use variants_set in auto)
  fix j assume "j : Ord" "x' \<in> \<P> (Tier j \<ominus> set)"
  hence "j : Ord" "x' \<subseteq> Tier j \<ominus> set"
    using powD[OF tier_ex_set] by auto
  thus ?thesis ..
qed



end
end
