theory GZF_Model_Base
  imports "../../ModelKit/ModelComponents"
begin

context ModelBase begin
ML \<open>val set_model = mcomp
 { name = "GZF_Model", 
   deps = [], 
   variant = SOME (vari 
    { tag_name = "set",
      vcases = 
        (@{term \<open>\<emptyset>\<close>}, 
         @{term "(\<lambda>_ x. \<P> x) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"}, 
         @{term "(\<lambda>_ _. \<emptyset>) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"}),
       alpha_typ = @{term "Set"},
       excludes_formulas = [@{prop \<open>\<not> Excluded set <set, x'>\<close>}]
    })
 }\<close>
end

local_setup \<open>snd o (mk_mcomp_class set_model)\<close>

context GZF_Model begin

definition mSet :: \<open>'a \<Rightarrow> bool\<close>
  where "mSet \<equiv> M \<bar> (\<^enum> set)"

definition mMem :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>m\<close> 50) 
where "x m y \<equiv> y : mSet \<and> x \<in> snd y"

definition mUnion' :: \<open>'a \<Rightarrow> 'a\<close> 
  where "mUnion' x \<equiv> <set, \<Union> y \<in> snd x. snd y>"

definition mPow' :: \<open>'a \<Rightarrow> 'a\<close> 
  where "mPow' x \<equiv> <set, set \<oplus> \<P> (snd x)>"

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

(*Probably need to make sure that b is a SetMem*)
definition mRepl' :: \<open>['a, ['a,'a] \<Rightarrow> bool] \<Rightarrow> 'a\<close> 
  where "mRepl' x P \<equiv> <set, { b | \<exists> a \<in> snd x. P a b \<and> (\<exists>y : mSet. b m y) }>" 

(*TODO: include simple definitions from *_sig in translated list of axioms for user to prove *)
interpretation m : GZF_sig GZF_Model_mdefault mSet mMem mUnion' mPow' mEmp mSucc' mInf mRepl' .

abbreviation "mSetOf \<equiv> m.SetOf"
lemmas msetofI = m.setofI
   and msetof_mset = m.setof_set
   and msetof_mmem = m.setof_mem
   and msetof_iff = m.setof_iff

abbreviation "mSetMem \<equiv> m.SetMem"
lemmas msetmemI = m.setmemI
   and msetmem_iff = m.setmem_iff

abbreviation "mSubset \<equiv> m.Subset"
lemmas msubsetI = m.subsetI
   and msubsetD = m.subsetD
   and msubset_def = m.Subset_def

abbreviation "mReplPred \<equiv> m.ReplPred"
lemmas mreplpred_def = m.ReplPred_def

definition mUnion :: \<open>'a \<Rightarrow> 'a\<close> (\<open>m\<Union>\<close>)
  where "m\<Union> x \<equiv> if x : mSetOf mSet then mUnion' x
                                    else GZF_Model_mdefault"

definition mPow :: \<open>'a \<Rightarrow> 'a\<close> (\<open>m\<P>\<close>)
  where "m\<P> x \<equiv> if x : mSet then mPow' x 
                            else GZF_Model_mdefault"



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
