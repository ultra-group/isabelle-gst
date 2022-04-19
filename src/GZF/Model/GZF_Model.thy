theory GZF_Model
  imports mUnion mPow mRepl mInf
begin

context GZF_Model begin

ML \<open>val mGZF = 
    mk_msig [] "mGZF" @{class GZF} 
      ["mSet", "mMem",  "mUnion", "mPow", "mEmp", "mSucc", "mInf", "mRepl",
       "mSubset", "mSetMem", "mSetOf", "mReplPred", 
       "GZF_Model_mdefault"] @{context}\<close>
translate_axioms mGZF_axioms : mGZF  
proof -
  show "m\<forall>x. x : mSetOf mSet \<longrightarrow> m\<Union> x : mSet" 
    using munion_mset by auto
  show "m\<forall>x. x : mSet \<longrightarrow> m\<P> x : mSetOf mSet"
    using mpow_mset by auto
  show "m\<forall>x. x : mSet \<longrightarrow> (\<forall>xa. xa : mReplPred x \<longrightarrow> m\<R> x xa : mSet)"
    using mrepl_mset by auto
  show "m\<emptyset> : mSet"
    using memp_mset .
  show "m\<forall>x. x : mSet \<longrightarrow> mSucc x : mSet"
    using msucc_mset by auto
  show "mInf : mSet" 
    using minf_mset .
  show "m\<forall>x:mSet. m\<forall>y:mSet. (m\<forall>a. (a m x) = (a m y)) \<longrightarrow> x = y"
    using mext_ax .
  show "m\<forall>x:mSetOf mSet. m\<forall>a. (a m m\<Union> x) = (m\<exists>z. z m x \<and> a m z)"
    using munion_ax .
  show "m\<forall>x:mSet. m\<forall>z:mSet. (z m m\<P> x) = mSubset z x"
    using mpow_ax .
  show "m\<forall>b. \<not> b m m\<emptyset>"
    using memp_ax .
  show "m\<forall>x:mSet. m\<forall>b. (b m mSucc x) = (b m x \<or> b = x)"
    using msucc_ax .
  show "mEmp m mInf \<and> (m\<forall>a. a m mInf \<longrightarrow> mSucc a m mInf)"
    using minf_ax .
  show "m\<forall>x:mSet. \<forall>P : mReplPred x. m\<forall>b. (b m m\<R> x P) 
          \<longleftrightarrow> (m\<exists>a. a m x \<and> P a b \<and> b : mSetMem)"
    using mrepl_ax .
  show "m\<forall>x y. mSubset x y = (m\<forall>a. a m x \<longrightarrow> a m y)" 
    unfolding mSubset_def by auto
  show "m\<forall>b. mSetMem b = (m\<exists>x:mSet. b m x)" 
    unfolding mSetMem_def by auto
  show "\<forall>\<alpha>. m\<forall>x. mSetOf \<alpha> x =
              (x : mSet \<and> (m\<forall>b. b m x \<longrightarrow> b : \<alpha>))" 
    unfolding mSetOf_def by auto
  show "m\<forall>x. \<forall>P. mReplPred x P = (m\<forall>a. a m x \<longrightarrow> mtuniq mSetMem (P a))"
    unfolding mReplPred_def by auto
qed

resp_thms mGZF_resp : mGZF 
proof (erule munion_rsp, erule mpow_rsp,
       rule memp_rsp, erule msucc_rsp, rule minf_rsp)
  fix x P Q 
  assume x:"x : M" and pq:"\<And>x y. x : M \<Longrightarrow> y : M \<Longrightarrow> P x y \<longleftrightarrow> Q x y"
  show "m\<R> x P : M \<and> m\<R> x P = m\<R> x Q"
    using mrepl_rsp[of x P Q, OF x] pq by fastforce 
next
  show "\<And>fun1 fun2. (\<And>x. x : M \<Longrightarrow> fun1 x = fun2 x) 
    \<Longrightarrow> (\<And>x. x : M \<Longrightarrow> mSetOf fun1 x = mSetOf fun2 x)"
    using msetof_cong .
  show "\<And>x. x : M \<Longrightarrow> (\<And>fun1 fun2.
           (\<And>x. x : M \<Longrightarrow> (\<And>xa. xa : M \<Longrightarrow> fun1 x xa = fun2 x xa)) \<Longrightarrow>
             mReplPred x fun1 = mReplPred x fun2)"
    using mreplpred_cong .
  show "GZF_Model_mdefault : M"
    using GZF_Model_mdefault_m .
qed

end

ML_file \<open>../../ModelKit/Tools/lift_model_sig.ML\<close>
ML_file \<open>../../Tools/transfer_all_method.ML\<close>

(* typedecl d0  

instance d0 :: GZF_Model  sorry

typedef (overloaded) d1 = \<open>Set.Collect (\<lambda>x :: d0. x : M)\<close> 
  using GZF_Model_mdefault_m by auto

setup_lifting type_definition_d1 

interpretation ConnectionBase Abs_d1 Rep_d1 pcr_d1 mdefault
  by (unfold ConnectionBase_def, rule,
      rule type_definition_d1, unfold pcr_d1_def cr_d1_def, auto, rule mdefault_m)

instantiation d1 :: GZF 
begin
  local_setup \<open>lift_mconsts @{thms mGZF_resp} (@{typ d1}) mGZF\<close>  
  instance 
  by (intro_classes, unfold funty_eq depfunty_eq,
      transfer_all, insert mGZF_axioms)
end *)
end