theory GZF_Model
  imports mUnion mPow mRepl mInf
begin

context GZF_Model begin

ML \<open>val mGZF = 
    mk_msig [] "mGZF" @{class GZF} 
      ["GZF_Model_mdefault", "mSet", "mMem", 
       "mUnion", "mPow", "mEmp", "mSucc", "mInf", "mRepl"] @{context}\<close>
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
qed

resp_thms mGZF_resp : mGZF  
proof (rule GZF_Model_mdefault_m, erule munion_rsp, erule mpow_rsp,
       rule memp_rsp, erule msucc_rsp, rule minf_rsp)
  fix x P Q 
  assume x:"x : M" and pq:"\<And>x y. x : M \<Longrightarrow> y : M \<Longrightarrow> P x y \<longleftrightarrow> Q x y"
  show "m\<R> x P : M \<and> m\<R> x P = m\<R> x Q"
    using mrepl_rsp[of x P Q, OF x] pq by fastforce 
qed

end
end