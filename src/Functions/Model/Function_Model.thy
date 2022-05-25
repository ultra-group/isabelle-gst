theory Function_Model 
  imports mapp mdom_mran mfspace mk_mfun
begin

context Function_Model begin

ML \<open>val mFunction = 
  mk_msig [mGZF] "mFunction" \<^class>\<open>Function\<close>
    ["mapp", "mFunc", "mk_mfun", "mdom", "mran", "mfspace", "mFunMem", "mFunPred", "Function_Model_mdefault"]
    \<^context>\<close>

translate_axioms mFunction_axioms : mFunction
proof (rule mk_mfun_typ_ax, rule mdom_typ_ax, rule mran_typ_ax,
       rule mfspace_typ_ax, rule mk_mfun_ax, rule mapp_functional_ax,
       rule mfunc_ext_ax, rule mdom_ax, rule mran_ax, rule mfspace_ax)
  show "m\<forall>b. mFunMem b = (m\<exists>r : mFunc. m\<exists>c. mapp r b c \<or> mapp r c b)"
    unfolding mFunMem_def by auto
  show "m\<forall>x. \<forall>P. mFunPred x P = (m\<forall>b : mFunMem. b m x \<longrightarrow> mtuniq mFunMem (P b)) "
    unfolding mFunPred_def by auto  
qed

resp_thms mFunction_rsp : mFunction 
proof -
  show "\<And>x. x : M \<Longrightarrow> (\<And>fun1 fun2. (\<And>x. x : M \<Longrightarrow>
          (\<And>xa. xa : M \<Longrightarrow> fun1 x xa = fun2 x xa)) \<Longrightarrow>
             mk_mfun x fun1 : M \<and> mk_mfun x fun1 = mk_mfun x fun2)"
    using mk_mfun_rsp by (metis)

  show "\<And>x. x : M \<Longrightarrow> mdom x : M"
    using mdom_rsp .
  show "\<And>x. x : M \<Longrightarrow> mran x : M"
    using mran_rsp .
  show "\<And>x y. x : M \<Longrightarrow> y : M \<Longrightarrow> mfspace x y : M"
    using mfspace_rsp .
  show "\<And>x. x : M \<Longrightarrow> (\<And>fun1 fun2. (\<And>x. x : M \<Longrightarrow>
          (\<And>xa. xa : M \<Longrightarrow> fun1 x xa = fun2 x xa)) \<Longrightarrow>
             mFunPred x fun1 = mFunPred x fun2)"
    using mfpred_cong by metis
  show "Function_Model_mdefault : M"
    using Function_Model_mdefault_m .  
qed

end
end