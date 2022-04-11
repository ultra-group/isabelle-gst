theory mRepl
  imports mMem
begin

context GZF_Model begin

lemma mRepl_eq : 
  assumes "x : mSet" "P : mReplPred x"
  shows "mRepl x P = <set, { b | \<exists> a \<in> snd x. P a b \<and> b : mSetMem }>"
  unfolding mRepl_def mRepl'_def tex_def msetmem_iff
  using assms by auto

lemma mreplpred_replpred : 
  assumes x : "<set,x'> : mSet" and P : "P : mReplPred <set,x'>"
  shows "(\<lambda>a b. P a b \<and> b : mSetMem) : ReplPred x'"
  unfolding ReplPred_def
proof (rule tyI, auto)
  fix a assume "a \<in> x'"
  hence "a m <set,x'>" using mmemI[OF x] by auto
  hence uniq:"m\<exists>\<^sub>\<le>\<^sub>1 b : mSetMem. P a b" 
     using P mmem_m
     unfolding mReplPred_def has_ty_def mall_def tall_def by auto
  thus "\<exists>\<^sub>\<le>\<^sub>1 b : SetMem. P a b \<and> b : mSetMem" 
   unfolding mtuniq_def muniq_def tuniq_def Uniq_def 
   using msmem_smem msmem_m by auto
qed

lemma mreplpred_cong :  
  "\<And>x. x : M \<Longrightarrow> (\<And>fun1 fun2.
      (\<And>x. x : M \<Longrightarrow> (\<And>xa. xa : M \<Longrightarrow> fun1 x xa = fun2 x xa))
        \<Longrightarrow> mReplPred x fun1 = mReplPred x fun2)"
  using mset_m[OF mmem_mset]
  unfolding mReplPred_def mall_def tall_def 
            mtuniq_def tuniq_def muniq_def Uniq_def by blast
     
lemma mrank_memfun : 
  assumes x : "x : SetOf M"
  shows "mrank : x \<leadsto> Ord"
  by (rule mem_funI, erule mrank_ord[OF setof_mem[OF x]])

lemma mrank_repfun :
  assumes x : "x : SetOf M"
  shows "i \<in> {mrank b | b \<in> x} \<longleftrightarrow> (\<exists>b\<in>x. i = mrank b)"
  unfolding repfun_iff[OF setof_set[OF x]] bex_def rex_def
  using ord_setmem[OF mem_funE[OF mrank_memfun[OF x]]] by auto

lemma mrank_repfun_setof : 
  assumes x:"x : SetOf M" 
  shows "{mrank b | b \<in> x} : SetOf Ord"
  using repfun_setof[OF setof_set[OF x] mrank_memfun[OF x]] .

lemma setof_mset :
  assumes x:"x' : SetOf M" and b:"\<forall>b\<in>x'. \<not> Excluded set b"
  shows "<set, x'> : mSet"
proof (rule msetI)
  let ?i = "supOrd {mrank b | b \<in> x'}"
  have "?i : Ord" and "\<forall>b\<in>x'. mrank b < ?i"
    using supord_iff[OF mrank_repfun_setof[OF x] repfunI[OF setof_set[OF x] _ ord_setmem]] 
          supord_ord[OF mrank_repfun_setof[OF x]] mrank_ord[OF setof_mem[OF x]] by auto
  moreover have "\<forall>b\<in>x'. b \<in> Tier (mrank b)"
    using mrank_tier[OF setof_mem[OF x]] by auto
  ultimately have "\<forall>b \<in> x'. b \<in> Tier ?i"
    using tier_increasing[OF mrank_ord[OF setof_mem[OF x]] \<open>?i : Ord\<close>] by auto
  hence "\<forall>b \<in> x'. b \<in> Tier ?i \<ominus> set" 
    using exsetI[OF tier_set[OF \<open>?i : Ord\<close>]] b by auto
  thus "<set,x'> : M"
    using mI_mset[OF \<open>?i : Ord\<close> setof_set[OF x]] by auto
qed

lemma mrepl_typ :
  "mRepl : (\<Pi> x:mSet. mReplPred x \<rightarrow> mSet)"
proof (rule depfunI, rule funI)
  fix x P 
  assume x : "x : mSet" and P: "P : mReplPred x"
  then obtain x' where x':"x = <set,x'>" "x' : Set"
    using msetE by auto
  hence Px':"(\<lambda>a b . P a b \<and> b : mSetMem) : ReplPred x'" 
    using mreplpred_replpred P x by auto

  let ?R = \<open>{ b | \<exists>a\<in>x'. P a b \<and> b : mSetMem }\<close>
  have mrepl_eq: "mRepl x P = <set,?R>" 
    using mRepl_eq[OF x P] 
    unfolding x' mset_snd_eq'[OF x'(2)] by auto
  show "mRepl x P : mSet" 
    unfolding mrepl_eq
  proof (rule setof_mset, rule setofI[OF repl_set[OF x'(2) Px']],
         rule_tac [2] ballI)
    fix b assume "b \<in> ?R"
    hence  "b : mSetMem" 
      using replaceE[OF x'(2) Px'] by blast
    thus "b : M" "\<not> Excluded set b" 
      using msmem_m msmem_not_excluded by auto
   qed
qed

lemmas mrepl_mset = funE[OF depfunE[OF mrepl_typ]]

lemma mrepl_iff :
  assumes x : "x : mSet" and P : "P : mReplPred x"
  shows "b m mRepl x P \<longleftrightarrow> (\<exists>a. a m x \<and> P a b \<and> b : mSetMem)"  
proof -
  obtain x' where x' : "x = <set,x'>" "x' : Set" 
    using msetE[OF x] by auto
  have Px' : "(\<lambda>a b. P a b \<and> b : mSetMem) : ReplPred x'" 
    using mreplpred_replpred P x unfolding x' by auto
  have mrepl_eq : "mRepl x P = <set, { b | \<exists>a\<in>x'. P a b \<and> b : mSetMem }>"
    using mRepl_eq[OF x P] 
    unfolding x' mset_snd_eq'[OF x'(2)] by auto

  show ?thesis 
    unfolding 
      mmem_iff_eq[OF mrepl_mset[OF x P] mrepl_eq] 
      replace_iff[OF x'(2) Px'] mmem_iff_eq[OF x x'(1)]
    using msmem_smem
    by auto
qed    

lemma mrepl_cong' : 
  assumes x : "x : mSet" 
      and P : "P : mReplPred x" 
      and Q : "Q : mReplPred x"
      and iff : "\<And>a b. a : M \<Longrightarrow> b : M \<Longrightarrow> P a b \<longleftrightarrow> Q a b" 
    shows "mRepl' x P = mRepl' x Q"
    unfolding mRepl'_def
proof (rule pair_eqI[OF refl], 
       rule replace_cong[OF mset_snd_set[OF x] _ mset_snd_set[OF x] _ refl])
  obtain x' where x':"x = <set, x'>" "x' : Set"
    using msetE[OF x] .
  show "(\<lambda>a b. P a b \<and> b : mSetMem) : ReplPred (\<pi> x)"
       "(\<lambda>a b. Q a b \<and> b : mSetMem) : ReplPred (\<pi> x)"
       using x mreplpred_replpred P Q 
       unfolding x' mset_snd_eq'[OF x'(2)] msetmem_iff
       by auto
  fix a b assume "a \<in> \<pi> x"
  hence "a m x" using mmemI x x' mset_snd_eq by auto
  hence "a : M" using mmem_m by auto
  thus "(P a b \<and> b : mSetMem) \<longleftrightarrow> (Q a b \<and> b : mSetMem)"
    using iff mmem_m msetmem_iff by auto
qed
  
lemma mrepl_cong :
  assumes iff:"\<And>a b. a : M \<Longrightarrow> b : M \<Longrightarrow> P a b \<longleftrightarrow> Q a b" 
  shows "m\<R> x P = m\<R> x Q"
proof -
  have pq:"P : mReplPred x \<longleftrightarrow> Q : mReplPred x"
    using iff[OF mmem_m msmem_m]
    unfolding mReplPred_def has_ty_def mtuniq_def muniq_def tuniq_def Uniq_def
              mall_def by blast
  show ?thesis
  proof (cases \<open>x : mSet \<and> P : mReplPred x\<close>)
    case h:True
    hence x:"x : mSet" and P: "P : mReplPred x" by auto
    hence Q:"Q : mReplPred x" using pq by auto
    have "mRepl' x P = mRepl' x Q"
      using mrepl_cong'[OF x P Q] iff by auto
    thus ?thesis 
      unfolding mRepl_def using x P Q by auto
  next
    case False
    then show ?thesis 
      unfolding mRepl_def pq by auto
  qed
qed 

lemma mrepl_m :
  "m\<R> x P : M"
  using mset_m[OF mrepl_mset] GZF_Model_mdefault_m
  unfolding mRepl_def by auto

theorem mrepl_ax : 
 "m\<forall>x:mSet. \<forall>P : mReplPred x. m\<forall>b. (b m m\<R> x P) = (m\<exists>a. a m x \<and> P a b \<and> b : mSetMem)"
  using mrepl_iff mmem_m 
  unfolding mall_def mtall_def mall_def tall_def mtex_def tex_def mex_def
  by blast

theorem mrepl_rsp : 
  assumes x : "x : M" and iff:"\<And>x y. x : M \<Longrightarrow> y : M \<Longrightarrow> P x y \<longleftrightarrow> Q x y"
  shows "m\<R> x P : M \<and> (m\<R> x P = m\<R> x Q)"
  using mrepl_m mrepl_cong iff by blast
  
end
end