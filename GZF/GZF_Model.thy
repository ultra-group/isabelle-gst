theory GZF_Model
  imports "../ModelKit/ModelComponents"
begin

local_setup \<open>snd o (mk_mcomp_class set_model)\<close>
(* local_setup \<open>snd o (mk_connection_locale @{theory} set_model)\<close> *)

context SetModel begin

definition mSet :: \<open>'a \<Rightarrow> bool\<close>
  where "mSet \<equiv> M \<bar> (\<^enum> set)"

definition mMem :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>m\<close> 50) 
where "x m y \<equiv> y : mSet \<and> x \<in> snd y"

definition mUnion :: \<open>'a \<Rightarrow> 'a\<close> (\<open>m\<Union>\<close>)
  where "m\<Union> x \<equiv> <set, \<Union> y \<in> snd x. snd y>"

definition mPow :: \<open>'a \<Rightarrow> 'a\<close> (\<open>m\<P>\<close>)
  where "m\<P> x \<equiv> <set, set \<oplus> \<P> (snd x)>"

definition mEmp :: \<open>'a\<close> (\<open>m\<emptyset>\<close>)
  where "mEmp = <set, \<emptyset>>" 

definition mSucc :: \<open>'a \<Rightarrow> 'a\<close>
  where "mSucc x = m\<Union> <set, {x, <set, {x}>}>"

definition ord_to_mvnord :: \<open>'a \<Rightarrow> 'a\<close> (\<open>\<Theta>\<close>)
  where \<open>\<Theta> \<equiv> OrdRec (\<lambda>\<mu> f. <set, {f j | j < \<mu>}>) (\<lambda>_ x. mSucc x) m\<emptyset>\<close>

definition mInf :: \<open>'a\<close>
  where \<open>mInf \<equiv> \<Theta> \<omega>\<close>

(*Probably need to make sure that b is a SetMem*)
definition mRepl :: \<open>['a, ['a,'a] \<Rightarrow> bool] \<Rightarrow> 'a\<close> (\<open>m\<R>\<close>)
  where "m\<R> x P \<equiv> <set, { b | \<exists> a \<in> snd x. P a b \<and> (\<exists>y : mSet. b m y) }>" 

(*TODO: include simple definitions from *_sig in translated list of axioms for user to prove *)
interpretation m : GZF_sig SetModel_mdefault mSet mMem mUnion mPow mInf mRepl .


section \<open>Structure of the 'set' part of Tier\<close>

lemma variants_set :
  shows "Variants set 0 \<emptyset> = \<emptyset>"
    and "j : Ord   \<Longrightarrow> Variants set (succ j) x = \<P> x"
    and "\<mu> : Limit \<Longrightarrow> Variants set \<mu> f = \<emptyset>"
  using v_set_0 v_set_succ v_set_limit by auto

section \<open>Model-set soft type\<close>

lemma mpair_snd_eq : 
  "<i,x'> : M \<Longrightarrow> \<pi> <i,x'> = x'"
  using snd_eq[OF m_pair] by auto

lemmas tag_set_pair = pair_pair[OF ord_pmem[OF tag_ord] smem_pmem[OF set_setmem]]
lemmas mset_snd_eq = snd_eq[OF tag_set_pair[OF set_tag]]

lemma mset_m : 
  "x : mSet \<Longrightarrow> x : M" 
  unfolding mSet_def by (unfold_typs)

lemmas mset_pair = mtagD(1)[OF mset_m]

lemma mset_tag : "x : mSet \<Longrightarrow> x :\<^enum> set"
  unfolding mSet_def by (unfold_typs)

lemma msetI: "<set,x'> : M \<Longrightarrow> <set,x'> : mSet"
  unfolding mSet_def using partI[OF _ m_pair] 
  sorry

lemma mset_pair_set : 
  "<set,x'> : M \<Longrightarrow> x' : Set"
  using mtagD_pair(3) alpha_set by auto

lemma mset_set : 
  "<set,x'> : mSet \<Longrightarrow> x' : Set"
  using mset_pair_set[OF mset_m] by auto

lemma msetE : 
  assumes x:"x : mSet"
  obtains x' where "x = <set,x'>" "x' : Set"
  by (rule partE[OF mset_tag[OF x]], use mset_pair_set[OF mset_m] x in auto)

lemma not_excluded_mset :
  assumes x : "x : mSet"
    shows "\<not> Excluded set x"
  by (rule msetE[OF x], metis excluded_set_1)

lemma mset_snd_set : 
  "x : mSet \<Longrightarrow> snd x : Set"
  using mset_pair_set[OF mset_m] mset_snd_eq 
  by (auto elim: msetE)

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


section \<open>Model set membership relation\<close>

lemma mmemI :
  assumes x' : "x' : Set" and a : "a \<in> x'" 
    shows "a m <set, x'>"
  unfolding mMem_def mset_snd_eq[OF x']
  by (rule a)

lemma mmemI_mset :
  assumes x' : "<set,x'> : mSet" and a : "a \<in> x'" 
    shows "a m <set, x'>"
  using mmemI[OF mset_set[OF x'] a] .

lemma mmemD :
  assumes x' : "x' : Set" and a : "a m <set, x'>"
    shows "a \<in> x'"
  using a 
  unfolding mMem_def mset_snd_eq[OF x'] .

lemma mmem_iff : 
  assumes x' : "x' : Set"
  shows "a m <set,x'> \<longleftrightarrow> a \<in> x'"
  using mmemI[OF x'] mmemD[OF x'] by auto

lemma mmem_iff_mset : 
  assumes x' : "<set,x'> : mSet"
  shows "a m <set,x'> \<longleftrightarrow> a \<in> x'"
  using mmemI mmemD mset_set[OF x'] by auto

lemma mmem_iff_eq : 
  assumes x : "x : mSet" and x' : "x = <set,x'>"
  shows "a m x \<longleftrightarrow> a \<in> x'"
  using mmemI mmemD mset_set x x' by auto

lemma mmem_tier :
  assumes j : "j : Ord" and x : "<set,x'> \<in> Tier (succ j)" 
      and a : "a m <set,x'>" 
    shows "a \<in> Tier j \<ominus> set"
 using tierD_mset[OF j x] mmemD[OF mset_pair_set[OF mI[OF succ_ord[OF j] x]] a] by auto

lemma mmem_m :
  assumes x : "x : mSet" and b : "b m x"
    shows "b : M"
proof (rule msetE[OF x], rule mE[OF mset_m[OF x]])
  fix x' i assume x:"x = <set,x'>" "x' : Set" "i : Ord" "x \<in> Tier i"
  hence "<set,x'> \<in> Tier (succ i)" using tier_succI1 by auto
  thus "b : M" using mI[OF _ exsetD1[OF tier_set mmem_tier]] b x by auto
qed
  
lemma mset_pair_setof : 
  assumes x : "<set, x'> : m.SetOf P" 
  shows "x' : SetOf P"
proof (rule setofI)
 from m.setof_set[OF x] have "<set,x'> : mSet" by auto
 thus "x' : Set" using mset_pair_set[OF mset_m] by auto
 fix b assume "b \<in> x'"
 hence "b m <set,x'>" using mmemI[OF \<open>x' : Set\<close>] by auto
 thus "b : P" using m.setof_mem[OF x] by auto
qed 

lemma setof_msetof :
  assumes x : "<set,x'> : M" and x' : "x' : SetOf P"
  shows "<set, x'> : m.SetOf P"
proof (rule m.setofI[OF msetI[OF x]])
  fix b assume "b m <set,x'>" thus "b : P"
    unfolding mmem_iff[OF setof_set[OF x']]
        using setof_mem[OF x'] by auto
qed

lemma msetofE : 
  assumes x : "x : m.SetOf P" 
  obtains x' where "x = <set,x'>" "x' : SetOf P"
  by (rule msetE[OF m.setof_set[OF x]], metis mset_pair_setof x)


text \<open>Axiom of Extensionality\<close>
theorem mset_eq_iff :
  assumes x : "x : mSet" and y : "y : mSet"
      and iff : "\<forall>a. a m x \<longleftrightarrow> a m y"
    shows "x = y"
proof -
  obtain x' y' 
   where x: "x = <set,x'>" "x' : Set" 
     and y: "y = <set,y'>" "y' : Set" 
    by (metis msetE x y)
  hence "x' = y'" 
    using equality_iffI iff mmem_iff by auto  
  thus "x = y" 
    unfolding x(1) y(1) by auto
qed 


section \<open>Model union operator\<close>

thm m.setof_iff
abbreviation "mSetOf \<equiv> m.SetOf"

lemma snd_replfun : 
  assumes x' : "x' : SetOf mSet" 
    shows "snd : x' \<leadsto> Set"
proof (rule mem_funI)
  fix y assume "y \<in> x'" 
  hence y:"y : mSet" using setof_mem[OF x'] by auto
  then obtain y' where "y = <set, y'>" "y' : Set" 
    using msetE by auto
  thus "snd y : Set" 
    using set_setmem mset_snd_eq by auto
qed
   
lemma munion_typ : 
  "m\<Union> : m.SetOf mSet \<rightarrow> mSet" 
   unfolding mUnion_def
proof (rule funI, rule msetI)
  fix x assume x_setof:"x : m.SetOf mSet"
  hence x : "x : mSet" and x_mem : "\<forall>b. b m x \<longrightarrow> b : mSet" 
    using m.setof_iff by auto
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
    using x_mem unfolding x' mmem_iff[OF x'(2)] by auto
    
  have "\<Union> {snd y | y \<in> snd x} \<subseteq> Tier j \<ominus> set"
    unfolding x'(1) mset_snd_eq[OF x'(2)]  
  proof
    fix b assume "b \<in> \<Union> {snd y | y \<in> x'}"
    then obtain y where "b \<in> snd y" "y \<in> x'" 
      using repfun_union[OF _ snd_replfun] mset_pair_setof x_setof x' by auto
    hence "y : mSet" "y \<in> Tier (succ j)" 
      using x'_sub x'_mem by auto
    moreover then obtain y' where y':"y = <set,y'>" "y' : Set" 
      using msetE by auto
    ultimately have "y' \<subseteq> Tier j \<ominus> set" using tierD_mset[OF j(1)] by auto
    thus "b \<in> Tier j \<ominus> set" using \<open>b \<in> snd y\<close> y' mset_snd_eq by auto
  qed
  moreover have "\<Union> {snd y | y \<in> snd x} : Set"
    using union_set[OF repfun_setof[OF _ snd_replfun]] 
          mset_pair_setof x_setof x' mset_snd_eq by auto
  ultimately show "<set, \<Union> {snd y | y \<in> snd x}> : M" 
    using mI_mset[OF j(1)] by auto 
qed

lemmas munion_mset = funE[OF munion_typ]

lemma munionI : 
  assumes x : "x : mSetOf mSet" 
      and y : "y m x" 
      and a : "a m y"
    shows "a m m\<Union> x"
proof (rule msetE[OF m.setof_set[OF x]])
  fix x' assume x':"x = <set,x'>" "x' : Set"
  obtain y' where y': "y = <set, y'>" "y' : Set" 
    using msetE[OF m.setof_mem[OF x y]] by auto
  have x'_setof : "x' : SetOf mSet"
    using mset_pair_setof x' x by auto

  show "a m m\<Union> x" 
    unfolding mUnion_def x' mset_snd_eq[OF x'(2)]
  proof (rule mmemI)
    show "\<Union> {snd y | y \<in> x'} : Set" 
      using mset_set munion_mset[OF x] 
      unfolding mUnion_def x' mset_snd_eq[OF x'(2)] by auto
    
    from a have "a \<in> snd y" using mmemD[OF y'(2)] a y'(1) mset_snd_eq[OF y'(2)] by auto
    moreover have "y \<in> x'" using mmemD[OF x'(2)] y x'(1) by auto
    ultimately show "a \<in> \<Union> {snd y | y \<in> x'}"
      using repfun_union[OF \<open>x' : Set\<close> snd_replfun[OF x'_setof]] by auto
   qed
qed

lemma munionE : 
  assumes x : "x : m.SetOf mSet"
      and a : "a m m\<Union> x"
    obtains y where "y m x" "a m y"
proof (rule msetofE[OF x])
  fix x' assume x':"x = <set,x'>" "x' : SetOf mSet"
  then obtain y where "y \<in> x'" "a \<in> snd y" 
    using repfun_union[OF setof_set[OF x'(2)] snd_replfun[OF x'(2)]] a 
    unfolding mUnion_def x'(1) mmem_iff[OF union_set[OF repfun_setof[OF setof_set[OF x'(2)] snd_replfun[OF x'(2)]]]]
              mset_snd_eq[OF setof_set[OF x'(2)]] by auto
  then obtain y' where "y = <set,y'>" "y' : Set" "a \<in> y'"
    using msetE[OF setof_mem[OF x'(2)]] mset_snd_eq by metis
  
  have "y m x" "a m y" 
    using mmemI[OF setof_set[OF x'(2)] \<open>y \<in> x'\<close>] 
          mmemI[OF \<open>y' : Set\<close> \<open>a \<in> y'\<close>]
          \<open>x = <set,x'>\<close> \<open>y = <set,y'>\<close> by auto
  thus ?thesis ..
qed

lemma munion_iff : 
  assumes x : "x : mSetOf mSet"
  shows "b m m\<Union> x \<longleftrightarrow> (\<exists>y. y m x \<and> b m y)"
  using munionI[OF x] munionE[OF x] by metis


section \<open>Model power set operator\<close>

lemma mpow_typ : "m\<P> : mSet \<rightarrow> mSetOf mSet"
  unfolding mPow_def
proof (rule funI, rule m.setofI, rule msetI)
  fix x assume "x : mSet"
  then obtain x' 
    where x' : "x = <set,x'>" "x' : Set" 
    by (rule msetE)
  then obtain j 
    where j : "j : Ord" and "<set,x'> \<in> Tier j" 
    using mE[OF mset_m[OF \<open>x : mSet\<close>]] by auto
  hence x'_sub:"x' \<subseteq> Tier j \<ominus> set" 
    using tierD_mset[OF j tier_succI1[OF j]] by auto
  
  have "set \<oplus> \<P> x' \<subseteq> Tier (succ j) \<ominus> set"  
  proof (rule, erule tmapE[OF tag_pmem[OF set_tag] pow_set[OF x'(2)]],
         rule exsetI[OF tier_set[OF succ_ord[OF j]]])
    fix y y' assume "y' \<in> \<P> x'" "y = <set,y'>"
    hence "y' \<subseteq> Tier j \<ominus> set" "y' : Set"
      using subset_trans[OF powD[OF x'(2)] x'_sub]
            pow_mem[OF \<open>x' : Set\<close>] by auto
    thus "y \<in> Tier (succ j)" using tierI_mset[OF j] \<open>y = <set,y'>\<close> by auto
    show "\<not> Excluded set y" 
      using excluded_set_1
      unfolding \<open>y = <set,y'>\<close> by auto
  qed

  thus "<set, set \<oplus> \<P> (snd x)> : M"
    unfolding x'(1) mset_snd_eq[OF x'(2)]
  by (rule mI[OF succ_ord[OF succ_ord[OF j]] 
    tierI_mset[OF succ_ord[OF j] tmap_set[OF tag_pmem[OF set_tag] pow_set[OF x'(2)]]]])
(*  by (rule mI[OF succ_ord[OF succ_ord[OF j]] tierI_mset[OF succ_ord[OF j]]]) *)

  fix b assume "b m <set, set \<oplus> \<P> (snd x)>"
  hence "b \<in> set \<oplus> \<P> x'" 
    using mmemD[OF tmap_set[OF tag_pmem[OF set_tag] pow_set[OF x'(2)]]]
    unfolding x'(1) mset_snd_eq[OF x'(2)] by auto
  then obtain b' where "b = <set,b'>" "b' \<in> \<P> x'" 
    by (rule tmapE[OF tag_pmem[OF set_tag] pow_set[OF x'(2)]])
  hence "b' \<subseteq> Tier j \<ominus> set" "b' : Set" 
    using subset_trans[OF powD[OF x'(2)] x'_sub]
          pow_mem[OF \<open>x' : Set\<close>] by auto
  thus "b : mSet" 
    using msetI[OF mI_mset[OF j]] \<open>b = <set,b'>\<close> by auto
qed

definition msub where 
  "msub x y = (m\<forall>b. b m x \<longrightarrow> b m y)"
abbreviation "mSubset \<equiv> m.Subset"
thm m.Subset_def

lemma mpowI :
  assumes x : "x : mSet" and y : "y : mSet" 
      and xy:"msub x y"
  shows "x m m\<P> y"
  unfolding mPow_def
proof (rule msetE[OF x], rule msetE[OF y])
  fix x' y' 
  assume x':"x = <set, x'>" "x' : Set"
     and y':"y = <set, y'>" "y' : Set"
  
  show "x m <set, set \<oplus> \<P> (snd y)>"
    unfolding y' mset_snd_eq[OF y'(2)] x'
  proof (rule mmemI[OF tmap_set[OF tag_pmem[OF set_tag] pow_set[OF y'(2)]]])
    have "x' \<subseteq> y'"
      using xy mmem_m[OF x]
      unfolding msub_def x' y' mmem_iff[OF x'(2)] mmem_iff[OF y'(2)] mall_def
      by auto
    hence "x' \<in> \<P> y'"
      using powI x' y' by auto
    thus "<set, x'> \<in> set \<oplus> \<P> y'"
      using tmapI[OF tag_pmem[OF set_tag] pow_set[OF y'(2)]] 
      by auto
  qed
qed


lemma mpowD : 
  assumes x : "x : mSet" and y : "y : mSet" 
      and pow : "x m m\<P> y"
    shows "msub x y"
proof (rule msetE[OF x], rule msetE[OF y])
  fix x' y' 
  assume x':"x = <set, x'>" "x' : Set"
     and y':"y = <set, y'>" "y' : Set"
  
  from pow have "<set,x'> \<in> set \<oplus> \<P> y'"
    using mmemD[OF tmap_set[OF tag_pmem[OF set_tag] pow_set[OF mset_snd_set[OF y]]]]
    unfolding mPow_def y' mset_snd_eq[OF y'(2)] x' by auto
  hence "x' \<in> \<P> y'" 
    using tmap_iff[OF tag_pmem[OF set_tag] pow_set[OF y'(2)] set_setmem[OF x'(2)]]   
    by auto
  hence "x' \<subseteq> y'" 
    using powD[OF y'(2)] by auto
  thus "msub x y"
    unfolding msub_def x' y' mmem_iff[OF x'(2)] mmem_iff[OF y'(2)] 
              mall_def by auto
qed

lemma mpow_iff :
  assumes "x : mSet" "y : mSet"
  shows "x m m\<P> y \<longleftrightarrow> msub x y"
  using mpowI mpowD assms by auto

section \<open>Witness of model Infinity\<close>

abbreviation "mEmp_defdes \<equiv> m.Emp"
lemmas mEmp_defdes_def = m.Emp_def

abbreviation "mSucc_defdes \<equiv> m.Succ"
subsection \<open>Equality of empty set definite description\<close>
thm m.Succ_def
lemma mball_generalize : 
  assumes x:"x : mSet"
  shows "(m\<forall>a. a m x \<longrightarrow> P a) = (\<forall>a. a m x \<longrightarrow> P a)"
  using mmem_m[OF x]   
  unfolding mall_def by auto

lemma mEmp_defdes_eq : 
  "mEmp_defdes = (m\<iota> x : mSet. m\<forall>b. \<not> b m x else SetModel_mdefault)"
  unfolding m.Emp_def typ_defdes_def mtdefdes_def mdefdes_def 
  by (rule the_def_cong, unfold mall_def tall_def, 
      use mset_m mmem_m in blast)

lemma mSucc_defdes_eq : 
  "mSucc_defdes = (\<lambda>x. m\<iota> y : mSet. x : mSet \<and> (m\<forall>a. a m y \<longleftrightarrow> (a m x \<or> a = x)) else SetModel_mdefault)"
  unfolding m.Succ_def typ_defdes_def mtdefdes_def mdefdes_def 
  proof (rule, rule the_def_cong, rule)
    fix x y 
    show "(y : mSet \<and> x : mSet \<and> (\<forall>a. (a m y) = (a m x \<or> a = x))) =
       (y : M \<and> y : mSet \<and> x : mSet \<and> (m\<forall>a. (a m y) = (a m x \<or> a = x)))"
      unfolding mall_def tall_def
    using mset_m[of y] mmem_m[of y] mmem_m[of x] mset_m by auto       
qed

lemma memp_mset : "m\<emptyset> : mSet"
  unfolding mEmp_def
proof (rule msetI, rule mI_mset[OF zero_typ emp_set])
  show "\<emptyset> \<subseteq> Tier 0 \<ominus> set" 
    using empty_subsetI[OF tier_set[OF zero_typ]] 
    by auto
qed

lemma memp_empty : "\<not> b m m\<emptyset>"
  unfolding mEmp_def mmem_iff[OF emp_set]
  by auto

lemma memp_uniq :
  assumes c : "c : mSet" and c_mem : "\<forall>b. \<not> b m c"
  shows "c = m\<emptyset>"
  using mset_eq_iff[OF c memp_mset] memp_empty c_mem 
  by metis

lemma memp_eq : "mEmp_defdes = mEmp"
  unfolding m.Emp_def
  by (rule typ_defdes_eq[OF memp_mset _],
      metis memp_empty, auto elim: memp_uniq)

subsection \<open>Equality of successor definite description\<close>

lemma mset_smem_subtyp :"mSet << SetMem"
proof (rule subtypI) 
  fix x assume "x : mSet"
  then obtain x' where x':"x = <set, x'>" "x' : Set"
    by (auto elim: msetE)
  hence "set : PairMem" "x' : PairMem"
    using tag_pmem[OF set_tag] smem_pmem[OF set_setmem] by auto
  thus "x : SetMem" 
    unfolding x' by (rule pair_setmem)
qed
   
lemmas mset_smem = subtypE[OF mset_smem_subtyp]

lemma msng_mset : 
  assumes x: "x : mSet"
  shows "<set, {x}> : mSet"
proof (rule msetI)
  obtain j where 
    j : "j : Ord" and xj :"x \<in> Tier j"
    by (metis mE[OF mset_m[OF x]])
  hence "{x} \<subseteq> Tier j \<ominus> set"
    using sng_subset[OF mset_smem[OF x] tier_ex_set[OF j]]
          exsetI[OF tier_set[OF j] xj not_excluded_mset[OF x]] by auto
  thus "<set, {x}> : M"
    by (rule mI_mset[OF j sng_set[OF mset_smem[OF x]]])
qed

lemma mupair_msetof :
  assumes x : "x : mSet" and y : "y : mSet"
  shows "<set, {x,y}> : mSetOf mSet"
proof (rule setof_msetof)
  obtain i j where 
    "i : Ord" "x \<in> Tier i" 
    "j : Ord" "y \<in> Tier j"
    using mE[OF mset_m] x y by metis
  then obtain k where 
    k : "k : Ord" and xk : "x \<in> Tier k" and yk : "y \<in> Tier k"
    by (metis greatest_tier)
  hence "{x,y} \<subseteq> Tier k \<ominus> set" 
    using upair_subset[OF mset_smem mset_smem tier_ex_set[OF k]] x y
          exsetI[OF tier_set[OF k] _ not_excluded_mset] by metis
  thus "<set, {x,y}> : M" 
    using mI_mset[OF k upair_set[OF mset_smem mset_smem]] 
          x y by metis  
  show "{x,y} : SetOf mSet"
    using setofI[OF upair_set[OF mset_smem[OF x] mset_smem[OF y]]] 
          upairE[OF mset_smem[OF x] mset_smem[OF y]] x y by auto
qed

lemmas mcons_msetof = mupair_msetof[OF _ msng_mset]
lemmas mcons_mset = m.setof_set[OF mcons_msetof]

lemma msucc_typ :
  "mSucc : mSet \<rightarrow> mSet" 
  unfolding mSucc_def
  by (rule funI, rule munion_mset, metis mcons_msetof)

lemmas msucc_mset = funE[OF msucc_typ]

lemma msucc_iff :
  assumes x : "x : mSet"
  shows "y m mSucc x \<longleftrightarrow> (y m x \<or> y = x)"
  unfolding mSucc_def munion_iff[OF mcons_msetof[OF x x]]
proof (rule, erule exE, erule conjE)
  fix z assume "z m <set, {x, <set, {x}>}>"
  hence z:"z \<in> {x, <set, {x}>}" 
    unfolding mmem_iff_mset[OF mcons_mset[OF x x]] .
  assume yz : "y m z" 
  show "y m x \<or> y = x" 
  proof (rule upairE[OF mset_smem[OF x] mset_smem[OF msng_mset[OF x]] z])
    assume "z = x" thus "y m x \<or> y = x" 
      using yz by simp
  next
    assume "z = <set,{x}>" 
    hence "y \<in> {x}" 
      using yz mmem_iff_mset[OF msng_mset[OF x]] by auto
    thus "y m x \<or> y = x" 
      unfolding sng_iff[OF mset_smem[OF x]] ..
  qed
next
  assume "y m x \<or> y = x"
  thus "\<exists>z. z m \<langle>set,{x,\<langle>set,{x}\<rangle>}\<rangle> \<and> y m z"
  proof 
   assume "y m x" 
   moreover have "x m <set, {x, <set,{x}>}>" 
    unfolding mmem_iff_mset[OF mcons_mset[OF x x]]
    using upairI1[OF mset_smem[OF x] mset_smem[OF msng_mset[OF x]]] .
   ultimately show "\<exists>z. z m <set, {x, <set,{x}>}> \<and> y m z"
    by auto
  next
    assume "y = x"
    hence "y m <set, {x}>"
      unfolding mmem_iff_mset[OF msng_mset[OF x]]
      using sngI[OF mset_smem[OF x]] by auto
    moreover have "<set, {x}> m <set, {x, <set,{x}>}>"
      unfolding mmem_iff_mset[OF mcons_mset[OF x x]]
          using upairI2[OF mset_smem[OF x] mset_smem[OF msng_mset[OF x]]] .
    ultimately show "\<exists>z. z m <set, {x, <set,{x}>}> \<and> y m z"
      by auto
  qed
qed

lemma msucc_defdes_eq : 
  assumes x : "x : mSet" 
  shows "mSucc_defdes x = mSucc x"
  unfolding m.Succ_def
proof (rule typ_defdes_eq) 
  show "mSucc x : mSet" 
    using msucc_mset[OF x] .
  show x_iff : "x : mSet \<and> (\<forall>a. (a m mSucc x) = (a m x \<or> a = x))"
    using msucc_iff[OF x] x by auto
  fix y assume "y : mSet" "x : mSet \<and> (\<forall>a. (a m y) = (a m x \<or> a = x))"
  thus "y = mSucc x"
    using mset_eq_iff[OF _ msucc_mset[OF x], of y] x_iff
    by auto
qed

lemma Theta_lim_smem : 
  assumes \<mu>:"\<mu> : Limit" and tj:"\<forall>j : Ord. j < \<mu> \<longrightarrow> \<Theta> j : mSet"
  shows "\<Theta> : (predSet \<mu>) \<leadsto> SetMem"
proof (rule mem_funI)
  fix j assume "j \<in> predSet \<mu>" 
  hence "j : Ord" "j < \<mu>" 
    using predsetD[OF limit_ord[OF \<mu>]] by auto
  thus "\<Theta> j : SetMem"
    using tj mset_smem by auto
qed
 
lemma Theta_lim_fmem :
  assumes \<mu>:"\<mu> : Limit" and tj:"\<forall>j : Ord. j < \<mu> \<longrightarrow> \<Theta> j : mSet"
  shows "\<Theta> : (predSet \<mu>) \<leadsto> FunMem"
  by (rule mem_funI, rule smem_fmem,
      erule mem_funE[OF Theta_lim_smem[OF \<mu> tj]])

(* lemma theta_lam_fun' :
  assumes u:"\<mu> : Limit" and tj:"\<forall>j : Ord. j < \<mu> \<longrightarrow> \<Theta> j : mSet"
  shows "(\<lambda>j<\<mu>. \<Theta> j) : Function" 
    using lam_fun[OF limit_fmem[OF u] Theta_lim_fmem[OF u]] tj by auto *)

(*TODO: refactor proof*)
lemma theta_tier : 
 assumes i:"j : Ord"
   shows "\<Theta> j : mSet ""\<Theta> j \<in> Tier (succ j)"
proof (induct rule: trans_induct3[OF i])
  have t0:"\<Theta> 0 = m\<emptyset>"
    unfolding ord_to_mvnord_def 
    using ordrec_0 by auto
  thus "\<Theta> 0 : mSet"
    using memp_mset  by auto 
  show "\<Theta> 0 \<in> Tier (succ 0)" 
    unfolding t0 mEmp_def 
    using tierI_mset[OF zero_typ emp_set] empty_subsetI[OF tier_ex_set[OF zero_typ]]
    by auto
next
  fix j assume j:"j : Ord" "\<Theta> j : mSet" "\<Theta> j \<in> Tier (succ j)"
  hence tj:"\<Theta> j \<in> Tier (succ j) \<ominus> set"
    using exsetI[OF tier_set[OF succ_ord[OF j(1)]] _ not_excluded_mset] by auto
  have tsucc:"\<Theta> (succ j) = mSucc (\<Theta> j)"
    unfolding ord_to_mvnord_def ordrec_succ[OF j(1)] ..
  thus "\<Theta> (succ j) : mSet"
    using msucc_mset[OF j(2)] by auto
  show "\<Theta> (succ j) \<in> Tier (succ (succ j))"
    unfolding tsucc
  proof (rule msetE[OF msucc_mset[OF j(2)]])
    fix x' assume x':"mSucc (\<Theta> j) = <set,x'>" "x' : Set"
    show "mSucc (\<Theta> j) \<in> Tier (succ (succ j))"
    proof (unfold x'(1), rule tierI_mset[OF succ_ord[OF j(1)] x'(2)], rule)
      fix a assume "a \<in> x'"
      hence "a m <set, x'>" 
        unfolding x' mmem_iff[OF x'(2)] .
      hence "a m (\<Theta> j) \<or> a = \<Theta> j"
        using x'(1) msucc_iff[OF j(2)] by auto
      thus "a \<in> Tier (succ j) \<ominus> set"
      proof (rule)
        from msetE[OF j(2)] obtain y' where y':"\<Theta> j = <set, y'>" "y' : Set" by auto
        assume "a m (\<Theta> j)" 
        hence "a \<in> Tier j \<ominus> set"
           using mmem_tier[OF j(1)] j(3) unfolding y' by auto
        thus "a \<in> Tier (succ j) \<ominus> set" 
          using ex_subset1[OF tier_set[OF j(1)] tier_set[OF succ_ord[OF j(1)]] 
                              tier_subset_succ[OF j(1)] subset_refl] by auto
      next 
        assume "a = \<Theta> j"
        thus "a \<in> Tier (succ j) \<ominus> set" using tj by auto
      qed
    qed
  qed
next
  fix \<mu> assume u:"\<mu> : Limit" and tj:"\<forall>j : Ord. j < \<mu> \<longrightarrow> \<Theta> j : mSet \<and> \<Theta> j \<in> Tier (succ j)"
  hence t_mset: "\<forall>j : Ord. j < \<mu> \<longrightarrow> \<Theta> j : mSet" by auto
  have tu:"\<Theta> \<mu> = <set, { \<Theta> j | j < \<mu>}>"
    unfolding ord_to_mvnord_def ordrec_lim[OF u] 
      repfun_ordrec_lim_restrict[OF u] .. 
    
  have tfun:"(\<lambda>j<\<mu>. \<Theta> j) : Function" 
    using lam_fun[OF lim_predset_set[OF u]] by auto
  show "\<Theta> \<mu> \<in> Tier (succ \<mu>)" unfolding tu 
  proof (rule tierI_mset[OF limit_ord[OF u]])
    show "{ \<Theta> j | j < \<mu> } : Set" 
      using repfun_lim_set[OF u] by auto
    
    show "{ \<Theta> j | j < \<mu> } \<subseteq> Tier \<mu> \<ominus> set"
    proof (rule, erule repfunE[OF lim_predset_set[OF u]], 
           drule predsetD[OF limit_ord[OF u]], auto)
      fix i assume "i : Ord" "i < \<mu>"
      moreover hence "\<Theta> i : mSet" "\<Theta> i \<in> Tier (succ i)"
        using tj by auto
      ultimately have "\<Theta> i \<in> Tier \<mu>"
        using tier_limI1[OF u succ_ord limit_lt_succ[OF u]] 
        by auto
      thus "\<Theta> i \<in> Tier \<mu> \<ominus> set"
        using exsetI[OF tier_set[OF limit_ord[OF u]]]
              not_excluded_mset[OF \<open>\<Theta> i : mSet\<close>] by auto
    qed
  qed        
  thus "\<Theta> \<mu> : mSet"  
    using msetI[OF mI[OF succ_ord[OF limit_ord[OF u]]]]
    unfolding tu by metis
qed

lemma theta_lam_fun :
  assumes u:"\<mu> : Limit" 
  shows "(\<lambda>j<\<mu>. \<Theta> j) : Function" 
    using lam_fun[OF lim_predset_set[OF u]] by auto

lemma Theta_lim_setfun :
  assumes u:"\<mu> : Limit" 
  shows "\<Theta> : (predSet \<mu>) \<leadsto> SetMem" 
proof (rule mem_funI)
 fix j assume j:"j \<in> predSet \<mu>" 
 hence "j : Ord" "j < \<mu>" 
   using predsetD[OF limit_ord[OF u]] by auto
 thus "\<Theta> j : SetMem" using theta_tier mset_smem by auto
qed

lemma theta_fmem :
  assumes \<mu>:"\<mu> : Limit"
  shows "\<Theta> : (predSet \<mu>) \<leadsto> FunMem"
  using theta_tier Theta_lim_fmem[OF \<mu>] by auto


lemma Theta_eq :
  "\<Theta> \<omega> = <set, {\<Theta> i | i < \<omega>}>" 
   unfolding ordrec_lim[OF omega_typ] ord_to_mvnord_def
             repfun_ordrec_lim_restrict[OF omega_typ] ..

lemma minf_mset : "mInf : mSet"
  unfolding mInf_def 
  using theta_tier(1)[OF omega_ord] by simp

lemma minf_iff : "b m mInf \<longleftrightarrow> (\<exists>i<\<omega>. b = \<Theta> i)"
  unfolding 
    mInf_def Theta_eq 
    mmem_iff[OF repfun_set[OF predset_set[OF omega_ord]]]
    repfun_iff[OF predset_set[OF omega_ord]]
    ord_ex_iff[OF omega_ord]
 using
    mset_smem[OF theta_tier(1)] 
 by auto

lemma minf_msetof : 
  "mInf : mSetOf mSet"
proof (rule m.setofI[OF minf_mset])
  fix b assume "b m mInf"
  thus "b : mSet"
    unfolding minf_iff
    using theta_tier by auto
qed

lemma memp_mem_minf : 
  "mEmp m mInf"
  unfolding minf_iff
proof (rule texI[OF zero_typ], auto)
  show "0 < \<omega>" 
    using omega_zero .
  show "m\<emptyset> = \<Theta> 0" 
    unfolding ord_to_mvnord_def
    using ordrec_0 by auto
qed

lemma msucc_mem_minf : 
  assumes x:"x m mInf"
  shows "mSucc x m mInf"
  unfolding minf_iff
proof -
  from x obtain i where
    i : "i : Ord" "i < \<omega>" "x = \<Theta> i"
    using minf_iff by auto
  hence "mSucc x = \<Theta> (succ i)"
    unfolding ord_to_mvnord_def
    using ordrec_succ[OF i(1)] by auto
  thus "\<exists>j: Ord. j < \<omega> \<and> mSucc x = \<Theta> j"
    using succ_ord omega_succ i by auto
qed


section \<open>Model replacement\<close>

abbreviation "mReplPred \<equiv> m.ReplPred"

lemma tex_mtex_mset :
  "(\<exists>x : mSet. P x) = (m\<exists> x : mSet. P x)"
  unfolding mtex_def mex_def tex_def 
  using mset_m by auto

abbreviation "mSetMem \<equiv> m.SetMem"

lemma msmem_m :
  assumes b:"b : mSetMem"
  shows "b : M"
proof -
  from b obtain x where 
    x:"x : mSet" and bx:"b m x" 
    unfolding m.SetMem_def has_ty_def tex_def by auto
  thus "b : M"
    using mmem_m by auto
qed

lemma mSetMem_eq : 
  "mSetMem b = (m\<exists>x : mSet. b m x)"
  unfolding m.SetMem_def tex_mtex_mset ..

lemma mSetOf_eq : 
   "mSetOf P x = (x : mSet \<and> (m\<forall>b. b m x \<longrightarrow> b : P))"
 unfolding m.SetOf_def mall_def using mmem_m by blast



lemma mtuniq_generalize : 
   "(m\<exists>\<^sub>\<le>\<^sub>1 b : mSetMem. P b)  = (\<exists>\<^sub>\<le>\<^sub>1 b : mSetMem. P b)"
  using msmem_m
  unfolding mtuniq_def muniq_def tuniq_def Uniq_def by auto

lemma mReplPred_eq : 
  "mReplPred x P = (x : mSet \<and> (m\<forall>a. a m x \<longrightarrow> (m\<exists>\<^sub>\<le>\<^sub>1 b : mSetMem. P a b)))"
  unfolding m.ReplPred_def mtuniq_generalize 
  using mball_generalize[of x \<open>\<lambda>a. tuniq mSetMem (P a)\<close>] by auto

lemma msmem_smem : 
  assumes b : "b : mSetMem" 
  shows "b : SetMem"
proof -
  from b obtain x where 
    x : "x : mSet" and b : "b m x"
    unfolding m.SetMem_def tex_def has_ty_def by auto
  then obtain x' where x' : "x = <set, x'>" "x' : Set"
    using msetE by auto
  hence bx:"b \<in> x'" using mmemD b by auto
  thus "b : SetMem" using setmemI[OF x'(2)] by auto
qed

lemma msmem_not_excluded :
  assumes b:"b : mSetMem"
  shows "\<not> Excluded set b"
proof -
  from b obtain x where 
    x:"x : mSet" and bx:"b m x" 
    unfolding m.SetMem_def has_ty_def tex_def by auto
  obtain x' where "x = <set,x'>" "b \<in> x'"
    by (rule msetE[OF x], metis mmemD bx)
  then obtain j where "j : Ord" and "<set,x'> \<in> Tier (succ j)"
    using tier_succI1 mE[OF mset_m[OF x]] by metis
  hence "x' \<subseteq> Tier j \<ominus> set"
    using tierD_mset by auto
  thus "\<not> Excluded set b"
    using exsetD2[OF tier_set[OF \<open>j : Ord\<close>]] \<open>b \<in> x'\<close> by auto
qed


lemma mreplpred_replpred : 
  assumes x : "<set,x'> : mSet" and P : "P : mReplPred <set,x'>"
  shows "(\<lambda>a b. P a b \<and> b : mSetMem) : ReplPred x'"
  unfolding ReplPred_def
proof (rule tyI, auto, rule mset_set[OF x])
  fix a assume "a \<in> x'"
  hence "a m <set,x'>" using mmemI_mset[OF x] by auto
  hence uniq:"\<exists>\<^sub>\<le>\<^sub>1 b : mSetMem. P a b" 
     using P unfolding m.ReplPred_def has_ty_def by auto
  thus "\<exists>\<^sub>\<le>\<^sub>1 b : SetMem. P a b \<and> b : mSetMem" 
   unfolding tuniq_def Uniq_def using msmem_smem by auto
  
qed

lemma mrepl_eq : 
  "mRepl x P = <set, { b | \<exists>a \<in> snd x. P a b \<and> b : mSetMem }>"
  unfolding mRepl_def tex_def m.setmem_iff ..

lemma mrepl_iff :
  assumes x : "x : mSet" and P : "P : mReplPred x"
  shows "b m mRepl x P \<longleftrightarrow> (\<exists>a. a m x \<and> P a b \<and> b : mSetMem)"  
proof -
  obtain x' where x' : "x = <set,x'>" "x' : Set" 
    using msetE[OF x] by auto
  have Px' : "(\<lambda>a b. P a b \<and> b : mSetMem) : ReplPred x'" 
    using mreplpred_replpred P x unfolding x' by auto
  have mrepl_eq : "mRepl x P = <set, { b | \<exists>a\<in>x'. P a b \<and> b : mSetMem }>"
    unfolding mrepl_eq x' mset_snd_eq[OF x'(2)] ..

  show ?thesis 
    unfolding mrepl_eq mmem_iff[OF repl_set[OF x'(2) Px']] 
              replace_iff[OF x'(2) Px'] mmem_iff_eq[OF x x'(1)]
    using     msmem_smem
              by auto
qed              

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
    unfolding mrepl_eq x' mset_snd_eq[OF x'(2)] ..
  show "mRepl x P : mSet" 
    unfolding mrepl_eq
  proof (rule setof_mset, rule setofI[OF repl_set[OF x'(2) Px']], rule_tac [2] ballI)
    fix b assume "b \<in> ?R"
    hence "b m mRepl x P"
      using mmemI[OF repl_set[OF x'(2) Px']]
      unfolding mrepl_eq by auto
    then obtain a where "a m x" "P a b" "b : mSetMem"
      using mrepl_iff[OF x P] by auto
    thus "b : M" "\<not> Excluded set b"
      using msmem_m msmem_not_excluded by auto
   qed
qed


theorem mGZF : "class.GZF SetModel_mdefault mSet mMem mUnion mPow mInf mRepl"
proof (unfold_locales)
  show "m\<Union> : mSetOf mSet \<rightarrow> mSet" using munion_typ .
  show "m\<P> : mSet \<rightarrow> mSetOf mSet" using mpow_typ .
  show "mInf : mSet" using minf_mset .
  show "m\<R> : (\<Pi> x:mSet. mReplPred x \<rightarrow> mSet)" using mrepl_typ .
  show "\<forall>x : mSet. \<forall>y : mSet. (\<forall>a. (a m x) = (a m y)) \<longrightarrow> x = y"
    using mset_eq_iff by auto
  show "\<forall>x : mSetOf mSet. \<forall>a. (a m m\<Union> x) = (\<exists>z. z m x \<and> a m z)"
    using munion_iff by auto
  show "\<forall>x : mSet. \<forall>z : mSet. (z m m\<P> x) = m.Subset z x" 
    using mpow_iff mmem_m 
    unfolding msub_def m.Subset_def mall_def tall_def by blast
  show "mEmp_defdes m mInf \<and> (\<forall>a. a m mInf \<longrightarrow> mSucc_defdes a m mInf)"
    using memp_mem_minf msucc_mem_minf msucc_defdes_eq[OF m.setof_mem[OF minf_msetof]]
    unfolding memp_eq by auto
  show "\<forall>x : mSet. \<forall>P : mReplPred x. \<forall>b. (b m m\<R> x P) = (\<exists>a. a m x \<and> P a b \<and> b : mSetMem)"
    using mrepl_iff by auto
qed

ML \<open>val mGZF = 
    mk_msig [] "mGZF" @{class GZF} 
      ["SetModel_mdefault", "mSet", "mMem", 
       "mUnion", "mPow", "mInf", "mRepl"] @{context}\<close>
translate_axioms mGZF_axioms : mGZF  
proof -
  show "m\<forall>x. x : mSetOf mSet \<longrightarrow> m\<Union> x : mSet" 
    using munion_mset by auto
  show "m\<forall>x. x : mSet \<longrightarrow> m\<P> x : mSetOf mSet"
    using funE[OF mpow_typ] by auto
  show "m\<forall>x. x : mSet \<longrightarrow> (\<forall>xa. xa : mReplPred x \<longrightarrow> m\<R> x xa : mSet)"
    using funE[OF depfunE[OF mrepl_typ]] by auto
  show "mInf : mSet" 
    using minf_mset by auto
  show "m\<forall>x:mSet. m\<forall>y:mSet. (m\<forall>a. (a m x) = (a m y)) \<longrightarrow> x = y"
    using mset_eq_iff mmem_m unfolding mtall_def mall_def tall_def by blast
  show "m\<forall>x:mSetOf mSet. m\<forall>a. (a m m\<Union> x) = (m\<exists>z. z m x \<and> a m z)"
    using munion_iff mmem_m[OF m.setof_set]
    unfolding mex_def tex_def mall_def mtall_def by blast
  show "m\<forall>x:mSet. m\<forall>z:mSet. (z m m\<P> x) = mSubset z x"
    sorry
  show "mEmp_defdes m mInf \<and> (m\<forall>a. a m mInf \<longrightarrow> mSucc_defdes a m mInf)"
    using memp_mem_minf msucc_mem_minf msucc_defdes_eq[OF m.setof_mem[OF minf_msetof]]
    unfolding mall_def tall_def memp_eq by auto
  show "m\<forall>x:mSet. \<forall>P : mReplPred x. m\<forall>b. (b m m\<R> x P) = (m\<exists>a. a m x \<and> P a b \<and> b : mSetMem)"
    using mrepl_iff mmem_m 
    unfolding mall_def mtall_def mall_def tall_def mtex_def tex_def mex_def
    by blast
qed


(*Respectfulness theorems do not currently hold,
  because currently most model-operators only give a result in M
  when their input is an mSet.
  Need to use if-else-statements like before defaulting to SetModel_mdefault

  To make this change nicer, we should split this huge file into many 
  small ones within a 'Model' directory.

  Also, there is an issue with Subset which we need to find a workaround for.
    - translate_axioms will always generate a power set axiom using m.Subset   
    - We can't define a transfer rule between d1.Subset and m.Subset,
      because the definition of subset involves a quantifier that can't be relativized
  Possible fix: make mMem only hold for mSets, so that we can have that
     (\<forall>a. a m x \<longrightarrow> a m y) = (m\<forall>a. a m x \<longrightarrow> a m y)



  Possible issue with transfer rules for post-signature simple definitions.
  At this rate, we will have to reprove transfer rules for simple defs 
  each time we connect a new domain....
  potential fix: add simple defs to the axioms of locale?
*)




end


ML \<open>msig_app mGZF (Binding.name "Union")\<close>

ML_file \<open>../ModelKit/lift_model_sig.ML\<close>

typedecl d0  

instance d0 :: SetModel  sorry

typedef (overloaded) d1 = \<open>Set.Collect (\<lambda>x :: d0. x : M)\<close> using SetModel_mdefault_m by auto

setup_lifting type_definition_d1 

global_interpretation ConnectionBase Abs_d1 Rep_d1 pcr_d1
  by (unfold ConnectionBase_def, rule,
      rule type_definition_d1, unfold pcr_d1_def cr_d1_def, auto)

instantiation d1 :: GZF_sig 
begin
  local_setup \<open>lift_mconsts @{thms mGZF_resp} (@{typ d1}) mGZF\<close> 
  instance ..
end

lemma setof_transfer [transfer_rule] : 
  "(rel_fun (rel_fun pcr_d1 iff) (rel_fun pcr_d1 iff)) mSetOf SetOf"
  unfolding mSetOf_eq SetOf_def
  by (transfer_prover)
             
lemma setmem_transfer [transfer_rule] : 
  "(rel_fun pcr_d1 iff) mSetMem SetMem"
  unfolding mSetMem_eq SetMem_def mtex_def tex_def
  by (transfer_prover)

lemma subset_transfer [transfer_rule] :
  "(rel_fun pcr_d1 (rel_fun pcr_d1 iff)) msub Subset"
  unfolding msub_def Subset_def 
  by (transfer_prover) 

lemma emp_transfer [transfer_rule] : 
  "(pcr_d1) mEmp_defdes Emp"
  unfolding Emp_def mEmp_defdes_eq
  by (transfer_prover)  

lemma succ_transfer [transfer_rule] : 
  "(rel_fun pcr_d1 pcr_d1) mSucc_defdes Succ"
  unfolding Succ_def mSucc_defdes_eq
  by (transfer_prover)

lemma replpred_transfer [transfer_rule] : 
  "(rel_fun pcr_d1 (rel_fun (rel_fun pcr_d1 (rel_fun pcr_d1 iff)) iff)) mReplPred ReplPred"
  unfolding mReplPred_eq ReplPred_def mtuniq_def tuniq_def
  by (transfer_prover)

ML_file \<open>../transfer_all_method.ML\<close>
instantiation d1 :: GZF begin
instance 
proof (intro_classes, unfold funty_eq depfunty_eq, transfer_all)
  thm mGZF_axioms
  have "\<forall>x :: d1. \<forall>z. z \<in> \<P> x \<longleftrightarrow> z \<subseteq> x"
  proof (transfer)
    thm tall_transfer
  show "(Union :: d1 \<Rightarrow> d1) : SetOf Set \<rightarrow> Set" 
  by (unfold funty_eq, transfer, rule mGZF_axioms(1))
  show "\<R> : (\<Pi> (x :: d1) :Set. ReplPred x \<rightarrow> Set)"
(*  



(*Lifting_Setup.setup_by_typedef_thm*)
ML \<open>Transfer.get_transfer_raw @{context}\<close>
thm mGZF_resp(2)
lift_definition GZF_default_d1 :: \<open>d1\<close> is SetModel_mdefault by (rule SetModel_mdefault_m)
lift_definition Set_d1 :: \<open>d1 \<Rightarrow> bool\<close> is mSet .
lift_definition Mem_d1:: \<open>d1 \<Rightarrow> d1 \<Rightarrow> bool\<close> is mMem .
(* lift_definition Union_d1 :: \<open>d1 \<Rightarrow> d1\<close> is mUnion
  by (tactic \<open>solve_tac @{context} @{thms mGZF_resp} 1\<close>)
 *)
lift_definition Pow_d1 :: \<open>d1 \<Rightarrow> d1\<close> is mPow sorry
lift_definition Inf_d1 :: \<open>d1\<close> is mInf sorry




ML \<open>val mdef = Syntax.read_term @{context} 
  (YXML.content_of (Syntax.string_of_term @{context} (hd (mcomp_ran mGZF))))\<close>
ML \<open>val unfree = Free ("Union",@{typ \<open>'a \<Rightarrow> 'a\<close>})\<close>
ML \<open>val mun_bad = mcomp_app mGZF unfree\<close>
ML \<open>val mun = mcomp_app mGZF (Syntax.read_term @{context} "mUnion")\<close>
local_setup \<open>fn lthy => 
  lift_mconst (rsp_thms_tac @{thms mGZF_resp}) @{typ \<open>d1\<close>}
    ((unfree , @{term mUnion}), lthy)\<close>

term Union_new
thm Union_new_def
ML \<open>@{thms mGZF_resp(2)}\<close>

 *)

(*TODO: 
 - write code to ask the user to prove the goals generated by lifitng
   
   can't use utilize Lifitng package for this purpose because:
    - generating respectfulness goals doesn't work if lifting_setup hasn't been run yet
    - much of the code is not made available in ML interface
   solution: use own code from model_closed instead

 - write a tactic that uses these theorems to prove the goals generated by lifitng 



 *)
 
(*TODO bundle for removing Isabelle/HOL style transfer rules, replacing with ours*)


