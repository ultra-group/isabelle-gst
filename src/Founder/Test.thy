theory Test
  imports  
    "../Ordinal/Model/OrdRec_Model" 
    "../Functions/Model/Function_Model"
    "../OPair/Model/OPair_Model_Base"
    "../Exception/Exception_Model"
    ZFC_in_HOL_Bootstrap
begin 

ML_file \<open>../ModelKit/Tools/model_implementation.ML\<close>
instance V :: Tagging ..

lemma if_cases : 
  assumes "Q \<Longrightarrow> P x" "\<not> Q \<Longrightarrow> P y"
  shows "P (if Q then x else y)"
  using assms by auto

lemma if_cases2 :
  assumes "P y" "Q \<Longrightarrow> P x" 
  shows "P (if Q then x else y)"
  using if_cases assms by auto

lemma int_typ_eq :
  "x : P \<triangle> Q \<longleftrightarrow> x : P \<and> x : Q"
  unfolding inter_ty_def has_ty_def by auto

lemma disjointI :
  assumes "x : P \<Longrightarrow> x : Q \<Longrightarrow> False"
  shows "(x : P \<triangle> Q) = (x : \<bottom>)"
  using assms
  unfolding has_ty_def inter_ty_def empty_typ_def by auto


lemma setmem_any : "(b :: V) : SetMem"
  using set_setmem[where 'a = V] 
  unfolding has_ty_def Set_V_def by auto

lemmas pair_inject_any = 
  pair_inject[OF pair_pair[OF setmem_any setmem_any] 
                 pair_pair[OF setmem_any setmem_any]]

lemma four_neq :
  "succ (succ (succ (succ 0))) \<noteq> 0"
  "succ (succ (succ (succ 0))) \<noteq> succ 0"
  "succ (succ (succ (succ 0))) \<noteq> succ (succ 0)"
  "succ (succ (succ (succ 0))) \<noteq> succ (succ (succ 0))"
  by (tactic \<open>REPEAT_DETERM (Proof_Context.fact_tac \<^context> 
        [neq_thm (4,0), neq_thm (4,1), neq_thm (4,2), neq_thm (4,3)] 1)\<close>)

instantiation 
  V :: \<open>ModelBase\<close> 
begin
  definition mexc' :: V where 
    "mexc' = <succ (succ (succ (succ 0))), \<emptyset>>"

  lemma fst_mexc : "\<tau> mexc' = succ (succ (succ (succ 0)))"
    unfolding mexc'_def 
    using OPair.fst_eq[OF setmem_pair[OF setmem_any setmem_any]] by auto

  local_setup 
  \<open> model_implementation \<^typ>\<open>V\<close> [ordrec_model, pair_model, func_model, exc_model] 
    [\<^term>\<open>\<lambda>b :: V. b = mexc'\<close>,\<^term>\<open>\<lambda>b :: V. b = mexc'\<close>, \<^term>\<open>\<lambda>b :: V. b = mexc'\<close>,
     \<^term>\<open>\<lambda>b :: V. b = mexc'\<close>, \<^term>\<open>\<lambda>b :: V. b = mexc'\<close>]
    [\<^term>\<open>Set :: V \<Rightarrow> bool\<close>, \<^term>\<open>Ord :: V \<Rightarrow> bool\<close>, \<^term>\<open>Pair :: V \<Rightarrow> bool\<close>,
     \<^term>\<open>Function :: V \<Rightarrow> bool\<close>, \<^term>\<open>Set :: V \<Rightarrow> bool\<close>]\<close>
  instance proof 
    show "Variants : (\<Pi> (i :: V) : Tag. nonLimit \<rightarrow> Set \<rightarrow> SetOf (\<alpha> i))"
    proof (rule depfunI, rule funI, rule funI)
      fix i :: V and j :: V and x :: V 
      assume "i : Tag" "j : nonLimit" and x :"x : Set"
      hence "i : Ord" "i < \<omega>" and j : "j : Ord"  
        using tagD nonlimit_ord by auto
        
      show "Variants i j x : SetOf (\<alpha> i)"
        unfolding Variants_V_def
      proof (rule if_cases2[OF if_cases2[OF if_cases2[OF if_cases2[OF if_cases2]]]])
        assume "i = 0"
        thus "caseof_ord \<emptyset> (\<P> x) \<emptyset> j : SetOf (\<alpha> i)"
          using gzf_model_case_typ[OF j x] \<alpha>_V_0 by auto
      next
        assume "i = succ 0"
        thus "caseof_ord {0} {j} {j} j : SetOf (\<alpha> i)"
          using ord_model_case_typ[OF j] \<alpha>_V_1 by auto
      next
        assume "i = succ (succ 0)"
        thus "caseof_ord \<emptyset> (x \<times> x) \<emptyset> j : SetOf (\<alpha> i)"
          using pair_model_case_typ[OF j x] \<alpha>_V_2 by auto
      next
        assume "i = succ (succ (succ 0))"
        thus "caseof_ord \<emptyset> (x \<midarrow>p\<rightarrow> x) \<emptyset> j : SetOf (\<alpha> i)"
          using func_model_case_typ[OF j x] \<alpha>_V_3 by auto
      next
        assume "i = succ (succ (succ (succ 0)))"
        thus "caseof_ord {\<emptyset>} \<emptyset> \<emptyset> j : SetOf (\<alpha> i)"
          using exc_model_case_typ[OF j] \<alpha>_V_4 by auto
      next
        show "\<emptyset> : SetOf (\<alpha> i)"
        using emp_setof by auto
      qed
    qed

    show "Variants : (\<Pi> (i :: V) :Tag. Limit \<rightarrow> Function \<rightarrow> SetOf (\<alpha> i))"
    proof (rule depfunI, rule funI, rule funI)
      fix i :: V and u :: V and f :: V 
      assume "i : Tag" and u : "u : Limit" and f :"f : Function"
      show "Variants i u f : SetOf (\<alpha> i)"
        unfolding Variants_V_def case_ord_lim[OF u]
        using sng_setof[OF ord_setmem[OF limit_ord[OF u]] limit_ord[OF u]]
              \<alpha>_V_1 emp_setof by auto
   qed
 qed
end   

instantiation 
  V :: ModelBase'
begin
  definition mdefault_V :: V
    where "mdefault_V \<equiv> <succ (succ (succ (succ 0))),\<emptyset>>"
  instance proof
    let ?four = "succ (succ (succ (succ 0)))"
    show "(mdefault :: V) : M"
      unfolding mdefault_V_def
    proof (rule mI[OF zero_ord], rule tier0I)    
      show "?four : Tag" 
        by (tactic \<open>Proof_Context.fact_tac \<^context> [tag_thm 4] 1\<close>)
  
      show "(\<emptyset> :: V) \<in> Variants ?four 0 \<emptyset>"
        unfolding Variants_V_4_zero
                  sng_iff[OF set_setmem[OF emp_set]]
        by auto
    qed
  qed
end

instantiation 
  V :: \<open>{GZF_Model, Ordinal_Model, OrdRec_Model,
          OPair_Model, Function_Model, Exc_Model}\<close> 
begin
  local_setup \<open>defn_tags_defaults \<^typ>\<open>V\<close> 
       [(set_model, \<^term>\<open>mdefault :: V\<close>), (ord_model, \<^term>\<open>mdefault :: V\<close>),
        (ordrec_model, \<^term>\<open>mdefault :: V\<close>),
        (pair_model, \<^term>\<open>mdefault :: V\<close>), (func_model, \<^term>\<open>mdefault :: V\<close>),
        (exc_model, \<^term>\<open>mdefault :: V\<close>)]\<close> 

  instance 
  proof
    show 
      "(GZF_Model_mdefault :: V) : M"
      "(Ordinal_Model_mdefault :: V) : M"    
      "(OrdRec_Model_mdefault :: V) : M"
      "(OPair_Model_mdefault :: V) : M"
      "(Function_Model_mdefault :: V) : M"
      "(Exc_Model_mdefault :: V) : M"      
      unfolding 
        GZF_Model_mdefault_V_def
        Ordinal_Model_mdefault_V_def
        OrdRec_Model_mdefault_V_def
        OPair_Model_mdefault_V_def
        Function_Model_mdefault_V_def
        Exc_Model_mdefault_V_def
      using 
        mdefault_m by auto

    show 
      "(GZF_Model_class.set :: V) : Tag"
      "(ord :: V) : Tag"
      "(opair :: V) : Tag"
      "(func :: V) : Tag"
      "(exc_tag :: V) : Tag"
    unfolding 
      set_V_def ord_V_def opair_V_def 
      func_V_def exc_tag_V_def
    by (tactic \<open>REPEAT_DETERM (Proof_Context.fact_tac \<^context> 
          [tag_thm 0, tag_thm 1, tag_thm 2, tag_thm 3, tag_thm 4] 1)\<close>)

    show
      "\<alpha> (GZF_Model_class.set :: V) = Set"
      "\<alpha> (ord :: V) = Ord"
      "\<alpha> (opair :: V) = Pair"
      "\<alpha> (func :: V) = Function"
      "\<alpha> (exc_tag :: V) = Set"
    unfolding
      \<alpha>_V_0 \<alpha>_V_1 \<alpha>_V_2 \<alpha>_V_3 \<alpha>_V_4
      set_V_def ord_V_def opair_V_def 
      func_V_def exc_tag_V_def
    by auto

    show 
      "Variants (GZF_Model_class.set :: V) 0 = (\<lambda>x. \<emptyset>)"
      "\<And>j. j : Ord \<Longrightarrow> Variants (GZF_Model_class.set :: V) (succ j) = Pow"
      "\<And>u. u : Limit \<Longrightarrow> Variants (GZF_Model_class.set :: V) u = (\<lambda>_. \<emptyset>)"
    unfolding set_V_def
    using Variants_V_0_zero Variants_V_0_succ Variants_V_0_lim by auto
    
    show 
      "Variants ord 0 = (\<lambda>x::V. {0})"
      "\<And>j::V. j : Ord \<Longrightarrow> Variants ord (succ j) = (\<lambda>x::V. {succ j})"
      "\<And>u::V. u : Limit \<Longrightarrow> Variants ord u = (\<lambda>f::V. {u})"
    unfolding ord_V_def
    using Variants_V_1_zero Variants_V_1_succ Variants_V_1_lim by auto

    show
      "Variants opair 0 = (\<lambda>x::V. \<emptyset>)"
      "\<And>j::V. j : Ord \<Longrightarrow> Variants opair (succ j) = (\<lambda>y::V. y \<times> y)"
      "\<And>u::V. u : Limit \<Longrightarrow> Variants opair u = (\<lambda>_::V. \<emptyset>)"
    unfolding opair_V_def
    using Variants_V_2_zero Variants_V_2_succ Variants_V_2_lim by auto

    show 
      "Variants func 0 = (\<lambda>x::V. \<emptyset>)"
      "\<And>j::V. j : Ord \<Longrightarrow> Variants func (succ j) = (\<lambda>x::V. x \<midarrow>p\<rightarrow> x)"
      "\<And>u::V. u : Limit \<Longrightarrow> Variants func u = (\<lambda>_::V. \<emptyset>)"
    unfolding func_V_def
    using Variants_V_3_zero Variants_V_3_succ Variants_V_3_lim by auto

    show 
      "Variants exc_tag 0 = (\<lambda>x::V. {\<emptyset>})"
      "\<And>j::V. j : Ord \<Longrightarrow> Variants exc_tag (succ j) = (\<lambda>y::V. \<emptyset>)"
      "\<And>u::V. u : Limit \<Longrightarrow> Variants exc_tag u = (\<lambda>_::V. \<emptyset>)"
    unfolding exc_tag_V_def
    using Variants_V_4_zero Variants_V_4_succ Variants_V_4_lim by auto

    show "\<And>x' :: V. \<not> Excluded GZF_Model_class.set \<langle>GZF_Model_class.set,x'\<rangle>"
      using Excluded_V_0 four_neq(1) pair_inject_any
      unfolding set_V_def mexc'_def pair_V_def by (metis)
    
    show "\<And>j'::V. \<not> Excluded GZF_Model_class.set \<langle>ord,j'\<rangle>"
      using Excluded_V_0 four_neq(2) pair_inject_any
      unfolding ord_V_def set_V_def mexc'_def pair_V_def by metis
      
    show "\<And>p'::V. \<not> Excluded opair \<langle>opair,p'\<rangle>"
      using Excluded_V_2 four_neq(3) pair_inject_any
      unfolding opair_V_def mexc'_def pair_V_def by metis

    show "\<And>f'::V. \<not> Excluded func \<langle>func,f'\<rangle>"
      using Excluded_V_3 four_neq(4) pair_inject_any
      unfolding func_V_def mexc'_def pair_V_def by metis

    show "Excluded (GZF_Model_class.set :: V) << Excluded func"
      unfolding set_V_def func_V_def
      unfolding Excluded_V_0 Excluded_V_3
      by (rule subtypI)
qed
end

typedef d1 = 
  "Set.Collect (\<lambda>x :: V. x : M)" using mdefault_m by auto

setup_lifting type_definition_d1

interpretation ConnectionBase Abs_d1 Rep_d1 pcr_d1 mdefault
  by (unfold ConnectionBase_def, rule, rule type_definition_d1, 
      unfold pcr_d1_def cr_d1_def, auto, rule mdefault_m)

instantiation d1 :: GZF begin
  local_setup \<open>lift_mconsts @{thms mGZF_resp} \<^typ>\<open>d1\<close> mGZF\<close>

  instance 
  by (intro_classes, unfold funty_eq depfunty_eq, transfer_all,
      tactic \<open>REPEAT_DETERM (Proof_Context.fact_tac \<^context> @{thms mGZF_axioms} 1)\<close>)
  end

instantiation d1 :: Ordinal begin
  local_setup \<open>lift_mconsts @{thms mOrdinal_resp} \<^typ>\<open>d1\<close> mOrdinal\<close>
  instance
  by (intro_classes, unfold funty_eq depfunty_eq, transfer_all,  
    tactic \<open>REPEAT_DETERM (Proof_Context.fact_tac \<^context> @{thms mOrdinal_axioms} 1)\<close>)
end

instantiation d1 :: OrdRec begin
  local_setup \<open>lift_mconsts @{thms mOrdRec_resp} \<^typ>\<open>d1\<close> mOrdRec\<close>
  instance
  by (intro_classes, unfold funty_eq depfunty_eq, transfer_all,  
    tactic \<open>REPEAT_DETERM (Proof_Context.fact_tac \<^context> @{thms mOrdRec_axioms} 1)\<close>)
end

instantiation d1 :: OPair begin
  local_setup \<open>lift_mconsts @{thms mOPair_rsp} \<^typ>\<open>d1\<close> mOPair\<close>
  instance
  by (intro_classes, unfold funty_eq depfunty_eq, transfer_all,  
    tactic \<open>REPEAT_DETERM (Proof_Context.fact_tac \<^context> @{thms mOPair_axioms} 1)\<close>)
end

instantiation d1 :: Function begin
  local_setup \<open>lift_mconsts @{thms mFunction_rsp} \<^typ>\<open>d1\<close> mFunction\<close>
  instance 
  by (intro_classes, unfold funty_eq depfunty_eq, transfer_all,
    tactic \<open>REPEAT_DETERM (Proof_Context.fact_tac \<^context> @{thms mFunction_axioms} 1)\<close>)
end

instantiation d1 :: Exc begin
  local_setup \<open>lift_mconsts @{thms mExc_rsp} \<^typ>\<open>d1\<close> mExc\<close>
  instance 
    by (intro_classes, transfer, rule mexc_ax)
end

lemma top_transfer [transfer_rule] :
  "rel_fun pcr_d1 iff (\<top>) (\<top>)"
  unfolding Any_def by auto

lemma bot_transfer [transfer_rule] :
  "rel_fun pcr_d1 iff (\<bottom>) (\<bottom>)"
  unfolding empty_typ_def by auto

lemma uni_typ_eq : 
 "x : P \<mho> Q \<longleftrightarrow> x : P \<or> x : Q"
 unfolding union_ty_def has_ty_def by auto
 
declare [[show_types = true, show_sorts = true, goals_limit = 100]]  

instantiation d1 :: ZFplus begin
  instance proof (intro_classes, unfold pred_ty_eq subtyp_eq, transfer_all)
   show "m\<forall>x. \<not> x : mSetOf mSet \<longrightarrow> m\<Union> x = GZF_Model_mdefault"
    unfolding mUnion_def by auto
   show "m\<forall>x. \<not> x : mSet \<longrightarrow> m\<P> x = GZF_Model_mdefault"
    unfolding mPow_def by auto
   show "m\<forall>x. \<not> x : mSet \<longrightarrow> mSucc x = GZF_Model_mdefault"
    unfolding mSucc_def by auto
   show "m\<forall>x. \<forall>xa. \<not> x : mSet \<or> \<not> xa : mReplPred x \<longrightarrow>
               m\<R> x xa = GZF_Model_mdefault"
    unfolding mRepl_def by auto
   show "m\<forall>x. \<not> x : mOrd \<longrightarrow> msucc x = Ordinal_Model_mdefault"
    unfolding msucc_def by auto
   show "m\<forall>x xa. \<not> x : mPairMem \<or> \<not> xa : mPairMem \<longrightarrow>
       mpair x xa = (OPair_Model_mdefault :: V)"
   proof -
     have "\<not> (OPair_Model_mdefault :: V) : mPair"
      unfolding mPair_def
     proof (rule, drule intE, auto elim: partE)
      assume "(OPair_Model_mdefault :: V) :\<^enum> opair"
      then obtain p :: V where "OPair_Model_mdefault = <opair,p>"
        using partE by metis
      thus "False"
        unfolding OPair_Model_mdefault_V_def mdefault_V_def 
          pair_V_def opair_V_def
        using pair_inject_any(1) four_neq(3) by auto
     qed
     thus ?thesis
      unfolding mpair_def by auto
   qed
   
   show "m\<forall>x. \<forall>xa. \<not> x : mSet \<or> \<not> xa : mFunPred x \<longrightarrow>
           mk_mfun x xa = Function_Model_mdefault"
     unfolding mk_mfun_def by auto
   show "m\<forall>x. \<not> x : mFunc \<longrightarrow> mdom x = Function_Model_mdefault"
    unfolding mdom_def by auto
   show "m\<forall>x. \<not> x : mFunc \<longrightarrow> mran x = Function_Model_mdefault"
    unfolding mran_def by auto
   show "m\<forall>x xa. \<not> x : mSet \<or> \<not> xa : mSet \<longrightarrow>
       mfspace x xa = Function_Model_mdefault"
    unfolding mfspace_def by auto
    
  show 
   "(GZF_Model_mdefault :: V) = mexc"
   "(Ordinal_Model_mdefault :: V) = mexc"
   "(OPair_Model_mdefault :: V) = mexc"
   "(Function_Model_mdefault :: V) = mexc"
   "(mexc :: V) = mexc"
  unfolding
    GZF_Model_mdefault_V_def
    Ordinal_Model_mdefault_V_def
    OPair_Model_mdefault_V_def
    Function_Model_mdefault_V_def 
    mdefault_V_def mexc_def exc_tag_V_def 
  by auto
  
   
  show "m\<forall>x :: V. (x : mSet \<mho> (mOrd \<mho> (mPair \<mho> (mFunc \<mho> mExc)))) = (x : \<top>)"
  proof (rule, rule, rule anyI, unfold uni_typ_eq)
    fix x :: V assume "x : M"
    hence x : "x : (\<Sigma> i : Tag. \<alpha> i)"
      using m_depsum by auto
    obtain i :: V and x' :: V where 
      i : "i : Tag" and x': "x' : \<alpha> i" and
      x_eq : "x = <i, x'>" and x_pair : "x : Pair"
      unfolding pair_V_def
      by (metis \<open>(x::V) : M\<close> mtagE pair_V_def)
    hence "i = GZF_Model_class.set \<or> i = ord \<or> i = opair 
            \<or> i = func \<or> i = exc_tag"
      unfolding 
        \<alpha>_V_def set_V_def ord_V_def opair_V_def
        func_V_def exc_tag_V_def
      using empty_typD[where 'a = V] 
      by fastforce
    thus
      "x : mSet \<or> x : mOrd \<or> x : mPair \<or> x : mFunc \<or> x : mExc"
    unfolding mSet_def mOrd_def mPair_def mFunc_def mExc_def
    using intI[OF \<open>x : M\<close> partI[OF x_eq x_pair]]
    by auto
  qed
  
  show "m\<forall>x::V. (x : mSet \<triangle> mOrd) = (x : \<bottom>)"
  proof (rule, rule disjointI)
    fix x :: V assume 
      "x : mSet" "x : mOrd"
    hence
      "\<tau> x = GZF_Model_class.set" "\<tau> x = ord"
      unfolding mSet_def mOrd_def int_typ_eq
      using partD by auto
    thus "False"
      unfolding set_V_def ord_V_def
      by (tactic \<open>Method.insert_tac \<^context> [neq_thm (1,0)] 1\<close>, auto)       
  qed

  show "m\<forall>x::V. (x : mSet \<triangle> mPair) = (x : \<bottom>)"
  proof (rule, rule disjointI)
    fix x :: V assume 
      "x : mSet" "x : mPair"
    hence
      "\<tau> x = GZF_Model_class.set" "\<tau> x = opair"
      unfolding mSet_def mPair_def int_typ_eq
      using partD by auto
    thus "False"
      unfolding set_V_def opair_V_def
      by (tactic \<open>Method.insert_tac \<^context> [neq_thm (2,0)] 1\<close>, auto)       
  qed

  show "m\<forall>x::V. (x : mSet \<triangle> mFunc) = (x : \<bottom>)"
  proof (rule, rule disjointI)
    fix x :: V assume 
      "x : mSet" "x : mFunc"
    hence
      "\<tau> x = GZF_Model_class.set" "\<tau> x = func"
      unfolding mSet_def mFunc_def int_typ_eq
      using partD by auto
    thus "False"
      unfolding set_V_def func_V_def
      by (tactic \<open>Method.insert_tac \<^context> [neq_thm (3,0)] 1\<close>, auto)       
  qed
 
  show "m\<forall>x::V. (x : mSet \<triangle> mExc) = (x : \<bottom>)"
  proof (rule, rule disjointI)
    fix x :: V assume 
      "x : mSet" "x : mExc"
    hence
      "\<tau> x = GZF_Model_class.set" "\<tau> x = exc_tag"
      unfolding mSet_def mExc_def int_typ_eq
      using partD by auto
    thus "False"
      unfolding set_V_def exc_tag_V_def
      by (tactic \<open>Method.insert_tac \<^context> [neq_thm (4,0)] 1\<close>, auto)       
  qed 
 
  show "m\<forall>x::V. (x : mOrd \<triangle> mPair) = (x : \<bottom>)"
  proof (rule, rule disjointI)
    fix x :: V assume 
      "x : mOrd" "x : mPair"
    hence
      "\<tau> x = ord" "\<tau> x = opair"
      unfolding mOrd_def mPair_def int_typ_eq
      using partD by auto
    thus "False"
      unfolding ord_V_def opair_V_def
      by (tactic \<open>Method.insert_tac \<^context> [neq_thm (2,1)] 1\<close>, auto)       
  qed

  show "m\<forall>x::V. (x : mOrd \<triangle> mFunc) = (x : \<bottom>)"
  proof (rule, rule disjointI)
    fix x :: V assume 
      "x : mOrd" "x : mFunc"
    hence
      "\<tau> x = ord" "\<tau> x = func"
      unfolding mOrd_def mFunc_def int_typ_eq
      using partD by auto
    thus "False"
      unfolding ord_V_def func_V_def
      by (tactic \<open>Method.insert_tac \<^context> [neq_thm (3,1)] 1\<close>, auto)       
  qed
  
  show "m\<forall>x::V. (x : mOrd \<triangle> mExc) = (x : \<bottom>)"
  proof (rule, rule disjointI)
    fix x :: V assume 
      "x : mOrd" "x : mExc"
    hence
      "\<tau> x = ord" "\<tau> x = exc_tag"
      unfolding mOrd_def mExc_def int_typ_eq
      using partD by auto
    thus "False"
      unfolding ord_V_def exc_tag_V_def
      by (tactic \<open>Method.insert_tac \<^context> [neq_thm (4,1)] 1\<close>, auto)       
  qed
  
  show "m\<forall>x::V. (x : mPair \<triangle> mFunc) = (x : \<bottom>)"
  proof (rule, rule disjointI)
    fix x :: V assume 
      "x : mPair" "x : mFunc"
    hence
      "\<tau> x = opair" "\<tau> x = func"
      unfolding mPair_def mFunc_def int_typ_eq
      using partD by auto
    thus "False"
      unfolding opair_V_def func_V_def
      by (tactic \<open>Method.insert_tac \<^context> [neq_thm (3,2)] 1\<close>, auto)       
  qed
  
  show "m\<forall>x::V. (x : mPair \<triangle> mExc) = (x : \<bottom>)"
  proof (rule, rule disjointI)
    fix x :: V assume 
      "x : mPair" "x : mExc"
    hence
      "\<tau> x = opair" "\<tau> x = exc_tag"
      unfolding mPair_def mExc_def int_typ_eq
      using partD by auto
    thus "False"
      unfolding opair_V_def exc_tag_V_def
      by (tactic \<open>Method.insert_tac \<^context> [neq_thm (4,2)] 1\<close>, auto)       
  qed
  
  show "m\<forall>x::V. (x : mFunc \<triangle> mExc) = (x : \<bottom>)"
  proof (rule, rule disjointI)
    fix x :: V assume 
      "x : mFunc" "x : mExc"
    hence
      "\<tau> x = func" "\<tau> x = exc_tag"
      unfolding mFunc_def mExc_def int_typ_eq
      using partD by auto
    thus "False"
      unfolding func_V_def exc_tag_V_def
      by (tactic \<open>Method.insert_tac \<^context> [neq_thm (4,3)] 1\<close>, auto)       
  qed

  show "m\<forall>x::V. x : mSet \<mho> (mOrd \<mho> (mPair \<mho> mFunc)) \<longrightarrow> x : mSetMem"
  proof (rule, rule)
    fix x :: V assume "x : M"
      and "x : mSet \<mho> (mOrd \<mho> (mPair \<mho> mFunc))"
    hence "x :\<^enum> GZF_Model_class.set \<or> x :\<^enum> ord \<or> x :\<^enum> opair \<or> x :\<^enum> func"
      unfolding uni_typ_eq int_typ_eq
        mSet_def mPair_def mOrd_def mFunc_def
      by auto
    hence "\<tau> x \<noteq> \<tau> mexc'"
      unfolding set_V_def ord_V_def opair_V_def func_V_def
      using fst_mexc partD(2) four_neq by metis
    hence "x \<noteq> mexc'" by auto
    hence "\<not> Excluded GZF_Model_class.set x"
      unfolding Excluded_V_def set_V_def by auto
    thus "x : mSetMem"
      using not_excluded_msmem[OF \<open>x : M\<close>] by auto
  qed

  show "m\<forall>x::V. x : mSet \<mho> (mOrd \<mho> (mPair \<mho> mFunc)) \<longrightarrow> x : mPairMem"
  proof (rule, rule)
    fix x :: V assume "x : M"
      and "x : mSet \<mho> (mOrd \<mho> (mPair \<mho> mFunc))"
    hence "x :\<^enum> GZF_Model_class.set \<or> x :\<^enum> ord \<or> x :\<^enum> opair \<or> x :\<^enum> func"
      unfolding uni_typ_eq int_typ_eq
        mSet_def mPair_def mOrd_def mFunc_def
      by auto
    hence "\<tau> x \<noteq> \<tau> mexc'"
      unfolding set_V_def ord_V_def opair_V_def func_V_def
      using fst_mexc partD(2) four_neq by metis
    hence "x \<noteq> mexc'" by auto
    hence "\<not> Excluded opair x"
      unfolding Excluded_V_def opair_V_def by auto
    thus "x : mPairMem"
      using mE[OF \<open>x  : M\<close>] mpmemI[OF _ exsetI[OF tier_set]] by metis  
  qed

  show "m\<forall>x::V. x : mSet \<mho> (mOrd \<mho> (mPair \<mho> mFunc)) \<longrightarrow> x : mFunMem"
  proof (rule, rule)
    fix x :: V assume "x : M"
      and "x : mSet \<mho> (mOrd \<mho> (mPair \<mho> mFunc))"
    hence "x :\<^enum> GZF_Model_class.set \<or> x :\<^enum> ord \<or> x :\<^enum> opair \<or> x :\<^enum> func"
      unfolding uni_typ_eq int_typ_eq
        mSet_def mPair_def mOrd_def mFunc_def
      by auto
    hence "\<tau> x \<noteq> \<tau> mexc'"
      unfolding set_V_def ord_V_def opair_V_def func_V_def
      using fst_mexc partD(2) four_neq by metis
    hence "x \<noteq> mexc'" by auto
    hence "\<not> Excluded func x"
      unfolding Excluded_V_def func_V_def by auto
    thus "x : mFunMem"
      using ex_mfmem[OF \<open>x : M\<close>] setmem_any
      unfolding FunMem_V_def by auto
  qed

  show "m\<forall>x::V. x : mSet \<mho> (mOrd \<mho> (mPair \<mho> (mFunc \<mho> mExc))) \<longrightarrow> x : \<top>"
    by auto

  show "m\<forall>x::V. (x : mExc \<triangle> mSetMem) = (x : \<bottom>)"
  proof (rule, rule disjointI)
    fix x :: V assume 
      "x : M" "x : mExc" "x : mSetMem"  
    hence "x = mexc'" "\<not> Excluded GZF_Model_class.set x"
      using mexc_ax[where 'a = V] msmem_not_excluded 
      unfolding mexc_def mexc'_def exc_tag_V_def has_ty_def mall_def tall_def
      by auto
    thus "False"
      unfolding set_V_def Excluded_V_0 by auto
  qed

  show "m\<forall>x::V. (x : mExc \<triangle> mPairMem) = (x : \<bottom>)"
  proof (rule, rule disjointI)
    fix x :: V assume 
      "x : M" "x : mExc" "x : mPairMem"  
    hence "x = mexc'" "\<not> Excluded opair x"
      using mexc_ax[where 'a = V] mpmem_ex
      unfolding mexc_def mexc'_def exc_tag_V_def has_ty_def mall_def tall_def
      by auto
    thus "False"
      unfolding opair_V_def Excluded_V_2 by auto
  qed

  show "m\<forall>x::V. (x : mExc \<triangle> mFunMem) = (x : \<bottom>)"
  proof (rule, rule disjointI)
    fix x :: V assume 
      "x : M" "x : mExc" "x : mFunMem"  
    hence "x = mexc'" "\<not> Excluded func x"
      using mexc_ax[where 'a = V] mfmem_ex
      unfolding mexc_def mexc'_def exc_tag_V_def has_ty_def mall_def tall_def
      by auto
    thus "False"
      unfolding func_V_def Excluded_V_3 by auto
  qed

  show "m\<forall>x::V. (x : \<bottom> \<triangle> \<top>) = (x : \<bottom>)"
    by (rule, rule disjointI, auto dest: empty_typD)
qed

end 
end