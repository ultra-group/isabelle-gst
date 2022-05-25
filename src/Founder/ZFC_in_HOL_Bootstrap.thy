section \<open>Bootstrap in V - Interpreting GZF, Ord, OrdRec in Paulson's ZFC in HOL\<close>

theory ZFC_in_HOL_Bootstrap
  imports 
    "ZFC_in_HOL.ZFC_Typeclasses" 
    "../GST_Features" "../GZF/KPair" 
  begin

text \<open>We show that V instantiates the GZF, Ordinal, and OrdRec, and Function typeclasses\<close>

text \<open>Bootstrapping GZF typeclass\<close>
instantiation V :: GZF 
begin
definition Set_V :: \<open>V \<Rightarrow> bool\<close>
  where "Set_V x \<equiv> True"
definition Mem_V :: \<open>V \<Rightarrow> V \<Rightarrow> bool\<close>
  where "Mem_V b x \<equiv> Set.member b (elts x)"
definition Union_V :: \<open>V \<Rightarrow> V\<close>
  where "Union_V x \<equiv> ZFC_in_HOL.set (Complete_Lattices.Union (Set.image elts (elts x)))"
definition Pow_V :: \<open>V \<Rightarrow> V\<close>
  where "Pow_V \<equiv> VPow"
definition Emp_V :: \<open>V\<close>
  where "Emp_V \<equiv> zero_class.zero"
definition Succ_V :: \<open>V \<Rightarrow> V\<close>
  where "Succ_V \<equiv> ZFC_in_HOL.succ"
definition Inf_V :: \<open>V\<close>
  where "Inf_V \<equiv> ZFC_in_HOL.\<omega>"
definition Repl_V :: \<open>[V, [V,V] \<Rightarrow> bool] \<Rightarrow> V\<close>
  where "Repl_V x P \<equiv> ZFC_in_HOL.set 
    (Set.image (\<lambda>a. (THE b. P a b)) (Set.Collect (\<lambda>a. Set.member a (elts x) \<and> (\<exists>b. P a b))))"
definition Subset_V :: \<open>[V,V] \<Rightarrow> bool\<close>
  where "Subset_V x y \<equiv> less_eq x y"
definition SetMem_V :: \<open>V \<Rightarrow> bool\<close>
  where "SetMem_V b \<equiv> True"
definition ReplPred_V :: \<open>V \<Rightarrow> ([V,V] \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where "ReplPred_V x P \<equiv> \<forall>b. Set.member b (elts x) \<longrightarrow> (\<exists>\<^sub>\<le>\<^sub>1 c. P b c)"
definition SetOf_V :: \<open>(V \<Rightarrow> bool) \<Rightarrow> V \<Rightarrow> bool\<close>
  where "SetOf_V P x \<equiv> \<forall>b. Set.member b (elts x) \<longrightarrow> has_ty b P"
definition GZF_default_V :: \<open>V\<close>
  where "GZF_default_V \<equiv> zero_class.zero"

instance proof (intro_classes, 
  unfold Set_V_def Mem_V_def Union_V_def Pow_V_def Emp_V_def Succ_V_def
         Inf_V_def Subset_V_def SetMem_V_def SetOf_V_def,
  unfold has_ty_def depfun_ty_def tall_def tex_def fun_ty_def tuniq_def, auto)

 fix P :: "V \<Rightarrow> V \<Rightarrow> bool" and x b 
 assume "ReplPred x P" "Set.member b (elts (\<R> x P))"  
 moreover then obtain a where "Set.member a (elts x)" "\<exists>b. P a b" "The (P a) = b"
   unfolding ReplPred_V_def Repl_V_def Uniq_def by auto
 moreover then obtain b' where "P a b'" by auto
 ultimately have "b = b'"   
    using the1_equality'[where P = \<open>P a\<close> and a = \<open>b'\<close>]
    unfolding ReplPred_V_def by auto
 thus "\<exists>a. Set.member a (elts x) \<and> P a b" 
    using \<open>Set.member a (elts x)\<close> \<open>P a b'\<close> by auto
next
 fix P :: "V \<Rightarrow> V \<Rightarrow> bool" and x a b 
 assume "ReplPred x P" "Set.member a (elts x)" "P a b"
 moreover hence "The (P a) = b" unfolding ReplPred_V_def Uniq_def by auto 
 ultimately show "Set.member b (elts (\<R> x P))" 
  unfolding Repl_V_def by auto
next
 fix P :: "V \<Rightarrow> V \<Rightarrow> bool" and x a b 
 assume "ReplPred x P" "Set.member a (elts x)"
 thus "\<exists>\<^sub>\<le>\<^sub>1 b. P a b" unfolding ReplPred_V_def by auto 
next
 fix P :: "V \<Rightarrow> V \<Rightarrow> bool" and x 
 assume "\<forall>a. Set.member a (elts x) \<longrightarrow> (\<exists>\<^sub>\<le>\<^sub>1 x. P a x)"
 thus "ReplPred x P" unfolding ReplPred_V_def by auto
qed
end

text \<open>Bootstrapping Ordinal typeclass\<close>
instantiation V :: Ordinal 
begin

definition Ord_V :: \<open>V \<Rightarrow> bool\<close>
  where "Ord_V \<equiv> ZFC_in_HOL.Ord"
definition lt_V :: \<open>[V,V] \<Rightarrow> bool\<close>
  where "lt_V i j \<equiv> less i j"
definition zero_V :: \<open>V\<close>
  where "zero_V \<equiv> zero_class.zero"
definition succ_V :: \<open>V \<Rightarrow> V\<close>
  where "succ_V i \<equiv> ZFC_in_HOL.succ i" 
definition omega_V :: \<open>V\<close>
  where "omega_V \<equiv> ZFC_in_HOL.\<omega>"
definition Limit_V :: \<open>V \<Rightarrow> bool\<close>
  where "Limit_V \<equiv> ZFC_in_HOL.Limit"
definition Ordinal_default_V :: \<open>V\<close>
  where "Ordinal_default_V \<equiv> zero_class.zero"

instance proof (intro_classes,
 unfold Ord_V_def lt_V_def zero_V_def succ_V_def
         omega_V_def Limit_V_def, 
 unfold has_ty_def fun_ty_def tall_def inter_ty_def)
 
  show 
    "ZFC_in_HOL.Ord zero_class.zero"
    "\<forall>x. ZFC_in_HOL.Ord x \<longrightarrow> ZFC_in_HOL.Ord (ZFC_in_HOL.succ x)"
    "ZFC_in_HOL.Limit ZFC_in_HOL.\<omega>"  
    "\<forall>x. ZFC_in_HOL.Ord x \<longrightarrow> \<not> less x zero_class.zero"
    by auto

  show "\<forall>x. ZFC_in_HOL.Ord x \<longrightarrow> (\<forall>xa. ZFC_in_HOL.Ord xa \<longrightarrow>
       (less x (ZFC_in_HOL.succ xa)) = (less x xa \<or> x = xa))"
       using elts_succ Ord_mem_iff_lt by blast

  show "\<forall>u. ZFC_in_HOL.Limit u \<longrightarrow> u = ZFC_in_HOL.\<omega> \<or> less ZFC_in_HOL.\<omega> u"
  proof (rule, rule, rule ccontr, auto)
    fix u assume u:"ZFC_in_HOL.Limit u" 
    and "u \<noteq> ZFC_in_HOL.\<omega>" "\<not> less ZFC_in_HOL.\<omega> u"
    hence "less u ZFC_in_HOL.\<omega>" 
      using Ord_linear_lt[OF Ord_\<omega> Limit_is_Ord[OF u]] by auto
    hence "\<exists>n. u = ord_of_nat n" 
      using Ord_mem_iff_lt[OF Limit_is_Ord[OF u] Ord_\<omega>] 
            elts_\<omega> by auto
    thus "False"
      using non_Limit_ord_of_nat u by auto
  qed

  show "\<forall>x. ZFC_in_HOL.Ord x \<longrightarrow> (\<forall>xa. ZFC_in_HOL.Ord xa \<longrightarrow>
          (\<forall>xb. ZFC_in_HOL.Ord xb \<longrightarrow>
            less x xa \<longrightarrow> less xa xb \<longrightarrow> less x xb))"
    by auto

  show "\<forall>x. ZFC_in_HOL.Ord x \<longrightarrow> (\<forall>xa. ZFC_in_HOL.Ord xa \<longrightarrow> 
     less x xa \<longrightarrow> \<not> less xa x)"
    by auto

  show "\<forall>x. ZFC_in_HOL.Ord x \<longrightarrow>
         (\<forall>xa. ZFC_in_HOL.Ord xa \<longrightarrow> less x xa \<or> x = xa \<or> less xa x)"
    using Ord_linear_lt by auto

  show "\<forall>P. (\<forall>x. ZFC_in_HOL.Ord x \<longrightarrow>
              (\<forall>xa. ZFC_in_HOL.Ord xa \<longrightarrow> less xa x \<longrightarrow> P xa) \<longrightarrow> P x) \<longrightarrow>
         (\<forall>x. ZFC_in_HOL.Ord x \<longrightarrow> P x)" 
    by (metis Ord_induct Ord_mem_iff_lt)

  show "\<forall>u. ZFC_in_HOL.Limit u =
         (ZFC_in_HOL.Ord u \<and> less zero_class.zero u \<and>
           (\<forall>x. ZFC_in_HOL.Ord x \<longrightarrow> less x u \<longrightarrow> 
              less (ZFC_in_HOL.succ x) u))" 
   unfolding Limit_def
   by (meson ON_imp_Ord Ord_0 Ord_mem_iff_lt Ord_succ elts_subset_ON) 
qed
end

text \<open>Bootstrapping OrdRec\<close>
instantiation V :: OrdRec
begin
definition predSet_V :: \<open>V \<Rightarrow> V\<close>
  where "predSet_V j \<equiv> j"
definition supOrd_V :: \<open>V \<Rightarrow> V\<close>
  where "supOrd_V x \<equiv> (\<Squnion> (elts x))"
definition OrdRec_V :: \<open>[[V, V \<Rightarrow> V] \<Rightarrow> V, [V,V] \<Rightarrow> V, V, V] \<Rightarrow> V\<close>
  where "OrdRec_V G F A \<equiv> transrec3 A (\<lambda>i. F (succ i))
            (\<lambda>u f. G u (\<lambda>j. if ZFC_in_HOL.Ord j \<and> less j u then f j else zero_class.zero))"
definition OrdRec_default_V :: \<open>V\<close>
  where "OrdRec_default_V \<equiv> zero_class.zero"
instance proof (intro_classes,
  unfold Ord_V_def lt_V_def zero_V_def succ_V_def Limit_V_def
    Mem_V_def SetOf_V_def predSet_V_def supOrd_V_def 
    OrdRec_V_def OrdRec_default_V_def,
  unfold tall_def fun_ty_def has_ty_def)

  show "\<forall>x. ZFC_in_HOL.Ord x \<longrightarrow> 
    (\<forall>b. Set.member b (elts x) \<longrightarrow> ZFC_in_HOL.Ord b)"
    by (metis Ord_in_Ord)

  show "\<forall>x. ZFC_in_HOL.Ord x \<longrightarrow> (\<forall>xa. ZFC_in_HOL.Ord xa \<longrightarrow> 
    (Set.member xa (elts x)) = (less xa x))"
    by (metis Ord_mem_iff_lt)
    
  show "\<forall>x. (\<forall>b. Set.member b (elts x) \<longrightarrow> ZFC_in_HOL.Ord b) \<longrightarrow>
         ZFC_in_HOL.Ord (\<Squnion> (elts x))"
    using Ord_Sup by fastforce

  show "\<forall>x. (\<forall>b. Set.member b (elts x) \<longrightarrow> ZFC_in_HOL.Ord b) \<longrightarrow>
         (\<forall>\<alpha>. Set.member \<alpha> (elts x) \<longrightarrow>
               less \<alpha> (ZFC_in_HOL.succ (\<Squnion> (elts x))))"
   using Ord_Sup Ord_succ OrdmemD ZFC_in_HOL.Sup_upper 
         in_succ_iff small_elts by presburger

  show "\<forall>G F A. transrec3 A (\<lambda>i. F (ZFC_in_HOL.succ i))
   (\<lambda>u f. G u (\<lambda>j. if ZFC_in_HOL.Ord j \<and> less j u then f j else zero_class.zero)) 
   zero_class.zero = A"        
   by auto

  show "\<forall>G F A x. ZFC_in_HOL.Ord x \<longrightarrow>
    transrec3 A (\<lambda>i. F (ZFC_in_HOL.succ i))
     (\<lambda>u f. G u (\<lambda>j. if ZFC_in_HOL.Ord j \<and> less j u then f j else zero_class.zero))
     (ZFC_in_HOL.succ x) =
       F (ZFC_in_HOL.succ x)
        (transrec3 A (\<lambda>i. F (ZFC_in_HOL.succ i))
          (\<lambda>u f. G u (\<lambda>j. if ZFC_in_HOL.Ord j \<and> less j u then f j else zero_class.zero)) x)"
  by auto

  show "\<forall>G F A x. ZFC_in_HOL.Limit x \<longrightarrow>
       transrec3 A (\<lambda>i. F (ZFC_in_HOL.succ i))
        (\<lambda>u f. G u (\<lambda>j. if ZFC_in_HOL.Ord j \<and> less j u then f j else zero_class.zero)) x =
       G x (\<lambda>j. if ZFC_in_HOL.Ord j \<and> less j x
        then transrec3 A (\<lambda>i. F (ZFC_in_HOL.succ i))
        (\<lambda>u f. G u (\<lambda>j. if ZFC_in_HOL.Ord j \<and> less j u then f j else zero_class.zero)) j
        else zero_class.zero)" 
  proof (auto)
    fix G F A u 
    assume u:"ZFC_in_HOL.Limit u"
    have eq:"(\<lambda>j. if ZFC_in_HOL.Ord j \<and> less j u
                then restrict (transrec3 A (\<lambda>i. F (ZFC_in_HOL.succ i))
                  (\<lambda>u f. G u (\<lambda>j. if ZFC_in_HOL.Ord j \<and> less j u then f j else zero_class.zero)))
                  (elts u) j
                else zero_class.zero) =
           (\<lambda>j. if ZFC_in_HOL.Ord j \<and> less j u
                then transrec3 A (\<lambda>i. F (ZFC_in_HOL.succ i))
                   (\<lambda>u f. G u (\<lambda>j. if ZFC_in_HOL.Ord j \<and> less j u then f j else zero_class.zero)) j
                else zero_class.zero)"
   by (meson Ord_mem_iff_lt[OF _ Limit_is_Ord[OF u]] restrict_apply')
   show "G u (\<lambda>j. if ZFC_in_HOL.Ord j \<and> less j u
                  then restrict
                  (transrec3 A (\<lambda>i. F (ZFC_in_HOL.succ i))
                    (\<lambda>u f. G u (\<lambda>j.
                if ZFC_in_HOL.Ord j \<and> less j u then f j else zero_class.zero)))
                      (elts u) j
                else zero_class.zero) =
       G u (\<lambda>j. if ZFC_in_HOL.Ord j \<and> less j u
                then transrec3 A (\<lambda>i. F (ZFC_in_HOL.succ i))
                      (\<lambda>u f. G u (\<lambda>j. if ZFC_in_HOL.Ord j \<and> less j u then f j
                                      else zero_class.zero)) j
                else zero_class.zero)" 
   unfolding eq ..
 qed
qed
end

text \<open>Instantiation of OPair and CartProd using Kuratowski Pairs\<close>

ML \<open>val GZF_OPair_ts =
   [\<^term>\<open>is_kpair :: V \<Rightarrow> bool\<close>, \<^term>\<open>kpair :: V \<Rightarrow> V \<Rightarrow> V\<close>,
    \<^term>\<open>SetMem :: V \<Rightarrow> bool\<close>, \<^term>\<open>GZF_default :: V\<close>]\<close>

setup \<open>mk_instantiation \<^type_name>\<open>V\<close> \<^class>\<open>OPair\<close> GZF_OPair_ts @{thm GZF_OPair}\<close>
setup \<open>mk_instantiation \<^type_name>\<open>V\<close> \<^class>\<open>CartProd\<close> [] @{thm GZF_CartProd}\<close>

text \<open>Instantiation of app, BinRel and Function using sets of ordered pairs\<close>

setup \<open>mk_instantiation \<^type_name>\<open>V\<close> \<^class>\<open>app\<close> [\<^term>\<open>setrel_app :: V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool\<close>] @{thm TrueI}\<close>

ML \<open>val GZF_BinRel_ts =
   [\<^term>\<open>SetOf (SetMem * SetMem) :: V \<Rightarrow> bool\<close>,
    \<^term>\<open>mk_setrel :: V \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V \<Rightarrow> bool) \<Rightarrow> V\<close>,
    \<^term>\<open>setrel_field :: V \<Rightarrow> V\<close>,
    \<^term>\<open>(\<lambda>x. \<P> (x \<times> x)) :: V \<Rightarrow> V\<close>,
    \<^term>\<open>SetMem :: V \<Rightarrow> bool\<close>,
    \<^term>\<open>GZF_default :: V\<close>]\<close>

setup \<open>mk_instantiation \<^type_name>\<open>V\<close> \<^class>\<open>BinRel\<close> GZF_BinRel_ts @{thm GZF_BinRel}\<close>

ML \<open>val GZF_Function_ts =
  [\<^term>\<open>FuncRel :: V \<Rightarrow> bool\<close>,
   \<^term>\<open>mk_funrel :: V \<Rightarrow> (V \<Rightarrow> V \<Rightarrow> bool) \<Rightarrow> V\<close>,
   \<^term>\<open>domain :: V \<Rightarrow> V\<close>,
   \<^term>\<open>range :: V \<Rightarrow> V\<close>,
   \<^term>\<open>mk_funspace :: V \<Rightarrow> V \<Rightarrow> V\<close>,
   \<^term>\<open>SetMem :: V \<Rightarrow> bool\<close>,
   \<^term>\<open>FuncRelPred :: V \<Rightarrow> (V \<Rightarrow> V \<Rightarrow> bool) \<Rightarrow> bool\<close>,
   \<^term>\<open>BinRelation_default :: V\<close>]\<close>

setup \<open>mk_instantiation \<^type_name>\<open>V\<close> \<^class>\<open>Function\<close> GZF_Function_ts @{thm BinRel_Function}\<close>

text \<open>Removing ZFC_in_HOL names from namespace,
      and making names print nicely in output panel.\<close>
(*Hide HOL constant \<open>set\<close> so we can use it as a tag in model building*)
(* and \<open>dom\<close> so we can use it in Function/Relation locales*)
hide_const 
 Union Pow Inf Nat Pair dom

hide_const 
 ZFC_in_HOL.Ord
 ZFC_in_HOL.Limit
 ZFC_in_HOL.succ wo_rel.succ
end