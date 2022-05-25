theory OrdRec_Model
  imports mpredSet msupOrd mOrdRec 
begin

context OrdRec_Model 
begin

ML \<open>val mOrdRec = 
  mk_msig [mGZF, mOrdinal] "mOrdRec" @{class OrdRec}
    ["mpredSet", "msupOrd", "mOrdRec","OrdRec_Model_mdefault"] @{context}\<close>

translate_axioms mOrdRec_axioms : mOrdRec
proof -   
  show "m\<forall>x. x : mOrd \<longrightarrow> mpredSet x : mSetOf mOrd" 
    using mpredset_msetof by auto

  show "m\<forall>x. x : mSetOf mOrd \<longrightarrow> msupOrd x : mOrd" 
    using msupord_mord by auto

  show "m\<forall>\<beta> : mOrd. m\<forall>\<alpha> : mOrd. (\<alpha> m mpredSet \<beta>) = (\<alpha> \<lless> \<beta>)" 
    using mpredset_ax unfolding mall_def mtall_def tall_def by auto

  show "m\<forall>x : mSetOf mOrd. m\<forall>\<alpha>. \<alpha> m x \<longrightarrow> \<alpha> \<lless> msucc (msupOrd x)" 
    using msupordI unfolding mtall_def by auto

  show "\<forall>G : LimFun. \<forall>F : M \<rightarrow> M \<rightarrow> M. m\<forall>A. 
          mOrdRec G F A m0 = A" 
     using mordrec_mzero by auto

  show "\<forall>G : LimFun. \<forall>F : M \<rightarrow> M \<rightarrow> M. m\<forall>A. m\<forall>b : mOrd. 
          mOrdRec G F A (msucc b) = F (msucc b) (mOrdRec G F A b)" 
     using mordrec_msucc unfolding mtall_def mall_def
     by auto

  show "\<forall>G : LimFun. \<forall>F : M \<rightarrow> M \<rightarrow> M. m\<forall>A. m\<forall>\<mu> : mLimit. 
          mOrdRec G F A \<mu> = G \<mu> (\<lambda>j. if j : mOrd \<and> j \<lless> \<mu> 
                                     then mOrdRec G F A j 
                                     else OrdRec_Model_mdefault)" 
     using mordrec_mlim mlt_mord1 unfolding mtall_def mall_def
     by auto
qed

resp_thms mOrdRec_resp : mOrdRec 
proof -
  show "\<And>x. x : M \<Longrightarrow> mpredSet x : M" 
    using mpredset_rsp .
  show "\<And>x. x : M \<Longrightarrow> msupOrd x : M" 
    using msupord_rsp .
  show "\<And>fun1 fun2. (\<And>x. x : M \<Longrightarrow> 
          (\<And>fun1a fun2a. (\<And>x. x : M \<Longrightarrow> fun1a x : M \<and> fun1a x = fun2a x) \<Longrightarrow> 
            fun1 x fun1a : M \<and> fun1 x fun1a = fun2 x fun2a)) \<Longrightarrow>
       (\<And>fun1a fun2a.
           (\<And>x. x : M \<Longrightarrow> (\<And>xa. xa : M \<Longrightarrow> fun1a x xa : M \<and> fun1a x xa = fun2a x xa)) \<Longrightarrow>
           (\<And>x. x : M \<Longrightarrow> (\<And>xa. xa : M \<Longrightarrow> 
        mOrdRec fun1 fun1a x xa : M \<and> mOrdRec fun1 fun1a x xa = mOrdRec fun2 fun2a x xa)))"
  proof (auto)
    fix G G' F F' A j
    show "mOrdRec G F A j : M"
      using mordrec_m .
    assume 
      G_cong:"\<And>u. u : M \<Longrightarrow> (\<And>f f'. (\<And>j. j : M \<Longrightarrow> f j : M \<and> f j = f' j) \<Longrightarrow> G u f : M \<and> G u f = G' u f')" and 
      F_cong:"\<And>j. j : M \<Longrightarrow> (\<And>b. b : M \<Longrightarrow> F j b : M \<and> F j b = F' j b)" and
      A:"A : M" and j:"j : M"
    show "mOrdRec G F A j = mOrdRec G' F' A j"
    proof (cases "G : LimFun \<and> F : M \<rightarrow> M \<rightarrow> M \<and> A : M \<and> j : mOrd")
      case True
      hence 
        G : "G : LimFun" and 
        F : "F : M \<rightarrow> M \<rightarrow> M" and 
        A : "A : M" and j : "j : mOrd" by auto
      have 
        G' : "G' : LimFun" and 
        F' : "F' : M \<rightarrow> M \<rightarrow> M"
      proof (unfold LimFun_def, rule intI, rule funI, rule funI,
             rule_tac [2] tyI)
        fix u f 
        assume u:"u : M" and f:"f : M \<rightarrow> M"
        hence "G u f = G' u f"
          using G_cong funE[OF f] by auto
        thus "G' u f : M"
          using funE[OF funE[OF limfunD1[OF G] u] f] by auto
       next
        show "\<forall>u : M. \<forall>f : M \<rightarrow> M. G' u f = G' u (\<lambda>j. f (forceM j))"
        proof (rule, rule)
          fix u f assume 
            u : "u : M" and f : "f : M \<rightarrow> M"
          hence "G u f = G u (\<lambda>j. f (forceM j))"
            using limfunD2[OF G] by auto
          thus "G' u f = G' u (\<lambda>j. f (forceM j))"
            using G_cong[OF u, of f f] 
                  G_cong[OF u, of \<open>\<lambda>j. f (forceM j)\<close> \<open>\<lambda>j. f (forceM j)\<close>]
                  funE[OF f] forceM_eq
            by metis
       qed
       show "F' : M \<rightarrow> M \<rightarrow> M"
          using F F_cong
          unfolding fun_ty_def has_ty_def by auto
      qed
      obtain j' where 
        j':"j' : Ord" and j_eq:"j = <ord,j'>" 
        using mordE[OF j] .
      show ?thesis
        unfolding mordrec_eq[OF G F A mordI[OF j']] mordrec_eq[OF G' F' A mordI[OF j']] j_eq
      proof (induct rule: trans_induct3[OF j'])
        show "mOrdRec' G F A <ord,0> = mOrdRec' G' F' A <ord,0>"
          using mordrec'_zero[OF A]
          unfolding j_eq mzero_def by auto        
      next
        case ih:(2 j)
        then show ?case 
        using
            mordrec'_msucc[OF F mordI[OF ih(1)]]
            mordrec'_msucc[OF F' mordI[OF ih(1)]] 
        unfolding msucc_eq[OF ih(1)]
        by (simp add: A F' F_cong G' local.mordI local.ord_m local.succ_ord mordrec'_m)
      next
        case ih:(3 \<mu>)
        show ?case unfolding 
          mordrec'_lim[OF G mlimitI[OF ih(1)]]
          mordrec'_lim[OF G' mlimitI[OF ih(1)]]
        proof (rule conjunct2[OF G_cong], auto)
          show "<ord, \<mu>> : M"
            using mord_m[OF mordI[OF limit_ord[OF ih(1)]]] .
          fix j assume "j : M" and jlt:"j \<lless> <ord, \<mu>>"
          thus "mOrdRec' G F A j : M"
            using mordrec'_m[OF mlt_mord1] by auto
          show "mOrdRec' G F A j = mOrdRec' G' F' A j"
            by (rule mordE[OF mlt_mord1[OF jlt]], use ih(2) mltD jlt in auto)
        next
          show "OrdRec_Model_mdefault : M"
            using OrdRec_Model_mdefault_m .
        qed
      qed
   next
    assume "\<not> (G : LimFun \<and> F : M \<rightarrow> M \<rightarrow> M \<and> A : M \<and> j : mOrd)"
    moreover hence "\<not> (G' : LimFun \<and> F' : M \<rightarrow> M \<rightarrow> M \<and> A : M \<and> j : mOrd)"
    proof (auto)
      assume "F' : M \<rightarrow> M \<rightarrow> M" "\<not> F : M \<rightarrow> M \<rightarrow> M" 
      thus "False" 
        using F_cong
        unfolding fun_ty_def has_ty_def
        by auto
    next
      assume G':"G' : LimFun" and G:"\<not> G : LimFun"
      hence "\<not> G : (M \<rightarrow> (M \<rightarrow> M) \<rightarrow> M) \<or> \<not> (\<forall>u: M. \<forall>f: M \<rightarrow> M. G u f = G u (\<lambda>j. f (forceM j)))"
        unfolding LimFun_def inter_ty_def has_ty_def by auto
      thus "False" 
      proof
        assume "\<not> G : (M \<rightarrow> (M \<rightarrow> M) \<rightarrow> M)" 
        thus "False"
          using G' G_cong 
          unfolding LimFun_def inter_ty_def has_ty_def fun_ty_def by auto
      next
        assume "\<not> (\<forall>u : M. \<forall>f : M \<rightarrow> M. G u f = G u (\<lambda>j. f (forceM j)))"
        then obtain u f where 
          u:"u : M" and f:"f : M \<rightarrow> M" and 
          G_neq:"G u f \<noteq> G u (\<lambda>j. f (forceM j))"
          unfolding tall_def by auto
        thus "False"
          using G_cong[OF u, of f f] G_cong[OF u, of \<open>\<lambda>j. f (forceM j)\<close> \<open>\<lambda>j. f (forceM j)\<close>] 
                limfunD2[OF G' u f] forceM_eq funE[OF f] by auto 
      qed
   qed
   ultimately show"mOrdRec G F A j = mOrdRec G' F' A j"
    unfolding mOrdRec_def
    by auto
 qed
qed
 show "OrdRec_Model_mdefault : M"
  using OrdRec_Model_mdefault_m .
qed
end

(* typedecl d  

instance d :: OrdRec_Model  sorry

typedef (overloaded) d1 = \<open>Set.Collect (\<lambda>x :: d. x : M)\<close> 
  using mdefault_m by auto

setup_lifting type_definition_d1 

interpretation ConnectionBase Abs_d1 Rep_d1 pcr_d1 mdefault
  by (unfold ConnectionBase_def, rule,
      rule type_definition_d1, unfold pcr_d1_def cr_d1_def, auto, rule mdefault_m)
 *)
(* Can either perform lifting/instances seperately, or all together *)
(* instantiation d1 :: GZF  sorry*)
(* instantiation d1 :: Ordinal  sorry*)
(* 
instantiation d1 :: OrdRec 
begin
  local_setup \<open>lift_mconsts @{thms mGZF_resp} (@{typ d1}) mGZF\<close>
  local_setup \<open>lift_mconsts @{thms mOrdinal_resp} (@{typ d1}) mOrdinal\<close>
  local_setup \<open>lift_mconsts @{thms mOrdRec_resp} (@{typ d1}) mOrdRec\<close> 
  instance 
    by (intro_classes, unfold funty_eq depfunty_eq, transfer_all,
        tactic \<open>REPEAT_DETERM (resolve_tac @{context} @{thms mGZF_axioms mOrdinal_axioms mOrdRec_axioms} 1)\<close>)  
end
 *)
end