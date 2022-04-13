theory OrdRec_Model_Base
  imports "../../ModelKit/ModelComponents"
          "../../GZF/Model/GZF_Model"
          "Ordinal_Model"
begin

context ModelBase 
begin

(*No different from an empty class that imports 
  GZF_Model and Ordinal_Model?*)
ML \<open>val ordrec_model = mcomp 
 { name = "OrdRec_Model", 
   deps = ["GZF_Model", "Ordinal_Model"], 
   variant = NONE }\<close>
end
local_setup \<open>snd o (mk_mcomp_class ordrec_model)\<close>

context OrdRec_Model 
begin

definition mpredSet' :: \<open>'a \<Rightarrow> 'a\<close> 
  where "mpredSet' j \<equiv> <set, ord \<oplus> predSet (snd j)>"

definition mpredSet :: \<open>'a \<Rightarrow> 'a\<close> 
  where "mpredSet j \<equiv> if j : mOrd then mpredSet' j 
                                  else OrdRec_Model_mdefault"

definition msupOrd' :: \<open>'a \<Rightarrow> 'a\<close>
  where "msupOrd' x \<equiv> <ord, supOrd {snd b | b \<in> snd x}>"

definition msupOrd :: \<open>'a \<Rightarrow> 'a\<close> 
  where "msupOrd x \<equiv> if x : mSetOf mOrd then msupOrd' x 
                                        else OrdRec_Model_mdefault"
lemma msupord_eq : 
  assumes "x : mSetOf mOrd"
  shows "msupOrd x = <ord, supOrd {snd b | b \<in> snd x}>"
  unfolding msupOrd_def msupOrd'_def
  using assms
  by auto

definition forceM :: \<open>'a \<Rightarrow> 'a\<close>
  where "forceM b \<equiv> if b : M then b else OrdRec_Model_mdefault"

lemma forceM_m : "forceM b : M"
  unfolding forceM_def using OrdRec_Model_mdefault_m 
  by auto

lemma forceM_eq : 
  assumes "b : M"
  shows "forceM b = b"
  using assms unfolding forceM_def
  by auto

definition forceM_fun 
  where "forceM_fun f \<equiv> f " 
  
definition mordrecG where 
  "mordrecG G u' (f' :: 'a \<Rightarrow> 'a) \<equiv> forceM (G (<ord, u'>) 
    (\<lambda>j. if j \<lless> <ord,u'> then f' (snd j) else OrdRec_Model_mdefault))"

definition mordrecF where
  "mordrecF F j' b \<equiv> forceM (F (<ord, j'>) b)"

definition mOrdRec' 
  where "mOrdRec' G F A b \<equiv> 
    OrdRec (mordrecG G) (mordrecF F) (forceM A) (snd b)"

lemma mordrec'_zero :
  assumes A : "A : M"
  shows "mOrdRec' G F A m0 = A"
  using ordrec_0 
  unfolding 
    mOrdRec'_def mzero_def 
    ord_snd_eq'[OF zero_ord] forceM_eq[OF A]
  by auto

lemma msucc_snd_eq :
  assumes j : "j : mOrd"
  shows "snd (msucc j) = succ (snd j)"
  by (rule mordE[OF j], use msucc_eq ord_snd_eq' succ_ord in auto)  

lemma msucc_eq' : 
  assumes j : "j : mOrd"
  shows "<ord, succ (snd j)> = msucc j"
  unfolding msucc_def msucc'_def using assms by auto


lemma mordrecG_m :
  shows "mordrecG G u' f' : M"
  unfolding mordrecG_def
  using forceM_m .

lemma mordrecF_m :
  shows "mordrecF F j' b : M"
  unfolding mordrecF_def
  using forceM_m .

lemma mordrec'_m :
  assumes G : "G : mLimit \<rightarrow> (M \<rightarrow> M) \<rightarrow> M"
      and F : "F : mOrd \<rightarrow> M \<rightarrow> M"
      and A : "A : M" and j : "j : mOrd"
    shows "mOrdRec' G F A j : M"
proof (rule ord_cases[OF mord_snd_ord[OF j]])
  assume "snd j = 0"
  thus "mOrdRec' G F A j : M"
    unfolding mOrdRec'_def
    using ordrec_0 forceM_m by auto
next
  fix i assume "i : Ord" "snd j = succ i"
  thus "mOrdRec' G F A j : M"
    unfolding mOrdRec'_def
    using ordrec_succ[OF \<open>i : Ord\<close>]
          mordrecF_m by auto
next
  assume "snd j : Limit"
  thus "mOrdRec' G F A j : M"
    unfolding mOrdRec'_def
    using ordrec_lim
          mordrecG_m by auto
qed

lemma mordrec'_msucc :
  assumes G : "G : mLimit \<rightarrow> (M \<rightarrow> M) \<rightarrow> M"
      and F : "F : mOrd \<rightarrow> M \<rightarrow> M"
      and A : "A : M" and j : "j : mOrd"
  shows "mOrdRec' G F A (msucc j) = F (msucc j) (mOrdRec' G F A j)"
proof -
  have "mOrdRec' G F A (msucc j) = 
    OrdRec (mordrecG G) (mordrecF F) (forceM A) (succ (snd j))"
    unfolding mOrdRec'_def msucc_snd_eq[OF j] ..
  
  hence "mOrdRec' G F A (msucc j) =
    mordrecF F (succ (snd j)) (mOrdRec' G F A j)"
    unfolding 
      ordrec_succ[OF mord_snd_ord[OF j]]
      mOrdRec'_def .

  thus "mOrdRec' G F A (msucc j) =
    F (msucc j) (mOrdRec' G F A j)"
    unfolding 
      mordrecF_def msucc_eq'[OF j]
      forceM_eq[OF funE[OF funE[OF F msucc_mord[OF j]] mordrec'_m[OF assms]]] .
qed

lemma mlimit_snd_limit : 
  "u : mLimit \<Longrightarrow> snd u : Limit"
  by (erule mlimitE, use ord_snd_eq[OF limit_ord] in auto) 

lemma mord_snd_eq' : 
  "u : mOrd \<Longrightarrow> <ord, \<pi> u> = u"
  by (erule mordE, use ord_snd_eq in auto) 

lemma mordrec'_lim :
  assumes G : "G : mLimit \<rightarrow> (M \<rightarrow> M) \<rightarrow> M"
      and F : "F : mOrd \<rightarrow> M \<rightarrow> M"
      and A : "A : M" and u : "u : mLimit"
  shows "mOrdRec' G F A u = 
   G u (\<lambda>j. if j \<lless> u then mOrdRec' G F A j else OrdRec_Model_mdefault)"
proof -
  have if_eq: 
    "(\<lambda>j. if j \<lless> \<langle>ord,\<pi> u\<rangle> then 
            if \<pi> j : Ord \<and> \<pi> j < \<pi> u then 
              mOrdRec' G F A \<langle>ord,\<pi> j\<rangle> 
            else 
              OrdRec_default 
          else OrdRec_Model_mdefault) =
     (\<lambda>j. if j \<lless> u then mOrdRec' G F A j else OrdRec_Model_mdefault)"
   proof (rule, rule if_cong, unfold mord_snd_eq'[OF mlimit_mord[OF u]], 
          rule_tac [1] refl, rule_tac [2] refl)
    fix j assume "j \<lless> u"
    hence "\<pi> j : Ord" "\<pi> j < \<pi> u"
      unfolding mlt_def using mord_snd_ord by auto
    thus "(if \<pi> j : Ord \<and> \<pi> j < \<pi> u then mOrdRec' G F A \<langle>ord,\<pi> j\<rangle> 
             else OrdRec_default) = mOrdRec' G F A j"
       unfolding mord_snd_eq'[OF mlt_mord1[OF \<open>j \<lless> u\<close>]] by simp
  qed

  have if_M : 
    "(\<lambda>j. if j \<lless> u then mOrdRec' G F A j 
                    else OrdRec_Model_mdefault) : M \<rightarrow> M"
  by (rule funI, use mordrec'_m[OF G F A mlt_mord1] OrdRec_Model_mdefault_m in auto)

  have "mOrdRec' G F A u = 
    OrdRec (mordrecG G) (mordrecF F) (forceM A) (snd u)"
    unfolding mOrdRec'_def ..
  
  have "mOrdRec' G F A u =
    mordrecG G (snd u) (\<lambda>j. if j : Ord \<and> j < \<pi> u then mOrdRec' G F A <ord,j> else OrdRec_default)"
    unfolding 
      ordrec_lim[OF mlimit_snd_limit[OF u]]
      mOrdRec'_def
    using ord_snd_eq'
    (*Thanks, sledgehammer*)
    by (metis (no_types, opaque_lifting))
   
  thus ?thesis 
    unfolding mordrecG_def if_eq 
    unfolding mord_snd_eq'[OF mlimit_mord[OF u]]
      forceM_eq[OF funE[OF funE[OF G u] if_M]] .
qed

definition mOrdRec 
  where "mOrdRec G F A j \<equiv> (if G : mLimit \<rightarrow> (M \<rightarrow> M) \<rightarrow> M \<and>
                               F : mOrd \<rightarrow> M \<rightarrow> M \<and> A : M \<and> j : mOrd 
                            then mOrdRec' G F A j 
                            else OrdRec_Model_mdefault)"

lemma mordrec_eq :
  assumes G : "G : mLimit \<rightarrow> (M \<rightarrow> M) \<rightarrow> M" 
      and F : "F : mOrd \<rightarrow> M \<rightarrow> M" and A : "A : M" 
      and j : "j : mOrd"
    shows "mOrdRec G F A j = mOrdRec' G F A j"
    unfolding mOrdRec_def using assms by auto

lemma mordrec_m :
  "mOrdRec G F A j : M"
  unfolding mOrdRec_def
  using mordrec'_m OrdRec_Model_mdefault_m
  by auto

ML \<open>val mOrdRec = 
  mk_msig [mGZF, mOrdinal] "mOrdRec" @{class OrdRec}
    ["mpredSet", "msupOrd", "mOrdRec","OrdRec_Model_mdefault"] @{context}\<close>
ML \<open>get_locale_param_names \<^theory> \<^class>\<open>OrdRec\<close>\<close>

translate_axioms mOrdRec_axioms : mOrdRec sorry
resp_thms mOrdRec 
proof -
  show "\<And>x. x : M \<Longrightarrow> mpredSet x : M" sorry
  show "\<And>x. x : M \<Longrightarrow> msupOrd x : M" sorry
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
    proof (cases "G : mLimit \<rightarrow> (M \<rightarrow> M) \<rightarrow> M \<and> F : mOrd \<rightarrow> M \<rightarrow> M \<and> A : M \<and> j : mOrd")
      case True
      hence 
        G : "G : mLimit \<rightarrow> (M \<rightarrow> M) \<rightarrow> M" and 
        F : "F : mOrd \<rightarrow> M \<rightarrow> M" and 
        A : "A : M" and j : "j : mOrd" by auto
      have 
        G' : "G' : mLimit \<rightarrow> (M \<rightarrow> M) \<rightarrow> M" and 
        F' : "F' : mOrd \<rightarrow> M \<rightarrow> M"
      proof (rule funI, rule funI)
        fix u f 
        assume u:"u : mLimit" and f:"f : M \<rightarrow> M"
        hence "G u f = G' u f"
          using G_cong[OF mord_m[OF mlimit_mord[OF u]]] funE[OF f]
          by auto
        thus "G' u f : M"
          using funE[OF funE[OF G u] f] by auto
       next
        show "F' : mOrd \<rightarrow> M \<rightarrow> M"
          using F F_cong[OF mord_m]
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
            mordrec'_msucc[OF G F A mordI[OF ih(1)]]
            mordrec'_msucc[OF G' F' A mordI[OF ih(1)]] 
        unfolding msucc_eq[OF ih(1)]
        by (simp add: A F' F_cong G' local.mordI local.ord_m local.succ_ord mordrec'_m)
      next
        case ih:(3 \<mu>)
        show ?case unfolding 
          mordrec'_lim[OF G F A mlimitI[OF ih(1)]]
          mordrec'_lim[OF G' F' A mlimitI[OF ih(1)]]
        proof (rule conjunct2[OF G_cong], auto)
          show "<ord, \<mu>> : M"
            using mord_m[OF mordI[OF limit_ord[OF ih(1)]]] .
          fix j assume "j : M" and jlt:"j \<lless> <ord, \<mu>>"
          thus "mOrdRec' G F A j : M"
            using mordrec'_m[OF G F A mlt_mord1] by auto
          show "mOrdRec' G F A j = mOrdRec' G' F' A j"
            by (rule mordE[OF mlt_mord1[OF jlt]], use ih(2) mltD jlt in auto)
        next
          show "OrdRec_Model_mdefault : M"
            using OrdRec_Model_mdefault_m .
        qed
      qed
   next
    assume "\<not> (G : mLimit \<rightarrow> (M \<rightarrow> M) \<rightarrow> M \<and> F : mOrd \<rightarrow> M \<rightarrow> M \<and> A : M \<and> j : mOrd)"
    moreover hence "\<not> (G' : mLimit \<rightarrow> (M \<rightarrow> M) \<rightarrow> M \<and> F' : mOrd \<rightarrow> M \<rightarrow> M \<and> A : M \<and> j : mOrd)"
    proof (auto)
      assume "F' : mOrd \<rightarrow> M \<rightarrow> M" "\<not> F : mOrd \<rightarrow> M \<rightarrow> M" 
      thus "False" 
        using F_cong[OF mord_m]
        unfolding fun_ty_def has_ty_def
        by auto
    next
      assume "G' : mLimit \<rightarrow> (M \<rightarrow> M) \<rightarrow> M" "\<not> G : mLimit \<rightarrow> (M \<rightarrow> M) \<rightarrow> M"
      thus "False"
        using G_cong[OF mord_m[OF mlimit_mord]]
        unfolding fun_ty_def has_ty_def
        by auto
    qed
    ultimately show "mOrdRec G F A j = mOrdRec G' F' A j"
      unfolding mOrdRec_def
      by auto
   qed
 qed
 show "OrdRec_Model_mdefault : M"
  using OrdRec_Model_mdefault_m .
qed



end
end