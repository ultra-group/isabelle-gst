theory mOrdRec
  imports OrdRec_Model_Base
begin

context OrdRec_Model begin

lemma mordrec'_zero :
  assumes A : "A : M"
  shows "mOrdRec' G F A m0 = A"
  using ordrec_0 
  unfolding 
    mOrdRec'_def mzero_def 
    ord_snd_eq'[OF zero_ord] forceM_ordrec_eq[OF A]
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
  using forceM_ordrec_m .

lemma mordrecF_m :
  shows "mordrecF F j' b : M"
  unfolding mordrecF_def
  using forceM_ordrec_m .

lemma mordrec'_m :
  assumes  j : "j : mOrd"
  shows "mOrdRec' G F A j : M"
proof (rule ord_cases[OF mord_snd_ord[OF j]])
  assume "snd j = 0"
  thus "mOrdRec' G F A j : M"
    unfolding mOrdRec'_def
    using ordrec_0 forceM_ordrec_m by auto
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
  assumes F : "F : M \<rightarrow> M \<rightarrow> M" and j : "j : mOrd"
  shows "mOrdRec' G F A (msucc j) = F (msucc j) (mOrdRec' G F A j)"
proof -
  have "mOrdRec' G F A (msucc j) = 
    OrdRec (mordrecG G) (mordrecF F) (forceM_ordrec A) (succ (snd j))"
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
      forceM_ordrec_eq[OF funE[OF funE[OF F mord_m[OF msucc_mord[OF j]]] 
      mordrec'_m[OF \<open>j : mOrd\<close>]]] .
qed

lemma mlimit_snd_limit : 
  "u : mLimit \<Longrightarrow> snd u : Limit"
  by (erule mlimitE, use ord_snd_eq[OF limit_ord] in auto) 

lemma mord_snd_eq' : 
  "u : mOrd \<Longrightarrow> <ord, \<pi> u> = u"
  by (erule mordE, use ord_snd_eq in auto) 

lemma mordrec'_lim :
  assumes G : "G : LimFun"
      and u : "u : mLimit"
  shows "mOrdRec' G F A u = 
   G u (\<lambda>j. if j \<lless> u then mOrdRec' G F A j else OrdRec_Model_mdefault)"
proof -
  note G_m = limfunD1[OF G]
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
  by (rule funI, use mordrec'_m[OF mlt_mord1] OrdRec_Model_mdefault_m in auto)

  have "mOrdRec' G F A u = 
    OrdRec (mordrecG G) (mordrecF F) (forceM_ordrec A) (snd u)"
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
      forceM_ordrec_eq[OF funE[OF funE[OF G_m mord_m[OF mlimit_mord[OF u]]] if_M]] .
qed

lemma mordrec_eq :
  assumes G : "G : LimFun" 
      and F : "F : M \<rightarrow> M \<rightarrow> M" 
      and A : "A : M" and j : "j : mOrd"
    shows "mOrdRec G F A j = mOrdRec' G F A j"
    unfolding mOrdRec_def using assms by auto

lemma mordrec_fun_eq :
  assumes G : "G : LimFun" 
      and F : "F : M \<rightarrow> M \<rightarrow> M" 
      and A : "A : M"
 shows "(\<lambda>j. if j : mOrd \<and> j \<lless> u then mOrdRec G F A j else OrdRec_Model_mdefault) = 
        (\<lambda>j. if j \<lless> u then mOrdRec' G F A j else OrdRec_Model_mdefault)"
    using mordrec_eq[OF G F A] mlt_mord1 by auto

lemma mordrec_m :
  "mOrdRec G F A j : M"
  unfolding mOrdRec_def
  using mordrec'_m OrdRec_Model_mdefault_m
  by auto

lemma mordrec_mzero :
  assumes G : "G : LimFun" 
      and F : "F : M \<rightarrow> M \<rightarrow> M" 
      and A : "A : M"
  shows "mOrdRec G F A m0 = A"
  unfolding mordrec_eq[OF assms mzero_mord]
  using mordrec'_zero[OF A] .

lemma mordrec_msucc :
  assumes G : "G : LimFun" 
      and F : "F : M \<rightarrow> M \<rightarrow> M" 
      and A : "A : M" and j : "j : mOrd"
    shows "mOrdRec G F A (msucc j) = F (msucc j) (mOrdRec G F A j)"
    unfolding 
      mordrec_eq[OF G F A msucc_mord[OF j]]
      mordrec_eq[OF G F A j]
    using
      mordrec'_msucc[OF F j] .

lemma mordrec_mlim :
  assumes G : "G : LimFun" 
      and F : "F : M \<rightarrow> M \<rightarrow> M" 
      and A : "A : M" and u : "u : mLimit"
    shows "mOrdRec G F A u = 
      G u (\<lambda>j. if j : mOrd \<and> j \<lless> u then mOrdRec G F A j else OrdRec_Model_mdefault)"
    unfolding 
      mordrec_eq[OF G F A mlimit_mord[OF u]]
      mordrec_fun_eq[OF G F A]
    using 
      mordrec'_lim[OF G u] .

end
end