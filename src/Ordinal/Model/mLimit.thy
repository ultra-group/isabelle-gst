theory mLimit
  imports msucc
begin

context Ordinal_Model 
begin

lemma mlimit_mord :
  assumes u:  "u : mLimit"
  shows "u : mOrd"
  using u unfolding mLimit_def has_ty_def
  by auto

lemma mlimitI : 
  assumes u : "u : Limit"
  shows "<ord, u> : mLimit"
  using u mordI[OF limit_ord[OF u]] mord_snd_eq
  unfolding mLimit_def has_ty_def by auto

lemma mlimitE :
  assumes u : "u : mLimit"
  obtains u' where "u' : Limit" "u = <ord, u'>"
  using mordE[OF mlimit_mord[OF u]] u ord_snd_eq
  unfolding mLimit_def has_ty_def by metis
  
lemma mlimit_mlt_mzero : 
  assumes u:"u : mLimit"
  shows "m0 \<lless> u"
proof (rule mlimitE[OF u], simp, unfold mzero_def,
       rule mltI[OF zero_ord limit_ord], auto)
  fix u' assume "u' : Limit" 
  thus "0 < u'" 
    using limit_lt_zero by auto
qed

lemma mlimit_mlt_msucc : 
  assumes u:"u : mLimit"
      and bu:"b \<lless> u"
    shows "msucc b \<lless> u"
proof (rule mlimitE[OF u])
  fix u' 
  assume u':"u' : Limit" "u = <ord,u'>"
  moreover obtain b' 
    where b':"b' : Ord" "b = <ord, b'>"
    using mordE[OF mlt_mord1[OF bu]] .
  ultimately have "b' < u'"
    using mltD bu by auto
  hence "succ b' < u'"
    using limit_lt_succ[OF u'(1) b'(1)] by auto  
  thus "msucc b \<lless> u"
    unfolding b' u' msucc_eq[OF b'(1)]
    using mltI[OF succ_ord[OF b'(1)] limit_ord[OF u'(1)]] 
    by auto
qed

lemma mlimit_mltI :
  assumes zero : "m0 \<lless> u"
      and succ : "\<And>j. j \<lless> u \<Longrightarrow> msucc j \<lless> u"
    shows "u : mLimit"
proof (rule mordE[OF mlt_mord2[OF zero]])
  fix u' 
  assume u' : "u' : Ord" "u = <ord, u'>"
  have "0 < u'"
    using mltD zero unfolding mzero_def u'
    by auto
  moreover have "\<And>j'. j' : Ord \<Longrightarrow> j' < u' \<Longrightarrow> succ j' < u'"
  proof -
    fix j' assume "j' : Ord" "j' < u'"
    hence "<ord, j'> \<lless> u" 
      using mltI[OF _ u'(1)] unfolding u' by auto
    hence "<ord, succ j'> \<lless> u"
      using succ msucc_eq[OF \<open>j' : Ord\<close>] by metis
    thus "succ j' < u'"
      using mltD unfolding u' by auto
  qed
  ultimately have "u' : Limit" 
    using u'(1)
    unfolding Limit_def inter_ty_def has_ty_def tall_def
    by auto
  thus "u : mLimit"
    unfolding u'(2)
    by (rule mlimitI)
qed

theorem mlimit_def_ax :
  "mLimit = (mOrd \<triangle> (\<lambda>\<mu>. m0 \<lless> \<mu> \<and> (m\<forall>j : mOrd. j \<lless> \<mu> \<longrightarrow> msucc j \<lless> \<mu>)))"
  using mlimit_mltI mlimit_mlt_mzero mlimit_mlt_msucc mlimit_mord mord_m mlt_mord1
  unfolding mtall_def inter_ty_def has_ty_def mall_def tall_def by meson
  
theorem momega_mlimit : 
  "m\<omega> : mLimit"
  unfolding momega_def
  by (rule mlimitI[OF omega_typ])

lemmas momega_m =
  mord_m[OF mlimit_mord[OF momega_mlimit]]

lemma momega_disj : 
  assumes u : "u : mLimit"
  shows "u = m\<omega> \<or> m\<omega> \<lless> u"
proof (rule mlimitE[OF u])
  fix u' 
  assume u': "u' : Limit" "u = <ord,u'>"
  hence "u' = \<omega> \<or> \<omega> < u'"
    using omega_ax by auto
  thus "u = m\<omega> \<or> m\<omega> \<lless> u"
    unfolding u' momega_def 
    using mltI[OF omega_ord limit_ord[OF u'(1)]] by auto
qed

lemma mlimit_ax :
  "m\<forall>\<mu> : mLimit. \<mu> = m\<omega> \<or> m\<omega> \<lless> \<mu>"
  unfolding mtall_def
  using momega_disj by auto
    
  

end
end