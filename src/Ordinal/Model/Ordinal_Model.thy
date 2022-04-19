theory Ordinal_Model
  imports mLimit
begin

context Ordinal_Model 
begin

ML \<open>val mOrdinal = 
  mk_msig [] "mOrdinal" @{class Ordinal}
    ["mOrd", "mlt", "mzero", "msucc", "momega", 
     "mLimit", "Ordinal_Model_mdefault"] @{context}\<close>

translate_axioms mOrdinal_axioms : mOrdinal
proof -
  show "m\<forall>x. x : mOrd \<longrightarrow> msucc x : mOrd"
    using msucc_mord by auto
  show "m0 : mOrd"
    using mzero_mord .
  show "m\<omega> : mLimit"
    using momega_mlimit .
  show "m\<forall>b : mOrd. \<not> b \<lless> m0"
    by (insert mzero_ax)
  show "m\<forall>a : mOrd. m\<forall>b : mOrd. (a \<lless> msucc b) = (a \<lless> b \<or> a = b)"
    using msucc_ax .
  show "m\<forall>\<mu> : mLimit. \<mu> = m\<omega> \<or> m\<omega> \<lless> \<mu>"
    using mlimit_ax .
  show "m\<forall>i : mOrd. m\<forall>j : mOrd. m\<forall>k : mOrd. i \<lless> j \<longrightarrow> j \<lless> k \<longrightarrow> i \<lless> k"
    using mlt_trans_ax .
  show "m\<forall>i : mOrd. m\<forall>j : mOrd. i \<lless> j \<longrightarrow> \<not> j \<lless> i"  
    using mlt_notsym_ax .
  show "m\<forall>i : mOrd. m\<forall>j : mOrd. i \<lless> j \<or> i = j \<or> j \<lless> i"
    using mlt_linear_ax .
  show "\<forall>P. (m\<forall>i : mOrd. (m\<forall>j : mOrd. j \<lless> i \<longrightarrow> P j) \<longrightarrow> P i) \<longrightarrow> mtall mOrd P"
    using mlt_induct_ax .
  show "m\<forall>u. mLimit u = (mOrd \<triangle> (\<lambda>\<mu>. m0 \<lless> \<mu> \<and> (m\<forall>j : mOrd. j \<lless> \<mu> \<longrightarrow> msucc j \<lless> \<mu>))) u"
    using mlimit_def_ax by auto
qed

resp_thms mOrdinal_resp : mOrdinal
 by (rule mzero_m, rule msucc_m, rule momega_m, 
    rule Ordinal_Model_mdefault_m)

end
end