theory mlt
  imports mOrd
begin

context Ordinal_Model
begin


lemma mlt_mord : 
  "i \<lless> j \<Longrightarrow> i : mOrd \<and> j : mOrd"
  unfolding mlt_def by simp

lemmas mlt_mord1 = conjunct1[OF mlt_mord]
   and mlt_mord2 = conjunct2[OF mlt_mord]

lemma mltI : 
  assumes i : "i : Ord" and j : "j : Ord"
    shows "i < j \<Longrightarrow> <ord, i> \<lless> <ord, j>"
    unfolding mlt_def
    using mordI i j ord_snd_eq' by auto

lemma mltI_eq : 
  assumes i : "i' : Ord" "i = <ord, i'>" 
      and j : "j' : Ord" "j = <ord, j'>"
    shows "i' < j' \<Longrightarrow> i \<lless> j"
    using mltI assms by auto

lemma mltD :
  assumes "<ord, i> \<lless> <ord, j>"
  shows "i < j"
  using assms mord_snd_eq
  unfolding mlt_def by auto

lemma mltE1 :
  assumes ij:"i \<lless> j"
  obtains i' j' 
    where "i' : Ord" "i = <ord, i'>" 
          "j' : Ord" "j = <ord, j'>" 
          "i' < j'"
proof -
  obtain i' j' where 
    "i' : Ord" "i = <ord, i'>" "j' : Ord" "j = <ord, j'>" 
    using mordE mlt_mord[OF ij] by metis
  moreover hence "i' < j'" 
    using mltD ij by auto
  ultimately show ?thesis ..
qed

(*Less info than mltE1, maybe more efficient?*)
lemma mltE2 : 
  assumes ij:"i \<lless> j"
  obtains i' j' 
    where "i = <ord, i'>" "j = <ord, j'>" "i' < j'"
  using mltE1[OF ij] .

lemma mlt_trans :
  assumes ij: "i \<lless> j" and jk: "j \<lless> k"
    shows "i \<lless> k"
proof (rule mltE1[OF ij], rule mltE1[OF jk]) 
  fix i' j' j'' k' 
  assume i':"i' : Ord" "i = <ord, i'>"
     and "j' : Ord" "j = <ord, j'>"
     and "j'' : Ord" "j = <ord, j''>"
     and k':"k' : Ord" "k = <ord, k'>"
     and "i' < j'" "j'' < k'"
  hence "i' < j'" "j' < k'" 
    using mord_pair_inject by auto
  hence "i' < k'" 
    using trans[OF \<open>i' : Ord\<close> \<open>j' : Ord\<close> \<open>k' : Ord\<close>] by auto
  thus "i \<lless> k"
    using mltI_eq[OF i' k'] by auto
qed

theorem mlt_trans_ax :
  "m\<forall>i : mOrd. m\<forall>j : mOrd. m\<forall>k : mOrd. i \<lless> j \<longrightarrow> j \<lless> k \<longrightarrow> i \<lless> k"
  unfolding mtall_def 
  using mlt_trans by blast

lemma mlt_notsym :
  assumes ij:"i \<lless> j"
  shows "\<not> j \<lless> i"
proof (rule mltE1[OF ij])
  fix i' j' 
  assume i':"i' : Ord" "i = <ord, i'>"
     and j':"j' : Ord" "j = <ord, j'>"
     and ij:"i' < j'"
  show "\<not> j \<lless> i"
  by (rule asym[OF i'(1) j'(1) ij], 
      unfold i' j', simp add: mltD)     
qed

lemma mlt_notsym_ax : 
  "m\<forall>i : mOrd. m\<forall>j : mOrd. i \<lless> j \<longrightarrow> \<not> j \<lless> i"
  unfolding mtall_def 
  using mlt_notsym by auto

lemma mlt_linear :
  assumes i : "i : mOrd" and j : "j : mOrd"
    shows "i \<lless> j \<or> i = j \<or> j \<lless> i" 
proof (rule mordE[OF i], rule mordE[OF j])
  fix i' j' 
  assume i':"i' : Ord" "i = <ord, i'>"
     and j':"j' : Ord" "j = <ord, j'>"
  have "i' < j' \<or> i' = j' \<or> j' < i'"
    using linear[OF i'(1) j'(1)] by auto
  thus ?thesis unfolding i' j'
    using mltI[OF i'(1) j'(1)]
          mltI[OF j'(1) i'(1)] by auto
qed

lemma mlt_linear_ax :
  "m\<forall>i : mOrd. m\<forall>j : mOrd. i \<lless> j \<or> i = j \<or> j \<lless> i"
  unfolding mtall_def
  using mlt_linear by auto
 
lemma mlt_induct :  
  assumes i : "\<And>i. \<lbrakk> i : mOrd ; \<And>j. j : mOrd \<Longrightarrow> j \<lless> i \<Longrightarrow> P j \<rbrakk> \<Longrightarrow> P i" 
      and a : "a : mOrd"
    shows "P a"
proof (rule mordE[OF a])
  let ?P' = "\<lambda>b'. P (<ord, b'>)"
  fix a' assume 
    a' : "a' : Ord" "a = <ord, a'>" 
  {
    fix i' 
    assume i' : "i' : Ord" 
       and ih : "\<And>j'. j' : Ord \<Longrightarrow> j' < i' \<Longrightarrow> ?P' j'"
    hence "<ord, i'> : mOrd" 
      using mordI by auto
    moreover have "\<And>j. j : mOrd \<Longrightarrow> j \<lless> <ord,i'> \<Longrightarrow> P j"
    proof -
      fix j assume "j : mOrd" "j \<lless> <ord, i'>"
      then obtain j' where "j' : Ord" "j = <ord, j'>" "j' < i'"
        using mltD mordE by metis
      thus "P j" using ih by auto
    qed
    hence "?P' i'" using i[OF \<open><ord, i'> : mOrd\<close>] by auto
  }
  hence "?P' a'" 
    by (rule trans_induct[OF \<open>a' : Ord\<close>, of ?P'])
  thus "P a"
    unfolding a' .
qed

lemma mlt_induct_ax :
  "\<forall>P. (m\<forall>i : mOrd. (m\<forall>j : mOrd. j \<lless> i \<longrightarrow> P j) \<longrightarrow> P i) \<longrightarrow> (m\<forall>i : mOrd. P i)"
proof (rule)
  fix P show 
    "(m\<forall>i : mOrd. (m\<forall>j : mOrd. j \<lless> i \<longrightarrow> P j) \<longrightarrow> P i) \<longrightarrow> (m\<forall>i : mOrd. P i)"  
    unfolding mall_def mtall_def tall_def
    using mord_m by (metis mlt_induct[of P])
qed

end
end