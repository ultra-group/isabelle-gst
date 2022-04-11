theory msucc
  imports mlt
begin

context Ordinal_Model 
begin

theorem mzero_mord : 
  "m0 : mOrd"
  unfolding mzero_def
  using mordI[OF zero_ord] .

lemmas mzero_m = 
  mord_m[OF mzero_mord]

lemma mzero_mlt :
  assumes j:"j : mOrd"
  shows "\<not> (j \<lless> m0)"
  unfolding mzero_def
proof (rule mordE[OF j], auto)
  fix j' assume "j' : Ord" "<ord, j'> \<lless> <ord, 0>"
  hence "j' < 0"  
    using mltD by auto
  thus "False" 
    using zero_lt[OF \<open>j' : Ord\<close>] by auto 
qed

theorem mzero_ax :
  "m\<forall>b : mOrd. \<not> b \<lless> m0"
  unfolding mtall_def mall_def
  using mzero_mlt by auto

lemma msucc'_mord :
  assumes j : "j : mOrd"
  shows "msucc' j : mOrd"
  unfolding msucc'_def
  using mordI[OF succ_ord[OF mord_snd_ord[OF j]]] .

lemma msucc_mord :
  assumes j : "j : mOrd"
  shows "msucc j : mOrd"
  unfolding msucc_def
  using msucc'_mord[OF j] j by auto

lemma msucc_m : 
  "msucc j : M"
  unfolding msucc_def 
  using mord_m[OF msucc'_mord] Ordinal_Model_mdefault_m 
  by auto

lemma msucc_eq :
  assumes j' : "j' : Ord"
  shows "msucc <ord, j'> = <ord, succ j'>"
  unfolding msucc_def msucc'_def 
  using mordI[OF j'] mord_snd_eq by auto

lemma msuccI : 
  assumes i : "i : mOrd" and j : "j : mOrd"
      and ij:"i \<lless> j \<or> i = j"
    shows "i \<lless> msucc j"
proof (rule mordE[OF i], rule mordE[OF j])
  fix i' j' 
  assume i': "i' : Ord" "i = <ord, i'>"
     and j': "j' : Ord" "j = <ord, j'>"
  from ij have "i' < succ j'"
    unfolding i' j' 
    using leqI1[OF i'(1) j'(1) mltD] 
          leqI2[OF i'(1) j'(1) mord_pair_inject[OF i'(1) j'(1)]]
    by auto
 thus "i \<lless> msucc j" 
  unfolding i' j' msucc_eq[OF j'(1)]
  using mltI[OF i'(1) succ_ord[OF j'(1)]]
  by auto
qed

lemma msuccD :
  assumes i : "i : mOrd" and j : "j : mOrd"
      and ij: "i \<lless> msucc j"
    shows "i \<lless> j \<or> i = j"
proof (rule mordE[OF i], rule mordE[OF j])
  fix i' j' 
  assume i': "i' : Ord" "i = <ord, i'>"
     and j': "j' : Ord" "j = <ord, j'>"
  from ij have "i' < succ j'"
    unfolding i' j' msucc_eq[OF j'(1)]
    using mltD by auto
  hence "i' < j' \<or> i' = j'"
    using leqE[OF i'(1) j'(1)] by auto
  thus "i \<lless> j \<or> i = j"
    unfolding i' j'
    using mltI[OF i'(1) j'(1)] by auto
qed

theorem msucc_ax :
  "m\<forall>i : mOrd. m\<forall>j : mOrd. i \<lless> msucc j \<longleftrightarrow> (i \<lless> j \<or> i = j)"
  unfolding mtall_def mall_def
  using msuccI msuccD by blast
    
end
end