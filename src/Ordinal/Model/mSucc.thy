theory mSucc
  imports mlt
begin

context Ordinal_Model 
begin

end

theorem mzero_mord : 
  "m0 : mOrd"
  unfolding mzero_def
  using mordI[OF zero_ord] .

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

end