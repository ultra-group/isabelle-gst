theory DependentOrd
  imports Ordinal "../OPair/DependentSum" 
begin

abbreviation (in Ordinal) (input) gt where "gt j i \<equiv> lt i j"

syntax
  "_depfun_ord" :: "[pttrn, 'a, bool] => bool" (\<open>(3\<Pi>_<_./ _)\<close> 10)
  "_depsum_ord" :: "[pttrn, 'a, bool] => bool" (\<open>(3\<Sigma>_<_./ _)\<close> 10)
translations
  "\<Pi> i<j. B" \<rightleftharpoons> "\<Pi> i:(CONST Ord \<triangle> (CONST gt) j). B"
  "\<Sigma> i<j. B" \<rightleftharpoons> "\<Sigma> i:(CONST Ord \<triangle> (CONST gt) j). B"

context Ordinal begin

subsection \<open>Rules for dependent functions on ordinals\<close>

lemma depfun_ordI :
  assumes i:"\<And>i. i : Ord \<Longrightarrow> i < j \<Longrightarrow> F i :  B i"
  shows "F : (\<Pi> i < j. B i)"
  by (rule depfunI, drule intE, use i in unfold_typs)

lemma depfun_ordE :
  assumes F:"F : (\<Pi> i < j. B i)" 
      and i:"i : Ord" "i < j"
  shows "F i : B i"
  by (rule depfunE[OF F intI[OF i(1) tyI]], rule i(2))

end

class DepSumOrd = 
  OPair + Ordinal

begin

subsection \<open>Rules for dependent sums on ordinals\<close>

lemma depsum_ordI : 
  assumes ib:"<i,b> : Pair" 
      and i:"i : Ord" "i < j" and b:"b : B i" 
    shows "<i,b> : (\<Sigma> i < j. B i)"
  by (rule depsumI[OF ib intI[OF i(1) tyI]], rule i(2), rule b)

lemma depsum_ordD : 
  assumes t:"t : (\<Sigma> i < j. B i)"
  shows "t : Pair" "\<tau> t : Ord" "\<tau> t < j" "\<pi> t : B (\<tau> t)"
  by (use depsumD[OF t] in unfold_typs)

lemma depsum_ordD_pair : 
  assumes t:"<i,b> : (\<Sigma> i < j. B i)"
  shows "<i,b> : Pair" "i : Ord" "i < j" "b : B i"
  by (use depsumD_pair[OF t] in unfold_typs)

lemma depsum_ordE : 
  assumes t:"t : (\<Sigma> i < j. B i)"
  obtains i b where "t : Pair" "t = <i,b>" "i : Ord" "i < j" "b : B i"
  by (rule depsumE[OF t], unfold_typs)

end
end

