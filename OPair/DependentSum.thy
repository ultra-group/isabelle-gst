theory DependentSum
  imports OPair
begin

context OPair begin

subsection \<open>Dependent Sum Type\<close>

definition depsum_ty :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('a \<Rightarrow> bool)) \<Rightarrow> ('a \<Rightarrow> bool)" 
  where "depsum_ty \<alpha> \<beta> \<equiv> Pair \<bar> (\<lambda>p. \<tau> p : \<alpha> \<and> \<pi> p : \<beta> (\<tau> p))"

end

syntax
  "_depsum_ty" :: "[pttrn, 'a \<Rightarrow> bool, bool] => bool" (\<open>(3\<Sigma>_:_./ _)\<close> 10)
(*What does CONST do?*)
translations
  "\<Sigma> x:A. B" \<rightleftharpoons> "CONST depsum_ty A (\<lambda>x. B)"

context OPair begin
lemma depsumI : 
  assumes ab:"<a,b> : Pair" 
     and a:"a : A" and b:"b : B a" 
  shows "<a,b> : (\<Sigma> a : A. B a)"
  unfolding depsum_ty_def
  by (rule intI[OF ab], 
      rule tyI, unfold fst_eq[OF ab] snd_eq[OF ab],
      simp only: a b)

lemma depsumI_eq : 
  assumes p:"p : Pair" "p = <a,b>" 
      and a:"a : A" and b:"b : B a" 
    shows "p : (\<Sigma> a : A. B a)"
  using depsumI[of a b A B, OF _ a b] p by auto

lemma depsumD : 
  assumes t:"t : (\<Sigma> a : A. B a)"
  shows "t : Pair" "\<tau> t : A" "\<pi> t : B (\<tau> t)"
  by (insert t, unfold depsum_ty_def, unfold_typs)

lemma depsumD_pair : 
  assumes t:"<a,b> : (\<Sigma> a : A. B a)"
  shows "<a,b> : Pair" "a : A" "b : B a"
  using depsumD[OF t] fst_eq snd_eq by auto

lemma depsumE : 
  assumes t:"t : (\<Sigma> a : A. B a)"
  obtains a b where "t : Pair" "t = <a,b>" "a : A" "b : B a" 
  using depsumD[OF t] pair_proj_eq by blast

lemma depsum_pair_subtyp : 
  "(\<Sigma> a : A. B a) << Pair"
  by (rule subtypI, drule depsumD(1), assumption)
subsection \<open>Product soft-type\<close>

definition Product (infix \<open>*\<close> 50) 
  where [typdef] : "\<alpha> * \<beta> \<equiv> \<Sigma> x : \<alpha>. \<beta>"

lemma productI [typ_intro] : 
  assumes "<a,b> : Pair" "a : \<alpha>" "b : \<beta>" 
  shows "<a,b> : \<alpha> * \<beta>"
  unfolding Product_def 
  by (rule depsumI, use assms in auto)

lemma productD : 
  assumes t:"t : \<alpha> * \<beta>"
  shows "t : Pair" "\<tau> t : \<alpha>" "\<pi> t : \<beta>"
  by (insert t, unfold Product_def, use depsumD in auto)

lemma productD_pair : 
  assumes t:"<a,b> : \<alpha> * \<beta>"
  shows "<a,b> : Pair" "a : \<alpha>" "b : \<beta>"
proof -
  from t have ab:"<a,b> : (\<Sigma> a:\<alpha>. \<beta>)" by (unfold Product_def)
  show "<a,b> : Pair" "a : \<alpha>" "b : \<beta>" using depsumD_pair[OF ab] by auto
qed

lemma productE :
  assumes "p : \<alpha> * \<beta>"
  obtains a b where "p : Pair" "p = <a,b>" "a : \<alpha>" "b : \<beta>"
  using assms unfolding Product_def 
  by (blast elim: depsumE)

lemma prod_pair : "p : \<alpha> * \<beta> \<Longrightarrow> p : Pair" 
  by (rule productE)

end
end