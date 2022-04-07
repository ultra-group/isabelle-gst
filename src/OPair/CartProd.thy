theory CartProd
  imports DependentSum "../GZF/SetComprehension"
begin

text \<open>
  To define Cartesian Products, we need both sets and pairs.
  We stay abstract and define a new class that imports a 
  representation of sets, and pairs. 
  
  An extra axiom is needed so that we can construct pairs out of the
  elements of sets, and construct sets with pairs as members.\<close>

class CartProd = GZF + OPair +
  assumes setmem_pair_typ1 : "pair : SetMem \<rightarrow> SetMem \<rightarrow> Pair"
      and setmem_pair_typ2 : "pair : PairMem \<rightarrow> PairMem \<rightarrow> SetMem"  

context CartProd begin

lemmas setmem_pair = funE[OF funE[OF setmem_pair_typ1]]
lemmas pair_setmem = funE[OF funE[OF setmem_pair_typ2]]

lemma smem_pmem :
  "b : SetMem \<Longrightarrow> b : PairMem"
  using setmem_pair[of b b] 
  unfolding PairMem_def has_ty_def tex_def by auto
  

subsection \<open>Cartesian product\<close>

definition cprod :: "['a, 'a] \<Rightarrow> 'a" (infixr \<open>\<times>\<close> 80) 
  where "cprod x y \<equiv> \<Union> {{<a,b> | b \<in> y} | a \<in> x}"

(*rkpair1, rkpair2, and rkpair_setof are all type introduction rules,
  but we don't mark them with the [typ_intro] attribute so we don't pollute the \<open>unfold_typs\<close> method*)

lemma rkpair1 :
  assumes x:"x : Set" and a:"a : PairMem" 
    shows "(\<lambda>b. <a,b>) : x \<leadsto> SetMem"
  by (rule mem_funI, rule pair_setmem[OF a], 
      erule smem_pmem[OF setmemI[OF x]])

lemma rkpair2 :
  assumes x:"x : Set" and y:"y : Set"
  shows "(\<lambda>a. {<a,b> | b \<in> y}) : x \<leadsto> SetMem" 
  by (rule mem_funI, rule set_setmem[OF repfun_set[OF y]]) 

lemma rkpair_setof : 
  assumes x:"x : Set" and y:"y : Set" 
  shows "{{<a,b> | b \<in> y} | a \<in> x} : SetOf Set"
proof (rule setofI[OF repfun_set[OF x]])
  let ?R = "{{<a,b> | b \<in> y} | a \<in> x}"
  fix b assume "b \<in> ?R" thus "b : Set" 
    by (rule repfunE[OF x], use repfun_set[OF y] in auto)
qed

lemma cprod_set [typ_intro] : assumes "x : Set" "y : Set" shows "x \<times> y : Set"
  unfolding cprod_def by (rule union_set, rule rkpair_setof[OF assms])

lemma cprod_iff : 
  assumes x:"x : Set" and y:"y : Set"
  shows "p \<in> x \<times> y \<longleftrightarrow> (\<exists>a b. p = <a,b> \<and> a \<in> x \<and> b \<in> y)" 
proof -  
  have F:"(\<lambda>a. {<a,b> | b \<in> y}) : x \<leadsto> Set" 
    by (rule mem_funI[OF repfun_set[OF y]])
  show ?thesis 
    unfolding cprod_def repfun_union[OF x F] repfun_iff[OF y] bex_def rex_def
    using pair_setmem[OF smem_pmem smem_pmem] setmemI x y  by auto
qed

lemma cprod_setof_prod [typ_intro]: 
  assumes x:"x : SetOf \<alpha>" and y:"y : SetOf \<beta>" 
    shows "cprod x y : SetOf (\<alpha> * \<beta>)"
proof (rule setofI, rule typ_intro)
  show x':"x : Set" and y':"y : Set" 
    using subtypE[OF setof_set_subtyp] assms by auto 
  fix p assume "p \<in> x \<times> y"
  then obtain a b 
    where p:"p = pair a b" and "a \<in> x" "b \<in> y" 
    using cprod_iff[OF x' y'] by auto
  hence "<a,b> : Pair" "a : \<alpha>" "b : \<beta>" 
    using setof_mem[OF x] setof_mem[OF y] 
          setmem_pair[OF setmemI[OF x'] setmemI[OF y']] by auto
  thus "p : \<alpha> * \<beta>" using p by (auto intro: productI)
qed

lemma cprod_setof [typ_intro] : 
  assumes "x : Set" "y : Set"
    shows "x \<times> y : SetOf Pair"
proof (rule setofI[OF cprod_set[OF assms]])
  fix p assume "p \<in> x \<times> y"
  then obtain a b where "p = pair a b" "a \<in> x" "b \<in> y" using cprod_iff[OF assms] by auto
  thus "p : Pair" using setmemI assms setmem_pair by auto
qed

lemma cprod_typ : "cprod : Set \<rightarrow> Set \<rightarrow> Set" 
  by (unfold_typs)

lemma cprod_typ2 : "cprod : SetOf \<alpha> \<rightarrow> SetOf \<beta> \<rightarrow> SetOf (\<alpha> * \<beta>)"
  by (rule funI, rule funI, rule cprod_setof_prod)

lemma cprod_typ3 : "cprod : Set \<rightarrow> Set \<rightarrow> SetOf Pair"
  by (rule funI, rule funI, rule cprod_setof)

lemma cprod_iff_pair : 
  assumes "x : Set" "y : Set" "pair a b : Pair" 
  shows "pair a b \<in> x \<times> y \<longleftrightarrow> a \<in> x \<and> b \<in> y" 
  unfolding cprod_iff[OF assms(1,2)] 
  using pair_inject[OF assms(3) setmem_pair[OF setmemI[OF \<open>x : Set\<close>] setmemI[OF \<open>y : Set\<close>]]]
  by blast

lemma cprodI : 
  assumes "x : Set" "y : Set" 
  shows "a \<in> x \<Longrightarrow> b \<in> y \<Longrightarrow> p = pair a b \<Longrightarrow> p \<in> x \<times> y"
  using cprod_iff[OF assms] by auto

lemma cprodI_pair : 
  assumes "x : Set" "y : Set" 
  shows "a \<in> x \<Longrightarrow> b \<in> y \<Longrightarrow> pair a b \<in> x \<times> y"
  using cprod_iff_pair[OF assms] setmem_pair setmemI assms by auto

lemma cprodE : 
  assumes "x : Set" "y : Set" 
  shows "\<lbrakk> p \<in> x \<times> y ; \<And>a b. \<lbrakk> a \<in> x ; b \<in> y ; p = pair a b \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using cprod_iff[OF assms] by auto   

lemma cprodE_pair : 
  assumes "x : Set" "y : Set" 
  shows "\<lbrakk> pair a b \<in> x \<times> y ; \<And>a b. \<lbrakk> a \<in> x ; b \<in> y \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using cprod_iff[OF assms] by auto   

lemma cprodD1 : 
  assumes "x : Set" "y : Set" "pair a b : Pair" 
  shows "pair a b \<in> x \<times> y \<Longrightarrow> a \<in> x" 
  using cprod_iff_pair assms by auto

lemma cprodD2 : 
  assumes "x : Set" "y : Set" "pair a b : Pair" 
  shows "pair a b \<in> x \<times> y \<Longrightarrow> b \<in> y"
  using cprod_iff_pair[OF assms] by auto

lemma cprod_eq : "\<lbrakk> x=x' ; y=y' \<rbrakk> \<Longrightarrow> x\<times>y = x'\<times>y'" by auto

thm fst_eq
lemma fst_set : 
  assumes "x : Set" "y : Set" 
  shows "p \<in> x \<times> y \<Longrightarrow> fst p \<in> x"
  by (rule cprodE[OF assms], use setmem_pair setmemI assms fst_eq in auto)

lemma snd_set : 
  assumes "x : Set" "y : Set" 
  shows "p \<in> x \<times> y \<Longrightarrow> snd p \<in> y"
  by (rule cprodE[OF assms], use setmem_pair setmemI assms snd_eq in auto)

lemma fst_snd_eq : 
  assumes "x : Set" "y : Set" 
  shows "p \<in> x \<times> y \<Longrightarrow> pair (fst p) (snd p) = p"
  by (rule cprodE[OF assms], use setmem_pair setmemI assms fst_eq snd_eq in auto)

end
end