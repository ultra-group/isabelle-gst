theory OPair
  imports "../GST_Features"
begin

syntax
  "_pair" :: "['a,'a] \<Rightarrow> 'a"  (\<open>\<langle>(_,_)\<rangle>\<close>)
syntax (ASCII)
  "_pair" :: "['a, 'a] \<Rightarrow> 'a" (\<open><(_,/ _)>\<close>)
translations 
  "\<langle>b,c\<rangle>" \<rightleftharpoons> "CONST pair b c"

context OPair begin

thm cpop pair_typ funE intE1 intE2
lemmas pair_pair    [typ_intro] = intE1[OF funE[OF funE[OF pair_typ]]]
lemmas pair_pairmem [typ_intro] = intE2[OF funE[OF funE[OF pair_typ]]]

subsection \<open>PairMem soft-type\<close>

lemma pairmemI:
  assumes p:"pair a b : Pair"
    shows "a : PairMem" "b : PairMem"
  unfolding has_ty_def using PairMem_def
  using p by auto

lemma pairmemI_eq:
  assumes p:"p : Pair" "p = pair a b"
    shows "a : PairMem" "b : PairMem"
  unfolding has_ty_def using PairMem_def
  using p by auto

subsection \<open>Equality of ordered pairs\<close>

lemma pair_iff_pairmem :
  assumes "a : PairMem" "b : PairMem" "c : PairMem" "d : PairMem"
    shows "pair a b = pair c d \<longleftrightarrow> (a = c \<and> b = d)"
  using cpop assms by auto

lemma pair_iff_eq :
  assumes p:"pair a b : Pair" and q:"pair c d : Pair"
    shows "pair a b = pair c d \<longleftrightarrow> (a = c \<and> b = d)"
  by (rule pair_iff_pairmem[OF pairmemI[OF p] pairmemI[OF q]])

lemma pair_eqI :
  assumes eq : "a = c" "b = d"
    shows "<a,b> = <c,d>"
    using eq by auto
    
lemma pair_inject : 
  assumes p:"pair a b : Pair" and q:"pair c d : Pair"
      and eq: "pair a b = pair c d"
    shows "a = c" "b = d"
  using pair_iff_eq[OF p q] eq by auto

lemma pair_inject1 : 
  assumes p:"pair a b : Pair" and q:"pair c d : Pair"
  shows "pair a b = pair c d \<Longrightarrow> a=c"
  by (auto elim: pair_inject[OF assms])

lemma pair_inject2 : 
  assumes p:"pair a b : Pair" and q:"pair c d : Pair"
  shows "pair a b = pair c d \<Longrightarrow> b=d"
  by (auto elim: pair_inject[OF assms])

subsection \<open>Projection relations\<close>

lemma proj_eq : 
  assumes p:"p : Pair"
  obtains a b where "p = <a,b>"
  using pair_projs p by blast

lemma proj_eq' : 
  assumes p:"p : Pair"
  obtains a b where "a : PairMem" "b : PairMem" "p = <a,b>"
  using proj_eq[OF p] pairmemI_eq[OF p] by auto

lemma pair_pmem :
  "p : Pair \<Longrightarrow> p : PairMem"
  using proj_eq' pair_pairmem by metis

definition fst :: "'a \<Rightarrow> 'a" (\<open>\<tau>\<close>) where
  "\<tau> p \<equiv> \<iota> a. \<exists>b. p = pair a b else OPair_default"
definition snd :: "'a \<Rightarrow> 'a" (\<open>\<pi>\<close>) where
  "\<pi> p \<equiv> \<iota> b. \<exists>a. p = pair a b else OPair_default"

(*Proofs are a bit harder than in ZF here because of the PairMem type assumptions*)
lemma pair_uniq1 :
  assumes p:"p : Pair"
  shows "\<exists>!a. (\<exists>b. p = pair a b)" 
  unfolding tex1_def tex_def 
  by (rule proj_eq[OF p], rule, auto, use pair_inject1 p in auto)
 
lemma pair_uniq2 : 
  assumes p:"p : Pair"
  shows "\<exists>!b. (\<exists>a. p = pair a b \<and> p : Pair)" 
  unfolding tex1_def tex_def
  by (rule proj_eq[OF p], rule, auto, use pair_inject2 p in auto)

lemma fst_eq [simp]:
  assumes "pair a b : Pair"
  shows "\<tau> (pair a b) = a" unfolding fst_def  
  by (rule the_def_eq', use pair_uniq1 assms in auto)

lemma snd_eq [simp]: 
  assumes "pair a b : Pair"
  shows "\<pi> (pair a b) = b" unfolding snd_def 
  by (rule the_def_eq', use pair_uniq2 assms in auto)

lemma pair_proj_eq :
  assumes p:"p : Pair"
    shows "p = <\<tau> p, \<pi> p>"
proof (rule proj_eq[OF p])
  fix a b assume eq:"p = <a,b>"
  hence ab:"<a,b> : Pair" using p by simp
  show "p = <\<tau> p, \<pi> p>" 
    unfolding eq fst_eq[OF ab] snd_eq[OF ab] by rule 
qed



end
end