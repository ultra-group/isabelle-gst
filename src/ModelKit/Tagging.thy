theory Tagging
  imports "../GZF/SetComprehension" "../OPair/CartProd"             
          "../Ordinal/Ordinal" "../Ordinal/OrdRec" 
          "../Ordinal/OrdQuants"
begin

class Tagging = OrdRec + CartProd

context Tagging begin

subsection \<open>Soft typing rules\<close>

definition Tag :: \<open>'a \<Rightarrow> bool\<close>
  where "Tag \<equiv> Ord \<triangle> (\<lambda>i. i < \<omega>)" 

lemma tagI :
  assumes "i : Ord" "i < \<omega>"
    shows "i : Tag"
  unfolding Tag_def 
  using assms 
  by unfold_typs   

lemma tagD :
  assumes "i : Tag"
  shows "i : Ord" "i < \<omega>"
  using assms
  unfolding Tag_def
  by unfold_typs

lemmas tag_ord = tagD(1)

lemma depfun_ord_setof_set :
  "X : (\<Pi> i : Tag. SetOf (\<alpha> i)) \<Longrightarrow> X : (\<Pi> i : Tag. Set)"
  using setof_set[OF depfunE] by (rule depfunI)

lemma depfun_ord_set_setof : 
  "X : (\<Pi> i : Tag. Set) \<Longrightarrow> X : (\<Pi> i : Tag. SetOf (MemOf (X i)))"
  using set_setof_memof[OF depfunE] by (rule depfunI) 

lemmas ord_pmem = smem_pmem[OF ord_setmem]

subsection \<open>Tag all members of a set\<close>

definition TagMap :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix \<open>\<oplus>\<close> 60) 
  where "t \<oplus> x \<equiv> { <t, b> | b \<in> x }"

lemma tmap_typ : 
  "TagMap : (\<alpha> \<triangle> PairMem) \<rightarrow> SetOf \<beta> \<rightarrow> SetOf (\<alpha> * \<beta>)"
  unfolding TagMap_def
proof (rule funI, drule intE, rule funI, 
       rule repfun_setof[OF setof_set mem_funI], auto)
  fix t b x 
  assume "t : \<alpha>" "t : PairMem" "x : SetOf \<beta>" "b \<in> x" 
  thus "<t,b> : \<alpha> * \<beta>" 
    using productI[OF pair_pair[OF _ smem_pmem]]
          setmemI[OF setof_set] setof_mem by blast
qed

lemmas tmap_setof = funE[OF funE[OF tmap_typ]]

lemma tmap_typ_setof_pair : "TagMap : PairMem \<rightarrow> Set \<rightarrow> SetOf Pair"
proof (rule funI[OF funI])
  fix t x assume t:"t : PairMem" and x:"x : Set" 
  hence "t : (PairMem \<triangle> PairMem)" and "x : SetOf SetMem" 
    using intI[OF t] setofI[OF x] setmemI[OF x] by auto
  hence "t \<oplus> x : SetOf (PairMem * SetMem)" using tmap_setof by auto
  hence t:"t \<oplus> x : Set" and p:"\<And>p. p \<in> t \<oplus> x \<Longrightarrow> p : PairMem * SetMem" 
    by (rule setof_set, auto intro: setof_mem) 
  thus "t \<oplus> x : SetOf Pair" using setofI[OF t prod_pair[OF p]] by auto 
qed

lemmas tmap_setof_pair = funE[OF funE[OF tmap_typ_setof_pair]]
lemmas tmap_set = setof_set[OF tmap_setof_pair]

lemma tag_setfun : 
  assumes t:"t : PairMem" and x:"x : Set"
    shows "(\<lambda>b. <t,b>) : x \<leadsto> SetMem"
  by (rule rkpair1[OF x t])

lemma tmap_iff :
  assumes t:"t : PairMem" and x:"x : Set" and b:"b : SetMem"
    shows "b \<in> x \<longleftrightarrow> <t,b> \<in> t \<oplus> x"
  unfolding TagMap_def
  by (simp add: repfun_iff[OF x],
      use pair_setmem[OF t smem_pmem[OF b]]
          pair_inject[OF pair_pair[OF t smem_pmem[OF b]] 
                         pair_pair[OF t smem_pmem[OF setmemI[OF x]]]] in auto)

lemma tmapI : 
  assumes t:"t : PairMem" and x:"x : Set"
    shows "b \<in> x \<Longrightarrow> <t,b> : Pair \<and> <t,b> \<in> t \<oplus> x"
  using tmap_iff[OF t x setmemI[OF x]] 
        pair_pair[OF t smem_pmem[OF setmemI[OF x]]] by auto 

lemma tmapD : 
  assumes t:"t : PairMem" and x:"x : Set"
    shows "b \<in> t \<oplus> x \<Longrightarrow> b : Pair \<and> (\<exists>b' \<in> x. b = <t, b'>)"
  unfolding TagMap_def
  by (erule repfunE[OF x], 
      use pair_pair[OF t smem_pmem[OF setmemI[OF x]]] in auto)

lemma tmapE : 
  assumes t:"t : PairMem" and x:"x : Set"
      and b:"b \<in> t \<oplus> x"
    obtains b' where "b : Pair" "b' \<in> x" "b = <t, b'>" 
  using tmapD[OF t x b] by auto


subsection \<open>Disjoint union of an ordinal-indexed sequence of sets\<close>

definition disj :: "['a \<Rightarrow> 'a] \<Rightarrow> 'a" (\<open>\<Uplus>\<close>)
  where "disj B \<equiv> \<Union> i < \<omega>. i \<oplus> B i" 

lemma tmap_replfun :
  assumes X:"X : (\<Pi> i : Tag. Set)"
  shows "(\<lambda>i. i \<oplus> X i) : predSet \<omega> \<leadsto> Set"
proof (rule mem_funI)
  fix i assume "i \<in> predSet \<omega>"
  hence "i : Ord" "i < \<omega>" 
    using setof_mem[OF predset_setof] 
          predsetE omega_ord 
    by auto
  hence "i : PairMem" "X i : Set" 
    using smem_pmem[OF ord_setmem] depfunE[OF X tagI]
    by auto
  thus "i \<oplus> X i : Set" 
    by (rule tmap_set)
qed
 
lemma disj_typ :
   "disj : (\<Pi> i : Tag. SetOf (\<alpha> i)) \<rightarrow> SetOf (\<Sigma> i : Tag. \<alpha> i)"
proof (rule funI)
  fix X 
  assume X:"X : (\<Pi> i : Tag. SetOf (\<alpha> i))"
  have X':"X : (\<Pi> i : Tag. Set)" by (rule depfun_ord_setof_set[OF X])
  
  show "disj X : SetOf (\<Sigma> i : Tag. \<alpha> i)" unfolding disj_def
  proof (rule setofI[OF union_set[OF repfun_setof[OF 
                predset_set[OF omega_ord] tmap_replfun[OF X']]]])
    fix b assume "b \<in> (\<Union> i<\<omega>. i \<oplus> X i)"
    then obtain i where 
      i:"i : Ord" and lt:"i < \<omega>" and b:"b \<in> i \<oplus> X i"  
      unfolding repfun_union[OF predset_set[OF omega_ord] tmap_replfun[OF X']]
      using predsetE[OF omega_ord] predset_mem_ord[OF omega_ord] by auto
    hence i_pmem:"i : PairMem" and Xi:"X i : SetOf (\<alpha> i)" 
      using ord_pmem depfunE[OF X tagI] by auto
    then obtain b' where b':"b' \<in> X i" and b':"b = <i, b'>"
      using tmapE[OF _ setof_set b] by auto
    hence "b' : \<alpha> i" using setof_mem[OF Xi] by auto
    thus "b : (\<Sigma> i : Tag. \<alpha> i)" 
      using depsumI[OF _ tagI[OF i lt]] b' 
            setof_mem[OF tmap_setof_pair[OF i_pmem setof_set[OF Xi]] b] 
      by auto
  qed
qed

lemmas disj_setof = funE[OF disj_typ]

lemma disj_typ_set : "disj : (\<Pi> i : Tag. Set) \<rightarrow> Set"
proof (rule funI)
  fix X assume X:"X : (\<Pi> i : Tag. Set)"
  have "X : (\<Pi> i : Tag. SetOf SetMem)" 
    by (rule depfunI, use set_setof[OF depfunE[OF X]] in auto)
  thus "\<Uplus> X : Set" by (rule setof_set[OF disj_setof])
qed

lemmas disj_set = funE[OF disj_typ_set]

lemma tex_oex : 
  assumes j:"j : Ord" 
  shows "(\<exists> i\<in>predSet j. P i) \<longleftrightarrow> (\<exists> i<j. P i)"
  using j predset_iff predset_mem_ord[OF j] by auto

lemma disj_iff : 
  assumes X:"X : (\<Pi> i : Tag. Set)" 
  shows "b \<in> \<Uplus> X \<longleftrightarrow> (\<exists>i : Tag. \<exists>b'\<in> X i. b : Pair \<and> b = <i,b'>)" 
  using tmapD tmapI ord_pmem depfunE[OF X tagI]
  unfolding disj_def repfun_union[OF predset_set[OF omega_ord] 
            tmap_replfun[OF X]]
            tex_oex[OF omega_ord] tex_def Tag_def inter_ty_def has_ty_def by blast
  
(*Weaker version*)
lemma disj_iff' : 
  assumes X:"X : (\<Pi> i : Tag. Set)" 
  shows "<i,b'> \<in> \<Uplus> X \<longleftrightarrow> <i,b'> : Pair \<and> i : Tag \<and> b' \<in> X i"
proof (auto) 
  assume ib:"<i,b'> \<in> \<Uplus> X"
  thus "<i,b'> : Pair" "i : Tag" "b' \<in> X i"
    using depsumD_pair(1,2,3)[OF setof_mem[OF disj_setof[where \<alpha> = "\<lambda>i. MemOf (X i)", 
                                    OF depfun_ord_set_setof[OF X]] ib]] memofD 
    by auto
next
  assume "<i,b'> : Pair" "i : Tag" "b' \<in> X i"
  hence "(\<exists>i' : Tag. \<exists>c' \<in> X i'. <i,b'> : Pair \<and> <i,b'> = <i',c'>)" by auto
  thus "<i,b'> \<in> \<Uplus> X" using disj_iff[OF X] by auto
qed


lemma disjI : 
  assumes X:"X : (\<Pi> i : Tag. Set)"  
      and ib:"b : Pair" "b = <i,b'>" 
      and ij:"i : Tag" and b':"b' \<in> X i"  
  shows "b \<in> \<Uplus> X"
  using ib ij b' unfolding disj_iff[OF X] by auto

lemma disjI_pair :
  assumes X:"X : (\<Pi> i : Tag. Set)"  
      and ib:"<i,b'> : Pair" 
      and ij:"i : Tag" and b':"b' \<in> X i"  
    shows "<i,b'> \<in> \<Uplus> X"
  using ib ij b' unfolding disj_iff[OF X] by auto


lemma disjE : 
  assumes X:"X : (\<Pi> i : Tag. Set)" 
      and b:"b \<in> \<Uplus> X"
   obtains i b' where "b : Pair" "b = <i,b'>" "i : Tag" "b' \<in> X i"
  using b unfolding disj_iff[OF X] by auto

lemma disjD_pair : 
  assumes X:"X : (\<Pi> i : Tag. Set)"
      and ib:"<i,b'> \<in> \<Uplus> X"
    shows "i : Tag" "b' \<in> X i"
  using disj_iff'[OF X] ib by auto


definition Part :: "'a \<Rightarrow> ('a \<Rightarrow> bool)" (\<open>\<^enum>\<close>)
  where "\<^enum> i \<equiv> (\<lambda>j. j = i) * Any"

lemma partI_pair : 
  assumes ib:"<i,b'> : Pair"  
    shows "<i,b'> :\<^enum> i"
  unfolding Part_def 
  by (rule productI[OF ib tyI anyI], rule refl)

lemma partI : 
  assumes eq:"b = <i,b'>" and b:"b : Pair"  
    shows "b :\<^enum> i"
  using partI_pair assms by auto

lemma partE :
  assumes "b :\<^enum> i"
  obtains b' where "b : Pair" "b = <i,b'>"
  using assms unfolding Part_def
  by (rule productE, unfold_typs)

lemma partD :
  assumes "b :\<^enum> i"  
    shows "b : Pair" "\<tau> b = i"
  by (rule partE[OF assms], auto, 
      rule partE[OF assms], use fst_eq in auto)

lemma partD_pair :
  assumes "<i,b'> :\<^enum> j"  
  shows "i = j"
  using partD[OF assms] fst_eq by auto

subsection \<open>Parts of dependent sums\<close>

lemma depsum_partI :
  assumes ib:"b : (\<Sigma> i : Tag. \<alpha> i)"
  obtains i where "b :\<^enum> i"  
  by (metis depsumE[OF ib] partI_pair)

lemma depsum_partI_pair :
  assumes ib:"<i,b'> : (\<Sigma> i : Tag. \<alpha> i)"
  shows "<i,b'> :\<^enum> i"  
  by (rule partI_pair[OF depsumD(1)[OF ib]])

lemma depsum_partD : 
  assumes b:"b : (\<Sigma> i : Tag. \<alpha> i)" "b :\<^enum> i"
      and i:"i : Tag" 
    shows "\<pi> b : \<alpha> i"
  using depsumD[OF b(1)] partD[OF b(2)] by auto

lemma depsum_partE : 
  assumes i:"i : Tag" 
      and b:"b : (\<Sigma> i : Tag. \<alpha> i)" "b :\<^enum> i"
    obtains b' where "b' : \<alpha> i"
  using depsumD[OF b(1)] partD[OF b(2)] by auto

lemma depsum_part_projs : 
  assumes b:"b : (\<Sigma> i : Tag. \<alpha> i)" "b :\<^enum> i"
    shows "b : Pair" "\<tau> b : Tag" "\<pi> b : \<alpha> (\<tau> b)"
  using depsumD[OF b(1)] partD[OF b(2)] by auto

lemma depsum_part : 
  assumes b:"b : (\<Sigma> i : Tag. \<alpha> i)"
  obtains i b' where "i : Tag" "b :\<^enum> i" "b' : \<alpha> i"
  using depsumD[OF b] partI[OF pair_proj_eq] by auto 

lemma tmap_setof_part :
  assumes X:"X : Set" and i:"i : Ord"
    shows "i \<oplus> X : SetOf (\<^enum> i)"
  by (unfold Part_def, rule tmap_setof, 
      rule intI[OF tyI ord_pmem[OF i]], auto,
      rule setofI[OF X anyI])

lemma disj_partI :
  assumes X:"X : (\<Pi> i : Tag. SetOf (\<alpha> i))" 
      and b:"b \<in> \<Uplus> X"
    obtains i where "b :\<^enum> i"
  by (rule depsum_partI[OF setof_mem[OF disj_setof[OF X] b]])

lemma disj_partI_pair :
  assumes X:"X : (\<Pi> i : Tag. SetOf (\<alpha> i))" 
      and b:"<i,b'> \<in> \<Uplus> X "
    shows "<i,b'> :\<^enum> i"
  by (rule depsum_partI_pair[OF setof_mem[OF disj_setof[OF X] b]])

lemma disj_partE :
  assumes X:"X : (\<Pi> i : Tag. SetOf (\<alpha> i))" 
      and b:"b \<in> \<Uplus> X" "b :\<^enum> i"
    obtains b' 
      where "i : Tag" "b : Pair" "b = <i,b'>" "b' : \<alpha> i"
  using depsum_part_projs[OF setof_mem[OF disj_setof[OF X] b(1)] b(2)] 
        pair_proj_eq partD[OF b(2)] by metis

lemma disj_part :
  assumes X:"X : (\<Pi> i : Tag. SetOf (\<alpha> i))" 
      and i:"i : Tag"
      and b:"b = <i,b'>" and b':"b' \<in> X i"
    shows "b :\<^enum> i" "b \<in> \<Uplus> X"
  by (rule_tac [1] partI[OF b], rule_tac [2] disjI[OF depfun_ord_setof_set[OF X] _ b i(1) b'],
       use b pair_pair[OF ord_pmem[OF tagD(1)[OF i]] 
          smem_pmem[OF setmemI[OF setof_set[OF depfunE[OF X i]] b']]] 
       in auto)

end
end