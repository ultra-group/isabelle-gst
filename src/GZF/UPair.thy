theory UPair (*Possibly rename to 'FiniteSets'*)
  imports EmptySet
begin

context GZF begin

subsection \<open>Unordered pairs; defined by replacement over \<P> (\<P> \<emptyset>)\<close>

abbreviation "\<phi> x y a b \<equiv> (a = \<emptyset> \<and> b = x) \<or> (a = \<P> \<emptyset> \<and> b = y)"

definition upair' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "upair' x y \<equiv> Repl (\<P> (\<P> \<emptyset>)) (\<phi> x y)"

definition upair :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> where
  "upair x y \<equiv> if \<not> x : SetMem then 
                  if \<not> GZF_default : Set 
                  then GZF_default else x 
               else
                if \<not> y : SetMem then
                  if \<not> GZF_default : Set 
                  then GZF_default else y
                else upair' x y"

lemma upair_eq : 
  assumes "x : SetMem" "y : SetMem"
    shows "upair x y = upair' x y"
  unfolding upair_def using assms by auto

definition sng :: "'a \<Rightarrow> 'a" where
  "sng x \<equiv> upair x x"

end

syntax
  "_upair" :: "['d, 'd] \<Rightarrow> 'd" (\<open>{_,_}\<close>)
  "_sng"   :: "'d \<Rightarrow> 'd"       (\<open>{_}\<close>)
translations
  "{X,Y}" \<rightleftharpoons> "CONST upair X Y"
  "{X}"   \<rightleftharpoons> "CONST sng X" 

context GZF begin

lemma pow_not_emp : 
  assumes "x : Set" 
    shows "\<P> x \<noteq> \<emptyset>"
  by (rule not_emptyI, rule pow_bottom[OF assms])

lemma pemp_set  : "\<P> \<emptyset> : Set"   by (rule pow_set[OF emp_set])
lemma ppemp_set : "\<P> \<P> \<emptyset> : Set" by (rule pow_set[OF pemp_set])

lemma phi_replpred : 
  assumes "x : SetMem" "y : SetMem" "z : Set"
    shows "\<phi> x y : ReplPred z"
proof (insert assms, unfold ReplPred_def has_ty_def, auto)
  fix a show "\<exists>\<^sub>\<le>\<^sub>1 b : SetMem. \<phi> x y a b" unfolding ReplPred_def 
    by (unfold tuniq_def, rule, use pow_not_emp[OF emp_set] in auto)
qed

lemma upair_typ : "upair : SetMem \<rightarrow> SetMem \<rightarrow> Set"
proof (rule funI[THEN funI])
  fix a b :: 'a assume ab: "a : SetMem" "b : SetMem" 
  have "\<P> (\<P> \<emptyset>) : Set" by (rule pow_set[OF pow_set[OF emp_set]])
  thus "{a, b} : Set" unfolding upair_eq[OF ab] upair'_def 
    using repl_set[OF _ phi_replpred[OF ab]] by auto
qed

lemmas upair_set = funE[OF funE[OF upair_typ]]

lemma pow_emp_iff :  "x \<in> \<P> \<emptyset> \<longleftrightarrow> x = \<emptyset>" 
proof
  assume "x \<in> \<P> \<emptyset>" 
  hence "x : Set" "x \<subseteq> \<emptyset>" 
    using pow_mem[OF emp_set] pow_iff[OF _ emp_set] by auto
  hence "\<forall>a. a \<notin> x" using subset_iff by auto
  thus "x = \<emptyset>" using equals0I[OF \<open>x : Set\<close>] by blast
next
  assume "x = \<emptyset>" thus "x \<in> \<P> \<emptyset>" 
    using pow_bottom[OF emp_set] by auto
qed

lemma pow_pow_emp_iff : "x \<in> \<P> (\<P> \<emptyset>) \<longleftrightarrow> (x = \<emptyset> \<or> x = \<P> \<emptyset>)" 
proof
  assume "x \<in> \<P> \<P> \<emptyset>" hence "x : Set" "x \<subseteq> \<P> \<emptyset>" using pow_mem powD pemp_set by auto  
  have "x = \<emptyset> \<or> (\<exists>y. y \<in> x)" by (rule set_disj[OF \<open>x : Set\<close>]) 
  thus "x = \<emptyset> \<or> x = \<P> \<emptyset>"
  proof (rule, simp)
    assume "\<exists>y. y \<in> x" hence "\<emptyset> \<in> x" 
      using subsetD[OF \<open>x \<subseteq> \<P> \<emptyset>\<close>] pow_emp_iff by auto
    have "x = \<P> \<emptyset>" proof (rule equality_iffI[OF \<open>x : Set\<close> pemp_set], rule)
      fix a 
      show "a \<in> x \<Longrightarrow> a \<in> \<P> \<emptyset>" using subsetD[OF \<open>x \<subseteq> \<P> \<emptyset>\<close>] by auto
      show "a \<in> \<P> \<emptyset> \<Longrightarrow> a \<in> x" using \<open>\<emptyset> \<in> x\<close> pow_emp_iff by auto
    qed
    thus "x = \<emptyset> \<or> x = \<P> \<emptyset>" by simp
  qed
next
  assume "x = \<emptyset> \<or> x = \<P> \<emptyset>" hence "x : Set" "x \<subseteq> \<P> \<emptyset>" 
    using empty_subsetI subset_refl emp_set pow_set by auto
  thus "x \<in> \<P> \<P> \<emptyset>" using powI[OF _ pemp_set] by auto
qed

lemma \<phi>_uniq : "\<phi> x y a b \<Longrightarrow> (\<forall>z. \<phi> x y a z \<longrightarrow> z = b)"
  using pow_emp_iff by blast

lemma upair_iff : 
  assumes "x : SetMem" "y : SetMem" 
  shows "b \<in> upair x y \<longleftrightarrow> (b = x \<or> b = y)"
proof - 
  have pp_emp_set : "\<P> \<P> \<emptyset> : Set" by (rule pow_set[OF pow_set[OF emp_set]])
  show ?thesis unfolding upair_eq[OF assms] upair'_def
  proof (rule, erule replaceE[OF pp_emp_set phi_replpred[OF assms pp_emp_set]])
    fix a assume "a \<in> (\<P> \<P> \<emptyset>)" and "\<phi> x y a b"
    thus "(b = x \<or> b = y)" using pow_pow_emp_iff by auto
  next
    assume "(b = x \<or> b = y)"
    thus "b \<in> Repl  (\<P> \<P> \<emptyset>) (\<phi> x y)" 
    proof
      assume "b = x" 
      show "b \<in> Repl (\<P> \<P> \<emptyset>) (\<phi> x y)"
      proof (rule replaceI[OF pp_emp_set phi_replpred[OF assms pp_emp_set]])
        let ?a = "\<emptyset>" 
        show "\<phi> x y ?a b" "b : SetMem" 
          using \<open>x : SetMem\<close> \<open>b = x\<close> by simp_all
        show "\<emptyset> \<in> \<P> (\<P> \<emptyset>)" 
          using pow_pow_emp_iff by simp
      qed
    next
      assume "b = y" 
      show "b \<in> Repl (\<P> \<P> \<emptyset>) (\<phi> x y)"
      proof (rule replaceI[OF pp_emp_set phi_replpred[OF assms pp_emp_set]])
        let ?a = "\<P> \<emptyset>" 
        show "\<phi> x y ?a b" "b : SetMem"
          using \<open>y : SetMem\<close> \<open>b = y\<close> by simp_all
        show "\<P> \<emptyset> \<in> \<P> (\<P> \<emptyset>)" 
          using pow_pow_emp_iff by simp
      qed
    qed
  qed
qed

lemma upairI1 : 
  assumes "a : SetMem" "b : SetMem" 
  shows "a \<in> {a, b}" using upair_iff[OF assms] by simp

lemma upairI2 : 
  assumes "a : SetMem" "b : SetMem"
  shows "b \<in> {a, b}" using upair_iff[OF assms] by simp

lemma upairE : 
  assumes "b : SetMem" "c : SetMem" 
  shows "\<lbrakk> a \<in> {b, c} ; a=b \<Longrightarrow> P ; a=c \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" 
  by (simp add: upair_iff[OF assms], blast)

lemma upair'_set : 
  assumes "b : SetMem" "c : SetMem"
  shows "upair' b c : Set"
  using upair_set[OF assms] 
  unfolding upair_eq[OF assms] .

lemma not_setmem_not_set :
  "\<not> x : SetMem \<Longrightarrow> \<not> x : Set"
  using set_setmem by auto

lemma upair_set_setmem : 
  assumes "{b,c} : Set"
    shows "b : SetMem \<and> c : SetMem"
proof (rule ccontr, auto)
  assume b:"\<not> b : SetMem"
  hence "\<not> {b, c} : Set"
    using not_setmem_not_set[OF b]
    unfolding upair_def by auto
  thus "False" using assms ..
next
  assume c:"\<not> c : SetMem"
  hence "\<not> {b, c} : Set"
    using not_setmem_not_set
    unfolding upair_def by auto
  thus "False" using assms ..
qed

lemmas upair_smem1 = conjunct1[OF upair_set_setmem]
   and upair_smem2 = conjunct2[OF upair_set_setmem]

subsection \<open>Rules for singleton sets\<close>

lemma sng_typ : "sng : SetMem \<rightarrow> Set" 
  by (rule funI, unfold sng_def, rule upair_set, auto) 
lemmas sng_set = funE[OF sng_typ]

lemma sng_iff : 
  assumes "x : SetMem" 
    shows "a \<in> {x} \<longleftrightarrow> a = x"
  unfolding sng_def using upair_iff[OF assms assms] 
  by auto

lemma sngI : 
  assumes "a : SetMem" 
    shows "a \<in> {a}" 
  using sng_iff[OF \<open>a : SetMem\<close>] 
  by auto

lemma sngE : 
  assumes "x : SetMem" 
    shows "\<lbrakk> a \<in> {x} ; a = x \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using sng_iff[OF \<open>x : SetMem\<close>] 
  by auto


subsection \<open>Properties of upairs and singletons\<close>

lemma upair_subset: 
  assumes "a : SetMem" "b : SetMem" "x : Set"
    shows "a \<in> x \<Longrightarrow> b \<in> x \<Longrightarrow> {a, b} \<subseteq> x" 
  using upair_iff[OF assms(1,2)] 
  by auto

lemma sng_subset: 
  assumes "a : SetMem" "x : Set" 
    shows "a \<in> x \<Longrightarrow> {a} \<subseteq> x" 
  unfolding sng_def 
  using upair_subset[OF \<open>a : SetMem\<close> \<open>a : SetMem\<close> \<open>x : Set\<close>] 
  by auto

lemma sng_eq_iff : 
  assumes "a : SetMem" "b : SetMem"
    shows "{a} = {b} \<longleftrightarrow> a=b"
  by (rule equality_iff[OF sng_set[OF \<open>a : SetMem\<close>], OF sng_set[OF \<open>b : SetMem\<close>], THEN cnf.iff_trans],
      use sng_iff assms in auto)

lemma upair_eq_iff : 
  assumes "a : SetMem" "b : SetMem" "c : SetMem" "d : SetMem" 
    shows "{a, b} = {c,d} \<longleftrightarrow> ((a=c \<and> b=d) \<or> (a=d \<and> b=c))"
proof (rule equality_iff[OF upair_set[OF assms(1,2)] upair_set[OF assms(3,4)], THEN cnf.iff_trans], rule)
  assume eq:"\<forall>x. x \<in> {a, b} \<longleftrightarrow> x \<in> {c,d}"
  have "a = b \<or> a \<noteq> b" by simp
  thus "a = c \<and> b = d \<or> a = d \<and> b = c"
  proof
    assume "a = b" hence "{a, b} = {a}" unfolding sng_def by simp
    hence "c = a \<and> d = a" using eq upair_iff assms sng_iff by auto
    thus "a = c \<and> b = d \<or> a = d \<and> b = c" using \<open>a = b\<close> by auto
  next
    assume "a \<noteq> b"
    have "a \<in> upair c d" "b \<in> upair c d" using eq upairI1 upairI2 assms by auto
    thus "a = c \<and> b = d \<or> a = d \<and> b = c" using \<open>a\<noteq>b\<close> upair_iff assms by auto
  qed
next
  assume "a = c \<and> b = d \<or> a = d \<and> b = c" 
  thus "\<forall>x. (x \<in> {a, b}) \<longleftrightarrow> (x \<in> upair c d)" using upair_iff assms by auto
qed

end
end 