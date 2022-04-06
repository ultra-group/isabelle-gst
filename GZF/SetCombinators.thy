theory SetCombinators
  imports SetComprehension UPair 
begin

context GZF begin

subsection \<open>Intersection of a set of sets\<close>

definition Int :: "'a \<Rightarrow> 'a" (\<open>\<Inter> _\<close> [90] 90)
  where "\<Inter> x \<equiv> { b \<in> \<Union> x | \<forall>y \<in> x. b \<in> y }"

lemma Int_typ : "Int : SetOf Set \<rightarrow> Set" 
  unfolding Int_def 
  by (rule funI, rule collect_set[OF union_set], assumption)

lemmas Int_set = funE[OF Int_typ]

lemma Int_iff: 
  assumes "x : SetOf Set"
  shows "a \<in> \<Inter> x \<longleftrightarrow> (ball x (\<lambda>y. a \<in> y)) \<and> x \<noteq> \<emptyset> "
proof
  assume "a \<in> \<Inter> x" hence "a \<in> \<Union> x" "ball x (\<lambda>y. a \<in> y)" unfolding Int_def
    using collectE[OF funE[OF Union_typ \<open>x : SetOf Set\<close>]] by auto
  thus "ball x (\<lambda>y. a \<in> y) \<and> x \<noteq> \<emptyset>" using union_emp[OF assms] by auto
next
  assume "ball x (\<lambda>y. a \<in> y) \<and> x \<noteq> \<emptyset>" 
  hence ball:"ball x (\<lambda>y. a \<in> y)" and "x \<noteq> \<emptyset>" by simp_all
  have "a \<in> \<Union> x"
  proof (rule not_emptyE[OF subtypE[OF setof_set_subtyp assms] \<open>x \<noteq> \<emptyset>\<close>])
    fix y assume "y \<in> x" thus "a \<in> \<Union> x" 
      using ball unionI[OF assms] unfolding ball_def rall_def by auto
  qed
  thus "a \<in> \<Inter> x" unfolding Int_def using ball collectI[OF funE[OF Union_typ assms]] by auto
qed

lemma IntI : 
  assumes "x : SetOf Set" 
  shows "\<lbrakk> \<And>y. y \<in> x \<Longrightarrow> a \<in> y ; x \<noteq> \<emptyset> \<rbrakk> \<Longrightarrow> a \<in> \<Inter> x"
  using Int_iff[OF assms] by auto

lemma IntD : 
  assumes "x : SetOf Set" 
  shows "\<lbrakk> a \<in> \<Inter> x ; y \<in> x \<rbrakk> \<Longrightarrow> a \<in> y"
  using Int_iff[OF assms] by auto

lemma IntE : 
  assumes "x : SetOf Set" 
  shows "\<lbrakk> a \<in> \<Inter> x ; y \<notin> x \<Longrightarrow> R; a \<in> y \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  using Int_iff[OF assms] by auto

subsection \<open>Set difference\<close>

definition diff :: "['a, 'a] \<Rightarrow> 'a" (infixl \<open>-\<close> 65) 
  where "x - y \<equiv> { b \<in> x | b \<notin> y }"
(*   *)
(*Diff will return a set even if its second argument (y above) is not a set*)
lemma diff_typ : "diff : Set \<rightarrow> Set \<rightarrow> Set" unfolding diff_def
  by (rule funI, rule funI, use collect_set in auto)

lemmas diff_set = funE[OF funE[OF diff_typ]]

lemma diff_iff : 
  assumes "x : Set" 
    shows "a \<in> x - y \<longleftrightarrow> a \<in> x \<and> a \<notin> y"
  unfolding diff_def using collect_iff[OF assms] by simp

lemma diffI : 
  assumes "x : Set" 
    shows "\<lbrakk> a \<in> x ; a \<notin> y \<rbrakk> \<Longrightarrow> a \<in> x - y"
  using diff_iff[OF assms] by simp

lemma diffD1 : 
  assumes "x : Set" 
    shows "a \<in> x - y \<Longrightarrow> a \<in> x" 
  using diff_iff[OF assms] by simp

lemma diffD2 : 
  assumes "x : Set" 
    shows "a \<in> x - y \<Longrightarrow> a \<notin> y" 
  using diff_iff[OF assms] by simp

lemma diffE : 
  assumes "x : Set" 
    shows "\<lbrakk> a \<in> x - y ; \<lbrakk> a \<in> x ; a \<notin> y\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using diff_iff[OF assms] by simp

lemma diff_sub : 
  assumes "x : Set" "y : Set" "z : Set" 
    shows "x \<subseteq> y \<Longrightarrow> x - z \<subseteq> y - z"
  using subset_iff diff_iff diff_set assms by auto

lemma diff_subset1 : 
  assumes "x : Set" "y : Set" "z : Set" "a : Set"
    shows "x \<subseteq> y \<Longrightarrow> a \<subseteq> (x - z) \<Longrightarrow> a \<subseteq> (y - z)"
  using subset_iff diff_iff funE[OF funE[OF diff_typ _] _] assms by auto

lemma diff_subset2 : 
  assumes "x : Set" "y : Set" "z : Set" 
    shows "x \<subseteq> (y - z) \<Longrightarrow> x \<subseteq> y"
  using subset_iff diff_iff[OF \<open>y : Set\<close>] diff_set assms by auto

lemma diff_emp : 
  assumes "x : Set" 
    shows "\<emptyset> - x = \<emptyset>"
proof -
  have "\<emptyset> - x : Set" by (rule diff_set[OF emp_set assms])
  show ?thesis using diff_iff[OF emp_set] equals0I[OF \<open>\<emptyset> - x : Set\<close>] by auto
qed


subsection \<open>Binary union and intersection\<close>

definition un :: "['a,'a] \<Rightarrow> 'a" (infixl \<open>\<union>\<close> 90) where
  "x \<union> y \<equiv> \<Union> upair x y"

lemma upair_setof : "x : Set \<Longrightarrow> y : Set \<Longrightarrow> upair x y : SetOf Set"
proof (rule setofI, rule upair_set)
  fix x y assume xy: "x : Set" "y : Set"
  thus "x : SetMem" "y : SetMem" by (simp_all only: set_setmem)
  moreover fix b assume "b \<in> upair x y"
  ultimately show "b : Set" using upair_iff xy by auto
qed

lemma un_typ : "(\<union>) : Set \<rightarrow> Set \<rightarrow> Set" unfolding un_def 
  by (rule funI, rule funI, simp only: union_set[OF upair_setof])

lemmas un_set = funE[OF funE[OF un_typ]]

lemma un_iff :
  assumes "x : Set" "y : Set" 
  shows "a \<in> x \<union> y \<longleftrightarrow> (a \<in> x \<or> a \<in> y)"
  unfolding un_def
  by (simp add: union_iff[OF upair_setof[OF assms]],
      use upair_iff set_setmem assms in auto)

lemma unI1 : 
  assumes "x : Set" "y : Set" 
  shows"a \<in> x \<Longrightarrow> a \<in> x \<union> y" by (simp add: un_iff assms)
lemma unI2 : 
  assumes "x : Set" "y : Set" 
  shows "b \<in> y \<Longrightarrow> b \<in> x \<union> y" by (simp add: un_iff assms)

lemma un_subset1 : 
  assumes "x : Set" "y : Set" 
  shows "x \<subseteq> x \<union> y" 
  using subsetI unI1[OF assms] by simp

lemma un_subset2 : 
  assumes "x : Set" "y : Set" 
  shows "y \<subseteq> x \<union> y" 
  using subsetI unI2[OF assms] by simp
                                                                               
lemma unE : 
  assumes "x : Set" "y : Set" 
  shows "\<lbrakk> a \<in> x \<union> y ; a \<in> x \<Longrightarrow> P ; a \<in> y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add: un_iff[OF assms], blast)

lemma unE' : 
  assumes "x : Set" "y : Set" 
  shows "\<lbrakk> a \<in> x \<union> y ; a \<in> x \<Longrightarrow> P ; \<lbrakk> a \<in> y ; a \<notin> x \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add: un_iff[OF assms], blast)

lemma unCI :
  assumes "x : Set" "y : Set" 
  shows "(a \<notin> y \<Longrightarrow> a \<in> x) \<Longrightarrow> a \<in> x \<union> y"
  by (simp add: un_iff[OF assms], blast)


subsection \<open>Rules for binary intersection\<close>

definition inter :: "['a,'a] \<Rightarrow> 'a" (infixl \<open>\<inter>\<close> 90) where
  "x \<inter> y \<equiv> \<Inter> upair x y"

lemma inter_typ : "(\<inter>) : Set \<rightarrow> Set \<rightarrow> Set"
  unfolding inter_def
  by (rule funI, rule funI, rule Int_set[OF upair_setof])

lemmas inter_set = funE[OF funE[OF inter_typ]]

lemma inter_iff : 
  assumes "x : Set" "y : Set" 
  shows "a \<in> x \<inter> y \<longleftrightarrow> (a \<in> x \<and> a \<in> y)"
  unfolding inter_def 
  by (simp add: Int_iff[OF upair_setof[OF assms]], 
      use upair_iff set_setmem assms in auto)

lemma interI : 
  assumes "x : Set" "y : Set" 
  shows "\<lbrakk> a \<in> x ; a \<in> y \<rbrakk> \<Longrightarrow> a \<in> x \<inter> y"
  by (simp add: inter_iff[OF assms])

lemma interD1 : 
  assumes "x : Set" "y : Set" 
  shows "a \<in> x \<inter> y \<Longrightarrow> a \<in> x" 
  by (simp add: inter_iff assms)  

lemma interD2 :
  assumes "x : Set" "y : Set" 
  shows "a \<in> x \<inter> y \<Longrightarrow> a \<in> y" 
  by (simp add: inter_iff assms)

lemma interE : 
  assumes "x : Set" "y : Set" 
  shows "\<lbrakk> a \<in> x \<inter> y ; \<lbrakk> a \<in> x ; a \<in> y \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add: inter_iff assms)
end

subsection \<open>Binders for union and intersection\<close>

syntax
  "_Union" :: "[pttrn, 'a, 'a] \<Rightarrow> 'a"  (\<open>(3\<Union>_\<in>_./ _)\<close> 10)
  "_Inter" :: "[pttrn, 'a, 'a] \<Rightarrow> 'a"  (\<open>(3\<Inter>_\<in>_./ _)\<close> 10)
translations
  "\<Union>b\<in>x. B" == "CONST Union {B | b \<in> x}"
  "\<Inter>b\<in>x. B" == "CONST Int {B | b \<in> x}"

end