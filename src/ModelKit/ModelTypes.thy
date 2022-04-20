theory ModelTypes 
  imports ModelBase
begin

section \<open>High-level reasoning about GST models\<close>

context ModelBase 
begin

subsection \<open> M - The soft type of all domain objects in a model\<close>

definition inModel :: \<open>'a \<Rightarrow> bool\<close> (\<open>M\<close>)
  where [typdef] : \<open>inModel \<equiv> (\<lambda>b. \<exists>i : Ord. b \<in> Tier i)\<close>

lemma mI :
  assumes i : "i : Ord" 
      and b : "b \<in> Tier i"
    shows "b : M"
  unfolding inModel_def 
  by (rule tyI, rule texI, rule i, rule b)

lemma mE :
  assumes b : "b : M" 
  obtains i 
    where "i : Ord" "b \<in> Tier i"
  using b 
  unfolding inModel_def tex_def has_ty_def
  by auto

lemma m_induct :
  assumes x : \<open>x : M\<close> 
      and zero : \<open>x \<in> Tier 0 \<Longrightarrow> P\<close>
      and succ : \<open>\<And>j. j : Ord \<Longrightarrow> (x \<in> Tier j \<Longrightarrow> P) \<Longrightarrow> x \<in> Tier (succ j) \<Longrightarrow> P\<close>
      and lim  : \<open>\<And>\<mu>. \<mu> : Limit \<Longrightarrow> (\<And>j. j : Ord \<Longrightarrow> j<\<mu> \<Longrightarrow> x \<in> Tier j \<Longrightarrow> P) \<Longrightarrow> x \<in> Tier \<mu>  \<Longrightarrow> P\<close>
   shows "P"
proof (rule mE[OF x])   
   fix i assume "i : Ord" "x \<in> Tier i" 
   thus ?thesis 
    by (induct rule: trans_induct3, 
        use zero succ lim in auto)
qed

theorem m_depsum : 
  "x : M \<Longrightarrow> x : (\<Sigma> i : Tag. \<alpha> i)"  
  using tier_mem_depsum by (auto elim: mE)

lemmas mtagE = depsumE[OF m_depsum]
lemmas mtagD = depsumD[OF m_depsum]
lemmas mtagD_pair = depsumD_pair[OF m_depsum]
lemmas m_pair = mtagD(1)
lemmas mpair_pair = mtagD_pair(1)
lemmas mpair_inject = pair_inject[OF mpair_pair mpair_pair]

lemma mpair_snd_eq : 
  "<i,x'> : M \<Longrightarrow> \<pi> <i,x'> = x'"
  using snd_eq[OF m_pair] by auto

theorem m_cases_pair : 
  assumes b : "<i,b'> : M"
  obtains 
    (zero) "b' \<in> Variants i 0 \<emptyset>"
  | (succ) j where "j : Ord" "b' \<in> Variants i (succ j) (Tier j \<ominus> i)"
  | (limit) \<mu> where "\<mu> : Limit" "b' \<in> Variants i \<mu> (\<lambda>j<\<mu>. Tier j \<ominus> i)"      
proof (induct rule: m_induct[OF b])
  case 1
  hence "b' \<in> Variants i 0 \<emptyset>" using tier0D(2) by auto
  then show ?case ..
next
  case IH_succ: (2 j)
  show ?case 
  proof (rule tier_succE_pair[OF IH_succ(1,3)])
    assume "<i,b'> \<in> Tier j"
    thus ?case using IH_succ(2)[OF _ IH_succ(4,5,6)] by auto
  next
    assume "b' \<in> Variants i (succ j) (Tier j \<ominus> i)"
    thus ?case using IH_succ(5)[OF \<open>j : Ord\<close>] by auto
  qed
next
  case IH_lim:(3 \<mu>)
  show ?case 
  proof (rule tier_limE_pair[OF IH_lim(1,3)])
    fix j assume "j : Ord" "j < \<mu>" "<i,b'> \<in> Tier j"
    thus ?case using IH_lim(2)[OF _ _ _] IH_lim(4,5,6) by auto
  next
    assume "b' \<in> Variants i \<mu> (\<lambda>j < \<mu>. Tier j \<ominus> i)"
    thus ?case using IH_lim(6)[OF \<open>\<mu> : Limit\<close>] by auto
  qed
qed

lemmas tag_set_pair = pair_pair[OF ord_pmem[OF tag_ord] smem_pmem[OF set_setmem]]
end

class ModelBase' = ModelBase +
  fixes mdefault :: \<open>'a\<close>
  assumes mdefault_m : "mdefault : M"

context ModelBase' begin

subsection \<open>Binders restricted to the model\<close>

(*TODO: a 'Binder class parameterised by a restriction,
        so we can autogenerate definitions/lemmas from a \<forall> quantifier *)
definition mall :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> (binder \<open>m\<forall>\<close> 10)
  where "m\<forall>x. P x \<equiv> \<forall>x : M. P x"

definition mex :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> (binder \<open>m\<exists>\<close> 10)
  where "m\<exists>x. P x \<equiv> \<exists>x : M. P x"

definition mex1 :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> (binder \<open>m\<exists>!\<close> 10)
  where "m\<exists>!x. P x \<equiv> \<exists>!x : M. P x"

definition muniq :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> (binder \<open>m\<exists>\<^sub>\<le>\<^sub>1\<close> 10)
  where "m\<exists>\<^sub>\<le>\<^sub>1x. P x \<equiv> \<exists>\<^sub>\<le>\<^sub>1x : M. P x"

definition mdefdes :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where "mdefdes P d \<equiv> \<iota> x : M. P x else d"

lemma mallI [intro] : 
  assumes "\<And>x. x : M \<Longrightarrow> P x"
  shows "m\<forall>x. P x"
  unfolding mall_def 
  using tallI assms by auto 

lemma mexI [intro] : 
  assumes "x : M" "P x"
  shows "m\<exists>x. P x"
  unfolding mex_def 
  using texI assms by auto 

subsection \<open>Type restricted model binders\<close>

definition mtall :: \<open>['a \<Rightarrow> bool, 'a \<Rightarrow> bool] \<Rightarrow> bool\<close>
  where "mtall P Q \<equiv> m\<forall>x. x : P \<longrightarrow> Q x"

definition mtex :: \<open>['a \<Rightarrow> bool, 'a \<Rightarrow> bool] \<Rightarrow> bool\<close>
  where "mtex P Q \<equiv> m\<exists>x. x : P \<and> Q x"

definition mtex1 :: \<open>['a \<Rightarrow> bool, 'a \<Rightarrow> bool] \<Rightarrow> bool\<close>
  where "mtex1 P Q \<equiv> m\<exists>!x. x : P \<and> Q x"

definition mtuniq :: \<open>['a \<Rightarrow> bool, 'a \<Rightarrow> bool] \<Rightarrow> bool\<close>
  where "mtuniq P Q \<equiv> m\<exists>\<^sub>\<le>\<^sub>1 x. x : P \<and> Q x"

definition mtdefdes :: \<open>['a \<Rightarrow> bool, 'a \<Rightarrow> bool, 'a] \<Rightarrow> 'a\<close>
  where "mtdefdes P Q d \<equiv> mdefdes (\<lambda>x. x : P \<and> Q x) d"

subsection \<open>Coercing into the model and LimFun\<close>

definition forceM :: \<open>'a \<Rightarrow> 'a\<close>
  where "forceM b \<equiv> if b : M then b else mdefault"

lemma forceM_m : "forceM b : M"
  unfolding forceM_def
  using mdefault_m by auto
  
lemma forceM_eq : 
  assumes "b : M"
  shows "forceM b = b"
  unfolding forceM_def
  using assms by auto


definition LimFun
  where "LimFun \<equiv> (M \<rightarrow> (M \<rightarrow> M) \<rightarrow> M) \<triangle> (\<lambda>G. \<forall>u : M. \<forall>f : M \<rightarrow> M. G u f = G u (\<lambda>j. f (forceM j)))"

lemma limfunD1 : 
  assumes "G : LimFun"
  shows "G : M \<rightarrow> (M \<rightarrow> M) \<rightarrow> M"
  using assms
  unfolding LimFun_def
  by (rule intE1)

lemma limfunD2 : 
  assumes "G : LimFun" "u : M" "f : M \<rightarrow> M"
  shows "G u f = G u (\<lambda>j. f (forceM j))"
  using assms
  unfolding LimFun_def tall_def has_ty_def inter_ty_def
  by (auto)

subsection \<open>Model Rank operator\<close>

definition mrank where "mrank x \<equiv> (least \<beta>. x \<in> Tier \<beta>)"

lemma mrank_tier : 
  assumes "x : M" 
  shows "x \<in> Tier (mrank x)"
proof (rule mE[OF assms])
  fix i assume "i : Ord" "x \<in> Tier i"
  thus "x \<in> Tier (mrank x)" unfolding mrank_def by (rule leastI)
qed

lemma mrank_eq : 
  assumes "j : Ord" 
  shows "x \<in> Tier j \<Longrightarrow> (\<And>i. i < j \<Longrightarrow> x \<notin> Tier i) \<Longrightarrow> mrank x = j"
  unfolding mrank_def using least_eq[OF assms] by auto

lemma mrank_ord : 
  assumes x : "x : M"
  shows "mrank x : Ord" 
  unfolding mrank_def 
  using least_ord mE[OF x] by metis

end

subsection \<open>Syntax for type-restricted model quantifiers\<close>
(*Equivalent to soft-type restriction on quantifiers.
  Only purpose of this notation is for less keystrokes.*)
syntax
  "_mtall"  :: "[pttrn, 'a \<Rightarrow> bool, bool] \<Rightarrow> bool"  ("(3m\<forall>_ : _./ _)" 10)
  "_mtex"   :: "[pttrn, 'a \<Rightarrow> bool, bool] \<Rightarrow> bool"  ("(3m\<exists>_ : _./ _)" 10)
  "_mtex1"  :: "[pttrn, 'a \<Rightarrow> bool, bool] \<Rightarrow> bool"  ("(3m\<exists>!_ : _./ _)" 10)
  "_mtuniq" :: "[pttrn, 'a \<Rightarrow> bool, bool] \<Rightarrow> bool"  ("(3m\<exists>\<^sub>\<le>\<^sub>1_ : _./ _)" 10)
  "_mtdefdes" :: "[pttrn, 'a \<Rightarrow> bool, 'a \<Rightarrow> bool, 'a] \<Rightarrow> 'a"  
    ("(4m\<iota> _ : _./ _ else _)" 10)
translations
  "m\<forall>x : P. Q"  \<rightleftharpoons> "CONST mtall P (\<lambda>x. Q)"
  "m\<exists>x : P. Q"  \<rightleftharpoons> "CONST mtex P (\<lambda>x. Q)"
  "m\<exists>!x : P. Q" \<rightleftharpoons> "CONST mtex1 P (\<lambda>x. Q)"
  "m\<exists>\<^sub>\<le>\<^sub>1x : P. Q" \<rightleftharpoons> "CONST mtuniq P (\<lambda>x. Q)"
  "m\<iota> x : P. Q else d" \<rightleftharpoons> "CONST mtdefdes P (\<lambda>x. Q) d"

end