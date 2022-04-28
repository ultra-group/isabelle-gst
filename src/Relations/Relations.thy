theory Relations
  imports "../GST_Features" "../GZF/SetComprehension" "../GZF/SetCombinators"
begin

context BinRel begin

thm mkrel_typ field_typ
thm rel ext field_iff

lemmas mkrel_binrel = funE[OF depfunE[OF depfunE[OF mkrel_typ]]]
lemmas field_set = funE[OF field_typ]

lemma brelmemI1 :
  assumes "r : BinRel" "app r a b"
  shows "a : BinRelMem"
  using assms 
  unfolding BinRelMem_def has_ty_def tex_def by auto
  
lemma brelmemI2 :
  assumes "r : BinRel" "app r a b"
  shows "b : BinRelMem"
  using assms 
  unfolding BinRelMem_def has_ty_def tex_def by auto
  
definition domain :: "'a \<Rightarrow> 'a"
  where "domain r \<equiv> Collect (field r) (\<lambda>a. \<exists>b. app r a b)"

lemma domain_typ : "domain : BinRel \<rightarrow> Set"
  unfolding domain_def by (rule funI[OF collect_set[OF field_set]])

lemma domain_iff : 
  assumes "r : BinRel"
  shows "x \<in> domain r \<longleftrightarrow> (\<exists>y. app r x y)"
  unfolding domain_def collect_iff[OF field_set[OF assms]]
  using field_iff assms by auto

definition range :: "'a \<Rightarrow> 'a"
  where "range r \<equiv> Collect (field r) (\<lambda>b. \<exists>a. app r a b)"

definition converse :: "'a \<Rightarrow> 'a"
  where "converse r \<equiv> mkrel (domain r) (range r) (\<lambda>a b. app r b a)"

definition FuncRel :: "'a \<Rightarrow> bool"
  where "FuncRel \<equiv> BinRel \<triangle> (\<lambda>r. \<forall>a b c. app r a b \<and> app r a c \<longrightarrow> b = c)"

definition FuncRelPred 
  where "FuncRelPred x \<equiv> ReplPred x \<triangle> (\<lambda>P. BinRelPred x (Repl x P) P)"

definition mk_funrel where "mk_funrel x P \<equiv> mkrel x (Repl x P) P"

interpretation Function
  where Function = FuncRel
    and mkfun = mk_funrel
    and dom = domain
    and ran = range
    and FunMem = BinRelMem
    and FunPred = FuncRelPred
    and Function_default = BinRelation_default oops

lemma funrelI : 
  assumes "f : BinRel" "\<forall>a b c. app f a b \<and> app f a c \<longrightarrow> b = c"
  shows "f : FuncRel"
  unfolding FuncRel_def by (rule Soft_Types.intI[OF assms(1)], rule tyI, rule assms(2))

lemma relmem_setmem_subtyp : "BinRelMem << SetMem"
proof (rule subtypI, unfold BinRelMem_def, drule tyE)
  fix b assume "\<exists>r : BinRel. \<exists>c. app r b c \<or> app r c b" 
  then obtain r where "r : BinRel" "\<exists>c. app r b c \<or> app r c b" by auto
  hence "field r : Set" "b \<in> field r" using field_set field_iff by auto
  thus "b : SetMem" by (rule setmemI)
qed

lemmas relmem_setmem = subtypE[OF relmem_setmem_subtyp]

lemma frelpred_replpred :
  assumes "P : FuncRelPred x"
  shows "P : ReplPred x" 
   using assms unfolding FuncRelPred_def 
   by unfold_typs

lemma frelpred_brelpred :
  assumes "P : FuncRelPred x"
  shows "P : BinRelPred x (Repl x P)" 
   using assms unfolding FuncRelPred_def 
   by unfold_typs

lemma mkfun_rel_iff :
  assumes x : "x : Set" and P : "P : FuncRelPred x" 
  shows "\<forall>a b. app (mk_funrel x P) a b \<longleftrightarrow> (a \<in> x \<and> b \<in> Repl x P \<and> P a b)"
proof -
  have "Repl x P : Set" "P : BinRelPred x (Repl x P)"  
    using repl_set[OF x frelpred_replpred[OF P]] frelpred_brelpred[OF P] by auto
  thus "\<forall>a b. app (mk_funrel x P) a b \<longleftrightarrow> (a \<in> x \<and> b \<in> Repl x P \<and> P a b)"
    using rel \<open>x : Set\<close> unfolding mk_funrel_def tall_def by auto
qed

theorem BinRel_Function : 
  "class.Function Set (\<in>) Union Pow \<emptyset> Succ Inf \<R> (\<subseteq>) SetMem SetOf ReplPred 
      app FuncRel mk_funrel domain range BinRelMem FuncRelPred"
proof (unfold_locales)
  show "mk_funrel : (\<Pi> x:Set. FuncRelPred x \<rightarrow> FuncRel)" 
  proof (rule depfunI, rule funI, rule funrelI)
    fix x P assume xp:"x : Set" "P : FuncRelPred x"
    hence "Repl x P : Set" "P : BinRelPred x (Repl x P)"  
      using repl_set[OF xp(1) frelpred_replpred] frelpred_brelpred by auto
    thus br:"mk_funrel x P : BinRel" unfolding mk_funrel_def 
      using mkrel_binrel[OF \<open>x : Set\<close>]  by auto  

    show func:"\<forall>a b c. app (mk_funrel x P) a b \<and> app (mk_funrel x P) a c \<longrightarrow> b = c"
    proof (rule)+
      fix a b c assume 
        "app (mk_funrel x P) a b \<and> app (mk_funrel x P) a c"
      hence "P a b" "P a c" "a \<in> x" "b : BinRelMem" "c : BinRelMem" 
        using mkfun_rel_iff[OF xp] brelmemI1[OF br] brelmemI2[OF br]  by auto
      moreover hence "b : SetMem" "c : SetMem"
        using relmem_setmem by auto
      ultimately show "b = c" 
        using frelpred_replpred[OF \<open>P : FuncRelPred x\<close>]
        unfolding ReplPred_def has_ty_def tuniq_def Uniq_def by auto
    qed
  qed

  show "domain : FuncRel \<rightarrow> Set" unfolding domain_def 
  proof (rule funI, rule collect_set)
    fix f assume "f : FuncRel" 
    hence "f : BinRel" unfolding FuncRel_def by (rule intE1)
    thus "field f : Set" by (rule field_set)
  qed

  show "\<forall>s : Set. \<forall>P : FunPred s. \<forall>x y. app (mk_funrel s P) x y = (x \<in> s \<and> P x y)"
  proof (rule, rule, rule, rule)
    fix s P x y assume sp: "s : Set" "P : FunPred s" 
    show "app (mk_funrel s P) x y = (x \<in> s \<and> P x y)" 
    proof
      assume "app (mk_funrel s P) x y"
      thus "x \<in> s \<and> P x y" using mkfun_rel_iff[OF sp] by auto
    next
      assume "x \<in> s \<and> P x y"
      moreover hence "y \<in> Repl s P" 
        using replaceI[OF \<open>s : Set\<close> funpred_replpred[OF \<open>P : FunPred s\<close>]] by auto
      ultimately show "app (mk_funrel s P) x y" using mkfun_rel_iff[OF sp] by auto
    qed
  qed

  show "\<forall>f : FuncRel. \<forall>x y z. app f x y \<and> app f x z \<longrightarrow> y = z"
    by (rule, unfold FuncRel_def, drule tyE[OF intE2], auto)

  show "\<forall>f : FuncRel. \<forall>g : FuncRel. (\<forall>x y. app f x y = app g x y) \<longrightarrow> f = g"
  proof (rule)+
    fix f g assume "f : FuncRel" "g : FuncRel"
    hence "f : BinRel" "g : BinRel" unfolding FuncRel_def by (auto elim: intE1)
    thus "\<forall>x y. app f x y = app g x y \<Longrightarrow> f = g" using ext by auto
  qed

  show "\<forall>f : FuncRel. \<forall>x. (x \<in> domain f) = (\<exists>y. app f x y)"
  proof (rule, rule)
    fix f x assume "f : FuncRel"
    hence "f : BinRel" unfolding FuncRel_def by (auto elim: intE1)
    show "(x \<in> domain f) = (\<exists>y. app f x y)" unfolding domain_def collect_iff[OF field_set[OF \<open>f : BinRel\<close>]]
      using field_iff \<open>f : BinRel\<close> by auto
  qed
qed 

(*Proving that any functional relations can interpret the Function interface!*)
 sorry

end 
end