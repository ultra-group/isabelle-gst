theory Relations
  imports GST_Features "GZF/SetComprehension" "GZF/SetCombinators"
begin

context Relation begin

thm rel_typ field_typ
thm rel ext field_iff

lemmas mkrel_binrel = funE[OF depfunE[OF depfunE[OF rel_typ]]]
lemmas field_set = funE[OF field_typ]

definition domain :: "'d \<Rightarrow> 'd"
  where "domain r \<equiv> Collect (field r) (\<lambda>a. \<exists>b. app r a b)"

lemma domain_typ : "domain : BinRelation \<rightarrow> Set"
  unfolding domain_def by (rule funI[OF collect_set[OF field_set]])

lemma domain_iff : 
  assumes "r : BinRelation"
  shows "x \<in> domain r \<longleftrightarrow> (\<exists>y. app r x y)"
  unfolding domain_def collect_iff[OF field_set[OF assms]]
  using field_iff assms by auto

definition range :: "'d \<Rightarrow> 'd"
  where "range r \<equiv> Collect (field r) (\<lambda>b. \<exists>a. app r a b)"

definition converse :: "'d \<Rightarrow> 'd"
  where "converse r \<equiv> mkrel (domain r) (range r) (\<lambda>a b. app r b a)"

definition FuncRel :: "'d \<Rightarrow> bool"
  where "FuncRel \<equiv> BinRelation \<bar> (\<lambda>r. \<forall>a b c. app r a b \<and> app r a c \<longrightarrow> b = c)"

lemma funrelI : 
  assumes "f : BinRelation" "\<forall>a b c. app f a b \<and> app f a c \<longrightarrow> b = c"
  shows "f : FuncRel"
  unfolding FuncRel_def by (rule Soft_Types.intI[OF assms(1)], rule tyI, rule assms(2))

definition mk_funrel where "mk_funrel x P \<equiv> mkrel x (Repl x P) P"

lemma relmem_setmem_subtyp : "BinRelMem << SetMem"
proof (rule subtypI, unfold BinRelMem_def, drule tyE)
  fix b assume "\<exists>r : BinRelation. \<exists>c. app r b c \<or> app r c b" 
  then obtain r where "r : BinRelation" "\<exists>c. app r b c \<or> app r c b" by auto
  hence "field r : Set" "b \<in> field r" using field_set field_iff by auto
  thus "b : SetMem" by (rule setmemI)
qed

lemmas relmem_setmem = subtypE[OF relmem_setmem_subtyp]

interpretation Function_sig
  where Function = FuncRel
    and app = app
    and mkfun = mk_funrel
    and dom = domain
  by (unfold_locales)

lemma funmem_relmem_subtyp : "FunMem << BinRelMem"
proof (rule subtypI, unfold FunMem_def BinRelMem_def, drule tyE, rule tyI)
  fix b assume "\<exists>r : FuncRel. \<exists>c. app r b c \<or> app r c b" 
  then obtain r where "r : FuncRel" "\<exists>c. app r b c \<or> app r c b"  by auto
  moreover hence "r : BinRelation" unfolding FuncRel_def using intE1 by auto
  ultimately show "\<exists>r : BinRelation. \<exists>c. app r b c \<or> app r c b" by auto
qed

lemmas funmem_relmem = subtypE[OF funmem_relmem_subtyp]
lemmas funmem_setmem = subtypE[OF subtyp_trans[OF funmem_relmem_subtyp relmem_setmem_subtyp]]

lemma funpred_replpred :
  assumes "P : FunPred x"
  shows "P : ReplPred x"
proof (unfold ReplPred_def tuniq_def, rule tyI, rule, rule, rule)
  fix a assume "a \<in> x" 
  thus "\<exists>\<^sub>\<le>\<^sub>1 x. x : SetMem \<and> P a x" 
    using \<open>P : FunPred x\<close> unfolding Uniq_def FunPred_def has_ty_def by auto
  show "\<forall>b. P a b \<longrightarrow> b : SetMem" 
  proof (rule, rule, rule funmem_setmem)
    fix b assume "P a b"
    thus "b : FunMem" using \<open>a \<in> x\<close> \<open>P : FunPred x\<close> unfolding FunPred_def has_ty_def by auto
  qed
qed

lemma funpred_repl_set : 
  assumes "x : Set" "P : FunPred x" 
  shows "Repl x P : Set"
  using repl_set[OF \<open>x : Set\<close> funpred_replpred[OF \<open>P : FunPred x\<close>]] by auto
thm FunPred_def

lemma funpred_relpred :
  assumes "x : Set" "P : FunPred x" 
  shows "P : BinRelPred x (Repl x P)" unfolding BinRelPred_def
proof (rule tyI, rule, rule, rule, rule, rule, rule)
  fix a b assume "a \<in> x" "b \<in> Repl x P" "P a b"
  hence "a : FunMem" "b : FunMem" using \<open>P : FunPred x\<close> unfolding FunPred_def has_ty_def by auto
  thus "a : BinRelMem" "b : BinRelMem" using funmem_relmem by auto
qed

lemma mkfun_rel_iff :
  assumes "x : Set" "P : FunPred x" 
  shows "\<forall>a b. app (mk_funrel x P) a b \<longleftrightarrow> (a \<in> x \<and> b \<in> Repl x P \<and> P a b)"
proof -
  have "Repl x P : Set" "P : BinRelPred x (Repl x P)"  
    using repl_set[OF _ funpred_replpred] funpred_relpred assms by auto
  thus "\<forall>a b. app (mk_funrel x P) a b \<longleftrightarrow> (a \<in> x \<and> b \<in> Repl x P \<and> P a b)"
    using rel \<open>x : Set\<close> unfolding mk_funrel_def tall_def by auto
qed

(*If we want to use interpretations in other interfaces, we need to prove locale theorems
  rather than form interpretations.
    For example, the Relation interface can be used to interpret the Function interface.
    The SetRel interface can interpret the Relation interface, and should therefore
    also be able to interpret the Function interface.
    - Suppose we do 'interpretation Function where ...' in the context of the Relation interface,
      and we then interpret the Relation interface in the SetRel context.
    - The constants, definitions and theorems of the Function interface are NOT available
      in this context. Interpreting the Function interface here is hard, 
      because we the 'interpretation' command leaves no trace of the fact that the Function
      interface can be interpreted in the Relation interface.
    - However, if we prove the "locale theorem":
        "Function Set Mem Emp Union Subset Pow Succ Inf Repl FuncRel app mk_funrel domain"
      in the Relation context, then when after interpreting the Relation interface in the SetRel context,
      we have this theorem ready for us to automatically interpret the Function interface.
    - Unfortunately, this requires us to do the work of explicitly filling in the parameters of
      the locale, usually performed by the Isar locale interpretation machinery. 
      This list also contains the parameters of all of the interfaces dependencies.
    - It should be relatively easy to write code to automate the construction of the 
      statement of the "locale theorem", and also write code that forms the interpretation of
      interfaces when fed these theorems. *)

(*Proving that any functional relations can interpret the Function interface!*)
lemma Function_interpretation: "Function Set Mem Emp Union Subset Pow Succ Inf Repl FuncRel app mk_funrel domain"
proof (unfold_locales)
  show "mk_funrel : (\<Pi> x:Set. FunPred x \<rightarrow> FuncRel)" 
  proof (rule depfunI, rule funI, rule funrelI)
    fix x P assume xp:"x : Set" "P : FunPred x"
    hence "Repl x P : Set" "P : BinRelPred x (Repl x P)"  
      using repl_set[OF _ funpred_replpred] funpred_relpred by auto
    thus "mk_funrel x P : BinRelation" unfolding mk_funrel_def 
      using mkrel_binrel[OF \<open>x : Set\<close>]  by auto  

    show func:"\<forall>a b c. app (mk_funrel x P) a b \<and> app (mk_funrel x P) a c \<longrightarrow> b = c"
    proof (rule)+
      fix a b c assume "app (mk_funrel x P) a b \<and> app (mk_funrel x P) a c" 
      hence "P a b" "P a c" "a \<in> x" using mkfun_rel_iff[OF xp] by auto
      thus "b = c" using \<open>P : FunPred x\<close> unfolding FunPred_def has_ty_def by auto
    qed
  qed

  show "domain : FuncRel \<rightarrow> Set" unfolding domain_def 
  proof (rule funI, rule collect_set)
    fix f assume "f : FuncRel" 
    hence "f : BinRelation" unfolding FuncRel_def by (rule intE1)
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
    hence "f : BinRelation" "g : BinRelation" unfolding FuncRel_def by (auto elim: intE1)
    thus "\<forall>x y. app f x y = app g x y \<Longrightarrow> f = g" using ext by auto
  qed

  show "\<forall>f : FuncRel. \<forall>x. (x \<in> domain f) = (\<exists>y. app f x y)"
  proof (rule, rule)
    fix f x assume "f : FuncRel"
    hence "f : BinRelation" unfolding FuncRel_def by (auto elim: intE1)
    show "(x \<in> domain f) = (\<exists>y. app f x y)" unfolding domain_def collect_iff[OF field_set[OF \<open>f : BinRelation\<close>]]
      using field_iff \<open>f : BinRelation\<close> by auto
  qed
qed

end 
end