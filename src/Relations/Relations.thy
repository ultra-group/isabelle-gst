theory Relations
  imports "../GST_Features" "../GZF/SetComprehension" "../GZF/SetCombinators"
begin

context BinRel begin

thm mkrel_typ field_typ
thm rel ext field_iff

lemmas mkrel_binrel = funE[OF funE[OF funE[OF mkrel_typ]] anyI]
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

subsection \<open>Relation space of a set\<close>

lemmas relspace_setof = funE[OF relspace_typ]
lemmas relspace_mem = setof_mem[OF relspace_setof]


lemma relspace_iff : 
  assumes "x : Set" "r : BinRel"
    shows "r \<in> \<RR> x \<longleftrightarrow> field r \<subseteq> x"
    using relspace_ax assms by auto

lemmas relspaceI = iffD2[OF relspace_iff]
lemma relspaceD : 
  assumes "x : Set" "r \<in> \<RR> x"
    shows "field r \<subseteq> x"
  using iffD1[OF relspace_iff[OF _ relspace_mem]] assms by auto

subsection \<open>Interpreting function feature with binary relations\<close>

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

lemma range_iff : 
  assumes "r : BinRel"
  shows "y \<in> range r \<longleftrightarrow> (\<exists>x. app r x y)"
  unfolding range_def collect_iff[OF field_set[OF assms]]
  using field_iff assms by auto

lemma field_disj :
  assumes r : "r : BinRel" and b : "b \<in> field r"
  obtains (dom) "b \<in> domain r"
        | (ran) "b \<in> range r"
  using field_iff r b 
  unfolding tall_def domain_iff[OF r] range_iff[OF r] 
  by metis

definition converse :: "'a \<Rightarrow> 'a"
  where "converse r \<equiv> mkrel (domain r) (range r) (\<lambda>a b. app r b a)"

definition FuncRel :: "'a \<Rightarrow> bool"
  where "FuncRel \<equiv> BinRel \<triangle> (\<lambda>r. \<forall>a b c. app r a b \<and> app r a c \<longrightarrow> b = c)"

definition FuncRelPred 
  where "FuncRelPred s P \<equiv> \<forall>x : BinRelMem. x \<in> s \<longrightarrow> (\<exists>\<^sub>\<le>\<^sub>1 y : BinRelMem. P x y)"

definition mk_funrel 
  where "mk_funrel x P \<equiv> 
    mkrel {a \<in> x | a : BinRelMem} (Repl x (\<lambda>a b. a : BinRelMem \<and> b : BinRelMem \<and> P a b)) P"

definition mk_funspace :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where "mk_funspace x y \<equiv> 
    {f \<in> \<RR> (x \<union> y) | f : FuncRel \<and> domain f \<subseteq> x \<and> range f \<subseteq> y}"

interpretation Function
  where Function = FuncRel
    and mkfun = mk_funrel
    and dom = domain
    and ran = range
    and FunMem = BinRelMem
    and FunPred = FuncRelPred
    and funspace = mk_funspace
    and Function_default = BinRelation_default oops

lemma frel_brel :
  assumes "f : FuncRel"
  shows "f : BinRel"
  using assms unfolding FuncRel_def
  by (unfold_typs)

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

(* 
lemma frelpred_brelpred :
  assumes "P : FuncRelPred x"
  shows "P : BinRelPred x (Repl x P)" 
   using assms unfolding FuncRelPred_def *) 
   (* by unfold_typs *)

lemma frelpred_replpred : 
  assumes "P : FuncRelPred x"
  shows "(\<lambda>a b. a : BinRelMem \<and> b : BinRelMem \<and> P a b) : ReplPred x"
proof (rule replpredI, unfold tuniq_def Uniq_def, auto)
  fix a b b' assume
    "a \<in> x" "a : BinRelMem" "b : BinRelMem" "b' : BinRelMem" "P a b" "P a b'"
  thus "b = b'"  
    using assms 
    unfolding FuncRelPred_def has_ty_def tall_def tuniq_def Uniq_def
    by auto
qed

lemma mk_funrel_binrel : 
  assumes x : "x : Set" and P : "P : FuncRelPred x"
  shows "mk_funrel x P : BinRel"
  unfolding mk_funrel_def
  using mkrel_binrel[OF collect_set[OF x] repl_set[OF x frelpred_replpred[OF P]]] . 

lemma mkfun_rel_iff :
  assumes x : "x : Set" and P : "P : FuncRelPred x" 
  shows "\<forall>a b. app (mk_funrel x P) a b \<longleftrightarrow> 
    (a \<in> x \<and> P a b \<and> a : BinRelMem \<and> b : BinRelMem)"
proof -
  have r_set:"Repl x (\<lambda>a b. a : BinRelMem \<and> b : BinRelMem \<and> P a b) : Set"  
    using repl_set[OF x frelpred_replpred[OF P]] by auto
  show "\<forall>a b. app (mk_funrel x P) a b 
    \<longleftrightarrow> (a \<in> x \<and> P a b \<and> a : BinRelMem \<and> b : BinRelMem)"
  proof (auto)
    fix a b assume "app (mk_funrel x P) a b"
    hence 
      "a \<in> {a' \<in> x | a' : BinRelMem}" 
      "b \<in> Repl x (\<lambda>a b. a : BinRelMem \<and> b : BinRelMem \<and> P a b)"
      "P a b" "a : BinRelMem" "b : BinRelMem"
      using rel collect_set[OF x, of \<open>\<lambda>a'. a' : BinRelMem\<close>] r_set
      unfolding mk_funrel_def by auto
    thus "a \<in> x" "P a b" "a : BinRelMem" "b : BinRelMem"
       using collectE[OF x] by auto
  next
    fix a b assume 
      "a \<in> x" "P a b" "a : BinRelMem" "b : BinRelMem"
    moreover hence 
      "a \<in> {a' \<in> x | a' : BinRelMem}" 
      "b \<in> Repl x (\<lambda>a b. a : BinRelMem \<and> b : BinRelMem \<and> P a b)"
      using collectI[OF x] replaceI[OF x frelpred_replpred[OF P] _ _ relmem_setmem] 
      by auto
    ultimately show 
      "app (mk_funrel x P) a b"
      unfolding mk_funrel_def
      using rel collect_set[OF x, of \<open>\<lambda>a'. a' : BinRelMem\<close>] r_set by auto
  qed
qed

theorem BinRel_Function : 
  "class.Function_axioms Set (\<in>) (\<subseteq>) SetOf app FuncRel mk_funrel domain range mk_funspace BinRelMem FuncRelPred"
proof (unfold_locales)
  show mk_funrel_typ : "mk_funrel : (\<Pi> x:Set. FuncRelPred x \<rightarrow> FuncRel)" 
  proof (rule depfunI, rule funI, rule funrelI, simp only: mk_funrel_binrel)
    fix x P assume xp:"x : Set" "P : FuncRelPred x"
    show func:"\<forall>a b c. app (mk_funrel x P) a b \<and> app (mk_funrel x P) a c \<longrightarrow> b = c"
    proof (rule)+
      fix a b c assume 
        "app (mk_funrel x P) a b \<and> app (mk_funrel x P) a c"
      hence "P a b" "P a c" "a \<in> x" "a : BinRelMem" "b : BinRelMem" "c : BinRelMem" 
        using mkfun_rel_iff[OF xp] by auto
      moreover hence "b : SetMem" "c : SetMem"
        using relmem_setmem by auto
      ultimately show "b = c" 
        using frelpred_replpred[OF \<open>P : FuncRelPred x\<close>]
        unfolding ReplPred_def has_ty_def tuniq_def Uniq_def by auto 
    qed
  qed

  show "domain : FuncRel \<rightarrow> Set" 
    unfolding domain_def 
  proof (rule funI, rule collect_set)
    fix f assume "f : FuncRel" 
    hence "f : BinRel" unfolding FuncRel_def by (rule intE1)
    thus "field f : Set" by (rule field_set)
  qed

  show "range : FuncRel \<rightarrow> Set" 
    unfolding range_def 
  proof (rule funI, rule collect_set)
    fix f assume "f : FuncRel" 
    hence "f : BinRel" unfolding FuncRel_def by (rule intE1)
    thus "field f : Set" by (rule field_set)
  qed

  show "mk_funspace : Set \<rightarrow> Set \<rightarrow> SetOf FuncRel"
  proof (rule funI, rule funI, rule setofI)
    fix x y assume 
      x : "x : Set" and y : "y : Set"
    hence "\<RR> (x \<union> y) : SetOf BinRel"  
      using relspace_setof[OF un_set] by auto
    moreover thus "mk_funspace x y : Set" 
      unfolding mk_funspace_def
      using collect_set[OF setof_set] by auto
    fix b assume "b \<in> mk_funspace x y"
    ultimately show "b : FuncRel"
      unfolding mk_funspace_def
      using collectD2[OF setof_set] by auto
   qed

  show "\<forall>s : Set. \<forall>P : FuncRelPred s. 
    \<forall>x y. app (mk_funrel s P) x y = (x \<in> s \<and> P x y \<and> x : BinRelMem \<and> y : BinRelMem)"
    using mkfun_rel_iff by auto

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
    show "(x \<in> domain f) = (\<exists>y. app f x y)" 
      unfolding domain_def collect_iff[OF field_set[OF \<open>f : BinRel\<close>]]
      using field_iff \<open>f : BinRel\<close> by auto
  qed

  show "\<forall>f : FuncRel. \<forall>y. (y \<in> range f) = (\<exists>x. app f x y)"
  proof (rule, rule)
    fix f y assume "f : FuncRel"
    hence "f : BinRel" unfolding FuncRel_def by (auto elim: intE1)
    show "(y \<in> range f) = (\<exists>x. app f x y)" 
      unfolding range_def collect_iff[OF field_set[OF \<open>f : BinRel\<close>]]
      using field_iff \<open>f : BinRel\<close> by auto
  qed

  show "\<forall>b. BinRelMem b = app_mem FuncRel b"
  proof -
    have "\<forall>b. b : BinRelMem \<longleftrightarrow> b : app_mem FuncRel"
    proof (rule)+
      fix b assume b : "b : BinRelMem"
      hence b_smem : "b : SetMem" 
        using relmem_setmem by auto
      let ?P = "\<lambda>c d. c = b \<and> d = b"
      have P : "?P : FuncRelPred {b}"
        unfolding FuncRelPred_def tall_def tuniq_def Uniq_def
        by (rule tyI, auto)
      
      let ?f = "mk_funrel {b} ?P"
      have "?f : FuncRel" 
        using funE[OF depfunE[OF mk_funrel_typ 
              sng_set[OF b_smem]] P] .
      moreover hence "app ?f b b"
        using mkfun_rel_iff[OF sng_set[OF b_smem] P] sngI[OF b_smem] b by auto
      ultimately show "b : app_mem FuncRel"
        unfolding tex_def has_ty_def by auto
    next
      fix b assume "b : app_mem FuncRel"
      thus "b : BinRelMem"
        unfolding BinRelMem_def tex_def FuncRel_def inter_ty_def has_ty_def 
        by auto
    qed
    thus ?thesis 
      unfolding has_ty_def 
      by presburger
  qed

  show "\<forall>x P. FuncRelPred x P = (\<forall>b : BinRelMem. b \<in> x \<longrightarrow> (\<exists>\<^sub>\<le>\<^sub>1 c : BinRelMem. P b c))"
    unfolding FuncRelPred_def by auto

  show "\<forall>x : Set. \<forall>y : Set. \<forall>f : FuncRel.
          (f \<in> mk_funspace x y) = (domain f \<subseteq> x \<and> range f \<subseteq> y)"
  proof (rule, rule, rule)
    fix x y f assume 
      x : "x : Set" and y : "y : Set" and 
      f : "f : FuncRel"
    hence f' : "f : BinRel" and R:"\<RR> (x \<union> y) : Set"
      using frel_brel setof_set[OF relspace_setof[OF un_set]] by auto
    show "f \<in> mk_funspace x y \<longleftrightarrow> domain f \<subseteq> x \<and> range f \<subseteq> y"
    proof
      assume "f \<in> mk_funspace x y"
      thus "domain f \<subseteq> x \<and> range f \<subseteq> y"
        unfolding mk_funspace_def
        using collectD2[OF R] by auto
    next
      assume xy:"domain f \<subseteq> x \<and> range f \<subseteq> y" 
      have "field f \<subseteq> x \<union> y" 
      by (rule, unfold un_iff[OF x y], 
          erule field_disj[OF f'], use xy in auto)
      hence "f \<in> \<RR> (x \<union> y)"
        using relspaceI[OF un_set[OF x y] f'] by auto
      thus "f \<in> mk_funspace x y"
        unfolding mk_funspace_def
        using collectI[OF R] f xy by auto
    qed
  qed        
qed

end 
end