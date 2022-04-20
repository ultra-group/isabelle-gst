theory GZF_Base
  imports BoundedQuants
begin

syntax
  "_Repl"  :: "[pttrn, pttrn, 'a, bool] => 'a"  (\<open>(1{_ |/\<exists>_ \<in> _. _})\<close>)
translations
  "{c | \<exists>b\<in>x. P }" \<rightleftharpoons> "CONST Repl x (\<lambda>b c. P)"
context GZF begin

thm Union_typ Pow_typ Inf_typ Repl_typ

lemma setof_subset : 
  assumes "x : Set" "y : SetOf \<alpha>" "x \<subseteq> y"
    shows "x : SetOf \<alpha>"
proof (rule setofI[OF \<open>x : Set\<close>])
  fix b assume "b \<in> x"
  hence "b \<in> y" by (rule subsetD[OF \<open>x \<subseteq> y\<close>])
  thus "b : \<alpha>" by (rule setof_mem[OF \<open>y : SetOf \<alpha>\<close>])
qed

declare subsetD [trans] rev_subsetD [trans] subset_trans [trans]

subsection \<open>Equality of sets\<close>
lemma equality_iff : 
  assumes "x : Set" "y : Set"
    shows "x = y \<longleftrightarrow> (\<forall>b. b \<in> x \<longleftrightarrow> b \<in> y)"
  using assms ext 
  by auto

lemma subset_equal : 
  assumes "x : Set" "y : Set" 
    shows "x = y \<longleftrightarrow> x \<subseteq> y \<and> y \<subseteq> x"
  using equality_iff[OF assms] subset_iff assms 
  by auto

(*Lemmas taken from ZF/ZF_Base:*)
lemma equalityI : 
  assumes "x : Set" "y : Set" 
    shows "\<lbrakk> x \<subseteq> y;  y \<subseteq> x \<rbrakk> \<Longrightarrow> x = y"
  using subset_equal[OF assms] 
  by auto
(*WAS: by (rule extension [THEN iffD2], rule conjI) *)

(*Added assumptions: \<open>A : Set\<close> \<open>B : Set\<close>*)
lemma equality_iffI: 
  assumes "x : Set" "y : Set" 
    shows "(\<And>b. b \<in> x \<longleftrightarrow> b \<in> y) \<Longrightarrow> x = y"
  using assms equalityI subsetI 
  by blast
(*WAS: by (rule equalityI, blast+)*)

(*Replaced \<open>extension\<close> with \<open>subset_equal\<close>*)
lemmas equalityD1 = subset_equal [THEN iffD1, THEN conjunct1]
lemmas equalityD2 = subset_equal [THEN iffD1, THEN conjunct2]

(*Added assumptions: \<open>A : Set\<close> \<open>B : Set\<close>*)
lemma equalityE: 
  assumes "A : Set"  
    shows "[| A = B;  [| A \<subseteq> B; B \<subseteq> A |] ==> P |]  ==>  P"
  by (use equalityD1[OF assms] equalityD2[OF assms] in auto)
(*WAS: by (blast dest: equalityD1 equalityD2) *)

(*Added assumptions: \<open>A : Set\<close> \<open>B : Set\<close>*)
lemma equalityCE: 
  assumes "A : Set" 
    shows "[| A = B;  [| c\<in>A; c\<in>B |] ==> P;  [| c\<notin>A; c\<notin>B |] ==> P |]  ==>  P"
by (erule equalityE[OF assms], use assms in blast)
(*WAS: by (erule equalityE, blast)*)
           
subsection \<open>Corollaries of the Axiom of Union\<close>

lemma union_set : "x : SetOf Set \<Longrightarrow> \<Union> x : Set"
  using Union_typ by (rule funE)

(*Added assumption: \<open>x : Set\<close>*)
lemma union_iff : 
  assumes "x : SetOf Set" 
    shows "a \<in> \<Union> x \<longleftrightarrow> (\<exists>y \<in> x. a \<in> y)"
  using assms uni 
  by auto
(*WAS: axiomatised then, declare union_iff [simp]*)

(*Added assumption: \<open>x : Set\<close>*)
lemma unionI [intro]: 
  assumes "x : SetOf Set" 
  shows "\<lbrakk> y \<in> x;  a \<in> y \<rbrakk> \<Longrightarrow> a \<in> \<Union> x"
  by (simp add: union_iff[OF assms], blast)
(*WAS: by (simp, blast)*)

(*Added assumption: \<open>x : Set\<close>*)
lemma unionE [elim]: 
  assumes "x : SetOf Set" 
  shows "\<lbrakk> a \<in> \<Union> x;  \<And>y. \<lbrakk> a \<in> y;  y \<in> x \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (simp add: union_iff[OF assms], blast)
(*WAS: by (simp, blast)*)

subsection \<open>Rules for power sets\<close>

(*Added assumption: \<open>x : Set\<close>*)
lemma pow_iff : 
  assumes "x : Set" "y : Set" 
    shows "x \<in> \<P> y \<longleftrightarrow> x \<subseteq> y"
  using pow assms by auto
(*WAS: an axiom*)

lemma Pow_typ_set : "Pow : Set \<rightarrow> Set"
  by (rule funI[OF subtypE[OF setof_set_subtyp funE[OF Pow_typ]]])

(*Soft typing rules can be derived from instances of typing rules: *)
lemmas pow_setof = funE[OF Pow_typ]
lemmas pow_set   = funE[OF Pow_typ_set]

lemma pow_mem : "x : Set \<Longrightarrow> y \<in> \<P> x \<Longrightarrow> y : Set"
  using funE[OF Pow_typ, THEN tyE] unfolding SetOf_def by auto

(*Added assumption: \<open>x : Set\<close>*)
lemma powI: 
  assumes "x : Set" "y : Set" 
    shows "x \<subseteq> y \<Longrightarrow> x \<in> \<P> y"
  using pow_iff[OF assms] by auto
(*WAS: by (erule Pow_iff [THEN iffD2])*)

lemma powD: 
  assumes y : "y : Set"  
    shows "x \<in> \<P> y \<Longrightarrow> x \<subseteq> y"
  using pow_iff[OF setof_mem[OF pow_setof[OF y]] assms] by simp
(*WAS: by (erule Pow_iff [THEN iffD1]) *)

lemma pow_top : 
  assumes x : "x : Set" 
    shows "x \<in> \<P> x"
  by (rule powI[OF x x subset_refl])

lemma set_setmem_subtyp : "Set << SetMem"
proof (rule subtypI, rule setmemI)
  fix x assume "x : Set"
  thus "\<P> x : Set" "x \<in> \<P> x" by (rule pow_set, rule pow_top)
qed

lemma pow_iterate :
  assumes x : "x : Set" and y : "y : Set" 
      and pow : "x \<in> \<P> y"
    shows "\<P> x \<in> \<P> (\<P> y)"
proof (rule powI[OF pow_set[OF x] pow_set[OF y]], rule)
  fix a assume "a \<in> \<P> x" 
  hence "a : Set" "a \<subseteq> x" 
    using setof_mem[OF pow_setof[OF x]] powD[OF x] by auto
  hence "a \<subseteq> y" using subset_trans[OF _ powD[OF y pow]] by auto
  thus "a \<in> \<P> y" using powI[OF \<open>a : Set\<close> y] by auto
qed

   (*  drule powD[OF x y], rule powI[OF y], metis subset_trans[OF _ powD[OF y pow]])
    *)
lemmas set_setmem = subtypE[OF set_setmem_subtyp]

subsection \<open>Rules for a witness of Axiom of Infinity\<close>

thm inf
lemma inf0 : "\<emptyset> \<in> Inf" by (simp add: inf)
lemma inf_closed: "x \<in> Inf \<Longrightarrow> Succ x \<in> Inf" by (simp add: inf)
(* lemma inf_set : "Inf : Set" by (rule Inf_typ) *)

subsection \<open>Rules for Replacement and derived operators\<close>

thm ReplPred_def
lemma replpredI :
  assumes "x : Set" "\<And>a. a \<in> x \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1 b : SetMem. P a b"
  shows "P : ReplPred x"
  using assms
  unfolding ReplPred_def has_ty_def by auto

lemma repl_iff : 
  assumes "x : Set" "P : ReplPred x"
    shows "\<forall>b. b \<in> { b | \<exists>a\<in>x. P a b } \<longleftrightarrow> (\<exists>a. a \<in> x \<and> P a b) \<and> b : SetMem"
  using repl assms by blast

lemma repl_set : 
  assumes "x : Set" "P : ReplPred x"
    shows "{ b | \<exists>a\<in>x. P a b } : Set"
  using funE[OF depfunE[OF Repl_typ]] assms 
  by auto

lemma replace_iff : 
  assumes "x : Set" "P : ReplPred x" 
    shows "b \<in> { b | \<exists>a\<in>x. P a b } \<longleftrightarrow> (\<exists>a \<in> x. P a b) \<and> b : SetMem"
  using repl assms unfolding bex_def rex_def 
  by blast

lemma replaceI : 
  assumes "x : Set" "P : ReplPred x" 
    shows "\<lbrakk> P a b ; a \<in> x ; b : SetMem\<rbrakk> \<Longrightarrow> b \<in> { b | \<exists>a\<in>x. P a b }"
  unfolding replace_iff[OF assms] 
  by blast   

lemma replaceE: 
  assumes "x : Set" "P : ReplPred x" 
    shows "\<lbrakk> b \<in> { b | \<exists>a\<in>x. P a b } ; \<And>a. \<lbrakk> a \<in> x ; b : SetMem ; P a b \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  using replace_iff[OF assms] by blast
  
lemma replace_cong : 
  assumes "x : Set" "P : ReplPred x" "y : Set" "Q : ReplPred y"  
    shows [cong]: "\<lbrakk> x = y ; \<And>a b. a \<in> y \<Longrightarrow> P a b \<longleftrightarrow> Q a b \<rbrakk> \<Longrightarrow> Repl x P = Repl y Q"
  by (rule equality_iffI[OF repl_set[OF assms(1,2)] repl_set[OF assms(3,4)]],
      unfold replace_iff[OF assms(1,2)] replace_iff[OF assms(3,4)], blast)

definition ReplFunPred :: "['a, 'a \<Rightarrow> bool] \<Rightarrow> ((['a,'a] \<Rightarrow> bool) \<Rightarrow> bool)"
  where [typdef] : "ReplFunPred x \<beta> \<equiv> ReplPred x \<triangle> BinPred (MemOf x) \<beta>"

lemma funpred_replpred: "ReplFunPred x \<beta> << ReplPred x"  
  unfolding ReplFunPred_def 
  by (rule int_sub1)

lemma funpred_binpred_typ : "ReplFunPred x \<beta> << BinPred (MemOf x) \<beta>"
  unfolding ReplFunPred_def 
  by (rule int_sub2)

lemmas funpred_binpred = subtypE[OF funpred_binpred_typ]

lemma Repl_typ2 : "Repl : (\<Pi> x : Set. ReplFunPred x \<alpha> \<rightarrow> SetOf \<alpha>)"
proof (rule depfunI, rule funI)  
  fix x P assume P:"P : ReplFunPred x \<alpha>" and x:"x : Set" 
  hence "P : ReplPred x" 
    using subtypE[OF funpred_replpred]  by simp_all
  show "Repl x P : SetOf \<alpha>"
  proof (rule setofI, rule repl_set[OF \<open>x : Set\<close> \<open>P : ReplPred x\<close>])
    fix b assume "b \<in> Repl x P" thus "b : \<alpha>" 
    proof (rule replaceE[OF \<open>x : Set\<close> \<open>P : ReplPred x\<close>])
      fix a assume "a \<in> x" "P a b"
      thus "b : \<alpha>"
        using bpredE[OF funpred_binpred[OF P] memofI] 
      by auto
    qed
  qed
qed


end
end