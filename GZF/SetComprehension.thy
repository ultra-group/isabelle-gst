theory SetComprehension
  imports GZF_Base
begin

context GZF begin

text \<open>Mapping a \<lambda>-function over a set\<close>
definition RepFun :: "['a, 'a \<Rightarrow> 'a] \<Rightarrow> 'a" where
  "RepFun x F \<equiv> Repl x (\<lambda>a b. b = F a)"

text \<open>Filtering a set using a predicate\<close>
definition Collect :: "'a \<Rightarrow> ['a \<Rightarrow> bool] \<Rightarrow> 'a" where
  "Collect x P \<equiv> Repl x (\<lambda>a b. a = b \<and> P a)"

end

syntax
  "_RepFun" :: "['a, pttrn, 'a] => 'a"  (\<open>(1{_ |/ _ \<in> _})\<close> [51,0,51])
  "_Collect" :: "[pttrn, 'a, bool ] \<Rightarrow> 'a"  (\<open>(1{_ \<in> _ |/ _})\<close>)
translations
  "{c | b\<in>x}" \<rightleftharpoons> "CONST RepFun x (\<lambda>b. c)"
  "{b\<in>x | P}" \<rightleftharpoons> "CONST Collect x (\<lambda>b. P)"


context GZF begin
(*We should only have to know that F returns a SetMem when it's applied to a member of a given set,
  but this would require making ReplFun take an extra parameter for the set.*)
(*Instead, it might be better to have a version of RepFun that restricts F to the domain of the set,
  which adds the proof obligation \<forall>a \<in> x. F a : SetMem to lemmas*)

lemma any_replpred : 
 "x : Set \<Longrightarrow> (\<lambda>a b. b = F a) : ReplPred x"
 by (rule replpredI, unfold tuniq_def Uniq_def, auto)

lemma RepFun_typ_set : "RepFun : (\<Pi> x : Set. Any \<rightarrow> Set)"
  unfolding RepFun_def 
  by (rule depfunI, rule funI, use any_replpred repl_set in auto)

definition mem_fun_ty :: \<open>'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'a) \<Rightarrow> bool)\<close> 
  (infixr \<open>\<leadsto>\<close> 50) where [typdef] : \<open>x \<leadsto> P \<equiv> MemOf x \<rightarrow> P\<close>

lemma mem_funI : 
  assumes "\<And>b. b \<in> x \<Longrightarrow> F b : P"
    shows "F : x \<leadsto> P"
  using assms 
  unfolding mem_fun_ty_def MemOf_def fun_ty_def has_ty_def
  by auto
     
lemma mem_funE : 
  assumes "F : x \<leadsto> P" "b \<in> x"
    shows "F b : P"
  using assms 
  unfolding mem_fun_ty_def MemOf_def fun_ty_def has_ty_def
  by auto

lemma replfun_funpred : 
  assumes x : "x : Set" and F : "F : x \<leadsto> \<beta>"  
    shows "(\<lambda>a b. b = F a) : ReplFunPred x \<beta>"
  unfolding ReplFunPred_def
  by (rule intI, rule any_replpred[OF x], rule bpredI, 
      use memofD mem_funE[OF F] in auto)
(*    
lemma replfunI :
  assumes x : "x : Set" and setfun:"\<And>a. a \<in> x \<Longrightarrow> F a : SetMem"
      and funty:"\<And>a. a \<in> x \<Longrightarrow>  a : \<alpha> \<Longrightarrow> F a : \<beta>"
    shows "F : ReplFun x \<alpha> \<beta>"
  unfolding ReplFun_def
  by (rule intI, rule mem_funI[OF setfun], auto, rule funI, drule intE, 
      insert funty, unfold MemOf_def has_ty_def, auto)
   *)

(* corollary setmap_replpred : "x : Set \<Longrightarrow> F : ReplFun x \<alpha> \<beta> \<Longrightarrow> (\<lambda>a b. b = F a) : ReplPred x" 
  by (rule subtypE[OF funpred_replpred replfun_funpred])
corollary setmap_binpred : "x : Set \<Longrightarrow> F : ReplFun x \<alpha> \<beta> \<Longrightarrow> (\<lambda>a b. b = F a) : BinPred (\<alpha> \<bar> MemOf x) \<beta>" 
  by (rule subtypE[OF funpred_binpred replfun_funpred])
 *)

lemma RepFun_typ : 
  "RepFun : (\<Pi> x : Set. (x \<leadsto> \<beta>) \<rightarrow> SetOf \<beta>)" 
proof (rule depfunI, rule funI)
  fix x :: 'a and F :: "'a \<Rightarrow> 'a" 
  assume "x : Set" "F : x \<leadsto> \<beta>"
  hence "(\<lambda>a b. b = F a) : ReplFunPred x \<beta>" 
    using replfun_funpred by auto
  thus "RepFun x F : SetOf \<beta>" 
    unfolding RepFun_def by (rule funE[OF depfunE[OF Repl_typ2 \<open>x : Set\<close>]])
qed

lemmas repfun_setof = funE[OF depfunE[OF RepFun_typ]]
lemmas repfun_set = funE[OF depfunE[OF RepFun_typ_set] anyI]

lemma repfunI : 
  assumes x : "x : Set"
      and b : "b \<in> x" and Fb : "F b : SetMem"
    shows "F b \<in> {F b | b \<in> x}" 
  unfolding RepFun_def
  by (rule replaceI[OF x any_replpred[OF x]], 
      use b Fb in auto)

lemma repfun_eqI : 
  assumes "x : Set"
    shows "\<lbrakk> c : SetMem ; c = F b ; b \<in> x \<rbrakk> \<Longrightarrow> c \<in> {F a | a \<in> x}"
  using repfunI[OF assms] by auto

lemma repfunE : 
  assumes x : "x : Set" and b : "b \<in> RepFun x F"
  obtains a where "a \<in> x" "b : SetMem" "b = F a" 
    using b unfolding RepFun_def
    using replaceE[OF x any_replpred[OF x], of b F] by blast
    
lemma repfun_cong : 
  assumes x : "x : Set" and y : "y : Set"
  shows "\<lbrakk> x = y ; \<And>a. a \<in> y \<Longrightarrow> F a = G a \<rbrakk> \<Longrightarrow> RepFun x F = RepFun y G" 
  unfolding RepFun_def 
  using replace_cong[OF x any_replpred[OF x] y any_replpred[OF y]] by simp 

lemma repfun_iff  : 
  assumes "x : Set"
  shows "b \<in> RepFun x F \<longleftrightarrow> (\<exists>c \<in> x. b = F c) \<and> b : SetMem"
  using repfun_eqI[OF assms] repfunE[OF assms] by blast

lemma repfun_union : 
  assumes x : "x : Set" and F : "F : x \<leadsto> Set"
  shows "b \<in> \<Union> {F a | a \<in> x} \<longleftrightarrow> (\<exists>a \<in> x. b \<in> F a)"
proof - 
  have R:"RepFun x F : SetOf Set" 
    by (rule funE[OF depfunE[OF RepFun_typ x] F])
  show ?thesis 
    unfolding union_iff[OF R] bex_def rex_def 
              repfun_iff[OF \<open>x : Set\<close>]
    by (auto, use set_setmem[OF mem_funE[OF F]] in auto )   
qed

lemma repfun_union_subset : 
  assumes x : "x : Set" and y : "y : Set" 
      and F : "F : x \<leadsto> Set" 
    shows "a \<in> x \<Longrightarrow> y \<subseteq> F a \<Longrightarrow> y \<subseteq> \<Union> {F a | a \<in> x}"
proof -
  assume "a \<in> x" "y \<subseteq> F a"
  hence "F a : Set" using mem_funE[OF F] by auto
  have "\<Union> RepFun x F : Set" 
    using union_set[OF repfun_setof[OF x F]] .
  from \<open>a \<in> x\<close> \<open>y \<subseteq> F a\<close> show ?thesis 
    unfolding repfun_union[OF x F] subset_iff
    by auto
qed


subsection \<open>Rules for subset comprehension\<close>

lemma collect_replpred : 
  "x : Set \<Longrightarrow> (\<lambda>a b. a = b \<and> P a) : ReplPred x"
  using setmemI
  unfolding ReplPred_def tuniq_def Uniq_def has_ty_def
  by auto
      (* rule, rule, rule, drule setmemI[OF \<open>x : Set\<close>], unfold has_ty_def, auto *)

lemma Collect_typ : "Collect : Set \<rightarrow> Any \<rightarrow> Set"
proof (rule funI)+
  fix x and P :: "'a => bool" assume "x : Set"
  moreover hence "(\<lambda>a b. a = b \<and> P a) : ReplPred x" by (rule collect_replpred)
  ultimately show "Collect x P : Set" unfolding Collect_def by (rule repl_set)
qed

lemmas collect_set = funE[OF funE[OF Collect_typ] anyI]

lemma collect_iff : 
  assumes x : "x : Set"
    shows "a \<in> { a \<in> x | P a} \<longleftrightarrow> a \<in> x \<and> P a"
  unfolding Collect_def replace_iff[OF \<open>x : Set\<close> collect_replpred[OF \<open>x : Set\<close>]] 
  using setmemI[OF x] by auto

lemma collectI : 
  assumes "x : Set" 
    shows "\<lbrakk> a \<in> x ; P a \<rbrakk> \<Longrightarrow> a \<in> { a \<in> x | P a }"
  using collect_iff[OF \<open>x : Set\<close>] by auto

lemma collectE : 
  assumes "x : Set" 
    shows "\<lbrakk> a \<in> { a \<in> x | P a } ; \<lbrakk> a \<in> x ; P a \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  using collect_iff[OF assms] by auto

lemma collectD1 : 
  assumes "x : Set" 
    shows "a \<in> { a\<in>x | P a } \<Longrightarrow> a \<in> x"
  using collectE[OF assms] by auto

lemma collectD2 : 
  assumes "x : Set" 
    shows "a \<in> { a\<in>x | P a } \<Longrightarrow> P a"
  using collectE[OF assms] by auto

lemma collect_subset : 
  assumes "x : Set" 
    shows "{ a\<in>x | P a } \<subseteq> x"
proof (rule subsetI)
  fix a assume "a \<in> Collect x P" 
  thus "a \<in> x" by (rule collectD1[OF \<open>x : Set\<close>])
qed

lemma collect_typ_subset : 
  assumes "x : SetOf \<alpha>" 
  shows "{ a\<in>x | P a } : SetOf \<alpha>"
proof (rule setof_subset[OF _ \<open>x : SetOf \<alpha>\<close>])
  have "x : Set" by (rule setof_set[OF \<open>x : SetOf \<alpha>\<close>])
  thus "Collect x P : Set" and "Collect x P \<subseteq> x" 
    by (rule collect_set, rule collect_subset)
qed

lemma Collect_cong [cong]: 
  assumes "x : Set" "y : Set" 
  shows [cong]: "\<lbrakk> x = y;  \<And>a. a \<in> y \<Longrightarrow> P a \<longleftrightarrow> Q a \<rbrakk> 
                  \<Longrightarrow> { a\<in>x | P a } = { a\<in>y | Q a }"
  unfolding Collect_def using collect_replpred[OF \<open>x : Set\<close>, of P] 
                              collect_replpred[of _ Q] assms by auto

end
end