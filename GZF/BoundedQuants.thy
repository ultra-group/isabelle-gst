theory BoundedQuants
  imports "../GST_Features"
begin

context GZF_sig begin

subsection \<open>Soft typing rules\<close>

declare SetOf_def [typdef] SetMem_def [typdef]

lemma setof_set_subtyp : "SetOf \<alpha> << Set"
  unfolding SetOf_def by (rule subtypI, drule tyE, simp)

lemma setof_iff :
  "x : SetOf \<alpha> \<longleftrightarrow> x : Set \<and> (\<forall>b. b \<in> x \<longrightarrow> b : \<alpha>)"
  unfolding SetOf_def by (unfold_typs) 

lemma setof_subtyp : "\<alpha> << \<beta> \<Longrightarrow> SetOf \<alpha> << SetOf \<beta>"
  unfolding subtyp_def setof_iff by auto

lemma setofI : "\<lbrakk> x : Set ; \<And>b. b \<in> x \<Longrightarrow> b : P \<rbrakk> \<Longrightarrow> x : SetOf P"
  unfolding SetOf_def by (unfold_typs, auto)

lemma setof_mem : "x : SetOf \<alpha> \<Longrightarrow> b \<in> x \<Longrightarrow> b : \<alpha>"
  unfolding SetOf_def by (drule tyE, auto)

lemma setmemI : "x : Set \<Longrightarrow> a \<in> x \<Longrightarrow> a : SetMem"
  unfolding SetMem_def by (unfold_typs, auto)

lemma setmem_iff :
 "b : SetMem \<longleftrightarrow> (\<exists>x : Set. b \<in> x)" 
 by (unfold_typs)

lemma setof_set : "x : SetOf \<alpha> \<Longrightarrow> x : Set"
  by (rule subtypE[OF setof_set_subtyp])

lemma set_setof : "x : Set \<Longrightarrow> x : SetOf (SetMem)"
  by (rule setofI, use setmemI in auto)  

definition MemOf :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "MemOf x b \<equiv> b \<in> x"

lemma memofI :
  assumes "b \<in> x"
  shows "b : MemOf x"
  using assms unfolding MemOf_def
  by (unfold_typs)

lemma memofD : 
  assumes "b : MemOf x"
  shows "b \<in> x"
  using assms unfolding MemOf_def 
  by (unfold_typs)

lemmas memof_setmem = setmemI[OF _ memofD]

lemma set_setof_memof :
  assumes x:"x : Set"
  shows "x : SetOf (MemOf x)"
  using setofI[OF x memofI] by auto

abbreviation not_mem :: "['a, 'a] \<Rightarrow> bool"  (infixl \<open>\<notin>\<close> 50)  \<comment> \<open>negated membership relation\<close>
  where "x \<notin> y \<equiv> \<not> (x \<in> y)"

section \<open>Bounding quantification over a set\<close>

definition ball :: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  ball_def : "ball x P \<equiv> rall (\<lambda>a. a \<in> x) P" 
definition bex :: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  bex_def : "bex x P \<equiv> rex (\<lambda>a. a \<in> x) P"

end

(*Temporarily exiting GZF context to perform
  syntax declarations for \<in>-bounded quantification*)
syntax
  "_ball" :: "[pttrn, 'a, bool] \<Rightarrow> bool"  (\<open>(3\<forall>_\<in>_./ _)\<close> 10)
  "_bex"  :: "[pttrn, 'a, bool] \<Rightarrow> bool"   (\<open>(3\<exists>_\<in>_./ _)\<close> 10)
translations
  "\<forall>x\<in>A. P" \<rightleftharpoons> "CONST ball A (\<lambda>x. P)"
  "\<exists>x\<in>A. P" \<rightleftharpoons> "CONST bex A (\<lambda>x. P)"

syntax
  "_depfun_set" :: "[pttrn, 'a, bool] => bool" (\<open>(3\<Pi>_\<in>_./ _)\<close> 10)
translations
  "\<Pi> b\<in>x. B" \<rightleftharpoons> "CONST depfun_ty (CONST MemOf x) (\<lambda>b. B)"

context GZF_sig begin

(*Lemmas taken from ZF/ZF_Base*)
lemma ballI [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> P x) \<Longrightarrow> \<forall>x\<in>A. P x"
  by (simp add: ball_def)

lemma bspec [dest?]: "[| \<forall>x\<in>A. P x;  x\<in>A |] ==> P x"
  unfolding ball_def by auto

lemma rev_ballE [elim]:
    "[| \<forall>x\<in>A. P x;  x\<notin>A ==> Q;  P x ==> Q |] ==> Q"
  by (simp add: ball_def, blast)

lemma ballE: "[| \<forall>x\<in>A. P x;  P x ==> Q;  x\<notin>A \<Longrightarrow>  Q |] ==> Q"
  by auto

lemma ball_triv [simp]: "\<forall>x\<in>A. P \<longleftrightarrow> ((\<exists>x. x\<in>A) \<longrightarrow> P)"
 by (simp add: ball_def)

lemma ball_cong [cong]:
 "[| A=A';  !!x. x\<in>A' ==> P x \<longleftrightarrow> P' x |] ==> ((\<forall>x\<in>A. P x) \<longleftrightarrow> (\<forall>x\<in>A'. P' x))"
  by (simp add: ball_def)

lemma bexI [intro]: "[| P x;  x \<in> A |] ==> \<exists>x\<in>A. P x"
  by (simp add: bex_def, blast)

lemma rev_bexI: "[| x\<in>A;  P x |] ==> \<exists>x\<in>A. P x" by blast

lemma bexCI: "[| ball A  (\<lambda>x. \<not> P x) \<Longrightarrow> P a;  a\<in> A |] ==> \<exists>x\<in>A. P x"
  by blast

lemma bexE [elim!]: 
  "[|  \<exists>x\<in>A. P x ;  !!x. [| x\<in>A; P x |] ==> Q |] ==> Q"
by (simp add: bex_def, blast)

lemma bex_triv [simp]: "(\<exists>x\<in>A. P) \<longleftrightarrow> ((\<exists>x. x\<in>A) \<and> P)"
by (simp add: bex_def)

lemma bex_cong [cong]:
    "[| A=A';  !!x. x\<in>A' ==> P x \<longleftrightarrow> P'(x) |]
     ==> (\<exists>x\<in>A. P x) \<longleftrightarrow> (\<exists>x\<in>A'. P' x)"
  by (simp add: bex_def cong: conj_cong)

subsection \<open>Rules for the subset relation\<close>
(*Removed the need for x and y to be sets for x \<subseteq> y to be true.
  x \<subseteq> y now holds if \<forall>a. a \<in> x \<longrightarrow> a \<in> y.
  This change is in anticipation of having other objects that implement \<in>
  (e.g., groups G \<subseteq> H being equivalent to carrier G \<subseteq> carrier H) *)

lemma subset_iff : 
  "x \<subseteq> y \<longleftrightarrow> (\<forall>a \<in> x. a \<in> y)"
  using Subset_def by auto

lemma subsetI [intro]: 
  "(\<And>a. a \<in> x \<Longrightarrow> a \<in> y) \<Longrightarrow> x \<subseteq> y"
  using subset_iff by auto
(*WAS: by (simp add: subset_def) *)

lemma subsetD [elim]: 
  "[| A \<subseteq> B;  c\<in>A |] ==> c\<in>B"
  using subset_iff by auto
(*WAS: apply (unfold subset_def)
       apply (erule bspec, assumption)
       done*)

lemma subsetCE [elim]: 
  "[| A \<subseteq> B;  c\<notin>A ==> P;  c\<in>B ==> P |] ==> P"
  using subsetD by auto
(*WAS: by (simp add: subset_def, blast)*)

lemma rev_subsetD: 
  "[| c\<in>A; A \<subseteq> B |] ==> c\<in>B"
   by blast

lemma contra_subsetD: 
  "[| A \<subseteq> B; c \<notin> B |] ==> c \<notin> A"
   by blast

lemma rev_contra_subsetD: 
  "[| c \<notin> B;  A \<subseteq> B |] ==> c \<notin> A"
  by blast

lemma subset_refl : "A \<subseteq> A" 
  by blast

lemma subset_trans: 
   "[| A \<subseteq> B;  B \<subseteq> C |] ==> A \<subseteq> C"
  using subset_iff by blast
(*WAS: by blast*)


end 
end