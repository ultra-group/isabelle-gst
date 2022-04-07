theory GST_Logic
  imports remove_syntax
begin

ML_file \<open>Tools/isar_tools.ML\<close>
ML_file \<open>Tools/locale_tools.ML\<close>
ML_file \<open>Tools/class_tools.ML\<close>

(*Perhaps not use 'a as the type variable *)
definition the_default :: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a" (\<open>\<iota>'' _ _\<close> [90,90] ) where
  "\<iota>' d F \<equiv> if Ex1 F then (THE x. F x) else d"

syntax 
  "_the_default" :: "[idts, 'a \<Rightarrow> bool, 'a] \<Rightarrow> bool" (\<open>(3\<iota>_./ _/ else _)\<close>  [0, 10, 10] 10)
translations
  "\<iota> x. P else default" \<rightleftharpoons> "CONST the_default default (\<lambda>x. P)"

lemma the_def_if : "if (Ex1 F) then (F a \<longleftrightarrow> \<iota>' d F = a) 
                               else \<iota>' d F = d"
proof (cases \<open>Ex1 F\<close>)
  assume "Ex1 F" 
  hence eq:"\<iota>' d F = (THE x. F x)" unfolding the_default_def by auto
  have "F a \<longleftrightarrow> \<iota>' d F = a" 
  proof
    assume "F a"
    thus "\<iota>' d F = a" by (subst eq, insert \<open>Ex1 F\<close>, auto)
  next
    assume "\<iota>' d F = a"
    thus "F a" using eq \<open>Ex1 F\<close> by (auto intro: theI)
  qed
  thus "if (Ex1 F) then (F a \<longleftrightarrow> \<iota>' d F = a) else \<iota>' d F = d" using \<open>Ex1 F\<close> by simp
next
  assume "\<not> Ex1 F"
  thus "if (Ex1 F) then (F a \<longleftrightarrow> \<iota>' d F = a) else \<iota>' d F = d" 
    unfolding the_default_def by auto
qed

lemma the_def_default :
  assumes "\<not> (Ex1 P)" 
  shows "\<iota>' d P = d"
  using the_def_if[of P] assms by auto

lemma the_def_eq : 
  assumes "P a" "\<And>x. P x \<Longrightarrow> x = a"
  shows "\<iota>' d P = a"
proof -
  from assms have "Ex1 P" by auto
  hence "P a \<longleftrightarrow> (\<iota>' d P) = a" using the_def_if[of P] by auto
  thus "(\<iota>' d P) = a" using \<open>P a\<close> by auto
qed

lemma the_def_eq' : "\<lbrakk> Ex1 P ; P a \<rbrakk> \<Longrightarrow> (\<iota>' d P) = a"
  by (blast intro: the_def_eq)

lemma the_defI : assumes "P a" "\<And>x. P x \<Longrightarrow> x = a"
  shows "P (\<iota>' d P)"
proof -
  from the_def_eq[of P] assms have "\<iota>' d P = a" by blast 
  thus "P (\<iota>' d P)" using \<open>P a\<close> by simp
qed

(*Definite description lemmas followed by an apostrophe use an 
 explicit uniqueness quantifier in their assumptions*)
lemma the_defI' : assumes "Ex1 P" shows "P (\<iota>' d P)"
  using assms by (blast intro: the_defI)

(*Distinction of _ and 2 is from Isabelle/HOL's lemma names *)
lemma the_defI2 : assumes "P a" "\<And>x. P x \<Longrightarrow> x = a" "\<And>x. P x \<Longrightarrow> Q x"
  shows "Q (\<iota>' d P)" by (blast intro: assms the_defI)

lemma the_defI2' : assumes "Ex1 P" "\<And>x. P x \<Longrightarrow> Q x" shows "Q (\<iota>' d P)" 
  by (blast intro: assms(2) the_defI2[where P=P and Q=Q] ex1E[OF assms(1)])

lemma the_def_cong : 
  assumes "P = Q"
  shows "(\<iota>' d P) = (\<iota>' d Q)"
  unfolding assms ..

declare the_defI2' [simp]  

subsection \<open>Restricted quantification using a predicate\<close>
(*TODO: remove these, and just define ball, bex in terms of tall, tex.*)

definition rall :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  rall_def : "rall P Q \<equiv> \<forall>x. P x \<longrightarrow> Q x"
definition rex :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  rex_def : "rex P Q \<equiv> \<exists>x. P x \<and> Q x"
definition rex_uniq :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  rex_uniq_def : "rex_uniq P Q \<equiv> (\<exists>\<^sub>\<le>\<^sub>1 x. P x \<and> Q x)"
definition rex1 :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  rex1_def : "rex1 P Q \<equiv> (\<exists>! x. P x \<and> Q x)"

syntax
  "_rall"     :: "['a=>bool, pttrn, bool] => bool" (\<open>(3\<forall>[_]_./ _)\<close> 10)
  "_rex"      :: "['a=>bool, pttrn,  bool] => bool" (\<open>(3\<exists>[_]_./ _)\<close> 10)
  "_rex_uniq" :: "['a=>bool, pttrn, bool] => bool" (\<open>(3\<exists>\<^sub>\<le>\<^sub>1[_]_./ _)\<close> 10)
  "_rex1"     :: "['a=>bool, pttrn, bool] => bool" (\<open>(3\<exists>![_]_./ _)\<close> 10)
translations
  "\<forall>[M]x. P" \<rightleftharpoons> "CONST rall M (\<lambda>x. P)"
  "\<exists>[M]x. P" \<rightleftharpoons> "CONST rex M  (\<lambda>x. P)"
  "\<exists>\<^sub>\<le>\<^sub>1[M] x. P" \<rightleftharpoons> "CONST rex_uniq M  (\<lambda>x. P)"
  "\<exists>![M] x. P" \<rightleftharpoons> "CONST rex1 M  (\<lambda>x. P)"

(*Taken from ZF/OrdQuant, unfolded syntax*)
(*Go back and take from OrdQuant*)
lemma rallI [intro]: "[| !!x. M(x) ==> P(x) |] ==> \<forall>[M]x. P x"
by (simp add: rall_def)

lemma rspec: "[| rall M P; M(x) |] ==> P(x)"
by (simp add: rall_def)

lemma rev_rallE [elim]:
    "[| rall M P;  \<not> M(x) ==> Q;  P(x) ==> Q |] ==> Q"
by (simp add: rall_def, blast)

lemma rallE: "[| rall M P; P(x) ==> Q;  \<not> M(x) ==> Q |] ==> Q"
by blast

lemma rall_triv [simp]: "(rall M (\<lambda>x. P)) \<longleftrightarrow> ((\<exists>x. M x) \<longrightarrow> P)"
by (simp add: rall_def)

lemma rall_cong [cong]:
    "(\<And>x. M(x) \<Longrightarrow> P(x) \<longleftrightarrow> P'(x)) ==> (rall M P) \<longleftrightarrow> (rall M P')"
by (simp add: rall_def)

lemma rexI [intro]: "[| P(x); M(x) |] ==> rex M P"
by (simp add: rex_def, blast)

lemma rev_rexI: "[| M(x);  P(x) |] ==> rex M P"
by blast

lemma rexCI: "[| rall M (\<lambda>x. \<not>P x) ==> P(a); M(a) |] ==> rex M P"
by blast

lemma rexE [elim]: "[| rex M P;  !!x. [| M(x); P(x) |] ==> Q |] ==> Q"
by (simp add: rex_def, blast)

lemma rex_triv [simp]: "(rex M (\<lambda>x. P)) \<longleftrightarrow> ((\<exists>x. M(x)) \<and> P)"
by (simp add: rex_def)

lemma rex_cong [cong]:
    "(!!x. M(x) ==> P(x) \<longleftrightarrow> P'(x)) ==> (rex M P) \<longleftrightarrow> (rex M P')"
by (simp add: rex_def cong: conj_cong)

lemma atomize_rall: "(!!x. M(x) ==> P(x)) == Trueprop (rall M P)"
by (simp add: rall_def atomize_all atomize_imp)


end