theory ConnectionBase
  imports ModelTypes
begin

locale ConnectionBase = opening lifting_syntax +
  fixes Abs :: \<open>('a :: ModelBase) \<Rightarrow> 'b\<close>
    and Rep :: \<open>'b \<Rightarrow> 'a\<close>
  assumes tydef : \<open>type_definition Rep Abs (Set.Collect (\<lambda>x. x : M))\<close>
begin

interpretation c : type_definition \<open>Rep :: 'b \<Rightarrow> 'a\<close> \<open>Abs :: 'a \<Rightarrow> 'b\<close> \<open>(Set.Collect (\<lambda>x. x : M))\<close>
  by (rule tydef)

lemma M_abs_inverse :
  assumes b:"b : M"
  shows "Rep (Abs b) = b"
  using c.Abs_inverse b by auto

lemma M_rep : 
  "Rep b : M"
  using c.Rep by auto

lemmas isom [simp] =  M_abs_inverse M_rep c.Rep_inverse 

definition ConnectionRelation :: \<open>['a, 'b] \<Rightarrow> bool\<close>  (infix \<open>\<simeq>\<close> 50)
  where "x \<simeq> y \<equiv> x = Rep y"

lemma ceqD1 [dest] : "x \<simeq> y \<Longrightarrow> Abs x = y"
  unfolding ConnectionRelation_def by auto

lemma ceqD2 [dest] : "x \<simeq> y \<Longrightarrow> x = Rep y"
  unfolding ConnectionRelation_def by auto

lemma ceq_rep_refl [simp] : "(Rep x) \<simeq> x"
  unfolding ConnectionRelation_def by auto

lemma ceq_abs_refl [simp] : 
  assumes "x : M"
    shows "x \<simeq> (Abs x)"
  unfolding ConnectionRelation_def 
  using assms by auto

subsection \<open>Transfer rules for logical constants\<close>

lemma eq_transfer [transfer_rule] : 
  "((\<simeq>) ===> (\<simeq>) ===> (\<longleftrightarrow>)) (=) (=)" 
  by auto

lemma all_transfer [transfer_rule] :
  "(((\<simeq>) ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) (mall) (All)"
proof (rule)
  fix P Q assume "((\<simeq>) ===> iff) P Q"
  hence x:"\<And>x x'. x \<simeq> x' \<Longrightarrow> P x \<longleftrightarrow> Q x'" by (auto dest: rel_funD)
  show "mall P \<longleftrightarrow> All Q"
    unfolding mall_def 
    using x[OF ceq_rep_refl] x[OF ceq_abs_refl] M_rep 
    by blast
qed

lemma ex_transfer [transfer_rule] :
  "(((\<simeq>) ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) (mex) (Ex)"
proof (rule)
  fix P Q assume "((\<simeq>) ===> iff) P Q"
  hence x:"\<And>x x'. x \<simeq> x' \<Longrightarrow> P x \<longleftrightarrow> Q x'" by (auto dest: rel_funD)
  show "mex P \<longleftrightarrow> Ex Q"
    unfolding mex_def 
    using x[OF ceq_rep_refl] x[OF ceq_abs_refl] M_rep 
    by blast
qed

lemma ex1_transfer [transfer_rule] :
  "(((\<simeq>) ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) (mex1) (Ex1)"
proof (rule)
  fix P Q assume "((\<simeq>) ===> iff) P Q"
  hence x:"\<And>x x'. x \<simeq> x' \<Longrightarrow> P x \<longleftrightarrow> Q x'" by (auto dest: rel_funD)
  show "mex1 P \<longleftrightarrow> Ex1 Q"
  proof 
    assume P:"mex1 P" show "Ex1 Q"
    proof (insert P, unfold mex1_def tex1_def, erule ex1E, rule ex1I)
      fix x assume 
        "x : M \<and> P x" and uniq:"\<forall>y. y : M \<and> P y \<longrightarrow> y = x"
      thus "Q (Abs x)" "\<And>y. Q y \<Longrightarrow> y = (Abs x)" 
      proof (metis x[OF ceq_abs_refl])
        fix y assume "Q y"
        hence "(Rep y) = x" using uniq x[OF ceq_rep_refl] by auto
        thus "y = Abs x" using c.Rep_inverse by auto 
      qed
    qed
  next
    assume Q:"Ex1 Q" show "mex1 P"
      unfolding mex1_def tex1_def
    proof (rule ex1E[OF Q], rule ex1I)
      fix y assume "Q y" and uniq:"\<forall>z. Q z \<longrightarrow> z = y"
      thus "Rep y : M \<and> P (Rep y)" using M_rep[of y] x[OF ceq_rep_refl, of y] by metis
      fix y' assume y': "y' : M \<and> P y'" 
      hence "Abs y' = y" using uniq x[OF ceq_abs_refl, of y'] by auto 
      thus "y' = Rep y" using M_abs_inverse y' by auto 
    qed
  qed
qed

lemma uniq_transfer [transfer_rule] :
  "(((\<simeq>) ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) (muniq) (Uniq)"
proof (rule)
  fix P Q assume "((\<simeq>) ===> iff) P Q"
  hence x:"\<And>x x'. x \<simeq> x' \<Longrightarrow> P x \<longleftrightarrow> Q x'" by (auto dest: rel_funD)
  show "muniq P \<longleftrightarrow> Uniq Q"
  proof 
    assume P:"muniq P" show "Uniq Q"
    proof (rule)
      fix x y assume "Q x" "Q y"
      hence "P (Rep x)" "P (Rep y)" using x[OF ceq_rep_refl] by auto
      hence "Rep x = Rep y" using P 
        unfolding muniq_def tuniq_def Uniq_def by auto
      thus "x = y" using c.Rep_inject by auto
     qed
  next
    assume Q:"Uniq Q" show "muniq P"
      unfolding muniq_def tuniq_def
    proof (rule, auto)
      fix x y assume "x : M" "P x" "y : M" "P y"
      hence "Q (Abs x)" "Q (Abs y)" using x[OF ceq_abs_refl] by auto
      hence "Abs x = Abs y" using Q unfolding Uniq_def by auto
      thus "x = y" using c.Abs_inject \<open>x : M\<close> \<open>y : M\<close> by auto
    qed
  qed
qed

lemma unary_pred_all_transfer [transfer_rule] :
  "((((\<simeq>) ===> iff) ===> iff) ===> iff) All All" 
proof 
  fix U :: "('a \<Rightarrow> bool) \<Rightarrow> bool" and V  
  assume "(((\<simeq>) ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) U V"
  hence pq:"\<And>P Q. (\<And>a a' b b'. a \<simeq> a' \<Longrightarrow> P a \<longleftrightarrow> Q a') \<Longrightarrow> U P \<longleftrightarrow> V Q"
    unfolding rel_fun_def by auto
  show "All U = All V"
  proof
    assume U:"All U"
    show "All V"
    proof 
      fix Q :: "'b \<Rightarrow> bool"
      let ?P = "\<lambda>a. Q (Abs a)"
      have "\<And>a a'. a \<simeq> a' \<Longrightarrow> ?P a \<longleftrightarrow> Q a'" by auto
      hence "U ?P \<longleftrightarrow> V Q" by (rule pq)
      thus "V Q" using U by simp
    qed
  next
    assume V: "All V"
    show "All U"  
    proof 
      fix P :: "'a \<Rightarrow> bool"
      let ?Q = "\<lambda>a'. P (Rep a')"
      have "\<And>a a'. a \<simeq> a' \<Longrightarrow> P a \<longleftrightarrow> ?Q a'" by auto
      hence "U P \<longleftrightarrow> V ?Q" by (rule pq)
      thus "U P" using V by simp
    qed
  qed
qed

lemma binary_pred_all_transfer [transfer_rule] :
  "((((\<simeq>) ===> (\<simeq>) ===> iff) ===> iff) ===> iff) All All" 
proof 
  fix U :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" and V  
  assume "(((\<simeq>) ===> (\<simeq>) ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) U V"
  hence pq:"\<And>P Q. (\<And>a a' b b'. a \<simeq> a' \<Longrightarrow> b \<simeq> b' \<Longrightarrow> P a b \<longleftrightarrow> Q a' b') \<Longrightarrow> U P \<longleftrightarrow> V Q"
    unfolding rel_fun_def by auto
  show "All U = All V"
  proof
    assume U:"All U"
    show "All V"
    proof 
      fix Q :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
      let ?P = "\<lambda>a b. Q (Abs a) (Abs b)"
      have "\<And>a a' b b'. a \<simeq> a' \<Longrightarrow> b \<simeq> b' \<Longrightarrow> ?P a b \<longleftrightarrow> Q a' b'" by auto
      hence "U ?P \<longleftrightarrow> V Q" by (rule pq)
      thus "V Q" using U by simp
    qed
  next
    assume V: "All V"
    show "All U"  
    proof 
      fix P :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
      let ?Q = "\<lambda>a' b'. P (Rep a') (Rep b')"
      have "\<And>a a' b b'. a \<simeq> a' \<Longrightarrow> b \<simeq> b' \<Longrightarrow> P a b \<longleftrightarrow> ?Q a' b'" by auto
      hence "U P \<longleftrightarrow> V ?Q" by (rule pq)
      thus "U P" using V by simp
    qed
  qed
qed

lemma binary_fun_all_transfer [transfer_rule] : 
  "((((\<simeq>) ===> (\<simeq>) ===> (\<simeq>)) ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) 
      (\<lambda>P. \<forall>F : M \<rightarrow> M \<rightarrow> M. P F) (\<lambda>P. \<forall>F. P F)"
proof
  fix P Q assume "(((\<simeq>) ===> (\<simeq>) ===> (\<simeq>)) ===> (\<longleftrightarrow>)) P Q"
  hence FG: "\<And>F G. (\<And>x x' y y'. x \<simeq> x' \<Longrightarrow> y \<simeq> y' \<Longrightarrow> F x y = Rep (G x' y')) \<Longrightarrow> P F \<longleftrightarrow> Q G"
    unfolding rel_fun_def by auto
  show "(\<forall>F : M \<rightarrow> M \<rightarrow> M. P F) \<longleftrightarrow> (\<forall>F. Q F)"
  proof (rule)
    assume P:"\<forall>F : M \<rightarrow> M \<rightarrow> M. P F"
    show "\<forall>G. Q G"
    proof
      fix G
      let ?F = "\<lambda>x y. Rep (G (Abs x) (Abs y))"
      have F_typ:"?F : M \<rightarrow> M \<rightarrow> M" by (rule funI, rule funI, auto)
      have "\<And>x x' y y'. x \<simeq> x' \<Longrightarrow> y \<simeq> y' \<Longrightarrow> ?F x y = Rep (G x' y')" by (auto)
      hence "P ?F \<longleftrightarrow> Q G" using FG by auto
      thus "Q G" using P F_typ by auto
    qed
  next
    assume Q:"All Q"
    show "\<forall>F : M \<rightarrow> M \<rightarrow> M. P F" 
    proof (rule) 
      fix F :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" 
      assume F_typ:"F : M \<rightarrow> M \<rightarrow> M"
      let ?G = "\<lambda>x y. Abs (F (Rep x) (Rep y))"
      have "\<And>x x' y y'. x \<simeq> x' \<Longrightarrow> y \<simeq> y' \<Longrightarrow> F x y = Rep (?G x' y')" 
        using funE[OF funE[OF F_typ]] by auto
      hence "P F \<longleftrightarrow> Q ?G" using FG by auto
      thus "P F" using Q by auto
    qed
  qed
qed


(* text \<open>Generating locales for connections of model components\<close>
local_setup \<open>snd o mk_connection_locale @{theory} set_model\<close>
local_setup \<open>snd o mk_connection_locale @{theory} ord_model\<close>
local_setup \<open>snd o mk_connection_locale @{theory} ordrec_model\<close>
local_setup \<open>snd o mk_connection_locale @{theory} pair_model\<close>
local_setup \<open>snd o mk_connection_locale @{theory} nat_model\<close>
 *)
end
end