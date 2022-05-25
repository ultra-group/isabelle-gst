theory ConnectionBase
  imports ModelTypes
begin

locale ConnectionBase = opening lifting_syntax +
  fixes Abs :: \<open>('a :: ModelBase') \<Rightarrow> 'b\<close>
    and Rep :: \<open>'b \<Rightarrow> 'a\<close>
    and rel :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close> (infix \<open>\<simeq>\<close> 50)
    and mdefault :: \<open>'a\<close>
  assumes tydef   : \<open>type_definition Rep Abs (Set.Collect (\<lambda>x. x : M))\<close>
      and rel_def : \<open>rel x y = (x = Rep y)\<close>
      and mdefault_m : "mdefault : M"
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


lemma ceqD1 [dest] : "x \<simeq> y \<Longrightarrow> Abs x = y"
  unfolding rel_def by auto

lemma ceqD2 [dest] : "x \<simeq> y \<Longrightarrow> x = Rep y"
  unfolding rel_def by auto

lemma ceq_rep_refl [simp] : "(Rep x) \<simeq> x"
  unfolding rel_def by auto

lemma ceq_abs_refl [simp] : 
  assumes "x : M"
    shows "x \<simeq> (Abs x)"
  unfolding rel_def 
  using assms by auto

subsection \<open>Transfer rules for soft typing\<close>

lemma typing_transfer [transfer_rule]: "(R ===> (R ===> iff) ===> iff) (:) (:)"
  unfolding rel_fun_def has_ty_def by auto

lemma int_transfer [transfer_rule]: "((R ===> iff) ===> (R ===> iff) ===> (R ===> iff)) (\<triangle>) (\<triangle>)"
  unfolding rel_fun_def inter_ty_def by auto

lemma un_transfer [transfer_rule]: "((R ===> iff) ===> (R ===> iff) ===> (R ===> iff)) (\<mho>) (\<mho>)"
  unfolding rel_fun_def union_ty_def has_ty_def by auto 

lemma pred_ty_eq :
  "P = Q \<longleftrightarrow> (\<forall>x. x : P \<longleftrightarrow> x : Q)"
  unfolding has_ty_def by auto

lemma subtyp_eq :
  "P << Q \<longleftrightarrow> (\<forall>x. x : P \<longrightarrow> x : Q)"
  unfolding has_ty_def subtyp_def by auto

subsection \<open>Transfer rules for logical constants\<close>


lemma eq_transfer [transfer_rule] : 
  "((\<simeq>) ===> (\<simeq>) ===> (\<longleftrightarrow>)) (=) (=)" 
  by auto

(* lemma higher_order_eq_transfer [transfer_rule] : 
  "(((\<simeq>) ===> iff) ===> ((\<simeq>) ===> iff) ===> (\<longleftrightarrow>)) (\<lambda>P Q. m\<forall>x. P x \<longleftrightarrow> Q x) (=)" 
   sorry*)
  
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

lemma limfun_all_transfer [transfer_rule] : 
  "((((\<simeq>) ===> ((\<simeq>) ===> (\<simeq>)) ===> (\<simeq>)) ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) 
      (\<lambda>P. \<forall>G : LimFun. P G) (\<lambda>P. \<forall>G. P G)"
proof
  fix P Q assume "(((\<simeq>) ===> ((\<simeq>) ===> (\<simeq>)) ===> (\<simeq>)) ===> (\<longleftrightarrow>)) P Q"
  hence FG: 
    "\<And>G G'. (\<And>x x'. x \<simeq> x' \<Longrightarrow> (\<And>f f'. ((\<simeq>) ===> (\<simeq>)) f f'  
      \<Longrightarrow> G x f = Rep (G' x' f'))) \<Longrightarrow> P G \<longleftrightarrow> Q G'"
    unfolding rel_fun_def rel_def by blast
  show "(\<forall>G : LimFun. P G) \<longleftrightarrow> (\<forall>G. Q G)"
  proof (rule)
    assume P:"\<forall>G : LimFun. P G"
    show "\<forall>G'. Q G'"
    proof
      fix G'
      let ?G = "\<lambda>x f. Rep (G' (Abs x) (\<lambda>y. Abs (f (Rep y))))"
      have G_typ:"?G : LimFun" 
        unfolding LimFun_def
        by (rule intI, rule funI, rule funI, auto, 
            rule tyI, use forceM_eq[OF M_rep] in auto)
      have "\<And>x x' f f'. x \<simeq> x' \<Longrightarrow> ((\<simeq>) ===> (\<simeq>)) f f' 
              \<Longrightarrow> ?G x f = Rep (G' x' f')" 
        unfolding rel_fun_def rel_def by (auto)
      hence "P ?G \<longleftrightarrow> Q G'" using FG by auto
      thus "Q G'" using P G_typ by auto
    qed
  next
    assume Q:"All Q"
    show "\<forall>G : LimFun. P G" 
    proof (rule) 
      fix G :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" 
      assume G_typ:"G : LimFun"
      let ?G' = "\<lambda>x f. Abs (G (Rep x) (\<lambda>y. Rep (f (Abs (forceM y)))))"
      have "\<And>x x' f f'. x \<simeq> x' \<Longrightarrow> ((\<simeq>) ===> (\<simeq>)) f f'  \<Longrightarrow> G x f = Rep (?G' x' f')" 
        unfolding rel_fun_def rel_def  
      proof -
        fix x x' f f' assume 
          x_eq : "x = Rep x'" and
          f_eq : "\<forall>x y. x = Rep y \<longrightarrow> f x = Rep (f' y)"
        hence 
          "\<forall>a. f (forceM a) = Rep (f' (Abs (forceM a)))"
          by (metis forceM_m M_abs_inverse)
        hence 
          "G x (\<lambda>a. f (forceM a)) = Rep (?G' x' f')"
          using x_eq funE[OF funE[OF limfunD1[OF G_typ]] funI] by auto
        moreover have "f : M \<rightarrow> M" 
        proof (rule funI)
          fix x :: \<open>'a\<close> assume "x : M"
          hence "x = Rep (Abs x)" by auto
          hence "f x = Rep (f' (Abs x))" using f_eq by blast
          thus "f x : M" using M_rep by auto
        qed
        ultimately show 
          "G x f = Rep (?G' x' f')"
          using limfunD2[OF G_typ] x_eq M_rep funI[OF ] by auto
      qed
      hence "P G \<longleftrightarrow> Q ?G'" using FG by auto
      thus "P G" using Q by auto
    qed
  qed
qed

subsection \<open>Transfer rules for type-bounded quantifiers\<close>

lemma tall_transfer [transfer_rule] :
  "(((\<simeq>) ===> (\<longleftrightarrow>)) ===> ((\<simeq>) ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) (mtall) (tall)"
  unfolding mtall_def tall_def
  by (transfer_prover)

lemma tall_binpred_transfer [transfer_rule] :
  "((((\<simeq>) ===> (\<simeq>) ===> iff) ===> iff) ===> (((\<simeq>) ===> (\<simeq>) ===> iff) ===> iff) ===> iff) tall tall" 
  unfolding mtall_def tall_def
  by (transfer_prover)

lemma tex_transfer [transfer_rule] :
  "(((\<simeq>) ===> (\<longleftrightarrow>)) ===> ((\<simeq>) ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) (mtex) (tex)"
  unfolding mtex_def tex_def
  by (transfer_prover)

lemma tuniq_transfer [transfer_rule] :
  "(((\<simeq>) ===> (\<longleftrightarrow>)) ===> ((\<simeq>) ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) (mtuniq) (tuniq)"
  unfolding mtuniq_def tuniq_def
  by (transfer_prover)


subsection \<open>Transfer rules for definite descriptions\<close>

lemma defdes_transfer [transfer_rule] :
  "(rel ===> (rel ===> (\<longleftrightarrow>)) ===> rel) (\<lambda>d P. mdefdes P d) the_default"
proof (rule, rule)
  fix d d' P P'
  assume d:"d \<simeq> d'" and "(rel ===> iff) P P'"
  hence P_iff :"\<And>b b'. b \<simeq> b' \<Longrightarrow> P b \<longleftrightarrow> P' b'" by (auto dest: rel_funD)
  show "(mdefdes P d) \<simeq> (\<iota>' d' P')"
    unfolding rel_def mdefdes_def typ_defdes_def
  proof (cases \<open>\<exists>!x. P' x\<close>, rule the_def_eq')
    case ex1:True
    hence "P' (\<iota>' d' P')"
      using the_defI' by simp
    moreover have rel:"(Rep \<iota>' d' P') \<simeq> \<iota>' d' P'" by auto
    ultimately show "Rep \<iota>' d' P' : M \<and> P (Rep \<iota>' d' P')" 
      using P_iff[OF rel] M_rep by auto
  
    from ex1 obtain b' where "P' b'" and c':"\<And>c'. P' c' \<Longrightarrow> c' = b'" by auto
    hence "P (Rep b')" "\<And>c. c : M \<and> P c \<Longrightarrow> c = Rep b'" 
    proof (metis P_iff[of \<open>Rep b'\<close> \<open>b'\<close>, OF ceq_rep_refl])
      fix c assume c:"c : M \<and> P c"
      hence "P' (Abs c)" 
        using P_iff[OF ceq_abs_refl] by auto
      hence "Abs c = b'" using c' by simp
      thus "c = Rep b'" using c by auto
    qed 
    thus "\<exists>!x'. x' : M \<and> P x'" 
      using ex1I[of \<open>\<lambda>x'. x' : M \<and> P x'\<close> \<open>Rep b'\<close>] by auto
  next
    case nex1P: False
    hence nex1P':"\<not> (\<exists>!x. x : M \<and> P x)" using P_iff 
      by (metis M_rep c.Rep_inverse ceq_abs_refl) 
    have "(\<iota> x. x : M \<and> P x else d) = d"
     and "\<iota>' d' P' = d'" 
    using the_def_default[OF nex1P] the_def_default[OF nex1P'] by auto
    then show "(\<iota> x. x : M \<and> P x else d) = Rep \<iota>' d' P'"
      using d by auto
  qed
qed

lemma typ_defdes_transfer [transfer_rule] :
  "((rel ===> (\<longleftrightarrow>)) ===> (rel ===> (\<longleftrightarrow>)) ===> rel ===> rel) mtdefdes typ_defdes"
  unfolding mtdefdes_def typ_defdes_def
  by (transfer_prover)

end
end