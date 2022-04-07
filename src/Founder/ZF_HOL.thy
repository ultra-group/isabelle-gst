section \<open>Domain 0 bootstrap - Interpret GZF and Ord in Paulson's ZFC in HOL\<close>

theory ZF_HOL 
  imports "$ISABELLE_HOME/src/HOL/ZFC_in_HOL/ZFC_Typeclasses" 
    OrdRecModel_locale OrdRecConnection_locale remove_syntax 
  begin

(*membership relation, defined as HOL set membership and the 'elements' coercion from V to V set *)
abbreviation mem where "mem a x \<equiv> a \<in> elts x"

(*empty set is a coerced version of the HOL empty set*)
thm zero_V_def

(*argument of union needs lifting, then result needs flattening *)
abbreviation union where "union x \<equiv> ZFC_in_HOL.set (Union (elts ` (elts x)))"

(*subset relation gained by showing that V is a distributive lattice*)
abbreviation subset where "subset x y \<equiv> x \<le> y"

(*V \<Rightarrow> V power set already defined in ZFC_in_HOL*)
thm VPow_def

thm succ_def

abbreviation repl where "repl P x \<equiv> ZFC_in_HOL.set ((\<lambda>a. (THE b. P a b)) ` {a . a \<in> elts x \<and> (\<exists>b. P a b)})"

abbreviation ord where "ord x \<equiv> ZFC_in_HOL.Ord x"
abbreviation lt where "lt x y \<equiv> x < y \<and> ord x \<and> ord y" 
lemma lt_ord' : "lt i j \<Longrightarrow> ord i \<and> ord j" by auto
lemma succD : "ord (succ i) \<Longrightarrow> ord i"
  by (erule Ord_in_Ord, auto)
lemma succ_mem_iff : "i \<in> elts (succ j) \<longleftrightarrow> i \<in> elts j | i = j" 
  unfolding elts_succ by auto
lemma lt_mem : "lt i j \<Longrightarrow> mem i j" using lt_ord' Ord_mem_iff_lt by auto
lemma succ_iff : "lt i (succ j) \<longleftrightarrow> lt i j | i = j \<and> ord j"
proof
  assume "lt i (succ j)" hence mem:"mem i (succ j)" by (rule lt_mem)
  have "ord i" "ord (succ j)" using lt_ord'[OF \<open>lt i (succ j)\<close>] by auto
  hence "ord j" using succD by auto
  
  from mem have "mem i j | i = j" using succ_mem_iff by auto
  thus "lt i j | i = j \<and> ord j" using Ord_mem_iff_lt \<open>ord i\<close> \<open>ord j\<close> by auto
next
  assume "lt i j | i = j \<and> ord j"
  thus "lt i (succ j)"
  proof
    assume "lt i j" hence "ord i" "ord j" by auto
    from \<open>lt i j\<close> have "mem i j" using Ord_mem_iff_lt by auto
    hence "mem i (succ j)" using succ_mem_iff by auto
    hence "i < succ j" using Ord_mem_iff_lt[OF \<open>ord i\<close> Ord_succ[OF \<open>ord j\<close>]] by auto
    thus "lt i (succ j)" using \<open>ord i\<close> \<open>ord j\<close>  by auto
  next
    assume h:"i = j \<and> ord j" 
    hence "ord i" "ord (succ j)" using Ord_succ by auto

    from h have "mem i (succ j)" using succ_mem_iff by auto
    thus "lt i (succ j)" using Ord_mem_iff_lt[OF \<open>ord i\<close> \<open>ord (succ j)\<close>] \<open>ord i\<close> \<open>ord (succ j)\<close> by auto
  qed
qed

lemma mem_lt : assumes "ord j" shows "mem i j \<Longrightarrow> lt i j" using OrdmemD assms Ord_in_Ord by auto
lemma ord0: "ord 0" by auto
lemma ord\<omega>: "ord \<omega>" by auto
lemma lt_ord'_conj : "\<forall>i j. lt i j \<longrightarrow> ord i \<and> ord j" by auto
lemma succ_ord_iff' : "\<forall>i. ord i \<longleftrightarrow> ord (succ i)" using Ord_in_Ord by auto 
lemma lt_0 : "\<forall>i. \<not> lt i 0" by auto
lemma succ_iff_ax : "(\<forall>\<alpha> \<beta>. lt \<alpha> (succ \<beta>) \<longleftrightarrow> (lt \<alpha> \<beta> | \<alpha> = \<beta>  \<and> ord \<beta>))" using succ_iff by simp
lemma limit_iff' : "\<forall>\<mu>. Limit \<mu> \<longleftrightarrow> (ord \<mu> \<and> lt 0 \<mu> \<and> (\<forall>\<beta>. lt \<beta> \<mu> \<longrightarrow> lt (succ \<beta>) \<mu>))" 
  proof (rule, rule)
    fix \<mu> assume "Limit \<mu>" hence def:"ord \<mu> \<and> mem 0 \<mu> \<and> (\<forall>y. mem y \<mu> \<longrightarrow> mem (ZFC_in_HOL.succ y) \<mu>)"
      unfolding Limit_def by simp
    hence 1: "ord \<mu>" and 2: "lt 0 \<mu>" using Ord_mem_iff_lt by auto
    have 3: "(\<forall>\<beta>. lt \<beta> \<mu> \<longrightarrow> lt (succ \<beta>) \<mu>)" 
    proof (rule, rule)
      fix \<beta> assume "lt \<beta> \<mu>" hence "ord \<beta>" "mem \<beta> \<mu>" using Ord_mem_iff_lt by auto
      hence "mem (succ \<beta>) \<mu>" using def by auto
      thus "lt (succ \<beta>) \<mu>" using Ord_mem_iff_lt Ord_succ[OF \<open>ord \<beta>\<close>] \<open>ord \<mu>\<close> by auto
    qed
    from 1 2 3 show "ord \<mu> \<and> lt 0 \<mu> \<and> (\<forall>\<beta>. lt \<beta> \<mu> \<longrightarrow> lt (succ \<beta>) \<mu>)" by auto
  next
    fix \<mu> assume h:"ord \<mu> \<and> lt 0 \<mu> \<and> (\<forall>\<beta>. lt \<beta> \<mu> \<longrightarrow> lt (ZFC_in_HOL.succ \<beta>) \<mu>)"
    thus "Limit \<mu>" unfolding Limit_def using lt_mem proof (auto)
      fix y assume "mem y \<mu>" moreover hence "ord y" "ord \<mu>"using Ord_in_Ord h by auto
      ultimately have "lt y \<mu>" using Ord_mem_iff_lt by auto
      hence "lt (succ y) \<mu>" using h by auto
      thus "mem (succ y) \<mu>" using lt_mem by auto
    qed
  qed
lemma limit_omega : "Limit \<omega> \<and> (\<forall>\<mu>. Limit \<mu> \<and> \<mu> \<noteq> \<omega> \<longrightarrow> lt \<omega> \<mu>)"
proof (rule, rule Limit_omega, rule, rule, erule conjE, rule)
  fix \<mu> assume "Limit \<mu>" "\<mu> \<noteq> \<omega>"
  have "ord \<omega>" "ord \<mu>" using Limit_omega \<open>Limit \<mu>\<close> Limit_is_Ord by auto
  thus "ord \<omega> \<and> ord \<mu>" by auto
  show "\<omega> < \<mu>" proof (rule ccontr)
    assume "\<not> \<omega> < \<mu>" hence "\<mu> < \<omega>" using \<open>\<mu> \<noteq> \<omega>\<close> Ord_linear_lt[OF \<open>ord \<omega>\<close> \<open>ord \<mu>\<close>] by auto
    hence "\<exists>n . \<mu> = ord_of_nat n" using elts_\<omega> Ord_mem_iff_lt[OF \<open>ord \<mu>\<close> \<open>ord \<omega>\<close>] by auto
    thus "False" using non_Limit_ord_of_nat \<open>Limit \<mu>\<close> by auto
  qed
qed
lemma lt_trans_ax : "\<forall>i j k. lt i j \<longrightarrow> lt j k \<longrightarrow> lt i k" by auto
lemma lt_notsym_ax : "\<forall>i j. lt i j \<longrightarrow> \<not> lt j i" by auto
lemma lt_linear_ax : "\<forall>i j. ord i \<and> ord j \<longrightarrow> lt i j | i = j | lt j i" using Ord_linear_lt by auto
lemma lt_induct' : "ord a \<Longrightarrow> (\<And>x. ord x \<Longrightarrow> (\<And>y. lt y x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a"
proof -
  assume "ord a" "(\<And>x. ord x \<Longrightarrow> (\<And>y. lt y x \<Longrightarrow> P y) \<Longrightarrow> P x)"
  hence "(\<And>x. ord x \<Longrightarrow> (\<And>y. mem y x \<Longrightarrow> P y) \<Longrightarrow> P x)" using lt_mem by auto
  thus ?thesis by (rule Ord_induct[OF \<open>ord a\<close>])
qed

lemma lt_induct_ax : "\<forall>P. \<forall>a. ord a \<longrightarrow> (\<forall>x. ord x \<longrightarrow> (\<forall>y. lt y x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> P a"
  using lt_induct' by auto

lemma predset_def' : "ord j \<Longrightarrow> mem i j \<longleftrightarrow> lt i j"
  by (rule, rule mem_lt, use lt_mem in auto)
lemma predset_def'_ax : "\<forall>j. ord j \<longrightarrow> True \<and> (\<forall>i. mem i j \<longleftrightarrow> lt i j)" using predset_def' by auto

abbreviation supord where "supord x \<equiv> succ (\<Squnion> {a \<in> elts x . ord a})"

lemma supord_ax: "\<forall>j. True \<longrightarrow> ord (supord j) \<and> (\<forall>a. mem a j \<and> ord a \<longrightarrow> lt a (supord j))" 
proof (rule, rule, rule)
  fix j show "ord (supord j)" using Ord_succ Ord_Sup[of \<open>{a. mem a j \<and> ord a}\<close>] by simp
  have on:"{a. mem a j \<and> ord a} \<subseteq> ON" and small: "small ({a. mem a j \<and> ord a})" by auto
  show "(\<forall>a. mem a j \<and> ord a \<longrightarrow> lt a (supord j))"
  proof (rule, rule, erule conjE)
    fix a assume "mem a j" "ord a" 
    hence "\<forall>y \<in> ON. y<a \<longrightarrow> (\<exists>a\<in>{a. mem a j \<and> ord a}. y < a)" by auto
    hence "a \<le> \<Squnion> {a. mem a j \<and> ord a}" using le_Sup_iff[OF on \<open>ord a\<close> small] by simp
    hence "a < \<Squnion> {a. mem a j \<and> ord a} \<or> a = \<Squnion> {a. mem a j \<and> ord a}" by auto
    hence "lt a (\<Squnion> {a. mem a j \<and> ord a}) \<or> (a = \<Squnion> {a. mem a j \<and> ord a} \<and> ord (\<Squnion> {a. mem a j \<and> ord a}))"
      using \<open>ord a\<close> Ord_Sup[of \<open>{a. mem a j \<and> ord a}\<close>] by auto
    thus "lt a (supord j)" using succ_iff by auto
  qed
qed

abbreviation tr3 where "tr3 G F A \<beta> \<equiv> transrec3 A (\<lambda>i. F (succ i)) 
                                      (\<lambda>\<mu> f. G \<mu> (\<lambda>\<beta>. if lt \<beta> \<mu> then f \<beta> else 0)) \<beta>"
lemma rec0 : "\<forall>G F A. tr3 G F A 0 = A" 
  using transrec3_0 by auto
lemma recsucc: "\<forall>G F A \<beta>. ord \<beta> \<longrightarrow> tr3 G F A (succ \<beta>) = F (succ \<beta>) (tr3 G F A \<beta>)"
  using transrec3_succ by auto
lemma reclim : "\<forall>G F A \<mu>. Limit \<mu> \<longrightarrow> tr3 G F A \<mu> = G \<mu> (\<lambda>\<beta>. if lt \<beta> \<mu> then tr3 G F A \<beta> else 0)"
  using transrec3_Limit 
proof (auto)
  fix G F A \<mu> have "(\<lambda>\<beta>. if lt \<beta> \<mu> then restrict (tr3 G F A) (elts \<mu>) \<beta> else 0) = 
                    (\<lambda>\<beta>. if lt \<beta> \<mu> then tr3 G F A \<beta> else 0)" using lt_mem by auto
  thus "G \<mu> (\<lambda>\<beta>. if lt \<beta> \<mu> then restrict (tr3 G F A) (elts \<mu>) \<beta> else 0) =
       G \<mu> (\<lambda>\<beta>. if lt \<beta> \<mu> then tr3 G F A \<beta> else 0) " by auto
qed

no_notation Set.member ("'(\<in>')") and 
            Set.member ("(_/ \<in> _)" [51, 51] 50) and
            Set.not_member  ("'(\<notin>')") and
            Set.not_member  (infixl \<open>\<notin>\<close> 50) and
            Set.not_member  ("(_/ \<notin> _)" [51, 51] 50) 

global_interpretation GZF mem 0 "(\<lambda>x. True)" union subset VPow succ \<omega> repl
proof (unfold_locales, auto, rule exI)
  fix P :: "V \<Rightarrow> V \<Rightarrow> bool" and x a b assume "\<forall>a. mem a x \<longrightarrow> Uniq (P a)" "mem a x" "P a b" 
  moreover hence "The (P a) = b" unfolding Uniq_def by auto
  ultimately show "mem a x \<and> P a (The (P a))" "Set.member b ((\<lambda>a. The (P a)) ` {a. mem a x \<and> Ex (P a)})" by auto
qed
(* definition LT where "LT x y \<equiv> lt x y" *)
global_interpretation Ord ord lt 0 succ Limit \<omega>
  by (unfold_locales, rule ord0, rule ord\<omega>, rule lt_ord'_conj, rule succ_ord_iff',
      rule lt_0, rule succ_iff_ax, rule limit_iff', rule limit_omega,                                    
      rule lt_trans_ax, rule lt_notsym_ax, rule lt_linear_ax, rule lt_induct_ax)

global_interpretation OrdRec mem 0 "(\<lambda>x. True)" union subset VPow succ \<omega> repl
                             ord lt 0 succ Limit \<omega> "(\<lambda>x. x)" supord tr3
  by (unfold_locales, rule predset_def'_ax, rule supord_ax, rule rec0, rule recsucc, rule reclim)

end