theory Ordinal
  imports "../GST_Features"
begin

context Ordinal begin
(*Recalling signature and axioms of feature:*)
(* - Types and axioms for \<open>zero\<close>, \<open>succ\<close> and \<open>\<omega>\<close>: *)
thm zero_typ succ_typ omega_typ zero_ax succ_ax omega_ax Limit_def
(* - Axioms specifying that \<open><\<close> is a well-order on the ordinals:*)  
thm lt_trans lt_notsym lt_linear lt_induct

lemmas succ_ord = funE[OF succ_typ]

subsection \<open>Initial Finite Ordinals\<close>

lemma zero_lt : 
  assumes "b : Ord"
    shows "\<not> b < 0"
  using zero_ax assms 
  by auto

(*Don't think we actually ever use this lemma,
  it's just analagous to the one in ZF/Ordinal.thy*)
lemmas zero_ltE = zero_lt [THEN notE]

(* definition one   :: "'d" (\<open>1\<close>) where "1 \<equiv> succ 0"
definition two   :: "'d" (\<open>2\<close>) where "2 \<equiv> succ 1"
definition three :: "'d" (\<open>3\<close>) where "3 \<equiv> succ 2"
lemma one_ord   : "1 : Ord" unfolding one_def   by (rule succ_ord[OF zero_typ])
lemma two_ord   : "2 : Ord" unfolding two_def   by (rule succ_ord[OF one_ord])
lemma three_ord : "3 : Ord" unfolding three_def by (rule succ_ord[OF two_ord])
 *)
subsection \<open>Well-Ordering properties of < \<close>

lemma trans :
  assumes "i : Ord" "j : Ord" "k : Ord" 
      and "i < j" "j < k"
    shows "i < k"
  using lt_trans assms
  by auto

lemma asym :
  assumes "i : Ord" "j : Ord"
      and "i < j" "\<not> P \<Longrightarrow> j < i"
    shows "P"
  using lt_notsym assms
  by auto

lemma lt_reflE : 
  assumes "i : Ord" 
    shows "i < i \<Longrightarrow> P"
  using asym assms 
  by auto

corollary not_refl :
  assumes "i : Ord"
    shows "\<not> i < i"
  using lt_reflE[OF assms] 
  by auto

lemma lt_neq :
  assumes "i : Ord" "j : Ord"
  shows "i < j \<Longrightarrow> i \<noteq> j"
  using lt_reflE assms 
  by auto

lemma linear : 
  assumes "i : Ord" "j : Ord"
  obtains (lt) "i < j" | (eq)  "i = j" | "j < i"
  using assms lt_linear
  by auto

subsection \<open>succ - Successor operation\<close>

lemma succ_lt :
  assumes "i : Ord"
    shows "i < succ i"
  using succ_ax assms by auto

lemma succ_neq : 
  assumes "i : Ord"
  shows "i \<noteq> succ i"
  by (rule lt_neq[OF assms succ_ord[OF assms] succ_lt[OF assms]])

lemma succ_nonzero :
  assumes "i : Ord"
  shows "succ i \<noteq> 0"
  using succ_lt zero_lt assms by auto

subsection \<open>leq - Less Than or Equal To\<close>

abbreviation leq (infixl \<open>\<le>\<close> 50) where "x \<le> y \<equiv> x < succ y"
lemma leq_iff : 
  assumes "i : Ord" "j : Ord"
    shows "i \<le> j \<longleftrightarrow> i < j \<or> i = j"
  using succ_ax assms unfolding tall_def 
  by auto

lemma leqI1 :
  assumes "i : Ord" "j : Ord"
    shows "i < j \<Longrightarrow> i \<le> j"
  using leq_iff[OF assms] 
  by auto

lemma leqI2 :
  assumes "i : Ord" "j : Ord"
    shows "i = j \<Longrightarrow> i \<le> j"
  using leq_iff[OF assms] 
  by auto
    
lemma leqE :
  assumes "i : Ord" "j : Ord" "i \<le> j"
      and "i < j \<Longrightarrow> P" "i = j \<Longrightarrow> P"
    shows "P"
  using leq_iff assms 
  by auto

lemma leq_refl :
  assumes "i : Ord"
    shows "i \<le> i"
  using leqI2 assms 
  by auto

lemma linear_lt_leq :
  assumes "i : Ord" "j : Ord"
  obtains (lt) "i < j" | (ge) "j \<le> i"
  by (rule linear[OF assms], use leqI1 leqI2 assms in auto)

lemma linear_leq :
  assumes "i : Ord" "j : Ord"
  obtains (le) "i \<le> j" | (ge) "j \<le> i"
  by (rule linear_lt_leq[OF assms], 
      blast intro: leqI1 leqI2 assms)

lemma not_lt_leq : 
  assumes "i : Ord" "j : Ord"
  shows "\<not> i < j \<Longrightarrow> j \<le> i"
  by (rule linear_lt_leq[OF assms], auto)

lemma leq_not_lt :
  assumes "i : Ord" "j : Ord"
    shows "j \<le> i \<Longrightarrow> \<not> i < j"
  using leqE asym assms 
  by blast

lemma not_leq_iff_lt :
  assumes "i : Ord" "j : Ord"
    shows "\<not> i < j \<longleftrightarrow> j \<le> i"
  using not_lt_leq leq_not_lt assms 
  by auto  

lemma neq_zero_lt :
  assumes "i : Ord"
    shows "i \<noteq> 0 \<Longrightarrow> 0 < i"
proof -
  have "0 \<le> i" using zero_lt[OF assms] not_leq_iff_lt[OF assms zero_typ] by auto
  assume "i \<noteq> 0" 
  thus "0 < i" using leqE[OF zero_typ assms \<open>0 \<le> i\<close>] by auto
qed

lemma leqCI : 
  assumes "i : Ord" "j : Ord"
      and "i \<noteq> j \<Longrightarrow> i < j"
    shows "i \<le> j"
  unfolding leq_iff[OF assms(1,2)] using assms(3) 
  by auto

lemma leq_antisym : 
  assumes "i : Ord" "j : Ord"
    shows "i \<le> j \<Longrightarrow> j \<le> i \<Longrightarrow> i = j"
  using leq_iff asym assms by auto

lemma leq_zero_iff :
  assumes "i : Ord"
    shows "i \<le> 0 \<longleftrightarrow> i = 0"
  unfolding leq_iff[OF \<open>i : Ord\<close> zero_typ] using zero_lt[OF \<open>i : Ord\<close>]
  by auto

lemma leq_zeroD :
  assumes "i : Ord"
    shows "i \<le> 0 \<Longrightarrow> i = 0"
  by (rule leq_zero_iff[OF \<open>i : Ord\<close>, THEN iffD1])

lemma zero_leq :
  assumes "i : Ord"
    shows "0 \<le> i"
  using not_lt_leq[OF _ zero_typ] zero_lt assms
  by auto

lemma zero_lt_iff : 
  assumes "i : Ord"
    shows "i \<noteq> 0 \<longleftrightarrow> 0 < i"
  using zero_leq[OF assms] leq_iff[OF zero_typ assms] not_refl[OF zero_typ] by auto

lemma all_lt_leq : 
  assumes "i : Ord" "j : Ord"
      and lt: "\<And>x. x : Ord \<Longrightarrow> x < j \<Longrightarrow> x < i"  
    shows "j \<le> i"
  using not_lt_leq not_refl assms 
  by auto

lemma leq_succ_iff :
  assumes "i : Ord" "j : Ord"
    shows "i \<le> succ j \<longleftrightarrow> i \<le> j \<or> i = succ j"
  unfolding leq_iff[OF \<open>i : Ord\<close> succ_ord[OF \<open>j : Ord\<close>]] 
  by rule



subsection \<open>Transitivity Rules\<close>

lemma lt_trans1 : 
  assumes "i : Ord" "j : Ord" "k : Ord"
  shows "i \<le> j \<Longrightarrow> j < k \<Longrightarrow> i < k"
  by (blast elim!: leqE[OF \<open>i : Ord\<close> \<open>j : Ord\<close>] 
            intro: trans[OF assms])

lemma lt_trans2 : 
  assumes "i : Ord" "j : Ord" "k : Ord"
  shows "i < j \<Longrightarrow> j \<le> k \<Longrightarrow> i < k"
  by (blast elim!: leqE[OF \<open>j : Ord\<close> \<open>k : Ord\<close>] 
            intro: trans[OF assms])

lemma leq_trans2 : 
  assumes "i : Ord" "j : Ord" "k : Ord"
  shows "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> i \<le> k"
  by (blast intro: lt_trans1[OF \<open>i : Ord\<close> \<open>j : Ord\<close> succ_ord[OF \<open>k : Ord\<close>]])

lemma succ_leqI :
  assumes "i : Ord" "j : Ord"
  shows "i<j \<Longrightarrow> succ i \<le> j"
proof (rule not_leq_iff_lt[OF \<open>j : Ord\<close> succ_ord[OF \<open>i : Ord\<close>], THEN iffD1])
  assume "i < j" thus "\<not> j \<le> i" 
    using not_leq_iff_lt[OF \<open>i : Ord\<close> \<open>j : Ord\<close>] by auto
qed

lemma succ_leqE : 
  assumes "i : Ord" "j : Ord"
  shows "succ i \<le> j \<Longrightarrow> i < j"
proof - 
  assume "succ i \<le> j"
  hence "\<not> j \<le> i" using not_leq_iff_lt[OF \<open>j : Ord\<close> succ_ord[OF \<open>i : Ord\<close>]] by auto
  thus "i < j" using not_leq_iff_lt[OF \<open>i : Ord\<close> \<open>j : Ord\<close>] by auto
qed

lemma succ_leq_iff : 
  assumes "i : Ord" "j : Ord"
  shows "succ i \<le> j \<longleftrightarrow> i < j"
  using succ_leqI succ_leqE assms
  by auto

lemma succ_leq_imp_leq : 
  assumes "i : Ord" "j : Ord"
  shows "succ i \<le> succ j \<longleftrightarrow> i \<le> j"
  using succ_leq_iff assms succ_ord 
  by auto

lemma lt_zero_lt :
  assumes "i : Ord" "j : Ord"
  shows "j < i \<Longrightarrow> 0 < i"
  using lt_trans1[OF zero_typ \<open>j : Ord\<close> \<open>i : Ord\<close>]
        zero_leq[OF \<open>j : Ord\<close>] 
  by auto


subsection \<open>Limit Ordinals\<close>


lemma limit_ord : 
  assumes "\<mu> : Limit"
    shows "\<mu> : Ord"
  using assms unfolding Limit_def 
  by (unfold_typs)

lemma limit_lt_zero : 
  assumes "\<mu> : Limit"
    shows "0 < \<mu>"
  using assms unfolding Limit_def 
  by (unfold_typs)

lemma limit_nonzero : 
  assumes "\<mu> : Limit"
  shows "\<mu> \<noteq> 0"
  using zero_lt_iff[OF limit_ord] limit_lt_zero assms
  by auto

lemma limit_lt_succ :
  assumes "\<mu> : Limit" "\<beta> : Ord" "\<beta> < \<mu>"
    shows "succ \<beta> < \<mu>"
  using assms unfolding Limit_def
  by (unfold_typs)

lemma limit_succE : 
  assumes i:"i : Ord" and succ_i:"succ i : Limit"
  shows "P"
proof (rule ccontr)
  have succ_i_ord:"succ i : Ord" by (rule limit_ord[OF succ_i])
  hence "\<not> succ i < succ i" by (rule not_refl)
  thus "False" using limit_lt_succ[OF succ_i i leq_refl[OF i]] by auto
qed

definition nonLimit where [typdef] : "nonLimit \<equiv> Ord \<bar> (\<lambda>i. \<not> i : Limit)"

lemma nonLimitI : 
  assumes "i : Ord" "\<not> i : Limit"
  shows "i : nonLimit"
  using assms by unfold_typs

lemma nonLimitD :
  assumes "i : nonLimit" 
  shows "i : Ord \<and> \<not> i : Limit"
  using assms by unfold_typs

lemmas nonLimitE = conjE[OF nonLimitD]
lemma nonlimit_ord :
  assumes i:"i : nonLimit"
  shows "i : Ord"
    using i by unfold_typs

thm Ordinal.limit_succE Ordinal_axioms
lemma not_succ_limit : 
  assumes i:"i : Ord"
  shows "\<not> succ i : Limit"
  by (meson i limit_succE)
  
(* lemma limit_lt_one :
  assumes \<mu>:"\<mu> : Limit"
  shows "1 < \<mu>"
  unfolding one_def 
  by (rule limit_lt_succ[OF \<mu> zero_typ limit_lt_zero[OF \<mu>]]) *)

lemma limit_succ_lt_iff : 
  assumes \<mu>:"\<mu> : Limit" and i:"i : Ord"
  shows "succ i < \<mu> \<longleftrightarrow> i < \<mu>"
proof (rule)
  assume "succ i < \<mu>"
  moreover have "i < succ i" by (rule succ_lt[OF i])
  ultimately show "i < \<mu>" using trans[OF i succ_ord[OF i] limit_ord[OF \<mu>]] by auto
next
  assume "i < \<mu>" 
  thus "succ i < \<mu>" by (rule limit_lt_succ[OF \<mu> i]) 
qed

lemma not_zero_limit : "\<not> 0 : Limit"
  using not_refl[OF zero_typ] unfolding Limit_def has_ty_def inter_ty_def 
  by auto

lemmas zero_nonlimit = nonLimitI[OF zero_typ not_zero_limit]

lemma succ_nonlimit : 
  assumes i:"i : Ord"
  shows "succ i : nonLimit"
  using nonLimitI not_succ_limit i succ_ord by auto

lemma limit_leq_succD : 
  assumes \<mu>:"\<mu> : Limit" and i:"i : Ord"
  shows "\<mu> \<le> succ i \<Longrightarrow> \<mu> \<le> i"
  by (rule leqE[OF limit_ord[OF \<mu>] succ_ord[OF i]], 
      use not_succ_limit[OF i] \<mu> in auto)
      
lemma limitI : 
  assumes "i : Ord" 
    and "0 < i" "\<forall>j : Ord. succ j \<noteq> i"
  shows "i : Limit" unfolding Limit_def 
proof (rule intI[OF \<open>i : Ord\<close>], rule tyI, rule, rule \<open>0 < i\<close>, rule, rule)
  fix j assume "j : Ord" "j < i"
  hence "\<not> i \<le> j" "succ j \<noteq> i" using leq_not_lt[OF _ \<open>i : Ord\<close>] assms(3) by auto
  thus "succ j < i" using assms(3) linear[OF succ_ord[OF \<open>j : Ord\<close>] \<open>i : Ord\<close>] by auto
qed

lemma increasing_limitI : 
  assumes \<mu>:"\<mu> : Ord" and zero: "0 < \<mu>" 
  and lt:"\<forall>i : Ord. i < \<mu> \<longrightarrow> (\<exists>j : Ord. j < \<mu> \<and> i < j)"
  shows "\<mu> : Limit"
  unfolding Limit_def
proof (rule Soft_Types.intI[OF \<mu>], rule tyI, rule conjI[OF zero], auto)
  fix i assume i:"i : Ord" and "i < \<mu>" 
  then obtain j where j:"j : Ord" and "j < \<mu>" "i < j" using lt by auto
  show "succ i < \<mu>" by (rule lt_trans1[OF succ_ord[OF i] j \<mu> succ_leqI[OF i j \<open>i < j\<close>] \<open>j < \<mu>\<close>])
qed

subsection \<open>Trichotomy of Ordinals, Transfinite Induction\<close>

lemma ord_cases_disj :
  assumes "i : Ord"
  shows "i = 0 \<or> (\<exists>j : Ord. i = succ j) \<or> i : Limit"
  using limitI neq_zero_lt assms 
  by auto 

lemma ord_cases : 
  assumes "i : Ord"
  obtains (zero) "i = 0" 
        | (succ) j where "j : Ord" "i = succ j" 
        | (limit) "i : Limit"
  using ord_cases_disj[OF assms]
  by auto

lemma trans_induct [consumes 1, case_names step] :
  assumes "i : Ord" "\<And>j. j : Ord \<Longrightarrow> (\<And>k. k : Ord \<Longrightarrow> k < j \<Longrightarrow> P k) \<Longrightarrow> P j" 
  shows "P i"
  using lt_induct assms unfolding tall_def 
  by auto 

lemma trans_induct3 [case_names zero succ lim, consumes 1] :
  assumes "i : Ord" 
     and zero: "P 0" 
     and succ: "\<And>j. \<lbrakk> j : Ord; P j \<rbrakk> \<Longrightarrow> P (succ j)"
     and lim : "\<And>\<mu>. \<lbrakk> \<mu> : Limit; \<forall>j : Ord. j < \<mu> \<longrightarrow> P j \<rbrakk> \<Longrightarrow> P \<mu>"
   shows "P i" 
proof (rule trans_induct[OF \<open>i : Ord\<close>])
  fix j assume j:"j : Ord" 
  and IH: "\<And>k. k : Ord \<Longrightarrow> k < j \<Longrightarrow> P k"
  show "P j" proof (rule ord_cases[OF j])
    assume "j = 0" thus "P j" using zero by auto
  next
    fix k assume "k : Ord" "j = succ k"
    hence "k < j" using succ_lt by auto
    thus "P j" using IH[OF \<open>k : Ord\<close>] succ[OF \<open>k : Ord\<close>] \<open>j = succ k\<close> by auto
  next
    assume "j : Limit"
    thus "P j" using lim IH by auto
  qed
qed  



subsection \<open>\<omega> - The Smallest Limit Ordinal\<close>

thm omega_typ

lemma omega_ord : "\<omega> : Ord" by (rule limit_ord[OF omega_typ])
lemma omega_zero : "0 < \<omega>" by (rule limit_lt_zero[OF omega_typ])

lemma omega_succ :
  assumes i:"i : Ord" 
  shows "i < \<omega> \<Longrightarrow> succ i < \<omega>"
  by (rule limit_lt_succ[OF omega_typ i])

(* lemma omega_one : "1 < \<omega>" unfolding one_def
  by (rule omega_succ[OF zero_typ omega_zero]) *)

lemma omega_lt_cases :
  assumes i:"i : Ord" and lt:"i < \<omega>"
  obtains (zero) "i = 0" | (succ) j where "j : Ord" "i = succ j"
proof (rule ord_cases[OF i], auto, rule ccontr)
  assume "i : Limit" hence "\<omega> < i" 
    using lt_neq[OF i omega_ord lt] omega_ax by auto
  thus "False" using lt asym[OF i omega_ord] by auto
qed

lemma omega_lt_not_limit :
  assumes i:"i : Ord" and lt:"i < \<omega>" 
  shows "\<not> i : Limit"
  by (rule omega_lt_cases[OF i lt], 
      use not_zero_limit not_succ_limit in auto)


subsection \<open>Least Ordinal operator\<close>

definition least :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" (binder \<open>least \<close> 10)
  where "least x. P x \<equiv> \<iota> i. i : Ord \<and> P i \<and> (\<forall>j : Ord. j < i \<longrightarrow> \<not> P j) else Ordinal_default"

lemma least_eq :
  assumes i:"i : Ord" and "P i"
    and lt:"\<And>j. j : Ord \<Longrightarrow> j < i \<Longrightarrow> \<not> P j"
  shows "(least i. P i) = i" unfolding least_def
proof (rule the_def_eq, use assms in auto)
  fix k assume k:"k : Ord" and "P k" and j:"\<forall>j. j : Ord \<longrightarrow> j < k \<longrightarrow> \<not> P j"
  show "k = i" by (rule linear[OF k i], use i k \<open>P i\<close> \<open>P k\<close> lt j in auto)
qed

lemma least_ord : 
  assumes i:"i : Ord"
  shows "P i \<Longrightarrow> (least i. P i) : Ord"
proof (induct rule: trans_induct[OF i])
  fix j assume j:"j : Ord" and "P j"
  and k:"\<And>k. k : Ord \<Longrightarrow> k < j \<Longrightarrow> P k \<Longrightarrow> (least i. P i) : Ord"
  show "(least i. P i) : Ord"
  proof (cases "(least i. P i) : Ord")
    case True 
    then show ?thesis .
  next
    case False
    hence "\<And>k. k : Ord \<Longrightarrow> k < j \<Longrightarrow> \<not> P k" using k by auto
    hence "(least i. P i) = j" using k least_eq[OF j, of P, OF \<open>P j\<close>] by auto
    then show ?thesis using \<open>j : Ord\<close> by auto
  qed
qed


lemma leastI : 
  assumes i:"i : Ord"
  shows "P i \<Longrightarrow> P (least i. P i)"
proof (induct rule: trans_induct[OF i])
  fix j assume j:"j : Ord" and "P j"
  and k:"\<And>k. k : Ord \<Longrightarrow> k < j \<Longrightarrow> P k \<Longrightarrow> P (least i. P i)"
  show "P (least i. P i)"
  proof (cases "P (least i. P i)")
    case True 
    then show ?thesis .
  next
    case False
    hence "\<And>k. k : Ord \<Longrightarrow> k < j \<Longrightarrow> \<not> P k" using k by auto
    hence "(least i. P i) = j" using k least_eq[OF j, of P, OF \<open>P j\<close>] by auto
    then show ?thesis using \<open>P j\<close> by auto
  qed
qed

(*MESSY PROOF: needs tidying*)
lemma least_leqI :
  assumes i:"i : Ord"
  shows "P i \<Longrightarrow> (least i. P i) \<le> i"
proof (induct rule: trans_induct[OF i]) 
  fix j assume j:"j : Ord" and "P j"
  and k : "\<And>k. k : Ord \<Longrightarrow> k < j \<Longrightarrow> P k \<Longrightarrow> (least i. P i) \<le> k"
  show "(least i. P i) \<le> j" 
  proof (cases "(least i. P i) \<le> j")
    case True
    then show ?thesis .
  next
    case False
    hence kj: "\<And>k. k : Ord \<Longrightarrow> k < j \<Longrightarrow> \<not> (least i. P i) \<le> j" using k by auto
    have "(least i. P i) = j" 
    proof (rule least_eq[OF j, of P, OF \<open>P j\<close>])
      fix k assume "k : Ord" "k < j" 
      hence lj:"\<not> (least i. P i) \<le> j" using kj by auto
      show "\<not> P k" proof
        assume "P k" hence l:"(least i. P i) : Ord" using least_ord[OF \<open>k : Ord\<close>] by auto
        have pk:"(least i. P i) \<le> k" using k[OF \<open>k : Ord\<close> \<open>k < j\<close> \<open>P k\<close>] by auto
        show "False" using leqI1[OF l j lt_trans1[OF l \<open>k : Ord\<close> j pk \<open>k < j\<close>]] lj by auto
      qed
    qed
    then show ?thesis using leq_refl[OF j] by auto
  qed
qed

lemma lt_leastE :
  assumes i:"i : Ord" and "P i"
    and lt : "i < (least i. P i)"
  shows "Q"
  using lt_trans2[OF i least_ord[OF i, of P, OF \<open>P i\<close>] i lt least_leqI[OF i, of P, OF \<open>P i\<close>]]  
        not_refl[OF i]
  by auto

(*Easier to apply than leastI: conclusion has only one occurrence of P*)
lemma leastI2 :
  assumes i:"i : Ord" and "P i"
  and lt: "\<And>j. j : Ord \<Longrightarrow> P j \<Longrightarrow> Q j"
  shows "Q (least j. P j)"
  by (rule lt[OF least_ord[of i P, OF i \<open>P i\<close>] 
                 leastI[of i P, OF i \<open>P i\<close>]])

lemma least_default :
  "\<not> (\<exists>i : Ord. P i) \<Longrightarrow> (least i. P i) = Ordinal_default"
  unfolding least_def tex_def
  by (rule the_def_default, auto)

end
end