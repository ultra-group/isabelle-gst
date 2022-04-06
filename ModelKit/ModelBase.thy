theory ModelBase
  imports Tagging "../Functions/Functions"
  (* keywords "model_interpretation" "model_closed" "model_closed'" "base_model" "build_model" :: thy_goal  *)
begin

class ModelBase = Tagging + Function +
  fixes
    Variants :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" and
    \<alpha> :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> and
    Excluded :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    
  assumes 
    variants_typ1 : "Variants : (\<Pi> i : Tag. nonLimit \<rightarrow> Set \<rightarrow> SetOf (\<alpha> i))" and
    variants_typ2 : "Variants : (\<Pi> i : Tag. Limit \<rightarrow> Function \<rightarrow> SetOf (\<alpha> i))" and
    smem_fmem_subtyp : "SetMem << FunMem"

context ModelBase begin

subsection \<open>Soft-typing rules for Variants\<close>

lemmas smem_fmem = subtypE[OF smem_fmem_subtyp]
lemmas ord_fmem = smem_fmem[OF ord_setmem]
lemmas tag_pmem = ord_pmem[OF tagD(1)]

lemma variants_setofseq1 :
  assumes j:"j : nonLimit" and x:"x : Set"
  shows "(\<lambda>i. Variants i j x) : (\<Pi> i : Tag. SetOf (\<alpha> i))"
  by (rule depfunI, 
      use funE[OF funE[OF depfunE[OF variants_typ1]]] j x in auto)

lemma variants_setof :
  assumes i:"i : Tag" and j:"j : nonLimit" and x : "x : Set"
    shows "Variants i j x : SetOf (\<alpha> i)"
  by (rule depfunE[OF variants_setofseq1[OF j x] i])

lemmas variants_set = setof_set[OF variants_setof]

lemma variants_setseq1 :
  assumes j:"j : nonLimit" and x:"x : Set"
  shows "(\<lambda>i. Variants i j x) : (\<Pi> i : Tag. Set)"
  by (rule depfunI, rule variants_set[OF _ j x])

lemma variants_setofseq2 :
  assumes j:"j : Limit" and f:"f : Function"
  shows "(\<lambda>i. Variants i j f) : (\<Pi> i : Tag. SetOf (\<alpha> i))"
  by (rule depfunI, 
      use funE[OF funE[OF depfunE[OF variants_typ2]]] j f in auto)

lemma variants_setof2 :
  assumes i:"i : Tag" and j:"j : Limit" and f:"f : Function"
    shows "Variants i j f : SetOf (\<alpha> i)"
  by (rule depfunE[OF variants_setofseq2[OF j f] i])

lemmas variants_set2 = setof_set[OF variants_setof2]

lemma variants_setseq2 :
  assumes j:"j : Limit" and x:"x : Function"
  shows "(\<lambda>i. Variants i j x) : (\<Pi> i : Tag. Set)"
  by (rule depfunI, rule variants_set2[OF _ j x])


subsection \<open>Operator for removing Excluded stuff from a set\<close>

definition RemoveExcluded :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix \<open>\<ominus>\<close> 60)
  where "RemoveExcluded x i \<equiv> { b \<in> x | \<not> Excluded i b }"

lemma exset_set : 
  assumes "x : Set" 
  shows "x \<ominus> i : Set"
  unfolding RemoveExcluded_def 
  by (rule collect_set[OF assms])

lemma exset_iff : 
  assumes "x : Set" 
  shows "b \<in> x \<ominus> i \<longleftrightarrow> b \<in> x \<and> \<not> Excluded i b"
  unfolding RemoveExcluded_def 
  using collect_iff[OF assms] by auto

lemma exsetI : 
  assumes x:"x : Set" 
      and b:"b \<in> x" "\<not> Excluded i b"
    shows "b \<in> x \<ominus> i"
  unfolding RemoveExcluded_def 
  using collectI[OF x] b by auto

lemma exsetD1 : 
  assumes x:"x : Set" and b:"b \<in> x \<ominus> i"
  shows "b \<in> x"
  using exset_iff x b by auto

lemma exsetD2 : 
  assumes x:"x : Set" and b:"b \<in> x \<ominus> i"
  shows "\<not> Excluded i b"
  using exset_iff x b by auto

lemma exsetD_conj : 
  assumes x:"x : Set" and b:"b \<in> x \<ominus> i"
  shows "b \<in> x \<and> \<not> Excluded i b"
  using exset_iff x b by auto

lemma exsetE :
  assumes x:"x : Set" and b:"b \<in> x \<ominus> i"
  obtains "b \<in> x" "\<not> Excluded i b"
  using exset_iff x b by auto


lemma ex_subset1 : 
  assumes x:"x : Set" and y:"y : Set"
      and sub:"x \<subseteq> y" 
    shows "a \<subseteq> x \<ominus> i \<Longrightarrow> a \<subseteq> y \<ominus> i"
  using subset_iff exset_iff x y sub 
  by auto

lemma ex_subset2 : 
  assumes x:"x : Set" and y:"y : Set" 
    shows "x \<subseteq> y \<ominus> i \<Longrightarrow> x \<subseteq> y"
  using subset_iff exset_iff x y 
  by auto

  
section \<open>Tier -- model building operator\<close>

abbreviation Tier_zero :: 'a
  where "Tier_zero \<equiv> \<Uplus> (\<lambda>i. Variants i 0 \<emptyset>)"

abbreviation Tier_succ :: "['a, 'a] \<Rightarrow> 'a"
  where "Tier_succ j x \<equiv> x \<union> \<Uplus> (\<lambda>i. Variants i j (x \<ominus> i))"

abbreviation Tier_lim :: "['a, 'a \<Rightarrow> 'a] \<Rightarrow> 'a"
  where "Tier_lim \<mu> f \<equiv> (\<Union> {f j | j < \<mu>}) 
                      \<union> \<Uplus> (\<lambda>i. Variants i \<mu> (\<lambda>j<\<mu>. f j \<ominus> i))"

definition Tier :: "'a \<Rightarrow> 'a" where
 "Tier \<equiv> OrdRec Tier_lim Tier_succ Tier_zero"

lemma tier_cases : 
  shows "Tier 0 = Tier_zero" 
    and "j : Ord \<Longrightarrow> Tier (succ j) = Tier_succ (succ j) (Tier j)"
    and "\<mu> : Limit \<Longrightarrow> Tier \<mu> = Tier_lim \<mu> (\<lambda>j. if j < \<mu> then Tier j else OrdRec_default)"
  unfolding Tier_def 
  by (simp add: ordrec_0, use ordrec_succ ordrec_lim in auto)

subsection \<open>All Tiers are sets\<close>

lemma tier_zero_set : 
  "Tier 0 : Set" 
  unfolding tier_cases(1) 
  by (rule disj_set[OF variants_setseq1[OF zero_nonlimit emp_set]])

lemma variants_succ_setseq :
  assumes j:"j : Ord" and x:"x : Set"   
    shows "(\<lambda>i. Variants i (succ j) (x \<ominus> i)) : (\<Pi> i : Tag. Set)"
proof (rule depfunI)
  fix i assume "i : Tag"
  thus "Variants i (succ j) (x \<ominus> i) : Set" 
  by (rule depfunE[OF variants_setseq1[OF succ_nonlimit[OF j] exset_set[OF x, of]], of i i])
qed
  
lemma tier_succ_set_ih :
  assumes j:"j : Ord"
      and tj : "Tier j : Set"
  shows "Tier (succ j) : Set"
  unfolding tier_cases(2)[OF j]
  by (rule un_set[OF tj disj_set[OF variants_succ_setseq[OF j tj]]])

lemma limit_fmem : 
  assumes \<mu>:"\<mu> : Limit"
  shows "predSet \<mu> : SetOf FunMem"
  using setofI[OF predset_set] ord_fmem[OF predset_mem_ord] limit_ord[OF \<mu>] by auto
      
lemma tier_fmem' : 
  assumes \<mu>:"\<mu> : Limit"
      and t\<mu> : "\<And>j. j : Ord \<Longrightarrow> j < \<mu> \<Longrightarrow> Tier j : Set"  
    shows "Tier : predSet \<mu> \<leadsto> FunMem"
proof (rule mem_funI)
  fix j assume "j \<in> predSet \<mu>" 
  hence "j : Ord" "j < \<mu>" 
    using predsetD[OF limit_ord[OF \<mu>]] by auto
  thus "Tier j : FunMem" using smem_fmem[OF set_setmem[OF t\<mu>]] by auto
qed

lemma tier_lim_set : 
  assumes \<mu>:"\<mu> : Limit"
      and t\<mu> : "\<And>j. j : Ord \<Longrightarrow> j < \<mu> \<Longrightarrow> Tier j : Set"  
    shows "Tier : MemOf (predSet \<mu>) \<rightarrow> Set"
 by (rule funI, drule memofD, drule predsetD[OF limit_ord[OF \<mu>]], 
     use t\<mu> in auto)
 
lemma tier_replfun' : 
  assumes \<mu> : "\<mu> : Limit"
      and t\<mu> : "\<And>j. j : Ord \<Longrightarrow> j < \<mu> \<Longrightarrow> Tier j : Set"  
    shows "Tier : (predSet \<mu>) \<leadsto> Set"
  by (rule mem_funI, use predsetD[OF limit_ord[OF \<mu>]] t\<mu> in auto)
  
(* lemma lam_tier_replfun' : 
  assumes \<mu> : "\<mu> : Limit"
      and t\<mu> : "\<And>j. j : Ord \<Longrightarrow> j < \<mu> \<Longrightarrow> Tier j : Set"  
  defines "t \<equiv> (\<lambda>j<\<mu>. Tier j)" 
    shows "(\<lambda>j. t ` j) : ReplFun (predSet \<mu>) Ord Set"
 unfolding ReplFun_def 
proof (rule intI[OF setfunI funI])
  fix j assume "j \<in> predSet \<mu>"
  hence "j : Ord" "j < \<mu>" "t ` j = Tier j" 
    unfolding t_def
    using predsetD[OF limit_ord[OF \<mu>]] 
          lam_app[OF limit_fmem[OF \<mu>] tier_fmem'[OF \<mu> t\<mu>]] by auto
  thus "t ` j : SetMem" using set_setmem t\<mu> by auto     
next
  fix j assume j:"j : (Ord \<bar> MemOf (predSet \<mu>))" 
  hence "j : Ord" "j < \<mu>" "t ` j = Tier j" 
  unfolding t_def
  using intE[OF j] memofD predsetD[OF limit_ord[OF \<mu>]] 
        lam_app[OF limit_fmem[OF \<mu>] tier_fmem'[OF \<mu> t\<mu>]]
    by auto
  thus "t ` j : Set" using t\<mu> by auto
qed       *)

lemma variants_limit_setseq' : 
  assumes \<mu> : "\<mu> : Limit"
  defines "t \<equiv> (\<lambda>j. if j < \<mu> then Tier j else OrdRec_default)" 
  shows "(\<lambda>i. Variants i \<mu> (\<lambda>j<\<mu>. t j \<ominus> i)) : (\<Pi> i : Tag. Set)"
proof (rule depfunI)
  fix i assume i:"i : Tag"
  have "(\<lambda>j<\<mu>. t j \<ominus> i) : Function"
    by (rule lam_fun[OF predset_set[OF limit_ord[OF \<mu>]]])
  thus "Variants i \<mu> (\<lambda>j<\<mu>. t j \<ominus> i) : Set"
    by (rule depfunE[OF variants_setseq2[OF \<mu> _] i])
qed

lemma tier_lim_set_ih : 
  assumes \<mu>:"\<mu> : Limit"
      and t\<mu> : "\<And>j. j : Ord \<Longrightarrow> j < \<mu> \<Longrightarrow> Tier j : Set"  
    shows "Tier \<mu> : Set"
  unfolding tier_cases(3)[OF \<mu>]
proof (rule un_set[OF union_set])
  let ?L = "\<lambda>j. if j < \<mu> then Tier j else OrdRec_default"
  show "{ ?L j | j<\<mu> } : SetOf Set"
  by (rule repfun_ord_setof[OF limit_ord[OF \<mu>] mem_funI], 
      drule predsetD[OF limit_ord[OF \<mu>]], use t\<mu> in auto)
  show "\<Uplus> (\<lambda>i. Variants i \<mu> (\<lambda>j<\<mu>. ?L j \<ominus> i)) : Set"
  by (rule disj_set[OF variants_limit_setseq'[OF \<mu>]])
qed    

theorem tier_set : 
  "j : Ord \<Longrightarrow> Tier j : Set"
  by (erule trans_induct3, 
      use tier_zero_set tier_succ_set_ih tier_lim_set_ih in auto)

lemma tier_ex_set : 
  "j : Ord \<Longrightarrow> Tier j \<ominus> i : Set"
  by (rule exset_set[OF tier_set])
 
lemma tier_fmem : 
  assumes \<mu>:"\<mu> : Limit"
    shows "Tier : (predSet \<mu>) \<leadsto> FunMem"
  using tier_fmem'[OF \<mu> tier_set] by auto

lemma tier_replfun : 
  assumes \<mu> : "\<mu> : Limit"
  shows "Tier : (predSet \<mu>) \<leadsto> Set"
  using tier_replfun'[OF \<mu> tier_set] by auto

lemmas lim_predset_set = predset_set[OF limit_ord]

lemma tier_restrict_replfun : 
  assumes \<mu> : "\<mu> : Limit"
  shows "(\<lambda>j. if j < \<mu> then Tier j else OrdRec_default) : (predSet \<mu>) \<leadsto> Set"
  by (rule mem_funI, frule predsetD[OF limit_ord[OF \<mu>]],
      use mem_funE[OF tier_replfun[OF \<mu>]] in auto)   

lemma lam_tier_restrict_eq : 
  assumes \<mu> : "\<mu> : Limit"
  shows "(\<lambda>j<\<mu>. (\<lambda>j. if j < \<mu> then Tier j else OrdRec_default) j \<ominus> i) = (\<lambda>j<\<mu>. Tier j \<ominus> i)"
  by (rule lam_cong[OF lim_predset_set[OF \<mu>]], 
      drule predsetD[OF limit_ord[OF \<mu>]], auto)


(* lemma lam_tier_replfun : 
  assumes \<mu> : "\<mu> : Limit"
  defines "t \<equiv> (\<lambda>j<\<mu>. Tier j)" 
  shows "(\<lambda>j. t ` j) : ReplFun (predSet \<mu>) Ord Set"
  unfolding t_def
  using lam_tier_replfun'[OF \<mu> tier_set] by auto *)

lemma lam_limit_fun : 
  assumes "u : Limit"
  shows "(\<lambda>i<u. F i) : Function"
    using lam_fun[OF predset_set[OF limit_ord[OF assms]]] .

lemma lam_tier_app : 
  assumes \<mu>:"\<mu> : Limit" 
      and j:"j : Ord" "j < \<mu>"
    shows "(\<lambda>j<\<mu>. Tier j) ` j = Tier j"
  using lam_app[OF predset_set[OF limit_ord[OF \<mu>]] tier_fmem[OF \<mu>]] 
        predsetI[OF \<open>j : Ord\<close> limit_ord[OF \<mu>] \<open>j < \<mu>\<close>] 
        ord_fmem[OF j(1)] by auto

(* lemma lam_tier_ex_eq : 
  assumes \<mu>:"\<mu> : Limit" 
  shows "(\<lambda>j<\<mu>. (\<lambda>j<\<mu>. Tier j) ` j \<ominus> i) = (\<lambda>j<\<mu>. Tier j \<ominus> i)"
proof (rule lam_cong[OF limit_fmem[OF \<mu>]], rule funI, drule memofD, drule predsetD[OF limit_ord[OF \<mu>]])
  fix j assume "j : Ord \<and> j < \<mu>"
  thus "(\<lambda>j<\<mu>. Tier j) ` j \<ominus> i : FunMem" 
    using smem_fmem[OF set_setmem[OF exset_set[OF tier_set]]]  
          lam_tier_app[OF \<mu>] by auto
next
  show "(\<lambda>b. Tier b \<ominus> i) : MemOf (predSet \<mu>) \<rightarrow> FunMem"
    by (rule funI, drule memofD, drule predsetD[OF limit_ord[OF \<mu>]], 
       rule smem_fmem[OF set_setmem[OF exset_set[OF tier_set]]], auto)
next
  fix j assume "j \<in> predSet \<mu>"
  hence "j : Ord" "j < \<mu>" using predsetD[OF limit_ord[OF \<mu>]] by auto
  thus "(\<lambda>j<\<mu>. Tier j) ` j \<ominus> i = Tier j \<ominus> i" using lam_tier_app[OF \<mu>] by auto
qed *)



lemma lam_tier_fun :
  assumes \<mu>:"\<mu> : Limit"
    shows "(\<lambda>j<\<mu>. Tier j) : Function"
 using lam_fun[OF lim_predset_set[OF \<mu>]] .

lemma lam_tier_ex_fun :
  assumes \<mu>:"\<mu> : Limit"
    shows "(\<lambda>j<\<mu>. Tier j \<ominus> i) : Function"
  using lam_limit_fun[OF \<mu>] .
        
lemma ord_ex_iff :
  assumes i:"i : Ord"
  shows "(\<exists>j\<in>predSet i. P j) \<longleftrightarrow> (\<exists>j<i. P j)"
  unfolding bex_def rex_def tex_def
  using predsetI predsetD i
  by metis
  
lemma variants_limit_setseq :
  assumes \<mu> : "\<mu> : Limit"
  defines "t \<equiv> (\<lambda>j. if j < \<mu> then Tier j else OrdRec_default)" 
  shows "(\<lambda>i. Variants i \<mu> (\<lambda>j<\<mu>. t j \<ominus> i)) : (\<Pi> i : Tag. Set)"
  unfolding t_def
  using variants_limit_setseq'[OF \<mu> ] .


subsection \<open>Rules for Tiers\<close>

subsubsection \<open>Tier 0\<close>

lemma variants0_pair :
  assumes i : "i : Tag" and b' : "b' \<in> Variants i 0 \<emptyset>" 
    shows "<i,b'> : Pair"
  using pair_pair[OF tag_pmem[OF i] smem_pmem[OF setmemI]]
        variants_set[OF i zero_nonlimit emp_set] b' 
  by auto

lemma tier0_iff : 
  "b \<in> Tier 0 \<longleftrightarrow> (\<exists> i : Tag. \<exists>b' \<in> Variants i 0 \<emptyset>. b : Pair \<and> b = <i,b'>)"
  unfolding tier_cases(1) 
  by (rule disj_iff[OF variants_setseq1[OF zero_nonlimit emp_set]])

lemma tier0I :
  assumes i:"i : Tag" and b':"b' \<in> Variants i 0 \<emptyset>"
    shows "<i,b'> \<in> Tier 0" 
proof - 
  have "<i,b'> : Pair" 
    using pair_pair[OF tag_pmem[OF i(1)] smem_pmem[OF setmemI]]
          variants_set[OF i zero_nonlimit emp_set] b' by metis
  thus "<i,b'> \<in> Tier 0" unfolding tier0_iff using i b' by auto
qed

lemma tier0E :
  assumes b:"b \<in> Tier 0"
  obtains i b' where "i : Tag" "b' \<in> Variants i 0 \<emptyset>" "b : Pair" "b = <i,b'>" 
  using b unfolding tier0_iff by auto

lemma tier0D : 
  assumes b:"<i,b'> \<in> Tier 0"
  shows "i : Tag" "b' \<in> Variants i 0 \<emptyset>" "<i,b'> : Pair" 
proof -
  from tier0E[OF b] obtain j c' 
    where "j : Tag" "c' \<in> Variants j 0 \<emptyset>" "<j,c'> : Pair" "<i,b'> = <j,c'>" 
    by metis
  moreover hence "i = j" "b' = c'" using pair_inject by auto
  ultimately show "i : Tag" "b' \<in> Variants i 0 \<emptyset>" "<i,b'> : Pair" by auto
qed

subsubsection \<open>Tier 'succ'\<close>

lemma variants_succ_pair :
  assumes i : "i : Tag" and j : "j : Ord"
      and b' : "b' \<in> Variants i (succ j) (Tier j \<ominus> i)" 
    shows "<i,b'> : Pair"
  using pair_pair[OF tag_pmem[OF i(1)] smem_pmem[OF setmemI]]
        variants_set[OF i succ_nonlimit[OF j] tier_ex_set[OF j]] b' 
  by auto

lemma tier_succ_iff :
  assumes j:"j: Ord" 
  shows "b \<in> Tier (succ j) \<longleftrightarrow> b \<in> Tier j \<or> 
          (\<exists>i : Tag. \<exists>b'\<in> Variants i (succ j) (Tier j \<ominus> i). b : Pair \<and> b = <i,b'>)"
  unfolding tier_cases(2)[OF assms] 
            un_iff[OF tier_set[OF j] disj_set[OF variants_succ_setseq[OF j tier_set[OF j]]]] 
            disj_iff[OF  variants_succ_setseq[OF j tier_set[OF j]]]
  by rule

lemma tier_succI1 :
  assumes j : "j  : Ord" 
      and b : "b \<in> Tier j"
    shows "b \<in> Tier (succ j)"
  using tier_succ_iff[OF j] b by auto

lemma tier_succI2 :
  assumes i : "i : Tag" and j : "j : Ord"
    and b' : "b' \<in> Variants i (succ j) (Tier j \<ominus> i)"
  shows "<i,b'> \<in> Tier (succ j)"
  using tier_succ_iff[OF j] i b' 
        variants_succ_pair[OF i j b'] 
  by auto

lemma tier_succE :
  assumes 
    j : "j : Ord" and b : "b \<in> Tier (succ j)"
  obtains (pred) "b \<in> Tier j" 
        | (fresh) i b' where "i : Tag" "b : Pair" "b = <i,b'>" 
                       "b' \<in> Variants i (succ j) (Tier j \<ominus> i)" 
  using b unfolding tier_succ_iff[OF j] 
  by blast 

lemma tier_succE_pair :
  assumes
     j : "j : Ord" and b : "<i,b'> \<in> Tier (succ j)"
   obtains
     (pred)  "<i,b'> \<in> Tier j"
   | (fresh) "b' \<in> Variants i (succ j) (Tier j \<ominus> i)"
  by (erule tier_succE[OF j b], metis pair_inject)

lemma tier_subset_succ :
  assumes j:"j : Ord"
  shows "Tier j \<subseteq> Tier (succ j)"
  using tier_succI1[OF j] by auto

lemma tier_ex_subset_succ :
  assumes j:"j : Ord"
  shows "Tier j \<ominus> i \<subseteq> Tier (succ j) \<ominus> i"
  using ex_subset1[OF tier_set[OF j] tier_set[OF succ_ord[OF j]] tier_subset_succ[OF j] subset_refl] 
  by auto

subsubsection \<open>Tier 'limit'\<close>

lemma variants_limit_pair :
  assumes i : "i : Tag" and \<mu> : "\<mu> : Limit"
      and b' : "b' \<in> Variants i \<mu> (\<lambda>j<\<mu>. Tier j \<ominus> i)" 
    shows "<i,b'> : Pair"
  using pair_pair[OF tag_pmem[OF i(1)] smem_pmem[OF setmemI]]
        variants_set2[OF i \<mu> lam_tier_ex_fun[OF \<mu>]] b'  
  by auto

lemma tier_lim_iff : 
  assumes \<mu>:"\<mu> : Limit"
  shows "b \<in> Tier \<mu> \<longleftrightarrow> (\<exists>j<\<mu>. b \<in> Tier j) 
          \<or> (\<exists> i : Tag. \<exists>b'\<in> Variants i \<mu> (\<lambda>j<\<mu>. Tier j \<ominus> i). b : Pair \<and> b = <i,b'>)"
  unfolding tier_cases(3)[OF \<mu>] 
            un_iff[OF repfun_union_ord_set[OF limit_ord[OF \<mu>] tier_restrict_replfun[OF \<mu>]]
                      disj_set[OF variants_limit_setseq[OF \<mu>]]]
 unfolding disj_iff[OF variants_limit_setseq[OF \<mu>]]
           repfun_union[OF predset_set[OF limit_ord[OF \<mu>]] tier_restrict_replfun[OF \<mu>]] 
 unfolding lam_tier_restrict_eq[OF \<mu>] tex_def            
           ord_ex_iff[OF limit_ord[OF \<mu>]] by auto


lemma tier_limI1 :
  assumes \<mu> : "\<mu> : Limit" and j : "j : Ord" "j < \<mu>"
      and b : "b \<in> Tier j"
    shows "b \<in> Tier \<mu>"
  unfolding tier_lim_iff[OF \<mu>]
  using b j by auto     

lemma tier_limI2 :
  assumes i : "i : Tag" and \<mu> : "\<mu> : Limit"
      and b : "b' \<in> Variants i \<mu> (\<lambda>j<\<mu>. Tier j \<ominus> i)"
    shows "<i,b'> \<in> Tier \<mu>"
  unfolding tier_lim_iff[OF \<mu>]
  using b i variants_limit_pair[OF i \<mu>] by auto     

lemma tier_limE :
  assumes 
    \<mu> : "\<mu> : Limit" and 
    b : "b \<in> Tier \<mu>"
  obtains (pred)  j where "j : Ord" "j < \<mu>" "b \<in> Tier j" 
        | (fresh) i b' where "i : Tag" "b : Pair" "b = <i,b'>" 
                       "b' \<in> Variants i \<mu> (\<lambda>j<\<mu>. Tier j \<ominus> i)" 
  using b unfolding tier_lim_iff[OF \<mu>] 
  by blast 

lemma tier_limE_pair :
  assumes 
    \<mu> : "\<mu> : Limit" and 
    b : "<i,b'> \<in> Tier \<mu>"
  obtains (pred)  j where "j : Ord" "j < \<mu>" "<i,b'> \<in> Tier j" 
        | (fresh) "b' \<in> Variants i \<mu> (\<lambda>j<\<mu>. Tier j \<ominus> i)" 
  by (erule tier_limE[OF \<mu> b], metis pair_inject)


lemma tier_limit_union :
  assumes \<mu>:"\<mu> : Limit"
  shows "(\<Union> j<\<mu>. Tier j) \<subseteq> Tier \<mu>"
proof 
  fix a assume "a \<in> (\<Union> j<\<mu>. Tier j)"  
  then obtain j where "j : Ord" "j < \<mu>" "a \<in> Tier j"
    using repfun_union[OF lim_predset_set[OF \<mu>] tier_replfun[OF \<mu>]]
          predsetD[OF limit_ord[OF \<mu>]] by auto
  thus "a \<in> Tier \<mu>" 
    unfolding tier_lim_iff[OF \<mu>]
    by auto
qed

lemma tier_limit_subset : 
  assumes \<mu> : "\<mu> : Limit" 
      and j : "j : Ord" "j < \<mu>"
    shows "Tier j \<subseteq> Tier \<mu>" 
    using repfun_union_subset[OF lim_predset_set[OF \<mu>] 
                                 tier_set[OF j(1)] tier_replfun[OF \<mu>]
                                 predsetI[OF j(1) limit_ord[OF \<mu>] j(2)] subset_refl]
           subset_trans[OF _ tier_limit_union[OF \<mu>]] 
    by auto

lemma tier_limit_ex_subset : 
  assumes \<mu> : "\<mu> : Limit" 
      and j : "j : Ord" "j < \<mu>"
    shows "Tier j \<ominus> i \<subseteq> Tier \<mu> \<ominus> i" 
  using ex_subset1[OF tier_set[OF j(1)] tier_set[OF limit_ord[OF \<mu>]]
                      tier_limit_subset[OF assms] subset_refl] 
  by auto


subsection \<open>Tier is a cumulative hierarchy\<close>
(* 
lemma tier_ord :
  assumes j : "j : Ord"
      and b : "b \<in> Tier j" 
  obtains i b' where "i : Tag" "b : Pair" "b = <i,b'>" 
*)

lemma tier_increasing : 
  assumes i:"i : Ord" and j:"j : Ord"
  shows "i < j \<Longrightarrow> Tier i \<subseteq> Tier j"
proof (induct rule: trans_induct3[OF j])
  case 1
  then show ?case 
  using zero_lt[OF i] by auto
next
  case IH:(2 j) 
  show ?case
  proof (rule leqE[OF i \<open>j : Ord\<close> \<open>i \<le> j\<close>])
    assume "i < j" 
    hence "Tier i \<subseteq> Tier j" by (rule IH(2))
    thus "Tier i \<subseteq> Tier (succ j)"
      by (rule subset_trans[OF _ tier_subset_succ[OF \<open>j : Ord\<close>]])
  next
    assume "i = j"
    thus "Tier i \<subseteq> Tier (succ j)"
      using tier_subset_succ[OF i] by auto
  qed
next
  case IH:(3 \<mu>)
  show ?case using tier_limit_subset[OF IH(1) i IH(3)] by simp
qed

lemma greatest_tier : 
  assumes i : "i : Ord" and j : "j : Ord"
      and b : "b \<in> Tier i" and c : "c \<in> Tier j"
  obtains k where "k : Ord" "b \<in> Tier k" "c \<in> Tier k"
proof (rule linear[OF i j])
  assume "i < j" 
  hence "j : Ord" "b \<in> Tier j" "c \<in> Tier j"
    using tier_increasing[OF i j] b c j by auto
  thus ?thesis ..
next
  assume "i = j"
  hence "j : Ord" "b \<in> Tier j" "c \<in> Tier j"
    using j b c by auto
  thus ?thesis ..
next
  assume "j < i"
  hence "i : Ord" "b \<in> Tier i" "c \<in> Tier i"
    using tier_increasing[OF j i] b c i by auto
  thus ?thesis ..  
qed

lemma tier_typ_setof_depsum : 
  "Tier : Ord \<rightarrow> SetOf (\<Sigma> i : Tag. \<alpha> i)"
proof (rule funI, rule setofI[OF tier_set], auto)
  fix j b assume "j : Ord" thus "b \<in> Tier j \<Longrightarrow> b : (\<Sigma> i : Tag. \<alpha> i)"
  proof (induct j rule: trans_induct3)
    case zero show ?case 
    proof (rule tier0E[OF zero], auto, rule depsumI, auto)
      fix i b' 
      assume "i : Tag" and "b' \<in> Variants i 0 \<emptyset>" 
      thus "b' : \<alpha> i" by (rule setof_mem[OF variants_setof[OF _ zero_nonlimit emp_set]])
    qed
  next
    case (succ j)
    show ?case 
    proof (rule tier_succE[OF succ(1,3) succ(2)], auto, 
           rule depsumI, auto)
      fix i b'
      assume "i : Tag" and "b' \<in> Variants i (succ j) (Tier j \<ominus> i)"
      thus "b' : \<alpha> i" 
        using setof_mem[OF variants_setof[OF _ succ_nonlimit tier_ex_set]] \<open>j : Ord\<close> by auto
    qed
  next
    case (lim \<mu>)
    show ?case 
    proof (rule tier_limE[OF \<open>\<mu> : Limit\<close> \<open>b \<in> Tier \<mu>\<close>], use lim(2) in auto,
           rule depsumI, auto)
      fix i b' 
      assume "i : Tag" "b' \<in> Variants i \<mu> (\<lambda>j<\<mu>. Tier j \<ominus> i)"
      thus "b' : \<alpha> i"
        using setof_mem[OF variants_setof2[OF _ lim(1) lam_tier_ex_fun[OF lim(1)]]] by auto
    qed
  qed
qed

lemmas tier_setof_depsum = funE[OF tier_typ_setof_depsum]
lemmas tier_setof_pair = subtypE[OF setof_subtyp[OF depsum_pair_subtyp] tier_setof_depsum] 
lemmas tier_mem_depsum = setof_mem[OF tier_setof_depsum]
lemmas tier_mem_pair = setof_mem[OF tier_setof_pair]

subsection \<open>Part of Tier\<close>

lemma tier0_partI : 
  assumes i : "i : Tag"
      and b : "b = <i,b'>"
      and b': "b' \<in> Variants i 0 \<emptyset>"
  shows "b :\<^enum> i" "b \<in> Tier 0"
  using partI[OF b] tier0I[OF i b'] variants0_pair[OF i b'] b
  by auto

lemma tier0_partE :
  assumes b:"b \<in> Tier 0" "b :\<^enum> i"  
  obtains b' where "i : Tag" 
    "b : Pair" "b = <i,b'>" "b' \<in> Variants i 0 \<emptyset>"  
  by (rule partE[OF b(2)], metis tier0D(1-3) b(1))
  
lemma tier0_partD : 
  assumes ib:"<i,b'> \<in> Tier 0"
  shows "<i,b'> :\<^enum> i"
  using partI[OF _ tier0D(3)[OF ib]] 
  by auto

lemma tier_succ_partI1 : 
  assumes i : "i : Tag" and j : "j : Ord" 
      and b : "<i,b'> \<in> Tier j"
    shows "<i,b'> :\<^enum> i" "<i,b'> \<in> Tier (succ j)"
  using partI tier_succI1[OF j] b tier_mem_pair[OF j b]
  by auto

lemma tier_succ_partI2 : 
  assumes i : "i : Tag" and j : "j : Ord" 
      and b': "b' \<in> Variants i (succ j) (Tier j \<ominus> i)"
      and b : "b = <i,b'>"
    shows "b :\<^enum> i" "b \<in> Tier (succ j)"
  using partI[OF b] tier_succI2[OF i j b'] variants_succ_pair[OF i j b'] b
  by auto

lemma tier_succ_partE : 
  assumes j : "j : Ord" 
      and b : "b \<in> Tier (succ j)" "b :\<^enum> i"
  obtains 
      (pred)  b' where "i : Tag" "b : Pair" "b = <i,b'>" "b \<in> Tier j"
    | (fresh) b' where "i : Tag"
      "b : Pair" "b = <i,b'>" "b' \<in> Variants i (succ j) (Tier j \<ominus> i)" 
proof (rule partE[OF b(2)])
  fix b' assume B: "b : Pair" "b = <i,b'>"
  thus ?thesis 
  proof (cases rule: tier_succE[OF j b(1)])
    case pred : 1
    hence "i : Tag" "b : Pair" "b = <i,b'>" "b \<in> Tier j"
      using depsumD_pair(2)[of i b', OF tier_mem_depsum[OF j]] B 
      by auto
     thus ?thesis ..      
  next
    case fresh:(2 i' c')
    have "i' = i" "c' = b'"
      using pair_inject B fresh(3) by auto
      hence "i : Tag" "b : Pair" "b = <i,b'>" 
        "b' \<in> Variants i (succ j) (Tier j \<ominus> i)"
     using fresh B by auto
     thus ?thesis ..
   qed
qed

end
end