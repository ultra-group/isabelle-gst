theory Function_Model_Base
  imports "../../ModelKit/ModelComponents" "../../GZF/Model/GZF_Model"
begin

context GZF_Model begin
ML \<open>val func_model = mcomp 
  { name = "Function_Model",
    deps = mcomps [set_model],
    variant = SOME (vari
      { tag_name = "func",
          vcases =
            (\<^term>\<open>\<emptyset>\<close>,
             \<^term>\<open>(\<lambda>_ x. x \<midarrow>p\<rightarrow> x) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>,
             \<^term>\<open>(\<lambda>_ _. \<emptyset>) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a \<close>),
       alpha_typ = \<^term>\<open>Function\<close>}),
    excludes_formulas = 
      [("func_not_excluded", \<^prop>\<open>\<not> Excluded func <func,f'>\<close>),
       ("func_set_excluded", \<^prop>\<open>Excluded set << Excluded func\<close>)] }\<close>
end

local_setup \<open>snd o (mk_mcomp_class func_model)\<close>

lemma func_model_case_typ :
  assumes j : "j : Ord" and x : "x : Set" 
  shows "caseof_ord \<emptyset> (x \<midarrow>p\<rightarrow> x) \<emptyset> j : SetOf Function"
  by (rule case_ordE[OF j], 
      use fspace_setof[OF x x] emp_setof in auto)


context Function_Model begin

definition mFunc :: \<open>'a \<Rightarrow> bool\<close>
  where "mFunc \<equiv> M \<triangle> \<^enum> func"

definition mapp :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where "mapp f x y \<equiv> app (snd f) x y"



subsection \<open>Lemmas about structure of Tier\<close>

theorem variants_func :
  shows "Variants func 0 \<emptyset> = \<emptyset>"
    and "j : Ord   \<Longrightarrow> Variants func (succ j) x = x \<midarrow>p\<rightarrow> x"
    and "\<mu> : Limit \<Longrightarrow> Variants func \<mu> f = \<emptyset>"
  using v_func_0 v_func_succ v_func_limit by auto

theorem tierI_mfunc :
  assumes j : "j : Ord" and f' : "f' : Function"
      and dom : "dom f' \<subseteq> (Tier j \<ominus> func)" 
      and ran : "ran f' \<subseteq> (Tier j \<ominus> func)"
    shows "<func, f'> \<in> Tier (succ j)"
    using fspaceI[OF tier_ex_set[OF j] tier_ex_set[OF j] f' dom ran]
          tier_succI2[OF func_tag j]
    unfolding variants_func(2)[OF j] by auto

theorem tierD_mfunc :
  assumes j : "j : Ord" 
      and f : "<func, f'> \<in> Tier (succ j)"
    shows "f' \<in> (Tier j \<ominus> func) \<midarrow>p\<rightarrow> (Tier j \<ominus> func)"
proof (rule tier_succE_pair[OF j f])
  show "\<langle>func,f'\<rangle> \<in> Tier j \<Longrightarrow> 
    f' \<in> (Tier j \<ominus> func) \<midarrow>p\<rightarrow> Tier j \<ominus> func"
  proof (induct rule: trans_induct3[OF j])
    case 1 then show ?case
      using tier0D(2) variants_func(1) 
      by auto
  next
    case IH: (2 j) 
  { assume f':"f' \<in> (Tier j \<ominus> func) \<midarrow>p\<rightarrow> (Tier j \<ominus> func)"
    hence "f' \<in> (Tier (succ j) \<ominus> func) \<midarrow>p\<rightarrow> (Tier (succ j) \<ominus> func)"
      using fspace_trans[OF tier_ex_set tier_ex_set tier_ex_set tier_ex_set,
                         OF IH(1) IH(1) succ_ord[OF IH(1)] succ_ord[OF IH(1)],
                         OF tier_ex_subset_succ[OF IH(1)] tier_ex_subset_succ[OF IH(1)]]
      by auto }
  thus ?case 
    by (rule tier_succE_pair[OF IH(1,3)],
        unfold variants_func(2)[OF IH(1)], meson IH(2))
  next
  case IH : (3 \<mu>)
  show ?case
  proof (rule tier_limE_pair[OF \<open>\<mu> : Limit\<close> \<open><func,f'> \<in> Tier \<mu>\<close>])
      fix j assume 
        j:"j : Ord" and "j < \<mu>" "<func,f'> \<in> Tier j"
      hence "f' \<in> (Tier j \<ominus> func) \<midarrow>p\<rightarrow> (Tier j \<ominus> func)" using IH(2) by auto 
      thus "f' \<in> (Tier \<mu> \<ominus> func) \<midarrow>p\<rightarrow> (Tier \<mu> \<ominus> func)" 
        using fspace_trans[OF tier_ex_set tier_ex_set tier_ex_set tier_ex_set,
                           OF j j limit_ord[OF IH(1)] limit_ord[OF IH(1)],
                           OF tier_limit_ex_subset[OF IH(1) j \<open>j < \<mu>\<close>] 
                              tier_limit_ex_subset[OF IH(1) j \<open>j < \<mu>\<close>]]
        by auto
    next
      show "f' \<in> Variants func \<mu> (\<lambda>j<\<mu>. Tier j \<ominus> func) \<Longrightarrow> 
        f' \<in> (Tier \<mu> \<ominus> func) \<midarrow>p\<rightarrow> Tier \<mu> \<ominus> func "
        unfolding variants_func(3)[OF \<open>\<mu> : Limit\<close>] by auto
    qed
  qed
next
  assume "f' \<in> Variants func (succ j) (Tier j \<ominus> func)"
  thus "f' \<in> (Tier j \<ominus> func) \<midarrow>p\<rightarrow> (Tier j \<ominus> func)"
    unfolding variants_func(2)[OF j] .
qed

theorem mI_mfunc :
  assumes j : "j : Ord"
      and f' : "f' : Function"
      and dom : "dom f' \<subseteq> (Tier j \<ominus> func)" 
      and ran : "ran f' \<subseteq> (Tier j \<ominus> func)"
    shows "<func, f'> : M"
 using mI[OF succ_ord[OF j] tierI_mfunc[OF j f' dom ran]] .

theorem mE_mfunc_pair :
  assumes f : "<func, f'> : M"
  obtains j where 
    "j : Ord" "f' \<in> (Tier j \<ominus> func) \<midarrow>p\<rightarrow> (Tier j \<ominus> func)"
  by (rule m_cases_pair[OF f], use variants_func in auto)   
  
lemma ex_func_set : 
  assumes x : "x : Set" and b :"b \<in> x \<ominus> func"
    shows "b \<in> x \<ominus> set"
  using exsetI[OF x exsetD1[OF x b]] exsetD2[OF x b]   
        subtypE[OF func_set_excluded]
  unfolding has_ty_def by auto

lemma ex_func_set_subset : 
  assumes x : "x : Set"
  shows "x \<ominus> func \<subseteq> x \<ominus> set"
  using ex_func_set[OF x] by auto

lemma ex_func_set_trans : 
  assumes y : "y : Set" 
  shows "x \<subseteq> y \<ominus> func \<Longrightarrow> x \<subseteq> y \<ominus> set"
  using ex_func_set[OF y] by auto

subsection \<open>mFunc\<close>

lemma mfunc_m : 
  "f : mFunc \<Longrightarrow> f : M"
  unfolding mFunc_def by unfold_typs

lemma mfuncI :
  assumes f : "<func, f'> : M"
    shows "<func, f'> : mFunc"
  using f partI[OF _ m_pair] 
  unfolding mFunc_def by (auto intro: intI)

lemma mfuncE1 :
  assumes "f : mFunc"
  obtains f' where "f = <func, f'>"
  using assms partE
  unfolding mFunc_def inter_ty_def has_ty_def by blast

theorem mfuncE2 :
  assumes f : "f : mFunc"
  obtains f' j where 
    "f' : Function" "f = <func, f'>" 
    "j : Ord" "dom f' \<subseteq> Tier j \<ominus> func" "ran f' \<subseteq> Tier j \<ominus> func"
proof (rule mfuncE1[OF f])
  fix f' assume 
    f_eq : "f = <func, f'>"
  then obtain j where 
    j : "j : Ord" and "f' \<in> (Tier j \<ominus> func) \<midarrow>p\<rightarrow> (Tier j \<ominus> func)"
    using mE_mfunc_pair[OF mfunc_m] f by auto
  hence f' : "f' : Function" 
    and dom_ran : "dom f' \<subseteq> Tier j \<ominus> func" "ran f' \<subseteq> Tier j \<ominus> func"
    using fspaceD fspace_mem tier_ex_set by (blast, blast, blast)
  
   from f' f_eq j dom_ran show ?thesis ..
qed

lemma mfunc_snd_eq :
  assumes f:"<func, f'> : mFunc"
  shows "snd <func, f'> = f'"
  using snd_eq[OF m_pair[OF mfunc_m[OF f]]] .

lemma mfunc_pair_snd_func :
  assumes f:"<func, f'> : mFunc"
    shows "f' : Function"
  by (rule mfuncE2[OF f], 
      use m_pair[OF mfunc_m[OF f]] pair_inject in metis)

lemma mfunc_snd_func : 
  "f : mFunc \<Longrightarrow> snd f : Function"
  using mfuncE1 mfunc_pair_snd_func mfunc_snd_eq by metis

end
end