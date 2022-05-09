theory Test
  imports  "../Ordinal/Model/OrdRec_Model" ZFC_in_HOL_Bootstrap      
begin 

ML_file \<open>../ModelKit/Tools/model_implementation.ML\<close>
instance V :: Tagging ..

lemma if_cases : 
  assumes "Q \<Longrightarrow> P x" "\<not> Q \<Longrightarrow> P y"
  shows "P (if Q then x else y)"
  using assms by auto

instantiation V :: ModelBase begin
  (*Call Variants: TierImplementation, change Ordinal_default to \<emptyset> *)
  local_setup \<open>model_implementation \<^typ>\<open>V\<close> [ordrec_model] 
    [\<^term>\<open>\<lambda>x :: V. False\<close>, \<^term>\<open>\<lambda>x :: V. False\<close>]
    [\<^term>\<open>Set :: V \<Rightarrow> bool\<close>, \<^term>\<open>Ord :: V \<Rightarrow> bool\<close>]\<close>

  thm Variants_V_def Excluded_V_def
  thm Variants_V_0 Variants_V_0_zero Variants_V_0_succ Variants_V_0_lim
  thm Variants_V_1 Variants_V_1_zero Variants_V_1_succ Variants_V_1_lim 
  thm Excluded_V_0 Excluded_V_1
  
  instance proof (intro_classes)
    show "Variants : (\<Pi> i::V:Tag. nonLimit \<rightarrow> Set \<rightarrow> SetOf (\<alpha> i))"
    proof (rule depfunI, rule funI, rule funI)
      fix i :: V and j :: V and x :: V 
      assume "i : Tag" "j : nonLimit" and x :"x : Set"
      hence "i : Ord" "i < \<omega>" and j : "j : Ord"  
        using tagD nonlimit_ord by auto
        
      show "Variants i j x : SetOf (\<alpha> i)"
        unfolding Variants_V_def \<alpha>_V_def 
        by (rule iffD2[OF if_split], rule, rule,
            use gzf_model_case_typ[OF j x] 
                ord_model_case_typ[OF j] emp_setof in auto)
    qed

    show "Variants : (\<Pi> (i::V) : Tag. Limit \<rightarrow> Function \<rightarrow> SetOf (\<alpha> i)) "
    proof (rule depfunI, rule funI, rule funI)
      fix i :: V and u :: V and f :: V 
      assume "i : Tag" "u : Limit" "f : Function" 
      show "Variants i u f : SetOf (\<alpha> i)"
        unfolding Variants_V_def case_ord_lim[OF \<open>u : Limit\<close>]
      proof (rule if_cases[OF _ if_cases], rule emp_setof)
        assume i:"i = succ 0"
        show "{u} : SetOf (\<alpha> i)"
          unfolding i \<alpha>_V_1
          using sng_setof[OF ord_setmem] 
            limit_ord[OF \<open>u : Limit\<close>] by auto
      next
        show "\<emptyset> : SetOf (\<alpha> i)"
          using emp_setof .
      qed
    qed
  qed
end

instantiation V :: GZF_Model 
begin

  definition mdefault_V :: V where
    "mdefault_V \<equiv> <set_V,\<emptyset>>"
  thm Variants_V_0_zero
  instance proof (intro_classes)
    show "(mdefault::V) : M"
        
end
instance V :: Ordinal_Model sorry
instance V :: OrdRec_Model sorry

thm Part_def 


end