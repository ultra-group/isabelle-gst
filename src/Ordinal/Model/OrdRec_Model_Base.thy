theory OrdRec_Model_Base
  imports "../../ModelKit/ModelComponents"
          "../../GZF/Model/GZF_Model"
          "Ordinal_Model"
begin


(*Formula \<open>ex_ordrec\<close> needs to be defined in context of both GZF_Model and Ordinal_Model
  Need a better workaround.*)
class foo = GZF_Model + Ordinal_Model 
begin
(*Constrains \<open>Excluded\<close> to allow sets of ordinals to be formed in model building process*)
ML \<open>val ex_ordrec = @{prop \<open>\<not> Excluded set <ord, j'>\<close>}\<close>
end

context ModelBase begin
ML \<open>val ordrec_model = mcomp
 { name = "OrdRec_Model", 
   deps = mcomps [set_model, ord_model], 
   variant = NONE,
  excludes_formulas = 
    [("not_excluded_set_mord", ex_ordrec)]
 }\<close>
end

local_setup \<open>snd o mk_mcomp_class ordrec_model\<close>

context OrdRec_Model 
begin

definition mpredSet' :: \<open>'a \<Rightarrow> 'a\<close> 
  where "mpredSet' j \<equiv> <set, ord \<oplus> predSet (snd j)>"

definition mpredSet :: \<open>'a \<Rightarrow> 'a\<close> 
  where "mpredSet j \<equiv> if j : mOrd then mpredSet' j 
                                  else OrdRec_Model_mdefault"

definition msupOrd' :: \<open>'a \<Rightarrow> 'a\<close>
  where "msupOrd' x \<equiv> <ord, supOrd {snd b | b \<in> snd x}>"

definition msupOrd :: \<open>'a \<Rightarrow> 'a\<close> 
  where "msupOrd x \<equiv> if x : mSetOf mOrd then msupOrd' x 
                                        else OrdRec_Model_mdefault"

definition forceM_ordrec :: \<open>'a \<Rightarrow> 'a\<close>
  where "forceM_ordrec b \<equiv> if b : M then b else OrdRec_Model_mdefault"

lemma forceM_ordrec_m : "forceM_ordrec b : M"
  unfolding forceM_ordrec_def using OrdRec_Model_mdefault_m 
  by auto

lemma forceM_ordrec_eq : 
  assumes "b : M"
  shows "forceM_ordrec b = b"
  using assms unfolding forceM_ordrec_def
  by auto

definition forceM_ordrec_fun 
  where "forceM_ordrec_fun f \<equiv> f " 
  
definition mordrecG where 
  "mordrecG G u' (f' :: 'a \<Rightarrow> 'a) \<equiv> forceM_ordrec (G (<ord, u'>) 
    (\<lambda>j. if j \<lless> <ord,u'> then f' (snd j) else OrdRec_Model_mdefault))"

definition mordrecF where
  "mordrecF F j' b \<equiv> forceM_ordrec (F (<ord, j'>) b)"

definition mOrdRec' 
  where "mOrdRec' G F A b \<equiv> 
    OrdRec (mordrecG G) (mordrecF F) (forceM_ordrec A) (snd b)"

definition mOrdRec 
  where "mOrdRec G F A j \<equiv> (if G : LimFun \<and> F : M \<rightarrow> M \<rightarrow> M \<and> A : M \<and> j : mOrd 
                            then mOrdRec' G F A j 
                            else OrdRec_Model_mdefault)"

end
end