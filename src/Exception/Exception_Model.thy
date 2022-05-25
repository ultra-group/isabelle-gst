theory Exception_Model
  imports "../GST_Features" "../ModelKit/ModelComponents"
begin

context ModelBase begin
ML \<open>val exc_model = mcomp 
  { name = "Exc_Model",
    deps = mcomps [],
    variant = SOME (vari
      { tag_name = "exc_tag",
          vcases =
            (\<^term>\<open>{\<emptyset>} :: 'a\<close>,
             \<^term>\<open>(\<lambda>_ y. \<emptyset>) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>,
             \<^term>\<open>(\<lambda>_ _. \<emptyset>) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a \<close>),
       alpha_typ = \<^term>\<open>Set\<close>}),
    excludes_formulas = [] }\<close>
end

local_setup \<open>snd o (mk_mcomp_class exc_model)\<close>

lemma exc_model_case_typ :
  assumes j : "j : Ord" 
  shows "caseof_ord {\<emptyset>} \<emptyset> \<emptyset> j : SetOf Set"
  by (rule case_ordE[OF j], 
      use sng_setof[OF set_setmem[OF emp_set] emp_set] emp_setof in auto)

context Exc_Model begin

definition mexc :: \<open>'a\<close>
  where "mexc = <exc_tag, \<emptyset>>"

definition mExc :: \<open>'a \<Rightarrow> bool\<close>
  where "mExc \<equiv> M \<triangle> (\<^enum> exc_tag)"

theorem variants_exc : 
  shows "Variants exc_tag 0 \<emptyset> = {\<emptyset>}"
    and "j : Ord   \<Longrightarrow> Variants exc_tag (succ j) y = \<emptyset>"
    and "u : Limit \<Longrightarrow> Variants exc_tag u f = \<emptyset>"
 using v_exc_tag_0 v_exc_tag_succ v_exc_tag_limit by auto

theorem mexc_m : 
  "mexc : M"
  using mI[OF zero_ord tier0I[OF exc_tag_tag]]
  unfolding mexc_def variants_exc(1) sng_iff[OF set_setmem[OF emp_set]]
  by auto
  
theorem mexc_ax : 
  "m\<forall>b. mExc b = (b = mexc)"
proof (rule, rule)
  fix b assume "mExc b"
  hence "b : mExc" by (rule tyI)
  hence "b : M" "b :\<^enum> exc_tag"
    unfolding mExc_def by (unfold_typs) 
  then obtain b' where b_eq:"b = <exc_tag, b'>"
    using partE by metis
  hence b : "<exc_tag, b'> : M"
    using \<open>b : M\<close> by auto
  have "b' \<in> Variants exc_tag 0 \<emptyset>"
    by (rule m_cases_pair[OF b], use variants_exc in auto)
  thus "b = mexc"
    unfolding mexc_def b_eq 
     variants_exc(1) sng_iff[OF set_setmem[OF emp_set]]
    by auto
next
  fix b assume "b = mexc"
  hence "b : M" "b :\<^enum> exc_tag"
    using mexc_m partI[OF _ setmem_pair[OF 
      ord_setmem[OF tag_ord[OF exc_tag_tag]] set_setmem[OF emp_set]]]
    unfolding mexc_def by auto
  thus "mExc b"
    unfolding mExc_def inter_ty_def has_ty_def 
    by auto
qed

ML \<open>val mExc = mk_msig [] "mExc" \<^class>\<open>Exc\<close> ["mExc", "mexc", "mexc"] \<^context>\<close>
translate_axioms mExc using mexc_ax .
resp_thms mExc_rsp : mExc by (rule mexc_m, rule mexc_m)

end
end