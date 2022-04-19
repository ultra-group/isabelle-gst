theory msupOrd
  imports OrdRec_Model_Base
begin


context OrdRec_Model
begin

lemma msupord_eq : 
  assumes "x : mSetOf mOrd"
  shows "msupOrd x = <ord, supOrd {snd b | b \<in> snd x}>"
  unfolding msupOrd_def msupOrd'_def
  using assms
  by auto

lemma msupord_thm :
  assumes x : "x : mSetOf mOrd"
  shows "msupOrd x : mOrd"
    and "i m x \<Longrightarrow> i \<lless> msucc (msupOrd x)"
proof -
  obtain x' where 
    x' : "x' : SetOf mOrd" and x_eq :"x = <set,x'>"
    using msetofE[OF x] by auto
  hence eq:"msupOrd x = <ord, supOrd {snd b | b \<in> x'}>"
    unfolding msupord_eq[OF x] 
    using mset_snd_eq[OF msetof_mset] x by auto
  have setof_ord : "{snd b | b \<in> x'} : SetOf Ord"
  proof (rule repfun_setof[OF setof_set[OF x']], rule mem_funI)
    fix b assume "b \<in> x'"
    thus "snd b : Ord" 
      using mord_snd_ord[OF setof_mem[OF x']] 
      by auto
  qed
  show "msupOrd x : mOrd"
    unfolding eq
    by (rule mordI, rule supord_ord[OF setof_ord])

  assume "i m x"
  hence "i \<in> x'" 
    using mmemD x_eq by auto
  moreover then obtain i' where
    i' : "i' : Ord" and i_eq: "i = <ord, i'>"
    using mordE[OF setof_mem[OF x']] by metis
  ultimately have 
    "i' \<in> {snd b | b \<in> x'}"
    using repfunI[of x' i snd,OF setof_set[OF x'] _ 
      ord_setmem[OF mord_snd_ord[OF setof_mem[OF x']]]]  
    unfolding ord_snd_eq[OF i' i_eq]
    by auto
  hence "i' < succ (supOrd {snd b | b \<in> x'})"
    using supord_iff[OF setof_ord] by auto
  hence "i \<lless> <ord, succ (supOrd {snd b | b \<in> x'})>"
    using mltI[OF i' succ_ord[OF supord_ord[OF setof_ord]]]
    unfolding i_eq by auto
  thus "i \<lless> msucc (msupOrd x)"
    unfolding eq msucc_eq[OF supord_ord[OF setof_ord]] .
qed

lemmas msupordI = msupord_thm(2)
   and msupord_mord = msupord_thm(1)

theorem msupord_rsp :
  "msupOrd x : M"
  using mord_m[OF msupord_mord]
   OrdRec_Model_mdefault_m
  unfolding msupOrd_def 
  by auto

end
end