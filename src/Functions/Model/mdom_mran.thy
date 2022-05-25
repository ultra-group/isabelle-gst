theory mdom_mran
  imports Function_Model_Base mapp
begin

context Function_Model begin

(*MOVE TO mSet.thy*)
lemma msetI_eq :
  assumes "x = <set,x'>" "<set,x'> : M"
    shows "x : mSet"
    using msetI assms by auto
(* ------------- *)

subsection \<open>Domain of model Functions\<close>


definition mdom' :: \<open>'a \<Rightarrow> 'a\<close>
  where "mdom' f \<equiv> <set, dom (snd f)>"

definition mdom :: \<open>'a \<Rightarrow> 'a\<close>
  where "mdom f \<equiv> if f : mFunc then mdom' f 
                  else Function_Model_mdefault"

lemma mdom_eq :
  assumes f : "f : mFunc" 
    shows "mdom f = <set, dom (snd f)>"
  unfolding mdom_def mdom'_def
  using f by auto

lemma mdom_eq_pair :
  assumes f : "<func, f'> : mFunc" 
    shows "mdom <func,f'> = <set, dom f'>"
  using mdom_eq[OF f] mfunc_snd_eq[OF f] by auto

lemma mdom_typ :
  "mdom : mFunc \<rightarrow> mSet"
proof (rule funI)
  fix f assume 
    f : "f : mFunc"
  then obtain f' j where
    f' : "f' : Function" and f_eq : "f = <func, f'>" and
    j : "j : Ord" and 
    dom : "dom f' \<subseteq> Tier j \<ominus> func"
    using mfuncE2 by metis
  hence "<set, dom f'> : M"
    using mI_mset[OF j dom_set[OF f'] ex_func_set_trans[OF tier_set]] by auto
  thus "mdom f : mSet" 
   using msetI mdom_eq_pair f
   unfolding f_eq by auto
qed 

lemmas mdom_mset = funE[OF mdom_typ]

lemma mdom_typ_ax : 
  "m\<forall>x. x : mFunc \<longrightarrow> mdom x : mSet"
  unfolding mall_def tall_def
  using mdom_mset by auto

lemma mdom_iff :  
  assumes f : "f : mFunc"
    shows "b m mdom f \<longleftrightarrow> (\<exists>c. mapp f b c)"
proof (rule mfuncE2[OF f])
  fix f' j assume
    f' : "f' : Function" and f_eq : "f = <func, f'>" 
  show "(b m mdom f) = (\<exists>c. mapp f b c)"
  proof
    assume "b m mdom f"
    hence "b \<in> dom f'"
      using mdom_eq_pair f f_eq mmemD by auto
    then obtain c where 
      "app f' b c" 
      using domE[OF f'] by auto
    hence "mapp f b c"
      using mappI_pair f f_eq by auto
    thus "\<exists>c. mapp f b c" by auto
  next
    assume "\<exists>c. mapp f b c"
    then obtain c where 
      "app f' b c"
      using mappD_pair f f_eq by auto
    hence "b \<in> dom f'"
      using domI[OF f'] by auto
    thus "b m mdom f"
      using mdom_eq_pair f mmemI_eq[OF mdom_mset] 
      unfolding f_eq by auto
  qed
qed

lemma mdom_ax : 
  "m\<forall>f : mFunc. m\<forall>x. (x m mdom f) = (m\<exists>y. mapp f x y)"
  unfolding mtall_def mall_def tall_def mex_def tex_def
  using mdom_iff mapp_m by metis


subsection \<open>Range of model Functions\<close>

definition mran' :: \<open>'a \<Rightarrow> 'a\<close>
  where "mran' f \<equiv> <set, ran (snd f)>"

definition mran :: \<open>'a \<Rightarrow> 'a\<close>
  where "mran f \<equiv> if f : mFunc then mran' f 
                  else Function_Model_mdefault"

lemma mran_eq :
  assumes f : "f : mFunc" 
    shows "mran f = <set, ran (snd f)>"
  unfolding mran_def mran'_def
  using f by auto

lemma mran_eq_pair :
  assumes f : "<func, f'> : mFunc" 
    shows "mran <func,f'> = <set, ran f'>"
  using mran_eq[OF f] mfunc_snd_eq[OF f] by auto

lemma mran_typ :
  "mran : mFunc \<rightarrow> mSet"
proof (rule funI)
  fix f assume 
    f : "f : mFunc"
  then obtain f' j where
    f' : "f' : Function" and f_eq : "f = <func, f'>" and
    j : "j : Ord" and 
    ran : "ran f' \<subseteq> Tier j \<ominus> func"
    using mfuncE2 by metis
  hence "<set, ran f'> : M"
    using mI_mset[OF j ran_set[OF f'] ex_func_set_trans[OF tier_set]] by auto
  thus "mran f : mSet" 
   using msetI mran_eq_pair f
   unfolding f_eq by auto
qed 

lemmas mran_mset = funE[OF mran_typ]

lemma mran_typ_ax : 
  "m\<forall>x. x : mFunc \<longrightarrow> mran x : mSet"
  unfolding mall_def tall_def
  using mran_mset by auto

lemma mran_iff :  
  assumes f : "f : mFunc"
    shows "c m mran f \<longleftrightarrow> (\<exists>b. mapp f b c)"
proof (rule mfuncE2[OF f])
  fix f' j assume
    f' : "f' : Function" and f_eq : "f = <func, f'>" 
  show "(c m mran f) = (\<exists>b. mapp f b c)"
  proof
    assume "c m mran f"
    hence "c \<in> ran f'"
      using mran_eq_pair f f_eq mmemD by auto
    then obtain b where 
      "app f' b c" 
      using ranE[OF f'] by auto
    hence "mapp f b c"
      using mappI_pair f f_eq by auto
    thus "\<exists>b. mapp f b c" by auto
  next
    assume "\<exists>b. mapp f b c"
    then obtain b where 
      "app f' b c"
      using mappD_pair f f_eq by auto
    hence "c \<in> ran f'"
      using ranI[OF f'] by auto
    thus "c m mran f"
      using mran_eq_pair f mmemI_eq[OF mran_mset] 
      unfolding f_eq by auto
  qed
qed

lemma mran_ax :
  "m\<forall>f : mFunc. m\<forall>y. (y m mran f) = (m\<exists>x. mapp f x y)"
   unfolding mtall_def mall_def tall_def mex_def tex_def
   using mran_iff mapp_m by metis

lemma mdom_rsp :
  "f : M \<Longrightarrow> mdom f : M"
  using mset_m[OF mdom_mset] Function_Model_mdefault_m
  unfolding mdom_def
  by auto

lemma mran_rsp :
  "f : M \<Longrightarrow> mran f : M"
  using mset_m[OF mran_mset] Function_Model_mdefault_m
  unfolding mran_def
  by auto

end
end