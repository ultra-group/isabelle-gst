theory mapp
  imports Function_Model_Base
begin

context Function_Model begin

subsection \<open>Application relation on model Functions\<close>
lemma mapp_iff :
  assumes "f : mFunc"
  shows "mapp f b c \<longleftrightarrow> app (snd f) b c"
  unfolding mapp_def 
  using assms by auto

lemma mapp_iff_pair :
  assumes "<func, f'> : mFunc"
  shows "mapp <func, f'> b c \<longleftrightarrow> app f' b c"
  unfolding mapp_iff[OF assms] mfunc_snd_eq[OF assms] ..

lemmas mappI = iffD2[OF mapp_iff]  
   and mappI_pair = iffD2[OF mapp_iff_pair]

lemmas mappD = iffD1[OF mapp_iff]
   and mappD_pair = iffD1[OF mapp_iff_pair]

lemma mappE :
  assumes f:"f : mFunc" and bc:"mapp f b c"
  obtains f' where 
    "f' : Function" "f = <func, f'>" "app f' b c"
proof (rule mfuncE1[OF f]) 
  thm mfunc_pair_snd_func mappD assms
  fix f' assume f_eq : "f = <func, f'>"
  moreover hence f':"f' : Function" 
    using mfunc_pair_snd_func f by auto
  have app: "app f' b c"
    using mappD_pair f_eq f bc by auto
  
  from f' f_eq app show ?thesis ..
qed

lemma mapp_m :
  assumes f:"f : mFunc" and bc:"mapp f b c"
  shows "b : M \<and> c : M"
proof (rule mappE[OF f bc])
  fix f' assume 
    f' : "f' : Function" and f_eq : "f = <func, f'>"
  then obtain j where
    j : "j : Ord" and "f' \<in> (Tier j \<ominus> func) \<midarrow>p\<rightarrow> (Tier j \<ominus> func)"
    using mE_mfunc_pair mfunc_m[OF f] by metis
  hence "dom f' \<subseteq> Tier j \<ominus> func" "ran f' \<subseteq> Tier j \<ominus> func"
    using fspaceD[OF tier_ex_set tier_ex_set, OF j j] by auto
  moreover have "app f' b c"
    using mappD_pair f bc 
    unfolding f_eq by auto
  ultimately have "b \<in> Tier j \<ominus> func" "c \<in> Tier j \<ominus> func"
    using domI[OF f'] ranI[OF f'] by auto
  thus "b : M \<and> c : M"
    using mI[OF j exsetD1[OF tier_set[OF j]]]
    by auto
qed

text \<open>Model application is functional:\<close>
lemma mapp_functional :
  assumes f : "f : mFunc"
      and bc : "mapp f b c" 
      and bd : "mapp f b d"
    shows "c = d"
  using bc bd app_eqI[OF mfunc_snd_func[OF f]]
  unfolding mapp_iff[OF f] by auto

lemma mapp_functional_ax :
  "m\<forall>f : mFunc. m\<forall>x y z. mapp f x y \<and> mapp f x z \<longrightarrow> y = z"
  unfolding mtall_def mall_def tall_def
  using mapp_functional by auto

text \<open>Model functions are extensional:\<close>
lemma mfunc_ext :
  assumes f : "f : mFunc" and g : "g : mFunc"
      and bc:"\<And>b c. mapp f b c \<longleftrightarrow> mapp g b c"
    shows "f = g"
proof (rule mfuncE1[OF f], rule mfuncE1[OF g])
  fix f' g' assume 
    f' : "f = <func, f'>" and g' : "g = <func, g'>"
  have
    "snd f = snd g"
    using bc fun_eqI[OF mfunc_snd_func mfunc_snd_func, OF f g]
    unfolding mapp_def by auto
  thus "f = g" 
    using mfunc_snd_eq f g unfolding f' g'
    by metis
qed

lemma mfunc_ext_ax : 
  "m\<forall>f : mFunc. m\<forall>g : mFunc. 
    (m\<forall>x y. mapp f x y = mapp g x y) \<longrightarrow> f = g"
  unfolding mtall_def mall_def tall_def
  using mfunc_ext mapp_m by meson

end
end