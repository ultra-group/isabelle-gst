theory KPair
  imports UPair SetRel
begin

context GZF begin

subsection \<open>Kuratowski ordered pairs\<close>

definition kpair :: "['a,'a] \<Rightarrow> 'a" where
  "kpair a b \<equiv> {{a,b},{a,a}}"

definition is_kpair :: \<open>'a \<Rightarrow> bool\<close>
  where "is_kpair p \<equiv> p : SetOf Set \<and> (\<exists>a b. p = kpair a b)"

lemma kpair_typ_setof : "kpair : SetMem \<rightarrow> SetMem \<rightarrow> SetOf Set" unfolding kpair_def
  by (rule funI, rule funI, rule upair_setof[OF upair_set upair_set])


lemmas kpair_setof [typ_intro] = funE[OF funE[OF kpair_typ_setof]]
  
lemma is_kpairI : 
  assumes "b : SetMem" "c : SetMem"
  shows "kpair b c : is_kpair"
  using kpair_setof assms
  unfolding is_kpair_def has_ty_def by auto

lemma is_kpairE :
  assumes "p : is_kpair"
  obtains b c where 
    "b : SetMem" "c : SetMem" "p = kpair b c"
proof -
  from assms obtain b c where
    "p : SetOf Set" and p_eq:"p = kpair b c"
    unfolding is_kpair_def has_ty_def by blast
  hence bb:"{b,b} : SetMem" and bc:"{b,c} : SetMem"
    using upair_set_setmem[OF setof_set] unfolding kpair_def by auto
  hence "{b,c} : Set"
    using setof_mem[OF \<open>p : SetOf Set\<close>] 
          upairI1[OF bc bb]
    unfolding \<open>p = kpair b c\<close> kpair_def by auto
  hence "b : SetMem" "c : SetMem" "p = kpair b c"
    using upair_set_setmem p_eq by auto
  thus ?thesis ..
qed

lemma kpair_iff : 
  assumes "a : SetMem" "b : SetMem" "c : SetMem" "d : SetMem" 
  shows "kpair a b = kpair c d \<longleftrightarrow> a = c \<and> b = d" 
proof -
  have "upair a b : SetMem" "upair a a : SetMem" "upair c d : SetMem" "upair c c : SetMem" 
    using set_setmem[OF upair_set] assms by auto
  thus ?thesis unfolding kpair_def using upair_eq_iff assms by fastforce
qed

lemma is_kpairD :
  assumes "kpair b c : is_kpair" 
  shows "b : SetMem \<and> c : SetMem"
proof 
  from assms have
    kp:"kpair b c : SetOf Set"
    unfolding is_kpair_def has_ty_def by blast
  hence bb:"{b,b} : SetMem" and bc:"{b,c} : SetMem"
    using upair_set_setmem[OF setof_set] unfolding kpair_def by auto
  hence "{b,c} : Set" using setof_mem[OF kp] upairI1[OF bc bb]
    unfolding kpair_def by auto
  thus "b : SetMem" "c : SetMem"
    using upair_set_setmem by auto
qed

theorem GZF_OPair :
  "class.OPair is_kpair kpair SetMem"
proof
  show "kpair : SetMem \<rightarrow> SetMem \<rightarrow> is_kpair \<triangle> SetMem"
  by (rule funI, rule funI, rule intI, rule is_kpairI, auto, 
      rule set_setmem[OF setof_set[OF kpair_setof]], auto) 
  
  show "\<forall>a : SetMem. \<forall>b : SetMem. \<forall>c : SetMem. \<forall>d : SetMem. 
          (kpair a b = kpair c d) = (a = c \<and> b = d)"
    unfolding tall_def 
    using kpair_iff by auto

  show "\<forall>p : is_kpair. \<exists>a b. p = kpair a b"
    unfolding tall_def 
    using is_kpairE by meson

  show "\<forall>b. SetMem b \<longleftrightarrow> (\<exists>p : is_kpair. \<exists>c. p = kpair b c \<or> p = kpair c b)"
  proof (auto)
    fix b assume "SetMem b"
    hence "kpair b b : is_kpair"
      using is_kpairI unfolding has_ty_def by auto
    thus "\<exists>p : is_kpair. \<exists>c. p = kpair b c \<or> p = kpair c b"
      by auto
  next
    fix b c assume "kpair b c : is_kpair"
    thus "SetMem b" 
      using is_kpairD unfolding has_ty_def by auto 
  next
    fix b c assume "kpair b c : is_kpair"
    thus "SetMem c" 
      using is_kpairD unfolding has_ty_def by auto 
  qed
qed

sublocale OPair is_kpair kpair SetMem GZF_default
  by (intro_locales, rule GZF_OPair)

section \<open>Cartesian Products of Kuratowski Pairs\<close>
(*Interpret Cartesian Product locale, using GZF for sets, and kpair for ordered pairs. *)

lemma kpair_typ_iskpair : "kpair : SetMem \<rightarrow> SetMem \<rightarrow> is_kpair" 
  by (rule funI, rule funI, rule is_kpairI)

lemma kpair_typ_setmem : "kpair : SetMem \<rightarrow> SetMem \<rightarrow> SetMem" 
  by (rule funI, rule funI, rule set_setmem[OF setof_set[OF kpair_setof]])

theorem GZF_CartProd :
  "class.CartProd Set (\<in>) Union Pow \<emptyset> Succ Inf \<R> (\<subseteq>) SetMem SetOf ReplPred is_kpair kpair SetMem"
  by (intro_locales, unfold_locales, rule kpair_typ_iskpair, rule kpair_typ_setmem)

end
end