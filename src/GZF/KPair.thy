theory KPair
  imports UPair SetRel
begin

context GZF begin

subsection \<open>Kuratowski ordered pairs\<close>

definition kpair :: "['a,'a] \<Rightarrow> 'a" where
  "kpair a b \<equiv> {{a,b},{a,a}}"

lemma kpair_typ_set : "kpair : SetMem \<rightarrow> SetMem \<rightarrow> Set" unfolding kpair_def
  by (rule funI, rule funI, 
      use upair_set[OF set_setmem[OF upair_set] set_setmem[OF upair_set]] in auto)

lemmas kpair_set [typ_intro] = funE[OF funE[OF kpair_typ_set]]
  
lemma kpair_iff : 
  assumes "a : SetMem" "b : SetMem" "c : SetMem" "d : SetMem" 
  shows "kpair a b = kpair c d \<longleftrightarrow> a = c \<and> b = d" 
proof -
  have "upair a b : SetMem" "upair a a : SetMem" "upair c d : SetMem" "upair c c : SetMem" 
    using set_setmem[OF upair_set] assms by auto
  thus ?thesis unfolding kpair_def using upair_eq_iff assms by metis
qed

end




(*
interpretation OPair_sig 
  where OPair_default = GZF_default
    and PairMem = SetMem
    and pair = kpair  
  by (unfold_locales)

lemma kpair_typ:"kpair : SetMem \<rightarrow> SetMem \<rightarrow> (Pair \<bar> SetMem)"
    by (rule funI, rule funI, rule Soft_Types.intI, unfold Pair_def, auto intro: tyI,
        rule set_setmem[OF kpair_set], auto)

interpretation OPair
  where OPair_default = GZF_default
    and PairMem = SetMem
    and pair = kpair 
proof (unfold_locales, rule kpair_typ)
  show "\<forall>a : SetMem. \<forall>b : SetMem. \<forall>c : SetMem. \<forall>d : SetMem.
        (kpair a b = kpair c d) = (a = c \<and> b = d)"
    using kpair_iff unfolding tall_def by auto
qed
(*It seems like when we interpret the pair locale,
  we don't carry over it's syntax, or the attributes places upon facts.
  Can this be resolved in any way? 
  Perhaps using "bundles"?*)


section \<open>Cartesian Products of Kuratowski Pairs\<close>
(*Interpret Cartesian Product locale, using GZF for sets, and kpair for ordered pairs. *)
interpretation SetRel 
  where OPair_default = GZF_default
    and PairMem = SetMem
    and pair = kpair 
  by (unfold_locales, rule kpair_typ)
 *)

end