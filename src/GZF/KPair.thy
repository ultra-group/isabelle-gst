theory KPair
  imports UPair SetRel
begin

context GZF begin

subsection \<open>Kuratowski ordered pairs\<close>

definition kpair :: "['a,'a] \<Rightarrow> 'a" where
  "kpair a b \<equiv> {{a,b},{a,a}}"

definition is_kpair :: \<open>'a \<Rightarrow> bool\<close>
  where "is_kpair p = (p : Set \<and> (\<exists>a : SetMem. \<exists>b : SetMem. p = kpair a b))"

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
(*FIXME, figure out how to interpret OPair class using Kpairs*)
interpretation OPair
  where OPair_default = GZF_default
    and Pair = is_kpair
    and pair = kpair
    and PairMem = SetMem sorry
(*It seems like when we interpret the pair locale,
  we don't carry over it's syntax, or the attributes places upon facts.
  Can this be resolved in any way? 
  Perhaps using "bundles"?*)


section \<open>Cartesian Products of Kuratowski Pairs\<close>
(*Interpret Cartesian Product locale, using GZF for sets, and kpair for ordered pairs. *)
(* interpretation SetRel 
  where OPair_default = GZF_default
    and PairMem = SetMem
    and pair = kpair 
  by (unfold_locales, rule kpair_typ)
 *)

end