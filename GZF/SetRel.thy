theory SetRel
  imports "../GST_Features" "../Pair_locale" "../Relations" SetComprehension SetCombinators 
begin

(*Developments that use sets and ordered pairs! 
    e.g., relations as sets, functions as sets, cartesian product
  The SetRel interface abstracts over the representation of sets and pairs.*)

(* section \<open>Relations and Functions as sets of ordered pairs\<close>

definition app where "app r a b \<equiv> a : SetMem \<and> b : SetMem \<and> pair a b \<in> r"
definition mkrel where "mkrel x y P \<equiv> Collect (cprod x y) (\<lambda>p. P (fst p) (snd p))"
definition field where "field r \<equiv> RepFun r fst \<union> RepFun r snd"

interpretation Relation_sig
  where BinRelation = "SetOf (SetMem ** SetMem)"
    and app = app
    and mkrel = mkrel
    and field = field
  by (unfold_locales)

interpretation Relation
  where BinRelation = "SetOf (SetMem ** SetMem)"
    and app = app
    and mkrel = mkrel
    and field = field
proof
  show mkrel_typ : "mkrel : (\<Pi> x:Set. \<Pi> y:Set. BinRelPred x y \<rightarrow> SetOf (SetMem ** SetMem))"
    unfolding mkrel_def
  proof (rule depfunI, rule depfunI, rule funI, rule collect_typ_subset)
    fix x y assume "x : Set" "y : Set"
    hence "x : SetOf SetMem" "y : SetOf SetMem" using setofI setmemI by auto
    thus "x \<times> y : SetOf (SetMem ** SetMem)" using cprod_setof_prod by auto
  qed
  
  show "field : SetOf (SetMem ** SetMem) \<rightarrow> Set" unfolding field_def
  proof (rule funI, rule un_set[OF repfun_set repfun_set], use setof_set in auto)
    fix x assume x_typ : "x : SetOf (SetMem ** SetMem)"
    show "fst : SetFun x"
    proof (rule setfunI)
      fix p assume "p \<in> x" 
      hence "p : SetMem ** SetMem" by (rule setof_mem[OF x_typ])
      then obtain a b where "p = pair a b" "a : SetMem" "b : SetMem"
        by (rule productE)
      moreover hence "pair a b : Pair" using setmem_pair by auto
      ultimately show "fst p : SetMem" using fst_eq by auto  
    qed
    show "snd : SetFun x"
    proof (rule setfunI)
      fix p assume "p \<in> x" 
      hence "p : SetMem ** SetMem" by (rule setof_mem[OF x_typ])
      then obtain a b where "p = pair a b" "a : SetMem" "b : SetMem"
        by (rule productE)
      moreover hence "pair a b : Pair" using setmem_pair by auto
      ultimately show "snd p : SetMem" by auto  
    qed
  qed

  show "\<forall>x : Set. \<forall>y : Set. \<forall>P : BinRelPred x y.
          \<forall>a b. app (mkrel x y P) a b = (a \<in> x \<and> b \<in> y \<and> P a b)"
  proof (rule, rule, rule, rule, rule, rule)
    fix x y P a b assume "x : Set" "y : Set" "P : BinRelPred x y"
    hence rtyp : "mkrel x y P : SetOf (SetMem ** SetMem)" 
      by (rule funE[OF depfunE[OF depfunE[OF mkrel_typ]]])
    show "app (mkrel x y P) a b \<Longrightarrow> (a \<in> x \<and> b \<in> y \<and> P a b)"
    unfolding app_def proof (auto)
      assume "a : SetMem" "b : SetMem" "pair a b \<in> mkrel x y P"
      hence "pair a b : Pair" "pair a b \<in> x \<times> y" "P (fst (pair a b)) (snd (pair a b))"
          using setmem_pair mkrel_def collect_iff[OF cprod_set[OF \<open>x : Set\<close> \<open>y : Set\<close>]] by auto
      thus "a \<in> x" "b \<in> y" "P a b" using fst_eq snd_eq cprod_iff_pair[OF \<open>x : Set\<close> \<open>y : Set\<close>] by auto
    qed
    show "a \<in> x \<and> b \<in> y \<and> P a b \<Longrightarrow> app (mkrel x y P) a b"
      unfolding app_def mkrel_def 
    proof (auto intro: setmemI[OF \<open>x : Set\<close>] setmemI[OF \<open>y : Set\<close>], 
           rule collectI[OF cprod_set[OF \<open>x : Set\<close> \<open>y : Set\<close>]],
           auto intro: cprodI_pair[OF \<open>x : Set\<close> \<open>y : Set\<close>])
      assume "a \<in> x" "b \<in> y" "P a b"
      moreover hence "pair a b : Pair" using setmemI \<open>x : Set\<close> \<open>y : Set\<close> setmem_pair by auto
      ultimately show "P (\<tau> (pair a b)) (\<pi> (pair a b))"
        using fst_eq snd_eq by auto  
    qed
  qed

  show "\<forall>r : SetOf (SetMem ** SetMem). \<forall>s : SetOf (SetMem ** SetMem).
          (\<forall>a b. app r a b = app s a b) \<longrightarrow> r = s" 
  proof (rule)+
    fix r s assume r:"r : SetOf (SetMem ** SetMem)" and s: "s : SetOf (SetMem ** SetMem)"
                   and ab: "\<forall>a b. app r a b \<longleftrightarrow> app s a b" 
    show "r = s" 
    proof (rule equality_iffI[OF setof_set[OF r] setof_set[OF s]])
      fix p show "p \<in> r \<longleftrightarrow> p \<in> s"
      proof
        assume "p \<in> r" 
        moreover then obtain a b where "p = pair a b" "a : SetMem" "b : SetMem" 
          using setof_mem[OF r] by (blast elim: productE)
        ultimately have "app r a b" unfolding app_def by auto
        hence "app s a b" using ab by simp
        thus "p \<in> s" unfolding app_def using ab \<open>p = pair a b\<close> \<open>p \<in> r\<close> by auto
      next
        assume "p \<in> s" 
        moreover then obtain a b where "p = pair a b" "a : SetMem" "b : SetMem" 
          using setof_mem[OF s] by (blast elim: productE)
        ultimately have "app s a b" unfolding app_def by auto
        hence "app r a b" using ab by simp
        thus "p \<in> r" unfolding app_def using ab \<open>p = pair a b\<close> \<open>p \<in> s\<close> by auto
      qed
    qed
  qed

  show "\<forall>r : SetOf (SetMem ** SetMem). \<forall>x. (x \<in> field r) = (\<exists>y. app r x y \<or> app r y x)"
  proof (rule, rule)
    fix r x assume rtyp:"r : SetOf (SetMem ** SetMem)"
    hence rset:"r : Set" by (rule setof_set)
    have fst:"fst : SetFun r" proof (rule setfunI, drule setof_mem[OF rtyp])
      fix p assume "p : SetMem ** SetMem"
      then obtain a b where "p : Pair" "p = pair a b" "a : SetMem" 
        using setmem_pair by (blast elim: productE)
      thus "fst p : SetMem" using fst_eq by auto
    qed
    have snd:"snd : SetFun r" proof (rule setfunI, drule setof_mem[OF rtyp])
      fix p assume "p : SetMem ** SetMem"
      then obtain a b where "p : Pair" "p = pair a b" "b : SetMem" 
        using setmem_pair by (blast elim: productE)
      thus "snd p : SetMem" using snd_eq by auto
    qed

    show "x \<in> field r \<longleftrightarrow> (\<exists>y. app r x y \<or> app r y x)" unfolding field_def
    proof (rule)
      assume "x \<in> RepFun r \<tau> \<union> RepFun r \<pi>"
      thus "\<exists>y. app r x y \<or> app r y x" 
      proof (rule unE[OF repfun_set[OF rset fst] repfun_set[OF rset snd]])
        assume "x \<in> RepFun r \<tau>"
        then obtain p where p:"p \<in> r" "x = fst p" by (rule repfunE[OF rset fst])
        hence "p : SetMem ** SetMem" using setof_mem[OF rtyp] by auto
        then obtain a b where "p : Pair" "p = pair a b" "a : SetMem" "b : SetMem" 
          using setmem_pair by (blast elim: productE)
        thus "\<exists>y. app r x y \<or> app r y x" 
          unfolding app_def using p by auto
      next
        assume "x \<in> RepFun r \<pi>"
        then obtain p where p:"p \<in> r" "x = snd p" by (rule repfunE[OF rset snd])
        hence "p : SetMem ** SetMem" using setof_mem[OF rtyp] by auto
        then obtain a b where "p : Pair" "p = pair a b" "a : SetMem" "b : SetMem" 
          using setmem_pair by (blast elim: productE)
        thus "\<exists>y. app r x y \<or> app r y x" 
          unfolding app_def using p by auto
      qed
    next
      assume "\<exists>y. app r x y \<or> app r y x"
      then obtain y where "x : SetMem" "y : SetMem" and xy:"pair x y \<in> r \<or> pair y x \<in> r" 
        unfolding app_def by blast
      hence fstx:"x = fst (pair x y)" and sndx:"x = snd (pair y x)" 
        using fst_eq snd_eq setmem_pair  by auto
      show "x \<in> RepFun r fst \<union> RepFun r snd" 
        unfolding un_iff[OF repfun_set[OF rset fst] repfun_set[OF rset snd]]
      proof (rule disjE[OF xy], rule_tac [1] disjI1 , rule_tac [2] disjI2)
        assume "pair x y \<in> r" thus "x \<in> RepFun r fst" 
          using repfunI[OF rset fst, of "pair x y"] fstx by auto
      next
        assume "pair y x \<in> r" thus "x \<in> RepFun r snd"
          using repfunI[OF rset snd, of "pair y x"] sndx by auto
      qed
    qed
  qed
qed

interpretation Function
  where Function = FuncRel
    and app = app
    and mkfun = mk_funrel
    and dom = domain
  by (rule Function_interpretation)
 *)
end
end