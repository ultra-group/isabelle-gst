theory SetRel
  imports 
    "../GST_Features" "../OPair/CartProd" "../Relations/Relations" 
    SetComprehension SetCombinators 
begin

(*Developments that use sets and ordered pairs! 
    e.g., relations as sets, functions as sets, cartesian product
  The SetRel interface abstracts over the representation of sets and pairs.*)
context CartProd begin

section \<open>Relations and Functions as sets of ordered pairs\<close>

definition setrel_app 
  where "setrel_app r a b \<equiv> a : SetMem \<and> b : SetMem \<and> pair a b \<in> r"
definition mk_setrel 
  where "mk_setrel x y P \<equiv> Collect (cprod x y) (\<lambda>p. P (fst p) (snd p))"
definition setrel_field 
  where "setrel_field r \<equiv> RepFun r fst \<union> RepFun r snd"

theorem GZF_BinRel : 
  "class.BinRel_axioms Set (\<in>) (\<subseteq>) SetOf 
    setrel_app (SetOf (SetMem * SetMem)) mk_setrel setrel_field 
    (\<lambda>x. \<P> (x \<times> x)) SetMem"
proof
  show mkrel_typ : "mk_setrel : Set \<rightarrow> Set \<rightarrow> Any \<rightarrow> SetOf (SetMem * SetMem)"
    unfolding mk_setrel_def
  proof (rule funI, rule funI, rule funI, rule collect_typ_subset)
    fix x y assume "x : Set" "y : Set"
    hence "x : SetOf SetMem" "y : SetOf SetMem" using setofI setmemI by auto
    thus "x \<times> y : SetOf (SetMem * SetMem)" using cprod_setof_prod by auto
  qed

  show "setrel_field : SetOf (SetMem * SetMem) \<rightarrow> Set" 
    unfolding setrel_field_def
  by (rule funI, rule un_set[OF repfun_set repfun_set], use setof_set in auto)
  
  show "(\<lambda>x. \<P> (x \<times> x)) : Set \<rightarrow> SetOf (SetOf (SetMem * SetMem))"
  proof (rule funI, rule setofI, rule pow_set[OF cprod_set], 
         auto, rule setofI)
    fix x r assume 
      x : "x : Set" and r : "r \<in> \<P> (x \<times> x)"
    thus "r : Set"  
      using setof_mem[OF pow_setof[OF cprod_set[OF x x]]]   
      by auto
   fix p assume "p \<in> r" 
   moreover have "r \<subseteq> x \<times> x" 
      using powD[OF cprod_set[OF x x] r] .
   ultimately show "p : SetMem * SetMem"
    using cprod_setof_prod[OF set_setof set_setof, OF x x, THEN setof_mem]
      by auto
  qed

 show "\<forall>x : Set. \<forall>y : Set. \<forall>P.
          \<forall>a b. setrel_app (mk_setrel x y P) a b \<longleftrightarrow> 
            (a \<in> x \<and> b \<in> y \<and> P a b \<and> a : SetMem \<and> b : SetMem)"
  proof (rule, rule, rule, rule, rule, rule)
    fix x y P a b assume "x : Set" "y : Set"
    hence rtyp : "mk_setrel x y P : SetOf (SetMem * SetMem)" 
      by (rule funE[OF funE[OF funE[OF mkrel_typ]] anyI])

    show "setrel_app (mk_setrel x y P) a b \<Longrightarrow> 
      (a \<in> x \<and> b \<in> y \<and> P a b \<and> a : SetMem \<and> b : SetMem)"
    unfolding setrel_app_def proof (auto)
      assume "a : SetMem" "b : SetMem" "<a, b> \<in> mk_setrel x y P"
      hence "<a,b> : Pair" "<a,b> \<in> x \<times> y" "P (fst (pair a b)) (snd (pair a b))"
          using setmem_pair mk_setrel_def collect_iff[OF cprod_set[OF \<open>x : Set\<close> \<open>y : Set\<close>]] by auto
      thus "a \<in> x" "b \<in> y" "P a b" using fst_eq snd_eq cprod_iff_pair[OF \<open>x : Set\<close> \<open>y : Set\<close>] by auto
    qed
    show "a \<in> x \<and> b \<in> y \<and> P a b \<and> a : SetMem \<and> b : SetMem \<Longrightarrow> 
      setrel_app (mk_setrel x y P) a b"
      unfolding setrel_app_def mk_setrel_def 
    proof (auto intro: setmemI[OF \<open>x : Set\<close>] setmemI[OF \<open>y : Set\<close>], 
           rule collectI[OF cprod_set[OF \<open>x : Set\<close> \<open>y : Set\<close>]],
           auto intro: cprodI_pair[OF \<open>x : Set\<close> \<open>y : Set\<close>])
      assume "a \<in> x" "b \<in> y" "P a b"
      moreover hence "pair a b : Pair" using setmemI \<open>x : Set\<close> \<open>y : Set\<close> setmem_pair by auto
      ultimately show "P (\<tau> (pair a b)) (\<pi> (pair a b))"
        using fst_eq snd_eq by auto  
    qed
  qed

  show "\<forall>r : SetOf (SetMem * SetMem). \<forall>s : SetOf (SetMem * SetMem).
          (\<forall>a b. setrel_app r a b = setrel_app s a b) \<longrightarrow> r = s" 
  proof (rule)+
    fix r s assume 
      r: "r : SetOf (SetMem * SetMem)" and 
      s: "s : SetOf (SetMem * SetMem)" and 
      ab:"\<forall>a b. setrel_app r a b \<longleftrightarrow> setrel_app s a b" 
    show "r = s" 
    proof (rule equality_iffI[OF setof_set[OF r] setof_set[OF s]])
      fix p show "p \<in> r \<longleftrightarrow> p \<in> s"
      proof
        assume "p \<in> r" 
        moreover then obtain a b where 
          "p = pair a b" "a : SetMem" "b : SetMem" 
          using setof_mem[OF r] by (blast elim: productE)
        ultimately have "setrel_app r a b" 
          unfolding setrel_app_def by auto
        hence "setrel_app s a b" using ab by simp
        thus "p \<in> s" unfolding setrel_app_def using ab \<open>p = pair a b\<close> \<open>p \<in> r\<close> by auto
      next
        assume "p \<in> s" 
        moreover then obtain a b where 
          "p = pair a b" "a : SetMem" "b : SetMem" 
          using setof_mem[OF s] by (blast elim: productE)
        ultimately have "setrel_app s a b" 
          unfolding setrel_app_def by auto
        hence "setrel_app r a b" using ab by simp
        thus "p \<in> r" 
          unfolding setrel_app_def 
          using ab \<open>p = pair a b\<close> \<open>p \<in> s\<close> by auto
      qed
    qed
  qed

  show "\<forall>r : SetOf (SetMem * SetMem). 
    \<forall>x. (x \<in> setrel_field r) = (\<exists>y. setrel_app r x y \<or> setrel_app r y x)"
  proof (rule, rule)
    fix r x assume rtyp:"r : SetOf (SetMem * SetMem)"
    hence rset:"r : Set" by (rule setof_set)

    show "x \<in> setrel_field r \<longleftrightarrow> (\<exists>y. setrel_app r x y \<or> setrel_app r y x)" 
      unfolding setrel_field_def
    proof (rule)
      assume "x \<in> RepFun r \<tau> \<union> RepFun r \<pi>"
      thus "\<exists>y. setrel_app r x y \<or> setrel_app r y x" 
      proof (rule unE[OF repfun_set[OF rset] repfun_set[OF rset]])
        assume "x \<in> RepFun r \<tau>"
        then obtain p where p:"p \<in> r" "x = fst p" by (rule repfunE[OF rset])
        hence "p : SetMem * SetMem" using setof_mem[OF rtyp] by auto
        then obtain a b where "p : Pair" "p = pair a b" "a : SetMem" "b : SetMem" 
          using setmem_pair by (blast elim: productE)
        thus "\<exists>y. setrel_app r x y \<or> setrel_app r y x" 
          unfolding setrel_app_def using p by auto
      next
        assume "x \<in> RepFun r \<pi>"
        then obtain p where p:"p \<in> r" "x = snd p" by (rule repfunE[OF rset])
        hence "p : SetMem * SetMem" using setof_mem[OF rtyp] by auto
        then obtain a b where "p : Pair" "p = pair a b" "a : SetMem" "b : SetMem" 
          using setmem_pair by (blast elim: productE)
        thus "\<exists>y. setrel_app r x y \<or> setrel_app r y x" 
          unfolding setrel_app_def using p by auto
      qed
    next
      assume "\<exists>y. setrel_app r x y \<or> setrel_app r y x"
      then obtain y where 
        "x : SetMem" "y : SetMem" and 
        xy:"pair x y \<in> r \<or> pair y x \<in> r" 
        unfolding setrel_app_def by blast
      hence fstx:"x = fst (pair x y)" and sndx:"x = snd (pair y x)" 
        using fst_eq snd_eq setmem_pair by auto
      show "x \<in> RepFun r fst \<union> RepFun r snd" 
        unfolding un_iff[OF repfun_set[OF rset] repfun_set[OF rset]]
      proof (rule disjE[OF xy], rule_tac [1] disjI1 , rule_tac [2] disjI2)
        assume "pair x y \<in> r" thus "x \<in> RepFun r fst" 
          using repfunI[OF rset, of "pair x y" fst] fstx \<open>x : SetMem\<close> by auto
      next
        assume "pair y x \<in> r" thus "x \<in> RepFun r snd"
          using repfunI[OF rset, of "pair y x" snd] sndx \<open>x : SetMem\<close> by auto
      qed
    qed
  qed

  show "\<forall>x : Set. \<forall>r : SetOf (SetMem * SetMem).
          (r \<in> \<P> (x \<times> x)) = (setrel_field r \<subseteq> x)"
  proof (rule, rule)
    fix x r assume x : "x : Set" and r : "r : SetOf (SetMem * SetMem)"
    hence r' : "r : Set" using setof_set[OF r] by auto
    show "(r \<in> \<P> (x \<times> x)) \<longleftrightarrow> (setrel_field r \<subseteq> x)"
    proof
      assume "r \<in> \<P> (x \<times> x)"
      hence r_sub : "r \<subseteq> x \<times> x" 
        using powD[OF cprod_set[OF x x]] by auto
      show "setrel_field r \<subseteq> x"
      proof
        fix b assume "b \<in> setrel_field r"
        hence "b \<in> RepFun r fst \<or> b \<in> RepFun r snd"
          unfolding setrel_field_def un_iff[OF repfun_set repfun_set, OF r' r'] .
        then obtain p where "p \<in> r" "b = fst p \<or> b = snd p"
          using repfunE[OF r'] by metis
        thus "b \<in> x"
          using fst_set[OF x x] snd_set[OF x x] r_sub by auto
      qed
    next
      assume f_sub:"setrel_field r \<subseteq> x"
      show "r \<in> \<P> (x \<times> x)"
      proof (rule powI[OF r' cprod_set[OF x x]], rule)
        fix p assume "p \<in> r"
        moreover hence 
          "p : Pair" "fst p : SetMem" "snd p : SetMem"
          using productD[OF setof_mem[OF r]] by auto
        ultimately have 
          "fst p \<in> RepFun r fst" "snd p \<in> RepFun r snd"
          using repfunI[OF r'] by auto
        hence "fst p \<in> x" "snd p \<in> x"
          using f_sub un_iff[OF repfun_set repfun_set, OF r' r']
          unfolding setrel_field_def by auto
        thus "p \<in> x \<times> x"
          using pair_proj_eq[OF \<open>p : Pair\<close>] 
            cprodI_pair[OF x x, of \<open>\<tau> p\<close> \<open>\<pi> p\<close>] by auto
      qed
    qed
  qed
       
  show "SetMem = (\<lambda>b. \<exists>r : SetOf (SetMem * SetMem). \<exists>c. setrel_app r b c \<or> setrel_app r c b)"
  proof -
    have eq:"\<forall>b. b : SetMem \<longleftrightarrow> (\<exists>r : SetOf (SetMem * SetMem). \<exists>c. setrel_app r b c \<or> setrel_app r c b)"
      unfolding setrel_app_def
    proof (auto)
      fix b assume b: "b : SetMem"
      hence bb_smem: "<b,b> : SetMem" and "<b,b> : SetMem * SetMem"
        using pair_setmem[OF smem_pmem smem_pmem, of b b] 
              productI[OF setmem_pair, of b b SetMem SetMem] by auto
      hence "{<b,b>} : SetOf (SetMem * SetMem)"
        using setofI[OF sng_set[of \<open><b,b>\<close>], of \<open>SetMem * SetMem\<close>] sng_iff by auto
      thus "\<exists>r : SetOf (SetMem * SetMem). 
              \<exists>c. c : SetMem \<and> \<langle>b,c\<rangle> \<in> r \<or> c : SetMem \<and> \<langle>c,b\<rangle> \<in> r "  
        using bb_smem b sngI[OF bb_smem] 
        unfolding tex_def by auto
    qed
    show ?thesis 
      by (rule, insert spec[OF eq], unfold has_ty_def, auto)
  qed
qed

sublocale BinRel
  where BinRel = "SetOf (SetMem * SetMem)"
    and app = setrel_app
    and mkrel = mk_setrel
    and field = setrel_field
    and relspace = \<open>(\<lambda>x. \<P> (x \<times> x))\<close>    
    and BinRelMem = SetMem
    and BinRelation_default = GZF_default
  using GZF_BinRel by intro_locales

theorem GZF_Function :
  "class.Function_axioms Set (\<in>) (\<subseteq>) SetOf setrel_app
     FuncRel mk_funrel domain range mk_funspace SetMem FuncRelPred"
  using BinRel_Function .

sublocale Function
  where Function = FuncRel
    and app = setrel_app
    and mkfun = mk_funrel
    and dom = domain
    and ran = range
    and funspace = mk_funspace
    and FunMem = SetMem
    and FunPred = FuncRelPred
  using GZF_Function by intro_locales

end
end