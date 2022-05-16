theory Functions
  imports "../GZF/SetComprehension" "../GZF/SetCombinators"
  abbrevs "pspace" = \<open>\<midarrow>p\<rightarrow>\<close>
begin

context Function begin

thm mkfun_typ dom_typ
thm mkfun_ax fun_prop fun_ext fun_dom

lemmas mkfun_fun = funE[OF depfunE[OF mkfun_typ]]
lemmas dom_set = funE[OF dom_typ]

section \<open>Basic properties of function application relation\<close>

lemma funpredI : 
  assumes "\<And>b. b : FunMem \<Longrightarrow> b \<in> x \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1 c : FunMem. P b c"
  shows "P : FunPred x"
  using assms
  unfolding FunPred_def has_ty_def tall_def
  by auto

lemma app_eqI :
  assumes f:"f : Function" 
  and y:"app f x y" and z:"app f x z"
  shows "y = z"
  using fun_prop f y z 
  by auto

lemma fun_eqI :
  assumes f:"f : Function" and g:"g : Function"
      and xy:"\<And>x y. app f x y \<longleftrightarrow> app g x y"
    shows "f = g"
  using fun_ext f g xy by auto 

lemma mkfun_iff : 
  assumes x:"x : Set" and P:"P : FunPred x"
  shows "app (mkfun x P) b c \<longleftrightarrow> b \<in> x \<and> P b c \<and> b : FunMem \<and> c : FunMem"
  using mkfun_ax x P by auto



section \<open>Function application operator\<close>
(*rapp and fapp*)
definition funapp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl \<open>`\<close> 70)
  where "funapp f x \<equiv> \<iota>' Function_default (\<lambda>y. app f x y)"

lemma funappI :
  assumes f:"f : Function" and app:"app f x y"
    shows "f`x = y"
  unfolding funapp_def
  by (rule the_def_eq, use app app_eqI[OF f] in auto)

lemma funapp_default : 
  assumes f:"f : Function" 
      and app:"\<And>y. \<not> app f x y"
    shows "f ` x = Function_default"
  unfolding funapp_def
  by (rule the_def_default, 
      use app in auto)
  
lemma funappE :
  assumes f:"f : Function" and eq:"f`x = y" 
      and y:"y \<noteq> Function_default" 
    shows "app f x y"
proof (cases \<open>\<exists>!y. app f x y\<close>)
  case True
  hence "app f x (f ` x)" 
    unfolding funapp_def using the_defI' by auto
  then show ?thesis by (unfold eq)
next
  case False
  hence d:"f ` x = Function_default" 
    unfolding funapp_def by (rule the_def_default)
  show ?thesis by (rule ccontr, use eq y d in auto)
qed

section \<open>Domain, Range, and Field\<close>

subsection \<open>Domain of function\<close>

lemma dom_iff :
  assumes f:"f : Function"
  shows "x \<in> dom f \<longleftrightarrow> (\<exists> y. app f x y)"
  using fun_dom f by auto

lemma domI :
  assumes f:"f : Function" and xy:"app f x y"
    shows "x \<in> dom f" 
  using fun_dom f xy by auto

lemma domE : 
  assumes f:"f : Function" and xy:"x \<in> dom f"
  obtains y where "app f x y" 
  using fun_dom f xy by auto

lemma funapp_dom :
  assumes f:"f : Function" and x:"x \<in> dom f" 
    shows "app f x (f ` x)"
proof -
  obtain z where z:"app f x z" using domE[OF f x] by auto
  hence "f ` x = z" by (rule funappI[OF f])
  thus "app f x (f ` x)" using z by auto
qed

lemma mkfun_dom : 
  assumes x:"x : Set" and P:"P : FunPred x"
    shows "b \<in> dom (mkfun x P) 
    \<longleftrightarrow> b \<in> x \<and> b : FunMem \<and> (\<exists>c. P b c \<and> c : FunMem)"
  unfolding dom_iff[OF mkfun_fun[OF x P]] mkfun_iff[OF x P]
  by auto

subsection \<open>Range of Function\<close>

lemma ran_iff :
  assumes f:"f : Function"
  shows "y \<in> ran f \<longleftrightarrow> (\<exists>x. app f x y)"
  using fun_ran f by auto

lemmas ran_set = funE[OF ran_typ]  

lemma ranI : 
  assumes f:"f : Function" 
      and b:"app f a b" 
    shows "b \<in> ran f"
  using fun_ran f b by auto

lemma ranE :
  assumes f:"f : Function" and b:"b \<in> ran f"
  obtains a where "app f a b" "a \<in> dom f"
  using fun_ran f b domI by auto

lemma ran_appE :
  assumes f:"f : Function" and b:"b \<in> ran f"
  obtains a where "f ` a = b" "a \<in> dom f"
  using ranE[OF f b] funappI[OF f]
  by metis

lemma ran_app :
  assumes f:"f : Function"
      and b:"b \<in> dom f"
    shows "f ` b \<in> ran f"
  by (rule ranI[OF f], rule domE[OF f b], 
      use funappI[OF f] in auto)  

subsection \<open>Field of a function\<close>

definition field :: "'a \<Rightarrow> 'a"
  where "field f \<equiv> dom f \<union> ran f"

lemma field_typ : "field : Function \<rightarrow> Set"
  unfolding field_def by (rule funI, rule un_set[OF dom_set ran_set])

lemmas field_set = funE[OF field_typ]

lemma field_iff :
  assumes f:"f : Function"
  shows "b \<in> field f \<longleftrightarrow> (b \<in> dom f \<or> b \<in> ran f)"
  unfolding field_def un_iff[OF dom_set[OF f] ran_set[OF f]] 
  by rule

lemma field_dom_subset :
  assumes f:"f : Function"
  shows "dom f \<subseteq> field f"
  unfolding field_def 
  by (rule un_subset1[OF dom_set[OF f] ran_set[OF f]]) 

lemma field_ran_subset :
  assumes f:"f : Function"
  shows "ran f \<subseteq> field f"
  unfolding field_def 
  by (rule un_subset2[OF dom_set[OF f] ran_set[OF f]]) 

lemmas field_domI = subsetD[OF field_dom_subset]
lemmas field_ranI = subsetD[OF field_ran_subset]

lemma field_disjE :
  assumes f:"f : Function" and b:"b \<in> field f"
  obtains (dom) c where "c \<in> dom f"
        | (ran) c where "c \<in> ran f"
  using b unfolding field_iff[OF f] 
  by auto

lemma field_app_iff :
  assumes f:"f : Function"
  shows "y \<in> field f \<longleftrightarrow> (\<exists>x. app f x y \<or> app f y x)"
  unfolding field_iff[OF f] dom_iff[OF f] ran_iff[OF f] 
  by auto

lemma field_appI1 : 
  assumes f:"f : Function" and app:"app f x y"
  shows "x \<in> field f"
  using field_app_iff[OF f] app 
  by auto

lemma field_appI2 : 
  assumes f:"f : Function" and app:"app f x y"
  shows "y \<in> field f"
  using field_app_iff[OF f] app 
  by auto

lemma field_app_disjE : 
  assumes f:"f : Function" and b:"b \<in> field f"
  obtains (dom) c where "app f b c"
        | (ran) c where "app f c b" 
  using field_app_iff[OF f] b by auto

subsection \<open>FunMem soft-type\<close>

lemma funmemI1 : 
  assumes f:"f : Function" and app:"app f x y"
  shows "x : FunMem"
  unfolding FunMem_def 
  by (rule tyI, use f app in auto)

lemma funmemI2 : 
  assumes f:"f : Function" and app:"app f x y"
  shows "y : FunMem"
  unfolding FunMem_def 
  by (rule tyI, use f app in auto)

lemma dom_funmem : 
  assumes f:"f : Function" and dom:"x \<in> dom f"
  shows "x : FunMem"
  by (rule domE[OF f dom], rule funmemI1[OF f])

lemma ran_funmem :
  assumes f:"f : Function" and ran:"x \<in> ran f"
  shows "x : FunMem"
  by (rule ranE[OF f ran], rule funmemI2[OF f])

lemma field_funmem : 
  assumes f:"f : Function" and field:"x \<in> field f"
  shows "x : FunMem"
  using field dom_funmem[OF f] ran_funmem[OF f] 
  unfolding field_iff[OF f]
  by auto

lemma funmem_appI : 
  assumes f:"f : Function" and b:"b \<in> dom f"
  shows "f ` b : FunMem"
  by (rule ran_funmem[OF f ran_app[OF f b]])
  
  lemma fmem_smem :
  assumes "b : FunMem"
  shows "b : SetMem"
  using assms setmemI[OF dom_set domI] setmemI[OF ran_set ranI]
  unfolding FunMem_def has_ty_def tex_def by auto
  
section \<open>Restrictions on functions\<close>

subsection \<open>Restriction of functions by a predicate\<close>

lemma restrict_funpred :
  assumes f:"f : Function"
  shows "(\<lambda>a b. P a \<and> app f a b): FunPred (dom f)"
  by (rule funpredI, unfold tuniq_def Uniq_def, 
      use app_eqI[OF f] in auto)

definition restrict :: "['a, 'a \<Rightarrow> bool] \<Rightarrow> 'a" (infixl \<open>\<lceil>\<close> 60)
  where "f \<lceil> P \<equiv> mkfun (dom f) (\<lambda>b c. P b \<and> app f b c)"

lemma restrict_typ :
  "restrict : Function \<rightarrow> Any \<rightarrow> Function"
  unfolding restrict_def
  by (rule funI, rule funI, rule mkfun_fun[OF dom_set restrict_funpred])

lemmas restrict_fun = funE[OF funE[OF restrict_typ] anyI]

lemma restrict_iff :
  assumes f:"f : Function"
  shows "app (f \<lceil> P) b c \<longleftrightarrow> P b \<and> app f b c"
  unfolding restrict_def mkfun_iff[OF dom_set[OF f] 
            restrict_funpred[OF f]] dom_iff[OF f] 
  using funmemI1[OF f] funmemI2[OF f] 
  by auto

lemma restrictI : 
  assumes f:"f : Function"
  and b:"P b" and app:"app f b c"
  shows "app (f \<lceil> P) b c"
  using restrict_iff[OF f] b app by auto

lemma restrictD1 : 
  assumes f:"f : Function"
      and app:"app (f \<lceil> P) b c"
    shows "P b"
  using restrict_iff[OF f] app by auto

lemma restrictD2 : 
  assumes f:"f : Function"
      and app:"app (f \<lceil> x) b c"
    shows "app f b c"
  using restrict_iff[OF f] app by auto

lemma restrict_dom :
  assumes f:"f : Function"
  shows "b \<in> dom (f \<lceil> P) \<longleftrightarrow> b \<in> dom f \<and> P b"
  unfolding dom_iff[OF restrict_fun[OF f]]
            dom_iff[OF f] restrict_iff[OF f] 
  by auto

lemma restrict_domI : 
  assumes f:"f : Function" 
      and b:"b \<in> dom f" "P b"
    shows "b \<in> dom (f \<lceil> P)"
  using restrict_dom[OF f] b by auto

lemmas restrict_domD = iffD1[OF restrict_dom]

lemma restrict_app : 
  assumes f:"f : Function" 
      and b:"P b" and dom:"b \<in> dom f"
    shows "(f \<lceil> P) ` b = f ` b"
proof (rule funappI[OF restrict_fun[OF f]])
  have "b \<in> dom (f \<lceil> P)" 
    unfolding restrict_dom[OF f]
    using b dom by auto
  hence "app f b (f ` b)" using funapp_dom[OF f dom] by auto
  thus "app (f \<lceil> P) b (f ` b)" using restrict_iff[OF f] b by auto
qed

lemma restrict_default :
  assumes f:"f : Function"
      and b:"\<not> P b"
    shows "(f \<lceil> P) ` b = Function_default"
  by (rule funapp_default[OF restrict_fun[OF f]], 
      use restrict_iff[OF f] b in auto)

subsection \<open>Restriction of functions by a set\<close>

definition set_restrict :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl \<open>\<restriction>\<close> 60)
  where "f \<restriction> x \<equiv> f \<lceil> (\<lambda>b. b \<in> x)"

lemma set_restrict_typ :
  "restrict : Function \<rightarrow> Any \<rightarrow> Function"
  unfolding restrict_def
  by (rule funI, rule funI, rule mkfun_fun[OF dom_set restrict_funpred])

lemmas set_restrict_fun = funE[OF funE[OF set_restrict_typ] anyI]

lemma set_restrict_iff :
  assumes f:"f : Function"
  shows "app (f \<restriction> x) b c \<longleftrightarrow> b \<in> x \<and> app f b c"
  by (simp only: set_restrict_def restrict_iff[OF f])

lemma set_restrictI : 
  assumes f:"f : Function"
  and b:"b \<in> x" and app:"app f b c"
  shows "app (f \<restriction> x) b c"
  unfolding set_restrict_def
  using restrictI assms by auto

lemma set_restrictD1 : 
  assumes f:"f : Function"
      and app:"app (f \<restriction> x) b c"
    shows "b \<in> x"
  using restrictD1 assms
  unfolding set_restrict_def
  by auto

lemma set_restrictD2 :
  assumes f:"f : Function"
      and app:"app (f \<restriction> x) b c"
    shows "app f b c"
  using restrictD2 assms
  unfolding set_restrict_def
  by auto

lemma set_restrict_dom :
  assumes f:"f : Function"
  shows "b \<in> dom (f \<restriction> x) \<longleftrightarrow> b \<in> dom f \<and> b \<in> x"
  unfolding set_restrict_def
  using restrict_dom assms
  by auto

lemma set_restrict_domI : 
  assumes f:"f : Function" 
      and b:"b \<in> dom f" "b \<in> x"
    shows "b \<in> dom (f \<restriction> x)"
  using set_restrict_dom[OF f] b by auto

lemmas set_restrict_domD = iffD1[OF set_restrict_dom]

lemma set_restrict_app : 
  assumes f:"f : Function" 
      and b:"b \<in> x" and dom:"b \<in> dom f"
    shows "(f \<restriction> x) ` b = f ` b"
  unfolding set_restrict_def
  using restrict_app assms
  by auto

lemma set_restrict_default :
  assumes f:"f : Function"
      and b:"b \<notin> x"
    shows "(f \<restriction> x) ` b = Function_default"
  unfolding set_restrict_def
  using restrict_default assms
  by auto


section \<open>Partial Functions\<close>

definition typish_partial_fun :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infixr \<open>\<Zpfun>''\<close> 70)
  where "x \<Zpfun>' y \<equiv> Function \<triangle> (\<lambda>f. (\<forall>a b. a \<in> x \<longrightarrow> app f a b \<longrightarrow> b \<in> y))" 

definition partial_fun :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infixr \<open>\<Zpfun>\<close> 70)
  where "x \<Zpfun> y \<equiv> (x \<Zpfun>' y) \<triangle> (\<lambda>f. dom f \<subseteq> x)"

lemma pfun_fun :
  assumes f:"f : x \<Zpfun>' y"
    shows "f : Function"
  using f unfolding typish_partial_fun_def 
  by (rule intE1)

lemma pfunI : 
  assumes f:"f : Function"
      and xy:"\<And>a b. a \<in> x \<Longrightarrow> app f a b \<Longrightarrow> b \<in> y"
    shows "f : x \<Zpfun>' y"
  unfolding typish_partial_fun_def
  by (rule intI[OF f], rule tyI, use xy in auto)

lemma pfunE :
  assumes f:"f : x \<Zpfun>' y" 
     and ab:"a \<in> x" "app f a b"
  shows "b \<in> y"
  using f ab unfolding typish_partial_fun_def has_ty_def inter_ty_def 
  by auto

lemma pfun_dom :
  assumes f:"f : x \<Zpfun>' y" 
      and b:"b \<in> x" and dom:"b \<in> dom f"
    shows "f ` b \<in> y"
proof (rule domE[OF pfun_fun[OF f] dom])
  fix c assume "app f b c"
  moreover hence "f`b = c" by (rule funappI[OF pfun_fun[OF f]])
  ultimately show "f ` b \<in> y" using pfunE[OF f b] by auto
qed

lemma pfun_app : 
  assumes f:"f : x \<Zpfun>' y" and a:"a \<in> x"
      and not_default:"f ` a \<noteq> Function_default"
    shows "f ` a \<in> y"
  using pfunE[OF f a] funappE[OF pfun_fun[OF f] _ not_default] 
  by auto

lemma pfun_app_disj :
  assumes f:"f : x \<Zpfun>' y" and b:"b \<in> x"
    shows "f ` b \<in> y \<or> f ` b = Function_default"
  using pfun_app[OF f b] by auto

section \<open>Total Functions\<close>

(*Consider changing soft-type arrow for ('a \<Rightarrow> 'b) to \<Rightarrow> or \<Rrightarrow>, then use \<rightarrow> for 'a-functions *)
definition typish_total_fun :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infixr \<open>\<leadsto>''\<close> 70)
  where "x \<leadsto>' y \<equiv> (x \<Zpfun>' y) \<triangle> (\<lambda>f. x \<subseteq> dom f)"

lemma typish_tfunI :
  assumes f:"f : (x \<Zpfun>' y)"
      and bc:"x \<subseteq> dom f"
    shows "f : x \<leadsto>' y"
  unfolding typish_total_fun_def 
  by (rule intI[OF f], rule tyI, use bc in auto)

definition total_fun :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infixr \<open>\<midarrow>t\<rightarrow>\<close> 70)
  where "x \<midarrow>t\<rightarrow> y \<equiv> (x \<leadsto>' y) \<triangle> (\<lambda>f. dom f \<subseteq> x)"

lemma tfunI :
  assumes f : "f : (x \<leadsto>' y)"
      and df : "dom f \<subseteq> x"
    shows "f : (x \<midarrow>t\<rightarrow> y)"
  unfolding total_fun_def
  by (rule intI[OF f], rule tyI, rule df) 

section \<open>Forming functions from ('a=>'a)-operators\<close>

lemma any_funpredI :
  "(\<lambda>a b. b = F a) : FunPred x"
  by (rule funpredI, unfold tuniq_def Uniq_def, auto)

definition lam :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "lam x F \<equiv> mkfun x (\<lambda>a b. b = F a)"

end

syntax
  "_lam_set" :: "[pttrn, 'a, 'a] => 'a" (\<open>(3\<lambda>_\<in>_./ _)\<close> 10)
translations
  "\<lambda>b \<in> x. F" \<rightleftharpoons> "CONST lam x (\<lambda>b. F)"

context Function begin

lemma lam_fun :
  assumes x : "x : Set"
    shows "(\<lambda>b\<in>x. F b) : Function"
  unfolding lam_def 
  by (rule mkfun_fun[OF x any_funpredI])

lemma lam_iff :
  assumes x:"x : Set"  
    shows "app (\<lambda>b\<in>x. F b) b c \<longleftrightarrow> b \<in> x \<and> b : FunMem \<and> c = F b \<and> c : FunMem"
  unfolding lam_def 
  using mkfun_ax x any_funpredI by auto

lemma lam_iff' :
  assumes x:"x : Set"
  shows "app (\<lambda>b\<in>x. F b) b (F b) \<longleftrightarrow> b \<in> x \<and> b : FunMem \<and> F b : FunMem"
  unfolding lam_def using mkfun_ax x any_funpredI by auto

lemma lam_app :
  assumes x:"x : Set" and F:"F : x \<leadsto> FunMem" 
      and b : "b \<in> x" "b : FunMem"
    shows "(\<lambda>b\<in>x. F b) ` b = F b"
  by (rule funappI[OF lam_fun[OF x]], 
      unfold lam_iff[OF x],
      use b mem_funE[OF F] in auto)

lemma lam_dom :
  assumes x:"x : SetOf FunMem" and F:  "F : x \<leadsto> FunMem"
    shows "dom (\<lambda>b\<in>x. F b) = x"
proof (rule equality_iffI[OF dom_set[OF lam_fun[OF setof_set[OF x]]] 
                             setof_set[OF x]],
       unfold collect_iff[OF setof_set[OF x]] dom_iff[OF lam_fun[OF setof_set[OF x]]], auto)
  fix b c assume "app (\<lambda>b\<in>x. F b) b c"       
  thus "b \<in> x" unfolding lam_iff[OF setof_set[OF x]] by auto
next
  fix b assume "b \<in> x"
  thus "\<exists>c. app (\<lambda>b\<in>x. F b) b c"  
    using lam_iff[OF setof_set[OF x]] setof_mem[OF x] 
          mem_funE[OF F] by auto
qed

lemma lam_ran : 
  assumes x:"x : SetOf FunMem" and F:"F : x \<leadsto> FunMem"
    shows "ran (\<lambda>b\<in>x. F b) = { F b | b \<in> x }"
proof -
  have func:"(\<lambda>b\<in>x. F b) : Function"
    using lam_fun[OF setof_set[OF x]] by auto
  hence set:"{F b | b \<in> x} : Set"
    using repfun_set[OF setof_set[OF x]] by auto

  thus ?thesis 
     using equality_iffI[OF ran_set[OF func] set]
           mem_funE[OF F] setof_mem[OF x] fmem_smem
     unfolding repfun_iff[OF setof_set[OF x]] ran_iff[OF func] 
               lam_iff[OF setof_set[OF x]] bex_def rex_def
     by auto
qed

lemma lam_ran_setof : 
  assumes x:"x : Set" 
      and F:"F : x \<leadsto> Set"
  shows "ran (\<lambda>b\<in>x. F b) : SetOf Set"
proof (rule setofI)   
  show "ran (\<lambda>b\<in>x. F b) : Set"
    using ran_set[OF lam_fun[OF x]] by auto

  fix b assume "b \<in> ran (\<lambda>b\<in>x. F b)"
  thus "b : Set" 
    unfolding ran_iff[OF lam_fun[OF x]] lam_iff[OF x]
    using mem_funE[OF F] by auto
qed

lemma lam_cong : 
assumes x:"x : Set" 
  and eq:"\<And>b. b \<in> x \<Longrightarrow> F b = G b"
  shows "(\<lambda>b\<in>x. F b) = (\<lambda>b\<in>x. G b)"
  by (rule fun_eqI[OF lam_fun[OF x] lam_fun[OF x]], 
      unfold lam_iff[OF x], use eq in auto) 
 

lemma lam_flatten : 
  assumes x:"x : SetOf FunMem" 
      and F:"F : x \<leadsto> FunMem"
    shows "(\<lambda>b\<in>x. (\<lambda>b\<in>x. F b) ` b) = (\<lambda>b\<in>x. F b)"
proof (rule lam_cong[OF setof_set[OF x]])
  fix b assume "b \<in> x" 
  thus "(\<lambda>b\<in>x. F b) ` b = F b" 
    using lam_app[OF setof_set[OF x] F] setof_mem[OF x] by auto
qed
  

(* lemma lam_tfun :
  assumes x:"x : SetOf FunMem" and y:"y : SetOf FunMem" 
      and F:"F : MemOf x \<rightarrow> MemOf y" 
    shows "(\<lambda>b\<in>x. F b) : x \<leadsto> y"
proof (rule tfunI[OF lam_fun[OF x]])
  show Fmem:"F : MemOf x \<rightarrow> FunMem"
  proof (rule funI)
    fix b assume "b : MemOf x"
    hence "F b : MemOf y" by (rule funE[OF F])
    thus "F b : FunMem" by (rule setof_mem[OF y memofD])
  qed
  fix b assume "b \<in> x"
  hence "F b \<in> y" using funE[OF F] unfolding MemOf_def by (unfold_typs)
  moreover have "app (lam x F) b (F b)" using lam_iff[OF x Fmem] \<open>b \<in> x\<close> by auto
  ultimately show "\<exists>c. c \<in> y \<and> app (lam x F) b c" by auto
qed *)
lemmas fspace_setof = funE[OF funE[OF funspace_typ]]
lemmas fspace_mem = setof_mem[OF fspace_setof]

lemma fspace_iff : 
  assumes x : "x : Set" and y : "y : Set"
      and f : "f : Function"
    shows "f \<in> x \<midarrow>p\<rightarrow> y \<longleftrightarrow> dom f \<subseteq> x \<and> ran f \<subseteq> y"
  using funspace_ax assms by auto

lemma fspaceI : 
  assumes x : "x : Set" and y : "y : Set"
      and f : "f : Function" 
      and "dom f \<subseteq> x" and "ran f \<subseteq> y"
    shows "f \<in> x \<midarrow>p\<rightarrow> y"
  using assms fspace_iff by auto

lemma fspaceD :
  assumes x : "x : Set" and y : "y : Set"
      and f : "f \<in> x \<midarrow>p\<rightarrow> y"
    shows "dom f \<subseteq> x \<and> ran f \<subseteq> y"
  using fspace_iff[OF x y fspace_mem[OF x y f]] f by auto

lemma fspace_triv :
  assumes f : "f : Function"
  shows "f \<in> dom f \<midarrow>p\<rightarrow> ran f"
  using fspaceI[OF dom_set[OF f] ran_set[OF f] f 
      subset_refl subset_refl] .
     
end
end