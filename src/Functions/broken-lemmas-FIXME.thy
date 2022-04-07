(* lemma tfun_fun : "f : x \<leadsto> y \<Longrightarrow> f : Function" 
  unfolding total_fun_def by (drule intE1)

(*Can't have \<open>\<forall>b \<in> x. f ` b \<in> y\<close> as introduction,
  because we could have \<open>y = {Function_default}\<close>*)
lemma tfunI :
  assumes f:"f : Function"
      and bc:"\<And>b. b \<in> x \<Longrightarrow> (\<exists>c. c \<in> y \<and> app f b c)"
    shows "f : x \<leadsto> y"
  unfolding total_fun_def 
  by (rule intI[OF f], rule tyI, use bc in auto)

lemma tfunE :
  assumes f:"f : x \<leadsto> y" 
      and b:"b \<in> x"
    obtains c where "c \<in> y" "app f b c"
  using f b unfolding total_fun_def has_ty_def inter_ty_def 
  by auto

lemma tfun_app :
  assumes f:"f : x \<leadsto> y"
      and b:"b \<in> x" 
    shows "f ` b \<in> y"
  by (rule tfunE[OF f b], 
      use funappI[OF tfun_fun[OF f]] in auto) 
  
lemma tfun_pfun :
  assumes f:"f : x \<leadsto> y" 
    shows "f : x \<Zpfun> y"
proof (rule pfunI[OF tfun_fun[OF f]])
  fix a b assume "a \<in> x" and b: "app f a b"
  then obtain c where "c \<in> y" and c:"app f a c" by (blast elim: tfunE[OF f])
  thus "b \<in> y" using app_eqI[OF tfun_fun[OF f] b c] by auto
qed
 *)

(* section \<open>Injective functions\<close>

(*Refactor anything that just makes use of \<open>app\<close> to a special locale for
  definitions and theorems for both relations and functions.*)
definition inj :: "'a \<Rightarrow> bool" 
  where "inj f \<equiv> \<forall>x y z. app f x z \<and> app f y z \<longrightarrow> x = y" 

lemma injI :
  assumes "\<And>x y z. app f x z \<Longrightarrow> app f y z \<Longrightarrow> x = y"
  shows "inj f"
  unfolding inj_def using assms 
  by auto

lemma inj_appI :
  assumes f:"f : Function" and eq:"\<And>x y. f ` x = f ` y \<Longrightarrow> x = y"
  shows "inj f"
proof (rule injI)
  fix x y z
  assume "app f x z" "app f y z"
  hence "f ` x = f ` y" using funappI[OF f] by auto
  thus "x = y" by (rule eq)
qed
  
lemma inj_eqI:
  assumes f:"inj f" 
      and x:"app f x z" and y:"app f y z"
    shows "x = y"
  using assms unfolding inj_def 
  by auto

(*Need that x,y \<in> dom f because it is feasible that x\<noteq>y and both f`x and f`y are undefined.*)
lemma inj_app_eqI:
  assumes f:"f : Function" and inj:"inj f"
      and xy:"x \<in> dom f" "y \<in> dom f"  
      and eq:"f`x = f`y"
    shows "x = y"
  by (rule inj_eqI[OF inj], 
      use funapp_dom[OF f] xy eq in auto)


(*REFACTOR TO 'APP' LOCALE - works on relations as well as functions*)
definition inj_on :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "inj_on f x \<equiv> \<forall>b c d. b \<in> x \<longrightarrow> c \<in> x 
                     \<longrightarrow> app f b d \<longrightarrow> app f c d \<longrightarrow> b = c"

lemma inj_onI :
  assumes xy:"\<And>b c d. b \<in> x \<Longrightarrow> c \<in> x \<Longrightarrow> app f b d \<Longrightarrow> app f c d \<Longrightarrow> b = c"
    shows "inj_on f x"
  unfolding inj_on_def using xy by auto

lemma inj_on_appI :
  assumes f:"f: Function" 
      and eq:"\<And>b c d. b \<in> x \<Longrightarrow> c \<in> x \<Longrightarrow> f`b = f`c \<Longrightarrow> b = c"
    shows "inj_on f x"
proof (rule inj_onI)
  fix b c d
  assume "b \<in> x" "c \<in> x" "app f b d" "app f c d"
  hence "f ` b = f ` c" using funappI[OF f] by auto
  thus "b = c" by (rule eq[OF \<open>b \<in> x\<close> \<open>c \<in> x\<close>])
qed

lemma inj_injon :
  assumes f:"f : Function" and inj:"inj (f \<restriction> x)" 
    shows "inj_on f x"
proof (rule inj_onI)
  fix b c d 
  assume "b \<in> x" "c \<in> x" "app f b d" "app f c d" 
  hence "app (f \<restriction> x) b d" "app (f \<restriction> x) c d" by (auto intro: restrictI[OF f])
  thus "b = c" by (rule inj_eqI[OF inj])
qed

lemma inj_on_eqI:
  assumes f:"inj_on f x" 
    and b:"b \<in> x" and c:"c \<in> x" 
    and bc:"app f b d" "app f c d"
  shows "b = c"
  using assms unfolding inj_on_def
  by auto

lemma inj_on_app_eqI:
  assumes f:"f : Function" and inj:"inj_on f x"
    and b:"b \<in> x" "b \<in> dom f" 
    and c:"c \<in> x" "c \<in> dom f" 
    and bc:"f`b = f`c"
  shows "b = c"
  by (rule inj_on_eqI[OF inj \<open>b \<in> x\<close> \<open>c \<in> x\<close>],
      use funapp_dom[OF f] b c bc in auto)

lemma injon_inj :
  assumes f:"f : Function" and inj:"inj_on f x"
  shows "inj (f \<restriction> x)"
  by (rule injI, unfold restrict_iff[OF f], 
      use inj_on_eqI[OF inj] in auto)
    

subsection \<open>Partial injections\<close>

(* "pinj" stands for "partial injection" *)
definition pinj :: "'a \<Rightarrow> 'a \<Rightarrow>'a \<Rightarrow> bool" (infixl \<open>\<Zpinj>\<close> 70)
  where "x \<Zpinj> y \<equiv> x \<Zpfun> y \<bar> (\<lambda>f. inj (f \<restriction> x))"

lemma pinj_pfun : "f : x \<Zpinj> y \<Longrightarrow> f : x \<Zpfun> y"
  unfolding pinj_def by (rule intE1)
lemmas pinj_fun = pfun_fun[OF pinj_pfun]
lemma pinj_inj : "f : x \<Zpinj> y \<Longrightarrow> inj (f \<restriction> x)"
  unfolding pinj_def by (drule intE2, drule tyE)

lemma pinjI: 
  assumes f:"f : x \<Zpfun> y"
    and eq:"\<And>b c d. b \<in> x \<Longrightarrow> c \<in> x \<Longrightarrow> app f b d \<Longrightarrow> app f c d \<Longrightarrow> b = c"
  shows "f : x \<Zpinj> y"
  unfolding pinj_def
  by (rule intI[OF f], rule tyI, rule injI, 
      unfold restrict_iff[OF pfun_fun[OF f]], 
      use eq in auto)

lemma pinj_appI: 
  assumes f:"f : x \<Zpfun> y"
    and eq:"\<And>b c d. b \<in> x \<Longrightarrow> c \<in> x \<Longrightarrow> f`b = f`c \<Longrightarrow> b = c"
  shows "f : x \<Zpinj> y"
  by (rule pinjI[OF f], 
      use funappI[OF pfun_fun[OF f]] eq in auto)

lemma pinj_eqI: 
  assumes f:"f : x \<Zpinj> y"
    and bc:"b \<in> x" "c \<in> x"
    and app:"app f b d" "app f c d"
  shows "b = c"
  by (rule inj_on_eqI[OF inj_injon[OF pinj_fun[OF f] pinj_inj[OF f]] bc app])

lemma pinj_app_eqI:
  assumes f:"f : x \<Zpinj> y"
    and b:"b \<in> x" "b \<in> dom f" 
    and c:"c \<in> x" "c \<in> dom f" 
    and eq:"f`b = f`c"
  shows "b = c"
  by (rule inj_on_app_eqI[OF pinj_fun inj_injon[OF pinj_fun pinj_inj] b c eq], 
      use f in auto)

subsection \<open>Total injections\<close>

(* "tinj" stands for "total injection" *)
definition tinj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl \<open>\<Zinj>\<close> 70)
  where "x \<Zinj> y \<equiv> x \<leadsto> y \<bar> (\<lambda>f. inj (f \<restriction> x))"

lemma tinj_tfun : "f : x \<Zinj> y \<Longrightarrow> f : x \<leadsto> y"
  unfolding tinj_def by (rule intE1)
lemmas tinj_fun = tfun_fun[OF tinj_tfun]

lemma tinj_inj : "f : x \<Zinj> y \<Longrightarrow> inj (f \<restriction> x)"
  unfolding tinj_def by (drule intE2, drule tyE)
lemma tinj_pinj :
  assumes f:"f : x \<Zinj> y"  
    shows "f : x \<Zpinj> y"
  unfolding pinj_def
  by (rule intI[OF tfun_pfun[OF tinj_tfun[OF f]] 
           tyI[of \<open>(\<lambda>f. inj (f \<restriction> x))\<close>, OF tinj_inj[OF f]]])

lemma tinj_injon :
  assumes f:"f : x \<Zinj> y"
  shows "inj_on f x"
  by (rule inj_injon[OF tinj_fun[OF f] tinj_inj[OF f]])
  
lemma tinjI: 
  assumes f:"f : x \<leadsto> y"
      and eq:"\<And>b c d. b \<in> x \<Longrightarrow> c \<in> x
                   \<Longrightarrow> app f b d \<Longrightarrow> app f c d \<Longrightarrow> b = c"
  shows "f : x \<Zinj> y"
  unfolding tinj_def
  by (rule intI[OF f], rule tyI, 
      rule injon_inj[OF tfun_fun[OF f] inj_onI],
      simp only: eq)

lemma tinj_appI: 
  assumes f:"f : x \<leadsto> y"
    and eq:"\<And>b c d. b \<in> x \<Longrightarrow> c \<in> x \<Longrightarrow> f`b = f`c \<Longrightarrow> b = c"
  shows "f : x \<Zinj> y"
  by (rule tinjI[OF f], 
      use funappI[OF tfun_fun[OF f]] eq in auto)

lemma tinj_eqI: 
  assumes f:"f : x \<Zinj> y"
    and bc:"b \<in> x" "c \<in> x"
    and app:"app f b d" "app f c d"
  shows "b = c"
  by (rule inj_on_eqI[OF tinj_injon[OF f] bc app])

lemma tinj_app_eqI:
  assumes f:"f : x \<Zinj> y"
    and b:"b \<in> x" and c:"c \<in> x" 
    and eq:"f`b = f`c"
  shows "b = c"
proof (rule inj_on_eqI[OF tinj_injon[OF f] b c])
  have tfun:"f : x \<leadsto> y" by (rule tinj_tfun[OF f])
  obtain d where "d \<in> y" and 1:"app f b d" by (rule tfunE[OF tfun b]) 
  obtain e where "e \<in> y" and 2:"app f c e" by (rule tfunE[OF tfun c]) 
  from 1 2 eq have "f ` b = d" "d = e"using funappI[OF tfun_fun[OF tfun]] by auto
  thus "app f b (f ` b)" "app f c (f ` b)" using 1 2 by auto
qed


section \<open>Surjective functions\<close>

definition surj :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "surj f y \<equiv> \<forall>c. c \<in> y \<longrightarrow> (\<exists>x. app f x y) "



section \<open>Inverses of functions\<close>

definition inverse :: "'a \<Rightarrow> 'a" 
  where "inverse f \<equiv> mkfun (ran f) (\<lambda>b a. app f a b)"

lemma inverse_funpred :
  assumes f:"f : Function" and inj:"inj f"
  shows "(\<lambda>b a. app f a b) : FunPred (ran f)"
  unfolding FunPred_def
proof (rule tyI, auto)
  fix a1 a2 b 
  assume "b \<in> ran f" "app f a1 b" "app f a2 b"
  thus "a1 = a2" using inj_eqI[OF inj] by auto
next
  fix a b 
  assume "b \<in> ran f" "app f a b"
  thus "a : FunMem" "b : FunMem" 
    using funmemI1[OF f] ran_funmem[OF f] 
    by auto
qed
lemma inj_inverse_fun :
  assumes f:"f : Function" and inj:"inj f"
  shows "inverse f : Function" 
  unfolding inverse_def
  by (rule mkfun_fun[OF ran_set[OF f] inverse_funpred[OF f inj]])

lemma inj_inverse_iff :
  assumes f:"f : Function" and inj:"inj f"
  shows "app (inverse f) b a \<longleftrightarrow> app f a b"
  unfolding inverse_def mkfun_iff[OF ran_set[OF f] inverse_funpred[OF f inj]] ran_iff[OF f] 
  by auto

lemma pinj_inverse_iff : 
  assumes f:"f : x \<Zpinj> y" 
      and b:"b \<in> x"
    shows "app (inverse (f \<restriction> x)) c b \<longleftrightarrow> app f b c"
  unfolding inj_inverse_iff[OF restrict_fun[OF pinj_fun[OF f]] pinj_inj[OF f]]
            restrict_iff[OF pinj_fun[OF f]] using b by auto

lemmas tinj_inverse_iff = pinj_inverse_iff[OF tinj_pinj]

lemma inj_inverse_app_eq:
  assumes f:"f : Function" 
      and inj:"inj f" and b:"b \<in> dom f"
  shows "inverse f ` (f ` b) = b"
  by (rule funappI[OF inj_inverse_fun[OF f inj]],
      unfold inj_inverse_iff[OF f inj],
      rule funapp_dom[OF f b])

lemma pinj_inverse_app_eq: 
  assumes f:"f : x \<Zpinj> y"
      and b:"b \<in> x" and dom:"b \<in> dom f"
    shows "inverse (f \<restriction> x) ` (f ` b) = b"
  using inj_inverse_app_eq[OF restrict_fun[OF pinj_fun[OF f]] pinj_inj[OF f] 
                              restrict_domI[OF pinj_fun[OF f] dom b]] 
  unfolding restrict_app[OF pinj_fun[OF f] b dom] by auto

lemmas tinj_inverse_app_eq = pinj_inverse_app_eq[OF tinj_pinj]


section \<open>Function composition\<close>
(*Use \circle to avoid clash with HOL function composition*)
definition comp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl \<open>\<circle>\<close> 50)
  where "g \<circle> f \<equiv> mkfun (dom f) (\<lambda>a c. (\<exists>b. app f a b \<and> app g b c))"

lemma comp_funpred : 
  assumes f:"f : Function" and g:"g : Function"
  shows "(\<lambda>a c. (\<exists>b. app f a b \<and> app g b c)) : FunPred x"
  unfolding FunPred_def
proof (rule tyI, auto)
  fix a b1 b2 c1 c2 
  assume "app f a b1" "app f a b2" 
  hence "b1 = b2" using app_eqI[OF f] by auto
  moreover assume "app g b1 c1" "app g b2 c2"
  ultimately show "c1 = c2" using app_eqI[OF g] by auto
next
  fix a b c
  assume "app f a b" "app g b c"
  thus "a : FunMem" "c : FunMem" 
    by (auto intro: funmemI1[OF f] funmemI2[OF g])
qed

lemma comp_typ : "(\<circle>) : Function \<rightarrow> Function \<rightarrow> Function"
  unfolding comp_def 
  by (rule funI, rule funI, rule mkfun_fun[OF dom_set comp_funpred])

lemmas comp_fun = funE[OF funE[OF comp_typ]]
lemmas pfun_comp_fun = comp_fun[OF pfun_fun pfun_fun]
lemmas tfun_comp_fun = comp_fun[OF tfun_fun tfun_fun]

lemma comp_iff :
  assumes f:"f : Function" and g:"g : Function"
  shows "app (g \<circle> f) a c \<longleftrightarrow> (\<exists>b. app f a b \<and> app g b c)"
  unfolding comp_def mkfun_iff[OF dom_set[OF f] comp_funpred[OF f g]] dom_iff[OF f] 
  by auto

lemma compI :
  assumes f:"f : Function" and g:"g : Function"
    and app_f:"app f a b" and app_g:"app g b c"
  shows "app (g \<circle> f) a c"
  using comp_iff[OF f g] app_f app_g 
  by auto 

lemma compE :
  assumes f:"f : Function" and g:"g : Function"
      and app:"app (g \<circle> f) a c"
  obtains b where "app f a b" "app g b c"
  using comp_iff[OF f g] app by auto

lemma pfun_comp_iff :
  assumes f:"f : x \<Zpfun> y" and g:"g : y \<Zpfun> z"
  shows "g \<circle> f : x \<Zpfun> z"
proof (rule pfunI[OF pfun_comp_fun[OF g f]])
  fix a c assume "a \<in> x" "app (g \<circle> f) a c"
  then obtain b where "app f a b" "app g b c" 
    by (blast elim: compE[OF pfun_fun[OF f] pfun_fun[OF g]])
  moreover hence "b \<in> y" using pfunE[OF f \<open>a \<in> x\<close>] by simp
  ultimately show "c \<in> z" using pfunE[OF g] by auto
qed

lemma tfun_comp_iff :
  assumes f:"f : x \<leadsto> y" and g:"g : y \<leadsto> z"
    shows "g \<circle> f : x \<leadsto> z"
proof (rule tfunI[OF tfun_comp_fun[OF g f]])
  fix a c assume "a \<in> x"
  then obtain b where "b \<in> y" "app f a b" by (blast elim: tfunE[OF f])
  moreover then obtain c where "c \<in> z" "app g b c" by (blast elim: tfunE[OF g])
  ultimately show "\<exists>c. c \<in> z \<and> app (g \<circle> f) a c" 
    using compI[OF tfun_fun[OF f] tfun_fun[OF g]] by auto
qed


lemma comp_app_eq : 
  assumes f:"f : Function" and g:"g : Function"
      and b:"b \<in> dom f" and fb:"f ` b \<in> dom g" 
    shows "(g \<circle> f) ` b = g ` (f ` b)"
  by (rule funappI[OF comp_fun[OF g f]], rule compI[OF f g], 
      rule funapp_dom[OF f b], rule funapp_dom[OF g fb])



section \<open>Forming functions from ('a=>'a)-operators\<close>

lemma funpredI :
  assumes x:"x : SetOf FunMem" and F:"F : MemOf x \<rightarrow> FunMem"
  shows "(\<lambda>a b. b = F a) : FunPred x"
  using funE[OF F memofI] setof_mem[OF x] 
  unfolding FunPred_def has_ty_def 
  by auto

definition lam :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "lam x F \<equiv> mkfun x (\<lambda>a b. b = F a)"

lemma lam_fun :
  assumes x:"x : SetOf FunMem" and F:"F : MemOf x \<rightarrow> FunMem" 
    shows "lam x F : Function"
  unfolding lam_def 
  by (rule mkfun_fun[OF setof_set[OF x] funpredI[OF x F]])

lemma lam_iff :
  assumes x:"x : SetOf FunMem" and F:"F : MemOf x \<rightarrow> FunMem" 
  shows "app (lam x F) b c \<longleftrightarrow> b \<in> x \<and> c = F b"
  unfolding lam_def using "fun" setof_set[OF x] funpredI[OF x F] by auto

lemma lam_app :
  assumes x:"x : SetOf FunMem" and F:"F : MemOf x \<rightarrow> FunMem" 
      and b : "b \<in> x"
    shows "lam x F ` b = F b"
  by (rule funappI[OF lam_fun[OF x F]], 
      use lam_iff[OF x F] b in auto) 

lemma lam_tfun :
  assumes x:"x : SetOf FunMem" and y:"y : SetOf FunMem" 
      and F:"F : MemOf x \<rightarrow> MemOf y" 
    shows "lam x F : x \<leadsto> y"
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
qed

(*HOL injection to GST injection*)
(*I think this is the first time we 'flatten' properties of HOL stuff to GST stuff.*)
lemma lam_inj :
  assumes x:"x : SetOf FunMem" and F:"F : MemOf x \<rightarrow> FunMem"
      and Finj:"Fun.inj F"
    shows "inj (lam x F)"
proof (rule injI)
  fix b c d 
  assume "app (lam x F) b d" "app (lam x F) c d"
  hence "F b = F c" using lam_iff[OF x F] by auto
  thus "b = c" using Finj unfolding Fun.inj_def by auto
qed
 *)
