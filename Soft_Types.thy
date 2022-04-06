theory Soft_Types
  imports remove_syntax GST_Logic "HOL-Eisbach.Eisbach"
begin

(*CREDIT TO KAPPELMANN: https://github.com/kappelmann/Isabelle-Set*)

subsection \<open>Typing judgements\<close>
definition has_ty :: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"  (infix ":" 45)
  where "x : P \<equiv> P x"

lemma tyI : "P x \<Longrightarrow> x : P" unfolding has_ty_def by simp
lemma tyE : "x : P \<Longrightarrow> P x" unfolding has_ty_def by simp 


definition tall :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "tall P Q \<equiv> \<forall>x. x : P \<longrightarrow> Q x"

definition tex :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "tex P Q \<equiv> \<exists>x. x : P \<and> Q x"

definition tex1 :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "tex1 P Q \<equiv> \<exists>!x. x : P \<and> Q x"

definition tuniq :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "tuniq P Q \<equiv> \<exists>\<^sub>\<le>\<^sub>1x. x : P \<and> Q x"

definition typ_defdes :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a"
  where "typ_defdes P Q d \<equiv> (\<iota> x. x : P \<and> Q x else d) "

syntax
  "_tball"  :: "[pttrn, 'a \<Rightarrow> bool, bool] \<Rightarrow> bool"  ("(3\<forall>_ : _./ _)" 10)
  "_tbex"   :: "[pttrn, 'a \<Rightarrow> bool, bool] \<Rightarrow> bool"  ("(3\<exists>_ : _./ _)" 10)
  "_tex1"   :: "[pttrn, 'a \<Rightarrow> bool, bool] \<Rightarrow> bool"  ("(3\<exists>!_ : _./ _)" 10)
  "_tuniq"  :: "[pttrn, 'a \<Rightarrow> bool, bool] \<Rightarrow> bool"  ("(3\<exists>\<^sub>\<le>\<^sub>1_ : _./ _)" 10)
  "_tdefdes" :: "[pttrn, 'a \<Rightarrow> bool, 'a \<Rightarrow> bool, 'a] \<Rightarrow> 'a"  ("(4\<iota>_ : _./ _ else _)" 10)
translations
  "\<forall>x : A. P"  \<rightleftharpoons> "CONST tall A (\<lambda>x. P)"
  "\<exists>x : A. P"  \<rightleftharpoons> "CONST tex A (\<lambda>x. P)"
  "\<exists>!x : A. P" \<rightleftharpoons> "CONST tex1 A (\<lambda>x. P)"
  "\<exists>\<^sub>\<le>\<^sub>1x: A. P" \<rightleftharpoons> "CONST tuniq A (\<lambda>x. P)"
  "\<iota> x : A. P else default" \<rightleftharpoons> "CONST typ_defdes A (\<lambda>x. P) default"


lemma tallI [intro!] : 
  "(\<And>x. x : P \<Longrightarrow> Q x) \<Longrightarrow> \<forall>x : P. Q x"
  unfolding tall_def by auto

lemma tallE [elim!]: 
  assumes "\<forall>x : P. Q x"
  obtains "\<And>x. (x : P \<Longrightarrow> Q x)"
  using assms unfolding tall_def by auto

lemma tallD [elim]: 
  "\<lbrakk> \<forall>x : P. Q x ; x : P \<rbrakk> \<Longrightarrow> Q x"
  by auto

lemma texI [intro] : 
  "\<lbrakk> x : P ; Q x \<rbrakk> \<Longrightarrow> \<exists>x:P. Q x"
  unfolding tex_def by auto

lemma texE [elim!] : 
  assumes "\<exists>x:P. Q x" 
  obtains x where "x : P" and "Q x"
  using assms unfolding tex_def by auto

lemma typ_defdes_eq :
  assumes "b : A" "P b" 
      and eq:"\<And>c. c : A \<Longrightarrow> P c \<Longrightarrow> c = b"
    shows "(\<iota> b : A. P b else d) = b"
  unfolding typ_defdes_def 
  by (rule the_def_eq, rule conjI[OF \<open>b : A\<close> \<open>P b\<close>], 
      use assms(3) in auto)

lemma typ_defdes_eq' : 
  assumes ex1:"\<exists>! b : A. P b" 
     and c:"c : A" "P c"
  shows "(\<iota> b : A. P b else d) = c"
  using ex1 c unfolding tex1_def
  by (blast intro: typ_defdes_eq)

lemma typ_defdesI :
  assumes b:"b : A" "P b" 
      and eq:"\<And>c. c : A \<Longrightarrow> P c \<Longrightarrow> c = b"
  shows "P (\<iota> x : A. P x else d)"
proof -
  from typ_defdes_eq[of b A P, OF b] eq 
  have "(\<iota> x : A. P x else d) = b" by auto  
  thus "P (\<iota> x : A. P x else d)" using \<open>P b\<close> by simp 
qed

lemma typ_defdesI' : 
  assumes ex1:"\<exists>! b : A. P b" 
  shows "P (\<iota> b : A. P b else d)"
  using ex1 unfolding tex1_def
  by (blast intro: typ_defdesI)


subsection \<open>Methods for soft-type automation\<close>

named_theorems typdef
named_theorems typ_intro

  
method unfold_typs =
  (rule typ_intro | 
   simp_all only: typdef has_ty_def tall_def tex_def)+
(*Repeatedly applies rules marked with [typ_intro] attribute and
  applies simp method to all goals using facts marked with [typdef], 
  the definition \<open>x : P \<equiv> P x\<close> and definitions of restricted/dervied quantifiers*)


definition Any :: "('a \<Rightarrow> bool)" where [typdef] : "Any \<equiv> (\<lambda>x. True)"

lemma anyI [simp] : "x : Any" unfolding has_ty_def Any_def by auto

definition Bool :: "bool \<Rightarrow> bool" ("\<bool>") where [typdef] : "\<bool> \<equiv> (\<lambda>p. True)"

subsection \<open>Function types\<close>
definition fun_ty :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> bool)" (infixr "\<rightarrow>" 50)
  where [typdef] : "P \<rightarrow> Q \<equiv> \<lambda>f. \<forall>x. P x \<longrightarrow> Q (f x)"
lemma funty_eq : "f : P \<rightarrow> Q \<equiv> \<forall>x. x : P \<longrightarrow> f x : Q"
  unfolding fun_ty_def has_ty_def by auto

lemma funE : "f : P \<rightarrow> Q \<Longrightarrow> x : P \<Longrightarrow> f x : Q"
  unfolding fun_ty_def has_ty_def by auto

lemma funI [typ_intro]: "(\<And>x. x : P \<Longrightarrow> f x : Q) \<Longrightarrow> f : P \<rightarrow> Q"
  unfolding fun_ty_def has_ty_def by auto

subsection \<open>Dependent Function types\<close>

definition depfun_ty :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('b \<Rightarrow> bool)) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> bool)" 
  where [typdef]: "depfun_ty P Q \<equiv> (\<lambda>f. \<forall>x : P. f x : Q x)" 
syntax
  "_depfunty" :: "[pttrn, 'a \<Rightarrow> bool, bool] => bool" (\<open>(3\<Pi> _:_./ _)\<close> 10)
translations
  "\<Pi> x:P. B" \<rightleftharpoons> "CONST depfun_ty P (\<lambda>x. B)"

lemma depfunty_eq : 
  "f : depfun_ty P Q \<equiv> \<forall>x. x : P \<longrightarrow> f x : Q x" 
  unfolding depfun_ty_def tall_def has_ty_def by auto

lemma depfunI [typ_intro] : 
  "(\<And>x. x : A \<Longrightarrow> f x : B x) \<Longrightarrow> f : (\<Pi> x : A. B x)"
  unfolding depfun_ty_def tall_def has_ty_def by auto 

lemma depfunE : 
  assumes "f : (\<Pi> x : A. B x)" "x : A"
  shows "f x : B x"
  using assms unfolding depfun_ty_def tall_def has_ty_def by auto

subsection \<open>Relation types\<close>
definition BinPred where [typdef] : "BinPred \<alpha> \<beta> P \<equiv> (\<forall>x y. x : \<alpha> \<and> P x y \<longrightarrow> y : \<beta>)" 

lemma bpredE : "P : BinPred \<alpha> \<beta> \<Longrightarrow> x : \<alpha> \<Longrightarrow> P x y \<Longrightarrow> y : \<beta>" 
  unfolding BinPred_def by (drule tyE, auto)
lemma bpredI [typ_intro]: "(\<And>x y. x : \<alpha> \<Longrightarrow> P x y \<Longrightarrow> y : \<beta>) \<Longrightarrow> P : BinPred \<alpha> \<beta>" 
  unfolding BinPred_def by (unfold_typs, auto)

subsection \<open>Intersection types\<close>
definition inter_ty :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infix "\<bar>" 45)
  where [typdef] : "P \<bar> Q \<equiv> \<lambda>x. P x \<and> Q x"

lemma intE : 
  assumes "x : (P \<bar> Q)" 
    shows "x : P \<and> x : Q" 
  using assms unfolding inter_ty_def by unfold_typs

lemma intE1 : "x : (P \<bar> Q) \<Longrightarrow> x : P" 
  unfolding inter_ty_def by unfold_typs

lemma intE2 : "x : (P \<bar> Q) \<Longrightarrow> x : Q" 
  unfolding inter_ty_def by unfold_typs

lemma intI [typ_intro] : 
  "\<lbrakk> x : P ; x : Q \<rbrakk> \<Longrightarrow> x : (P \<bar> Q)" 
  unfolding inter_ty_def by unfold_typs

subsection \<open>Subtyping\<close>
definition subtyp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" (infix "<<" 45) 
  where "P << Q \<equiv> \<forall>x. x : P \<longrightarrow> x : Q"

lemma subtypI  : "(\<And>x. x : P \<Longrightarrow> x : Q) \<Longrightarrow> P << Q" unfolding subtyp_def by (auto)
lemma subtypE : "P << Q \<Longrightarrow> x : P \<Longrightarrow> x : Q" unfolding subtyp_def by auto

lemma subtyp_trans : 
  assumes "P << Q" "Q << R"
  shows "P << R"
  by (rule subtypI, rule subtypE[OF \<open>Q << R\<close>], rule subtypE[OF \<open>P << Q\<close>], assumption)

lemma int_sub1 : "(P \<bar> Q) << P" by (rule subtypI, erule intE1)
lemma int_sub2 : "(P \<bar> Q) << Q" by (rule subtypI, erule intE2)

lemma subtyp_fun_dom : "R << P \<Longrightarrow> f : P \<rightarrow> Q \<Longrightarrow> f : R \<rightarrow> Q"
proof (rule funI)
  assume "f : P \<rightarrow> Q" "R << P"
  fix x assume "x : R" hence "x : P" by (rule subtypE[OF \<open>R << P\<close>])
  thus "f x : Q" by (rule funE[OF \<open>f : P \<rightarrow> Q\<close>])
qed

lemma subtyp_fun_ran : "Q << R \<Longrightarrow> f : P \<rightarrow> Q \<Longrightarrow> f : P \<rightarrow> R"
proof (rule funI)
  assume "f : P \<rightarrow> Q" "Q << R"
  fix x assume "x : P" hence "f x : Q" by (rule funE[OF \<open>f : P \<rightarrow> Q\<close>])
  thus "f x : R" by (rule subtypE[OF \<open>Q << R\<close>])
qed


definition forall_ty (binder "\<questiondown>" 10)
  where "\<questiondown>\<alpha>. P \<alpha> \<equiv> \<lambda>x. \<forall>\<alpha>. P \<alpha> x"
ML \<open>domain_type (Term.fastype_of @{term \<open>F :: 'a \<Rightarrow> 'b\<close>})\<close>

ML \<open>
fun mk_styping_trm trm typ styp = 
    ((Const ("Soft_Types.has_ty", typ --> fastype_of styp --> @{typ bool})) $ trm $ styp) 

fun unfold_fun_typing trm =  
  let
    fun funE (f,ty1,ty2) =
      let 
        val x_typ = domain_type (fastype_of f)
        val fx_typ = range_type (fastype_of f)
        val x = Free ("x", x_typ)
        val typ_trm1 = mk_styping_trm x (x_typ) ty1
        val typ_trm2 = (mk_styping_trm (f $ x) (fx_typ) ty2)
      in 
        HOLogic.mk_all ("x", x_typ, 
          HOLogic.mk_imp (unfold_fun_typing typ_trm1, unfold_fun_typing typ_trm2))
      end
    fun depfunE (f, ty1, ty2) = 
      let 
        val x_typ  = domain_type (fastype_of f)
        val fx_typ = range_type (fastype_of f)
        val x = Free ("x", x_typ)
        val typ_trm1 = mk_styping_trm x x_typ ty1
        val typ_trm2 = mk_styping_trm (f $ x) fx_typ (betapply (ty2, x))
      in 
        HOLogic.mk_all ("x", x_typ, 
          HOLogic.mk_imp (unfold_fun_typing typ_trm1, unfold_fun_typing typ_trm2))  
      end
   in
     case trm of
      ((Const ("Soft_Types.has_ty", _)) $ t $ styp) =>
        (case (t,styp) of
          (f, ((Const ("Soft_Types.fun_ty",_)) $ p $ q)) => funE (f, p, q)
        | (f, ((Const ("Soft_Types.depfun_ty",_)) $ p $ q)) => depfunE (f, p, q)
        | _ => trm)
     | _ => trm 
   end
\<close>

declare [[ML_print_depth=30]]
ML \<open>betapply (@{term \<open>(\<lambda>x. P x)\<close>}, @{term \<open>F\<close>})\<close>
ML \<open>@{term \<open>F : (\<Pi> x : P.  Q x \<rightarrow> R)\<close>}\<close>

ML \<open>val t = unfold_fun_typing @{term \<open>F : (\<Pi> x : P.  Q x \<rightarrow> R)\<close>}\<close>
ML \<open>val t' = unfold_fun_typing @{term \<open>F x : Q x \<rightarrow> R\<close>}\<close>
ML \<open>Thm.cterm_of @{context} t\<close>
ML \<open>
fun is_typing ((Const ("Soft_Types.has_ty",_)) $ _ $ _) = true
  | is_typing _ = false

fun is_fun_ty ((Const ("Soft_Types.fun_ty",_)) $ _ $ _) = true
  | is_fun_ty _ = false

fun is_depfun_ty ((Const ("Soft_Types.depfun_ty",_)) $ _ $ _) = true
  | is_depfun_ty _ = false

fun split_typings ((Const ("Soft_Types.has_ty",_)) $ c $ typ) = (c,typ)
  | split_typings _ = error "not a soft typing"

fun split_fun_ty ((Const ("Soft_Types.fun_ty",_)) $ t $ s) = (t,s)
  | split_fun_ty _ = error "not a function soft type"

fun is_fun_typing trm = is_typing trm andalso 
    (is_fun_ty (snd (split_typings trm)) orelse is_depfun_ty (snd (split_typings trm))) 

fun get_styps ((Const ("Soft_Types.fun_ty",_)) $ t $ s) = t :: get_styps s
  | get_styps t = [t] 

(*Let B be a term, and \<tau> be the type of B, and P be a soft-type on \<tau>:
  Then \<open>mk_styping_trm B \<tau> P\<close> and returns the term \<open>B : P\<close>*)


fun tall_const T = 
  Const ("Soft_Types.tall", (T --> @{typ bool}) --> 
                 (T --> @{typ bool}) --> @{typ bool});

fun mk_tall (x, T, P, Q) = tall_const T $ P $ absfree (x, T) Q;

 infixr ~> 
(* ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> bool) *)
 fun fun_sty_typ dom ran = (dom --> @{typ bool}) --> (ran --> @{typ bool}) --> ((dom --> ran) --> @{typ bool}) 
fun t ~> s = 
  let val dom = domain_type o fastype_of
  in Const ("Soft_Types.fun_ty", fun_sty_typ (dom t) (dom s)) $ t $ s end
\<close>

end