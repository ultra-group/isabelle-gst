theory GST_Features
  imports remove_syntax Soft_Types GST_Logic
begin

ML_file \<open>Tools/gst_features.ML\<close>

class GZF =
  fixes 
    \<comment> \<open>Axiomatzed constants\<close> 
    Set :: \<open>'a \<Rightarrow> bool\<close> and
    Mem :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<in>\<close> 50) and
    Union :: \<open>'a \<Rightarrow> 'a\<close> (\<open>\<Union> _\<close> [90] 90) and
    Pow :: \<open>'a \<Rightarrow> 'a\<close> (\<open>\<P> _\<close> [90] 90) and
    Emp :: \<open>'a\<close> (\<open>\<emptyset>\<close>) and
    Succ :: \<open>'a \<Rightarrow> 'a\<close> and
    Inf :: \<open>'a\<close> and
    Repl :: \<open>['a, ['a,'a] \<Rightarrow> bool] \<Rightarrow> 'a\<close> (\<open>\<R>\<close>) and
    \<comment> \<open>Derived constants\<close>
    Subset :: \<open>['a,'a] \<Rightarrow> bool\<close> (infix \<open>\<subseteq>\<close> 50) and
    SetMem :: \<open>'a \<Rightarrow> bool\<close> and
    SetOf :: \<open>['a \<Rightarrow> bool] \<Rightarrow> 'a \<Rightarrow> bool\<close> and
    ReplPred :: \<open>['a, ['a, 'a] \<Rightarrow> bool] \<Rightarrow> bool\<close> and
    \<comment> \<open>Default value\<close>
    GZF_default :: \<open>'a\<close> 
  assumes
    \<comment> \<open>Soft typings\<close>
    Union_typ : "Union : SetOf Set \<rightarrow> Set" and
    Pow_typ   : "Pow : Set \<rightarrow> SetOf Set" and
    Emp_typ   : "Emp : Set" and
    Succ_typ  : "Succ : Set \<rightarrow> Set" and 
    Inf_typ   : "Inf : Set" and
    Repl_typ  : "Repl : (\<Pi> x : Set. ReplPred x \<rightarrow> Set)" and
    \<comment> \<open>Main axioms\<close>
    ext : "\<forall>x : Set. \<forall>y : Set. ((\<forall>b. b \<in> x \<longleftrightarrow> b \<in> y) \<longrightarrow> x = y)" and
    uni : "\<forall>x : SetOf Set. (\<forall>a. a \<in> \<Union> x \<longleftrightarrow> (\<exists>z. z \<in> x \<and> a \<in> z))" and
    pow : "\<forall>x : Set. \<forall>z : Set. z \<in> \<P> x \<longleftrightarrow> z \<subseteq> x" and
    emp : "\<forall>b. \<not> (b \<in> \<emptyset>)" and
    succ : "\<forall>x : Set. \<forall>b. b \<in> Succ x \<longleftrightarrow> (b \<in> x \<or> b = x)" and
    inf : "\<emptyset> \<in> Inf \<and> (\<forall>a. a \<in> Inf \<longrightarrow> Succ a \<in> Inf)" and
    repl : "\<forall>x : Set. \<forall>P : ReplPred x. (\<forall>b. b \<in> Repl x P \<longleftrightarrow> (\<exists>a. a \<in> x \<and> P a b \<and> b : SetMem))" and
    \<comment> \<open>Simple definitions\<close>
    Subset_ax   : "\<forall>x y. x \<subseteq> y = (\<forall>a. a \<in> x \<longrightarrow> a \<in> y)" and
    SetMem_ax   : "\<forall>b. SetMem b = (\<exists>y : Set. b \<in> y)" and
    SetOf_ax    : "\<forall>\<alpha> x. SetOf \<alpha> x = (x : Set \<and> (\<forall>b. b \<in> x \<longrightarrow> b : \<alpha>))" and
    ReplPred_ax : "\<forall>x P. ReplPred x P = (\<forall>a. a \<in> x \<longrightarrow> (\<exists>\<^sub>\<le>\<^sub>1 b: SetMem. P a b))"
   
class OPair = 
  fixes
    \<comment> \<open>Axiomatized constants\<close>
    Pair :: \<open>'a \<Rightarrow> bool\<close> and
    pair :: \<open>['a,'a] \<Rightarrow> 'a\<close> and
    \<comment> \<open>Derived constants\<close>
    PairMem :: \<open>'a \<Rightarrow> bool\<close> and
    \<comment> \<open>Default value\<close>
    OPair_default :: \<open>'a\<close>
  assumes
    \<comment> \<open>Soft typings\<close>
    pair_typ : "pair : PairMem \<rightarrow> PairMem \<rightarrow> (Pair \<triangle> PairMem)" and
    \<comment> \<open>Main axioms\<close>
    cpop : "\<forall>a : PairMem. \<forall>b : PairMem. \<forall>c : PairMem. \<forall>d : PairMem.
              pair a b = pair c d \<longleftrightarrow> (a = c \<and> b = d)" and
    pair_projs : "\<forall>p : Pair. \<exists>a b. p = pair a b" and
    \<comment> \<open>Simple definitions\<close>
    PairMem_def : "PairMem = (\<lambda>b. \<exists>p : Pair. \<exists>c. p = pair b c \<or> p = pair c b)"


class app = fixes app :: "['a,'a,'a] \<Rightarrow> bool"
(*Explain what this is*)
abbreviation (in app) "app_mem P b \<equiv> \<exists> r : P. \<exists>c. app r b c \<or> app r c b"

class BinRelation = GZF + app + 
  fixes 
    \<comment> \<open>Axiomatized constants\<close>
    BinRel :: \<open>'a \<Rightarrow> bool\<close> and 
    mkrel :: \<open>['a, 'a, ['a,'a] \<Rightarrow> bool] \<Rightarrow> 'a\<close> and
    field :: \<open>'a \<Rightarrow> 'a\<close> and
    \<comment> \<open>Derived constants\<close>
    BinRelMem :: \<open>'a \<Rightarrow> bool\<close> and
    BinRelPred :: \<open>['a, 'a, ['a,'a] \<Rightarrow> bool] \<Rightarrow> bool\<close> and
    \<comment> \<open>Default value\<close>
    BinRelation_default :: \<open>'a\<close>
  assumes 
    \<comment> \<open>Soft typings\<close>
    mkrel_typ : "mkrel : (\<Pi> x : Set. \<Pi> y : Set. BinRelPred x y \<rightarrow> BinRel)" and 
    field_typ : "field : BinRel \<rightarrow> Set" and
    \<comment> \<open>Main axioms\<close>
    rel : "\<forall>x : Set. \<forall>y : Set. \<forall>P : BinRelPred x y. 
              (\<forall>a b. app (mkrel x y P) a b \<longleftrightarrow> (a \<in> x \<and> b \<in> y \<and> P a b))" and
    ext : "\<forall>r : BinRel. \<forall>s : BinRel. (\<forall>a b. app r a b \<longleftrightarrow> app s a b) \<longrightarrow> r = s" and
    field_iff : "\<forall>r : BinRel. \<forall>x. x \<in> field r \<longleftrightarrow> (\<exists>y. app r x y \<or> app r y x)" and
    \<comment> \<open>Simple definitions\<close>
    BinRelMem_def : "BinRelMem = app_mem BinRel" and
    BinRelPred_def : "BinRelPred = 
      (\<lambda>x y P.  \<forall>a b. a \<in> x \<longrightarrow> b \<in> y \<longrightarrow> P a b \<longrightarrow> a : BinRelMem \<and> b : BinRelMem)"

class Function = GZF + app + 
  fixes 
    \<comment> \<open>Axiomatized constants\<close>
    Function :: \<open>'a \<Rightarrow> bool\<close> and 
    mkfun :: \<open>['a, ['a,'a] \<Rightarrow> bool] \<Rightarrow> 'a\<close> and
    dom :: \<open>'a \<Rightarrow> 'a\<close> and
    ran :: \<open>'a \<Rightarrow> 'a\<close> and
    \<comment> \<open>Derived constants\<close>
    FunMem :: \<open>'a \<Rightarrow> bool\<close> and
    FunPred :: \<open>['a, ['a,'a] \<Rightarrow> bool] \<Rightarrow> bool\<close> and
    \<comment> \<open>Default value\<close>
    Function_default :: \<open>'a\<close>
  assumes 
    \<comment> \<open>Soft typings\<close>
    mkfun_typ : "mkfun : (\<Pi> x : Set. FunPred x \<rightarrow> Function)" and 
    dom_typ : "dom : Function \<rightarrow> Set" and
    ran_typ : "ran : Function \<rightarrow> Set" and
    \<comment> \<open>Main axioms\<close>
    mkfun_ax : "\<forall>s : Set. \<forall>P : FunPred s. \<forall>x y. app (mkfun s P) x y 
                     \<longleftrightarrow> (x \<in> s \<and> P x y \<and> x : FunMem \<and> y : FunMem)" and
    fun_prop : "\<forall>f : Function. \<forall>x y z. app f x y \<and> app f x z \<longrightarrow> y = z" and
    fun_ext  : "\<forall>f : Function. \<forall>g : Function. (\<forall>x y. app f x y \<longleftrightarrow> app g x y) \<longrightarrow> f = g" and 
    fun_dom  : "\<forall>f : Function. \<forall>x. x \<in> dom f \<longleftrightarrow> (\<exists>y. app f x y)" and
    fun_ran  : "\<forall>f : Function. \<forall>y. y \<in> ran f \<longleftrightarrow> (\<exists>x. app f x y)" and
    \<comment> \<open>Simple definitions\<close>
    FunMem_def : "FunMem = app_mem Function" and
    FunPred_def : "FunPred = (\<lambda>s P. \<forall>x : FunMem. x \<in> s \<longrightarrow> (\<exists>\<^sub>\<le>\<^sub>1 y : FunMem. P x y))"

section \<open>Ordinal feature\<close>

class Ordinal =
  fixes 
    \<comment> \<open>Axiomatized constants\<close>
    Ord :: \<open>'a \<Rightarrow> bool\<close> and 
    lt  :: \<open>['a, 'a] \<Rightarrow> bool\<close> (infix \<open><\<close> 50) and
    zero  :: \<open>'a\<close> (\<open>0\<close>) and
    succ  :: \<open>'a \<Rightarrow> 'a\<close> and
    omega :: \<open>'a\<close> (\<open>\<omega>\<close>) and
    \<comment> \<open>Derived constants\<close>
    Limit :: \<open>'a \<Rightarrow> bool\<close> and
    \<comment> \<open>Default value\<close>
    Ordinal_default :: \<open>'a\<close>
  assumes 
    \<comment> \<open>Soft typings\<close>
    zero_typ  : "0 : Ord" and 
    succ_typ  : "succ : Ord \<rightarrow> Ord" and
    omega_typ : "\<omega> : Limit" and
    \<comment> \<open>Main axioms\<close>
    zero_ax  : "\<forall>b : Ord. \<not> (b < 0)" and
    succ_ax  : "\<forall>a : Ord. \<forall>b : Ord. a < (succ b) \<longleftrightarrow> a < b \<or> a = b" and
    omega_ax : "\<forall>\<mu> : Limit. \<mu> = \<omega> \<or> \<omega> < \<mu>" and
    lt_trans  : "\<forall>i : Ord. \<forall>j : Ord. \<forall>k : Ord. i < j \<longrightarrow> j < k \<longrightarrow> i < k" and
    lt_notsym : "\<forall>i : Ord. \<forall>j : Ord. i < j \<longrightarrow> \<not> (j < i)" and
    lt_linear : "\<forall>i : Ord. \<forall>j : Ord. i < j \<or> i = j \<or> j < i" and
    lt_induct : "\<forall>P. (\<forall>i : Ord. (\<forall>j : Ord. j < i \<longrightarrow> P j) \<longrightarrow> P i) \<longrightarrow> (\<forall>a : Ord. P a)" and
    \<comment> \<open>Simple definitions\<close>
    Limit_ax : "\<forall>u. Limit u \<longleftrightarrow> (Ord \<triangle> (\<lambda>\<mu>. 0 < \<mu> \<and> (\<forall>j : Ord. j < \<mu> \<longrightarrow> succ j < \<mu>))) u" 
    
class Nat =
  fixes 
    \<comment> \<open>Axiomatized constants\<close>
    Nat :: \<open>'a \<Rightarrow> bool\<close> and
    Zero :: \<open>'a\<close> (\<open>\<zero>\<close>) and
    S :: \<open>'a \<Rightarrow> 'a\<close> (\<open>\<S>\<close>) and
    \<comment> \<open>Default value\<close>
    Nat_default :: \<open>'a\<close>
  assumes 
    \<comment> \<open>Soft typings\<close>
    zero_typ : "\<zero> : Nat" and
    S_typ : "\<S> : Nat \<rightarrow> Nat" and
    \<comment> \<open>Main axioms\<close>
    S_inj : "\<forall>n : Nat. \<forall>m : Nat. n = m \<longrightarrow> \<S> n = \<S> m" and
    S_nonzero : "\<forall>n : Nat. \<S> n \<noteq> \<zero>" and
    nat_induct : "\<forall>P. P \<zero> \<longrightarrow> (\<forall>k : Nat. P k \<longrightarrow> P (\<S> k)) \<longrightarrow> (\<forall>n : Nat. P n)"

ML \<open>Term.strip_abs @{term \<open>P :: 'a \<Rightarrow> bool\<close>}\<close>
ML \<open>fun mk_disj_list ts = List.foldr HOLogic.mk_disj (List.last ts) ((rev o tl o rev) ts)\<close>
ML \<open>Thm.cterm_of @{context} (mk_disj_list [\<^term>\<open>P :: bool\<close>, \<^term>\<open>Q :: bool\<close>, \<^term>\<open>R :: bool\<close>])\<close>
ML \<open>type feature_instance =
  { feature : class,
    pred : term,
    default : term }\<close>
ML \<open>HOLogic.class_equal\<close>
ML \<open>
fun get_feature_funtypings thy cla = 
  filter (is_fun_typing o HOLogic.dest_Trueprop o snd) (get_locale_axioms thy cla)
fun get_default_param cla = Free (last_field cla ^ "_default", @{typ 'a})\<close>

ML \<open>get_default_param \<^class>\<open>GZF\<close>\<close>
ML \<open>get_feature_funtypings \<^theory> \<^class>\<open>GZF\<close>\<close>


ML \<open>
fun list_imp ([], B) = B
  | list_imp (A::As, B) = HOLogic.mk_imp (A, list_imp (As,B))

fun list_disj ([A]) = A
  | list_disj (A::As) = HOLogic.mk_disj (A, list_disj As)
  | list_disj [] = error "list_disj: empty list!"

fun app_until_bool trm = 
  let
    val typs = (fst o strip_type o fastype_of) trm
    val idxs = map (fn i => ("x",i)) (0 upto (length typs - 1))
    val vars = map Var (idxs ~~ typs)
  in 
    list_comb (trm,vars) 
  end

fun all_until_bool (Abs (x,T,P)) = 
    (HOLogic.all_const T $ Abs (x, T, all_until_bool P)) 
  | all_until_bool t = t  
\<close>

ML \<open>fun mk_styping trm styp = mk_styping_trm trm (fastype_of trm) styp\<close>
ML \<open>fun phi default i sftyp f = 
  case sftyp of
    ((Const ("Soft_Types.fun_ty",_)) $ P $ Q) => 
      let 
        val x = Var (("x",i), domain_type (fastype_of P))
        val not_xP = HOLogic.mk_not (mk_styping x P)
      in not_xP :: phi default (i+1) Q (f $ x) end   
  | ((Const ("Soft_Types.depfun_ty",_)) $ P $ Q) => 
      let 
        val x = Var (("x",i), domain_type (fastype_of P))
        val not_xP = HOLogic.mk_not (mk_styping x P)
      in not_xP :: phi default (i+1) (betapply (Q, x)) (f $ x) end   
  | _ => [HOLogic.mk_eq (f, default)]
\<close> 
ML \<open>fun gen_default_form default sftyping =
  let 
    val (t, sftyp) = split_typings sftyping
    val phis = phi default 0 sftyp t
    val disj = (mk_disj_list o rev o tl o rev) phis
    val imp = HOLogic.mk_imp (disj, List.last phis)
    val abs = Term.close_schematic_term imp
  in all_until_bool abs end\<close>

ML \<open>get_feature_funtypings \<^theory> \<^class>\<open>GZF\<close>\<close>
ML \<open>fun gen_default_axs thy default cla =
  let
    val typings = get_feature_funtypings thy cla
    val default_prop = (HOLogic.mk_Trueprop o gen_default_form default o HOLogic.dest_Trueprop)
  in map (fn (iden, trm) => (Binding.name_of iden ^ "_default", default_prop trm)) typings end\<close>
    
ML \<open>val GZF_defaults = gen_default_axs \<^theory> (get_default_param \<^class>\<open>GZF\<close>) \<^class>\<open>GZF\<close>\<close>
ML \<open>val OPair_defaults = gen_default_axs \<^theory> (get_default_param \<^class>\<open>OPair\<close>) \<^class>\<open>OPair\<close>\<close>

local_setup \<open>snd o mk_class "ZFP" [@{class GZF}, @{class OPair}] []  (GZF_defaults @ OPair_defaults)\<close>
context ZFP begin
ML \<open>map (Thm.cterm_of \<^context>) it\<close>



end