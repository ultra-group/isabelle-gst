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

ML \<open>val GZF = Feature
  {cla = \<^class>\<open>GZF\<close>, deps = [], 
   logo = \<^term>\<open>Set\<close>, cargo = \<^term>\<open>SetMem\<close>,
   default_param = \<^term>\<open>GZF_default\<close>}\<close>

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
    PairMem_def : "\<forall>b. PairMem b = (\<exists>p : Pair. \<exists>c. p = pair b c \<or> p = pair c b)"

ML \<open>val OPair = Feature
  {cla = \<^class>\<open>OPair\<close>, deps = [], 
   logo = \<^term>\<open>Pair\<close>, cargo = \<^term>\<open>PairMem\<close>,
   default_param = \<^term>\<open>OPair_default\<close>}\<close>


class app = fixes app :: "['a,'a,'a] \<Rightarrow> bool"
(*Explain what this is*)
abbreviation (in app) "app_mem P b \<equiv> \<exists> r : P. \<exists>c. app r b c \<or> app r c b"

class BinRel = GZF + app + 
  fixes 
    \<comment> \<open>Axiomatized constants\<close>
    BinRel :: \<open>'a \<Rightarrow> bool\<close> and 
    mkrel :: \<open>['a, 'a, ['a,'a] \<Rightarrow> bool] \<Rightarrow> 'a\<close> and
    field :: \<open>'a \<Rightarrow> 'a\<close> and
    relspace :: \<open>'a \<Rightarrow> 'a\<close> (\<open>\<RR>\<close>) and
    \<comment> \<open>Derived constants\<close>
    BinRelMem :: \<open>'a \<Rightarrow> bool\<close> and
    \<comment> \<open>Default value\<close>
    BinRelation_default :: \<open>'a\<close>
  assumes 
    \<comment> \<open>Soft typings\<close>
    mkrel_typ : "mkrel : Set \<rightarrow> Set \<rightarrow> Any \<rightarrow> BinRel" and 
    field_typ : "field : BinRel \<rightarrow> Set" and
    relspace_typ : "relspace : Set \<rightarrow> SetOf BinRel" and
    \<comment> \<open>Main axioms\<close>
    rel : "\<forall>x : Set. \<forall>y : Set. \<forall>P. 
        (\<forall>a b. app (mkrel x y P) a b \<longleftrightarrow> 
          (a \<in> x \<and> b \<in> y \<and> P a b \<and> a : BinRelMem \<and> b : BinRelMem))" and
    ext : "\<forall>r : BinRel. \<forall>s : BinRel. (\<forall>a b. app r a b \<longleftrightarrow> app s a b) \<longrightarrow> r = s" and
    field_iff : "\<forall>r : BinRel. \<forall>x. x \<in> field r \<longleftrightarrow> (\<exists>y. app r x y \<or> app r y x)" and
    relspace_ax : "\<forall>x : Set. \<forall>r : BinRel. r \<in> \<RR> x \<longleftrightarrow> (field r \<subseteq> x)" and
    \<comment> \<open>Simple definitions\<close>
    BinRelMem_def : "BinRelMem = app_mem BinRel"
    
ML \<open>val BinRel = Feature
  {cla = \<^class>\<open>BinRel\<close>, deps = [GZF], 
   logo = \<^term>\<open>BinRel\<close>, cargo = \<^term>\<open>BinRelMem\<close>,
   default_param = \<^term>\<open>BinRelation_default\<close>}\<close>

class Function = GZF + app + 
  fixes 
    \<comment> \<open>Axiomatized constants\<close>
    Function :: \<open>'a \<Rightarrow> bool\<close> and 
    mkfun :: \<open>['a, ['a,'a] \<Rightarrow> bool] \<Rightarrow> 'a\<close> and
    dom :: \<open>'a \<Rightarrow> 'a\<close> and
    ran :: \<open>'a \<Rightarrow> 'a\<close> and
    funspace :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>\<midarrow>p\<rightarrow>\<close> 60) and
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
    funspace_typ : "funspace : Set \<rightarrow> Set \<rightarrow> SetOf Function" and
    \<comment> \<open>Main axioms\<close>
    mkfun_ax : "\<forall>s : Set. \<forall>P : FunPred s. \<forall>x y. app (mkfun s P) x y 
                     \<longleftrightarrow> (x \<in> s \<and> P x y \<and> x : FunMem \<and> y : FunMem)" and
    fun_prop : "\<forall>f : Function. \<forall>x y z. app f x y \<and> app f x z \<longrightarrow> y = z" and
    fun_ext  : "\<forall>f : Function. \<forall>g : Function. (\<forall>x y. app f x y \<longleftrightarrow> app g x y) \<longrightarrow> f = g" and 
    fun_dom  : "\<forall>f : Function. \<forall>x. x \<in> dom f \<longleftrightarrow> (\<exists>y. app f x y)" and
    fun_ran  : "\<forall>f : Function. \<forall>y. y \<in> ran f \<longleftrightarrow> (\<exists>x. app f x y)" and
    funspace_ax : "\<forall>x : Set. \<forall>y : Set. \<forall>f : Function. 
                      f \<in> x \<midarrow>p\<rightarrow> y \<longleftrightarrow> (dom f \<subseteq> x \<and> ran f \<subseteq> y)" and
    \<comment> \<open>Simple definitions\<close>
    FunMem_def : "\<forall>b. FunMem b = (app_mem Function) b" and
    FunPred_def : "\<forall>x P. FunPred x P  = (\<forall>b : FunMem. b \<in> x \<longrightarrow> (\<exists>\<^sub>\<le>\<^sub>1 c : FunMem. P b c))"

ML \<open>val Function = Feature
  {cla = \<^class>\<open>Function\<close>, deps = [GZF], 
   logo = \<^term>\<open>Function\<close>, cargo = \<^term>\<open>FunMem\<close>,
   default_param = \<^term>\<open>Function_default\<close>}\<close>


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

ML \<open>val Ordinal = Feature
  {cla = \<^class>\<open>Ordinal\<close>, deps = [], 
   logo = \<^term>\<open>Ord\<close>, cargo = \<^term>\<open>\<top>\<close>,
   default_param = \<^term>\<open>Ordinal_default\<close>}\<close>

abbreviation (in Ordinal) leq (infixl \<open>\<le>\<close> 50) where "x \<le> y \<equiv> x < succ y"
    
class OrdRec = GZF + Ordinal + 
  fixes 
    predSet :: \<open>'a \<Rightarrow> 'a\<close> and 
    supOrd :: \<open>'a \<Rightarrow> 'a\<close> and
    OrdRec :: \<open>[['a,'a \<Rightarrow> 'a] \<Rightarrow> 'a, ['a,'a] \<Rightarrow> 'a, 'a, 'a] \<Rightarrow> 'a\<close> and
    OrdRec_default :: \<open>'a\<close>
  assumes 
    predset_typ : "predSet : Ord \<rightarrow> SetOf Ord" and
    predset_ax :  "\<forall>\<beta> : Ord. \<forall>\<alpha> : Ord. \<alpha> \<in> predSet \<beta> \<longleftrightarrow> \<alpha> < \<beta>" and
    supord_typ :  "supOrd : SetOf Ord \<rightarrow> Ord" and
    supord_ax :  "\<forall>x : SetOf Ord. \<forall>\<alpha>. \<alpha> \<in> x \<longrightarrow> \<alpha> \<le> supOrd x" and
    ordrec_0 :  "\<forall>G. \<forall>F. \<forall>A. OrdRec G F A 0 = A" and
    ordrec_succ_ax :  "\<forall>G. \<forall>F. \<forall>A. \<forall>b : Ord. 
       OrdRec G F A (succ b) = F (succ b) (OrdRec G F A b)" and
    ordrec_lim_ax :  "\<forall>G. \<forall>F. \<forall>A. \<forall>\<mu> : Limit. 
       OrdRec G F A \<mu> = G \<mu> (\<lambda>j. if j : Ord \<and> j < \<mu> then OrdRec G F A j else OrdRec_default)"                    

ML \<open>val OrdReec = Feature
  {cla = \<^class>\<open>OrdRec\<close>, deps = [], 
   logo = \<^term>\<open>\<bottom>\<close>, cargo = \<^term>\<open>\<top>\<close>,
   default_param = \<^term>\<open>OrdRec_default\<close>}\<close>


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

ML \<open>val Nat = Feature
  {cla = \<^class>\<open>Nat\<close>, deps = [], 
   logo = \<^term>\<open>Nat\<close>, cargo = \<^term>\<open>\<top>\<close>,
   default_param = \<^term>\<open>Nat_default\<close>}\<close>

class Exc =
  fixes Exc :: \<open>'a \<Rightarrow> bool\<close>
    and exc :: \<open>'a\<close> (\<open>\<Zspot>\<close>)
    and Exc_default :: \<open>'a\<close> (*redunant default value, added for consistency*)
  assumes "\<forall>b. Exc b \<longleftrightarrow> (b = \<Zspot>)"
ML \<open>val Exc = Feature
  {cla = \<^class>\<open>Exc\<close>, deps = [], 
   logo = \<^term>\<open>Exc\<close>, cargo = \<^term>\<open>\<top>\<close>,
   default_param = \<^term>\<open>Exc_default\<close>}\<close>

text \<open>An example GST: ZF+\<close>

ML \<open>val ZFPlus_spec = 
  [ {feat = GZF, default_val = \<^term>\<open>\<Zspot>\<close>, blacklist = [Exc]},
    {feat = Ordinal, default_val = \<^term>\<open>\<Zspot>\<close>, blacklist = []},
    {feat = OPair, default_val = \<^term>\<open>\<Zspot>\<close>, blacklist = [Exc]},
    {feat = Function, default_val = \<^term>\<open>\<Zspot>\<close>, blacklist = [Exc]},
    {feat = Exc, default_val = \<^term>\<open>\<Zspot>\<close>, blacklist = []}]\<close>

local_setup \<open>snd o mk_gst "ZFplus" ZFPlus_spec\<close>

context ZFplus begin

end
end