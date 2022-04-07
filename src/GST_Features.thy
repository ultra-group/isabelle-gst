theory GST_Features
  imports remove_syntax Soft_Types GST_Logic
begin

ML_file \<open>Tools/gst_features.ML\<close>

section \<open>Generalised ZF feature\<close>

ML \<open>val GZF_sig = [("Set", @{typ "'a \<Rightarrow> bool"}, nsyn),
                   ("Mem", @{typ "'a \<Rightarrow> 'a \<Rightarrow> bool"}, mk_infixl ("\<in>", 50)),
                   ("Union", @{typ "'a \<Rightarrow> 'a"}, mk_mixfix ("\<Union> _", [90], 90)),
                   ("Pow", @{typ "'a \<Rightarrow> 'a"}, mk_mixfix ("\<P> _", [90], 90)),
                   ("Emp", @{typ \<open>'a\<close>}, mk_sym "\<emptyset>"),
                   ("Succ", @{typ \<open>'a \<Rightarrow> 'a\<close>}, NoSyn),
                   ("Inf", @{typ "'a"}, nsyn),
                   ("Repl", @{typ "'a \<Rightarrow> (['a,'a] \<Rightarrow> bool) \<Rightarrow> 'a"}, mk_sym "\<R>")]\<close>
ML \<open>val GZF_defs = 
  [("Subset", @{term "\<lambda>x :: 'a. \<lambda>y :: 'a. \<forall>a :: 'a. Mem a x \<longrightarrow> Mem a y"}, mk_infixl ("\<subseteq>",50)),
   ("SetMem", @{term "\<lambda>x::'a. \<exists> y :: 'a : Set. Mem x y"}, nsyn),
   ("SetOf",  @{term "\<lambda>\<alpha> :: 'a \<Rightarrow> bool. \<lambda>x :: 'a. x : Set \<and> (\<forall>b :: 'a. Mem b x \<longrightarrow> b : \<alpha>)"}, nsyn),
   ("ReplPred", @{term "\<lambda>x :: 'a. \<lambda>P :: ['a,'a] \<Rightarrow> bool. x : Set \<and> (\<forall>a :: 'a. Mem a x 
                          \<longrightarrow> (\<exists>\<^sub>\<le>\<^sub>1 b : SetMem. P a b))"}, nsyn)]\<close>

(*Currently we have to make the class in two stages, because the axioms can only be
  parsed correctly by Isabelle's antiquotations in the context of a feature's signature class.
  Once we write an Isar command, we should be able to just generate both in one-fell-swoop.
   *)

(*Consider reformulating Repl to use a dependent type that enforces
  P to have at most one b : SetMem such that P a b for any a \<in> x? *)
local_setup \<open>snd o mk_sig_class "GZF" [] GZF_sig GZF_defs\<close>
(* local_setup \<open>snd o mk_sig_class "GZF" [] GZF_sig GZF_defs\<close> *)
context GZF_sig begin
ML \<open>val GZF_styps = 
    [("Union_typ", @{prop "Union : SetOf Set \<rightarrow> Set"}), 
     ("Pow_typ",   @{prop "Pow : Set \<rightarrow> SetOf Set"}),  
     ("Emp_typ",   @{prop "Emp : Set"}), 
     ("Succ_typ",   @{prop "Succ : Set \<rightarrow> Set"}), 
     ("Inf_typ",   @{prop "Inf : Set"}), 
     ("Repl_typ",  @{prop "Repl : (\<Pi> x : Set. ReplPred x \<rightarrow> Set)"})]
val GZF_axioms = 
    [("ext", @{prop "\<forall> x : Set. \<forall> y : Set. ((\<forall>b. b \<in> x \<longleftrightarrow> b \<in> y) \<longrightarrow> x = y)"}), 
     ("uni", @{prop "\<forall>x : SetOf Set. (\<forall>a. a \<in> \<Union> x \<longleftrightarrow> (\<exists>z. z \<in> x \<and> a \<in> z))"}), 
     ("pow", @{prop "\<forall>x : Set. \<forall>z : Set. z \<in> \<P> x \<longleftrightarrow> z \<subseteq> x"}),
     ("emp", @{prop "\<forall>b. \<not> (b \<in> \<emptyset>)"}),
     ("succ",@{prop "\<forall>x : Set. \<forall>b. b \<in> Succ x \<longleftrightarrow> (b \<in> x \<or> b = x)"}),
     ("inf", @{prop "\<emptyset> \<in> Inf \<and> (\<forall>a. a \<in> Inf \<longrightarrow> Succ a \<in> Inf)"}),
     ("repl", @{prop "\<forall>x : Set. \<forall>P : ReplPred x. (\<forall>b. b \<in> Repl x P \<longleftrightarrow> (\<exists>a. a \<in> x \<and> P a b \<and> b : SetMem))"})]\<close> 
end
local_setup \<open>snd o mk_main_class "GZF" (GZF_styps @ GZF_axioms)\<close>

section \<open>Ordered Pair feature\<close>
ML \<open>
val Pair_sig = 
    [("Pair", @{typ "'a \<Rightarrow> bool"}, nsyn),
     ("pair", @{typ "'a \<Rightarrow> 'a \<Rightarrow> 'a"}, nsyn)]
val Pair_defs = 
    [("PairMem", @{term "\<lambda>b :: 'a. \<exists>p :: 'a : Pair. \<exists>c :: 'a. 
                          p = pair b c \<or> p = pair c b"}, nsyn)]\<close>


local_setup \<open>snd o mk_sig_class "OPair" [] Pair_sig Pair_defs\<close>
context OPair_sig begin
ML \<open>val Pair_styps = 
  [("pair_typ", @{prop "pair : PairMem \<rightarrow> PairMem \<rightarrow> (Pair \<bar> PairMem)"})] 
    val Pair_axs =
  [("pair_projs", @{prop "\<forall>p : Pair. \<exists>a b. p = pair a b"}),
   ("cpop", @{prop "\<forall>a : PairMem. \<forall>b : PairMem. \<forall>c : PairMem. \<forall>d : PairMem.
                          pair a b = pair c d \<longleftrightarrow> (a = c \<and> b = d)"})]\<close>
end
local_setup \<open>snd o mk_main_class "OPair" (Pair_styps @ Pair_axs)\<close>


class app = fixes app :: "['a,'a,'a] \<Rightarrow> bool"
(*Explain what this is*)
abbreviation (in app) "app_mem P b \<equiv> \<exists> r : P. \<exists>c. app r b c \<or> app r c b"

section \<open>Relation Feature -- depends on GZF\<close>

(*Need better terminology to distinguish between \<lambda>-relations and d-relations.
  We can't use the symbols \<lambda> or - in Isabelle names. *)
(*Nice syntax for relations?*)
ML \<open>val binrel_sig = 
  [ ("BinRelation", @{typ "'a \<Rightarrow> bool"}, nsyn),
    ("mkrel", @{typ "'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a"}, nsyn),
    ("field", @{typ "'a \<Rightarrow> 'a"}, nsyn)]\<close>
local_setup \<open>snd o mk_sig_class "Relation" ["GZF","app"] binrel_sig []\<close>

(*Need to constrain BOTH the domain and the range of the constructed relation to sets, 
  because otherwise we can exploit Russell's paradox:
    Let P := (\<lambda>a b. \<not> app a b) and r := mk_rel {\<emptyset>} P, 
  hence app r \<emptyset> r \<longleftrightarrow> \<not> app \<emptyset> r*)

(*Mention in English text: if you don't want the Relation feature to depend on the Set feature, 
 you need extra axioms. Cite Jan Kuper*)
context Relation_sig begin

definition BinRelMem where 
 "BinRelMem \<equiv> app_mem BinRelation"

definition BinRelPred :: "'a \<Rightarrow> 'a \<Rightarrow> (['a,'a] \<Rightarrow> bool) \<Rightarrow> bool" 
  where "BinRelPred x y P \<equiv> \<forall>a b. a \<in> x \<longrightarrow> b \<in> y \<longrightarrow> P a b \<longrightarrow> a : BinRelMem \<and> b : BinRelMem"

ML \<open>val relation_axs =
  [("rel_typ",   @{prop "mkrel : (\<Pi> x : Set. \<Pi> y : Set. BinRelPred x y \<rightarrow> BinRelation)"}),
   ("field_typ", @{prop "field : BinRelation \<rightarrow> Set"}), 
   ("rel", @{prop "\<forall>x : Set. \<forall>y : Set. \<forall>P : BinRelPred x y. 
              (\<forall>a b. app (mkrel x y P) a b \<longleftrightarrow> (a \<in> x \<and> b \<in> y \<and> P a b))"}),
   ("ext", @{prop "\<forall>r : BinRelation. \<forall>s : BinRelation. (\<forall>a b. app r a b \<longleftrightarrow> app s a b) \<longrightarrow> r = s"}),
   ("field_iff", @{prop "\<forall>r : BinRelation. \<forall>x. x \<in> field r \<longleftrightarrow> (\<exists>y. app r x y \<or> app r y x)"})]\<close>
end
local_setup \<open>snd o mk_main_class "Relation" relation_axs\<close>


section \<open>Function Feature -- depends on Binary Relation feature\<close>

ML \<open> val fun_sig = 
    [("Function", @{typ "'a \<Rightarrow> bool"}, nsyn),
     ("mkfun", @{typ "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a"}, nsyn),
     ("dom", @{typ "'a \<Rightarrow> 'a"}, nsyn),
     ("ran", @{typ "'a \<Rightarrow> 'a"}, nsyn)]\<close>
local_setup \<open>snd o mk_sig_class "Function" ["GZF", "app"] fun_sig []\<close>

context Function_sig begin
definition FunMem where "FunMem \<equiv> app_mem Function"

definition FunPred :: "'a \<Rightarrow> (['a,'a] \<Rightarrow> bool) \<Rightarrow> bool" 
  where "FunPred s P \<equiv> \<forall>x : FunMem. x \<in> s \<longrightarrow> (\<exists>\<^sub>\<le>\<^sub>1 y : FunMem. P x y)"

ML \<open>val fun_axs = 
  [("mkfun_typ", @{prop "mkfun : (\<Pi> x : Set. FunPred x \<rightarrow> Function)"}),
   ("dom_typ",   @{prop "dom : Function \<rightarrow> Set"}),
   ("ran_typ", @{prop "ran : Function \<rightarrow> Set"}),
   ("fun", @{prop "\<forall>s : Set. \<forall>P : FunPred s. \<forall>x y. app (mkfun s P) x y 
                     \<longleftrightarrow> (x \<in> s \<and> P x y \<and> x : FunMem \<and> y : FunMem)"}),
   ("fun_prop", @{prop "\<forall>f : Function. \<forall>x y z. app f x y \<and> app f x z \<longrightarrow> y = z"}),
   ("fun_ext", @{prop "\<forall>f : Function. \<forall>g : Function. (\<forall>x y. app f x y \<longleftrightarrow> app g x y) \<longrightarrow> f = g"}), 
   ("fun_dom",   @{prop "\<forall>f : Function. \<forall>x. x \<in> dom f \<longleftrightarrow> (\<exists>y. app f x y)"}),
   ("fun_ran", @{prop "\<forall>f : Function. \<forall>y. y \<in> ran f \<longleftrightarrow> (\<exists>x. app f x y)"})]\<close>
end
local_setup \<open>snd o mk_main_class "Function" fun_axs\<close>


section \<open>Ordinal feature\<close>

ML \<open>
val ord_sig =
  [("Ord", @{typ "'a \<Rightarrow> bool"}, nsyn),
   ("lt", @{typ "['a,'a] => bool"}, mk_infixl ("<", 50)),
   ("zero", @{typ "'a"}, mk_sym "0"),
   ("succ", @{typ "'a \<Rightarrow> 'a"}, nsyn),
   ("omega", @{typ "'a"}, mk_sym "\<omega>")]
val ord_defs = 
  [("Limit", @{term "Ord \<bar> (\<lambda>\<mu> :: 'a. lt (zero :: 'a) \<mu> \<and> (\<forall>\<beta> :: 'a : Ord. lt \<beta> \<mu> \<longrightarrow> lt (succ \<beta>) \<mu>))"}, nsyn)]\<close>
local_setup \<open>snd o mk_sig_class "Ordinal" [] ord_sig ord_defs\<close>

context Ordinal_sig begin
ML \<open>val ord_axs =
 [("zero_typ", @{prop "0 : Ord"}),
  ("succ_typ", @{prop "succ : Ord \<rightarrow> Ord"}),
  ("omega_typ", @{prop "\<omega> : Limit"}),
  ("zero_ax", @{prop "\<forall>b : Ord. \<not> (b < 0)"}),
  ("succ_ax", @{prop "\<forall>a : Ord. \<forall>b : Ord. a < (succ b) \<longleftrightarrow> a < b \<or> a = b"}),
  ("omega_ax", @{prop "\<forall>\<mu> : Limit. \<mu> = \<omega> \<or> \<omega> < \<mu>"}),
  ("lt_trans", @{prop "\<forall>i : Ord. \<forall>j : Ord. \<forall>k : Ord. i < j \<longrightarrow> j < k \<longrightarrow> i < k"}),
  ("lt_notsym", @{prop "\<forall>i : Ord. \<forall>j : Ord. i < j \<longrightarrow> \<not> (j < i)"}),
  ("lt_linear", @{prop "\<forall>i : Ord. \<forall>j : Ord. i < j \<or> i = j \<or> j < i"}),
  ("lt_induct", @{prop "\<forall>P. (\<forall>i : Ord. (\<forall>j : Ord. j < i \<longrightarrow> P j) \<longrightarrow> P i) \<longrightarrow> (\<forall>a : Ord. P a)"})]\<close>
end
local_setup \<open>snd o mk_main_class "Ordinal" ord_axs\<close>


ML \<open>val nat_sig = 
   [("Nat", @{typ "'a \<Rightarrow> bool"}, nsyn), 
    ("Zero", @{typ "'a"}, mk_sym "\<zero>"), 
    ("S", @{typ "'a \<Rightarrow> 'a"}, nsyn)]\<close>
local_setup \<open>snd o mk_sig_class "Nat" [] nat_sig []\<close>

context Nat_sig begin
ML \<open>val nat_axs =
  [("zero_nat", @{prop "\<zero> : Nat"}),
   ("S_nat", @{prop "\<forall>n :: 'a. Nat n \<longrightarrow> Nat (S n)"}),
   ("S_inj", @{prop "\<forall>n m :: 'a. Nat n \<longrightarrow> Nat m \<longrightarrow> n = m \<longrightarrow> (S n :: 'a) = S m"}),
   ("S_nonzero", @{prop "\<forall>n :: 'a. Nat n \<longrightarrow> S n \<noteq> (Zero :: 'a)"}),
   ("nat_induct", @{prop "\<forall>P :: 'a \<Rightarrow> bool. P Zero \<longrightarrow> (\<forall>n :: 'a. Nat n \<longrightarrow> P n \<longrightarrow> P (S n)) 
                           \<longrightarrow> (\<forall>m. Nat m \<longrightarrow> P m)"})]\<close>
end
local_setup \<open>snd o mk_main_class "Nat" nat_axs\<close>



end