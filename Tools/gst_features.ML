(*A feature is a represented as an ML record, with the following definition: *)
datatype gst_feature = Feature 
of { name : string, 
     deps : string list,
     feature_sig : (string * typ * mixfix) list,
     simple_defs : (string * term) list,
     theory : (string * term) list,
     child_pred : string option } 

(* A feature declaration \<open>F\<close> is an ML record consists of the following fields:

  name : string 
    -- The name of the feature. 
       Used as a prefix for the names of the locales L(F), shown below.
          
  deps : string list
    -- A list of the names of features that F depends on.
       Used for gathering locale imports when generating features

  feature_sig : (string * typ * mixfix) list
    -- A list of declarations (iden, \<tau>, \<MM>) for the signature of the theory,
       Where \<open>iden\<close> is the name of the constant, \<tau> is the Isabelle 
       including any soft-types that are not given by simple definition.

  simple_defs : (string * term) list
    -- A list of pairs of strings and terms \<open>(iden, B)\<close>,
       used for forming simple definitions \<open>iden \<equiv> B\<close>. 

  theory : (string * term) list
    -- A list of pairs of strings and terms \<open>(str,B)\<close> representing the axioms of the feature. 
       Can include partial-typings of the constants given by feature_sig.
       \<open>B\<close> must be a term of type \<open>bool\<close> and can make use of the constants 
       given by feature_sig and simple_defs.  
       \<open>str\<close> is the name given to the axiom \<open>B\<close>.
       
  child_pred : string option
    -- The name of an optional child predicate given in either \<open>feature_sig\<close> or \<open>simple_defs\<close>.
      Afterwards, this constant is used for building well-foundedness axioms for feature combinations.
*)


(* A feature \<open>F\<close> has 2 locales associated with it: 
    L(F) = { <NAME>_sig,           -- Fixes parameters for: 
                                   (a). the signature of the feature,
                                   (b). the constant used for the feature's default value, and 
                                   (c). constants for soft types not given by simple definition.  
                                   Also adds simple definitions provided by the user.
                                   The user should never see this locale, 
                                   or do any development within its context. *)

(*Takes a name, list of names, a signature, and simple definitions, and a local theory,
  and returns a pair \<open>(loc, lthy)\<close> where loc is the name of the generated locale (i.e <NAME>_sig)
  and lthy is a local theory updated with the registration of \<open>loc\<close>, 
  and with the definitions from \<open>defs\<close> *)
fun mk_sig_locale name deps decls defs lthy = let
  val thy = get_thy lthy
  val imports = locale_expr thy (map (get_locale thy) deps)
  val def_decl = (name ^ "_default", SOME @{typ 'd}, nsyn) 
  val fixes = def_decl :: map (fn (str,typ,syn) => (str, SOME typ, syn)) decls 
  val (loc, lthy') = mk_locale (name ^ "_sig") imports fixes [] lthy
  in (loc, make_defns lthy' defs) end

fun mk_sig_class name deps decls defs lthy = let
  val imports = (map (get_class lthy) deps)
  val def_decl = (name ^ "_default", SOME @{typ 'a}, nsyn) 
  val fixes = def_decl :: map (fn (str,typ,syn) => (str, SOME typ, syn)) decls 
  val (loc, lthy') = mk_class (name ^ "_sig") imports fixes [] lthy
  in (loc, make_defns lthy' defs) end

(* EXAMPLE 2.1:  Consider the following Isar code:

local_setup 
  \<open> snd o mk_sig_locale "Nat" [] 
        [("Nat", @{typ "'d \<Rightarrow> bool"}, nsyn), 
         ("Zero", @{typ "'d"}, nsyn), 
         ("Succ", @{typ "'d \<Rightarrow> 'd"}, nsyn)]
        [("AddTwo", @{term "(\<lambda>n :: 'd. Succ (Succ n))"}}),
         ("NonZero", @{term "(\<lambda>n :: 'd. n \<noteq> Zero)})] \<close>
         
Running the above Isar code has the same effect as running the following Isar code: 
  
locale Nat_sig = 
  fixes Nat_default :: "'d
    and Nat :: "'d \<Rightarrow> bool" 
    and Zero :: "'d"
    and Succ :: "'d \<Rightarrow> bool"
 
context Nat_sig begin
 
definition "AddTwo \<equiv> (\<lambda>n :: 'd. Succ (Succ n))"
definition "NonZero \<equiv> (\<lambda>n :: 'd. n \<noteq> Zero)"

end *)


(* EXAMPLE 2.2: Consider the following Isar code:

local_setup 
  \<open> snd o mk_sig_locale "OrdRec" ["GZF", "Ordinal"]
      [("predSet", @{typ "'d \<Rightarrow> 'd"}, nsyn), 
        ("supOrd", @{typ "'d \<Rightarrow> 'd"}, nsyn), 
        ("OrdRec", @{typ "[['d, 'd \<Rightarrow> 'd] \<Rightarrow> 'd, ['d,'d] \<Rightarrow> 'd", 'd, 'd] \<Rightarrow> 'd}, nsyn)]\<close>
      [] \<close>

Running the above Isar code has the same effect as running the following Isar code: 

locale OrdRec_sig = 
    GZF GZF_default Set Mem Emp Union Pow Succ Inf Repl 
  + Ordinal Ordinal_default Ord lt zero succ omega
  for GZF_default :: "'d"
  and Set :: "'d \<Rightarrow> bool"
  and Mem :: "'d \<Rightarrow> 'd \<Rightarrow> bool"  (infixl \<open>\<in>\<close> 50)
  and Emp :: "'d"  (\<open>\<emptyset>\<close>)
  and Union :: "'d \<Rightarrow> 'd"  (\<open>\<Union> _\<close> [90] 90)
  and Pow :: "'d \<Rightarrow> 'd"  (\<open>\<P> _\<close> [90] 90)
  and Succ :: "'d \<Rightarrow> 'd"
  and Inf :: "'d"
  and Repl :: "'d \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'd"  (\<open>\<R>\<close>)
  and Ordinal_default :: "'d"
  and Ord :: "'d \<Rightarrow> bool"
  and lt :: "'d \<Rightarrow> 'd \<Rightarrow> bool"  (infixl \<open><\<close> 50)
  and zero :: "'d"  (\<open>0\<close>)
  and succ :: "'d \<Rightarrow> 'd"
  and omega :: "'d"  (\<open>\<omega>\<close>) +
  fixes OrdRec_default :: "'d"
    and predSet :: "'d \<Rightarrow> 'd"
    and supOrd  :: "'d \<Rightarrow> 'd"
    and OrdRec :: "('d \<Rightarrow> 'd) \<Rightarrow> 'd" 

Our code is used for a special case of locale import where the free variable
is always kept the same. Perhaps this always happens with typeclasses?

*)
fun mk_main_locale name axioms lthy = let
  val thy = get_thy lthy
  val import = locale_expr thy [get_locale thy (name ^ "_sig")]
  in mk_locale name import [] axioms lthy end 

fun mk_main_class name axioms lthy = let
  val import = [get_class lthy (name ^ "_sig")]
  in mk_class name import [] axioms lthy end



(*! ! ! ! ! ! WARNING: UNDER CONSTRUCTION ! ! ! ! *)
(*
             <NAME>,               -- The main locale. Inherits solely from \<open>NAME\<close>_sig. 
                                   Assumes (a). the axioms of the theory, 
                                           (b). the partial-typings of the signature            
                                   The user works within this locale to develop definitions
                                   & theorems for a feature's interface.

   EXAMPLE:

} *)



(* 
fun suffixes [] = []
  | suffixes xs = map ((fn s => "_" ^ s) o Int.toString) (1 upto (length xs))

fun mk_dom_preds (str,styp) = 
 let fun preds str [] = error ("Error, no soft type assigned for " ^ str) 
       | preds str [(x,_)] = [("ran_" ^ str, x)]
       | preds str ((x,n)::xs) = ("dom_" ^ str ^ n, x) :: preds str xs 
      val styps = get_styps styp
      val sufxs = case length styps of
                    2 => ["",""]
                  | _ => suffixes styps 
 in preds str (get_styps styp ~~ sufxs) end
*)
(*
fun mk_feature_locale (f as feature {name, feature_sig, deps, styp_fixes, styp_defs,...}) lthy = let
  val (loc, lthy') = mk_feature_defs_locale name feature_sig (get_fdeps f) styp_fixes styp_defs lthy
  val thy' = Local_Theory.exit_global lthy'
  val imports = locale_expr thy' [loc] 
  val (_,lthy'') = mk_locale (get_fname f) imports [] (mk_feature_assms f) lthy'
  in lthy'' end  *) 


(*Probably don't need: 

(*If \<open>iden\<close> is a name, and \<open>styp\<close> is a soft-type on a \<tau>, 
  then \<open>mk_styp_assm iden styp\<close> returns the pair \<open>(iden_typ, Free (iden, \<tau>) : P)\<close>.
  This pair is later handed to the locale 'assumption' machinery, 
  so that 'iden_typ' is the name given to the fact \<open>iden : P\<close> in the context
  of a locale that uses this assumption.*)
fun mk_styp_assm iden styp = 
  let val typ = domain_type (fastype_of styp)
      val prop = HOLogic.mk_Trueprop (mk_styping_trm (Free (iden, typ)) typ styp)
  in (iden ^ "_typ", prop) end*)
