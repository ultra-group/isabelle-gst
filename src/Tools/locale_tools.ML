(*Functions that allow interactions with Isar's locale interface.
  See src/Pure/Isar/
    locale.ML, expression.ML, element.ML, 
  See Isar Reference Manual - Sec 5.7 *)

(*Each locale is identified with a \<open>string\<close>*)

(*Gets full name of locale \<open>loc\<close> in \<open>thy\<close>*)
fun get_locale thy loc = 
  Locale.check thy (loc, Position.none)

(*Gets axioms of locale \<open>loc\<close> in \<open>thy\<close>*)
fun get_locale_axioms thy loc =
  case Locale.hyp_spec_of thy loc of
     (Element.Assumes xs) :: es => map (fn (a,b) => (fst a, fst (hd b))) xs
   | [] => [] 

fun get_locale_param_names thy loc =
  map (Binding.name o fst o fst) (Locale.params_of thy loc)

(*------ Locale Instances ------*)

(*TODO: Write code for forming instances of classes *)

(*A locale qualifier is a pair of type \<open>string * bool\<close>*)
(*A parameter instantiation of \<open>loc\<close> is a pair \<open>(iden, trm) : string * term\<close>
  where \<open>iden\<close> is a parameter of \<open>loc\<close>.*)
(*A locale instance is formed from a triple \<open>(loc, qual, params)\<close> where: 
    - \<open>loc\<close> is the name of a locale
    - \<open>qual\<close> is a locale qualifier
    - \<open>params\<close> is a list of parameter instantiations of \<open>loc\<close> *)
(* Let \<open>(str,b)\<close> be a locale qualifer. 
  If \<open>b\<close> is true, then the qualifier \<open>str\<close> must always be used in occurrences 
  of terms/facts defined in the locale when in a context of a locale declared with
  this locale instance as an import, or in the context enriched by an interpretation
  that uses this locale instance.
  Otherwise, the qualifier is optional.*)

(*
  Function \<open>locale_instance\<close> declared below creates a locale instance 
  from \<open>(loc, paul, params)\<close>. 
  Used in locale imports and interpretations.

  ---- EXAMPLE ---- 
  Let pair_inst = 
    ("Pair", ("Kuratowski", true), [("Pair", @{term iskpair}), ("pair", @{term kpair})]) 
  and nat_inst =
    ("Nat", ("vonNeumann", false), [("Nat", @{term isnat), ("Zero", @{term \<emptyset>}), (S, @{term Succ})])    
  
 1.1.  locale_instance pair_inst
  creates an ML term that is equivalent to that produced by the following Isar code
  which specifies a locale instance:
    Kuratowski : Pair 
      where Pair = iskpair 
        and pair = kpair 

 1.2. locale_instances [pair_inst, nat_inst]
    creates an ML term that is equivalent to that produced by the following Isar code
    which specifies a list of locale instances:
      Kuratowski : Pair 
      where Pair = iskpair 
        and pair = kpair
    + vonNeumann? : Nat
      where Nat = isnat
        and Zero = \<emptyset>
        and S = Succ
*)
fun locale_instance (loc,qual,params) = (loc, (qual, (Expression.Named params, []))) 
fun locale_instances locs_params = map locale_instance locs_params : (string, term) Expression.expr
val mk_for_clause = map (fn (str, typ, syn) => (Binding.name str, SOME typ, syn))
(*A parameter declaration is a triple of type \<open>string * typ * mixfix\<close>
  My terminology -- not Isabelle's. Corresponds with "the optional for clause"*)
(*A list of lists of declarations is merged by a union operation, 
  where equality is determined by comparing the string of the declaration*)
fun merge_decls [] = [] 
  | merge_decls (xs::xss) = List.foldr (merge (fn (p,q) => #1 p = #1 q)) xs xss


(*When we import locales A and B (that each use a single type variable) 
  in the declaration of a locale C, we usually want the type variable used by the types of the 
  parameters of A to remain the same as the one one fixed by locale B. 
  By default, Isabelle uses a different type variable for A and B.
  
  We can use parameter declarations to ensure this type variable is the same.
  We can also use parameter declarations to change the type variable. 
  e.g., when defining Connection locales for model components*)

(* A locale expression is a list of instances together with a list of parameter declarations.

  Creates a locale expression for the imports used in a locale declaration, 
  from a list of pairs \<open>(loc, qual, decls)\<close> where \<open>loc\<close> is a locale name,
  \<open>qual\<close> is a locale qualifier, and \<open>decls\<close> is a list of declarations.
  
 ---- EXAMPLE ----
  1.3. locale_import_expr [("Nat", ("foo",true), 
                            [("Nat", @{typ "'i \<Rightarrow> bool"}, nsyn), ("Zero", @{typ "'i"}, mk_sym "\<zero>"),
                             ("S", @{typ "'i \<Rightarrow> 'i", mk_sym "\<S>")]),
                           ("Pair", ("bar",false),
                             [("Pair", @{typ "'i \<Rightarrow> bool", nsyn), 
                              ("pair", @{typ "'i \<Rightarrow> 'i \<Rightarrow> bool", nsyn)])]
  creates an ML term denoting the locale import expression given by the Isar code

    foo  : Nat where Nat = Nat 
           and Zero = Zero
           and S = S
  + bar? : Pair where Pair = Pair
           and pair = pair
   for Nat :: "'i \<Rightarrow> bool"
   and Zero :: "'i" ("\<zero>")
   and S :: "'i \<Rightarrow> 'i" ("\<S>")
   and Pair :: "'i \<Rightarrow> bool"
   and pair :: "'i \<Rightarrow> 'i \<Rightarrow> bool"      *)

fun locale_import_expr locs_decls = let 
  val free_params = map (fn (str,typ,_) => (str, Free (str, typ)))
  val instances   = locale_instances (map (fn (loc,qual,decls) => (loc,qual,free_params decls)) locs_decls)
  val all_decls   = merge_decls (map (#3) locs_decls)
  val for_clause  = mk_for_clause all_decls
  in (instances, for_clause) : Expression.expression_i end

(*Creates a locale expression from a list of pairs of form \<open>(loc, qual)\<close>
  with declarations given by original declaration of \<open>loc\<close>.*)
fun locale_expr_qual thy locs = let  
  fun decls loc = map (fn ((str,typ),mix) => (str,typ,mix)) (Locale.params_of thy loc)
  in locale_import_expr (map (fn (loc, qual) => (loc, qual, decls loc)) locs) end

(*Creates a locale expression from a list of locales,
  using a default empty qualifier and declarations given by the original definition of the locale*)
fun locale_expr thy = locale_expr_qual thy o (map (fn loc => (loc, ("",false))))

(*Creates a locale expression used for interpretations 
  from a list of triples (\<open>(loc, qual, [(p1, t1), ..., (pn, tn)])\<close>)
  Creates the same Isar code as Example 1.2, but as a "locale expression" rather than
  a "locale instance".*)
fun locale_expr_interp locs_terms = (locale_instances locs_terms, []) : Expression.expression_i



(*------ Locale Declarations ------*)
(*Creates fix data from a triple of a string, type, and mixfix syntax*)
fun mk_fix (str,typ,syn) = (Binding.name str, typ, syn)
(*Creates assumption data from name and term for a locale expression *)
fun mk_assm (name,trm) = ((Binding.name name, []), [(trm, [])]) 
(*Creates assumption data from name and a list of terms for a locale expression*)
fun mk_assms (name,trms) = ((Binding.name name, []), map (fn t => (t,[])) trms)

(*Returns term \<open>s : typ \<equiv> trm\<close>*)
fun mk_def_ax (s, typ, trm) = Logic.mk_equals (Free (s, typ), trm)
(*Creates assumption data with \<open>name_def\<close> and \<open>s : typ \<equiv> trm\<close> for a locale expression*)
fun mk_defines (def as (s,_,_)) = mk_assm (s ^ "_def", mk_def_ax def)

(*Takes a name, a list of locale expressions, a list of declarations, a list of assumptions,
  and a local theory, and returns a new local theory including locale given by declaration:
       \<open>locale name = inst\<^sub>1 + ... + inst\<^sub>n 
                   + fixes fix\<^sub>1 and ... and fix\<^sub>n
                     assumes a\<^sub>1 : \<phi>\<^sub>1 and ... and a\<^sub>n : \<phi>\<^sub>n\<close>   *)
fun mk_locale name imports fixes assms lthy = 
  let val thy = Local_Theory.exit_global lthy 
      val fixes' = Element.Fixes (map mk_fix fixes)
      val assms' = Element.Assumes (map mk_assm assms) 
  in Expression.add_locale (Binding.name name) Binding.empty [] imports [fixes', assms'] thy end 


(*------ Modifying Locale Expressions ------*)

(*Apply \<open>f : (string * term) list -> (string * term) list\<close> to 
  the list of parameter instantiations in a locale instance*)
fun app_named_params f (loc, (qual, (params, rw))) =
  case params of Expression.Named ps => 
      (loc, (qual, (Expression.Named (f ps), rw)))
   | _ => error "Not a locale instance with named parameters."

(*Maps \<open>f : term -> term\<close> over the terms of parameter instantiation of locale instance with named parameters*)
fun map_named_params f = app_named_params (map (fn (str,trm) => (str, f trm)))
(*Extend the list of parameter instantiations of a locale instance*)
fun instantiate_params ps' = app_named_params (fn ps => ps @ ps')

(*Applies \<open>f\<close> and \<open>g\<close> to the name and type of the declaration, if there is one.*)
fun decl_app f g (bd, SOME typ, syn) = (f bd, SOME (g typ), syn) 
  | decl_app f _ (bd, NONE, syn) = (f bd, NONE, syn)

(*Maps \<open>f\<close> and \<open>g\<close> over a locale expression by: 
    - mapping \<open>f\<close> over the locale instances, and
    - applying \<open>g1\<close> and \<open>g2\<close> to each of the the fixed declarations\<close>*)
fun map_expr' f g1 g2 (is,ds) = (map (map_named_params f) is,  map (decl_app g1 g2) ds)
fun map_expr f g = map_expr' f (fn x => x) g


(*------ Using Interpretations of Locales ------*)

(*Returns the morphism of most recent interpretation of \<open>loc\<close> in \<open>ctxt\<close> *)
fun interp_morphism ctxt loc = 
  case Locale.registrations_of (Context.Proof ctxt) loc of
    [] => error ("No registration of locale " ^ loc ^ " found in context.")
  | _  => snd (hd (Locale.registrations_of (Context.Proof ctxt) loc))

fun interp_trm ctxt loc = Morphism.term (interp_morphism ctxt loc)
fun interp_typ ctxt loc = Morphism.typ (interp_morphism ctxt loc)

(*Creates a list of parameter instantiations from most recent interpretation of \<open>loc\<close>*)
fun interp_params ctxt loc = map (fn ((str,typ),_) => (str, interp_trm ctxt loc (Free (str,typ)))) 
                                  (Locale.params_of (get_thy ctxt) loc)

(*Create a locale instance of \<open>loc1\<close>, with parameter instantiations given by 
  the most recent interpretation of \<open>loc2\<close>*)
fun interp_instance ctxt loc1 loc2 = locale_instance (loc1, ("",false), interp_params ctxt loc2) 