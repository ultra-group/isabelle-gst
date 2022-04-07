(*------- Model Components -------*)

datatype variant = vari of
  { tag_name  : string,
    vcases    : term * term * term,
    alpha_typ : term,
    excludes_formulas : term list } 

datatype model_comp = mcomp of 
  { name : string,
    deps : string list,
    variant : variant option }

fun get_mcomp_tag (mcomp {variant,...}) = case variant of
    SOME (vari v) => #tag_name v 
  | NONE          => error "Cannot get tag name, component has no variant"

fun get_mcomp_vcases (mcomp {variant,...}) = case variant of
    SOME (vari v) => #vcases v 
  | NONE          => error "Cannot get variant cases, component has no variant"

fun mk_variants_0 i A = 
  HOLogic.mk_Trueprop (HOLogic.mk_eq 
    (@{term Variants} $ i $ @{term 0}, Abs ("x", @{typ 'a}, A))) 

fun mk_variants_succ i F = 
  HOLogic.mk_Trueprop (mk_tall ("j", @{typ 'a}, @{term Ord}, 
      HOLogic.mk_eq (@{term Variants} $ i $ (@{term "succ j"}), 
                     F $ @{term "succ j"})))

fun mk_variants_lim i G = 
  HOLogic.mk_Trueprop (mk_tall ("\<mu>", @{typ 'a}, @{term Limit},
      HOLogic.mk_eq (@{term Variants} $ i $ (@{term "\<mu> :: 'a"}), 
                     G $ @{term "\<mu> :: 'a"})))

fun tag_formula B = 
  HOLogic.mk_Trueprop (mk_styping_trm B @{typ 'a} @{term Tag}) 

fun alpha_typ_formula tag styp =
  HOLogic.mk_Trueprop (HOLogic.mk_eq (@{term \<alpha>} $ tag, styp))

fun M_formula B = 
  HOLogic.mk_Trueprop (mk_styping_trm B @{typ 'a} @{term M}) 

fun mk_excludes_assms tag_name ts =
  (map (fn i => "excluded_" ^ tag_name ^"_"^ (Int.toString i)) 
   (1 upto (length ts))) ~~ ts

fun tag_trm name = Free (name, @{typ 'a})
fun mdefault_trm name = Free (name ^ "_mdefault", @{typ 'a})

fun get_mcomp_imports _    [] = [@{locale ModelBase}]
  | get_mcomp_imports ctxt ms = map (get_class ctxt) ms 
  
fun mk_mcomp_class (mcomp {name, deps, variant}) ctxt =
  let val imports = get_mcomp_imports ctxt deps
      val fixes = [(name ^ "_mdefault", SOME @{typ 'a}, NoSyn)]
      val mdefault_m = (name ^ "_mdefault_m", M_formula (mdefault_trm name))
  in case variant of    
  SOME (vari {tag_name, vcases, alpha_typ, excludes_formulas}) => 
      let val tag = tag_trm tag_name
          val tag_fix = (tag_name, SOME @{typ 'a}, NoSyn)
          val (v0, v_succ, v_lim) = vcases
          val assms = 
            [ mdefault_m,
             (tag_name ^ "_tag", tag_formula tag),
             ("v_" ^ tag_name ^ "_0", mk_variants_0 tag v0),
             ("v_" ^ tag_name ^ "_succ", mk_variants_succ tag v_succ),
             ("v_" ^ tag_name ^ "_limit", mk_variants_lim tag v_lim),
             ("alpha_" ^ tag_name, alpha_typ_formula tag alpha_typ)]
           @ mk_excludes_assms tag_name excludes_formulas
       in mk_class name imports (tag_fix :: fixes) assms ctxt end
   | NONE => mk_class name imports fixes [mdefault_m] ctxt end

(*------ Model component morphisms -------*)

(*A term morphism is a pair of a morphism, together with a list of 
  terms that forms a subset of the domain of that morphism*)
(*The list is the SUPPORT of the tern part of the morphism*)

type model_sig = 
  { feature : string,
    morph : morphism,
    support : binding list }

(*A model component morphism is a triple (iden, (\<phi>, ts)), where: 
    \<^enum> \<open>iden\<close> is the name of the target feature class
    \<^enum> \<open>\<phi>\<close> is a morphism mapping some constants of a feature's typeclass 
      to model constants, and \<open>ts\<close> is a list of those constants *)
fun msig_app (msig : model_sig) = Morphism.binding (#morph msig) 
fun msig_term_app ctxt msig trm = 
  let val bd_map = (Syntax.read_term ctxt o Binding.name_of 
      o msig_app msig o Binding.name) 
  in case trm of
     Free (id,_) => bd_map id
   | t => t
  end

fun msig_ran (msig : model_sig) = map (msig_app msig) (#support msig) 
fun msig_term_ran ctxt msig = 
  map (Syntax.read_term ctxt o Binding.name_of o msig_app msig) (#support msig) 

fun mk_fun dom ran c = 
  case List.find (fn (x,_) => x = c) (ListPair.zip (dom,ran)) of
    SOME (_,y) => y
  | NONE   => c  

fun msig_compose ((m1,s1), (m2,s2)) =
  (Morphism.compose m1 m2, s1 @ s2)

fun mk_msig msigs str cla ids ctxt = 
  let 
    val feat_name = get_class ctxt cla
    val feat_params = get_locale_param_names (get_thy ctxt) feat_name
    val bnds = map Binding.name ids
    val imports = List.foldl msig_compose (Morphism.identity, []) 
        (map (fn msig : model_sig => (#morph msig, #support msig)) msigs)
    val morph = Morphism.binding_morphism str (mk_fun feat_params bnds)
    val (morph', supp) = msig_compose ((morph, feat_params), imports)
  in 
    {feature = feat_name, morph = morph', support = supp} : model_sig
  end;