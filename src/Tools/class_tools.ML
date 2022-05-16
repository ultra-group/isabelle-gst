(*Functions that allow interactions with Isar's locale interface.
  See src/Pure/Isar/
    class.ML, class_declaration.ML, element.ML, 
  and src/Pure/
    axclass.ML
  See Isar Reference Manual - Sec 5.8 *)

(*Each class is identified with a \<open>string\<close>*)
val get_class = Proof_Context.read_class

(*TODO: DOCUMENT --- SAME BUT FOR CLASSES*)
fun mk_class name imports fixes assms lthy = 
  let val thy = Local_Theory.exit_global lthy 
      val fixes' = Element.Fixes (map mk_fix fixes)
      val assms' = Element.Assumes (map mk_assm assms) 
  in Class_Declaration.class (Binding.name name) [] imports [fixes', assms'] thy end 

fun ofclass_form ctxt typ cla = 
  let val name = (get_class ctxt cla) ^ "_class"
      val t_itself = Type ("itself", [typ])
      val pure_typ = Const ("Pure.type", t_itself)
  in Const (name, t_itself --> @{typ prop}) $ pure_typ end 

fun class_params thy cla = #params (Axclass.get_info thy cla)
fun class_param_names thy cla = map (last_field o fst) (class_params thy cla)
fun class_axioms thy cla = #axioms (Axclass.get_info thy cla)
fun interp_generic_term ctxt cla typ trm =
  let
    val morph = interp_morphism ctxt cla
    val trm' = map_types (map_atyps (Morphism.typ morph)) (Morphism.term morph trm)
    val trm'' = subst_TVars [(("'a",0), typ)] trm'
  in trm'' end

fun drop_last xs = List.take (xs,length xs - 1)
fun get_class_deps thy cla =
  let
    val cla_def_trm = (Thm.prop_of o #def o Axclass.get_info thy) cla
    val of_cla_list = (drop_last o Logic.dest_conjunction_list o snd o Logic.dest_equals) cla_def_trm
  in 
    case map (snd o Logic.dest_of_class) of_cla_list of
      ["HOL.type"] => []
    | xs => xs
  end

fun cla_insts ctxt cla typ = 
  let val ps = class_params (get_thy ctxt) cla
  in map (interp_generic_term ctxt cla typ o Const) ps end

(*-------- Automatically proving instantiations --------*)

fun open_instantiation typ_str cla thy = 
  let val ctxt' = Class.instantiation ([typ_str],[], [cla]) thy
  in ctxt' end

fun add_param_defs typ_str ts cla lthy = 
  let
    val defns = map (fn (iden, t) => (iden ^ "_" ^ (last_field typ_str), t, NoSyn)) 
                  (class_param_names (get_thy lthy) cla ~~ ts)
  in 
    make_defns lthy defns
  end

fun get_dep_trivs thy cla = map (Thm.class_triv thy) (\<^class>\<open>type\<close> :: get_class_deps thy cla) 

fun prove_instance def_thms lthm cla lthy =
  let
    fun intro_tac lthy = resolve_tac lthy [#intro (Axclass.get_info (get_thy lthy) cla)] 1
    val trivs = get_dep_trivs (get_thy lthy) cla
    fun resolve_trivs lthy = REPEAT_DETERM (resolve_tac lthy trivs 1)
    fun resolve_lthm lthy = resolve_tac lthy [lthm] 1
  in 
    Class.prove_instantiation_exit (fn lthy => 
      intro_tac lthy 
        THEN resolve_trivs lthy 
        THEN (TRY (unfold_tac lthy def_thms
        THEN resolve_lthm lthy))) lthy
  end

fun get_loc_thm_trms thm typ =
     (snd o strip_comb o subst_TVars [(("'a", 0), typ)] 
       o HOLogic.dest_Trueprop o Thm.full_prop_of) thm

fun get_trm_inst_defs thm typ_str thy = 
      map (Global_Theory.get_thm thy 
      o (fn iden => iden ^ "_" ^ (last_field typ_str) ^ "_def") 
      o last_field o fst o dest_Const) (get_loc_thm_trms thm \<^typ>\<open>_\<close>)

fun get_lthm thy cla = (class_axioms thy cla)

fun mk_instantiation typ_str cla ts loc_thm thy = 
  let 
    val lthy'    = open_instantiation typ_str cla thy
    val lthy''   = add_param_defs typ_str ts cla lthy' 
    val def_thms = case get_lthm thy cla of
      [lthm] => get_trm_inst_defs lthm typ_str (get_thy lthy'')
    | [] => [] 
    | _ => error "lthm list longer than expected"
    val thy' = prove_instance def_thms loc_thm cla lthy''
  in thy' end