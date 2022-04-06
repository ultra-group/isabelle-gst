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


