(*TODO: 
  - Connection locales should come with pre-defined 'swapped' constants! constant names ? ? 
  - Every Connection locale should open the 'lifting_syntax' bundle. Unsure if possible? 
 *)

(*------ Generating connection locales -------*)
fun get_connection_deps _   [] = [@{locale ConnectionBase}]
  | get_connection_deps thy ds = map (get_locale thy o (fn loc => loc ^ "Connection")) ds

fun connection_import thy cla deps = 
  let val cla' = get_class (get_ctxt thy) cla
      val (typ_a, typ_b) = (TFree ("'a", [cla']), @{typ 'b})
      val abs = ("Abs", typ_a --> typ_b, NoSyn)
      val rep = ("Rep", typ_b --> typ_a, NoSyn)
  in map (fn loc => (loc, ("",false), [abs,rep])) (get_connection_deps thy deps) end

fun mk_connection_locale thy (mcomp {name, deps,...}) =
  let val imports = locale_import_expr (connection_import thy name deps)
  in mk_locale (name ^ "Connection") imports [] [] end

(*  DEAD CODE - no need to import the locale of ModelBase type class,
                all we need to do is place a ModelBase sort constraint on the type 'a.
fun mk_base_connection_locale thy =
  let val imports = locale_expr thy [@{locale ModelBase}]
      val abs = ("Abs", SOME @{typ \<open>'a \<Rightarrow> 'b\<close>}, NoSyn) 
      val rep = ("Rep", SOME @{typ \<open>'b \<Rightarrow> 'a\<close>}, NoSyn)
      val tdef_form = @{prop \<open>type_definition Rep Abs (Set.Collect M)\<close>}
      val tdef_assm = ("tdef", tdef_form)
  in mk_locale "ConnectionBase" imports [abs,rep] [tdef_assm] end *)