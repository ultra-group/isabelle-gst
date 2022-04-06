
(*
  Suppose we have already performed:
  - typedef dj = { x :: di | x : M}
  - setup_lifting dj
  Now we want to lift each of the constants from
  a model signature, and also prove the axioms of the target feature
  using those lifted constants.
*)

fun rsp_thms_tac thms ctxt = (resolve_tac ctxt thms 1) THEN (auto_tac ctxt)

fun lift_def_open_proof iden typ rhs lthy= 
  let
    val typ_str = YXML.content_of (Syntax.string_of_typ lthy typ)
  in 
    Lifting_Def_Code_Dt.lift_def_cmd
      ([], (Binding.name iden, SOME typ_str, NoSyn), rhs, []) lthy
  end

fun lift_def_ml tactic iden typ trm lthy = 
  let
    val method = (Method.Basic (SIMPLE_METHOD o REPEAT o tactic), Position.no_range);
    val state = lift_def_open_proof iden typ trm lthy
  in
    if Proof.goal_finished state 
    then Proof.global_immediate_proof state
    else Proof.global_terminal_proof (method, NONE) state
  end

val last_field = List.last o (String.fields (fn c => c = #"."))
fun lift_mconst tac abs_typ ((iden,rhs),lthy) = 
  let 
    val typ_name = (last_field o fst o dest_Type) abs_typ
    val const = Syntax.read_term lthy iden
    val typ' = map_atyps (fn ty => case ty of TFree ("'a", _) => abs_typ | _ => ty) 
                         (fastype_of const)
  in 
    lift_def_ml tac (iden ^ "_" ^ typ_name) typ' rhs lthy 
  end

fun lift_mconsts thms abs_typ msig lthy = 
  let 
    val pairs = (map Binding.name_of (#support msig)) 
             ~~ (map Binding.name_of (msig_ran msig))
    val tac = rsp_thms_tac thms  
  in List.foldl (lift_mconst tac abs_typ) lthy pairs end 

