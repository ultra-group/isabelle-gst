(*  Suppose we have already performed:
  - typedef dj = { x :: di | x : M}
  - setup_lifting dj
  Now we want to lift each of the constants from
  a model signature, and also prove the axioms of the target feature
  using those lifted constants.
*)
fun lift_def_open_proof iden typ rhs lthy = 
  let
    val typ_str = YXML.content_of (Syntax.string_of_typ lthy typ)
  in 
    Lifting_Def_Code_Dt.lift_def_cmd
      ([], (Binding.name iden, SOME typ_str, NoSyn), rhs, []) lthy
  end


fun rsp_thms_tac thms ctxt = (Method.insert_tac ctxt thms 0)
 
fun lift_def_ml thm iden typ trm lthy = 
  let
    val state = (lift_def_open_proof iden typ trm lthy)
    val fact_method = (Method.Basic (fn _ => Method.fact [thm] lthy), Position.no_range)
  in
    if Proof.goal_finished state 
      then Proof.global_immediate_proof state
      else Proof.global_terminal_proof (fact_method, NONE) state
  end
 

fun has_Lfun (Type ("fun", [u,v])) =
    (case u of
      Type ("fun", _) => true
    | _ => has_Lfun u orelse has_Lfun v)
  | has_Lfun _ = false

fun needs_transfer_rule trm = 
  (fn typ => has_Lfun typ orelse not (body_type typ = @{typ bool})) (fastype_of trm)

fun lift_mconst abs_typ ((thm,(iden,rhs)),lthy) = 
  let 
    val typ_name = (last_field o fst o dest_Type) abs_typ
    val const = Syntax.read_term lthy iden
    val typ' = map_atyps (fn ty => case ty of TFree ("'a", _) => abs_typ | _ => ty) 
                         (fastype_of const)
  in 
    lift_def_ml thm (iden ^ "_" ^ typ_name) typ' rhs lthy 
  end

fun pair_rsp_thms ctxt (t::thms) ((t', (p, mp))::ps) = 
      if needs_transfer_rule (Syntax.read_term ctxt p) 
        then (t,  (p,mp)) :: pair_rsp_thms ctxt thms ps
        else (t', (p,mp)) :: pair_rsp_thms ctxt (t::thms) ps
      | pair_rsp_thms _ [] ps = ps
      | pair_rsp_thms _ _ [] = error "more resp theorems than needed?"

fun lift_mconsts thms abs_typ msig lthy = 
  let 
    val const_pairs = (map Binding.name_of (#support msig)) 
                   ~~ (map Binding.name_of (msig_ran msig))
    val thm_pairs = pair_rsp_thms lthy thms (map (fn p => (@{thm TrueI}, p)) const_pairs)                
  in List.foldl (lift_mconst abs_typ) lthy thm_pairs end