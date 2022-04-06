(*------ Generating swapped constants -------*)

fun swapty _     (TFree ("'a", _))  = @{typ 'b} (*Sort constraints?*)
  | swapty a_var (TFree ("'b", _))  = a_var
  | swapty a_var (Type ("fun",[u,t])) = swapty a_var u --> swapty a_var t
  | swapty _ @{typ bool} = @{typ bool}
  | swapty _ _ = error "swapty error: Type not made from 'a and 'b and bool and \<Rightarrow>"

fun swap B abs_trm rep_trm a_var = 
  let fun swap' i B = 
      case fastype_of B of 
        (Type ("fun",[u,_])) => 
            let val x = Var (("x",i), swapty a_var u) 
            in lambda x (swap' (i+1) (B $ (swap' (i+1) x))) end
       | TFree ("'a", _) => abs_trm $ B (*Sort constraints?*)
       | TFree ("'b", _) => rep_trm $ B
       | @{typ bool} => B
       | _ => error ("Type not made from 'a and 'b and bool and \<Rightarrow>")
  in swap' 0 B end

val last_field = List.last o (String.fields (fn c => c = #"."))

fun gen_swap_pairs m_morph abs_trm rep_trm a_var = let
  fun name_of (Free (iden,_)) = last_field iden
  fun mconst_of   c = mcomp_app m_morph c
  fun con_pair_of c = (name_of c ^ "'", swap (mconst_of c) abs_trm rep_trm a_var) 
  in map (fn t => (mconst_of t, con_pair_of t)) (mcomp_dom m_morph) end

fun defn_swaps m_morph lthy = 
  let
    val abs_trm = Syntax.read_term lthy "Abs"
    val rep_trm = Syntax.read_term lthy "Rep"
    val a_var = Syntax.read_typ lthy "'a"
    val swap_pairs = gen_swap_pairs m_morph abs_trm rep_trm a_var
    val (trms, lthy') = make_defns_trms lthy 
      (map (fn (_, (iden, trm)) => (iden, trm, NoSyn)) (swap_pairs))
  in 
    ((map fst swap_pairs ~~ List.rev trms), lthy') 
  end


(*------ Generating transfer rules for swapped constants ------*)

fun type_to_transfer_rel crel @{typ 'b} = crel
  | type_to_transfer_rel _ @{typ bool} = @{term iff}
  | type_to_transfer_rel crel (Type ("fun",[u,t])) = 
      Const ("BNF_Def.rel_fun", 
         @{typ "(_ \<Rightarrow> _ \<Rightarrow> bool) \<Rightarrow> (_ \<Rightarrow> _ \<Rightarrow> bool) \<Rightarrow> (_ \<Rightarrow> _) \<Rightarrow> (_ \<Rightarrow> _) \<Rightarrow> bool"})
           $ type_to_transfer_rel crel u $ type_to_transfer_rel crel t
  | type_to_transfer_rel _ _ = error ("Type not made from 'b and bool and \<Rightarrow>")

fun mk_transfer_rule_form ctxt (c1,c2) = 
  let
    val (crel, typ) = (Syntax.read_term ctxt "(\<simeq>)", fastype_of c2)
    val rel = Syntax.check_term ctxt (type_to_transfer_rel crel typ)
  in 
    HOLogic.mk_Trueprop (rel $ c1 $ c2)
  end

fun mk_swap_transfers swaps ctxt =
  map (mk_transfer_rule_form ctxt) swaps

(*How to properly Isar syntax into ML objects without using Cookies?*)
(* fun lift_model_defs_cmd (fact_name, src) ctxt *)
