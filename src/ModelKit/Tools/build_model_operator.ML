(*Builds a term \<open>if P then b else c\<close>*)
fun mk_if typ P b c = 
  let val If = (Const ("HOL.If", @{typ bool} --> typ --> typ --> typ))
  in If $ P $ b $ c end

(*Builds a term \<open>if v = n then b else c\<close>*)
fun mk_if_eq typ v n b c = 
   mk_if typ (HOLogic.eq_const (fastype_of n) $ v $ n) b c

(*Builds the term \<open>caseof_ord b f g\<close> *)
fun mk_ordcases typ (b,f,g) =
  let val caseop = Const ("Ordinal.Ordinal_class.caseof_ord", 
          typ --> (typ --> typ --> typ) --> (typ --> typ --> typ) --> (typ --> typ --> typ))
  in caseop $ b $ f $ g end

fun zero_const typ = Const ("GST_Features.Ordinal_class.zero", typ)
fun mk_succ typ n = Const ("GST_Features.Ordinal_class.succ", typ --> typ) $ n
fun ord_pred_const typ = (Const ("GST_Features.Ordinal_class.Ord", typ --> @{typ bool}))
fun limit_pred_const typ = (Const ("GST_Features.Ordinal_class.Limit", typ --> @{typ bool}))

fun mk_ord typ 0 = zero_const typ
  | mk_ord typ n = mk_succ typ (mk_ord typ (n-1))

fun mk_ord_styping j = mk_styping j (ord_pred_const (fastype_of j)) 
fun mk_lim_styping j = mk_styping j (limit_pred_const (fastype_of j)) 
(*Builds a term denoting an ordinal-indexed sequence of functions,
  (that defaults to a chosen value) from a list of pairs of ordinals and functions *)
fun mk_ord_seq typ v default seq =
  List.foldr (fn ((n,t), s) => mk_if_eq typ v n t s) default seq

fun ordinal_list typ k = 
  let fun ordinal_list 0 ns = ns
        | ordinal_list k (n :: ns) = ordinal_list (k-1) (mk_succ typ n :: n :: ns)      
  in List.rev (ordinal_list k [zero_const typ]) end

(* val ordinal_list_poly = ordinal_list' @{term succ} @{term zero} *)
fun mk_variants typ cols = 
  let
    val (i,j,x) = (Bound 2, Bound 1, Bound 0)
    val default = Const ("GST_Features.Ordinal_class.Ordinal_default", typ)
    val ord_cases = map (fn (ord,col) => (ord, mk_ordcases typ col $ j $ x)) cols
    val body = mk_ord_seq typ i default ord_cases
  in Term.abs ("i", typ) (Term.abs ("j", typ) (Term.abs ("x", typ) body)) end


fun get_cols ctxt typ ms = 
  let
    val cols = 
      (map (get_mcomp_vcases) o filter 
         (fn mcomp {variant,...} => Option.isSome variant))
            (resolve_mdeps ms)
    val interp = interp_generic_term ctxt \<^class>\<open>ModelBase\<close> typ
  in 
    map (fn (z,s,l) => (interp z, interp s, interp l)) cols
  end

fun mk_variants_case_rule typ (vname,vdef_thm,vtrm) ((n, (otrm, (z,s,l))), ctxt) =
  let
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (betapply (vtrm,otrm), mk_ordcases typ (z,s,l)))
    val thm_name = vname ^ "_" ^ Int.toString n
    val state = Proof.theorem NONE (after_qed (Binding.name thm_name, [])) [[(eq,[])]] ctxt
    val state' = Proof.unfolding [[([vdef_thm, if_thm n], [])]] state
  in
    Proof.global_default_proof state'
  end

fun mk_variants_zero_rule typ (vname,vcase_thm,vtrm) ((n,(otrm, (zero_case, _, _))), ctxt) =
  let
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq 
                (betapplys (vtrm,[otrm, zero_const typ, Free ("x", typ)]), zero_case))
    
    val thm_name = vname ^ "_" ^ Int.toString n ^ "_zero"
    val state = Proof.theorem NONE (after_qed (Binding.name thm_name, [])) [[(eq,[])]] ctxt
    val state' = Proof.unfolding [[([vcase_thm,  @{thm case_ord_zero}], [])]] state
  in
    Proof.global_default_proof state'
  end

fun mk_variants_succ_rule typ (vname,vcase_thm,vtrm) (n,otrm) succ_case ctxt =
  let
    val (j, x) = (Free ("j", typ), Free ("x", typ))
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq 
              (betapplys (vtrm,[otrm, mk_succ typ j, x]), 
               betapplys (succ_case, [mk_succ typ j, x])))
    val imp = Logic.mk_implies (HOLogic.mk_Trueprop (mk_ord_styping j), eq)
    val thm_name = vname ^ "_" ^ Int.toString n ^ "_succ"
    val state = Proof.theorem NONE (after_qed (Binding.name thm_name, [])) [[(imp,[])]] ctxt
    val state' = Proof.unfolding [[([vcase_thm, @{thm case_ord_succ}], [])]] state
  in
    Proof.global_default_proof state'
  end

fun mk_variants_lim_rule typ (vname,vcase_thm,vtrm) (n,otrm) lim_case ctxt =
  let
    val (u, x) = (Free ("u", typ), Free ("x", typ))
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq 
              (betapplys (vtrm,[otrm, u, x]), 
               betapplys (lim_case, [u,x])))
    val imp = Logic.mk_implies (HOLogic.mk_Trueprop (mk_lim_styping u), eq)
    val thm_name = vname ^ "_" ^ Int.toString n ^ "_lim"
    val state = Proof.theorem NONE (after_qed (Binding.name thm_name, [])) [[(imp,[])]] ctxt
    val state' = Proof.unfolding [[([vcase_thm, @{thm case_ord_lim}], [])]] state
  in
    Proof.global_default_proof state'
  end

fun mk_variants_const typ =
  Const ("ModelBase.ModelBase_class.Variants", typ --> typ --> typ --> typ)

(*Defines Variants operator for a model in \<open>typ\<close> using model components \<open>ms\<close>.
  Variants is defined as a nested if statement on ordinals, 
  rules are autoproved:
    Variants_\<open>typ\<close>_\<open>i\<close> : "Variants_\<open>typ\<close> i \<equiv> caseof_ord ZERO(m\<^sub>i) SUCC(m\<^sub>i) LIMIT(m\<^sub>i)"
    Variants_\<open>typ\<close>_\<open>i\<close>_zero : "Variants_\<open>typ\<close> i 0 x = ZERO(m\<^sub>i)"
    Variants_\<open>typ\<close>_\<open>i\<close>_succ : "j : Ord \<Longrightarrow> Variants_\<open>typ\<close> i (succ j) x = SUCC(m\<^sub>i) (succ j) x"
    Variants_\<open>typ\<close>_\<open>i\<close>_lim :  "u : Limit \<Longrightarrow> Variants_\<open>typ\<close> i u x = LIM(m\<^sub>i) u x"
*)
fun create_variants_op typ ms ctxt =
  let 
    val cols = get_cols ctxt typ ms 
    val ords = ordinal_list typ (length cols - 1)
    val ords_cols = (ords ~~ cols)
    val vtrm = mk_variants typ (ords_cols)
    val n_ords_cols = (0 upto (length cols - 1) ~~ ords_cols)
    val vname = "Variants_" ^ last_field (fst (Term.dest_Type typ))
    val ((trm, (_,thm)), lthy) = make_defn_all vname vtrm NoSyn ctxt
    fun add_rule (t,lthy) = mk_variants_case_rule typ (vname, thm, trm) (t,lthy)
    val lthy' = List.foldl add_rule lthy n_ords_cols
    fun get_vcase_thm n lthy = Global_Theory.get_thm (get_thy lthy) (vname ^ "_" ^ Int.toString n)
    val trm' = mk_variants_const typ
    val lthy'_zero = List.foldl (fn p as ((n,_), ctxt) => 
      mk_variants_zero_rule typ (vname, get_vcase_thm n ctxt, trm') p) lthy' n_ords_cols
    val lthy'_succ = List.foldl (fn ((n,(ord,(_,s,_))), ctxt) => 
      mk_variants_succ_rule typ (vname, get_vcase_thm n ctxt, trm') (n,ord) s ctxt) lthy'_zero n_ords_cols
    val lthy'_lim = List.foldl (fn ((n,(ord,(_,_,l))), ctxt) => 
      mk_variants_lim_rule typ (vname, get_vcase_thm n ctxt, trm') (n,ord) l ctxt) lthy'_succ n_ords_cols
  in lthy'_lim end   