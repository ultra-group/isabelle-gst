theory Test
  imports ZFC_in_HOL_Bootstrap 
    "../Ordinal/Model/OrdRec_Model" "../GZF/KPair"  
   
begin 
ML_file \<open>../ModelKit/Tools/build_model_operator.ML\<close> 

ML \<open>val GZF_OPair_ts = 
   [\<^term>\<open>is_kpair :: V \<Rightarrow> bool\<close>, \<^term>\<open>kpair :: V \<Rightarrow> V \<Rightarrow> V\<close>,
    \<^term>\<open>SetMem :: V \<Rightarrow> bool\<close>, \<^term>\<open>GZF_default :: V\<close>]\<close>

setup \<open>mk_instantiation \<^type_name>\<open>V\<close> \<^class>\<open>OPair\<close> GZF_OPair_ts @{thm GZF_OPair}\<close>

instance V :: Function sorry
instance V :: CartProd sorry
instance V :: Tagging ..
 
(*cols should be a list of (i, t) where i is a term denoting an ordinal,
  and is a term of type D \<Rightarrow> bool *)
(*all of the stuff below needs a major refactor*)
ML \<open>fun mk_excluded typ cols =
  let
    val (i,b) = (Bound 1, Bound 0) 
    val ex_seq = map (fn (ord, t) => (ord, betapply (t,b))) cols
    val body = mk_ord_seq \<^typ>\<open>bool\<close> i \<^term>\<open>True\<close> ex_seq
    in Term.abs ("i", typ) (Term.abs ("b", typ) body) end\<close>

ML \<open>fun mk_slot_typs typ seq =
  let
    val any = Const ("Soft_Types.Any", typ --> \<^typ>\<open>bool\<close>)
    val body = mk_ord_seq (typ --> \<^typ>\<open>bool\<close>) (Bound 0) any seq
  in (Term.abs ("i", typ) body) end\<close>

ML \<open>fun excluded_rule typ (exname, exdef_thm, ex_trm) (n, otrm, pred) lthy = 
  let 
    val b = Free ("b",typ)
    val iff = HOLogic.mk_Trueprop ((\<^term>\<open>iff\<close> $  
         (betapplys (ex_trm, [otrm, b]))) $ betapply (pred, b))
    val thm_name = exname ^ "_" ^ Int.toString n
    val state = Proof.theorem NONE (after_qed (Binding.name thm_name, [])) 
                [[(iff,[])]] lthy
    val state' = Proof.unfolding [[([exdef_thm, if_thm n], [])]] state
  in
    Proof.global_default_proof state'
  end\<close>

ML \<open>fun slottype_rule (iden, def_thm, trm) (n, otrm, styp) lthy = 
  let 
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (betapply (trm, otrm), styp))
    val thm_name = iden ^ "_" ^ Int.toString n
    val state = Proof.theorem NONE (after_qed (Binding.name thm_name, [])) 
                [[(eq,[])]] lthy
    val state' = Proof.unfolding [[([def_thm, if_thm n], [])]] state
  in
    Proof.global_default_proof state'
  end\<close>

ML \<open>fun create_excluded_op typ ts lthy = 
  let
    val ex_name = "Excluded_" ^ last_field (fst (Term.dest_Type typ))
    val ords = ordinal_list typ (length ts - 1)
    val ex_trm = mk_excluded typ (ords ~~ ts)
    val ((trm, (_,thm)), lthy) = make_defn_all ex_name ex_trm NoSyn lthy
    val ints_ords_preds = (0 upto (length ords - 1) ~~ (ords ~~ ts))
    fun add_rule ((n,(i,p)),lthy) = excluded_rule typ (ex_name, thm, trm) (n,i,p) lthy
  in
    List.foldl add_rule lthy ints_ords_preds
  end\<close>

ML \<open>fun create_slot_typ_op typ styps lthy = 
  let
    val iden = "\<alpha>_" ^ last_field (fst (Term.dest_Type typ))
    val ords = ordinal_list typ (length styps - 1)
    val ex_trm = mk_slot_typs typ (ords ~~ styps)
    val ((trm, (_,thm)), lthy) = make_defn_all iden ex_trm NoSyn lthy
    val ints_ords_preds = (0 upto (length ords - 1) ~~ (ords ~~ styps))
    fun add_rule ((n,(i,p)),lthy) = slottype_rule (iden, thm, trm) (n,i,p) lthy
  in
    List.foldl add_rule lthy ints_ords_preds
  end\<close>

ML \<open>fun get_tags ms = (map (get_mcomp_tag) 
                o filter (fn mcomp {variant,...} => Option.isSome variant))
                  (resolve_mdeps ms)\<close>

ML \<open>fun defn_tags typ ms lthy = 
    let
      val tag_idens = get_tags ms
      val ords = ordinal_list typ (length tag_idens - 1)
      val defs = map (fn (iden,trm) => 
        (iden ^ "_" ^ last_field (fst (Term.dest_Type typ)),trm, NoSyn)) (tag_idens ~~ ords)
    in make_defns lthy defs end\<close>

ML \<open>
fun model_implementation typ ms ex_preds styps =
    (defn_tags typ ms)
  o (create_variants_op typ ms) 
  o (create_excluded_op typ ex_preds)
  o (create_slot_typ_op typ styps)\<close>

instantiation V :: ModelBase' begin
  (*Call Variants: TierImplementation, change Ordinal_default to \<emptyset> *)
  local_setup \<open>model_implementation \<^typ>\<open>V\<close> [ordrec_model] 
    [\<^term>\<open>\<lambda>x :: V. False\<close>, \<^term>\<open>\<lambda>x :: V. False\<close>]
    [\<^term>\<open>Set :: V \<Rightarrow> bool\<close>, \<^term>\<open>Ord :: V \<Rightarrow> bool\<close>]\<close>

  thm Variants_V_def Excluded_V_def set_V_def ord_V_def
  thm Variants_V_0 Variants_V_0_zero Variants_V_0_succ Variants_V_0_lim
  thm Variants_V_1 Variants_V_1_zero Variants_V_1_succ Variants_V_1_lim 
  thm Excluded_V_0 Excluded_V_1
  
  instance 
  proof (intro_classes)
    show "Variants : (\<Pi> i::V:Tag. nonLimit \<rightarrow> Set \<rightarrow> SetOf (\<alpha> i))"
    proof (rule depfunI, rule funI, rule funI)
      fix i :: V and j :: V and x :: V 
      assume "i : Tag" "j : nonLimit" "x : Set"
      hence "i : Ordinal_class.Ord" "i < \<omega>" 
        using tagD by auto
        
      have "Variants 0 j x : SetOf Set"  
        unfolding Variants_V_0
      proof (rule case_ordE[OF nonlimit_ord[OF \<open>j : nonLimit\<close>]])
      show "Variants i j x : SetOf (\<alpha> i)"
     
 end
instance V :: GZF_Model sorry
instance V :: Ordinal_Model sorry
instance V :: OrdRec_Model sorry





end