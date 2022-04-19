
fun quant_trans @{term \<open>All :: ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>} 
    = @{term mall}
  | quant_trans @{term \<open>All :: (('a \<Rightarrow> 'a) \<Rightarrow> bool) \<Rightarrow> bool\<close>} 
    = @{term \<open>tall (M \<rightarrow> M)\<close>}
  | quant_trans @{term \<open>All :: (('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool) \<Rightarrow> bool\<close>} 
    = @{term \<open>tall (M \<rightarrow> M \<rightarrow> M)\<close>}
  | quant_trans @{term \<open>All :: (('a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a) \<Rightarrow> bool) \<Rightarrow> bool\<close>} 
    = @{term \<open>tall LimFun\<close>}
  | quant_trans @{term \<open>Ex :: ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>}
      = @{term mex}
  | quant_trans @{term \<open>Uniq :: ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>}
      = @{term muniq}
  | quant_trans @{term "tall :: (('a :: _) \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"}
      = @{term mtall}
  | quant_trans @{term "tex :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"}
      = @{term mtex}
  | quant_trans @{term "tex1 :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"}
      = @{term mtex1}
  | quant_trans @{term "tuniq :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"}
      = @{term mtuniq}
  | quant_trans c = c 

fun translate_term ctxt msig =
  map_aterms (quant_trans o msig_term_app ctxt msig)

fun gen_axiom_goals ctxt msig = 
  let 
    val axioms = map snd (get_locale_axioms (get_thy ctxt) (#feature msig))
    val conv_typing = (HOLogic.mk_Trueprop o unfold_fun_typing o HOLogic.dest_Trueprop)
    val axioms' = map (fn phi => if is_fun_typing (HOLogic.dest_Trueprop phi) then conv_typing phi else phi) axioms
  in 
    map (translate_term ctxt msig) axioms'
  end

(*Generating goals for proving respectfulness theorems for model consts*)
fun rsp_goal' i m (t,t') = 
  case fastype_of t of 
    Type ("fun",[u,_]) => 
     (case u of 
        Type ("fun", _) => 
          let
            val F = (Var (("fun1",i), u))
            val G = (Var (("fun2",i), u))
            val imp = Logic.mk_implies 
              (rsp_goal' (i+1) m (F,G),
               rsp_goal' (i+1) m (t $ F, t' $ G))         
          in 
            Logic.all_const u $ lambda F
              (Logic.all_const u $ lambda G imp)
          end  
       | _ => 
        let
         val x = Var (("x",i), u)
         val imp = Logic.mk_implies
            (rsp_goal' (i+1) m (x,x), rsp_goal' (i+1) m (t $ x, t' $ x))
        in
         Logic.all_const u $ lambda x imp
        end)
  | @{typ 'a} => 
    if t = t' 
      then HOLogic.mk_Trueprop (m $ t)
      else HOLogic.mk_Trueprop (HOLogic.mk_conj (m $ t, HOLogic.mk_eq (t, t')))
  | @{typ bool} => 
    if t = t' 
      then @{prop True} 
      else HOLogic.mk_Trueprop (HOLogic.mk_eq (t, t'))
 | _ => error "weird type!"

fun rsp_goal t = rsp_goal' 0 @{term \<open>\<lambda>x. x : M\<close>} (t,t)
 
fun simp_rsp' trm =
  if Logic.is_all trm then
    case Logic.dest_all_global trm of
      (_,@{prop True}) => @{prop True} 
    | (v, B) => Logic.all (Free v) (simp_rsp' B)
  else 
    if Logic.no_prems trm then trm else 
    case Logic.dest_implies trm of
      (_, @{prop True}) => @{prop True}  
    | (P, Q) => Logic.mk_implies (simp_rsp' P, simp_rsp' Q)

fun simp_rsp trm = 
  let val trm' = simp_rsp' trm
  in 
    if trm' = trm 
    then trm 
    else simp_rsp trm' 
  end

val gen_resp_goal = simp_rsp o rsp_goal  
fun gen_resp_goals ctxt msig = 
  filter (fn p => not (p = @{prop True})) 
    (map gen_resp_goal (msig_term_ran ctxt msig))
   
fun after_qed thm_name thms lthy =
  Local_Theory.note (thm_name, (flat thms)) lthy |> snd

structure ModelMorphResult = Proof_Data
  (type T = unit -> model_sig
   fun init _ () = error "Result")

val model_morph_result_cookie = 
  (ModelMorphResult.get, ModelMorphResult.put, "ModelMorphResult.put")

fun src_to_morph src ctxt = let
    val (text, _) = Input.source_content src
    val model = Code_Runtime.value ctxt model_morph_result_cookie ("", text)
  in model end;

fun translate_axioms_cmd (thm_name,src) ctxt = 
  let
    val morph = src_to_morph src ctxt 
    val goals = gen_axiom_goals ctxt morph 
  in 
     Proof.refine_singleton (Method.Basic (fn _ => Method.succeed)) 
      ((Proof.theorem NONE (after_qed thm_name) (map (fn t => [(t,[])]) goals) ctxt)) 
  end

fun resp_thms_cmd (thm_name,src) ctxt = 
  let
    val morph = src_to_morph src ctxt 
    val goals = gen_resp_goals ctxt morph 
  in 
    Proof.refine_singleton (Method.Basic (fn _ => Method.succeed)) 
      ((Proof.theorem NONE (after_qed thm_name) (map (fn t => [(t,[])]) goals) ctxt)) 
  end

val _ = Outer_Syntax.local_theory_to_proof
  @{command_keyword "translate_axioms"}
  "sets up proof of the translation of each axiom of a locale" 
  (Parse_Spec.opt_thm_name ":" -- Parse.ML_source >> translate_axioms_cmd)

val _ = Outer_Syntax.local_theory_to_proof
  @{command_keyword "resp_thms"}
  "sets up proof of the translation of each axiom of a locale" 
  (Parse_Spec.opt_thm_name ":" -- Parse.ML_source >> resp_thms_cmd)
