(*A feature is a represented as an ML record, with the following definition: *)
datatype gst_feature = Feature of 
  { cla : class, 
    deps : gst_feature list,
    logo : term,
    cargo : term,
    default_param : term }
 (* child_pred : string option *) 

(*TODO: move to class_tools.ML*)
fun replace_tfree_sort sort = 
  map_types (map_type_tfree (fn (typ_iden, _) => TFree (typ_iden, sort)))

fun prepare_trm sort = replace_tfree_sort sort o subst_TVars [(("'a",0), \<^typ>\<open>'a\<close>)] 
                    

fun feature_cla (Feature {cla,...}) = cla
fun feature_deps (Feature {deps,...}) = deps
fun feature_logo sort (Feature {logo,...}) = 
  replace_tfree_sort sort logo
fun feature_cargo sort (Feature {cargo,...}) = 
  replace_tfree_sort sort cargo
fun feature_default sort (Feature {default_param,...}) = 
  replace_tfree_sort sort default_param

(*------ Feature Configurations ------*)
type feature_config = 
  {feat : gst_feature, 
   default_val : term, 
   blacklist: (gst_feature list) }

(*-------- Generating 'otherwise' axioms --------*)

fun mk_un_typ typ (trm1,trm2) = 
  Const ("Soft_Types.union_ty",(typ --> \<^typ>\<open>bool\<close>) --> (typ --> \<^typ>\<open>bool\<close>) --> (typ --> \<^typ>\<open>bool\<close>))
  $ trm1 $ trm2

(*Create a union type from a list of terms*)
fun list_un_typ _ ([A]) = A
  | list_un_typ typ (A::As) = mk_un_typ typ (A, list_un_typ typ As)
  | list_un_typ typ [] = Const ("Soft_Types.empty_typ", typ --> \<^typ>\<open>bool\<close>)

fun list_disj ([A]) = A
  | list_disj (A::As) = HOLogic.mk_disj (A, list_disj As)
  | list_disj [] = error "list_disj: empty list!"

(*Descend into abstractions, applying HOL \<forall> quantifiers along the way*)
fun all_until_bool (Abs (x,T,P)) = 
    (HOLogic.all_const T $ Abs (x, T, all_until_bool P)) 
  | all_until_bool t = t

(*Get list of all of the axioms of a feature that have either form:
    - f : P \<rightarrow> Q, or f : (\<Pi> x : P. Q x)  *)
fun get_feature_funtypings thy cla = 
  filter (is_fun_typing o HOLogic.dest_Trueprop o snd) (get_locale_axioms thy cla)
(*Maps the string <name> to the free variable <name>_default.
  Used when constructing default axioms *)
(* fun get_default_param cla = Free (last_field cla ^ "_default", @{typ 'a}) *)

(*Translates a function soft-typing to a list of terms used in the corresponding 'default axiom'.*)
fun fun_typing_to_default_trms default i sftyp f = 
  case sftyp of
    ((Const ("Soft_Types.fun_ty",_)) $ P $ Q) => 
      let 
        val x = Var (("x",i), domain_type (fastype_of P))
        val not_xP = HOLogic.mk_not (mk_styping x P)
      in not_xP :: fun_typing_to_default_trms default (i+1) Q (f $ x) end   
  | ((Const ("Soft_Types.depfun_ty",_)) $ P $ Q) => 
      let 
        val x = Var (("x",i), domain_type (fastype_of P))
        val not_xP = HOLogic.mk_not (mk_styping x P)
      in not_xP :: fun_typing_to_default_trms default (i+1) (betapply (Q, x)) (f $ x) end   
  | _ => [HOLogic.mk_eq (f, default)]

(*Translates a function soft-typing to its corresponding otherwise axiom'*)
fun gen_default_form default sftyping =
  let 
    val (t, sftyp) = split_typings sftyping
    val phis = fun_typing_to_default_trms default 0 sftyp t
    val disj = (list_disj o rev o tl o rev) phis
    val imp = HOLogic.mk_imp (disj, List.last phis)
    val abs = Term.close_schematic_term imp
  in all_until_bool abs end

(*Generates a list of 'otherwise axioms' for a feature.*)
fun gen_default_axs lthy sort feat =
  let
    val typings = get_feature_funtypings (get_thy lthy) (feature_cla feat)
    val default = feature_default sort feat
    val default_prop = (HOLogic.mk_Trueprop o gen_default_form default o HOLogic.dest_Trueprop)
  in 
    map (fn (iden, trm) => (Binding.name_of iden ^ "_default", 
      default_prop (prepare_trm sort (interp_trm lthy (feature_cla feat) trm)))) typings 
  end

(*Generates an equality for a defualt value*)
fun default_eq_ax default t = 
  HOLogic.mk_Trueprop (HOLogic.mk_eq (default, t))

(*Generates default equality axioms from a list of pairs of features and terms*)
fun gen_default_eqs sort xs = 
  map (fn (feat, t) => 
        (last_field (feature_cla feat) ^ "_default_eq", 
         default_eq_ax (feature_default sort feat) t)) xs

(*-------- Generating cover & disjointness Axioms --------*)

(*Generates the cover axiom from a list of predicates*)
fun cover_ax sort trms = 
  let 
    val un_typ = (list_un_typ \<^typ>\<open>'a\<close> trms)
    val eq = prepare_trm sort (HOLogic.mk_eq (un_typ, \<^term>\<open>\<top>\<close>))
  in 
    ("cover_ax", HOLogic.mk_Trueprop eq)
  end


(*Very naive algorithm for generating pairs of all elements of a list,
   with 'duplicates' removed*)
fun pair_eq p (a,b) = (p = (a,b)) orelse (p = (b,a)) 
fun isolate [] = []
  | isolate (x :: xs) = x :: isolate (filter_out (pair_eq x) xs)
fun cartsq xs = map_product (fn a => fn b => (a,b)) xs xs
fun gen_pairs xs = (filter_out (fn (a,b) => a = b) o isolate o cartsq) xs


(*Generates a disjointness axiom for two predicates*)
fun disjoint_ax sort ((name1,p1),(name2,p2)) = 
    (name1 ^ "_" ^ name2 ^ "_disjoint", prepare_trm sort
      (HOLogic.mk_Trueprop (HOLogic.mk_eq (mk_int_ty p1 p2, \<^term>\<open>\<bottom>\<close>))))

(*Generates disjointness axioms for a list of predicates*)
fun all_disjoint_axs sort trms = map (disjoint_ax sort) (gen_pairs trms)

(*------- Cargo regulation axioms ------*)

fun mk_subtyp typ (P,Q) =
  Const ("Soft_Types.subtyp", (typ --> \<^typ>\<open>bool\<close>) --> (typ --> \<^typ>\<open>bool\<close>) --> \<^typ>\<open>bool\<close>)
  $ P $ Q

fun admit_cargo sort iden P Qs =
  let
    val un_typ = list_un_typ \<^typ>\<open>'a\<close> Qs
    val subtyp = mk_subtyp \<^typ>\<open>'a\<close> (un_typ, P)
  in ("admit_cargo_" ^ iden , prepare_trm sort (HOLogic.mk_Trueprop subtyp)) end

fun restrict_cargo sort iden P Qs =
  let
    val un_typ = list_un_typ \<^typ>\<open>'a\<close> Qs
  in 
    ("restrict_cargo_" ^ iden, prepare_trm sort 
      (HOLogic.mk_Trueprop (HOLogic.mk_eq (mk_int_ty un_typ P, \<^term>\<open>\<bottom>\<close>)))) 
  end

fun list_in x xs = exists (fn y => x = y) xs

fun cargo_axs sort feat wlist blist =
  let
    val wlist' = (filter (fn feat => not (list_in feat blist)) wlist)
    val iden = (last_field o feature_cla) feat 
    val admit = admit_cargo sort iden (feature_cargo sort feat) (map (feature_logo sort) wlist')
    val restrict = restrict_cargo sort iden (feature_cargo sort feat) (map (feature_logo sort) blist)
  in 
    [admit, restrict]
  end

(*------ Combining feature configurations ------*)

fun mk_gst name (spec : feature_config list) lthy = 
  let
    val feats = map #feat spec
    val sort = map (feature_cla) feats
    val imports = map (feature_cla) feats  
    val axioms = maps (gen_default_axs lthy sort) feats 
               @ gen_default_eqs sort
                (map (fn config => (#feat config, 
                  (replace_tfree_sort sort (#default_val config)))) spec) 
               @ [cover_ax sort (map (feature_logo sort) feats)]
               @ all_disjoint_axs sort (map ((fn f => (last_field (feature_cla f), feature_logo sort f))) feats)
               @ maps (fn config => cargo_axs sort (#feat config) feats (#blacklist config)) spec 
  in
    mk_class name imports [] axioms lthy
  end