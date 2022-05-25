(*-------- Generating 'otherwise' axioms --------*)

(*Create a disjunction from a list of terms*)
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
fun get_default_param cla = Free (last_field cla ^ "_default", @{typ 'a})

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
fun gen_default_axs thy cla =
  let
    val typings = get_feature_funtypings thy cla
    val default = get_default_param cla
    val default_prop = (HOLogic.mk_Trueprop o gen_default_form default o HOLogic.dest_Trueprop)
  in 
    map (fn (iden, trm) => (Binding.name_of iden ^ "_default", default_prop trm)) typings 
  end

(*Generates an equality for a defualt value*)
fun default_eq_ax default t = 
  HOLogic.mk_Trueprop (HOLogic.mk_eq (default, t))

(*Generates default equality axioms from a list of pairs of classes and terms*)
fun gen_default_eqs xs = 
  map (fn (cla, t) => (last_field cla ^ "_default_eq", default_eq_ax (get_default_param cla) t)) xs


(*-------- Generating Identification & Disjointness Axioms --------*)

(*Very naive algorithm for generating pairs of all elements of a list,
   with 'duplicates' removed*)
fun pair_eq p (a,b) = (p = (a,b)) orelse (p = (b,a)) 
fun isolate [] = []
  | isolate (x :: xs) = x :: isolate (filter_out (pair_eq x) xs)
fun cartsq xs = map_product (fn a => fn b => (a,b)) xs xs
fun gen_pairs xs = (filter_out (fn (a,b) => a = b) o isolate o cartsq) xs

(*Generates the identification axiom from a list of predicates*)
fun iden_ax trms = 
  HOLogic.mk_Trueprop (HOLogic.mk_all ("x", @{typ 'a}, list_disj 
    (map (fn t => mk_styping @{term "x :: 'a"} t) trms)))

(*Generates a disjointness axiom for two predicates*)
fun disjoint_ax (p1,p2) = 
  let
    val iden = last_field o fst o dest_Free
  in
    (iden p1 ^ "_" ^ iden p2 ^ "_disjoint",
      (HOLogic.mk_Trueprop (HOLogic.mk_eq (mk_int_ty p1 p2, \<^term>\<open>\<bottom>\<close>))))
  end
(*Generates disjointness axioms for a list of predicates*)
fun all_disjoint_axs trms = map disjoint_ax (gen_pairs trms)


(*-------- Combining Features ---------*)

(*Creates a GST typeclass from a list of pairs of classes, and default terms (free vars of type 'a), 
  and a list of 'surface' predicates (free vars of type 'a \<Rightarrow> bool).
  Default terms should be free variables that are parameters of any of the chosen classes*)
fun combine_features name xs strms lthy = 
  let
    val imps = map fst xs
    val org_axs = (name ^ "_iden", iden_ax strms) :: all_disjoint_axs strms
    val default_axs = maps (gen_default_axs (get_thy lthy)) imps 
                    @ gen_default_eqs xs
  in
    mk_class name imps [] (org_axs @ default_axs) lthy
  end