(*Various functions for interacting with Isar*)

(*Alias for getting background theory of context*)
fun get_thy ctxt = Proof_Context.theory_of ctxt
fun get_ctxt thy = Proof_Context.init_global thy

(*Defines \<open>name \<equiv> trm\<close> in lthy*)
fun make_defn_trm name trm mx lthy = let
  val binding_const = (Binding.name name, mx)
  val binding_fact = (Binding.name (name ^ "_def"), [])
  val arg = (binding_const, (binding_fact, trm))
  val ((trm, (_ , _)), lthy') = Local_Theory.define arg lthy
  in (trm,lthy') end

fun make_defn name trm mx = snd o make_defn_trm name trm mx
 
fun make_defns_trms lthy = 
  List.foldl (fn ((iden, trm, mx), (ts,lthy)) => 
      let val (trm, lthy') = make_defn_trm iden trm mx lthy
      in (trm :: ts, lthy') end) ([],lthy)

(*Defines a list of triples of (name,trm,mx)*)
val make_defns = List.foldl (fn ((iden, trm, mx), lthy) => make_defn iden trm mx lthy)

(*Various aliases for creating values of type mixfix*)
val nsyn = Mixfix.NoSyn 
fun mk_mixfix (str, ns, m) = Mixfix.Mixfix (Input.string str, ns, m, Position.no_range)
fun mk_sym (str) = mk_mixfix (str, [], 1000)
fun mk_infix (str, pr) = Mixfix.Infixl (Input.string str, pr, Position.no_range)
fun mk_infixl (str, pr) = Mixfix.Infixl (Input.string str, pr, Position.no_range)
fun mk_infixr (str, pr) = Mixfix.Infixr (Input.string str, pr, Position.no_range)
fun mk_binder (str, pr1, pr2) = Mixfix.Binder (Input.string str, pr1, pr2, Position.no_range)