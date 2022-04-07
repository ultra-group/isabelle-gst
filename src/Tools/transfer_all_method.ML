 open Transfer;

  val free = Args.context -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
  error ("Bad free variable: " ^ Syntax.string_of_term ctxt t))

  val fixing = Scan.optional (Scan.lift (Args.$$$ "fixing" -- Args.colon)
  |-- Scan.repeat free) []
  
  fun transfer_all_method equiv = fixing >> (fn vs => fn ctxt =>
    SIMPLE_METHOD (ALLGOALS (gen_frees_tac vs ctxt THEN' transfer_tac equiv ctxt)))

  val _ =
  Theory.setup (Method.setup \<^binding>\<open>transfer_all\<close> (transfer_all_method true)
       "applies transfer tactic to all subgoals")