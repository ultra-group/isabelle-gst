theory FunctionSpace
  imports Functions "../OPair/CartProd"
begin
class FunSpace = Function + CartProd
context FunSpace
begin

definition fun_from_opair_set :: "'a \<Rightarrow> 'a"
  where "fun_from_opair_set x \<equiv> mkfun {\<tau> p | p \<in> x} (\<lambda>a b. <a,b> \<in> x)"

definition partial_fun_space :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr \<open>\<Zpfun>''''\<close> 70)
  where "x \<Zpfun>'' y \<equiv> {g | \<exists>f \<in> \<P>(x \<times> y). g = fun_from_opair_set f \<and> g : x \<Zpfun> y}"

(* definition total_fun_space ::  "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr \<open>\<leadsto>''''\<close> 70)
  where "x \<leadsto>'' y \<equiv> {g | \<exists>f \<in> \<P>(x \<times> y). g = fun_from_opair_set f \<and> g : x \<leadsto> y}"
 *)
(* lemma total_fun_space_typ :
  "(\<leadsto>'') : (\<Pi> x : Set. \<Pi> y : Set. SetOf (x \<leadsto> y))"
proof (rule depfunI, rule depfunI, rule setofI)
  fix x y
  assume x : "x : Set"
     and y : "y : Set"
  show "x \<leadsto>'' y : Set"
    unfolding total_fun_space_def
    using repl_set[OF pow_set[OF cprod_set[OF x y]]]
    sorry
  fix b
  assume "b \<in> x \<leadsto>'' y"
  then
  show "b : x \<leadsto> y"
    unfolding total_fun_space_def
    using replaceE[OF pow_set[OF cprod_set[OF x y]]]
    sorry
qed
 *)
(* lemmas total_fun_space_setof = depfunE[OF depfunE[OF total_fun_space_typ]] *)

end
end