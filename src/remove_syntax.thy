theory remove_syntax
imports Main begin
(*Comments for theories*)

(*Hiding syntax and translations for HOL-set-bounded quantification*)
no_translations
  "\<forall>x\<in>A. P" \<rightleftharpoons> "CONST Ball A (\<lambda>x. P)"
  "\<exists>x\<in>A. P" \<rightleftharpoons> "CONST Bex A (\<lambda>x. P)"
no_syntax
  "_Ball"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"  ("(3\<forall>(_/\<in>_)./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"   ("(3\<exists>(_/\<in>_)./ _)" [0, 0, 10] 10)

(*Hiding syntax for HOL set comprehension notation*)
no_translations
  "{x. P}" \<rightleftharpoons> "CONST Collect (\<lambda>x. P)"
no_syntax
  "_Coll" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a set"    ("(1{_./ _})")

no_translations
  "{x, xs}" \<rightleftharpoons> "CONST insert x {xs}"
  "{x}" \<rightleftharpoons> "CONST insert x {}"
no_syntax
  "_Finset" :: "args \<Rightarrow> 'a set"    ("{(_)}")

no_translations
  "\<Inter>x\<in>A. f" \<rightleftharpoons> "CONST Inter ((\<lambda>x. f) ` A)"
  "\<Union>x\<in>A. f" \<rightleftharpoons> "CONST Union ((\<lambda>x. f) ` A)"
  "\<Union>i<n. A" \<rightleftharpoons> "\<Union>i\<in>{..<n}. A"
no_syntax
  "_INTER"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b set"  ("(3\<Inter>_\<in>_./ _)" [0, 0, 10] 10)
  "_UNION"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b set"  ("(3\<Union>_\<in>_./ _)" [0, 0, 10] 10)
  "_UNION_less" :: "'a => 'a => 'b set => 'b set"       ("(3\<Union>_<_./ _)" [0, 0, 10] 10)

(*Hiding HOL set theory notation*)
no_notation Set.member ("'(\<in>')") and 
            Set.member ("(_/ \<in> _)" [51, 51] 50) and
            Set.not_member  ("'(\<notin>')") and
            Set.not_member  (infixl \<open>\<notin>\<close> 50) and
            Set.not_member  ("(_/ \<notin> _)" [51, 51] 50) and
            subset_eq  ("'(\<subseteq>')") and
            subset_eq  ("(_/ \<subseteq> _)" [51, 51] 50) and
            Union ("\<Union>") and Inter ("\<Inter>") and
            union (infixl "\<union>" 65) and inter (infixl "\<inter>" 70) and
            image (infixr "`" 90)





no_notation Product_Type.Times (infixr "\<times>" 80)



(*Switch to using setminus character*)
no_notation 
  Groups.minus (infixl "-" 65) and 
  Groups.zero ("0") and 
  Groups.one_class.one ("1") and
  Groups.times (infixl "*" 70)
(*Removing HOL ASCII notation for logical connectives.
  Currently, we only do this to warnings about parsing
  set comprehensions: { _ | _ }*)
no_notation (ASCII)
  Not  ("~ _" [40] 40) and
  conj  (infixr "&" 35) and
  disj  (infixr "|" 30) and
  implies  (infixr "-->" 25) and
  not_equal  (infix "~=" 50)

(*Removing syntax from Orderings.thy*)
no_translations
  "\<forall>x<y. P" \<rightharpoonup> "\<forall>x. x < y \<longrightarrow> P"
  "\<exists>x<y. P" \<rightharpoonup> "\<exists>x. x < y \<and> P"
no_syntax
  "_All_less" :: "[idt, 'a, bool] => bool" ("(3\<forall>_<_./ _)"  [0, 0, 10] 10)
  "_Ex_less"  :: "[idt, 'a, bool] => bool" ("(3\<exists>_<_./ _)"  [0, 0, 10] 10)
no_notation 
  less_eq  ("'(\<le>')") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50) and
  less  ("'(<')") and
  less  ("(_/ < _)"  [51, 51] 50)
no_notation
  Orderings.ord_class.greater (\<open><\<close> 10)



no_notation (ASCII)
  Set.member  ("'(:')") and
  Set.member  ("(_/ : _)" [51, 51] 50) and
  Set.not_member  ("'(~:')") and
  Set.not_member  ("(_/ ~: _)" [51, 51] 50) and
  less_eq  ("'(<=')") and
  less_eq  ("(_/ <= _)" [51, 51] 50) and
  union (infixl "Un" 65) and
  inter (infixl "Int" 70)


(*Removing list syntax so that we can have f[x] := image(f,x) 
  Use backquote, Z language unicode*)
no_translations
  "[x, xs]" == "x#[xs]"
  "[x]" == "x#[]"
no_syntax
  "_list" :: "args => 'a list" ("[(_)]")

(*Hide HOL constant \<open>set\<close> so we can use it as a tag in model building*)
hide_const set
hide_const Union Pow Inf 
hide_const Nat Pair

(*Hide HOL constant \<open>dom\<close> so we can use it in Function/Relation locales*)
hide_const dom



end