theory remove_syntax
imports "$ISABELLE_HOME/src/HOL/ZFC_in_HOL/ZFC_Typeclasses" 
begin

(*Don't actually need to remove any of these..
  Consider using & for intersection types?*)
no_notation (ASCII)
  Not  ("~ _" [40] 40) and
  conj  (infixr "&" 35) and
  disj  (infixr "|" 30) and
  implies  (infixr "-->" 25) and
  not_equal  (infix "~=" 50)
no_notation FuncSet.funcset (infixr "\<rightarrow>" 60)

no_translations
  "\<Pi> x\<in>A. B" \<rightleftharpoons> "CONST Pi A (\<lambda>x. B)"
  "\<lambda>x\<in>A. f" \<rightleftharpoons> "CONST restrict (\<lambda>x. f) A"
no_syntax
  "_Pi" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"  ("(3\<Pi> _\<in>_./ _)"   10)
  "_lam" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_\<in>_./ _)" [0,0,3] 3)
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
no_notation (ASCII)
  Set.member  ("'(:')") and
  Set.member  ("(_/ : _)" [51, 51] 50) and
  Set.not_member  ("'(~:')") and
  Set.not_member  ("(_/ ~: _)" [51, 51] 50) and
  less_eq  ("'(<=')") and
  less_eq  ("(_/ <= _)" [51, 51] 50) and
  union (infixl "Un" 65) and
  inter (infixl "Int" 70)

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
  "\<Inter>x\<in>A. f" \<rightleftharpoons> "CONST Inter (Set.image (\<lambda>x. f) A)"
  "\<Union>x\<in>A. f" \<rightleftharpoons> "CONST Union (Set.image (\<lambda>x. f) A)"
  "\<Union>i<n. A" \<rightleftharpoons> "\<Union>i\<in>{..<n}. A"
no_syntax
  "_INTER"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b set"  ("(3\<Inter>_\<in>_./ _)" [0, 0, 10] 10)
  "_UNION"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b set"  ("(3\<Union>_\<in>_./ _)" [0, 0, 10] 10)
  "_UNION_less" :: "'a => 'a => 'b set => 'b set"       ("(3\<Union>_<_./ _)" [0, 0, 10] 10)


no_notation Product_Type.Times (infixr "\<times>" 80)
no_translations
  "<x, y, z>"    \<rightleftharpoons> "<x, <y, z>>"
  "<x, y>"       \<rightleftharpoons> "CONST vpair x y"
  "<x, y, z>"    \<rightleftharpoons> "<x, <y, z>>"
  "\<lambda><x,y,zs>. b" \<rightleftharpoons> "CONST vsplit(\<lambda>x <y,zs>. b)"
  "\<lambda><x,y>. b"    \<rightleftharpoons> "CONST vsplit(\<lambda>x y. b)"
no_syntax (ASCII)
  "_Tuple"    :: "[V, Vs] \<Rightarrow> V"              ("<(_,/ _)>")
  "_hpattern" :: "[pttrn, patterns] \<Rightarrow> pttrn"   ("<_,/ _>")
no_syntax
  ""          :: "V \<Rightarrow> Vs"                    ("_")
  "_Enum"     :: "[V, Vs] \<Rightarrow> Vs"             ("_,/ _")
  "_Tuple"    :: "[V, Vs] \<Rightarrow> V"              ("\<langle>(_,/ _)\<rangle>")
  "_hpattern" :: "[pttrn, patterns] \<Rightarrow> pttrn"   ("\<langle>_,/ _\<rangle>")

(*Switch to using setminus character*)
no_notation 
  Groups.minus (infixl "-" 65) and (*for set difference - perhaps use a different symbol?*)
  Groups.zero ("0") and (*for the ordinal zero*)
  Groups.times (infixl "*" 70) (*for product soft-types*)

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
term \<open>x <o y\<close>
no_notation ordLess2 (infix "<o" 50)

end