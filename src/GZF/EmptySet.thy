theory EmptySet
  imports SetComprehension
begin           

context GZF begin

subsection \<open>Unique existence of the empty set\<close>

subsection\<open>Rules for the empty set\<close>

lemmas emp_set = Emp_typ

(*Taken from ZF/ZF_Base*)
lemma not_mem_empty : "a \<notin> \<emptyset>"
  by (simp add: emp)
(*WAS: apply (cut_tac foundation)
       apply (best dest: equalityD2)
       done *)

lemmas emptyE [elim] = not_mem_empty [THEN notE]

lemma emp_setof : "\<emptyset> : SetOf P"
  using setofI[OF emp_set emptyE] .

(*Added assumption: \<open>A : Set\<close>*)
lemma empty_subsetI [simp]: 
  assumes "x : Set" 
    shows "\<emptyset> \<subseteq> x"
  using assms by auto
(*WAS: by blast*)

(*Added assumption: \<open>A : Set\<close>*)
lemma equals0I: 
  assumes "x : Set" 
    shows "[|!!y. y\<in>x ==> False |] ==> x = \<emptyset>"
  by (rule equality_iffI[OF \<open>x : Set\<close> emp_set], 
      use not_mem_empty in auto)
(*WAS: by blast*)

lemma equals0D [dest]: "x = \<emptyset> \<Longrightarrow> a \<notin> x"
  by blast

declare sym [THEN equals0D, dest]

lemma not_emptyI: "a \<in> x ==> x \<noteq> \<emptyset>"
  by blast

lemma not_emptyD: 
  assumes "x : Set" 
    shows "x \<noteq> \<emptyset> \<Longrightarrow> \<exists>a. a \<in> x"
proof (rule ccontr)
  assume "x \<noteq> \<emptyset>" "\<not> (\<exists>a. a \<in> x)"
  hence "\<forall>a. a \<notin> x" by auto
  hence "x = \<emptyset>" using equals0I[OF \<open>x : Set\<close>] by auto
  thus "False" using \<open>x \<noteq> \<emptyset>\<close> by simp
qed

(*Added assumption: \<open>A : Set\<close>*)
lemma not_emptyE: 
  assumes "A : Set" 
    shows "[| A \<noteq> \<emptyset>;  !!x. x\<in>A ==> R |] ==> R"
  using not_emptyD[OF assms] 
  by auto

lemma set_disj : 
  assumes "x : Set"
    shows "x = \<emptyset> \<or> (\<exists>a. a \<in> x)"
  using not_emptyE[OF assms] 
  by auto
(*WAS: by blast*)

lemma union_emp : 
  assumes "x : SetOf Set" 
    shows "a \<in> \<Union> x \<Longrightarrow> x \<noteq> \<emptyset>"
  using assms unionE not_emptyI 
  by auto

lemma pow_bottom : 
  assumes "x : Set" 
    shows "\<emptyset> \<in> \<P> x"
  by (rule powI[OF emp_set \<open>x : Set\<close> empty_subsetI[OF \<open>x : Set\<close>]])

subsection \<open>Example: Soft-typing on Power Set & Empty Set\<close>
(*EXAMPLE: soft-typing on power set and empty set, 
    todo: create 'examples' directory and move there.*)

(*The soft-types of \<P> and \<emptyset> are given in the specification of the Set feature.
  The funE rule is defined in Soft_Types.thy*)
thm Pow_typ emp_set funE
(*Show \<P> \<emptyset> : SetOf Set by instantiating the funE rule with the types of \<P> and \<emptyset>*)
lemmas pow_emp_typ = funE[OF Pow_typ emp_set]

thm setof_set_subtyp subtypE
(*To show \<P> \<emptyset> : Set*)
lemmas pow_emp_typ_set = subtypE[OF setof_set_subtyp pow_emp_typ]

(*New soft-typings can be derived for the same operator*)
lemma Pow_typ_set : "Pow : Set \<rightarrow> Set"
  by (rule funI[OF subtypE[OF setof_set_subtyp funE[OF Pow_typ]]])

(*Soft typing rules can be derived from instances of typing rules: *)
lemmas pow_setof = funE[OF Pow_typ]
lemmas pow_set   = funE[OF Pow_typ_set]

(*We can then derive soft typings without explicitly mentioning fundamental soft-typing rules*)
thm pow_set[OF pow_set[OF emp_set]]
(*This is usually much smaller and less complex than always using the fundamental rules*)
thm funE[OF Pow_typ_set funE[OF Pow_typ_set emp_set]]

end 
end
