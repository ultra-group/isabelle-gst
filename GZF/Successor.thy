theory Successor
  imports SetCombinators 
begin

context GZF begin

subsection \<open>Set Concatenation\<close>

definition cons :: "['a, 'a] \<Rightarrow> 'a"
  where "cons b x \<equiv> {b} \<union> x"

lemma cons_typ : "cons : SetMem \<rightarrow> Set \<rightarrow> Set"  
  unfolding cons_def 
  by (rule funI[OF funI], rule un_set, rule sng_set)

lemmas cons_set = funE[OF funE[OF cons_typ]]

lemma cons_iff :
  assumes b:"b : SetMem" and x:"x : Set"
    shows "c \<in> cons b x \<longleftrightarrow> (c = b \<or> c \<in> x)"
  unfolding cons_def un_iff[OF sng_set[OF b] x] sng_iff[OF b]
  by (rule)

lemma consI1 : 
  assumes b:"b : SetMem" and x:"x : Set"
    shows "b \<in> cons b x"
  using cons_iff[OF b x] by simp

lemma consI2 : 
  assumes b:"b : SetMem" and x:"x : Set"
     and c:"c \<in> x"
   shows "c \<in> cons b x"
  using cons_iff[OF b x] c by simp

(*Classical introduction rule*)
lemma consCI : 
  assumes b:"b : SetMem" and x:"x : Set"
     and c:"c \<notin> x \<Longrightarrow> c = b"
   shows "c \<in> cons b x"
  using cons_iff[OF b x] c by auto

lemma consE : 
  assumes b:"b : SetMem" and x:"x : Set"
      and c:"c \<in> cons b x"
  obtains "c = b" | "c \<in> x"
  using cons_iff[OF b x] c by auto

(*Stronger version of \<open>consE\<close>*)
lemma consE' : 
  assumes b:"b : SetMem" and x:"x : Set"
      and c:"c \<in> cons b x"
  obtains "c = b" | "c \<in> x" "c \<noteq> b"
  using cons_iff[OF b x] c by auto


lemma cons_not_emp : 
  assumes b:"b : SetMem" and x:"x : Set"
    shows "cons b x \<noteq> \<emptyset>"
  by (rule not_emptyI[OF consI1[OF b x]])


subsection \<open>Unique existence of von Neumann successor operation\<close>

lemmas succ_set = funE[OF Succ_typ]


subsection \<open>Rules for von Neumann successor operation\<close>

lemma vsucc_iff :
  assumes x:"x : Set"
    shows "y \<in> Succ x \<longleftrightarrow> (y \<in> x \<or> y = x)"
  using succ x  
  by auto

lemma vsuccI1 : 
  assumes "x : Set"
    shows "y \<in> x \<Longrightarrow> y \<in> Succ x"
  using vsucc_iff[OF assms] by simp

lemma vsuccI2 : 
  assumes "x : Set"
    shows "x \<in> Succ x"
  using vsucc_iff[OF assms] by simp

lemma vsuccE : 
  assumes "x : Set" 
    shows "y \<in> Succ x \<Longrightarrow> (y \<in> x \<or> y = x)"
  using vsucc_iff[OF assms] by simp

end
end