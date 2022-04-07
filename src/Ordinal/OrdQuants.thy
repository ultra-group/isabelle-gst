theory OrdQuants 
  imports Ordinal
begin

section \<open>Restricted quantification on the ordinal part of the < relation\<close>

syntax
  "_oall" :: "[pttrn, 'a, bool] \<Rightarrow> bool"  (\<open>(3\<forall>_<_./ _)\<close> 10)
  "_oex"  :: "[pttrn, 'a, bool] \<Rightarrow> bool"  (\<open>(3\<exists>_<_./ _)\<close> 10)
translations
  "\<forall>i<j. P" \<rightharpoonup> "\<forall>i:(CONST Ord). i < j \<longrightarrow> P"
  "\<exists>i<j. P" \<rightharpoonup> "\<exists>i:(CONST Ord). i < j \<and> P"


context Ordinal begin

lemma oallI [intro!] : 
  "(\<And>i. i : Ord \<Longrightarrow> i < j \<Longrightarrow> Q i) \<Longrightarrow> \<forall>i < j. Q i"
   by auto

lemma tallE [elim!]: 
  assumes "\<forall>i < j. Q i"
  obtains "\<And>i. (i : Ord \<Longrightarrow> i < j \<Longrightarrow> Q i)"
  using assms by auto

lemma oallD [elim]: 
  "\<lbrakk> \<forall>i < j. Q i ; i : Ord; i < j \<rbrakk> \<Longrightarrow> Q i"
  by auto

lemma oexI [intro] : 
  "\<lbrakk> i : Ord ; i < j ; Q i \<rbrakk> \<Longrightarrow> \<exists>i < j. Q i"
  by auto

lemma oexE [elim!] : 
  assumes "\<exists>i < j. Q i" 
  obtains i where "i : Ord" "i < j" "Q i"
  using assms by auto
end
end