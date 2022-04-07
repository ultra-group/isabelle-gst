theory mSet
  imports GZF_Model_Base
begin

context GZF_Model begin
text \<open>Recall that mSet is defined as the intersection
      of M and pairs with 'set' on the left.\<close>
thm mSet_def

lemma mset_m : 
  "x : mSet \<Longrightarrow> x : M" 
  unfolding mSet_def by (unfold_typs)

lemma mset_tag : "x : mSet \<Longrightarrow> x :\<^enum> set"
  unfolding mSet_def by (unfold_typs)

lemmas mset_snd_eq' = snd_eq[OF tag_set_pair[OF set_tag]]
lemmas mset_pair = mtagD(1)[OF mset_m]
lemmas mset_snd_eq = snd_eq[OF mset_pair]

lemma msetI: "<set,x'> : M \<Longrightarrow> <set,x'> : mSet"
  unfolding mSet_def using partI[OF _ m_pair] 
  by (unfold_typs)

lemma mset_pair_set : 
  "<set,x'> : M \<Longrightarrow> x' : Set"
  using mtagD_pair(3) alpha_set by auto

lemma mset_set : 
  "<set,x'> : mSet \<Longrightarrow> x' : Set"
  using mset_pair_set[OF mset_m] by auto

lemma msetE : 
  assumes x:"x : mSet"
  obtains x' where "x = <set,x'>" "x' : Set"
  by (rule partE[OF mset_tag[OF x]], 
      use mset_pair_set[OF mset_m] x in auto)

lemma mset_snd_set : 
  "x : mSet \<Longrightarrow> snd x : Set"
  using mset_pair_set[OF mset_m] mset_snd_eq'
  by (auto elim: msetE)

lemma snd_replfun : 
  assumes x' : "x' : SetOf mSet" 
    shows "snd : x' \<leadsto> Set"
proof (rule mem_funI)
  fix y assume "y \<in> x'" 
  hence y:"y : mSet" using setof_mem[OF x'] by auto
  then obtain y' where "y = <set, y'>" "y' : Set" 
    using msetE by auto
  thus "snd y : Set" 
    using set_setmem mset_snd_eq' by auto
qed

lemma not_excluded_mset :
  assumes x : "x : mSet"
    shows "\<not> Excluded set x"
  by (rule msetE[OF x], metis excluded_set_1)

lemma mset_smem_subtyp :"mSet << SetMem"
proof (rule subtypI) 
  fix x assume "x : mSet"
  then obtain x' where x':"x = <set, x'>" "x' : Set"
    by (auto elim: msetE)
  hence "set : PairMem" "x' : PairMem"
    using tag_pmem[OF set_tag] smem_pmem[OF set_setmem] by auto
  thus "x : SetMem" 
    unfolding x' by (rule pair_setmem)
qed
   
lemmas mset_smem = subtypE[OF mset_smem_subtyp]

lemma tex_mtex_mset :
  "(\<exists>x : mSet. P x) = (m\<exists> x : mSet. P x)"
  unfolding mtex_def mex_def tex_def 
  using mset_m by auto


end
end
