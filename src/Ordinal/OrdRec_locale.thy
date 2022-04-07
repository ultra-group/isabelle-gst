theory OrdRec_locale
  imports "../GZF/GZF_Base" Ordinal 
begin

context OrdRec begin


lemmas predset_set = funE[OF predset_typ]

lemma predset_iff : assumes "\<beta> : Ord" 
  shows "\<alpha> \<in> predSet \<beta> \<longleftrightarrow> \<alpha> < \<beta>"
  using predset_def assms by auto 

lemma predsetI : 
  shows "\<alpha> < \<beta> \<Longrightarrow> \<alpha> \<in> predSet \<beta>"
  using predset_iff lt_ord by auto

lemma predsetE : assumes "Ord \<beta>"
  shows "\<alpha> \<in> predSet \<beta> \<Longrightarrow> \<alpha> < \<beta>"
  using predset_iff[OF assms] by simp 
  
lemma predset_mem_ord : assumes "Ord \<beta>"
  shows "\<alpha> \<in> predSet \<beta> \<Longrightarrow> Ord \<alpha>"
  using predset_iff[OF \<open>Ord \<beta>\<close>] lt_ord1 by auto


lemma ordrec_succ : assumes "Ord b" 
  shows "OrdRec G F A (succ b) = F (succ b) (OrdRec G F A b)"
  using ordrec_succ_ax assms by auto

lemma ordrec_lim : assumes "Limit u" 
  shows "OrdRec G F A u = G u (\<lambda>\<beta>. if \<beta> < u then OrdRec G F A \<beta> else 0)"
  using ordrec_lim_ax assms by auto

definition if_ord3 :: "('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd" where 
  "if_ord3 G F A \<beta> x \<equiv> 
      if \<beta> = 0 then A else if \<exists>\<beta>'. \<beta> = succ \<beta>' then F \<beta> x else if Limit \<beta> then G \<beta> x else \<emptyset>" 

lemma if_ord_0 : "if_ord3 G F A 0 x = A" unfolding if_ord3_def by auto
lemma if_ord_succ : assumes "Ord \<beta>" shows "if_ord3 G F A (succ \<beta>) = F (succ \<beta>)" unfolding if_ord3_def 
  using exI[of \<open>(\<lambda>\<beta>'. succ \<beta> = succ \<beta>')\<close> \<open>\<beta>\<close>, OF refl] succ_nonzero[OF assms] by auto
lemma if_ord_lim : assumes "Limit \<mu>" shows "if_ord3 G F A \<mu> = G \<mu>"
  unfolding if_ord3_def using Limit_nonzero not_succ_Limit assms by auto

lemma if_set : assumes "Set x" "Set y" shows "Set (if P then x else y)" using assms by simp

lemma if_ord3_set : assumes "Set A" "\<And>\<beta>. Ord \<beta> \<Longrightarrow> Set x \<Longrightarrow> Set (F (succ \<beta>) x)" 
                                    "\<And>\<mu>. Limit \<mu> \<Longrightarrow> Set x \<Longrightarrow> Set (G \<mu> x)"
                    shows "Ord \<beta> \<Longrightarrow> Set x \<Longrightarrow> Set (if_ord3 G F A \<beta> x)" 
  unfolding if_ord3_def using assms by auto

thm if_True if_False Eq_TrueI Eq_FalseI
thm if_P if_not_P
thm refl succ_nonzero
thm not_sym[OF lt_neq]
thm succ_lt[OF zero_ord]
thm lt_trans_pure[OF lt_trans_pure[OF lt_trans_pure], 
                  of \<open>0\<close> \<open>succ 0\<close> \<open>succ (succ 0)\<close> \<open>succ (succ (succ 0))\<close> \<open>succ (succ (succ (succ 0)))\<close>,
                  OF le_refl[OF zero_ord] le_refl[OF succ_ord[OF zero_ord]] 
                     le_refl[OF succ_ord[OF succ_ord[OF zero_ord]]] 
                     le_refl[OF succ_ord[OF succ_ord[OF succ_ord[OF zero_ord]]]]]

thm lt_trans_pure[OF le_refl[of 0] lt_trans_pure[OF le_refl]]
ML \<open>fun mk_ord_thm z _ 0 = z
      | mk_ord_thm z s n = s OF [mk_ord_thm z s (n-1)]\<close>

ML \<open>fun le_trans r t 0 = r 
      | le_trans r t j = t OF [le_trans r t (j-1)]\<close>

ML \<open>fun ord_le (z,s,r,t) i j = le_trans r t (j-i) OF (map (fn n => if n = i then mk_ord_thm z s n else r OF [mk_ord_thm z s n]) (i upto j))\<close>
ML \<open>fun ord_neq thms neq i j = @{thm not_sym} OF [neq] OF [ord_le thms i (j-1)]\<close>

ML \<open>fun ops_alpha thms neq i j = 
      if i = j then @{thm if_P} OF [@{thm refl}]
      else @{thm trans} OF [@{thm if_not_P} OF [ord_neq thms neq i j], 
                            ops_alpha thms neq (i+1) j]\<close>


(*Ops 0*)
thm if_P[OF refl[of 0]]
(*Ops 1*)
thm trans[OF if_not_P[OF succ_neq[OF zero_ord]] if_P[OF refl[of \<open>succ 0\<close>]]]
(*Ops 2*)
thm trans[OF if_not_P[OF succ_neq[OF zero_ord]] if_P[OF refl[of \<open>succ (succ 0)\<close>]]]


end
end