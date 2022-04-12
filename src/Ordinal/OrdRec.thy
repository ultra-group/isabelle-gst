theory OrdRec
  imports "../GZF/GZF_Base" Ordinal "../Functions/Functions"
begin

class OrdRec = GZF + Ordinal + 
  fixes 
    predSet :: \<open>'a \<Rightarrow> 'a\<close> and 
    supOrd :: \<open>'a \<Rightarrow> 'a\<close> and
    OrdRec :: \<open>[['a,'a \<Rightarrow> 'a] \<Rightarrow> 'a, ['a,'a] \<Rightarrow> 'a, 'a, 'a] \<Rightarrow> 'a\<close> and
    OrdRec_default :: \<open>'a\<close>
  assumes 
    predset_typ : "predSet : Ord \<rightarrow> SetOf Ord" and
    predset_ax :  "\<forall>\<beta> : Ord. \<forall>\<alpha> : Ord. \<alpha> \<in> predSet \<beta> \<longleftrightarrow> \<alpha> < \<beta>" and
    supord_typ :  "supOrd : SetOf Ord \<rightarrow> Ord" and
    supord_ax :  "\<forall>x : SetOf Ord. \<forall>\<alpha>. \<alpha> \<in> x \<longrightarrow> \<alpha> < supOrd x" and
    ordrec_0 :  "\<forall>G. \<forall>F. \<forall>A. OrdRec G F A 0 = A" and
    ordrec_succ_ax :  "\<forall>G. \<forall>F. \<forall>A. \<forall>b : Ord. 
       OrdRec G F A (succ b) = F (succ b) (OrdRec G F A b)" and
    ordrec_lim_ax :  "\<forall>G. \<forall>F. \<forall>A. \<forall>\<mu> : Limit. 
       OrdRec G F A \<mu> = G \<mu> (\<lambda>j. if j : Ord \<and> j < \<mu> then OrdRec G F A j else OrdRec_default)"                    

syntax
  "_lam_ord" :: "[pttrn, 'a, 'a] => 'a" (\<open>(3\<lambda>_<_./ _)\<close> 10)
translations
  "\<lambda>i < j. F" \<rightleftharpoons> "CONST lam (CONST predSet j) (\<lambda>i. F)"

syntax
  "_RepFun_ord"  :: "['a, pttrn, 'a] => 'a"    (\<open>(1{ _ |/ _<_ })\<close> [51,0,51])
  "_Collect_ord" :: "[pttrn, 'a, bool ] \<Rightarrow> 'a" (\<open>(1{ _<_ |/ _ })\<close>)
  "_Union_ord"   :: "[pttrn, 'a, 'a] \<Rightarrow> 'a"    (\<open>(3\<Union>_<_./ _)\<close> 10)
translations
  "{c | i < j}" \<rightleftharpoons> "CONST RepFun (CONST predSet j) (\<lambda>i. c)"
  "{i < j | P}" \<rightleftharpoons> "CONST Collect (CONST predSet j) (\<lambda>i. P)"
  "\<Union> i<j. B"   \<rightleftharpoons> "CONST Union {B | i < j}"

context OrdRec begin

thm predset_typ supord_typ 
thm predset_ax supord_ax

lemmas predset_setof = funE[OF predset_typ]
lemmas predset_set = setof_set[OF predset_setof]
lemmas lim_predset_set = predset_set[OF limit_ord]
lemmas repfun_ord_setof = repfun_setof[OF predset_set]
lemmas repfun_union_ord_set = union_set[OF repfun_ord_setof]

lemma predset_mem_ord : 
  assumes "j : Ord"
  shows "i \<in> predSet j \<Longrightarrow> i : Ord"
  using setof_mem[OF predset_setof[OF assms]] by auto

lemma predset_iff : 
  assumes "i : Ord" "j : Ord" 
  shows "i \<in> predSet j \<longleftrightarrow> i < j"
  using predset_ax assms by auto 

lemma predsetI : 
  assumes "i : Ord" "j : Ord"
  shows "i < j \<Longrightarrow> i \<in> predSet j"
  using predset_iff[OF assms] by auto

lemma predsetE : 
  assumes j:"j : Ord"
  shows "i \<in> predSet j \<Longrightarrow> i < j"
  using predset_iff[OF _ j] setof_mem[OF predset_setof[OF j]] by auto 

lemma mem_predset_succ :
  assumes i:"i : Ord"
  shows "i \<in> predSet (succ i)"
  by (rule predsetI, use succ_ord leq_refl i in auto)

lemma predsetD : 
  assumes j:"j : Ord"
  shows "i \<in> predSet j \<Longrightarrow> i : Ord \<and> i < j"
  using predset_iff[OF _ j] setof_mem[OF predset_setof[OF j]] by auto 

lemma supord_iff : 
  assumes x : "x : SetOf Ord" and i : "i \<in> x"
  shows "i < supOrd x"
  using supord_ax assms by auto

lemmas supord_ord = funE[OF supord_typ]

lemma ord_setmem : 
  assumes i:"i : Ord" 
  shows "i : SetMem"
  by (rule setmemI[OF setof_set], 
      use predset_setof[OF succ_ord] mem_predset_succ i in auto)

lemma ordrec_succ : 
  assumes "b : Ord" 
    shows "OrdRec G F A (succ b) = 
    F (succ b) (OrdRec G F A b)"
  using ordrec_succ_ax assms by auto

lemma ordrec_lim : 
  assumes "u : Limit" 
    shows "OrdRec G F A u = 
    G u (\<lambda>j. if j : Ord \<and> j < u then OrdRec G F A j else OrdRec_default)"
  using ordrec_lim_ax assms by auto 

lemmas repfun_ord_set = repfun_set[OF predset_set]
lemmas repfun_lim_set = repfun_ord_set[OF limit_ord]

lemma repfun_ordrec_lim_restrict :
  assumes u : "u : Limit"
    shows "{ (if j : Ord \<and> j < u then OrdRec G F A j else OrdRec_default) | j < u } = 
           { OrdRec G F A j | j < u}"
   by (rule repfun_cong[OF lim_predset_set[OF u] lim_predset_set[OF u]], 
       rule refl, drule predsetD[OF limit_ord[OF u]], auto)
(* 

  





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
thm trans[OF if_not_P[OF succ_neq[OF zero_ord]] if_P[OF refl[of \<open>succ (succ 0)\<close>]]] *)


end
end