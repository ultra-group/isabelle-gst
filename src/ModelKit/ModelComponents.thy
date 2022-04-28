theory ModelComponents
  imports ConnectionBase
  keywords "translate_axioms" "resp_thms" :: thy_goal 
begin

context ModelBase' begin
ML_file \<open>Tools/model_components.ML\<close>
ML_file \<open>Tools/translate_axioms.ML\<close>
end
(* 

ML \<open>val ordrec_model = mcomp 
 { name = "OrdRecModel", 
   deps = ["SetModel","OrdModel"], 
   variant = NONE } \<close>

ML \<open>val pair_model = mcomp 
 { name = "PairModel", 
   deps = [], 
   variant = SOME (vari 
    { tag_name = "opair",
      vcases = 
        (@{term \<open>\<emptyset>\<close>}, 
         @{term "(\<lambda>j x. x \<times> x) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"}, 
         @{term "(\<lambda>\<mu> f. \<emptyset>) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"}),
      alpha_typ = @{term \<open>Pair\<close>}}) } \<close>

ML \<open>val nat_model = mcomp
 { name = "NatModel", 
   deps = [], 
   variant = SOME (vari 
    { tag_name = "nat",
      vcases = 
        (@{term "{0}"},
         @{term "(\<lambda>\<beta> x. if \<beta> < \<omega> then {\<beta>} else \<emptyset>) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"},
         @{term "(\<lambda>\<mu> f. \<emptyset>) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"}),
      alpha_typ = @{term \<open>Ord\<close>}})}\<close> *)

(*Probably don't need?*)
(* ML_file \<open>Tools/connection_locales.ML\<close> *)

text \<open>Generating type-classes for models components,
      and locales for connecting model components to domains\<close>

(* No longer needed, using lifting & transfer now.
ML_file \<open>swap_transfer.ML\<close> *)



end


(* local_setup \<open>snd o (mk_mcomp_class ord_model)\<close>
local_setup \<open>snd o (mk_connection_locale @{theory} ord_model)\<close>

local_setup \<open>snd o (mk_mcomp_class ordrec_model)\<close>
local_setup \<open>snd o (mk_connection_locale @{theory} ordrec_model)\<close>

local_setup \<open>snd o (mk_mcomp_class pair_model)\<close>
local_setup \<open>snd o (mk_connection_locale @{theory} pair_model)\<close>

local_setup \<open>snd o (mk_mcomp_class nat_model)\<close>
local_setup \<open>snd o (mk_connection_locale @{theory} nat_model)\<close>  *)