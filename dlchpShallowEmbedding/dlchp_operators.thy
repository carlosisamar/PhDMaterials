theory dlchp_operators
  imports "Z_Toolkit.List_Extra"  "dlCHP_alpha" "dlchp_traces" "Vars_dlchp"  "Framed_ODEs.Framed_ODEs"
begin

unbundle UTP_Syntax

notation lens_get ("(_<_>)" [76, 0] 75)


definition inp_dlchp :: "('a \<Rightarrow> 'e) \<Rightarrow> ('a \<Longrightarrow> 's time_alpha_scheme) \<Rightarrow> ('s::scene_space, 'e::channel) dlCHP_rel" where
"inp_dlchp c x = (\<lambda> (s,s'). if (\<not> wait<s>) then (\<exists> e.( ((tr<s'> \<le> tr<s>@[(c e, time<s>)] \<and> tr<s> \<le> tr<s'> \<and> wait<s'>) \<or> (tr<s'> = tr<s>@[(c e, time<s>)] \<and> \<not>wait<s'>) ) \<and> st<s'> = put\<^bsub>x\<^esub> (st<s>) e \<and> ok<s'> = ok<s>  )) else s' = s )"


(*"inp c P = (\<Sqinter> e \<in> range c. tr := tr @ [(\<guillemotleft>e\<guillemotright>, time)] ;; P(inv c e))"*)

syntax "_inp_dlchp" :: "id \<Rightarrow> id \<Rightarrow> logic" ("(_?\<^sub>d_)" [70, 0] 71)
translations "c?\<^sub>dx" == "CONST inp_dlchp c  x "
syntax_consts "_inp_dlchp" == inp_dlchp

definition out_dlchp :: "('a \<Rightarrow> 'e) \<Rightarrow> ('s time_alpha_scheme \<Rightarrow> 'a) \<Rightarrow> ('s::scene_space, 'e::channel) dlCHP_rel" where
"out_dlchp c e = ((\<lambda> (s,s'). if (\<not> wait<s>) then ( ((tr<s'> \<le> tr<s>@[(c (e (st<s>)), time<s>)] \<and> tr<s> \<le> tr<s'> \<and> wait<s'>) \<or> (tr<s'> = tr<s>@[(c(e (st<s>)), time<s>)] \<and> \<not>wait<s'> )) \<and> (st<s'>) = (st<s>)  \<and> ok<s'> = ok<s> ) else s' = s ))"

syntax "_out_dlchp" :: "id \<Rightarrow> logic  \<Rightarrow> logic" ("(_!\<^sub>d_)" [70, 0] 71)
translations "c!\<^sub>de " == "CONST out_dlchp c e "

(* restriction of trace t to P\<Parallel>Q, defined as communication events in t with a channel in P or Q *)
definition trace_restriction_paral ::  "(('e::channel \<times> real) list) \<Rightarrow> ('s, 'e) dlCHP_rel \<Rightarrow> ('s, 'e) dlCHP_rel \<Rightarrow> ('e \<times> real) list " where
  "trace_restriction_paral t P Q =  trace_restriction_channels t (CN P \<union> CN Q) "

(* [[\<alpha>\<Parallel>\<beta>]]= (\<nu>,\<tau>,\<omega>\<^sub>\<alpha>\<oplus>\<omega>\<^sub>\<beta>) | (\<nu>,\<tau>\<down>\<gamma>,\<omega>\<^sub>\<gamma>) \<in> [[\<gamma>]] for \<gamma> \<in> {\<alpha>,\<beta>} and \<omega>\<^sub>\<alpha> = \<omega>\<^sub>\<beta> on {\<mu>}, and \<tau>\<down>(\<alpha>\<Parallel>\<beta>) = \<tau> *)
(*t' needs to agree *)
definition parallel :: "('s::scene_space, 'e::channel) dlCHP_rel \<Rightarrow> ('s, 'e) dlCHP_rel => ('s, 'e) dlCHP_rel" (infixr "\<parallel>\<^sub>d" 85) where
  "parallel P  Q  = ( \<lambda>(s, s\<^sub>0). (\<exists> s' s'' ptr. s\<^sub>0 = put\<^bsub>time\<^esub> (put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (s'' \<oplus>\<^sub>S s' on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr)) (wait<s'> \<or> wait<s''>)) (if (wait<s'> \<or> wait<s''>) then (if (time<s'> = time<s''>) then time<s'> else -1 ) else time<s'>)  \<and>   
                                             P (s, s') \<and>   Q (s, s'') \<and>
                                             ptr \<downharpoonright> P = (tr<s'> - tr<s>) \<and>  ptr \<downharpoonright> Q = (tr<s''>  - tr<s>) \<and> 
                                             (((wait<s'> \<or> wait<s''>)) \<or> ( (time<s'> = time<s''>))) \<and>
                                             trace_restriction_paral ptr P Q = ptr))"



definition commit_dlchp :: "('s::scene_space, 'e::channel) dlCHP_rel \<Rightarrow> (bool, 's::scene_space, 'e::channel) dlCHP_expr \<Rightarrow> (bool, 's::scene_space, 'e::channel) dlCHP_expr \<Rightarrow>  ('s, 'e) dlCHP_alpha \<Rightarrow> bool" where
  "commit_dlchp P A C s = (\<forall> s'.  P (s,s') \<longrightarrow> 
              (\<forall> t < (tr<s'>-tr<s>).  A (trace_state_conc s t )) \<longrightarrow> C (trace_state_conc s (tr<s'>-tr<s>)))"

definition post_dlchp ::  "('s::scene_space, 'e::channel) dlCHP_rel \<Rightarrow> (bool, 's::scene_space, 'e::channel) dlCHP_expr \<Rightarrow> (bool, 's::scene_space, 'e::channel) dlCHP_expr \<Rightarrow> ('s, 'e) dlCHP_alpha \<Rightarrow> bool" where
  " post_dlchp P A F s =  (\<forall> s'.  P (s,s') \<longrightarrow> 
                       ((\<forall> t \<le> (tr<s'>-tr<s>).  A (trace_state_conc s t)) \<and> \<not> wait<s'> ) \<longrightarrow> F s')"

definition fbox_ac :: "('s::scene_space, 'e::channel) dlCHP_rel \<Rightarrow> (bool, 's::scene_space, 'e::channel) dlCHP_expr \<Rightarrow> (bool, 's::scene_space, 'e::channel) dlCHP_expr \<Rightarrow>(bool, 's::scene_space, 'e::channel) dlCHP_expr \<Rightarrow> (bool, 's::scene_space, 'e::channel) dlCHP_expr" where
   "fbox_ac P A C F  = ( \<lambda> s. (commit_dlchp P A C s) \<and> (post_dlchp P A F s))"

syntax "_fbox_ac" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("([_]\<^sub>P {_,_} _ )" [80, 80, 80, 80] 71)
translations "[P]\<^sub>P {A,C} F" == "CONST fbox_ac P A C F "

definition fbox_utp :: "('s::scene_space, 'e::channel) dlCHP_rel \<Rightarrow>(bool, 's::scene_space, 'e::channel) dlCHP_expr \<Rightarrow> (bool, 's::scene_space, 'e::channel) dlCHP_expr" where
  "fbox_utp P F = (\<lambda> s. (\<forall> s'.\<not>wait<s'> \<longrightarrow>  (P (s,s') \<longrightarrow> F s'))) "

syntax "_fbox_utp" :: "logic  \<Rightarrow> logic \<Rightarrow> logic" ("([_]\<^bold> _ )" [70, 0] 71)
translations "[P] F" == "CONST fbox_utp P F "


definition choice_dlchp :: "('s::scene_space, 'e::channel) dlCHP_rel \<Rightarrow> ('s, 'e) dlCHP_rel => ('s, 'e) dlCHP_rel" (infixr "\<Union>\<^sub>d" 85) where
  "choice_dlchp P Q = (\<lambda>(s, s'). P(s,s') \<or> Q(s, s'))"

definition test_dlchp :: "(bool, 's::scene_space, 'e::channel) dlCHP_expr \<Rightarrow> ('s, 'e) dlCHP_rel" where
  "test_dlchp T = (\<lambda>(s,s'). (s' = (put\<^bsub>wait\<^esub> s (True))) \<or> (s' = s \<and> T s)) "

syntax "_test_dlchp" :: "logic \<Rightarrow> logic" ("(?_)" [70])
translations "? T" == "CONST test_dlchp T"

definition seq_comp_dlchp :: "('s::scene_space, 'e::channel) dlCHP_rel \<Rightarrow> ('s, 'e) dlCHP_rel => ('s, 'e) dlCHP_rel" (infixr ";;\<^sub>d" 85) where
  "seq_comp_dlchp P Q = (\<lambda>(s, s'). (P(s,s') \<and> wait<s'>) \<or> (\<exists> s\<^sub>0. P(s,s\<^sub>0) \<and> \<not>wait<s\<^sub>0> \<and> Q (s\<^sub>0, s')))"


definition assign_dlchp :: "('a  \<Longrightarrow> 's  time_alpha_scheme)  \<Rightarrow> ('s  time_alpha_scheme\<Rightarrow> 'a)  \<Rightarrow> ('s::scene_space, 'e::channel) dlCHP_rel" where
[pred]: "assign_dlchp x e =((\<lambda>(s, s'). (if (\<not> wait<s>) then (s' = (put\<^bsub>wait\<^esub> s (True))) \<or> (st<s'> = put\<^bsub>x\<^esub> (st<s>) (e (st<s>)) \<and> tr<s'> = tr<s> \<and> wait<s'> = wait<s> \<and> ok<s'> = ok<s>) else s=s') )) "

syntax "_assign_dlchp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("(_ :=\<^sub>d _)" [70,70])
translations "x :=\<^sub>d e" == "CONST assign_dlchp x (e)\<^sub>e"

definition ndet_assign_dlchp :: "('a  \<Longrightarrow> 's  time_alpha_scheme)  \<Rightarrow> ('s::scene_space, 'e::channel) dlCHP_rel" where
[pred]: "ndet_assign_dlchp x  = (\<Sqinter> v. x :=\<^sub>d \<guillemotleft>v\<guillemotright>) "

syntax "_ndet_assign_dlchp" :: "logic \<Rightarrow> logic" ("(_ :=\<^sub>d \<star>)" [70])
translations "x :=\<^sub>d \<star>" == "CONST ndet_assign_dlchp x"

fun upower_dlchp ::
  "('s::scene_space, 'e::channel) dlCHP_rel \<Rightarrow> nat \<Rightarrow>
   ('s, 'e) dlCHP_rel"
  (infixr "^\<^sup>d" 80)
where
  "P ^\<^sup>d 0 = (?(True)\<^sub>e)"
| "P ^\<^sup>d (Suc n) = P ;;\<^sub>d (P ^\<^sup>d n)"

definition loop_dlchp :: " ('s::scene_space, 'e::channel) dlCHP_rel \<Rightarrow>  ('s::scene_space, 'e::channel) dlCHP_rel"  where
  "loop_dlchp P =  (\<Sqinter>i. P^\<^sup>d i)"

syntax "_loop_dlchp" :: "logic \<Rightarrow> logic" ("(_\<^sup>d)" [70])
translations "P\<^sup>d" == "CONST loop_dlchp P"

definition Dyn_SysC :: "('a::real_normed_vector \<Longrightarrow> 's time_alpha_scheme) \<Rightarrow> ('s time_alpha_scheme \<Rightarrow> 's time_alpha_scheme) \<Rightarrow> ('s time_alpha_scheme \<Rightarrow> bool) \<Rightarrow> ('s::scene_space, 'e::channel) dlCHP_rel" where
"Dyn_SysC x \<sigma> G = (\<lambda> (s, s').(if (\<not> wait<s>) then (s' = (put\<^bsub>wait\<^esub> s (True))) \<or> ( st<s'> \<in> g_orbital_on x (\<lambda> t. \<sigma>) G (\<lambda> t. UNIV) UNIV 0 (st<s>) \<and> tr<s'> = tr<s> \<and> wait<s'> = wait<s>) else s = s') )"



syntax
  "_ode" :: "derivs \<Rightarrow> logic \<Rightarrow> logic" ("{_ | _}")

translations
  "_ode \<sigma> G" => "CONST Dyn_SysC (_smaplets_svids \<sigma>) (_Subst \<sigma>) (G)\<^sub>e"

term "{x` = 1 | True}"

end