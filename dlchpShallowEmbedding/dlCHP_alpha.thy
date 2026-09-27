theory dlCHP_alpha
  imports "UTP-Reactive.utp_reactive" "HOL-Library.Prefix_Order" "Scene_spaces_extra"
begin 

unbundle UTP_Syntax

type_synonym 'e ttrace = "('e \<times> real) list"


alphabet time_alpha = time_var :: real
alphabet_scene_space time_alpha
(*alphabet 'e dlCHP_alpha = "'e ttrace rea_vars" +
  time :: real*)

abbreviation "dst \<equiv> more\<^sub>L"

abbreviation "time \<equiv> (st:time_var)\<^sub>v"

type_synonym ('s, 'e) dlCHP_rel = "('s time_alpha_scheme,'e ttrace,unit) rsp_hrel"
type_synonym ('a, 's, 'e) dlCHP_expr = "('s time_alpha_scheme,'e ttrace,unit) rsp \<Rightarrow> 'a"

type_synonym ('s, 'e) dlCHP_alpha = "('s time_alpha_scheme,'e ttrace,unit) rsp" 


instantiation des_vars_ext :: (scene_space) scene_space
begin

  definition "Vars \<equiv> alpha_scene_space' [\<lbrakk>ok\<rbrakk>\<^sub>\<sim>] des_vars.more\<^sub>L 1\<^sub>L"

instance 

  apply (rule scene_space_class.intro)
   apply intro_classes[1]
  apply (simp add: Vars_des_vars_ext_def)
  apply (rule alpha_scene_space_class_intro alpha_scene_space_class_intro')
         apply (simp_all add: scene_indeps_def pairwise_def scene_space_lemmas)
  done
end

lemma lens_quot_equiv_cong:
  assumes "vwb_lens X" "vwb_lens Y" "vwb_lens Z" "X \<approx>\<^sub>L Y" "X \<subseteq>\<^sub>L Z" "Y \<subseteq>\<^sub>L Z"
  shows "X /\<^sub>L Z \<approx>\<^sub>L Y /\<^sub>L Z"
  by (metis assms lens_comp_quotient mwb_lens_def scene_space_lemmas(10,2) sublens_def
      vwb_lens_iff_mwb_UNIV_src)


lemma wait_tr_vR_bij: "wait +\<^sub>L tr +\<^sub>L \<^bold>v\<^sub>R \<approx>\<^sub>L \<^bold>v\<^sub>D"
  by (simp add: lens_equiv_sym) 

thm lens_quot_equiv_cong[where X = X and Y = Y and Z = Y]

lemma lens_equiv_quot_one:
  assumes "vwb_lens X" "vwb_lens Y" "X \<approx>\<^sub>L Y"
  shows "X /\<^sub>L Y \<approx>\<^sub>L 1\<^sub>L"
  using assms(1,2,3) bij_lens_equiv_id lens_equiv_sym lens_quotient_bij by blast

thm lens_quotient_indep

lemma lens_quot_indep:
  assumes "vwb_lens Z\<^sub>1" "vwb_lens Z\<^sub>2" "X \<subseteq>\<^sub>L Z\<^sub>1" "Y \<subseteq>\<^sub>L Z\<^sub>2" "Z\<^sub>1 \<approx>\<^sub>L Z\<^sub>2" "X \<bowtie> Y" 
  shows "X /\<^sub>L Z\<^sub>1 \<bowtie> Y /\<^sub>L Z\<^sub>2"
  using assms
  apply (unfold_locales)
  apply (simp_all add: lens_quotient_def sublens_iff_sublens' lens_create_def lens_indep.lens_put_comm sublens'_prop1 sublens'_prop2 lens_indep.lens_put_irr2)
  oops

instantiation rea_vars_ext :: (trace, scene_space) scene_space
begin

  definition Vars_rea_vars_ext :: "\<lparr>wait\<^sub>v :: \<bool>, tr\<^sub>v :: 'a, \<dots> :: 'b\<rparr> scene list" where
  "Vars_rea_vars_ext \<equiv> alpha_scene_space' [\<lbrakk>wait /\<^sub>L des_vars.more\<^sub>L\<rbrakk>\<^sub>\<sim>, \<lbrakk>tr /\<^sub>L des_vars.more\<^sub>L \<rbrakk>\<^sub>\<sim>] (rea_vars.more\<^sub>L /\<^sub>L des_vars.more\<^sub>L) 1\<^sub>L"

instance 

  apply (rule scene_space_class.intro)
   apply intro_classes[1]
  apply (simp add: Vars_rea_vars_ext_def)
  apply (rule alpha_scene_space_class_intro alpha_scene_space_class_intro')
         apply (simp_all add: scene_indeps_def pairwise_def scene_space_lemmas)
  apply (rule lens_equiv_quot_one)
  apply (simp_all add: lens_equiv_sym)

  done

end


instantiation srea_vars_ext :: (scene_space, scene_space) scene_space
begin

  (*definition Vars_srea_vars_ext :: "\<lparr>st\<^sub>v :: 'a, \<dots> :: 'b\<rparr> scene list" where
  "Vars_srea_vars_ext \<equiv> alpha_scene_space' [\<lbrakk>st /\<^sub>L (rea_vars.more\<^sub>L :: _ \<Longrightarrow> _)\<rbrakk>\<^sub>\<sim>] ((srea_vars.more\<^sub>L :: 'a \<Longrightarrow> ((unit \<times> real) list, 'a) dlCHP_alpha_scheme) /\<^sub>L rea_vars.more\<^sub>L) 1\<^sub>L"

instance
  apply (rule scene_space_class.intro)
   apply intro_classes[1]
  apply (simp add: Vars_dlCHP_alpha_ext_def)
  apply (rule alpha_scene_space_class_intro alpha_scene_space_class_intro')
         apply (simp_all add: scene_indeps_def pairwise_def scene_space_lemmas)
  apply (rule lens_equiv_quot_one)
  apply (simp_all add: lens_equiv_sym)
  done
*)
instance sorry
end

declare lens_quotient_id_denom [simp]

lemma "\<lbrakk>tr /\<^sub>L \<^bold>v\<^sub>D\<rbrakk>\<^sub>\<sim> ;\<^sub>S \<^bold>v\<^sub>D /\<^sub>L 1\<^sub>L = \<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
  apply (simp add: )
  done

(*  
lemma time_prop: "time = time /\<^sub>L \<^bold>v\<^sub>R ;\<^sub>L \<^bold>v\<^sub>R" (* Should be automatically generated *)
  apply (auto simp add: alpha_defs lens_defs fun_eq_iff)
  apply (metis (no_types, lifting) dlCHP_alpha.simps(1) dlCHP_alpha.surjective rea_vars.simps(3,6))
  by (smt (verit) des_vars_ext_def dlCHP_alpha.simps(3,3) dlCHP_alpha.surjective dlCHP_alpha.surjective
      rea_vars.simps(3,3,6,6) rea_vars_ext_def)
*)

lemma tr_is_var: "\<lbrakk>tr\<rbrakk>\<^sub>\<sim> \<in> set Vars"
  apply( auto simp add:  alpha_scene_space'_def alpha_scene_space_def Vars_des_vars_ext_def Vars_rea_vars_ext_def )
  done

lemma wait_is_var:  "\<lbrakk>wait\<rbrakk>\<^sub>\<sim> \<in> set Vars"
  apply( auto simp add:  alpha_scene_space'_def alpha_scene_space_def Vars_des_vars_ext_def Vars_rea_vars_ext_def )
  done


lemma time_is_var: "\<lbrakk>time\<rbrakk>\<^sub>\<sim> \<in> set Vars"
  apply( auto simp add:  alpha_scene_space'_def alpha_scene_space_def Vars_des_vars_ext_def Vars_rea_vars_ext_def )
  sorry



definition observables :: "('s, 'e) dlCHP_alpha scene  set" where
  "observables =  {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>, \<lbrakk>wait\<rbrakk>\<^sub>\<sim>, \<lbrakk>time\<rbrakk>\<^sub>\<sim>}" 

lemma observables_is_vars: "observables \<subseteq> set Vars"
  apply( auto simp add: observables_def alpha_scene_space'_def alpha_scene_space_def Vars_des_vars_ext_def Vars_rea_vars_ext_def )
  (*apply(simp add: lens_scene_quotient)
  apply (metis (no_types, opaque_lifting) dlCHP_alpha.sublenses(1) lens_quotient_vwb rea_vars.more\<^sub>L_vwb_lens
      scene_space_lemmas(10,4) sublens_pres_vwb time_prop)*)
  sorry
  

definition para_obs :: "('s, 'e) dlCHP_alpha scene set" where
  "para_obs =  {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>, \<lbrakk>wait\<rbrakk>\<^sub>\<sim>}" 

lemma para_obs_is_vars: "para_obs \<subseteq> set Vars" (is "?A \<subseteq> ?B")
proof -
  have "?A \<subseteq> observables"
    by (simp add: para_obs_def observables_def)
  thus ?thesis
    using observables_is_vars by auto
qed

lemma st_is_vR: "(st::'a \<Longrightarrow> ('b::trace, 'a, unit) srea_vars_scheme) \<approx>\<^sub>L \<^bold>v\<^sub>R"
  apply (simp add: lens_equiv_iff_lens_equiv' lens_equiv'_def)
  apply (auto simp add: lens_defs alpha_defs)
  apply (case_tac s\<^sub>1)
  apply simp
  apply (case_tac s\<^sub>1)
  apply simp
  apply (metis rea_vars.simps(3) srea_vars.surjective unit.exhaust)
  done

end