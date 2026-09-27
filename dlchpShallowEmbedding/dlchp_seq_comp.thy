theory dlchp_seq_comp
  imports "dlchp_operators" "dlchp_health"
begin

definition comm_well_formed :: "(bool, 's::scene_space, 'e::channel) dlCHP_expr \<Rightarrow> ('s, 'e) dlCHP_rel \<Rightarrow> bool" where 
 "comm_well_formed A P = (FV A \<inter> BV_progs P \<subseteq> {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>} )"


lemma coincidence_cwf :
  assumes "comm_well_formed A P" "P(s,s')"
  shows "s \<approx>\<^sub>S s' on \<Union>\<^sub>S (FV A - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
proof -
  have bv:"s \<approx>\<^sub>S s' on -\<Union>\<^sub>S (BV_progs P)"
    using bound_eff_1 bound_eff_prop_def
    by (metis assms(2))

  hence "\<forall> x \<in> (set Vars - BV_progs P). s \<approx>\<^sub>S s' on x"
    using   BV_is_vars
    by (metis scene_neg_decomp)

  moreover have "(FV A - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>}) \<subseteq> (set Vars - BV_progs P)"
    using assms(1) comm_well_formed_def FV_Vars tr_is_var
    by blast 

  ultimately have "\<forall> x \<in> (FV A - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>}). s \<approx>\<^sub>S s' on x"
    by blast

  thus ?thesis
    using scene_union_equiv
    by (metis (mono_tags, lifting) Diff_subset FV_Vars basic_trans_rules(23)
        mem_Vars_scene_space)
qed


lemma cwf_seq_comp:
  assumes "comm_well_formed A P" "comm_well_formed A Q"
  shows "comm_well_formed A (P ;;\<^sub>d Q)"
proof -
  have "BV_progs (P ;;\<^sub>d Q) \<subseteq> BV_progs P \<union> BV_progs Q"
    apply(simp add: BV_progs_def seq_comp_dlchp_def)
    apply(auto)
    by (metis (no_types, lifting) scene_equiv_def scene_override_overshadow_right)
  then show ?thesis 
    using comm_well_formed_def assms
    by (smt (verit) Diff_partition Int_Un_distrib le_sup_iff)
qed

lemma action_comp_prev:
   assumes "comm_well_formed A P" "P(s, s')" "P is R1" "t = (tr<s'>-tr<s>)@t'"
   shows "(trace_state_conc s t) \<approx>\<^sub>S (trace_state_conc s' t') on \<Union>\<^sub>S (FV A)" 
proof -
  have l0:"tr<s> \<le> tr<s'>"
    using assms(2,3) Healthy_def R1_def
    by (metis (no_types, lifting) SEXP_def conj_pred_def get_post get_pre inf_apply
        inf_bool_def)
  have s1:"(trace_state_conc s t) \<approx>\<^sub>S  (trace_state_conc s' t' ) on \<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
        using trace_state_conc_def assms(4)
        by (metis (no_types, lifting) Prefix_Order.prefixE Scenes_extra.scene_equiv_get_eq
            l0 append.assoc append_minus tr_vwb_lens vwb_lens_def
            wb_lens.axioms(1) weak_lens.put_get)
  moreover have s2:"(trace_state_conc s t) \<approx>\<^sub>S (trace_state_conc s' t' ) on - \<Union>\<^sub>S(BV_progs P \<union> { \<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
        proof -
          have "(trace_state_conc s t) \<approx>\<^sub>S s on - \<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
            using trace_state_conc_def
            by (metis (no_types, opaque_lifting) lens_override_def lens_scene_override scene_equiv_def
                scene_override_commute tr_vwb_lens vwb_lens.axioms(1) vwb_lens_mwb wb_lens.axioms(1)
                weak_lens.put_get)
          then have l1:"(trace_state_conc s t) \<approx>\<^sub>S s on - \<Union>\<^sub>S(BV_progs P \<union> { \<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
            by (metis (mono_tags, opaque_lifting) BV_is_vars Sup_scene_closed UnCI bot.extremum
                insert_subset le_Sup_scene mem_Vars_scene_space scene_compl_subset_iff scene_lessthan_equiv
                scene_space_uminus singletonI sup.bounded_iff tr_is_var)
          have "(trace_state_conc s' t) \<approx>\<^sub>S s' on - \<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
            using trace_state_conc_def
            by (metis (no_types, opaque_lifting) lens_override_def lens_scene_override scene_equiv_def
                scene_override_commute tr_vwb_lens vwb_lens.axioms(1) vwb_lens_mwb wb_lens.axioms(1)
                weak_lens.put_get)
          then have l2:"(trace_state_conc s' t) \<approx>\<^sub>S s' on - \<Union>\<^sub>S(BV_progs P \<union> { \<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
            by (metis (mono_tags, opaque_lifting) BV_is_vars Sup_scene_closed UnCI bot.extremum
                insert_subset le_Sup_scene mem_Vars_scene_space scene_compl_subset_iff scene_lessthan_equiv
                scene_space_uminus singletonI sup.bounded_iff tr_is_var)
          have "s \<approx>\<^sub>S s' on - \<Union>\<^sub>S(BV_progs P)"
            using assms(2) bound_eff_prop_def bound_eff_1
            by metis
          then have l3:"s \<approx>\<^sub>S s' on - \<Union>\<^sub>S(BV_progs P \<union> { \<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
            by (metis (no_types, lifting) BV_is_vars scene_union_neg_put_preserved tr_is_var tr_vwb_lens
                vwb_lens.put_eq)
          show ?thesis
            using l1 l2 l3
            by (smt (verit, ccfv_SIG) BV_is_vars Prefix_Order.prefixE Scenes_extra.scene_equiv_get_eq
                Sup_scene_closed Un_insert_right l0 append.assoc append_minus
                assms(2) bound_eff_2 idem_scene_space idem_scene_uminus insert_absorb insert_subset
                para_obs_def para_obs_is_vars scene_equiv_def scene_equiv_sym
                scene_override_overshadow_right scene_union_neg_put_preserved sup_bot_right assms(4) tr_vwb_lens
                trace_state_conc_def)
        qed
      ultimately show ?thesis
      proof -
        {
          fix x
          assume x1:"x \<in> FV A"
          have x2:"x \<in> { \<lbrakk>tr\<rbrakk>\<^sub>\<sim>} \<or> x \<notin> BV_progs P - { \<lbrakk>tr\<rbrakk>\<^sub>\<sim>} "
            using assms(1) comm_well_formed_def x1 by auto
          moreover have "x \<in> { \<lbrakk>tr\<rbrakk>\<^sub>\<sim>} \<longrightarrow> (trace_state_conc s t) \<approx>\<^sub>S  (trace_state_conc s' t' ) on x"
            using s1
            by simp
          moreover have "x \<notin> BV_progs P - { \<lbrakk>tr\<rbrakk>\<^sub>\<sim>} \<longrightarrow> (trace_state_conc s t) \<approx>\<^sub>S  (trace_state_conc s' t' ) on x"
            using s2 x1 scene_neg_decomp FV_Vars
            by (smt (verit, del_insts) BV_is_vars Diff_iff Diff_insert Un_insert_right calculation(2)
                insert_Diff insert_subset sup_bot_right tr_is_var)
          ultimately have "(trace_state_conc s t) \<approx>\<^sub>S  (trace_state_conc s' t' ) on x"
            by meson
        }
        then show ?thesis
          by (meson FV_Vars mem_Vars_scene_space scene_union_equiv)  
      qed
    qed


lemma action_comp_leq:
  assumes "comm_well_formed A P"  "comm_well_formed A Q" "P(s, s0)"  "(\<forall> t \<le> (tr<s0>-tr<s>).  A (trace_state_conc s t))" "Q(s0,s')" "\<forall> t \<le> (tr<s'>-tr<s0>).  A (trace_state_conc s0 t )" "P is R1" "Q is R1" 
  shows "\<forall> t \<le> (tr<s'>-tr<s>).  A (trace_state_conc s t )"
proof -
  {
    fix t
    assume t1:"t \<le> (tr<s'>-tr<s>)"
    have "tr<s> \<le> tr<s0>"
      using assms(3,7) Healthy_def R1_def
      by (metis (no_types, lifting) SEXP_def conj_pred_def get_post get_pre inf_apply
          inf_bool_def)
    moreover have "tr<s0> \<le> tr<s'>"
      using assms(5,8) Healthy_def R1_def
      by (metis (no_types, lifting) SEXP_def conj_pred_def get_post get_pre inf_apply
          inf_bool_def)
    ultimately have l0:"t \<le> (tr<s0>-tr<s>) \<or> (\<exists> t'. t' \<le> (tr<s'>-tr<s0>) \<and> t = (tr<s0>-tr<s>)@t')"
      using t1
      apply(pred_simp)
      apply(auto)
      by (smt (verit, del_insts) Prefix_Order.prefixE append_minus le_common_total
          list_append_prefixD list_concat_minus_list_concat minus_cancel_le)
    have " A (trace_state_conc s t )"
    proof (cases "t \<le> (tr<s0>-tr<s>)")
      case True
      then show ?thesis
        using assms(4) by blast
    next
      case False
      then have l1:"(\<exists> t'. t' \<le> (tr<s'>-tr<s0>) \<and> t = (tr<s0>-tr<s>)@t')"
        using l0 False by auto
      obtain t' where t2:"t' \<le> (tr<s'>-tr<s0>)" and t3:" t = (tr<s0>-tr<s>)@t'"
        using l1 by blast
      have "(trace_state_conc s t) \<approx>\<^sub>S  (trace_state_conc s0 t' ) on \<Union>\<^sub>S (FV A)"
        using action_comp_prev assms(1,3,7) t3 by blast
      moreover have "A (trace_state_conc s0 t' )"
        using t2 assms(6)
        by blast
      ultimately show ?thesis
        using coincidence_eff_term_prop_def coin_eff_term_1
        by (smt (verit) FV_Vars scene_union_equiv set_Vars_scene_space subset_trans)
    qed
  }
  then show ?thesis
    by auto
qed
   
lemma action_comp_le:
  assumes "comm_well_formed A P"  "comm_well_formed A Q" "P(s, s0)"  "(\<forall> t < (tr<s0>-tr<s>).  A (trace_state_conc s t))" "Q(s0,s')" "\<forall> t < (tr<s'>-tr<s0>).  A (trace_state_conc s0 t )" "P is R1" "Q is R1" 
  shows "\<forall> t < (tr<s'>-tr<s>).  A (trace_state_conc s t )"
proof -
  {
    fix t
    assume t1:"t < (tr<s'>-tr<s>)"
    have "tr<s> \<le> tr<s0>"
      using assms(3,7) Healthy_def R1_def
      by (metis (no_types, lifting) SEXP_def conj_pred_def get_post get_pre inf_apply
          inf_bool_def)
    moreover have "tr<s0> \<le> tr<s'>"
      using assms(5,8) Healthy_def R1_def
      by (metis (no_types, lifting) SEXP_def conj_pred_def get_post get_pre inf_apply
          inf_bool_def)
    ultimately have l0:"t < (tr<s0>-tr<s>) \<or> (\<exists> t'. t' < (tr<s'>-tr<s0>) \<and> t = (tr<s0>-tr<s>)@t')"
      using t1
      apply(pred_simp)
      apply(auto)
      using Prefix_Order.prefixE append_minus le_common_total
          list_append_prefixD list_concat_minus_list_concat minus_cancel_le
      by (smt (z3) Prefix_Order.same_prefix_prefix less_list_def)
    have " A (trace_state_conc s t )"
    proof (cases "t < (tr<s0>-tr<s>)")
      case True
      then show ?thesis
        using assms(4) by blast
    next
      case False
      then have l1:"(\<exists> t'. t' < (tr<s'>-tr<s0>) \<and> t = (tr<s0>-tr<s>)@t')"
        using l0 False by auto
      obtain t' where t2:"t' < (tr<s'>-tr<s0>)" and t3:" t = (tr<s0>-tr<s>)@t'"
        using l1 by blast
      have "(trace_state_conc s t) \<approx>\<^sub>S  (trace_state_conc s0 t' ) on \<Union>\<^sub>S (FV A)"
        using action_comp_prev assms(1,3,7) t3 by blast
      moreover have "A (trace_state_conc s0 t' )"
        using t2 assms(6)
        by blast
      ultimately show ?thesis
        using coincidence_eff_term_prop_def coin_eff_term_1
        by (smt (verit) FV_Vars scene_union_equiv set_Vars_scene_space subset_trans)
    qed
  }
  then show ?thesis
    by auto
qed
   


lemma bv_seq:
  assumes "total P"
  shows "BV_progs P = BV_progs (P ;;\<^sub>d P)" 
  apply(simp add: seq_comp_dlchp_def BV_progs_def)
  apply(auto)
  apply (metis assms scene_equiv_def scene_override_overshadow_right total_def)
  by (metis (no_types, opaque_lifting) scene_equiv_def
      scene_override_overshadow_right)

end