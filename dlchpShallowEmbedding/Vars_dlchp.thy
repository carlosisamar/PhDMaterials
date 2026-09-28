theory Vars_dlchp
  imports "Vars_UTP" "dlCHP_alpha" "dlchp_traces"
begin
unbundle UTP_Syntax

definition bound_eff_prop_dlchp :: "('s, 'e::channel) dlCHP_rel \<Rightarrow> ('s, 'e) dlCHP_alpha scene \<Rightarrow> 'e set set \<Rightarrow> bool" where
  [expr_defs]: "bound_eff_prop_dlchp P S chs = (\<forall> s s'. (P (s, s') \<longrightarrow> ( s  \<approx>\<^sub>S s' on S \<and> (trace_restriction_channels (tr<s'>-tr<s>) (chan_univ-chs) = [] )) ))"

lemma bound_eff_dlchp: 
  shows "bound_eff_prop_dlchp P (\<Union>\<^sub>S(set Vars - BV_progs P - para_obs)) (CN P)"
proof -
  {
  fix s s'
  assume sas1:"P (s, s')"
  have "s  \<approx>\<^sub>S s' on (\<Union>\<^sub>S(set Vars - BV_progs P - para_obs))"
  proof -
    {
    fix v
    assume as1:"v \<in> set Vars - BV_progs P - para_obs"
    have "v \<notin> BV_progs P"
      using as1 by blast
    then have "\<forall> s s'. (P (s, s') \<longrightarrow>  s  \<approx>\<^sub>S s' on v)"
      using BV_progs_def
      using as1 set_diff_eq by blast
    }
    thus ?thesis
      by (metis (no_types, lifting) BV_is_vars Diff_subset Int_Diff_Un \<open>P (s, s')\<close> bound_eff_1
          bound_eff_prop_def le_sup_iff scene_minus scene_subset_equiv set_Vars_scene_space)
  qed 
  moreover have "trace_restriction_channels (tr<s'>-tr<s>) (chan_univ - (CN P)) = []"
  proof -
      have "tr<s'>-tr<s> \<in> traces P"
        using sas1 traces_def by auto
      then have "\<forall> ch \<in> (channels_from_trace (tr<s'>-tr<s>)). ch \<in> CN P"
        using CN_def
        by (metis (no_types, lifting) channels_from_trace_cn insert_Diff insert_subset sas1
            trace_rest_contr)
      then have f1:"\<forall> ch \<in> (chan_univ - (CN P)). ch \<notin> channels_from_trace (tr<s'>-tr<s>) "
        by auto
      then have "\<forall> ch \<in> (chan_univ - (CN P)).(trace_restriction_channel (tr<s'>-tr<s>) ch = [])"
      proof -
        {
        fix ch
        assume ch1:"ch \<in> (chan_univ - (CN P))"
        have "ch \<notin> channels_from_trace (tr<s'>-tr<s>)"
          using f1 ch1 by auto
        then have "trace_restriction_channel (tr<s'>-tr<s>) ch = []"
          apply (simp add: trace_restriction_channel_def channels_from_trace_def)
          by (smt (verit, best) empty_filter_conv imageI)
      }
      thus ?thesis
        by auto
    qed
    thus ?thesis 
      using trace_res_empty
      by (metis Diff_subset)
  qed
  ultimately have "( s  \<approx>\<^sub>S s' on( \<Union>\<^sub>S(set Vars - BV_progs P - para_obs)) \<and> (trace_restriction_channels (tr<s'>-tr<s>) (chan_univ- (CN P)) = [] )) "
    by auto   
}
  thus ?thesis
    using bound_eff_prop_dlchp_def by blast
qed


lemma bound_eff_lemma_dlchp:
  fixes V Chs 
  assumes "bound_eff_prop_dlchp P (\<Union>\<^sub>S(set Vars - V - para_obs)) (Chs)" and "V \<subseteq> set Vars" and "Chs \<subseteq> chan_univ"
  shows " CN P \<subseteq> Chs \<and> BV_progs P - para_obs \<subseteq> V - para_obs" 
proof -
  have " CN P \<subseteq> Chs"
  proof -
    {
      fix ch
      assume ch1:"ch \<in> CN P" and ch2:"ch \<notin> Chs"
      obtain s s' where as1:"P(s, s')" and as2: "ch \<in> channels_from_trace (tr<s'>-tr<s>)"
        using ch1 CN_def by (smt (verit) mem_Collect_eq traces_def)
      have "trace_restriction_channel (tr<s'>-tr<s>) ch \<noteq> []"
        using as2 trace_rest_exist by blast
      then have "trace_restriction_channels (tr<s'>-tr<s>) (chan_univ - Chs) \<noteq> []"
        using ch2
        by (metis (no_types, lifting) CN_def Diff_subset Int_Diff_Un UnE assms(3) ch1 inf_absorb2
            mem_Collect_eq trace_res_empty)
      then have "\<not> bound_eff_prop_dlchp P (\<Union>\<^sub>S(set Vars - V - para_obs)) (Chs)"
        using bound_eff_prop_dlchp_def as1
        by metis
    }
    thus ?thesis
      using assms(1) by blast
  qed
  moreover have "BV_progs P - para_obs \<subseteq> V - para_obs"
  proof -
    {
      fix v
      assume v1:"v \<in> BV_progs P - para_obs" and v2:"v \<notin> V - para_obs"
      obtain s s' where as1:"P(s, s')" and as2: "\<not> (s \<approx>\<^sub>S s' on v)"
        using BV_progs_def
        by (smt (verit) Diff_iff mem_Collect_eq v1)
      have "\<not> (s \<approx>\<^sub>S s' on(\<Union>\<^sub>S(set Vars - V - para_obs)) )"
        using v2 as2
        by (metis (no_types, lifting) BV_progs_def Diff_iff Diff_subset dual_order.trans
            mem_Collect_eq scene_union_equiv set_Vars_scene_space v1)
      then have  "\<not> bound_eff_prop_dlchp P (\<Union>\<^sub>S(set Vars - V - para_obs)) (Chs)"
        using bound_eff_prop_dlchp_def as1
        by blast
    }
    thus ?thesis
      using assms(1) by blast
  qed
  ultimately show ?thesis
    by auto
qed

definition coincidence_eff_prop_term_dlchp :: "('a, 's::scene_space, 'e::channel) dlCHP_expr \<Rightarrow> ('s, 'e) dlCHP_alpha scene \<Rightarrow> 'e set set \<Rightarrow> bool" where
 "coincidence_eff_prop_term_dlchp T S chs = (\<forall> s s'. trace_restriction_state s chs \<approx>\<^sub>S trace_restriction_state s' chs on S \<longrightarrow> T s = T s')"

lemma coincidence_eff_prop_term_dlchp1 :
  "coincidence_eff_prop_term_dlchp T (\<Union>\<^sub>S((FV T) )) (CN_term T) "
proof -
  {
  fix s s'
  assume a1:" trace_restriction_state s (CN_term T) \<approx>\<^sub>S trace_restriction_state s' (CN_term T) on  (\<Union>\<^sub>S(FV T))"
  have  "T s = T s'"
  proof (cases "\<lbrakk>tr\<rbrakk>\<^sub>\<sim> \<in> (FV T)")
    case True
    then show ?thesis
    proof -
      have "\<forall> st.  T st = T (trace_restriction_state st (CN_term T))"
      proof -
        obtain chs' where a1:"chs' = chan_univ - CN_term T"
          by blast
        have "chan_univ - (chan_univ - CN_term T) = CN_term T"
          using CN_term_def by blast
        thus ?thesis
          using a1 cn_term_dist_set
          by (metis subset_refl)
      qed
      moreover have  "T (trace_restriction_state s (CN_term T)) = T (trace_restriction_state s' (CN_term T)) "
        using a1 scene_union_equiv Vars_UTP.coincidence_eff_term_prop_def coin_eff_term_1
        by (smt (verit) FV_iff scene_space_class.scene_space.Vars_scene_space subset_iff)
      ultimately show ?thesis
        by auto
    qed
  next
    case False
    then show ?thesis
    proof-
      have f1:" (\<Union>\<^sub>S(FV T)) \<le> -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
        using False
        by (smt (verit, ccfv_threshold) DiffI Diff_subset FV_Vars Sup_scene_closed le_Sup_scene
            scene_compl_subset_iff scene_minus set_Vars_scene_space subset_eq tr_is_var
            uminus_scene_twice)
      have "s \<approx>\<^sub>S trace_restriction_state s (CN_term T) on (\<Union>\<^sub>S(FV T))"
      using  state_conservation_rest_trace f1
      by (metis (no_types, lifting) Sup_scene_closed scene_lessthan_equiv scene_space_uminus
          set_Vars_scene_space subset_eq tr_is_var)
      moreover have "s' \<approx>\<^sub>S trace_restriction_state s' (CN_term T) on (\<Union>\<^sub>S(FV T))"
        using  state_conservation_rest_trace f1
        by (metis (no_types, lifting) Sup_scene_closed scene_lessthan_equiv scene_space_uminus
            set_Vars_scene_space subset_eq tr_is_var)
      ultimately have "s \<approx>\<^sub>S s' on (\<Union>\<^sub>S(FV T))"
        by (metis (no_types, lifting) Diff_empty Diff_insert0 False a1 scene_equiv_def
            scene_override_overshadow_right)
      thus ?thesis
        using scene_union_equiv Vars_UTP.coincidence_eff_term_prop_def coin_eff_term_1
        by (metis (mono_tags, lifting) FV_Vars dual_order.trans set_Vars_scene_space)
    qed
  qed
}
  thus ?thesis
  using coincidence_eff_prop_term_dlchp_def
  by blast
qed




end

  

      
      
  