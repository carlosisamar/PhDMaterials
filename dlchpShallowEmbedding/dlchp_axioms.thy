theory dlchp_axioms
  imports "dlchp_operators" "dlchp_parallel" "dlchp_alpha" "dlchp_health" "dlchp_seq_comp" "dlchp_loop"
  "dlchp_communication"
begin

unbundle UTP_Syntax

notation lens_get ("(_<_>)" [76, 0] 75)

theorem box_simp_1: "([P] F)  s \<longleftrightarrow> ([P]\<^sub>P {(True)\<^sub>e,(True)\<^sub>e} F ) s "
  unfolding fbox_ac_def fbox_utp_def commit_dlchp_def post_dlchp_def
  by auto

theorem parallel_injection:
  assumes "P is R1" "non_inter_dlchp_comp Q P A C F" "prefix_closed P" "prefix_closed Q"
  shows "([P]\<^sub>P {A,C} F ) s \<longrightarrow> ([(P \<parallel>\<^sub>d Q)]\<^sub>P {A,C} F ) s"
proof -
  {
    assume a1:"([P]\<^sub>P {A,C} F ) s"
    have l1:"commit_dlchp (P \<parallel>\<^sub>d Q) A C s"
    proof -
      {
      fix s'
      assume a2:"(P\<parallel>\<^sub>d Q) (s, s')"
      obtain sa' where psa1: "P (s, sa')" and psa2: "ppl s' sa' (tr<s'>-tr<s>) (tr<sa'>-tr<s>) ((BV_progs P) - observables) (CN P)"
        using ppl_ext a2 by blast
      have t1:" ((((\<forall> t < (tr<s'>-tr<s>).  A (trace_state_conc s t )) )) \<longrightarrow> C (trace_state_conc s (tr<s'>-tr<s>)))"
      proof - 
        {
          assume aa1: "(((\<forall> t < (tr<s'>-tr<s>).  A (trace_state_conc s t )) ))"
          have "(((\<forall> t < (tr<sa'>-tr<s>).  A (trace_state_conc s t )) ))"
          proof -
            {
              fix tp
              assume atp1:"tp < (tr<sa'>-tr<s>)"
              have "tr<sa'>-tr<s> = (tr<s'>-tr<s>)\<downharpoonright>P"
                using psa2 ppl_def trace_restriction_prog_def
                by (metis (no_types, lifting))

              then have l1:"\<exists> t'< (tr<s'>-tr<s>). tp = t'\<downharpoonright>P"
                using trace_rest_dist_ext atp1
                by (metis (no_types, lifting) order_less_le trace_restriction_prog_def)
              obtain t' where atp2:"t' < (tr<s'>-tr<s>)" and atp3:"tp = t'\<downharpoonright>P"
                using l1 by blast
              have l2:"\<exists> ss'. tr<ss'> = tr<s>@t' \<and> (P\<parallel>\<^sub>d Q) (s, ss')"
                using atp2 assms(3,4) prefix_closed_paral prefix_closed_def
                by (metis a2 less_list_def)
              obtain ss' where ss1:"tr<ss'> = tr<s>@t'" and ss2:"(P\<parallel>\<^sub>d Q) (s, ss')"
                using l2 by blast
              have l3: "A(trace_state_conc s t' )"
                using aa1 atp2
                by blast
              then have "A(trace_state_conc s (t'\<downharpoonright> P) )"
                using ss1 ss2 non_inter_safe1 assms(2) non_inter_dlchp_comp_def by fastforce
              then have "A(trace_state_conc s tp)"
                using atp3 by blast
              }
              then show ?thesis by auto
            qed
            then have "C (trace_state_conc s (tr<sa'>-tr<s>))"
              by (metis a1 fbox_ac_def commit_dlchp_def psa1)
            then have "C (trace_state_conc s (tr<s'>-tr<s>))"
              using non_inter_safe1 assms(2) psa2 ppl_def
              by (metis (no_types, lifting) a2 non_inter_dlchp_comp_def
                  trace_restriction_prog_def)
          }
          then show ?thesis by auto
        qed
      }
      then show ?thesis 
        using commit_dlchp_def
        by blast
    qed
    moreover have "post_dlchp (P \<parallel>\<^sub>d Q) A F s"
    proof -
      {
      fix s'
      assume a2:"(P\<parallel>\<^sub>d Q) (s, s')"
      obtain sa' where psa1: "P (s, sa')" and psa2: "ppl s' sa' (tr<s'>-tr<s>) (tr<sa'>-tr<s>) ((BV_progs P) - observables) (CN P)"
        using ppl_ext a2 by blast
      have t2:"((\<forall> t \<le> (tr<s'>-tr<s>).  A (trace_state_conc s t)) \<and> \<not> wait<s'> ) \<longrightarrow> F s'"
      proof -
        {
          assume aa2: "(((\<forall> t \<le> (tr<s'>-tr<s>).  A (trace_state_conc s t )) ))" and aa3: "\<not> wait<s'>"
          have "(((\<forall> t \<le> (tr<sa'>-tr<s>).  A (trace_state_conc s t )) ))"
          proof -
            {
              fix tp
              assume atp1:"tp \<le> (tr<sa'>-tr<s>)"
              have "tr<sa'>-tr<s> = (tr<s'>-tr<s>)\<downharpoonright>P"
                using psa2 ppl_def
                by (metis(no_types,lifting) trace_restriction_prog_def)
              then have l1:"\<exists> t'\<le> (tr<s'>-tr<s>). tp = t'\<downharpoonright>P"
                using trace_rest_dist_ext atp1
                by (metis trace_restriction_prog_def)
              obtain t' where atp2:"t'\<le> (tr<s'>-tr<s>)" and atp3:"tp = t'\<downharpoonright>P"
                using l1 by blast
              have l2:"\<exists> ss'. tr<ss'> = tr<s>@t' \<and> (P\<parallel>\<^sub>d Q) (s, ss')"
                using atp2 assms(3,4) prefix_closed_paral prefix_closed_def
                by (metis a2)
              obtain ss' where ss1:"tr<ss'> = tr<s>@t'" and ss2:"(P\<parallel>\<^sub>d Q) (s, ss')"
                using l2 by blast
              have l3: "A(trace_state_conc s t' )"
                using aa2 atp2
                by blast
              then have "A(trace_state_conc s (t'\<downharpoonright> P) )"
                using ss1 ss2 non_inter_safe1 assms(2) non_inter_dlchp_comp_def by fastforce
              then have "A(trace_state_conc s tp)"
                using atp3 by blast
              }
              then show ?thesis by auto
            qed 
            moreover have "\<not> wait<sa'>"
              using aa3 psa2 ppl_def by metis
            moreover have "post_dlchp P A F s"
              using a1 fbox_ac_def by metis
            ultimately have "F sa'"
              using  post_dlchp_def psa1 by metis
            then have "F s'"
              using non_inter_dlchp_comp_def assms(1,2) non_inter_safe3 a2 psa1 psa2 aa3 by blast
          }
          then show ?thesis by blast
        qed
      }
      then show ?thesis
        using post_dlchp_def by blast
    qed
    ultimately have "([(P \<parallel>\<^sub>d Q)]\<^sub>P {A,C} F ) s"
      using fbox_ac_def by metis
  }
  then show ?thesis
    by auto
qed


theorem union_decomp : 
  shows "([(P \<Union>\<^sub>d Q)]\<^sub>P {A,C} F) s = (([P]\<^sub>P {A,C} F) s \<and> ([Q]\<^sub>P {A,C} F) s)"
  apply(simp add: choice_dlchp_def fbox_ac_def)
  by (smt (verit) case_prod_conv commit_dlchp_def post_dlchp_def)

theorem test_box :
  fixes  T ::"(bool, 's::scene_space, 'e::channel) dlCHP_expr"
  assumes "\<not> wait<s>"
  shows "(([(? T)] F)  s) = ((T s  \<longrightarrow> F s) )"
  using assms
  apply(simp add: test_dlchp_def fbox_utp_def)
  apply(pred_simp)
  apply(auto)
  apply (metis rea_vars.surjective)
  apply (metis rea_vars.surjective rea_vars.select_convs(1)
      rea_vars.update_convs(1))
  by (metis rea_vars.surjective rea_vars.select_convs(1) rea_vars.update_convs(1))

theorem godel_ac:
  assumes "\<forall> s'. F s'" "\<forall> s'. C s'"
  shows "([P]\<^sub>P {A,C} F ) s"
  using assms
  by(simp add: fbox_ac_def commit_dlchp_def post_dlchp_def)

theorem seq_comp_ac:
  assumes "prefix_closed P" "prefix_closed Q" "P is R1" "Q is R1" "comm_well_formed A P" "comm_well_formed A Q" "comm_well_formed C P"
  shows "([(P ;;\<^sub>d Q)]\<^sub>P {A,C} F) s = (([P]\<^sub>P {A,C} ([Q]\<^sub>P {A,C} F)) s)"
  proof -
    {
      assume a1:"([(P ;;\<^sub>d Q)]\<^sub>P {A,C} F) s"
      have "(([P]\<^sub>P {A,C} ([Q]\<^sub>P {A,C} F)) s)"
        using a1
        apply(simp add: fbox_ac_def)
        apply(auto)
        subgoal premises prems1
        proof -
            {
              fix s'
              assume p1: "P (s, s')"
              assume t1: "\<forall> t < (tr<s'>-tr<s>). A (trace_state_conc s t )"
              have l1: "(tr<s'>-tr<s>) \<le> (tr<s'>-tr<s>)"
                by blast
              have "tr<s> \<le> tr<s'>"
                using assms(3) p1 Healthy_def R1_def
                by (metis (no_types, lifting) SEXP_def conj_pred_def get_post get_pre inf_apply
                    inf_bool_def)
              then have "(tr<s>@ ( tr<s'> - tr<s>)) = tr<s'>"
                by fastforce
              then have l2:"\<exists> s''. tr<s''> = tr<s'> \<and> wait<s''> \<and> P (s, s'')"
                using prefix_closed_def p1 assms(1) l1
                by metis
              obtain s'' where as1:"tr<s''> = tr<s'>" and as2:"wait<s''>" and as3:"P (s, s'')"
                using l2 by blast

              have "(P ;;\<^sub>d Q)(s, s'')"
                using seq_comp_dlchp_def as2 as3
                by (metis (no_types, lifting) curryD curry_case_prod)
              moreover have "\<forall> t < (tr<s''>-tr<s>). A (trace_state_conc s t)"
                using t1 as1 by presburger 
              ultimately have " C (trace_state_conc s (tr<s''>-tr<s>))"
                using prems1(1) commit_dlchp_def
                by metis
              then have " C (trace_state_conc s (tr<s'>-tr<s>))"
                using as1 by auto
            }
            then show ?thesis
              using commit_dlchp_def
              by (metis) 
          qed
          subgoal premises prems2
        proof-
          {
            fix s0
            assume a1:"P(s, s0)"
            assume a2:"\<not> wait<s0>"
            assume a3:"(\<forall> t \<le> (tr<s0>-tr<s>).  A (trace_state_conc s t))" 
            have "commit_dlchp Q A C s0 \<and> post_dlchp Q A F s0"
            proof -
              have "commit_dlchp Q A C s0"
              proof -
                {
                  fix s'
                  assume as1:"Q(s0,s')"
                  assume as2:"\<forall> t < (tr<s'>-tr<s0>).  A (trace_state_conc s0 t )"
                  have "(P ;;\<^sub>d Q) (s,s')"
                    using as1 a1 a2 seq_comp_dlchp_def
                    by (metis (mono_tags, lifting) old.prod.case) 
                  moreover have "\<forall> t < (tr<s'>-tr<s>).  A (trace_state_conc s t )"
                    using action_comp_le  a1 a3 as1 as2 assms(3,4,5,6) less_list_def by blast
                  ultimately have c1:"C (trace_state_conc s (tr<s'>-tr<s>))"
                    using prems2 commit_dlchp_def
                    by blast
                  then have "C (trace_state_conc s0 (tr<s'>-tr<s0>))"
                  proof -
                    have "(tr<s'>-tr<s>) = (tr<s0> - tr<s>)@ (tr<s'>-tr<s0>)"
                      by (smt (verit, best) Healthy_def R1_def SEXP_def a1 append.assoc append_minus as1 assms(3,4)
                          conj_pred_def diff_add_cancel_left' get_post get_pre inf_apply inf_bool_def
                          plus_list_def)
                    then have "(trace_state_conc s (tr<s'>-tr<s>)) \<approx>\<^sub>S (trace_state_conc s0 (tr<s'>-tr<s0>))   on \<Union>\<^sub>S (FV C)"
                      using action_comp_prev a1 assms(3,7) by blast
                    then show ?thesis
                      using c1 coincidence_eff_term_prop_def  coin_eff_term_1
                      by (smt (verit) FV_Vars order.trans scene_union_equiv set_Vars_scene_space)
                  qed
                }
                then show ?thesis
                  using commit_dlchp_def
                  by blast
              qed
              moreover have "post_dlchp Q A F s0"
              proof -
                {
                  fix s'
                  assume as1:"Q(s0,s')"
                  assume as2:"\<forall> t \<le> (tr<s'>-tr<s0>).  A (trace_state_conc s0 t )"
                  assume as3:"\<not>wait<s'>"
                  have "(P ;;\<^sub>d Q) (s, s')"
                    using as1 a1 a2 seq_comp_dlchp_def
                    by (metis (mono_tags, lifting) old.prod.case) 
                  moreover have "\<forall> t \<le> (tr<s'>-tr<s>).  A (trace_state_conc s t )"
                    using action_comp_leq
                    using a1 a3 as1 as2 assms(3,4,5,6) by blast
                  ultimately have "F s'"
                    using prems2 post_dlchp_def as3 by blast
                }
                then show ?thesis
                  using post_dlchp_def by blast
              qed
              ultimately show ?thesis
                  by auto
              qed
          }
          then show ?thesis
            using post_dlchp_def
            by force
        qed
        done
    } 
    moreover {
      assume a1:"(([P]\<^sub>P {A,C} ([Q]\<^sub>P {A,C} F)) s)"
      have "([(P ;;\<^sub>d Q)]\<^sub>P {A,C} F) s"
        using a1
        apply(simp add: fbox_ac_def)
        apply(auto)
        subgoal premises prems1
      proof -
        {
          fix s'
          assume pq1:"(P ;;\<^sub>d Q) (s, s')"
          assume t1:"(\<forall> t < (tr<s'>-tr<s>).  A (trace_state_conc s t ))"
          have "C (trace_state_conc s (tr<s'>-tr<s>))"
          proof -
            {
              assume p1:"(P(s,s') \<and> wait<s'>)"
              have "C (trace_state_conc s (tr<s'>-tr<s>))"
                using prems1(1) commit_dlchp_def t1 p1
                by metis
            }
            moreover {
              assume q1:"(\<exists> s\<^sub>0. P(s,s\<^sub>0) \<and> \<not>wait<s\<^sub>0> \<and> Q (s\<^sub>0, s'))"
              obtain s0 where s1:"P(s,s0)" and s2:"\<not>wait<s0>" and s3:"Q (s0, s')"
                using q1 by blast
              have tr0:"tr<s0> \<le> tr<s'>"
                  using s3 assms(4) Healthy_def R1_def
                  by (metis (no_types, lifting) SEXP_def conj_pred_def get_post get_pre inf_apply
                      inf_bool_def)
              moreover have tr1:"tr<s> \<le> tr<s0>"
                  using s1 assms(3) Healthy_def R1_def
                  by (metis (no_types, lifting) SEXP_def conj_pred_def get_post get_pre inf_apply
                      inf_bool_def)
              ultimately have tr2:"(tr<s0>-tr<s>) \<le> (tr<s'>-tr<s>)"
                  using minus_cancel_le by blast
              
              {
                assume "tr<s0> = tr<s'>"
                have "C (trace_state_conc s (tr<s'>-tr<s>))"
                using prems1(1) commit_dlchp_def t1 s1 tr2
                by (metis \<open>get\<^bsub>tr\<^esub> s0 = get\<^bsub>tr\<^esub> s'\<close>) 
              }
            moreover {
              assume tr3:"tr<s0> < tr<s'>"
              have "(tr<s0>-tr<s>) < (tr<s'>-tr<s>)"
                using tr3 tr1
                by (metis (no_types, lifting) antisym_conv2 diff_add_cancel_left' order_trans tr0
                    tr2)
              then have t2:"(\<forall> t \<le> (tr<s0>-tr<s>).  A (trace_state_conc s t ))"
                using t1 
                by force
              then have "commit_dlchp Q A C s0"
                using prems1(2) s2 post_dlchp_def
                by (metis (no_types, lifting) s1)
              moreover have "(\<forall> t < (tr<s'>-tr<s0>).  A (trace_state_conc s0 t ))"
              proof -
                {
                  fix t'
                  assume t3:"t' < (tr<s'>-tr<s0>)"
                  obtain t where t4:"t = (tr<s0>-tr<s>)@t'"
                    by blast
                  have "t < (tr<s'> - tr<s>)"
                    using tr3 tr1 t3 t4
                    by (smt (z3) Prefix_Order.prefixE Prefix_Order.same_prefix_prefix append_minus
                        list_concat_minus_list_concat order.strict_trans1 trace_class.less_iff)
                  then have  "A (trace_state_conc s t)"
                    using t1 by blast
                  moreover have "(trace_state_conc s t) \<approx>\<^sub>S (trace_state_conc s0 t') on \<Union>\<^sub>S (FV A)"
                    using action_comp_prev s1 assms(3,5) t4 by blast
                  ultimately have  "A (trace_state_conc s0 t')"
                    using coincidence_eff_term_prop_def coin_eff_term_1
                    by (smt (verit, ccfv_SIG) FV_Vars dual_order.trans scene_union_equiv
                        set_Vars_scene_space) 
                }
                then show ?thesis by blast
              qed
              ultimately have c1:"C (trace_state_conc s0 (tr<s'>-tr<s0>))"
                using commit_dlchp_def s3 by blast
              have "(tr<s'>-tr<s>) = (get\<^bsub>tr\<^esub> s0 - get\<^bsub>tr\<^esub> s) @ (tr<s'>-tr<s0>)"
                by (smt (z3) Healthy_def R1_def SEXP_def append.assoc append_minus assms(3,4) conj_pred_def
                    diff_add_cancel_left' get_post get_pre inf_apply inf_bool_def plus_list_def s1 s3)
              then have c2:"(trace_state_conc s (tr<s'>-tr<s>)) \<approx>\<^sub>S (trace_state_conc s0 (tr<s'>-tr<s0>)) on \<Union>\<^sub>S (FV C)"
                using action_comp_prev s1 assms(3,7) by blast
              have "C (trace_state_conc s (tr<s'>-tr<s>))"
                using c1 c2 coincidence_eff_term_prop_def coin_eff_term_1
                by (smt (verit, ccfv_SIG) FV_Vars dual_order.trans scene_union_equiv
                        set_Vars_scene_space) 
            }
            moreover have "tr<s0> < tr<s'> \<or> tr<s0> = tr<s'>"
              using tr0
              by force
            ultimately have " C (trace_state_conc s (tr<s'> - tr<s>))"
              by blast
          }
            ultimately show ?thesis
              using pq1 seq_comp_dlchp_def
              by (smt (verit, best) old.prod.case)
          qed
          
        }
        then show ?thesis
          using commit_dlchp_def by metis
      qed
      subgoal premises prems2
      proof -
        {
          fix s'
          assume s1: "(P ;;\<^sub>d Q) (s, s')"
          assume t1:"\<forall> t \<le> (tr<s'>-tr<s>).  A (trace_state_conc s t)"
          assume s2:"\<not> wait<s'>"
          have l1:"(\<exists> s\<^sub>0. P(s,s\<^sub>0) \<and> \<not>wait<s\<^sub>0> \<and> Q (s\<^sub>0, s'))"
            using s1 s2 seq_comp_dlchp_def
            by (smt (verit, del_insts) internal_case_prod_conv internal_case_prod_def)
          obtain s0 where ps1:"P(s,s0)" and ps2:"\<not>wait<s0>" and ps3:"Q (s0, s')"
            using l1 by blast
          have t2:"tr<s0> \<le> tr<s'>"
                using ps3 assms(4) Healthy_def R1_def
                by (metis (no_types, lifting) SEXP_def conj_pred_def get_post get_pre inf_apply
                      inf_bool_def)
          have t3:"tr<s> \<le> tr<s0>"
              using ps1 assms(3) Healthy_def R1_def
              by (metis (no_types, lifting) SEXP_def conj_pred_def get_post get_pre inf_apply
                      inf_bool_def)
          have t4:"(tr<s0>-tr<s>) \<le> (tr<s'>-tr<s>)"
            using minus_cancel_le t3 t2  by blast
          then have t4:"(\<forall> t \<le> (tr<s0>-tr<s>).  A (trace_state_conc s t ))"
             using t1
             by force
          then have "post_dlchp Q A F s0"
             using prems2(2) ps2 post_dlchp_def ps1
             by (metis (no_types, lifting))
           moreover have "\<forall> t \<le> (tr<s'>-tr<s0>).  A (trace_state_conc s0 t)"
           proof -
                {
                  fix t'
                  assume t5:"t' \<le> (tr<s'>-tr<s0>)"
                  obtain t where t6:"t = (tr<s0>-tr<s>)@t'"
                    by blast
                  have "t \<le> tr<s'> - tr<s>"
                    using t2 t3 t4 t6 t5
                    by fastforce
                  then have  "A (trace_state_conc s t)"
                    using t1 by blast
                  moreover have "(trace_state_conc s t) \<approx>\<^sub>S (trace_state_conc s0 t') on \<Union>\<^sub>S (FV A)"
                    using action_comp_prev ps1 assms(3,5) t6 by blast
                  ultimately have  "A (trace_state_conc s0 t')"
                    using coincidence_eff_term_prop_def coin_eff_term_1
                    by (smt (verit, ccfv_SIG) FV_Vars dual_order.trans scene_union_equiv
                        set_Vars_scene_space) 
                }
                then show ?thesis by blast
             qed
          ultimately have "F s'"
            using post_dlchp_def  ps3
            by (metis s2)
        }
        then show ?thesis 
          using post_dlchp_def by blast
      qed
      done
    }
    ultimately show ?thesis
      by blast
  qed

lemma empty_ac:
  assumes "CN P = {}" "P is R1" "total P"
  shows "([P]\<^sub>P {A,C} F) s = (C s \<and> (A s \<longrightarrow> [P] F s))"
proof -
  {
    assume a1:"([P]\<^sub>P {A,C} F) s"
    have "C s \<and> (A s \<longrightarrow> [P] F s)"
    proof -
      have tr1:" \<forall> s'. P(s, s') \<longrightarrow> tr<s'> = tr<s>"
        using empty_cn assms  by blast
      then have "(\<forall> s'.  P (s,s') \<longrightarrow> 
              (\<forall> t < (tr<s'>-tr<s>).  A (trace_state_conc s t )))"
        by auto
      then have "(\<forall> s'.  P (s,s') \<longrightarrow> C (trace_state_conc s (tr<s'>-tr<s>)))"
        using a1 commit_dlchp_def 
        by (metis fbox_ac_def)
      then have "(\<forall> s'.  P (s,s') \<longrightarrow> C s)"
        using tr1 trace_state_conc_def
        by (metis diff_add_cancel_left' order_eq_refl plus_list_def tr_vwb_lens vwb_lens_wb
            wb_lens.get_put)
      then have "C s"
        using assms(3) total_def
        by metis
      moreover have "(A s \<longrightarrow> [P] F s)"
      proof -
        have "post_dlchp P A F s"
          using a1 fbox_ac_def
          by metis 
        then have " (\<forall> s'.  P (s,s') \<longrightarrow>  (\<forall> t \<le> (tr<s'>-tr<s>).  (A (trace_state_conc s t)) \<and> \<not> wait<s'> ) \<longrightarrow> F s')"
          using post_dlchp_def
          by (metis order_refl) 
        then have "(A s \<longrightarrow> (\<forall> s'. \<not> wait<s'> \<longrightarrow> P (s,s') \<longrightarrow> F s'))"
          using tr1
          by (simp add: trace_state_conc_def)
        then show ?thesis
          using fbox_utp_def
          by metis
      qed
      ultimately show ?thesis
        by auto
    qed
    }
    moreover {
      assume a1:"C s \<and> (A s \<longrightarrow> [P] F s)"
      have "commit_dlchp P A C s"
        using a1 commit_dlchp_def
        by (metis (no_types, lifting) assms(1,2) diff_add_cancel_left' dual_order.order_iff_strict
            empty_cn plus_list_def tr_vwb_lens trace_state_conc_def vwb_lens.put_eq)
      moreover have  "post_dlchp P A F s"
        using a1 post_dlchp_def fbox_utp_def
        by (metis Prefix_Order.prefixI append.right_neutral append_minus minus_cancel_le tr_vwb_lens
            trace_state_conc_def vwb_lens.axioms(1) wb_lens.get_put)
      ultimately have "([P]\<^sub>P {A,C} F) s"
        using fbox_ac_def by metis
    }
    ultimately show ?thesis
      by blast
  qed
      
      

    
theorem w_ac:
  assumes "([P]\<^sub>P {(True)\<^sub>e,(C \<and> B \<longrightarrow> A )} (True)\<^sub>e) s" "prefix_closed P" 
  shows "([P]\<^sub>P {A,C} F) s \<longrightarrow> ([P]\<^sub>P {B,C} F) s"
proof -
  {
    assume a1:"([P]\<^sub>P {A,C} F) s"
    have "([P]\<^sub>P {B,C} F) s"
    proof -
      {
        fix s'
        assume p1:"P(s, s')"
        have tr1: "(\<forall> t < (tr<s'>-tr<s>).  B (trace_state_conc s t )) \<longrightarrow> (\<forall> t < (tr<s'>-tr<s>).  A (trace_state_conc s t ))"
        proof -
          {
            fix t'
            assume t1:"t' = (tr<s'>-tr<s>)"
            have "(\<forall> t < t'. B (trace_state_conc s  t )) \<longrightarrow> (\<forall> t < t'. A (trace_state_conc s t ))"
              using p1 t1
            proof (induction t' arbitrary: s' rule: rev_induct )
                case Nil
                then show ?case
                  by auto 
              next
                case (snoc a t')
                {
                  assume t2:"\<forall>t. t <  t'@[a] \<longrightarrow> B (trace_state_conc s t)"
                  have b1:"B (trace_state_conc s t')"
                    using t2
                    by (meson Prefix_Order.strict_prefixI')
                  have "t'@[a] = (tr<s'>-tr<s>)"
                    using snoc.prems
                    by force
                  then have "t' < (tr<s'>-tr<s>)"
                    by (metis Prefix_Order.strict_prefixI')
                  then have t3:"\<exists> s''. P(s,s'') \<and> tr<s''> =tr<s>@t'"
                    using assms(2) snoc.prems(1) prefix_closed_def
                    by (metis (no_types, opaque_lifting) less_list_def)
                  obtain s'' where s1:" P(s,s'')" and s2:"tr<s''> =tr<s>@t'"
                    using t3 by blast
                  have t4:"t' = tr<s''> - tr<s>"
                    using s2 by auto
                  moreover have "\<forall>t. t <  t' \<longrightarrow> B (trace_state_conc s t)"
                    using t2
                    by (meson Prefix_Order.strict_prefixI' order.strict_trans)
                  ultimately have  t5:"\<forall>t. t <  t' \<longrightarrow> A (trace_state_conc s t)"
                    using snoc.IH s1 by blast
                  then have c1:"C (trace_state_conc s t')"
                    using a1 commit_dlchp_def fbox_ac_def t4 s1
                    by metis 
                  have "A (trace_state_conc s t')"
                  proof -
                    have "commit_dlchp P (True)\<^sub>e (C \<and> B \<longrightarrow> A ) s"
                      using assms(1) fbox_ac_def
                      by metis
                    then have " (C \<and> B \<longrightarrow> A ) (trace_state_conc s t')"
                      using s1 t4 commit_dlchp_def
                      by (metis SEXP_def)
                    then show ?thesis
                      using c1 b1
                      by (simp add: conj_pred_def impl_pred_def)
                  qed
                  then have "\<forall>t. t <  t'@[a] \<longrightarrow> A (trace_state_conc s t)"
                    using t5
                    by (metis Prefix_Order.prefix_snoc nless_le)
                }
              then show ?case 
                by auto
              qed
          }
          then show ?thesis
            by blast
        qed
        have l0:"(\<forall> t < (tr<s'>-tr<s>).  B (trace_state_conc s t )) \<longrightarrow> C (trace_state_conc s (tr<s'>-tr<s>))"
        proof -
          {
            assume b1:"(\<forall> t < (tr<s'>-tr<s>).  B (trace_state_conc s t ))"
            have "(\<forall> t < (tr<s'>-tr<s>).  A (trace_state_conc s t ))"
              using tr1 b1 by auto
            then have " C (trace_state_conc s (tr<s'>-tr<s>))"
              using a1 fbox_ac_def commit_dlchp_def
              by (metis p1)
          }
          then show ?thesis
            by blast
        qed
        have l1:"((\<forall> t \<le> (tr<s'>-tr<s>). B (trace_state_conc s t)) \<and> \<not> wait<s'> ) \<longrightarrow> F s'"
        proof -
          {
            assume b1:"(\<forall> t \<le> (tr<s'>-tr<s>). B (trace_state_conc s t))"
            assume w1:"\<not> wait<s'>"
            have b2:"B (trace_state_conc s (tr<s'>-tr<s>))"
              using b1 by auto
            have a2:"(\<forall> t < (tr<s'>-tr<s>).  A (trace_state_conc s t ))"
              using tr1 b1 by auto
            then have c1:"C (trace_state_conc s (tr<s'>-tr<s>))"
              using a1 commit_dlchp_def fbox_ac_def p1
              by metis
            have a3:"A (trace_state_conc s (tr<s'>-tr<s>))"
            proof -
              have "commit_dlchp P (True)\<^sub>e (C \<and> B \<longrightarrow> A ) s"
                using assms(1) fbox_ac_def
                by metis
              then have " (C \<and> B \<longrightarrow> A ) (trace_state_conc s (tr<s'>-tr<s>))"
                using p1  commit_dlchp_def
                by (metis SEXP_def)
              then show ?thesis
                using c1 b1
                by (simp add: conj_pred_def impl_pred_def)
            qed
            then have "(\<forall> t \<le> (tr<s'>-tr<s>). A (trace_state_conc s t))"
              using a2
              by (metis nless_le)
            then have "F s'"
              using a1 post_dlchp_def w1 p1
              by (metis fbox_ac_def)
          }
          then show ?thesis
            by auto
        qed
        note local_facts = l0 l1
      }
      then show ?thesis
        using fbox_ac_def commit_dlchp_def  post_dlchp_def
        by metis
    qed
  }
  then show ?thesis
    by auto
qed

theorem k_ac:
  assumes "([P]\<^sub>P {A, (C\<^sub>1 \<longrightarrow> C\<^sub>2)} (F\<^sub>1 \<longrightarrow> F\<^sub>2)) s"
  shows "([P]\<^sub>P {A,C\<^sub>1} F\<^sub>1) s \<longrightarrow> ([P]\<^sub>P {A,C\<^sub>2} F\<^sub>2) s" 
  using assms
  apply(simp add: fbox_ac_def)
  apply(auto)
   apply(simp add:commit_dlchp_def)
   apply(simp add: impl_pred_def)
   apply(simp add:post_dlchp_def)
  apply(simp add: impl_pred_def)
  done



theorem m_ac:
  assumes "\<forall> s. (A\<^sub>2 \<longrightarrow> A\<^sub>1) s" "\<forall> s. (C\<^sub>1 \<longrightarrow> C\<^sub>2) s" "\<forall> s. (F\<^sub>1 \<longrightarrow> F\<^sub>2) s" "prefix_closed P"
  shows "([P]\<^sub>P {A\<^sub>1,C\<^sub>1} F\<^sub>1) s \<longrightarrow> ([P]\<^sub>P {A\<^sub>2,C\<^sub>2} F\<^sub>2) s"
proof -
  have l1:"([P]\<^sub>P {A\<^sub>1,C\<^sub>1} F\<^sub>1) s \<longrightarrow> ([P]\<^sub>P {A\<^sub>1,C\<^sub>2} F\<^sub>2) s" 
    using godel_ac assms(2,3) k_ac
    by (metis (full_types)) 
  have "([P]\<^sub>P {(True)\<^sub>e,((C\<^sub>2 \<and> A\<^sub>2) \<longrightarrow> A\<^sub>1)} (True)\<^sub>e) s"
    using godel_ac assms(1)
    by (smt (verit, ccfv_SIG) impl_pred_def pred_ba.inf_le2 pred_refine_iff taut_True
        taut_def)
  then have "([P]\<^sub>P {A\<^sub>1,C\<^sub>1} F\<^sub>1) s \<longrightarrow> ([P]\<^sub>P {(True)\<^sub>e,((C\<^sub>2 \<and> A\<^sub>2) \<longrightarrow> A\<^sub>1)} (True)\<^sub>e) s"
    by blast
  then show ?thesis
    using l1 w_ac assms(4)
    by blast
qed

theorem and_decomp:
  shows "(([P]\<^sub>P {A\<^sub>1,C\<^sub>1} F\<^sub>1)  \<and> ([P]\<^sub>P {A\<^sub>2,C\<^sub>2} F\<^sub>2) )s = (([P]\<^sub>P {A\<^sub>1,C\<^sub>1} F\<^sub>1) s \<and> ([P]\<^sub>P {A\<^sub>2,C\<^sub>2} F\<^sub>2) s)"
  apply(simp add: fbox_ac_def)
  by (simp add: conj_pred_def)
    

theorem decomp_ac:
  assumes "prefix_closed P"
  shows "([P]\<^sub>P {A, (C\<^sub>1 \<and> C\<^sub>2)} (F\<^sub>1 \<and> F\<^sub>2)) s = (([P]\<^sub>P {A,C\<^sub>1} F\<^sub>1)  \<and> ([P]\<^sub>P {A,C\<^sub>2} F\<^sub>2) )s"  
  apply(simp add: fbox_ac_def commit_dlchp_def conj_pred_def 
      post_dlchp_def)
  by(auto)

theorem paral_decomp:
  assumes "\<forall> s.((A \<and> C\<^sub>1 \<longrightarrow> A\<^sub>1) \<and> (A \<and> C\<^sub>2 \<longrightarrow> A\<^sub>2)) s" "P is R1" "Q is R1" "non_inter_dlchp_comp Q P A\<^sub>1 C\<^sub>1 F\<^sub>1" "non_inter_dlchp_comp P Q A\<^sub>2 C\<^sub>2 F\<^sub>2"  "prefix_closed P" "prefix_closed Q" "([P]\<^sub>P {A\<^sub>1,C\<^sub>1} F\<^sub>1) s" "([Q]\<^sub>P {A\<^sub>2,C\<^sub>2} F\<^sub>2) s" "BV_progs P \<inter> BV_progs Q \<subseteq> observables"
  shows "([(P \<parallel>\<^sub>d Q) ]\<^sub>P {A,(C\<^sub>1 \<and> C\<^sub>2)} (F\<^sub>1 \<and> F\<^sub>2)) s"
proof -
  have "([(P \<parallel>\<^sub>d Q) ]\<^sub>P {(A\<^sub>1 \<and> A\<^sub>2),(C\<^sub>1 \<and> C\<^sub>2)} (F\<^sub>1 \<and> F\<^sub>2)) s"
  proof -
    have  "([(P \<parallel>\<^sub>d Q) ]\<^sub>P {(A\<^sub>1 \<and> A\<^sub>2),(C\<^sub>1)} (F\<^sub>1)) s"
    proof -
      have "([(P \<parallel>\<^sub>d Q) ]\<^sub>P {(A\<^sub>1),(C\<^sub>1)} (F\<^sub>1)) s"
        using assms(2,4,6,7,8) parallel_injection by blast
      moreover have "\<forall> s. ((A\<^sub>1 \<and> A\<^sub>2) \<longrightarrow> A\<^sub>1) s"
        by pred_simp
      ultimately show ?thesis
        using m_ac assms(6,7) prefix_closed_paral
        by (smt (verit, ccfv_SIG) impl_pred_def pred_ba.inf_le1 pred_refine_iff)
    qed
    moreover have  "([(P \<parallel>\<^sub>d Q) ]\<^sub>P {(A\<^sub>1 \<and> A\<^sub>2),(C\<^sub>2)} (F\<^sub>2)) s"
    proof -
      have "([(P \<parallel>\<^sub>d Q) ]\<^sub>P {(A\<^sub>2),(C\<^sub>2)} (F\<^sub>2)) s"
        using assms(3,5,6,7,9, 10) parallel_injection paral_comm
        by metis 
      then show ?thesis
        using m_ac assms(6,7) prefix_closed_paral
        by (smt (verit, ccfv_SIG) conj_pred_def impl_pred_def inf1E)
    qed 
    ultimately show ?thesis
      using decomp_ac assms(6,7) prefix_closed_paral and_decomp by blast
  qed
  moreover have "([(P \<parallel>\<^sub>d Q) ]\<^sub>P {(True)\<^sub>e,(A \<and> (C\<^sub>1 \<and> C\<^sub>2) \<longrightarrow> (A\<^sub>1 \<and> A\<^sub>2))} (True)\<^sub>e) s"
  proof -
    have "\<forall> s. (A \<and> (C\<^sub>1 \<and> C\<^sub>2) \<longrightarrow> (A\<^sub>1 \<and> A\<^sub>2)) s"
      using assms(1)
      by (simp add: conj_pred_def impl_pred_def inf1I)
    then show ?thesis
      using godel_ac assms(1)
      by (metis (no_types, lifting) ext taut_True taut_def)
  qed
  ultimately show ?thesis
    using w_ac assms(6,7) prefix_closed_paral
    by (metis pred_ba.inf_commute)
qed




theorem loop_ac:
  assumes "prefix_closed P" "P is R1" "comm_well_formed A P" "comm_well_formed C P" "total P"
  shows "([(P\<^sup>d)]\<^sub>P {A,C} F) s = (([ P ^\<^sup>d 0]\<^sub>P {A,C} F) s \<and> (([P ]\<^sub>P {A,C} ([(P\<^sup>d)]\<^sub>P {A,C} F)) s))"
proof -
  have l0:"([(P\<^sup>d)]\<^sub>P {A,C} F) s = ([((P ^\<^sup>d 0) \<Union>\<^sub>d (P ;;\<^sub>d (P\<^sup>d)))]\<^sub>P {A,C} F) s"
    using repetition_seq_decomp
    by metis
  have l1:"... = (([ P ^\<^sup>d 0]\<^sub>P {A,C} F) s \<and> (([(P ;;\<^sub>d (P\<^sup>d))]\<^sub>P {A,C} F) s))"
    using union_decomp
    by metis
  have l2:"... = (([ P ^\<^sup>d 0]\<^sub>P {A,C} F) s \<and> (([P ]\<^sub>P {A,C} ([(P\<^sup>d)]\<^sub>P {A,C} F)) s))"
    using assms seq_comp_ac comm_well_formed_loop
    using prefix_closed_loop r1_loop by blast
  show ?thesis
    using l0 l1 l2 by blast
qed



theorem I_ac:
  assumes "prefix_closed P" "P is R1" "comm_well_formed A P" "comm_well_formed C P" "total P" "waits_wf P"
  shows  "([(P\<^sup>d)]\<^sub>P {A,C} F) s =  (([ P ^\<^sup>d 0]\<^sub>P {A,C} F) s \<and> ([P\<^sup>d ]\<^sub>P {A, (True)\<^sub>e}  (F  \<longrightarrow> ([P]\<^sub>P {A,C} F)) )  s)"
proof -
  {
    assume lhs: "([(P\<^sup>d)]\<^sub>P {A,C} F) s"
    have l0:"([((P ^\<^sup>d 0) \<Union>\<^sub>d (P ;;\<^sub>d (P\<^sup>d)))]\<^sub>P {A,C} F) s"
      using repetition_seq_decomp lhs
      by metis
    then have l1:"(([ P ^\<^sup>d 0]\<^sub>P {A,C} F) s \<and> (([(P ;;\<^sub>d (P\<^sup>d))]\<^sub>P {A,C} F) s))"
      using union_decomp
      by metis
    then have l2:" ([ P ^\<^sup>d 0]\<^sub>P {A,C} F) s \<and> ([(P\<^sup>d) ;;\<^sub>d P]\<^sub>P {A,C} F) s"
      using loop_comm_ac assms(5,6) by metis
    then have "([ P ^\<^sup>d 0]\<^sub>P {A,C} F) s \<and> ([P\<^sup>d ]\<^sub>P {A,C}  (([P]\<^sub>P {A,C} F)) )  s"
      using  seq_comp_ac assms
      by (metis comm_well_formed_loop prefix_closed_loop r1_loop) 
    then have "(([ P ^\<^sup>d 0]\<^sub>P {A,C} F) s \<and> ([P\<^sup>d ]\<^sub>P {A,(True)\<^sub>e}  (F  \<longrightarrow> ([P]\<^sub>P {A,C} F)) )  s)"
      using m_ac assms(1)
      by (simp add: commit_dlchp_def fbox_ac_def impl_pred_def post_dlchp_def)
  }

  moreover {
    assume rhs:"(([ P ^\<^sup>d 0]\<^sub>P {A,C} F) s \<and> ([P\<^sup>d ]\<^sub>P {A, (True)\<^sub>e}  (F  \<longrightarrow> ([P]\<^sub>P {A,C} F)) )  s)"
    {
    fix n
    have rhs0_commit: "commit_dlchp ( P ^\<^sup>d 0) A C s"
      using rhs fbox_ac_def by metis
    have rhs0_post: "post_dlchp ( P ^\<^sup>d 0) A F s"
      using rhs fbox_ac_def by metis
    have rhsn_commit: "commit_dlchp (P ^\<^sup>d n) A (True)\<^sub>e s"
      using rhs fbox_ac_def loop_dlchp_def
      by (simp add: commit_dlchp_def)
    have rhsn_post: "post_dlchp (P ^\<^sup>d n) A (F  \<longrightarrow> ([P]\<^sub>P {A,C} F)) s"
      using rhs fbox_ac_def loop_dlchp_def
      by (smt (verit, ccfv_SIG) SUP1_I UNIV_I post_dlchp_def)

    have "([ P ^\<^sup>d n]\<^sub>P {A,C} F) s"
    proof(induction n)
      case 0
      then show ?case
      using fbox_ac_def rhs0_commit rhs0_post by metis
    next
      case (Suc n)
      have commit_ind:"commit_dlchp ( P ^\<^sup>d n) A C s"
        using Suc fbox_ac_def by metis
      have post_ind:"post_dlchp ( P ^\<^sup>d n) A F s"
        using Suc fbox_ac_def by metis

      have commit:"commit_dlchp ( P ^\<^sup>d Suc n) A C s"
      proof -
        {
          fix s'
          assume is_run: "(P ^\<^sup>d Suc n) (s, s')"
          assume tr_ass: "(\<forall> t < (tr<s'>-tr<s>).  A (trace_state_conc s t ))"  

          have is_loop: "(P\<^sup>d) (s, s')"
            using is_run loop_dlchp_def
            by (metis SUP1_I UNIV_I)

          have seq_decomp: "(P ;;\<^sub>d (P ^\<^sup>d  n)) (s, s')"
            using is_run upower_dlchp.simps(2) by auto

          hence is_loop_decomp:"(P ;;\<^sub>d (P\<^sup>d)) (s, s')"
            using loop_dlchp_def
            by (smt (verit, ccfv_SIG) SUP1_I UNIV_I curryD curryI curry_case_prod
                seq_comp_dlchp_def)

          have "C (trace_state_conc s (tr<s'>-tr<s>))"
          proof (cases "wait<s>")
            case True
            note wait_start = True
            have "waits_wf (P ^\<^sup>d Suc n)"
              using waits_wf_power assms(6) by metis
            
            hence eq_states:"s' = s"
              using waits_wf_def is_run skip_def wait_start
              by (metis (mono_tags, lifting) old.prod.case) 
            moreover have "waits_wf (P ^\<^sup>d 0)"
              using assms(6) waits_wf_power by metis
            ultimately have  is_run0:"(P ^\<^sup>d 0) (s, s')"
              using skip_def waits_wf_def
              using \<open>waits_wf (P ^\<^sup>d Suc n)\<close> is_run wait_start by blast 
            then show ?thesis
              using tr_ass rhs0_commit commit_dlchp_def by metis
          next
            case False
            note nwaits_start = False
            then show ?thesis 
            proof -
              obtain s'' where is_runs2:"((P ^\<^sup>d n) ;;\<^sub>d P) (s, s'')" and tr_eq: "tr<s'> = tr<s''>"
                using loop_comm_ac_prev_power_nwait assms(5,6) seq_decomp nwaits_start by metis

              have tr_s2:"(\<forall> t < (tr<s''>-tr<s>).  A (trace_state_conc s t ))"
                using tr_ass tr_eq by auto

              have seq_decomp2:"((P ^\<^sup>d n) (s, s'') \<and> wait<s''>) \<or> (\<exists> s0. (P ^\<^sup>d n) (s, s0) \<and> \<not>wait<s0> \<and> P(s0,s''))"
                using is_runs2 by (simp add: seq_comp_dlchp_def)

              from seq_decomp2 consider 
                  (left) "(P ^\<^sup>d n) (s, s'')" "wait<s''>"
                  | (right) s0 where "(P ^\<^sup>d n) (s, s0)" "\<not>wait<s0>" "P(s0,s'')"
                by auto 
              
              then show ?thesis
              proof cases
                case left
                have "C (trace_state_conc s (get\<^bsub>tr\<^esub> s'' - get\<^bsub>tr\<^esub> s))"
                  using Suc fbox_ac_def commit_dlchp_def left(1) tr_s2
                  by metis
                then show ?thesis 
                  using tr_eq by auto
              next
                case right

                have "tr<s0> \<le> tr<s''>"
                  using right(3) assms(2)
                  by (simp add: R1_by_refinement pred_refine_iff subst_app_def subst_ext_def)
                then have tr_leq_right:"get\<^bsub>tr\<^esub> s0 - get\<^bsub>tr\<^esub> s \<le> get\<^bsub>tr\<^esub> s'' - get\<^bsub>tr\<^esub> s"
                  by (metis Prefix_Order.Nil_prefix minus_cancel minus_cancel_le not_le_minus
                          trace_class.diff_cancel)

                from tr_leq_right consider
                  (eq) "get\<^bsub>tr\<^esub> s0 - get\<^bsub>tr\<^esub> s = get\<^bsub>tr\<^esub> s'' - get\<^bsub>tr\<^esub> s"
                  | (le) "get\<^bsub>tr\<^esub> s0 - get\<^bsub>tr\<^esub> s < get\<^bsub>tr\<^esub> s'' - get\<^bsub>tr\<^esub> s"
                  by fastforce

                then show ?thesis
                proof(cases)
                  case eq
                  then have "\<forall>t. t < get\<^bsub>tr\<^esub> s0 - get\<^bsub>tr\<^esub> s \<longrightarrow> A (trace_state_conc s t)"
                    using tr_s2
                    by presburger
                  then have "C (trace_state_conc s (get\<^bsub>tr\<^esub> s0 - get\<^bsub>tr\<^esub> s))"
                    using Suc fbox_ac_def commit_dlchp_def right(1) 
                    by metis
                  then show ?thesis 
                    using eq tr_eq by argo
                next
                  case le
                  then have tr_ass_s2:"\<forall>t. t \<le> get\<^bsub>tr\<^esub> s0 - get\<^bsub>tr\<^esub> s \<longrightarrow> A (trace_state_conc s t)"
                    using tr_s2
                    by auto
                  moreover have "(P\<^sup>d) (s, s0)"
                    using right(1) loop_dlchp_def
                    by (metis Sup1_I range_eqI)
                  ultimately have  post_rhs:"(F  \<longrightarrow> ([P]\<^sub>P {A,C} F)) s0"
                    using rhsn_post post_dlchp_def right(2)
                    by (metis fbox_ac_def rhs)

                  have f_s0:"F s0"
                    using Suc fbox_ac_def post_dlchp_def right(1,2) tr_ass_s2
                    by metis

                  have "([P]\<^sub>P {A,C} F) s0"
                    using post_rhs f_s0
                    by (simp add: impl_pred_def)

                 
                  moreover have "(\<forall> t < (tr<s''>-tr<s0>).  A (trace_state_conc s0 t ))"
                  proof-
                    { 
                      fix t
                      assume tr_temp0:"t < (tr<s''>-tr<s0>)"
                      have tr_temp1:"tr<s0> \<le> tr<s''>"
                        using assms(2) right(3)
                        by (simp add: \<open>get\<^bsub>tr\<^esub> s0 \<le> get\<^bsub>tr\<^esub> s''\<close>)
                      have tr_temp2:"tr<s> \<le> tr<s0>"
                        using right(1) assms(2) r1_power
                        by (metis (mono_tags, lifting) Healthy_def R1_def SEXP_def conj_pred_def get_post get_pre
                            inf_apply inf_bool_def)
                      obtain t' where tr_temp3:"t'=(tr<s0> -tr<s>)@t"
                        using tr_temp0 tr_temp1 tr_temp2
                        by presburger

                      have "t' < (tr<s''> - tr<s>)"
                        using less_list_def tr_temp0 tr_temp1 tr_temp2 tr_temp3 by fastforce
                      hence at_temp:"A (trace_state_conc s t')"
                        using tr_s2 by auto

                      moreover have "(trace_state_conc s t') \<approx>\<^sub>S (trace_state_conc s0 t) on (\<Union>\<^sub>S (FV A))"
                        using action_comp_prev tr_temp3 assms(3) right(1) assms(2) r1_power
                        using \<open>P\<^sup>d (s, s0)\<close> assms(5) comm_well_formed_loop r1_loop by blast

                      ultimately have "A (trace_state_conc s0 t)"
                        using coincidence_eff_term_prop_def coin_eff_term_1
                        by (smt (verit, best) FV_Vars order_trans scene_union_equiv set_Vars_scene_space)
                    }
                    then show ?thesis
                      by auto
                  qed
                  ultimately have c1_right:"C (trace_state_conc s0 (tr<s''>-tr<s0>))"
                    using fbox_ac_def commit_dlchp_def right(3) by metis
                  have "(tr<s''>-tr<s>) = (get\<^bsub>tr\<^esub> s0 - get\<^bsub>tr\<^esub> s) @ (tr<s''>-tr<s0>)"
                    using right(1,3) assms(2) r1_power
                    by (smt (verit, ccfv_threshold) Healthy_def R1_def SEXP_def append.assoc append_minus
                        conj_pred_def diff_add_cancel_left' get_post get_pre inf_apply inf_bool_def
                        plus_list_def)
                  then have c2:"(trace_state_conc s (tr<s''>-tr<s>)) \<approx>\<^sub>S (trace_state_conc s0 (tr<s''>-tr<s0>)) on \<Union>\<^sub>S (FV C)"
                    using action_comp_prev assms(2,4) right(3)
                    by (metis \<open>P\<^sup>d (s, s0)\<close> assms(5) comm_well_formed_loop r1_loop)
                  then have "C (trace_state_conc s (tr<s''>-tr<s>))"
                    using  coincidence_eff_term_prop_def coin_eff_term_1 c1_right
                     by (smt (verit, best) FV_Vars order_trans scene_union_equiv set_Vars_scene_space)

                  then show ?thesis 
                    using tr_eq
                    by presburger
                qed
              qed
            qed
          qed
        }
        then show ?thesis
          using commit_dlchp_def
          by blast
      qed

      moreover have "post_dlchp (P ^\<^sup>d Suc n) A F s"
      proof -
        {
          fix s'
          assume is_run: "(P ^\<^sup>d Suc n) (s, s')"
          assume tr_ass: "(\<forall> t \<le> (tr<s'>-tr<s>).  A (trace_state_conc s t ))"  
          assume nwaits_end: "\<not> wait<s'>"

          have waits_wf_ind: "waits_wf (P ^\<^sup>d Suc n)"
            using assms(6) waits_wf_power
            by blast
          hence nwaits_start: "\<not> wait<s>"
            by (metis (mono_tags, lifting) is_run nwaits_end prod.simps(2) skip_def
                waits_wf_def)
            
  
          have is_loop: "(P\<^sup>d) (s, s')"
            using is_run loop_dlchp_def
            by (metis SUP1_I UNIV_I)

          have seq_decomp: "(P ;;\<^sub>d (P ^\<^sup>d  n)) (s, s')"
            using is_run upower_dlchp.simps(2) by auto

          hence seq_comm:"((P ^\<^sup>d  n) ;;\<^sub>d P) (s, s')"
            using power_comm_nwait nwaits_start nwaits_end
            by blast

          hence seq_comm_decomp:"((P ^\<^sup>d  n)  (s, s') \<and> wait<s'>) \<or> (\<exists> s0. (P ^\<^sup>d  n)  (s, s0) \<and> \<not>wait<s0> \<and> P(s0,s'))"
            using seq_comp_dlchp_def
            by (smt (verit, ccfv_SIG) internal_case_prod_conv internal_case_prod_def)

          hence nwait_seq:"(\<exists> s0. (P ^\<^sup>d  n)  (s, s0)  \<and> \<not>wait<s0> \<and> P(s0,s'))"
            using nwaits_end by auto

          obtain s0 where right1:"(P ^\<^sup>d  n)  (s, s0)" and right2:"\<not>wait<s0>" and right3:"P(s0,s')"
            using nwait_seq by blast

          have  "tr<s0> \<le> tr<s'>"
            using right3 assms(2) Healthy_def R1_def
            by (simp add: R1_by_refinement pred_refine_iff subst_app_def subst_ext_def)

          hence tr_leqs0:"(tr<s0>-tr<s>) \<le> (tr<s'>-tr<s>)"
            by (metis least_zero minus_cancel_le not_le_minus)
            
          hence tr_ass_s0:"(\<forall> t \<le> (tr<s0>-tr<s>).  A (trace_state_conc s t ))"  
            using tr_ass
            by auto
          moreover have "(P\<^sup>d)  (s, s0)"
            using right1 loop_dlchp_def
            by (metis Sup1_I range_eqI)
          ultimately have  post_rhs:"(F  \<longrightarrow> ([P]\<^sub>P {A,C} F)) s0"
            using rhsn_post post_dlchp_def right2
            by (metis fbox_ac_def rhs)

          have f_s0:"F s0"
            using Suc fbox_ac_def post_dlchp_def right1 right2 tr_ass_s0
            by metis

          hence "([P]\<^sub>P {A,C} F) s0"
            using post_rhs 
            by (simp add: impl_pred_def)
          

          moreover have "(\<forall> t \<le> (tr<s'>-tr<s0>).  A (trace_state_conc s0 t ))"
          proof-
            { 
              fix t
              assume tr_temp0:"t \<le> (tr<s'>-tr<s0>)"
              have tr_temp1:"tr<s0> \<le> tr<s'>"
                using assms(2) right3
                by (simp add: \<open>get\<^bsub>tr\<^esub> s0 \<le> get\<^bsub>tr\<^esub> s'\<close>)
              have tr_temp2:"tr<s> \<le> tr<s0>"
                using right1 assms(2) r1_power
                by (metis (mono_tags, lifting) Healthy_def R1_def SEXP_def conj_pred_def get_post get_pre
                    inf_apply inf_bool_def)
              obtain t' where tr_temp3:"t'=(tr<s0> -tr<s>)@t"
                using tr_temp0 tr_temp1 tr_temp2
                by presburger

              have "t' \<le> (tr<s'> - tr<s>)"
                using less_list_def tr_temp0 tr_temp1 tr_temp2 tr_temp3 by fastforce
              hence at_temp:"A (trace_state_conc s t')"
                using tr_ass by auto

              moreover have "(trace_state_conc s t') \<approx>\<^sub>S (trace_state_conc s0 t) on (\<Union>\<^sub>S (FV A))"
                using action_comp_prev tr_temp3 assms(3) right1 assms(2)
                by (metis (mono_tags, lifting) Sup1_I assms(5) comm_well_formed_loop loop_dlchp_def r1_loop
                    range_eqI)

              ultimately have "A (trace_state_conc s0 t)"
                using coincidence_eff_term_prop_def coin_eff_term_1
                by (smt (verit, best) FV_Vars order_trans scene_union_equiv set_Vars_scene_space)
            }
            then show ?thesis
              by auto
          qed 

          ultimately have "F s'"
            using fbox_ac_def post_dlchp_def nwaits_end right3
            by metis
        }
        thus ?thesis
          using post_dlchp_def
          by metis 
      qed
          
      ultimately show ?case
          using fbox_ac_def
          by metis 
      qed
    }
    then have "([ P\<^sup>d ]\<^sub>P {A,C} F) s"
      using loop_pre_from_all_powers
      by blast
  }

  ultimately show ?thesis
    by metis
qed


theorem inductive_ac:
  assumes "\<forall> s'. (F s'  \<longrightarrow> ([P]\<^sub>P {A,C} F) s')  " "\<not> wait<s>"  "prefix_closed P" "P is R1" "comm_well_formed A P" "comm_well_formed C P" "total P" "waits_wf P"
  shows "(F \<and> C  \<longrightarrow> ([P\<^sup>d]\<^sub>P {A,C} F))   s"
proof -
  have l0:"(F \<and> C \<longrightarrow> (C \<and> (A \<longrightarrow> ( (True)\<^sub>e \<longrightarrow> F)))) s"
    by (metis (no_types, lifting) SEXP_def Vars_UTP.wlp_conj impl_pred_def wlp_skip_r)

  hence "(F \<and> C \<longrightarrow> ([P ^\<^sup>d 0]\<^sub>P {A,C} F)) s"
  proof-
    have "\<forall> s s'. (? (True)\<^sub>e) (s, s') \<longrightarrow> tr<s'> - tr<s> = []"
      by(simp add: test_dlchp_def)
   
    hence "traces (P ^\<^sup>d 0) = {[]}"
      apply(simp add: traces_def)
      apply(auto)
      by (metis total_def total_test)
  
    hence "CN (P ^\<^sup>d 0) = {}"
      by(simp add: CN_def channels_from_trace_def)
  
    moreover have "(P ^\<^sup>d 0) is R1"
      using r1_test by simp
  
    ultimately show ?thesis
      using empty_ac test_box upower_dlchp.simps(1) assms(2)
      by (metis conj_pred_def impl_pred_def inf1E total_test)
  qed


  moreover have "(C \<and> F \<longrightarrow>([P\<^sup>d ]\<^sub>P {A, (True)\<^sub>e}  (F  \<longrightarrow> ([P]\<^sub>P {A,C} F)) ))  s"
    using godel_ac assms(1)
    by (metis (no_types, lifting) SEXP_def impl_pred_def)

  ultimately show ?thesis
    using I_ac assms(3,4,5,6,7,8)
    by (metis impl_pred_def pred_ba.inf_commute)
qed

theorem send_ac:
  shows "([(c!\<^sub>de)]\<^sub>P {A, C}  F) s \<longleftrightarrow> ([?(True)\<^sub>e]\<^sub>P {A, C}([(c!\<^sub>de)] ([?(True)\<^sub>e]\<^sub>P {A, C} F))) s "
proof -
  {
    assume lhs:"([(c!\<^sub>de)]\<^sub>P {A, C}  F) s"
    
    have commit_lhs:"commit_dlchp (c!\<^sub>de) A C s"
      using lhs fbox_ac_def by metis

    have post_lhs:"post_dlchp (c!\<^sub>de) A F s"
      using lhs fbox_ac_def by metis

    have commit_rhs: "commit_dlchp (?(True)\<^sub>e) A C s"
    proof -
      {
        fix s'
        assume is_run: "(?(True)\<^sub>e) (s,s')"
        assume tr_ass: "\<forall> t < (tr<s'>-tr<s>).A (trace_state_conc s t )"


        obtain s'' where is_run_send: "(c!\<^sub>de) (s, s'')" and empty_run:"tr<s> = tr<s''>"
          by (metis total_def total_send)


        have sub_trace_send:"\<forall> t < (tr<s''>-tr<s>).A (trace_state_conc s t )"
          using tr_ass empty_run
          by simp

        hence rhs_comm_send: "C (trace_state_conc s (tr<s''> - tr<s>))"
          using is_run_send tr_ass commit_lhs commit_dlchp_def
          by (metis)

        moreover have "tr<s'> = tr<s>"
          using is_run 
          by (auto simp add: test_dlchp_def)

        ultimately have  "C (trace_state_conc s (tr<s'> - tr<s>))"
          using empty_run
          by force
      }
      
      thus ?thesis
        using commit_dlchp_def
        by blast
    qed


    moreover have "post_dlchp  (?(True)\<^sub>e) A ([(c!\<^sub>de)] ([?(True)\<^sub>e]\<^sub>P {A, C} F)) s"
    proof -
      {
        fix s'
        assume is_run: "(?(True)\<^sub>e) (s,s')"
        assume not_wait:"\<not> wait<s'>"
        assume tr_ass: "\<forall> t \<le> (tr<s'>-tr<s>).A (trace_state_conc s t )" 

        have eq_states:"s' = s"
          using is_run not_wait
          by (auto simp add:test_dlchp_def)

        hence As: "A s"
          using tr_ass
          by (simp add: trace_state_conc_def)


        have rhs_post:"([(c!\<^sub>de)] ([?(True)\<^sub>e]\<^sub>P {A, C} F)) s'"
        proof -
            {
              fix s''
              assume is_run_send: " (c!\<^sub>de) (s',s'')"
              assume not_wait2: "\<not> wait<s''>"

              have is_run_s:  " (c!\<^sub>de) (s,s'')"
                using is_run_send eq_states by auto

              have "([?(True)\<^sub>e]\<^sub>P {A, C} F) s''"
              proof -
                have "commit_dlchp (?(True)\<^sub>e) A C s''"
                proof -
                  {
                    fix s'''
                    assume is_run3: "(?(True)\<^sub>e) (s'', s''')"
                    assume tr_ass2: "\<forall> t < (tr<s'''>-tr<s''>).A (trace_state_conc s'' t )"

                    have "s'' \<approx>\<^sub>S s on -(\<Union>\<^sub>S {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>, \<lbrakk>wait\<rbrakk>\<^sub>\<sim>})"
                      using eq_states is_run_send send_vars
                      by blast

                    moreover have   "(trace_state_conc s (tr<s''>-tr<s>)) \<approx>\<^sub>S s on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                      using trace_state_conc_def
                      by (metis (no_types, lifting) Sup_Vars_top Sup_scene_closed idem_scene_uminus insert_absorb
                          scene_equiv_refl scene_minus2 scene_space_equiv_union scene_space_uminus scene_union_compl
                          scene_union_put_preserved subset_insertI tr_is_var tr_vwb_lens vwb_impl_idem_scene)


                    moreover have "s'' \<approx>\<^sub>S (trace_state_conc s'' (tr<s'''>-tr<s''>)) on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                      using trace_state_conc_def
                      by (metis Sup_scene_closed idem_scene_space order_refl scene_equiv_refl scene_equiv_sym scene_minus2
                          scene_union_put_preserved tr_is_var tr_vwb_lens)

                    ultimately have "(trace_state_conc s'' (tr<s'''>-tr<s''>)) \<approx>\<^sub>S (trace_state_conc s (tr<s''>-tr<s>)) on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                      by (smt (verit, ccfv_threshold) Scenes_extra.scene_equiv_get_eq Un_insert_right bot_set_def eq_states
                          insert_Diff insert_Diff1 insert_is_Un insert_subset not_wait not_wait2 para_obs_def para_obs_is_vars
                          scene_agreement_neg_comp scene_equiv_def scene_minus2 scene_override_overshadow_right
                          scene_union_put_preserved set_Vars_scene_space singletonI ss_clat.weak_sup_of_singleton subset_insertI
                          tr_vwb_lens trace_state_conc_def wait_vwb_lens)
                    moreover have  "(trace_state_conc s'' (tr<s'''>-tr<s''>)) \<approx>\<^sub>S (trace_state_conc s (tr<s''>-tr<s>)) on \<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                    proof -
                      have "tr<s''> = tr<s'''>"
                        using is_run3
                        by(auto simp add: test_dlchp_def)

                      hence "tr<s''> = tr<s''>@ (tr<s'''>-tr<s''>)"
                        by auto

                      moreover have "tr<s''> = tr<s>@ (tr<s''>-tr<s>)"
                        using is_run_send eq_states out_dlchp_def
                        by (metis (lifting) list_singleton_iff minus_list_def not_Cons_self2 not_wait2 prefix_concat_minus
                            send_trace_length)

                      ultimately show ?thesis
                        using trace_state_conc_def
                        by (metis Scenes_extra.scene_equiv_get_eq tr_vwb_lens vwb_lens_def wb_lens.axioms(1)
                            weak_lens.put_get)
                    qed

                    ultimately have tr_conc_eq:"(trace_state_conc s'' (tr<s'''>-tr<s''>)) = (trace_state_conc s (tr<s''>-tr<s>))"
                      by (metis scene_equiv_def scene_equiv_sym scene_override_commute tr_vwb_lens
                          vwb_impl_idem_scene)


                    have tr_s:"\<forall> t < (tr<s''>-tr<s>).A (trace_state_conc s t )"
                      using eq_states is_run_send tr_ass is_run send_trace_length
                      by (smt (verit) Prefix_Order.prefixE Prefix_Order.prefix_snoc append_minus case_prodE get_fst_lens
                          get_snd_lens list_concat_minus_list_concat minus_gr_zero_iff nless_le not_le_minus not_wait2
                          out_dlchp_def)


                    hence  "C (trace_state_conc s (tr<s''>-tr<s>))"
                      using commit_lhs commit_dlchp_def is_run_s by metis

                    hence "C (trace_state_conc s'' (tr<s'''>-tr<s''>))"
                      using tr_conc_eq by auto
                  }
                  then show ?thesis
                    using commit_dlchp_def by blast
                qed

                moreover have "post_dlchp (?(True)\<^sub>e) A F s''"
                proof -
                  {
                    fix s'''
                    assume is_run3:"(?(True)\<^sub>e) (s'', s''')"
                    assume not_wait_end: "\<not> wait<s'''>"
                    assume tr_ass: "(\<forall> t \<le> (tr<s'''>-tr<s''>).  A (trace_state_conc s'' t))"

              
                    have post_eq_states:"s'' = s'''"
                      using is_run3 not_wait_end
                      by (auto simp add: test_dlchp_def)

                    hence is_run_final:"(c!\<^sub>de) (s, s''')"
                      using is_run_s by auto

                    have As2:"A s''"
                      using post_eq_states tr_ass
                      by (simp add: trace_state_conc_def)

                    have "s'' \<approx>\<^sub>S s on -(\<Union>\<^sub>S {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>, \<lbrakk>wait\<rbrakk>\<^sub>\<sim>})"
                      using eq_states is_run_send send_vars
                      by blast

                    moreover have   "(trace_state_conc s (tr<s''>-tr<s>)) \<approx>\<^sub>S s on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                      using trace_state_conc_def
                      by (metis (no_types, lifting) Sup_Vars_top Sup_scene_closed idem_scene_uminus insert_absorb
                          scene_equiv_refl scene_minus2 scene_space_equiv_union scene_space_uminus scene_union_compl
                          scene_union_put_preserved subset_insertI tr_is_var tr_vwb_lens vwb_impl_idem_scene)


                    moreover have "s'' \<approx>\<^sub>S (trace_state_conc s'' (tr<s'''>-tr<s''>)) on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                      using trace_state_conc_def
                      by (metis Sup_scene_closed idem_scene_space order_refl scene_equiv_refl scene_equiv_sym scene_minus2
                          scene_union_put_preserved tr_is_var tr_vwb_lens)

                    ultimately have "(trace_state_conc s'' (tr<s'''>-tr<s''>)) \<approx>\<^sub>S (trace_state_conc s (tr<s''>-tr<s>)) on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                      by (smt (verit, ccfv_threshold) Scenes_extra.scene_equiv_get_eq Un_insert_right bot_set_def eq_states
                          insert_Diff insert_Diff1 insert_is_Un insert_subset not_wait not_wait2 para_obs_def para_obs_is_vars
                          scene_agreement_neg_comp scene_equiv_def scene_minus2 scene_override_overshadow_right
                          scene_union_put_preserved set_Vars_scene_space singletonI ss_clat.weak_sup_of_singleton subset_insertI
                          tr_vwb_lens trace_state_conc_def wait_vwb_lens)
                    moreover have  "(trace_state_conc s'' (tr<s'''>-tr<s''>)) \<approx>\<^sub>S (trace_state_conc s (tr<s''>-tr<s>)) on \<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                    proof -
                      have "tr<s''> = tr<s'''>"
                        using is_run3
                        by(auto simp add: test_dlchp_def)

                      hence "tr<s''> = tr<s''>@ (tr<s'''>-tr<s''>)"
                        by auto

                      moreover have "tr<s''> = tr<s>@ (tr<s''>-tr<s>)"
                        using is_run_send eq_states out_dlchp_def
                        by (metis (lifting) list_singleton_iff minus_list_def not_Cons_self2 not_wait2 prefix_concat_minus
                            send_trace_length)

                      ultimately show ?thesis
                        using trace_state_conc_def
                        by (metis Scenes_extra.scene_equiv_get_eq tr_vwb_lens vwb_lens_def wb_lens.axioms(1)
                            weak_lens.put_get)
                    qed

                    ultimately have tr_conc_eq:"(trace_state_conc s'' (tr<s'''>-tr<s''>)) = (trace_state_conc s (tr<s''>-tr<s>))"
                      by (metis scene_equiv_def scene_equiv_sym scene_override_commute tr_vwb_lens
                          vwb_impl_idem_scene)

                    hence state_eq_tr_conc: "s''  = (trace_state_conc s (tr<s''>-tr<s>))"
                      using post_eq_states
                      by (simp add: trace_state_conc_def)

                    hence tr_s:"\<forall> t \<le> (tr<s'''>-tr<s>).A (trace_state_conc s t )"
                    proof -
                      {
                        fix t
                        assume t_leq:"t \<le> (tr<s'''>-tr<s>)"

                        consider 
                            (equal) "t = (tr<s'''>-tr<s>)" 
                            | (empty) "t = []"
                          using is_run_s send_trace_length post_eq_states
                          by (metis One_nat_def length_0_conv length_minus_less less_Suc0 minus_zero_eq not_wait2 t_leq
                              zero_list_def)

                        hence "A (trace_state_conc s t )"
                        proof(cases)
                          case equal
                          then show ?thesis 
                            using As2 state_eq_tr_conc post_eq_states
                            by argo
                        next
                          case empty
                          hence "s = (trace_state_conc s t )"
                            by (auto simp add:trace_state_conc_def)
                          then show ?thesis 
                            using As
                            by auto
                        qed
                      }
                      then show ?thesis 
                        by blast
                    qed

                    hence "F s'''"
                      using post_lhs post_dlchp_def is_run_final not_wait_end
                      by metis
                  }
                  then show ?thesis
                    by (simp add: post_dlchp_def)
                qed

                ultimately show ?thesis
                  using fbox_ac_def by metis
              qed                
            }
            then show ?thesis
              using fbox_utp_def
              by (metis (no_types, lifting)) 
          qed
        }
        then show ?thesis
          using post_dlchp_def
          by force
      qed
  
   ultimately have " ([?(True)\<^sub>e]\<^sub>P {A,C} [c!\<^sub>de] ([?(True)\<^sub>e]\<^sub>P {A,C} F ) ) s"
      using fbox_ac_def by metis
    }

    moreover {
      assume rhs:"([?(True)\<^sub>e]\<^sub>P {A,C} [c!\<^sub>de] ([?(True)\<^sub>e]\<^sub>P {A,C} F ) ) s"

      have rhs_commit: "commit_dlchp (?(True)\<^sub>e) A C s"
        using rhs fbox_ac_def by metis

      hence AC_imp: "A s \<longrightarrow> C s"
        by(simp add: commit_dlchp_def test_dlchp_def trace_state_conc_def)

      have rhs_post:"post_dlchp (?(True)\<^sub>e) A ([c!\<^sub>de] ([?(True)\<^sub>e]\<^sub>P {A,C} F ))  s"
        using rhs fbox_ac_def by metis

      have lhs:"([(c!\<^sub>de)]\<^sub>P {A, C}  F) s"
      proof -
        have "commit_dlchp (c!\<^sub>de) A C s"
        proof -
          {
            fix s' t
            assume is_run: "(c!\<^sub>de) (s,s')"
            assume tr_ass_lenght: "t < (tr<s'>-tr<s>)"
            assume tr_ass: "A (trace_state_conc s t )"

            
            have "t = []"
              using send_trace_length tr_ass_lenght is_run
              by (smt (verit, best) Prefix_Order.prefix_Nil Prefix_Order.prefix_snoc Prefix_Order.same_prefix_prefix
                  Prefix_Order.strict_prefix_simps(1) diff_add_cancel_left' less_list_def minus_right_nil not_le_minus
                  out_dlchp_def plus_list_def prod.simps(2) skip_def snd_lens_def zero_list_def)

            hence tr_conc_eq: "(trace_state_conc s t ) = s"
              by (simp add:trace_state_conc_def)

            hence As:"A s"
              using tr_ass by auto

            hence Cs:"C s"
              using AC_imp by auto

            from is_run consider
            (empty) "tr<s'> = tr<s>"
            | (sending) "tr<s'> =tr<s>@[(c(e (st<s>)), time<s>)]"
              using out_dlchp_def
              by (smt (verit, best) Prefix_Order.prefix_snoc case_prod_conv less_list_def
                  order_le_imp_less_or_eq)

            hence "C (trace_state_conc s (tr<s'>-tr<s>))"
            proof(cases)
              case empty
              then show ?thesis 
                using Cs
                by (auto simp add: trace_state_conc_def)
            next
              case sending

              from sending have nwait_start:"\<not> wait<s>"
                using is_run out_dlchp_def
                by (smt (verit, ccfv_threshold) Prefix_Order.strict_prefix_simps(1) case_prodD minus_cancel
                    tr_ass_lenght)

              moreover have "(?(True)\<^sub>e)(s,s)"
                by (auto simp add: test_dlchp_def)

              moreover have "\<forall> t \<le> tr<s> - tr<s>. A(trace_state_conc s t )"
                using As \<open>t = []\<close> tr_ass by auto

              ultimately have send_fbox:"([c!\<^sub>de] ([?(True)\<^sub>e]\<^sub>P {A,C} F ))  s"
                using rhs_post nwait_start post_dlchp_def by metis 

              obtain s'' where is_run2:"(c!\<^sub>de) (s,s'')" and n_waits2:"s'' = put\<^bsub>wait\<^esub> s' False"
                using is_run nwait_start sending
                by(auto simp add:out_dlchp_def)


              have nwaits_end:"\<not> wait<s''>"
                using n_waits2 by pred_simp

              hence "([?(True)\<^sub>e]\<^sub>P {A,C} F )  s''"
                using send_fbox fbox_utp_def is_run2 by metis

              hence "commit_dlchp (?(True)\<^sub>e) A C s''"
                using fbox_ac_def by metis

              moreover have "(?(True)\<^sub>e) (s'',s'')"
                by (auto simp:test_dlchp_def) 

              moreover have "(\<forall>t. t < get\<^bsub>tr\<^esub> s'' - get\<^bsub>tr\<^esub> s'' \<longrightarrow> A (trace_state_conc s'' t))"
                by simp


              ultimately have  Cs2:"C s''"
                using commit_dlchp_def
                by (metis (no_types, lifting) Orderings.order_eq_iff diff_add_cancel_left' plus_list_def tr_vwb_lens
                    trace_state_conc_def vwb_lens.axioms(1) wb_lens.get_put) 

              have "s' \<approx>\<^sub>S (trace_state_conc s (get\<^bsub>tr\<^esub> s' - get\<^bsub>tr\<^esub> s)) on \<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                using  sending 
                apply(auto simp add:trace_state_conc_def scene_equiv_def)
                by(pred_simp)


              moreover have "s' \<approx>\<^sub>S (trace_state_conc s (get\<^bsub>tr\<^esub> s' - get\<^bsub>tr\<^esub> s)) on -(\<Union>\<^sub>S {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>, \<lbrakk>wait\<rbrakk>\<^sub>\<sim>})"
                using send_vars is_run
                by (smt (verit) Diff_iff calculation idem_scene_Vars insert_subset para_obs_def para_obs_is_vars
                    scene_equiv_sym scene_neg_decomp scene_space_put_preserved tr_vwb_lens trace_state_conc_def)

              ultimately have "s' \<approx>\<^sub>S (trace_state_conc s (get\<^bsub>tr\<^esub> s' - get\<^bsub>tr\<^esub> s)) on -\<lbrakk>wait\<rbrakk>\<^sub>\<sim>"
                by (smt (verit) dual_order.trans insert_is_Un insert_subset para_obs_def para_obs_is_vars
                    scene_agreement_neg_comp set_Vars_scene_space ss_clat.weak_sup_of_singleton)

              moreover have "s' \<approx>\<^sub>S s'' on -\<lbrakk>wait\<rbrakk>\<^sub>\<sim>"
                using n_waits2
                by (metis (no_types, lifting) lens_obs_eq_def scene_lens_equiv_iff vwb_lens.put_eq vwb_lens_mwb
                    wait_vwb_lens)

              moreover have "\<not> wait<(trace_state_conc s (get\<^bsub>tr\<^esub> s' - get\<^bsub>tr\<^esub> s))>"
                using nwait_start 
                by (auto simp add: trace_state_conc_def)

              ultimately have "s'' = (trace_state_conc s (get\<^bsub>tr\<^esub> s' - get\<^bsub>tr\<^esub> s))"
                using n_waits2
                by (smt (z3) lens_obs_eq_def scene_lens_equiv_iff vwb_lens.axioms(2) vwb_lens.put_eq
                    wait_vwb_lens)

              thus ?thesis
                using Cs2 by auto
            qed

          }
          then show ?thesis
            apply(auto simp add: commit_dlchp_def)
            by (smt (verit, del_insts) SEXP_def antisym_conv1 commit_dlchp_def minus_cancel minus_gr_zero_iff
                not_le_minus prod.simps(2) rhs_commit test_dlchp_def zero_list_def)
        qed
        moreover have "post_dlchp (c!\<^sub>de) A F s"
        proof -
          {
            fix s'
            assume is_run: "(c!\<^sub>de) (s,s')"
            assume not_wait:"\<not> wait<s'>"
            assume tr_ass:"\<forall> t \<le> (tr<s'>-tr<s>).  A (trace_state_conc s t)"

            have not_wait_start:"\<not> wait<s>"
              using is_run  not_wait
              by(auto simp add: out_dlchp_def)

            moreover have "(?(True)\<^sub>e) (s,s)"
              by(simp add: test_dlchp_def)

            moreover have "\<forall> t \<le> (tr<s>-tr<s>).  A (trace_state_conc s t)"
              using tr_ass
              by simp

            ultimately have " ([c!\<^sub>de] ([?(True)\<^sub>e]\<^sub>P {A,C} F ))  s"
              using rhs_post post_dlchp_def
              by blast

            hence l2:"([?(True)\<^sub>e]\<^sub>P {A,C} F )  s'"
              using is_run not_wait fbox_utp_def
              by metis

            have " A (trace_state_conc s (tr<s'>-tr<s>))"
              using tr_ass
              by blast

            hence "A s'"
              using send_tr_states not_wait
              by (metis is_run)

            hence "\<forall> t \<le> (tr<s'>-tr<s'>).  A (trace_state_conc s' t)"
              by (metis Prefix_Order.prefixE Prefix_Order.prefix_Nil append_minus minus_cancel order_refl tr_vwb_lens
                  trace_state_conc_def vwb_lens.put_eq)

            moreover have "(?(True)\<^sub>e) (s',s')"
              by (auto simp add: test_dlchp_def)

            ultimately have "F s'"
              using l2 fbox_ac_def post_dlchp_def not_wait by metis
          }
          then show ?thesis
            using post_dlchp_def by metis
        qed
        ultimately  show ?thesis
          using fbox_ac_def by metis
      qed
    }
    ultimately show ?thesis
      by metis
  qed


theorem receive_ac:
  assumes "x \<bowtie> time_var" "comm_well_formed A (c?\<^sub>dx)" "vwb_lens x" "comm_well_formed A (x :=\<^sub>d \<star>)"  "comm_well_formed C (x :=\<^sub>d \<star>)" "\<not> wait<s>"
  shows "([(c?\<^sub>dx)]\<^sub>P {A, C}  F) s  \<longleftrightarrow> ([(x :=\<^sub>d \<star>)] ([(c!\<^sub>d ($x)\<^sub>e )]\<^sub>P {A, C}  F) s)"
proof -
  {
    assume lhs: "([(c?\<^sub>dx)]\<^sub>P {A, C}  F) s"
    have lhs_commit: "commit_dlchp (c?\<^sub>dx) A C s"
      using lhs fbox_ac_def by metis
    have lhs_post: "post_dlchp (c?\<^sub>dx) A F s"
      using lhs fbox_ac_def by metis

    have rhs: "([(x :=\<^sub>d \<star>)] ([(c!\<^sub>d ($x)\<^sub>e)]\<^sub>P {A, C}  F) s)"
    proof -
      {
        fix s'
        assume is_run_assign: "(x :=\<^sub>d \<star>) (s,s')"
        assume nwaits_mid: "\<not> wait<s'>"

        have nwaits_start:"\<not> wait<s>"
          using is_run_assign
          unfolding ndet_assign_dlchp_def assign_dlchp_def
          using nwaits_mid
          by auto

        hence tr_eq:"tr<s'> = tr<s>"
          using is_run_assign
          unfolding ndet_assign_dlchp_def assign_dlchp_def
          by  simp auto

        have "commit_dlchp (c!\<^sub>d ($x)\<^sub>e) A C s'"
        proof -
          {
            fix s''
            assume is_run_send:"(c!\<^sub>d ($x)\<^sub>e) (s',s'')"
            assume tr_ass:" \<forall> t < (tr<s''>-tr<s'>).  A (trace_state_conc s' t )"

            have cwf_agree:"s \<approx>\<^sub>S s' on \<Union>\<^sub>S (FV A - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
              using coincidence_cwf assms(4) is_run_assign
              by blast

            have  tr_ass2:" \<forall> t < (tr<s''>-tr<s>).  A (trace_state_conc s t )"
            proof -
              { 
                fix t
                assume t1:"t < (tr<s''>-tr<s>)"
                have t2:"t < (tr<s''>-tr<s'>)"
                  using tr_eq t1 by auto

                have "(trace_state_conc s t ) \<approx>\<^sub>S (trace_state_conc s' t ) on \<Union>\<^sub>S (FV A - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
                proof -
                  have "(trace_state_conc s t ) \<approx>\<^sub>S s on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                    using trace_state_conc_def
                    by (metis idem_scene_uminus scene_equiv_refl scene_indep_self_compl scene_indep_sym
                        scene_put_preserved tr_vwb_lens vwb_impl_idem_scene)

                  moreover have  "(trace_state_conc s' t ) \<approx>\<^sub>S s' on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                    using trace_state_conc_def
                    by (metis idem_scene_uminus scene_equiv_refl scene_indep_self_compl scene_indep_sym
                        scene_put_preserved tr_vwb_lens vwb_impl_idem_scene)

                  moreover have "\<Union>\<^sub>S (FV A - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>}) \<subseteq>\<^sub>S -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                    by (metis (no_types, opaque_lifting) Diff_mono FV_Vars bot.extremum insert_subsetI scene_minus2
                        scene_subset_union_lessthan set_Vars_scene_space singletonI subset_insertI2 subset_insert_iff
                        tr_is_var)
                  
                  ultimately show ?thesis
                    using cwf_agree
                    by (smt (verit) Diff_mono Diff_subset FV_Vars bot_unique insert_mono scene_minus2
                        scene_subset_agreement tr_is_var)
                qed

                moreover have "(trace_state_conc s t ) \<approx>\<^sub>S (trace_state_conc s' t ) on \<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                  using tr_eq trace_state_conc_def
                  by (metis Scenes.scene_equiv_get_eq tr_vwb_lens vwb_lens_def wb_lens.axioms(1)
                      weak_lens.put_get)

                ultimately have "(trace_state_conc s t ) \<approx>\<^sub>S (trace_state_conc s' t ) on \<Union>\<^sub>S (FV A)"
                  using scene_union_equiv
                  by (smt (verit, ccfv_SIG) Diff_empty Diff_insert0 Diff_mono Diff_partition Diff_subset_conv FV_Vars
                      Sup_scene_closed diff_shunt insert_Diff insert_subset scene_space_equiv_union set_Vars_scene_space
                      squnion_to_union)

                moreover have "A (trace_state_conc s' t )"
                  using t2 tr_ass by auto

                ultimately have "A (trace_state_conc s t )"
                  using coincidence_eff_term_prop_def coin_eff_term_1
                  by (smt (verit, ccfv_SIG) FV_Vars basic_trans_rules(23) scene_union_equiv
                      set_Vars_scene_space)
              }
              then show ?thesis
                by fastforce
            qed
               


            moreover have "(c?\<^sub>dx) (s, s'')"
              using send_eq_ndet_rec assms(1,3) is_run_send is_run_assign by blast

            ultimately have sC:"C (trace_state_conc s (tr<s''>-tr<s>))"
              using lhs_commit commit_dlchp_def by blast

            hence "C (trace_state_conc s' (tr<s''>-tr<s'>))"
            proof -
              have cwf_agreeC:"s \<approx>\<^sub>S s' on \<Union>\<^sub>S (FV C - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
                using coincidence_cwf assms(5) is_run_assign
                by blast
              have "(trace_state_conc s (tr<s''>-tr<s>)) \<approx>\<^sub>S (trace_state_conc s' (tr<s''>-tr<s'>)) on  \<Union>\<^sub>S (FV C - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
              proof -
                have "(trace_state_conc s (tr<s''>-tr<s>) ) \<approx>\<^sub>S s on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                    using trace_state_conc_def
                    by (metis idem_scene_uminus scene_equiv_refl scene_indep_self_compl scene_indep_sym
                        scene_put_preserved tr_vwb_lens vwb_impl_idem_scene)

                  moreover have  "(trace_state_conc s' (tr<s''>-tr<s'>) ) \<approx>\<^sub>S s' on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                    using trace_state_conc_def
                    by (metis idem_scene_uminus scene_equiv_refl scene_indep_self_compl scene_indep_sym
                        scene_put_preserved tr_vwb_lens vwb_impl_idem_scene)

                  moreover have "\<Union>\<^sub>S (FV C - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>}) \<subseteq>\<^sub>S -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                    by (metis (no_types, opaque_lifting) Diff_mono FV_Vars bot.extremum insert_subsetI scene_minus2
                        scene_subset_union_lessthan set_Vars_scene_space singletonI subset_insertI2 subset_insert_iff
                        tr_is_var)
                  
                  ultimately show ?thesis
                    using cwf_agreeC
                    by (smt (verit) Diff_mono Diff_subset FV_Vars bot_unique insert_mono scene_minus2
                        scene_subset_agreement tr_is_var)
                qed

                moreover have "(trace_state_conc s (tr<s''>-tr<s>)) \<approx>\<^sub>S (trace_state_conc s' (tr<s''>-tr<s'>)) on  \<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                  using tr_eq trace_state_conc_def
                  by (metis Scenes.scene_equiv_get_eq tr_vwb_lens vwb_lens_def wb_lens.axioms(1)
                      weak_lens.put_get)

                ultimately have "(trace_state_conc s (tr<s''>-tr<s>)) \<approx>\<^sub>S (trace_state_conc s' (tr<s''>-tr<s'>)) on  \<Union>\<^sub>S (FV C)"
                  using scene_union_equiv
                  by (smt (verit, ccfv_SIG) Diff_empty Diff_insert0 Diff_mono Diff_partition Diff_subset_conv FV_Vars
                      Sup_scene_closed diff_shunt insert_Diff insert_subset scene_space_equiv_union set_Vars_scene_space
                      squnion_to_union)

                thus ?thesis
                  using coincidence_eff_term_prop_def coin_eff_term_1 sC
                  by (smt (verit, ccfv_SIG) FV_Vars basic_trans_rules(23) scene_union_equiv
                      set_Vars_scene_space)
              qed
            }
            then show ?thesis
              using commit_dlchp_def
              by blast
          qed
            
        moreover have "post_dlchp (c!\<^sub>d ($x)\<^sub>e) A F s'"
        proof -
          {
            fix s''
            assume is_run:"(c!\<^sub>d ($x)\<^sub>e) (s', s'')"
            assume tr_ass:"(\<forall> t \<le> (tr<s''>-tr<s'>).  A (trace_state_conc s' t))"  
            assume nwait: "\<not> wait<s''> "

            have cwf_agree:"s \<approx>\<^sub>S s' on \<Union>\<^sub>S (FV A - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
              using coincidence_cwf assms(4) is_run_assign
              by blast

            have  tr_ass2:" \<forall> t \<le> (tr<s''>-tr<s>).  A (trace_state_conc s t )"
            proof -
              { 
                fix t
                assume t1:"t \<le> (tr<s''>-tr<s>)"
                have t2:"t \<le> (tr<s''>-tr<s'>)"
                  using tr_eq t1 by auto

                have "(trace_state_conc s t ) \<approx>\<^sub>S (trace_state_conc s' t ) on \<Union>\<^sub>S (FV A - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
                proof -
                  have "(trace_state_conc s t ) \<approx>\<^sub>S s on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                    using trace_state_conc_def
                    by (metis idem_scene_uminus scene_equiv_refl scene_indep_self_compl scene_indep_sym
                        scene_put_preserved tr_vwb_lens vwb_impl_idem_scene)

                  moreover have  "(trace_state_conc s' t ) \<approx>\<^sub>S s' on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                    using trace_state_conc_def
                    by (metis idem_scene_uminus scene_equiv_refl scene_indep_self_compl scene_indep_sym
                        scene_put_preserved tr_vwb_lens vwb_impl_idem_scene)

                  moreover have "\<Union>\<^sub>S (FV A - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>}) \<subseteq>\<^sub>S -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                    by (metis (no_types, opaque_lifting) Diff_mono FV_Vars bot.extremum insert_subsetI scene_minus2
                        scene_subset_union_lessthan set_Vars_scene_space singletonI subset_insertI2 subset_insert_iff
                        tr_is_var)
                  
                  ultimately show ?thesis
                    using cwf_agree
                    by (smt (verit) Diff_mono Diff_subset FV_Vars bot_unique insert_mono scene_minus2
                        scene_subset_agreement tr_is_var)
                qed

                moreover have "(trace_state_conc s t ) \<approx>\<^sub>S (trace_state_conc s' t ) on \<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                  using tr_eq trace_state_conc_def
                  by (metis Scenes.scene_equiv_get_eq tr_vwb_lens vwb_lens_def wb_lens.axioms(1)
                      weak_lens.put_get)

                ultimately have "(trace_state_conc s t ) \<approx>\<^sub>S (trace_state_conc s' t ) on \<Union>\<^sub>S (FV A)"
                  using scene_union_equiv
                  by (smt (verit, ccfv_SIG) Diff_empty Diff_insert0 Diff_mono Diff_partition Diff_subset_conv FV_Vars
                      Sup_scene_closed diff_shunt insert_Diff insert_subset scene_space_equiv_union set_Vars_scene_space
                      squnion_to_union)

                moreover have "A (trace_state_conc s' t )"
                  using t2 tr_ass by auto

                ultimately have "A (trace_state_conc s t )"
                  using coincidence_eff_term_prop_def coin_eff_term_1
                  by (smt (verit, ccfv_SIG) FV_Vars basic_trans_rules(23) scene_union_equiv
                      set_Vars_scene_space)
              }
              then show ?thesis
                by fastforce
            qed

            moreover have "(c?\<^sub>dx) (s, s'')"
              using send_eq_ndet_rec assms(1,3) is_run is_run_assign by blast

            ultimately have sC:"F s''"
              using lhs_post post_dlchp_def nwait by blast
          }

          then show ?thesis
            using post_dlchp_def by blast
        qed
        ultimately have "([(c!\<^sub>d ($x)\<^sub>e)]\<^sub>P {A, C}  F) s'"
          using fbox_ac_def
          by metis

      }
      then show ?thesis
        using fbox_utp_def
        by metis
    qed
  }
   moreover {
    assume rhs:"([(x :=\<^sub>d \<star>)] ([(c!\<^sub>d ($x)\<^sub>e )]\<^sub>P {A, C}  F) s)"

    have lhs:"([(c?\<^sub>dx)]\<^sub>P {A, C} F) s"
    proof -
      have lhs_commit:"commit_dlchp (c?\<^sub>dx) A C s"
      proof -
        {
          fix s''
          assume is_run_rec:"(c?\<^sub>dx) (s,s'')"
          assume tr_ass:"\<forall> t < (tr<s''>-tr<s>).  A (trace_state_conc s t )"

          obtain v where rec_cases:
              "((tr<s''> \<le> tr<s>@[(c v, time<s>)] \<and> tr<s> \<le> tr<s''> \<and> wait<s''>)
                \<or>
                (tr<s''> = tr<s>@[(c v, time<s>)] \<and> \<not>wait<s''>))"
            and rec_state:"st<s''> = put\<^bsub>x\<^esub> (st<s>) v"
            and rec_ok:"ok<s''> = ok<s>"
            using is_run_rec assms(6)
            unfolding inp_dlchp_def
            by auto

          obtain s' where post:"s' = put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) v)"
            by blast

          have is_run_assign:"(x :=\<^sub>d \<star>) (s,s')"
            using post assms(6)
            unfolding ndet_assign_dlchp_def assign_dlchp_def
            by auto

          have nwaits_mid:"\<not> wait<s'>"
            using post assms(6)
            by simp

          have tr_eq:"tr<s'> = tr<s>"
            using post
            by simp

          have time_eq:"time<s'> = time<s>"
            using post assms(1)
            by (metis Scenes.scene_equiv_get_eq is_run_assign ns_alpha_vwb st_vwb_lens time_nbound_ndet
                time_var_vwb_lens)

          have ok_eq:"ok<s'> = ok<s>"
            using post
            by simp

          have state_eq:"st<s'> = put\<^bsub>x\<^esub> (st<s>) v"
            using post
            by simp

          have xval:"($x)\<^sub>e (st<s'>) = v"
            using state_eq assms(3)
            by simp

          have is_run_send:"(c!\<^sub>d ($x)\<^sub>e) (s',s'')"
            using rec_cases rec_state rec_ok tr_eq time_eq ok_eq state_eq xval nwaits_mid
            unfolding out_dlchp_def
            by auto

          have rhs_send:"([(c!\<^sub>d ($x)\<^sub>e)]\<^sub>P {A, C} F) s'"
            using rhs fbox_utp_def is_run_assign nwaits_mid
            by metis

          have rhs_commit:"commit_dlchp (c!\<^sub>d ($x)\<^sub>e) A C s'"
            using rhs_send fbox_ac_def
            by metis

          have cwf_agree:"s \<approx>\<^sub>S s' on \<Union>\<^sub>S (FV A - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
            using coincidence_cwf assms(4) is_run_assign
            by blast

          have tr_ass2:"\<forall> t < (tr<s''>-tr<s'>).  A (trace_state_conc s' t )"
          proof -
            {
              fix t
              assume t1:"t < (tr<s''>-tr<s'>)"
              have t2:"t < (tr<s''>-tr<s>)"
                using tr_eq t1
                by auto

              have "(trace_state_conc s t ) \<approx>\<^sub>S (trace_state_conc s' t ) on \<Union>\<^sub>S (FV A - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
              proof -
                have "(trace_state_conc s t ) \<approx>\<^sub>S s on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                  using trace_state_conc_def
                  by (metis idem_scene_uminus scene_equiv_refl scene_indep_self_compl scene_indep_sym
                      scene_put_preserved tr_vwb_lens vwb_impl_idem_scene)

                moreover have  "(trace_state_conc s' t ) \<approx>\<^sub>S s' on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                  using trace_state_conc_def
                  by (metis idem_scene_uminus scene_equiv_refl scene_indep_self_compl scene_indep_sym
                      scene_put_preserved tr_vwb_lens vwb_impl_idem_scene)

                moreover have "\<Union>\<^sub>S (FV A - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>}) \<subseteq>\<^sub>S -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                  by (metis (no_types, opaque_lifting) Diff_mono FV_Vars bot.extremum insert_subsetI scene_minus2
                      scene_subset_union_lessthan set_Vars_scene_space singletonI subset_insertI2 subset_insert_iff
                      tr_is_var)

                ultimately show ?thesis
                  using cwf_agree
                  by (smt (verit) Diff_mono Diff_subset FV_Vars bot_unique insert_mono scene_minus2
                      scene_subset_agreement tr_is_var)
              qed

              moreover have "(trace_state_conc s t ) \<approx>\<^sub>S (trace_state_conc s' t ) on \<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                using tr_eq trace_state_conc_def
                by (metis Scenes.scene_equiv_get_eq tr_vwb_lens vwb_lens_def wb_lens.axioms(1)
                    weak_lens.put_get)

              ultimately have "(trace_state_conc s t ) \<approx>\<^sub>S (trace_state_conc s' t ) on \<Union>\<^sub>S (FV A)"
                using scene_union_equiv
                by (smt (verit, ccfv_SIG) Diff_empty Diff_insert0 Diff_mono Diff_partition Diff_subset_conv FV_Vars
                    Sup_scene_closed diff_shunt insert_Diff insert_subset scene_space_equiv_union set_Vars_scene_space
                    squnion_to_union)

              moreover have "A (trace_state_conc s t )"
                using t2 tr_ass
                by auto

              ultimately have "A (trace_state_conc s' t )"
                using coincidence_eff_term_prop_def coin_eff_term_1
                by (smt (verit, ccfv_SIG) FV_Vars basic_trans_rules(23) scene_union_equiv
                    set_Vars_scene_space)
            }
            then show ?thesis
              by fastforce
          qed

          hence sC:"C (trace_state_conc s' (tr<s''>-tr<s'>))"
            using rhs_commit commit_dlchp_def is_run_send
            by blast

          hence "C (trace_state_conc s (tr<s''>-tr<s>))"
          proof -
            have cwf_agreeC:"s \<approx>\<^sub>S s' on \<Union>\<^sub>S (FV C - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
              using coincidence_cwf assms(5) is_run_assign
              by blast

            have "(trace_state_conc s (tr<s''>-tr<s>)) \<approx>\<^sub>S
                  (trace_state_conc s' (tr<s''>-tr<s'>)) on  \<Union>\<^sub>S (FV C - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
            proof -
              have "(trace_state_conc s (tr<s''>-tr<s>) ) \<approx>\<^sub>S s on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                using trace_state_conc_def
                by (metis idem_scene_uminus scene_equiv_refl scene_indep_self_compl scene_indep_sym
                    scene_put_preserved tr_vwb_lens vwb_impl_idem_scene)

              moreover have  "(trace_state_conc s' (tr<s''>-tr<s'>) ) \<approx>\<^sub>S s' on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                using trace_state_conc_def
                by (metis idem_scene_uminus scene_equiv_refl scene_indep_self_compl scene_indep_sym
                    scene_put_preserved tr_vwb_lens vwb_impl_idem_scene)

              moreover have "\<Union>\<^sub>S (FV C - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>}) \<subseteq>\<^sub>S -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                by (metis (no_types, opaque_lifting) Diff_mono FV_Vars bot.extremum insert_subsetI scene_minus2
                    scene_subset_union_lessthan set_Vars_scene_space singletonI subset_insertI2 subset_insert_iff
                    tr_is_var)

              ultimately show ?thesis
                using cwf_agreeC
                by (smt (verit) Diff_mono Diff_subset FV_Vars bot_unique insert_mono scene_minus2
                    scene_subset_agreement tr_is_var)
            qed

            moreover have "(trace_state_conc s (tr<s''>-tr<s>)) \<approx>\<^sub>S
                           (trace_state_conc s' (tr<s''>-tr<s'>)) on  \<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
              using tr_eq trace_state_conc_def
              by (metis Scenes.scene_equiv_get_eq tr_vwb_lens vwb_lens_def wb_lens.axioms(1)
                  weak_lens.put_get)

            ultimately have "(trace_state_conc s (tr<s''>-tr<s>)) \<approx>\<^sub>S
                             (trace_state_conc s' (tr<s''>-tr<s'>)) on  \<Union>\<^sub>S (FV C)"
              using scene_union_equiv
              by (smt (verit, ccfv_SIG) Diff_empty Diff_insert0 Diff_mono Diff_partition Diff_subset_conv FV_Vars
                  Sup_scene_closed diff_shunt insert_Diff insert_subset scene_space_equiv_union set_Vars_scene_space
                  squnion_to_union)

            thus ?thesis
              using coincidence_eff_term_prop_def coin_eff_term_1 sC
              by (smt (verit, ccfv_SIG) FV_Vars basic_trans_rules(23) scene_union_equiv
                  set_Vars_scene_space)
          qed
        }
        then show ?thesis
          using commit_dlchp_def
          by blast
      qed

      moreover have lhs_post:"post_dlchp (c?\<^sub>dx) A F s"
      proof -
        {
          fix s''
          assume is_run_rec:"(c?\<^sub>dx) (s,s'')"
          assume tr_ass:"\<forall> t \<le> (tr<s''>-tr<s>).  A (trace_state_conc s t )"
          assume nwait:"\<not> wait<s''>"

          obtain v where rec_cases:
              "((tr<s''> \<le> tr<s>@[(c v, time<s>)] \<and> tr<s> \<le> tr<s''> \<and> wait<s''>)
                \<or>
                (tr<s''> = tr<s>@[(c v, time<s>)] \<and> \<not>wait<s''>))"
            and rec_state:"st<s''> = put\<^bsub>x\<^esub> (st<s>) v"
            and rec_ok:"ok<s''> = ok<s>"
            using is_run_rec assms(6)
            unfolding inp_dlchp_def
            by auto

          obtain s' where post:"s' = put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) v)"
            by blast

          have is_run_assign:"(x :=\<^sub>d \<star>) (s,s')"
            using post assms(6)
            unfolding ndet_assign_dlchp_def assign_dlchp_def
            by auto

          have nwaits_mid:"\<not> wait<s'>"
            using post assms(6)
            by simp

          have tr_eq:"tr<s'> = tr<s>"
            using post
            by simp

          have time_eq:"time<s'> = time<s>"
            using post assms(1)
            by (metis Scenes.scene_equiv_get_eq is_run_assign ns_alpha_vwb st_vwb_lens time_nbound_ndet
                time_var_vwb_lens)

          have ok_eq:"ok<s'> = ok<s>"
            using post
            by simp

          have state_eq:"st<s'> = put\<^bsub>x\<^esub> (st<s>) v"
            using post
            by simp

          have xval:"($x)\<^sub>e (st<s'>) = v"
            using state_eq assms(3)
            by simp

          have is_run_send:"(c!\<^sub>d ($x)\<^sub>e) (s',s'')"
            using rec_cases rec_state rec_ok tr_eq time_eq ok_eq state_eq xval nwaits_mid
            unfolding out_dlchp_def
            by auto

          have rhs_send:"([(c!\<^sub>d ($x)\<^sub>e)]\<^sub>P {A, C} F) s'"
            using rhs fbox_utp_def is_run_assign nwaits_mid
            by metis

          have rhs_post:"post_dlchp (c!\<^sub>d ($x)\<^sub>e) A F s'"
            using rhs_send fbox_ac_def
            by metis

          have cwf_agree:"s \<approx>\<^sub>S s' on \<Union>\<^sub>S (FV A - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
            using coincidence_cwf assms(4) is_run_assign
            by blast

          have tr_ass2:"\<forall> t \<le> (tr<s''>-tr<s'>).  A (trace_state_conc s' t )"
          proof -
            {
              fix t
              assume t1:"t \<le> (tr<s''>-tr<s'>)"
              have t2:"t \<le> (tr<s''>-tr<s>)"
                using tr_eq t1
                by auto

              have "(trace_state_conc s t ) \<approx>\<^sub>S (trace_state_conc s' t ) on \<Union>\<^sub>S (FV A - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
              proof -
                have "(trace_state_conc s t ) \<approx>\<^sub>S s on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                  using trace_state_conc_def
                  by (metis idem_scene_uminus scene_equiv_refl scene_indep_self_compl scene_indep_sym
                      scene_put_preserved tr_vwb_lens vwb_impl_idem_scene)

                moreover have  "(trace_state_conc s' t ) \<approx>\<^sub>S s' on -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                  using trace_state_conc_def
                  by (metis idem_scene_uminus scene_equiv_refl scene_indep_self_compl scene_indep_sym
                      scene_put_preserved tr_vwb_lens vwb_impl_idem_scene)

                moreover have "\<Union>\<^sub>S (FV A - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>}) \<subseteq>\<^sub>S -\<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                  by (metis (no_types, opaque_lifting) Diff_mono FV_Vars bot.extremum insert_subsetI scene_minus2
                      scene_subset_union_lessthan set_Vars_scene_space singletonI subset_insertI2 subset_insert_iff
                      tr_is_var)

                ultimately show ?thesis
                  using cwf_agree
                  by (smt (verit) Diff_mono Diff_subset FV_Vars bot_unique insert_mono scene_minus2
                      scene_subset_agreement tr_is_var)
              qed

              moreover have "(trace_state_conc s t ) \<approx>\<^sub>S (trace_state_conc s' t ) on \<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
                using tr_eq trace_state_conc_def
                by (metis Scenes.scene_equiv_get_eq tr_vwb_lens vwb_lens_def wb_lens.axioms(1)
                    weak_lens.put_get)

              ultimately have "(trace_state_conc s t ) \<approx>\<^sub>S (trace_state_conc s' t ) on \<Union>\<^sub>S (FV A)"
                using scene_union_equiv
                by (smt (verit, ccfv_SIG) Diff_empty Diff_insert0 Diff_mono Diff_partition Diff_subset_conv FV_Vars
                    Sup_scene_closed diff_shunt insert_Diff insert_subset scene_space_equiv_union set_Vars_scene_space
                    squnion_to_union)

              moreover have "A (trace_state_conc s t )"
                using t2 tr_ass
                by auto

              ultimately have "A (trace_state_conc s' t )"
                using coincidence_eff_term_prop_def coin_eff_term_1
                by (smt (verit, ccfv_SIG) FV_Vars basic_trans_rules(23) scene_union_equiv
                    set_Vars_scene_space)
            }
            then show ?thesis
              by fastforce
          qed

          hence "F s''"
            using rhs_post post_dlchp_def is_run_send nwait
            by blast
        }
        then show ?thesis
          using post_dlchp_def
          by blast
      qed

      ultimately show ?thesis
        using fbox_ac_def
        by metis
    qed
  }
  ultimately show ?thesis
    by blast
qed   

theorem assign_dlchp_fbox_state:
  assumes "\<not> wait<s>"
  shows
    "([x :=\<^sub>d e] F) s = F (put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) ((e)\<^sub>e (st<s>))))"
proof -
  {
    assume lhs:"([x :=\<^sub>d e] F) s "

    have "\<forall> s'.\<not>wait<s'> \<longrightarrow>  ((x :=\<^sub>d e) (s,s') \<longrightarrow> F s')"
      using lhs unfolding fbox_utp_def by auto

    moreover have "(x :=\<^sub>d e) (s,(put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) ((e)\<^sub>e (st<s>)))))"
      unfolding assign_dlchp_def using assms by auto

    moreover have "\<not> wait<put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) ((e)\<^sub>e (st<s>)))>"
      using assms by pred_simp

    ultimately have "F (put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) ((e)\<^sub>e (st<s>))))"
      by blast
  }

  moreover {
    assume rhs:"F (put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) ((e)\<^sub>e (st<s>))))"

    have "([x :=\<^sub>d e] F) s "
    proof -
      { 
        fix s'
        assume is_run:"(x :=\<^sub>d e) (s,s')"
        assume nwait_end:"\<not>wait<s'>"

        have "s' =(put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) ((e)\<^sub>e (st<s>))))"
          using is_run nwait_end nwait unfolding assign_dlchp_def
          by(pred_auto)

        hence " F s'"
          using rhs by blast
         
      }
      then show ?thesis
        unfolding fbox_utp_def by blast
    qed
  }

  ultimately show ?thesis
    by blast
qed





theorem ndet_assign_dlchp_fbox_state:
  assumes  "\<not> wait<s>"
  shows
    "([x :=\<^sub>d \<star>] F) s = (\<forall>v. F (put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) v)))"
proof -
  {
    assume lhs:"([x :=\<^sub>d \<star>] F) s"

    have "\<forall> s'.\<not>wait<s'> \<longrightarrow>  ((x :=\<^sub>d \<star>) (s,s') \<longrightarrow> F s')"
      using lhs unfolding fbox_utp_def by auto

    moreover have "\<forall> v. (x :=\<^sub>d \<star>) (s,(put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) (v (st<s>)))))"
      unfolding ndet_assign_dlchp_def assign_dlchp_def using assms by auto

    moreover have "\<forall> v.\<not> wait<put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) (v (st<s>)))>"
      using assms by pred_simp

    ultimately have "\<forall> v. F (put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) (v (st<s>))))"
      by blast
  }

  moreover {
    assume rhs:"\<forall> v. F (put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) (v (st<s>))))"

    have "([x :=\<^sub>d \<star>] F) s "
    proof -
      { 
        fix s'
        assume is_run:"(x :=\<^sub>d \<star>) (s,s')"
        assume nwait_end:"\<not>wait<s'>"

        have det:"\<exists> v. (x :=\<^sub>d v)  (s,s')"
          using is_run unfolding ndet_assign_dlchp_def by auto

        obtain v where det_run:"(x :=\<^sub>d v)  (s,s')"
          using det by blast

        have "s' = (put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) ((v)\<^sub>e (st<s>))))"
          using det_run nwait_end assms unfolding assign_dlchp_def
          by(pred_auto)

        hence " F s'"
          using rhs by blast
         
      }
      then show ?thesis
        unfolding fbox_utp_def by blast
    qed
  }

  ultimately show ?thesis
    by auto 
qed

theorem send_box:
  assumes  "\<not> wait<s>"
  shows "([(c!\<^sub>de)] F) s = F (put\<^bsub>tr\<^esub> s (tr<s>@[(c (e (st<s>)), time<s>)]))"
proof -
  {
    assume lhs:"([c!\<^sub>de] F) s "

    have "\<forall> s'.\<not>wait<s'> \<longrightarrow>  ((c!\<^sub>de) (s,s') \<longrightarrow> F s')"
      using lhs unfolding fbox_utp_def by auto

    moreover have "(c!\<^sub>de) (s,(put\<^bsub>tr\<^esub> s (tr<s>@[(c (e (st<s>)), time<s>)])))"
      unfolding out_dlchp_def using assms by auto

    moreover have "\<not> wait<(put\<^bsub>tr\<^esub> s (tr<s>@[(c (e (st<s>)), time<s>)]))>"
      using assms by pred_simp

    ultimately have "F (put\<^bsub>tr\<^esub> s (tr<s>@[(c (e (st<s>)), time<s>)]))"
      by blast
  }

  moreover {
    assume rhs:"F (put\<^bsub>tr\<^esub> s (tr<s>@[(c (e (st<s>)), time<s>)]))"

    have "([(c!\<^sub>de)] F) s "
    proof -
      { 
        fix s'
        assume is_run:"(c!\<^sub>de) (s,s')"
        assume nwait_end:"\<not>wait<s'>"

        have "s' =(put\<^bsub>tr\<^esub> s (tr<s>@[(c (e (st<s>)), time<s>)]))"
          using is_run nwait_end assms unfolding out_dlchp_def
          by(pred_auto)

        hence " F s'"
          using rhs by blast
         
      }
      then show ?thesis
        unfolding fbox_utp_def by blast
    qed
  }

  ultimately show ?thesis
    by blast
qed
end