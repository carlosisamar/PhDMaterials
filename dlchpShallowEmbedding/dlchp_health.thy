theory dlchp_health
  imports "dlchp_parallel"
begin

definition prefix_closed :: "('s, 'e::channel) dlCHP_rel \<Rightarrow> bool" where
  "prefix_closed P = (\<forall> s s'. P(s,s') \<longrightarrow>
                         (\<forall> t. t \<le> (tr<s'>-tr<s>)  \<longrightarrow>  
                         (\<exists> w. tr<w> = tr<s>@t \<and> (wait<w>)  \<and> P(s,w))))"

definition total :: "('s, 'e::channel) dlCHP_rel \<Rightarrow> bool" where
  "total P = (\<forall> s. \<exists> s'. P(s,s') \<and> wait<s'> \<and> tr<s'> = tr<s>)"

definition waits_wf ::  "('s, 'e::channel) dlCHP_rel \<Rightarrow> bool" where
  "waits_wf P = (\<forall> s s'. wait<s> \<longrightarrow> (P(s,s') = skip(s,s')))"


lemma waits_wf_r3:
 "waits_wf P \<longleftrightarrow> P is R3"
  apply(simp add: waits_wf_def R3_def Healthy_def)
  apply(auto)
  apply(expr_simp)
  apply (metis (no_types, lifting) SEXP_def expr_if_def expr_pre)
  apply (metis (no_types, lifting) SEXP_def expr_if_def expr_pre)
  done


lemma prefix_closed_paral:
  assumes "prefix_closed P" "prefix_closed Q"
  shows "prefix_closed (P \<parallel>\<^sub>d Q)"
proof -
  {
    fix s s'
    assume a1:"(P \<parallel>\<^sub>d Q)(s,s')"
    fix t
    assume a2:"t \<le> (tr<s'>-tr<s>)"
    have t1:"trace_restriction_paral t P Q = t"
    proof -
      have "channels_from_trace (tr<s'>-tr<s>) \<subseteq> CN P \<union> CN Q"
        using channels_from_trace_cn trace_rest_contr a1 channel_names_paral
        by (metis (no_types, lifting) subset_trans)
      then have "channels_from_trace t \<subseteq> CN P \<union> CN Q"
        using a2 channels_from_trace_transit 
      using nless_le by blast 
      then show ?thesis
        by (simp add: trace_rest_subset trace_restriction_paral_def)
    qed
    have "\<exists> s''. wait<s''> \<and> tr<s''> = tr<s>@t \<and> (P \<parallel>\<^sub>d Q)(s,s'')"
    proof-
      obtain ps where ps1:"P(s,ps)" and ps2:"ppl s' ps (tr<s'>-tr<s>) (tr<ps>-tr<s>) (BV_progs P - observables ) (CN P)"
        using ppl_ext a1 by blast
      have ps3:"\<exists> ps'.(tr<ps'> = tr<s>@ (trace_restriction_channels t (CN P)) \<and> wait<ps'> \<and>  P(s,ps'))"
      proof -
        have "trace_restriction_channels (tr<s'>-tr<s>)  (CN P) = tr<ps>-tr<s>"
          using ps2 ppl_def  by (metis (no_types, lifting))
        then have "trace_restriction_channels t (CN P) \<le> tr<ps>-tr<s>"
          using a2
          by (metis (no_types, lifting) Prefix_Order.prefixE Prefix_Order.prefixI filter_append
              trace_restriction_channels_def)
        then show ?thesis
            using ps1 assms(1) prefix_closed_def trace_state_comp_def
            by blast
        qed
      obtain ps' where "tr<ps'> = tr<s>@ (trace_restriction_channels t (CN P))" and ps4:"P(s,ps')" and ps5:"wait<ps'>"
        using ps3 by blast
      obtain qs where qs1:"Q(s,qs)" and qs2:"ppr s' qs (tr<s'>-tr<s>) (tr<qs>-tr<s>) (BV_progs P \<union> observables) (CN Q)"
        using ppr_ext a1 by blast
      have qs3:"\<exists> qs'.(tr<qs'> = tr<s>@ (trace_restriction_channels t (CN Q)) \<and> wait<qs'> \<and>  Q(s,qs'))"
      proof -
        have "trace_restriction_channels t (CN Q) \<le> tr<qs>-tr<s>"
          using a2 ppr_def qs2
          by (smt (verit, ccfv_SIG) Prefix_Order.prefixE Prefix_Order.prefixI filter_append
              trace_restriction_channels_def)
        then show ?thesis
            using qs1 assms(2) prefix_closed_def by blast
        qed
      obtain qs' where "tr<qs'> = tr<s>@ (trace_restriction_channels t (CN Q))" and qs4:"Q(s,qs')" and qs5:"wait<qs'>"
        using qs3 by blast
      obtain s'' where s1:"s'' = (put\<^bsub>time\<^esub>(put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (qs' \<oplus>\<^sub>S ps' on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ t)) (wait<ps'> \<or> wait<qs'>)) ((if get\<^bsub>wait\<^esub> ps' \<or> get\<^bsub>wait\<^esub> qs' then (if (time<ps'> = time<qs'>) then time<ps'> else -1 ) else get\<^bsub>time\<^esub> ps')))"
        by blast
      have t2:"t\<downharpoonright>P = tr<ps'> - tr<s>"
        by (simp add: \<open>get\<^bsub>tr\<^esub> ps' = get\<^bsub>tr\<^esub> s @ trace_restriction_channels t (CN P)\<close>
            trace_restriction_prog_def)
      have t3: "t\<downharpoonright>Q = tr<qs'> - tr<s>"
        by (simp add: \<open>get\<^bsub>tr\<^esub> qs' = get\<^bsub>tr\<^esub> s @ trace_restriction_channels t (CN Q)\<close>
            trace_restriction_prog_def)
      have t4: " wait<ps'> \<or> wait<qs'> \<or> (time<ps'> = time<qs'> )"
        using qs5 by auto
      have "(P \<parallel>\<^sub>d Q)(s,s'')"
        using s1 t1 t2 t3 t4 ps4 qs4 parallel_def
        by (smt (verit) old.prod.case)
      moreover have "wait<s''>"
        using s1 qs5  ns_alpha_indep_3 srea_vars.indeps(8) rea_vars.indeps(3) lens_indep.lens_put_irr1
        by (metis (no_types, lifting) mwb_lens.axioms(1) vwb_lens.axioms(2) wait_vwb_lens
            weak_lens.put_get)
      moreover have "tr<s''> = tr<s>@t"
      proof -
        have "tr<s''> = tr<put\<^bsub>time\<^esub>
     (put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (qs' \<oplus>\<^sub>S ps' on \<Union>\<^sub>S (BV_progs P)) (get\<^bsub>tr\<^esub> s @ t))
       (get\<^bsub>wait\<^esub> ps' \<or> get\<^bsub>wait\<^esub> qs'))
     (if get\<^bsub>wait\<^esub> ps' \<or> get\<^bsub>wait\<^esub> qs' then if get\<^bsub>time\<^esub> ps' = get\<^bsub>time\<^esub> qs' then get\<^bsub>time\<^esub> ps' else -1
      else get\<^bsub>time\<^esub> ps')>"
          using s1
          by blast
        then have "tr<s''> = tr<(put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (qs' \<oplus>\<^sub>S ps' on \<Union>\<^sub>S (BV_progs P)) (get\<^bsub>tr\<^esub> s @ t))
       (get\<^bsub>wait\<^esub> ps' \<or> get\<^bsub>wait\<^esub> qs'))>"
          using lens_indep.lens_put_irr1 ns_alpha_indep_3 srea_vars.indeps(8) rea_vars.indeps(5) 
          by (metis (no_types, lifting))
        then have  "tr<s''> = tr< ((put\<^bsub>tr\<^esub> (qs' \<oplus>\<^sub>S ps' on \<Union>\<^sub>S (BV_progs P)) (get\<^bsub>tr\<^esub> s @ t)) )>"
          using lens_indep.lens_put_irr1   rea_vars.indeps(2) 
          by (metis (no_types, lifting))
        thus ?thesis
          by simp
      qed
      ultimately show ?thesis
        by blast
    qed
  }
  then show ?thesis
    using prefix_closed_def
    by blast
qed

lemma total_parallel:
  fixes P::"('s::scene_space, 'e::channel) dlCHP_rel"
  assumes "total P" "total Q"
  shows "total (P \<parallel>\<^sub>d Q)"
proof -
  {
    fix s
    obtain ps where ps1:"P(s,ps)" and ps2:"wait<ps>" and ps3:"tr<ps> = tr<s>" 
      using assms(1) total_def by blast 
    obtain qs where qs1:"Q(s,qs)" and qs2:"wait<qs>" and qs3:"tr<qs> = tr<s>" 
      using assms(2) total_def by blast 
    obtain ptr::"('e::channel \<times> real) list" where ptr1: "ptr = []"
      by auto
    obtain s' where sp:"s' =put\<^bsub>time\<^esub> (put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr)) (wait<ps> \<or> wait<qs>)) (if (wait<ps> \<or> wait<qs>) then (if (time<ps> = time<qs>) then time<ps> else -1 ) else time<ps>)"
      by blast
    have "ptr \<downharpoonright> P = (tr<ps> - tr<s>)"
      using ptr1 ps3
      by (metis minus_cancel ps1 trace_rest_contr)
    moreover have "ptr \<downharpoonright> Q = (tr<qs>  - tr<s>)"
      using ptr1 qs3
      by (metis minus_cancel qs1 trace_rest_contr)
    moreover have "(((wait<ps> \<or> wait<qs>)) \<or> ( (time<ps> = time<qs>)))"
      using ps2 by auto
    moreover have "trace_restriction_paral ptr P Q = ptr"
      using trace_restriction_paral_def ptr1
      by (metis append.right_neutral filter_append same_append_eq
          trace_restriction_channels_def)
    ultimately have "(P \<parallel>\<^sub>d Q) (s, s')"
      using ps1 qs1 sp parallel_def
      by (smt (verit) old.prod.case)
    moreover have "wait<s'>"
      using ps2 qs2
      using local.sp by fastforce
    moreover have "tr<s'> = tr<s>"
    proof -
      have l1:"tr<s> @ ptr =  tr<(put\<^bsub>tr\<^esub> (qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr))>"
        using tr_vwb_lens
        by simp
      have l2:"tr<(put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr)) (wait<ps> \<or> wait<qs>))> = tr< (put\<^bsub>tr\<^esub> (qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr))>"
        using tr_vwb_lens wait_vwb_lens  wait_is_var lens_put_get_preserved_indep
        by force
      have "tr \<bowtie> time"
        using tr_is_var time_is_var ns_alpha_indep_3 srea_vars.indeps(8) rea_vars.indeps(5) by blast
      then have l3:"tr<s'> = tr<(put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr)) (wait<ps> \<or> wait<qs>))>"
        using sp  lens_put_get_preserved_indep2
        by fastforce
      have "tr<s'> = tr<s> @ ptr"
        using l1 l2 l3 by auto
      then show ?thesis
        using ptr1 by auto
    qed
    ultimately have "\<exists> s'. ((P \<parallel>\<^sub>d Q)(s,s') \<and> wait<s'> \<and> tr<s'> = tr<s>)"
      by auto
  }
  then show ?thesis
    using total_def by blast
qed

lemma waits_wf_paral:
  fixes P::"('s::scene_space, 'e::channel) dlCHP_rel"
  assumes "waits_wf P" "waits_wf Q" 
  shows "waits_wf (P \<parallel>\<^sub>d Q)"
proof -
  {
    fix s::"('s::scene_space, 'e::channel) dlCHP_alpha"
    fix s'::"('s::scene_space, 'e::channel) dlCHP_alpha"
    assume a2:"wait<s>"
    {
    assume a3:"(P \<parallel>\<^sub>d Q) (s, s')"
    have l0:" (\<exists> ps qs ptr. s' = put\<^bsub>time\<^esub> (put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr)) (wait<ps> \<or> wait<qs>)) (if (wait<ps> \<or> wait<qs>) then (if (time<ps> = time<qs>) then time<ps> else -1 ) else time<ps>)  \<and>   
                                             skip (s, ps) \<and>   skip (s, qs) \<and>
                                             ptr \<downharpoonright> P = (tr<ps> - tr<s>) \<and>  ptr \<downharpoonright> Q = (tr<qs>  - tr<s>) \<and> 
                                             (((wait<ps> \<or> wait<qs>)) \<or> ( (time<ps> = time<qs>))) \<and>
                                             trace_restriction_paral ptr P Q = ptr)"
      using parallel_def assms waits_wf_def a2 a3
      by (smt (verit) case_prod_conv)
    obtain ps qs ptr where s1:"s' = put\<^bsub>time\<^esub> (put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr)) (wait<ps> \<or> wait<qs>)) (if (wait<ps> \<or> wait<qs>) then (if (time<ps> = time<qs>) then time<ps> else -1 ) else time<ps>)"
                     and s2:"skip (s, ps)" and s3:" skip (s, qs)" and s4:"ptr \<downharpoonright> P = (tr<ps> - tr<s>)" and s5:"ptr \<downharpoonright> Q = (tr<qs>  - tr<s>)"
                                            and s6:" (((wait<ps> \<or> wait<qs>)) \<or> ( (time<ps> = time<qs>)))" 
                                            and s7:" trace_restriction_paral ptr P Q = ptr"
      using l0 by blast
    have l1:"ps = s" 
      using s2
      by (simp add: skip_def)
    moreover have l2:"qs = s" 
      using s3
      by (simp add: skip_def)
    moreover have "ptr = []"
    proof-
      have "ptr \<downharpoonright> P = []"
        using l1 s4
        by auto
      moreover have "ptr \<downharpoonright> Q = []"
        using l2 s5
        by auto
      ultimately have "trace_restriction_paral ptr P Q = []"
        using trace_restriction_paral_def trace_restriction_prog_def
        by (metis (no_types, lifting) UnE empty_filter_conv trace_restriction_channels_def)
      then show ?thesis
        using s7
        by presburger
    qed
    ultimately have "s = s'"
      using s1
      by (smt (z3) a2 append.right_neutral assms(1) bound_eff_1 bound_eff_prop_def l0 ns_alpha_vwb
          old.prod.case scene_equiv_def scene_override_commute skip_def st_vwb_lens time_var_vwb_lens tr_vwb_lens
          vwb_lens_def wait_vwb_lens waits_wf_def wb_lens.get_put)

    then have "skip (s,s')"
      using l2 s3 by force
  }
  moreover{
    assume a3:"skip (s,s')"
    have l0:"s = s'"
      using a3
      by (simp add: skip_def)
    have l1:"P(s,s)"
      using l0 a2 a3 assms(1) waits_wf_def by blast
    have l2:"Q(s,s)"
      using l0 a2 a3 assms(2) waits_wf_def by blast
    obtain ptr::"('e::channel \<times> real) list" where t1:"ptr = []"
      by simp
    have l3:"s = put\<^bsub>time\<^esub> (put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (s \<oplus>\<^sub>S s on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr)) (wait<s> \<or> wait<s>)) (if (wait<s> \<or> wait<s>) then (if (time<s> = time<s>) then time<s> else -1 ) else time<s>)"
      by (simp add: Sup_scene_closed idem_scene_space t1)
    have l4:"ptr \<downharpoonright> P = (tr<s> - tr<s>)"
      using t1
      by (metis l1 minus_cancel trace_rest_contr)
    have l5:"ptr \<downharpoonright> Q = (tr<s> - tr<s>)"
      using t1
      by (metis l2 minus_cancel trace_rest_contr)
    have l6:"(((wait<s> \<or> wait<s>)) \<or> ( (time<s> = time<s>)))"
      by fastforce
    have l7:" trace_restriction_paral ptr P Q = ptr"
      using t1
      by (metis channels_from_trace_cn l4 subset_trans sup_ge1 trace_class.diff_cancel
          trace_rest_subset trace_restriction_paral_def zero_list_def)
    have "(P \<parallel>\<^sub>d Q)(s,s)"
      using parallel_def l1 l2 l3 l4 l5 l6 l7
      by (smt (verit) old.prod.case)
    then have "(P \<parallel>\<^sub>d Q)(s,s')"
      using l0 by blast
  }
  ultimately have "skip (s,s') = (P \<parallel>\<^sub>d Q)(s,s')"
    by auto
}
  then show ?thesis
    using waits_wf_def
    by blast
qed


lemma r1_union:
  assumes "P is R1" "Q is R1"
  shows "(P \<Union>\<^sub>d Q) is R1"
  using assms
  apply(simp add:choice_dlchp_def Healthy_def)
  apply(pred_simp)
  by meson

lemma prefix_closed_union :
  assumes "prefix_closed P" "prefix_closed Q"
  shows "prefix_closed (P \<Union>\<^sub>d Q)"
  using assms
  apply(simp add:choice_dlchp_def)
  by (smt (verit, best) case_prod_conv prefix_closed_def)

lemma total_union :
  assumes "total P" "total Q"
  shows "total (P \<Union>\<^sub>d Q)"
  using assms
  apply(simp add:choice_dlchp_def total_def)
  by(auto)

lemma waits_wf_union:
  assumes "waits_wf P" "waits_wf Q"
  shows "waits_wf  (P \<Union>\<^sub>d Q)"
  using assms
  by(simp add:choice_dlchp_def waits_wf_def)

lemma r1_test:
  shows "(? T) is R1"
  apply(simp add: test_dlchp_def)
  apply(pred_simp)
  by fastforce

lemma prefix_closed_test:
  shows "prefix_closed (? T)"
  apply(simp add: prefix_closed_def test_dlchp_def)
  apply(pred_simp)
  by(auto)

lemma total_test:
  shows "total (? T)"
  apply(simp add: total_def test_dlchp_def)
  by(auto)

lemma waits_wf_test:
  shows "waits_wf  (? T)"
  apply(simp add:test_dlchp_def waits_wf_def)
  by (metis (mono_tags, lifting) old.prod.case skip_def vwb_lens.put_eq wait_vwb_lens)


lemma r1_seq_comp:
  assumes "P is R1" "Q is R1"
  shows "(P ;;\<^sub>d Q) is R1"
  using assms
  apply(simp add: seq_comp_dlchp_def)
  apply(pred_simp)
  apply(auto)
  apply blast
  apply metis
   apply metis
  by (meson dual_order.trans)
  

lemma prefix_closed_seq_comp:
  assumes "prefix_closed P" "prefix_closed Q" "P is R1" "Q is R1"
  shows "prefix_closed (P ;;\<^sub>d Q)"
proof -
  {
    fix s s'
    assume a1:"(P ;;\<^sub>d Q) (s, s')"
    fix t
    assume a2:"t \<le> (tr<s'>-tr<s>)"
    have "\<exists> s''. wait<s''> \<and> tr<s''> = tr<s>@t \<and> (P ;;\<^sub>d Q) (s, s'')"
    proof (cases "P(s, s') \<and> wait<s'>")
      case True
      then have l1:"\<exists> s''. wait<s''> \<and> tr<s''> = tr<s>@t \<and> P(s,s'')"
        using assms(1) prefix_closed_def a2 by blast
      obtain s'' where as1:"wait<s''>" and as2:"tr<s''> = tr<s>@t" and as3: "P(s,s'')"
        using l1 by blast
      have " (P ;;\<^sub>d Q) (s, s'')"
        using seq_comp_dlchp_def as1 as3
        by (metis (no_types, lifting) old.prod.case) 
      then show ?thesis
        using  as1 as2 by blast
    next
      case False
      have l2:"(\<exists> s\<^sub>0. P(s,s\<^sub>0) \<and> \<not>wait<s\<^sub>0> \<and> Q (s\<^sub>0, s'))"
        using a1 False seq_comp_dlchp_def
        by (smt (verit) case_prodD)
      obtain s\<^sub>0 where s01: "P(s,s\<^sub>0)" and s02:"\<not>wait<s\<^sub>0>" and s03:"Q (s\<^sub>0, s')"
        using l2 by blast
      have ltr1:"tr<s> \<le> tr<s\<^sub>0>"
        using s01 assms(3) Healthy_def R1_def
        by (metis (no_types, lifting) SEXP_def conj_pred_def get_post get_pre inf_apply
            inf_bool_def) 
      moreover have ltr2:"tr<s\<^sub>0> \<le> tr<s'>"
        using s03 assms(4) Healthy_def R1_def
        by (metis (no_types, lifting) SEXP_def conj_pred_def get_post get_pre inf_apply
            inf_bool_def) 
      ultimately have "(tr<s\<^sub>0>-tr<s>) \<le> (tr<s'>-tr<s>)"
        using minus_cancel_le by blast
      then have l3:"t\<le>(tr<s\<^sub>0>-tr<s>)  \<or> (tr<s\<^sub>0>-tr<s>) \<le> t"
        using a2 le_common_total by blast
      show ?thesis
      proof (cases "t\<le>(tr<s\<^sub>0>-tr<s>)")
        case True
        then have l4:"\<exists> s''. wait<s''> \<and> tr<s''> = tr<s>@t \<and> P(s,s'')"
          using s01 assms(1) prefix_closed_def by blast
        obtain s'' where as4:"wait<s''>" and  as5:"tr<s''> = tr<s>@t" and as6:"P(s,s'')"
          using l4 by blast
        have "(P ;;\<^sub>d Q) (s, s'')"
          using as6 as4 seq_comp_dlchp_def
          by (metis (no_types, lifting) curryD curry_case_prod)
        then show ?thesis
          using as5 as4 by blast          
      next
        case False
        then have l5:"(tr<s\<^sub>0>-tr<s>) \<le> t"
          using l3 by auto
        then have l6: "(tr<s\<^sub>0>) \<le> tr<s>@t"
          using ltr1 by force
        moreover have "tr<s>@t \<le> tr<s'>"
          using a2 ltr1 ltr2 by fastforce
        ultimately have "((tr<s>@t) - tr<s\<^sub>0>) \<le> (tr<s'> - tr<s\<^sub>0>)"
          by (meson minus_cancel_le)
        then have l6:"\<exists> s''. wait<s''> \<and> tr<s''> = tr<s>@t \<and> Q(s\<^sub>0,s'')"
          using assms(2) prefix_closed_def
          by (metis (no_types, lifting) Prefix_Order.prefixE append_minus l6 s03)
        obtain s'' where as7:" wait<s''>" and as8:"tr<s''> = tr<s>@t" and as9:"Q(s\<^sub>0,s'')"
          using l6 by blast
        have "(P ;;\<^sub>d Q) (s, s'')"
          using as9 s01 s02 seq_comp_dlchp_def
          by (metis (mono_tags, lifting) case_prod_conv)
        then show ?thesis
          using as7 as8 by auto
      qed
    qed
  }
  then show ?thesis
    using prefix_closed_def by blast
qed

lemma total_seq_comp :
  assumes "total P" "total Q"
  shows "total (P ;;\<^sub>d Q)"
  using assms
  apply(simp add: total_def seq_comp_dlchp_def)
  by(auto)

lemma waits_wf_seq_comp:
  assumes "waits_wf P" "waits_wf Q"
  shows "waits_wf  (P ;;\<^sub>d Q)"
  using assms
  apply(simp add:seq_comp_dlchp_def waits_wf_def)
  by (metis (mono_tags, lifting) old.prod.case skip_def)

lemma r1_assign:
  "(x :=\<^sub>d e) is R1"
  apply(simp add: assign_dlchp_def Healthy_def R1_def)
  apply(pred_simp)
  by fastforce

lemma prefix_closed_assign:
  "prefix_closed (x :=\<^sub>d e)"
  apply(simp add: assign_dlchp_def prefix_closed_def)
  apply(pred_simp)
  by blast

lemma total_assign:
  "total (x :=\<^sub>d e)"
  apply(simp add: assign_dlchp_def total_def)
  apply(pred_simp)
  by blast

lemma waits_wf_assign:
  "waits_wf (x :=\<^sub>d e)"
  apply(simp add: assign_dlchp_def waits_wf_def)
  apply(pred_simp)
  by blast

lemma r1_ndet_assign:
  "(x :=\<^sub>d \<star>) is R1"
  apply(simp add: ndet_assign_dlchp_def Healthy_def R1_def)
  apply(pred_simp)
  by fastforce

lemma prefix_closed_ndet_assign:
  "prefix_closed (x :=\<^sub>d \<star>)"
  apply(simp add: ndet_assign_dlchp_def prefix_closed_def)
  apply(pred_simp)
  by (metis Prefix_Order.prefix_Nil minus_cancel)

lemma total_ndet_assign:
  "total (x :=\<^sub>d \<star>)"
  apply(simp add: ndet_assign_dlchp_def total_def)
  apply(pred_simp)
  by blast

lemma waits_wf_ndet_assign:
  "waits_wf (x :=\<^sub>d \<star>)"
  apply(simp add: ndet_assign_dlchp_def waits_wf_def)
  apply(pred_simp)
  by blast

lemma r1_power:
  assumes "P is R1"
  shows "P ^\<^sup>d n is R1"
proof (induction n)
      case 0
      then show ?case 
        using r1_test
        by fastforce
    next
      case (Suc n)
      then show ?case 
        using r1_seq_comp assms
        by auto
    qed
  
lemma r1_loop:
  assumes "P is R1"
  shows "P\<^sup>d is R1"
  apply(simp add: loop_dlchp_def)
  using r1_power assms
  by (metis UINF_ind_R1_closed)

lemma prefix_closed_power:
  assumes "prefix_closed P" "P is R1"
  shows "prefix_closed (P^\<^sup>d n)"
    proof (induction n)
      case 0
      then show ?case 
        using prefix_closed_test
          by fastforce
    next
      case (Suc n)
      then show ?case
        using prefix_closed_seq_comp assms r1_power
        by auto
    qed

lemma prefix_closed_Inf:
  assumes "\<forall>P \<in> A. prefix_closed P"
  shows "prefix_closed (\<Sqinter> A)"
  by (smt (z3) Sup1_E Sup1_I assms prefix_closed_def)

lemma prefix_closed_loop:
  assumes "prefix_closed P" "P is R1"
  shows "prefix_closed (P\<^sup>d)"
proof -
  have "\<forall> i. prefix_closed ( P ^\<^sup>d i)"
    using prefix_closed_power assms
    by auto
  then have "prefix_closed ( \<Sqinter> range ((^\<^sup>d) P))"
    using prefix_closed_Inf
    by (metis f_inv_into_f)
  then show ?thesis
    using  loop_dlchp_def
    by metis
qed

lemma total_power:
  assumes "total P"
  shows "total (P ^\<^sup>d n)"
  proof (induction n)
    case 0
    then show ?case 
      by (metis total_test upower_dlchp.simps(1))
  next
    case (Suc n)
    then show ?case 
      using Suc upower_dlchp.simps(2) total_seq_comp assms by metis
  qed

lemma total_loop:
  shows "total (P\<^sup>d)"
  apply(simp add: loop_dlchp_def total_def)
  by (metis total_def total_test upower_dlchp.simps(1))


lemma waits_wf_power:
  assumes "waits_wf P"
  shows "waits_wf (P ^\<^sup>d n)"
  proof (induction n)
      case 0
      then show ?case 
        using upower_dlchp.simps(1) waits_wf_test
        by auto
    next
      case (Suc n)
      then show ?case
        using Suc upower_dlchp.simps(2) waits_wf_seq_comp assms by auto
  qed

lemma waits_wf_loop:
  assumes "waits_wf P"
  shows "waits_wf (P\<^sup>d)"
  using loop_dlchp_def waits_wf_power assms
  by (smt (verit) SUP1_E Sup_apply Sup_bool_def image_eqI range_eqI waits_wf_def)



lemma r1_receive:
  shows "(c?\<^sub>dx) is R1"
  apply(simp add: inp_dlchp_def)
  apply(pred_simp)
  by fastforce

lemma prefix_closed_receive:
  shows "prefix_closed (c?\<^sub>dx)"
  apply(simp add: prefix_closed_def inp_dlchp_def)
  apply(auto)
  apply(pred_simp)
  apply (metis (no_types, opaque_lifting) Prefix_Order.prefix_Nil Prefix_Order.prefix_snoc append_Nil
      srea_vars.simps(1))
  apply(pred_simp)
    apply (metis (no_types, opaque_lifting) Prefix_Order.prefix_Nil Prefix_Order.prefix_snoc append_Nil
      srea_vars.simps(1))
   apply(pred_simp)
   apply (metis (no_types, opaque_lifting) Prefix_Order.prefix_Nil Prefix_Order.prefix_snoc append_Nil
      srea_vars.simps(1))
   apply(pred_simp)
  by (metis (no_types, opaque_lifting) Prefix_Order.prefix_Nil Prefix_Order.prefix_snoc append_Nil
      srea_vars.simps(1))

lemma total_receive:
  fixes x::"('a \<Longrightarrow> 's::scene_space time_alpha_scheme)" and c::"('a \<Rightarrow> 'e::channel)" 
  shows "total (c?\<^sub>dx)"
proof -
  {
    fix s::"('s::scene_space, 'e::channel) dlCHP_alpha"

    have total_rhs: "\<exists> s'. ((c?\<^sub>dx)(s,s') \<and> wait<s'> \<and> tr<s'> = tr<s>)"
    proof (cases "wait<s>")
      case True
      have "(c?\<^sub>dx)(s,s)"
        apply(simp add: inp_dlchp_def)
        using True by auto
      then show ?thesis 
        using True by auto
    next
      case False
      obtain v :: 'a where True
        by simp
      
      define s' :: "('s::scene_space, 'e::channel) dlCHP_alpha"
        where "s' =
          put\<^bsub>wait\<^esub>
            (put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) v))
            True"
  
      have tr_s: "tr<s> = tr<s'>"
        unfolding s'_def
        by simp
  
      hence tr_1:"tr<s'> \<le> tr<s>@[(c v, time<s>)]"
        by force
  
      moreover have tr_2:"tr<s> \<le> tr<s'>"
        using tr_s by force
      
      moreover have w_s: "wait<s'>"
        unfolding s'_def
        by simp
      
      moreover have rest_s:
        "st<s'> = put\<^bsub>x\<^esub> (st<s>)  v \<and>
         ok<s'> = ok<s> "
        unfolding s'_def
        by simp

      ultimately have "(c?\<^sub>dx) (s,s')"
        apply(simp add: inp_dlchp_def)
        using False  by(auto)

      then show ?thesis 
        using tr_s w_s by auto
    qed
  }
  then show ?thesis 
    using total_def by blast
qed
    



lemma waits_wf_receive:
  shows "waits_wf  (c?\<^sub>dx)"
  apply(simp add:waits_wf_def inp_dlchp_def)
  by(pred_simp)

lemma r1_send:
  shows "(c!\<^sub>de) is R1"
  apply(simp add: out_dlchp_def)
  apply(pred_simp)
  by fastforce

lemma prefix_closed_send:
  shows "prefix_closed (c!\<^sub>dx)"
  apply(simp add: prefix_closed_def out_dlchp_def)
  apply(auto)
  apply(pred_simp)
     apply (metis (no_types, opaque_lifting) Prefix_Order.prefix_Nil Prefix_Order.prefix_snoc append_Nil
      srea_vars.simps(1))
  apply(pred_simp)
   apply (metis (no_types, opaque_lifting) Prefix_Order.prefix_Nil Prefix_Order.prefix_snoc append_Nil
      srea_vars.simps(1))
  apply(pred_simp)
   apply (metis (no_types, opaque_lifting) Prefix_Order.prefix_Nil Prefix_Order.prefix_snoc append_Nil
      srea_vars.simps(1))
  apply(pred_simp)
  by  (metis (no_types, opaque_lifting) Prefix_Order.prefix_Nil Prefix_Order.prefix_snoc append_Nil
      srea_vars.simps(1))

lemma total_send:
  fixes c::"('a \<Rightarrow> 'e::channel)"  and e::"('s::scene_space time_alpha_scheme \<Rightarrow> 'a)"
  shows "total (c!\<^sub>de)"
proof -
  {
    fix s::"('s::scene_space, 'e::channel) dlCHP_alpha"

    have total_rhs: "\<exists> s'. ((c!\<^sub>de)(s,s') \<and> wait<s'> \<and> tr<s'> = tr<s>)"
    proof (cases "wait<s>")
      case True
      have "(c!\<^sub>de)(s,s)"
        apply(simp add: out_dlchp_def)
        using True by auto
      then show ?thesis 
        using True by auto
    next
      case False
      define s' :: "('s::scene_space, 'e::channel) dlCHP_alpha"
        where "s' = put\<^bsub>wait\<^esub> s True"
  
      have tr_s: "tr<s> = tr<s'>"
        unfolding s'_def
        by simp
  
      hence tr_1:"tr<s'> \<le> tr<s>@[(c(e(st<s>)), time<s>)]"
        by force
  
      moreover have tr_2:"tr<s> \<le> tr<s'>"
        using tr_s by force
      
      moreover have w_s: "wait<s'>"
        unfolding s'_def
        by simp
      
      moreover have rest_s:
        "st<s'> = st<s> \<and>
         ok<s'> = ok<s> "
        unfolding s'_def
        by simp

      ultimately have "(c!\<^sub>de) (s,s')"
        apply(simp add: out_dlchp_def)
        using False  by(auto)

      then show ?thesis 
        using tr_s w_s by auto
    qed
  }
  then show ?thesis 
    using total_def by blast
qed
    

lemma waits_wf_send:
  shows "waits_wf  (c!\<^sub>dx)"
  apply(simp add:waits_wf_def out_dlchp_def)
  by(pred_simp)





lemma r1_diff:
  shows "(Dyn_SysC x \<sigma> G) is R1"
  apply(simp add: Dyn_SysC_def Healthy_def R1_def )
  by(pred_auto)


lemma prefix_closed_diff:
  shows "prefix_closed (Dyn_SysC x \<sigma> G)"
  apply(simp add: Dyn_SysC_def prefix_closed_def )
  by(pred_auto)

lemma total_diff:
  shows "total  (Dyn_SysC x \<sigma> G)"
  apply(simp add: Dyn_SysC_def total_def )
  by(pred_auto)

lemma waits_wf_diff:
  shows "waits_wf  (Dyn_SysC x \<sigma> G)"
  apply(simp add: Dyn_SysC_def waits_wf_def )
  by(pred_auto)

  



end