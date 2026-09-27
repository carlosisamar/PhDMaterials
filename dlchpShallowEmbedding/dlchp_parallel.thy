theory dlchp_parallel
  imports "dlchp_operators"
begin

unbundle UTP_Syntax

notation lens_get ("(_<_>)" [76, 0] 75)

lemma trace_rest_paral_trivial:
  assumes "t \<in> (traces(parallel P Q))"
  shows "trace_restriction_paral t P Q = t"
  using assms
  apply(simp add: traces_def parallel_def trace_restriction_paral_def)
  apply(auto)
  done

lemma channel_names_paral: "CN(parallel P Q) \<subseteq> (CN P) \<union> (CN Q)"
proof -
  have "\<forall> t \<in> (traces(parallel P Q)). trace_restriction_paral t P Q = t"
    using trace_rest_paral_trivial
    by blast
  moreover have "\<forall> t. (channels_from_trace (trace_restriction_paral t P Q)) \<subseteq>  ((CN P) \<union> (CN Q) )"
    using trace_restriction_paral_def
    by (metis trace_rest_channels)
  ultimately have "\<forall> t \<in> (traces(parallel P Q)). (channels_from_trace t) \<subseteq>  ((CN P) \<union> (CN Q) )"
    by metis
  then show ?thesis
    using CN_def
    by (smt (verit) mem_Collect_eq subsetD subsetI)
qed


lemma trace_preservance:
  assumes  "(parallel P Q) (s, s')"
  shows "\<exists> ptr. tr<s'> = tr<s> @ ptr"
proof-
   obtain s'' ptr w t where ass_1:" s' = put\<^bsub>time\<^esub>(put\<^bsub>wait\<^esub>  (put\<^bsub>tr\<^esub> s'' ( tr<s> @ ptr)) w) t"
     using parallel_def assms
     by (smt (verit) old.prod.case)
   thus ?thesis 
     using weak_lens.put_get
     by auto
 qed

lemma trace_rest_suffix:
  assumes  "(parallel P Q) (s, s\<^sub>0)" "tr<s\<^sub>0> = tr<s> @ ptr"
  shows "trace_restriction_paral ptr P Q = ptr"
proof-
obtain s'' ptr' w t where ass_1:" s\<^sub>0 = put\<^bsub>time\<^esub> (put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> s'' ( tr<s> @ ptr')) w) t" and ass_2:"trace_restriction_paral ptr' P Q = ptr'"
  proof -
    have "(\<exists> s' s'' ptr''. s\<^sub>0 = put\<^bsub>time\<^esub> (put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (s'' \<oplus>\<^sub>S s' on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr'')) (wait<s'> \<or> wait<s''>)) (if (wait<s'> \<or> wait<s''>) then (if (time<s'> = time<s''>) then time<s'> else -1 ) else time<s'>)  \<and>   
                                             P (s, s') \<and>   Q (s, s'') \<and>
                                             ptr'' \<downharpoonright> P = (tr<s'> - tr<s>) \<and>  ptr'' \<downharpoonright> Q = (tr<s''>  - tr<s>) \<and> 
                                             (((wait<s'> \<or> wait<s''>)) \<or>( (time<s'> = time<s''>))) \<and>
                                             trace_restriction_paral ptr'' P Q = ptr'')"
      using assms(1)
      by (simp add: parallel_def)
    with that show ?thesis
      by auto
  qed
  have "tr<s\<^sub>0> = tr<s> @ ptr'"
    using weak_lens.put_get ass_1
    by auto
  then have "ptr' = ptr"
    using assms(2) by force
  thus ?thesis
    using ass_2
    by simp
qed

      

lemma r1_preservance_parallel:
  shows "(parallel P Q) is R1"
proof -
  {
  fix s s\<^sub>0
  assume para1: "(parallel P Q) (s, s\<^sub>0)"
  obtain ptr where "tr<s\<^sub>0> = tr<s> @ ptr"
    using trace_preservance para1 by blast
  then have "tr<s> \<le> tr<s\<^sub>0>"
    by auto
}
  thus ?thesis
    by (simp add: R1_by_refinement pred_refine_iff subst_app_def subst_ext_def)
qed


definition ppl :: "('s::scene_space, 'e::channel) dlCHP_alpha \<Rightarrow>('s::scene_space, 'e::channel) dlCHP_alpha \<Rightarrow> ('e \<times> real) list \<Rightarrow> ('e \<times> real) list \<Rightarrow> ('s::scene_space, 'e::channel) dlCHP_alpha scene set \<Rightarrow> 'e set set \<Rightarrow> bool" where
"ppl w ps tw tps BVP CNP = ((w \<approx>\<^sub>S ps on (\<Union>\<^sub>S  BVP)) \<and> (tps  = trace_restriction_channels tw CNP ) \<and> (wait<ps> \<longrightarrow> wait<w>) \<and> (\<not>wait<w> \<longrightarrow> time<ps> = time<w>))"

lemma ppl_ext:
  assumes "(parallel P Q) (s, w)"
  shows "\<exists> ps. P (s, ps) \<and> ppl w ps (tr<w>-tr<s>) (tr<ps>-tr<s>) (BV_progs P - observables) (CN P) "
proof -
  obtain ps' qs  ptr where ass1:"w = put\<^bsub>time\<^esub>(put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (qs \<oplus>\<^sub>S ps' on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr)) (wait<ps'> \<or> wait<qs>))(if (wait<ps'> \<or> wait<qs>) then (if (time<ps'> = time<qs>) then time<ps'> else -1 ) else time<ps'>)" and  ass2:"P (s, ps')" 
                                             and ass3: "ptr \<downharpoonright> P = (tr<ps'> - tr<s>)" and ass4: "time<ps'> = time<qs> \<or> (wait<ps'> \<or> wait<qs>)"
  proof -
    have "(\<exists> s' s'' ptr''. w =  put\<^bsub>time\<^esub> (put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (s'' \<oplus>\<^sub>S s' on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr'')) (wait<s'> \<or> wait<s''>)) (if (wait<s'> \<or> wait<s''> ) then (if (time<s'> = time<s''>) then time<s'> else -1 ) else time<s'>)  \<and>   
                                             P (s, s') \<and>   Q (s, s'') \<and>
                                             ptr'' \<downharpoonright> P = (tr<s'> - tr<s>) \<and>  ptr'' \<downharpoonright> Q = (tr<s''>  - tr<s>) \<and> 
                                             (((wait<s'> \<or> wait<s''>)) \<or>( (time<s'> = time<s''>))) \<and>
                                             trace_restriction_paral ptr'' P Q = ptr'')"
      using assms
      by (simp add: parallel_def)
    with that show ?thesis
      by auto      
  qed
  have "w \<approx>\<^sub>S ps' on \<Union>\<^sub>S (BV_progs P - observables)"
  proof -
    have "qs \<oplus>\<^sub>S ps' on (\<Union>\<^sub>S ( BV_progs P)) \<approx>\<^sub>S ps' on \<Union>\<^sub>S (BV_progs P)"
      by (simp add: scene_equiv_def)
    then have "(put\<^bsub>tr\<^esub> (qs \<oplus>\<^sub>S ps' on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr)) \<approx>\<^sub>S ps' on \<Union>\<^sub>S (BV_progs P - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
      using scene_union_put_preserved 
      by (metis BV_is_vars tr_is_var tr_vwb_lens)
    then have "put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (qs \<oplus>\<^sub>S ps' on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr)) (wait<ps'> \<or> wait<qs>) \<approx>\<^sub>S ps' on \<Union>\<^sub>S (BV_progs P - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>} - {\<lbrakk>wait\<rbrakk>\<^sub>\<sim>})"
      using scene_union_put_preserved
      by (metis BV_is_vars Diff_subset_conv le_supI2 wait_is_var wait_vwb_lens)
    then have "put\<^bsub>time\<^esub>(put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (qs \<oplus>\<^sub>S ps' on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr)) (wait<ps'> \<or> wait<qs>))(if (wait<ps'> \<or> wait<qs> ) then (if (time<ps'> = time<qs>) then time<ps'> else -1 ) else time<ps'>)
                \<approx>\<^sub>S ps' on \<Union>\<^sub>S (BV_progs P - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>} - {\<lbrakk>wait\<rbrakk>\<^sub>\<sim>} -  {\<lbrakk>time\<rbrakk>\<^sub>\<sim>})" 
      using scene_union_put_preserved
      by (smt (verit) BV_is_vars Diff_empty Diff_insert0 insert_Diff insert_subset ns_alpha_vwb st_vwb_lens
          time_is_var time_var_vwb_lens)
    thus ?thesis
      using observables_def ass1
      by (metis (no_types, opaque_lifting) Diff_insert insert_commute)
  qed
  moreover have "wait<ps'> \<longrightarrow> wait<w>"
    by (simp add: ass1)
  moreover have " (tr<ps'>-tr<s>) = (tr<w>-tr<s>)\<downharpoonright> P"
    by (simp add: ass1 ass3)
  moreover have "\<not>wait<w> \<longrightarrow>time<w> = time<ps'>"
  proof -
    {
      assume aw1:"\<not> wait<w>"
      have "wait \<bowtie> time"
        using time_is_var wait_is_var  rea_vars.indeps(3)
        using ns_alpha_indep_3 srea_vars.indeps(8) by blast
      then have "\<not>(wait<ps'> \<or> wait<qs>)"
        using aw1 ass1 wait_vwb_lens
        by auto
      then have "time<w> = time<ps'>"
        using ass1 ass4
        by simp
    }
    then show ?thesis
      by auto
  qed
  ultimately have "ppl w ps' (tr<w>-tr<s>) (tr<ps'>-tr<s>) (BV_progs P - observables) (CN P)"
    by (metis (no_types, lifting)  ppl_def trace_restriction_prog_def trace_restriction_channels_def)
  thus ?thesis
    using ass2
    by blast
qed

definition ppr :: "('s::scene_space, 'e::channel) dlCHP_alpha \<Rightarrow> ('s::scene_space, 'e::channel) dlCHP_alpha \<Rightarrow> ('e \<times> real) list \<Rightarrow> ('e \<times> real) list \<Rightarrow> ('s, 'e) dlCHP_alpha scene set \<Rightarrow> 'e set set \<Rightarrow> bool" where
  "ppr w qs tw tqs BVP CNQ =  ((w \<approx>\<^sub>S qs on -(\<Union>\<^sub>S  BVP)) \<and> (tqs  = trace_restriction_channels tw CNQ )\<and> (wait<qs> \<longrightarrow> wait<w>) \<and> (\<not>wait<w> \<longrightarrow> time<qs> = time<w>))"

lemma ppr_ext:
  assumes "(parallel P Q) (s, w)"
  shows "\<exists> qs. Q (s, qs) \<and> ppr w qs (tr<w>-tr<s>) (tr<qs>-tr<s>) (BV_progs P \<union> observables) (CN Q)"
proof -
  obtain ps qs' ptr where ass1:"w = put\<^bsub>time\<^esub>(put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (qs' \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr)) (wait<ps> \<or> wait<qs'>))(if (wait<ps> \<or> wait<qs'> ) then (if (time<ps> = time<qs'>) then time<ps> else -1 ) else time<ps>)" and  ass2:"Q (s, qs')" 
                                             and ass3: "ptr \<downharpoonright> Q = (tr<qs'> - tr<s>)" and ass4: "time<ps> = time<qs'> \<or> (wait<ps> \<or> wait<qs'>)"
  proof -
    have "(\<exists> s' s'' ptr''. w = put\<^bsub>time\<^esub> (put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (s'' \<oplus>\<^sub>S s' on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr'')) (wait<s'> \<or> wait<s''>)) (if (wait<s'> \<or> wait<s''> ) then (if (time<s'> = time<s''>) then time<s'> else -1 ) else time<s'>)  \<and>   
                                             P (s, s') \<and>   Q (s, s'') \<and>
                                             ptr'' \<downharpoonright> P = (tr<s'> - tr<s>) \<and>  ptr'' \<downharpoonright> Q = (tr<s''>  - tr<s>) \<and> 
                                             (((wait<s'> \<or> wait<s''>)) \<or>( (time<s'> = time<s''>))) \<and>
                                             trace_restriction_paral ptr'' P Q = ptr'')"
      using assms
      by (simp add: parallel_def)
    with that show ?thesis
      by auto      
  qed
  have "w \<approx>\<^sub>S qs' on -\<Union>\<^sub>S (BV_progs P \<union> observables)"
  proof -
     have "qs' \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P)) \<approx>\<^sub>S qs' on -\<Union>\<^sub>S (BV_progs P)"
       by (simp add: scene_equiv_def scene_override_commute)
     then have "(put\<^bsub>tr\<^esub> (qs' \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr)) \<approx>\<^sub>S qs' on -\<Union>\<^sub>S (BV_progs P \<union> {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
       using scene_union_neg_put_preserved
       by (metis BV_is_vars tr_is_var tr_vwb_lens)
     then have "put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (qs' \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr)) (wait<ps> \<or> wait<qs'>) \<approx>\<^sub>S qs' on -\<Union>\<^sub>S (BV_progs P \<union> {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>} \<union> {\<lbrakk>wait\<rbrakk>\<^sub>\<sim>})"
       using scene_union_neg_put_preserved wait_is_var
       by (metis BV_is_vars empty_subsetI insert_subset le_sup_iff tr_is_var wait_vwb_lens)
     then have "put\<^bsub>time\<^esub>(put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (qs' \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr)) (wait<ps> \<or> wait<qs'>))(if (wait<ps> \<or> wait<qs'> ) then (if (time<ps> = time<qs'>) then time<ps> else -1 ) else time<ps>)
                \<approx>\<^sub>S qs' on -\<Union>\<^sub>S (BV_progs P \<union> {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>} \<union> {\<lbrakk>wait\<rbrakk>\<^sub>\<sim>} \<union> {\<lbrakk>time\<rbrakk>\<^sub>\<sim>})" 
        using scene_union_neg_put_preserved time_is_var
        by (metis BV_is_vars Un_subset_iff bot_least insert_subsetI ns_alpha_vwb st_vwb_lens time_var_vwb_lens
            tr_is_var wait_is_var)
     thus ?thesis
       using observables_def ass1
       by (metis (no_types, lifting) boolean_algebra_cancel.sup1 insert_is_Un)
   qed
  moreover have "wait<qs'> \<longrightarrow> wait<w>"
    by (simp add: ass1)
  moreover have " (tr<qs'>-tr<s>) = (tr<w>-tr<s>)\<downharpoonright> Q"
    by (simp add: ass1 ass3)
  moreover have "\<not>wait<w> \<longrightarrow>time<w> = time<qs'>"
  proof -
    {
      assume aw1:"\<not> wait<w>"
      have "wait \<bowtie> time"
        using time_is_var wait_is_var rea_vars.indeps(3)
        using ns_alpha_indep_3 srea_vars.indeps(8) by blast
      then have aw2:"\<not>(wait<qs'> \<or> wait<ps>)"
        using aw1 ass1 wait_vwb_lens
        by auto
      then have "time<w> = time<ps>"
        using ass1 ass4
        by simp
      then have "time<w> = time<qs'>"
        using ass4 aw2 by auto
    }
    then show ?thesis
      by auto
  qed
  ultimately have "ppr w qs' (tr<w>-tr<s>) (tr<qs'>-tr<s>) (BV_progs P \<union> observables) (CN Q)"
    using ppr_def
    by (metis (no_types, lifting)  trace_restriction_prog_def trace_restriction_channels_def) 
  thus ?thesis
    using ass2
    by blast
qed



lemma parallel_partial:
  assumes " ((parallel P Q) (s, w))" "ppr w wq (tr<w>-tr<s>) (tr<wq>-tr<s>) (BV_progs P \<union> observables) (CN Q) "  "ppl w ps (tr<w>-tr<s>) (tr<ps>-tr<s>) (BV_progs P - observables) (CN P)"
  shows "w \<approx>\<^sub>S (wq \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P))) on -(\<Union>\<^sub>S observables )"
 proof -
    have "w \<approx>\<^sub>S wq on -(\<Union>\<^sub>S  (BV_progs P \<union> observables))"
      using ppr_def assms(2) by blast 
    moreover have "w \<approx>\<^sub>S ps on (\<Union>\<^sub>S  (BV_progs P - observables))"
      using ppl_def assms(3) by blast
    ultimately show ?thesis
      using scene_agreement_decomp2 BV_is_vars observables_is_vars
      by metis
  qed

lemma naive_para:
  assumes " (parallel P Q) (s, w)"
  shows "\<exists> ns'. (para_dl P Q) (s, ns') \<and> ns' \<approx>\<^sub>S w on -(\<Union>\<^sub>S observables) " 
proof -
  obtain ps where  ps1:"P (s, ps)" and ps2:"ppl w ps (tr<w>-tr<s>) (tr<ps>-tr<s>) (BV_progs P - observables) (CN P)"
    using ppl_ext assms
    by blast
  obtain qs where qs1:"Q (s, qs)" and qs2:"ppr w qs (tr<w>-tr<s>) (tr<qs>-tr<s>) (BV_progs P \<union> observables) (CN Q)"
    using ppr_ext assms
    by blast
  obtain ns where ns1: "ns =  qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S (BV_progs P))"
    by blast
  have "(para_dl P Q) (s, ns)"
    using ps1 qs1 para_dl_def ns1
    by (metis (mono_tags, lifting) curryD curry_case_prod)
  moreover have  "ns \<approx>\<^sub>S w on -(\<Union>\<^sub>S observables)"
    using ns1 ps2 qs2 
    by (metis (no_types, lifting) Sup_scene_closed assms idem_scene_space idem_scene_uminus
        parallel_partial scene_equiv_sym)
  ultimately show ?thesis
    by blast
qed

lemma naive_para_left:
  assumes "ns' \<approx>\<^sub>S w on -(\<Union>\<^sub>S observables)" "ppl w sa (tr<s'>-tr<s>) (tr<sa>-tr<s>) (BV_progs P - observables) (CN P)"  "partial_left ns' ps P" "P (s, ps)" "P (s, sa)" 
  shows "sa \<approx>\<^sub>S ps on -(\<Union>\<^sub>S observables)"
proof -
  have "sa \<approx>\<^sub>S w on (\<Union>\<^sub>S (BV_progs P - observables))"
    using assms(2) ppl_def scene_comm by blast
  moreover have "ns' \<approx>\<^sub>S ps on  (\<Union>\<^sub>S (BV_progs P))"
    using assms(3) partial_left_def by blast
  ultimately have l1:"sa \<approx>\<^sub>S ps on (\<Union>\<^sub>S (BV_progs P - observables))"
    using assms(1) scene_comm
    by (smt (verit, ccfv_SIG) BV_is_vars Diff_Int_distrib2 Diff_eq Diff_subset diff_shunt_var
        observables_is_vars scene_minus scene_subset_agreement)
  have "sa \<approx>\<^sub>S s on  -(\<Union>\<^sub>S (BV_progs P))"
    by (metis Sup_scene_closed assms(5) bound_eff_1 bound_eff_prop_def idem_scene_space
        scene_equiv_sym scene_space_uminus)
  moreover have "ps \<approx>\<^sub>S s on  -(\<Union>\<^sub>S (BV_progs P))"
    by (metis Sup_scene_closed assms(4) bound_eff_1 bound_eff_prop_def idem_scene_space
        idem_scene_uminus scene_equiv_sym)
  ultimately have "sa \<approx>\<^sub>S ps on  -(\<Union>\<^sub>S (BV_progs P))"
    by (metis scene_equiv_def scene_override_commute scene_override_overshadow_left)
  then have "sa \<approx>\<^sub>S ps on  (\<Union>\<^sub>S ((BV_progs P - observables) \<union> (set Vars - BV_progs P)))"
    using l1 scene_minus
    by (smt (verit, ccfv_threshold) BV_is_vars Diff_subset Un_iff dual_order.trans le_sup_iff
        scene_union_equiv set_Vars_scene_space)
  then have "sa \<approx>\<^sub>S ps on (\<Union>\<^sub>S (set Vars - observables))"
    using BV_is_vars
    by (smt (verit) Diff_iff Diff_partition Diff_subset \<open>sa \<approx>\<^sub>S ps on - \<Union>\<^sub>S (BV_progs P)\<close> l1
        le_sup_iff scene_neg_decomp scene_union_equiv set_Vars_scene_space) 
  then show ?thesis
    using scene_minus observables_is_vars
    by metis
qed

definition non_inter_dlchp ::  "('s::scene_space, 'e::channel) dlCHP_rel \<Rightarrow> ('s::scene_space, 'e::channel) dlCHP_rel \<Rightarrow> (bool, 's::scene_space, 'e::channel) dlCHP_expr \<Rightarrow> bool" where
  "non_inter_dlchp P Q F = (((BV_progs P) \<inter> (FV F) \<subseteq> {\<lbrakk>time\<rbrakk>\<^sub>\<sim>,\<lbrakk>tr\<rbrakk>\<^sub>\<sim>}) \<and> ((CN_term F) \<inter> (CN P) \<subseteq> (CN Q)))"

definition non_inter_dlchp_comp :: "('s::scene_space, 'e::channel) dlCHP_rel \<Rightarrow> ('s::scene_space, 'e::channel) dlCHP_rel \<Rightarrow> (bool, 's::scene_space, 'e::channel) dlCHP_expr \<Rightarrow> (bool, 's::scene_space, 'e::channel) dlCHP_expr\<Rightarrow> (bool, 's::scene_space, 'e::channel) dlCHP_expr \<Rightarrow> bool" where
 "non_inter_dlchp_comp P Q F A C = (non_inter_dlchp P Q F \<and> non_inter_dlchp P Q A \<and> non_inter_dlchp P Q C)"

lemma non_inter_safe1:
  fixes s s'
  assumes "non_inter_dlchp Q P A" "(parallel P Q) (s, s')" 
  shows "A (trace_state_conc s ((tr<s'> - tr<s>)\<downharpoonright> P)) \<longleftrightarrow> A (trace_state_conc s (tr<s'> - tr<s>))" 
proof -
  have "(tr<s'> - tr<s>) = (tr<s'> - tr<s>)\<downharpoonright> (parallel P Q)"
    by (simp add: assms(2) trace_rest_contr)
  moreover have "(tr<s'> - tr<s>) \<in> traces(parallel P Q)"
    using assms(2) traces_def by blast
  ultimately have f0:"channels_from_trace (tr<s'> - tr<s>) \<subseteq> (CN P) \<union> (CN Q)"
    using channel_names_paral
    by (metis (no_types, lifting) channels_from_trace_cn subset_trans)
  have "(trace_restriction_channels ((tr<s'> - tr<s>)\<downharpoonright> P) (CN_term A)) = (trace_restriction_channels (tr<s'> - tr<s>) (CN_term A))"
  proof -
    have "channels_from_trace(trace_restriction_channels (tr<s'> - tr<s>) (CN_term A)) \<subseteq>(CN P) \<union> (CN Q)"
      using f0 trace_rest_restricts
      by blast
    moreover have "channels_from_trace(trace_restriction_channels (tr<s'> - tr<s>) (CN_term A)) \<subseteq> (CN_term A)"
      using trace_rest_channels by blast
    ultimately have "channels_from_trace(trace_restriction_channels (tr<s'> - tr<s>) (CN_term A))\<subseteq>(CN P)"
      using assms(1) non_inter_dlchp_def
      by blast
    then show ?thesis
      using trace_rest_subset trace_rest_channels_comm2
      by (metis (no_types, lifting) trace_restriction_prog_def)
  qed
  then  have f0:"trace_restriction_state (trace_state_conc s ((tr<s'> - tr<s>)\<downharpoonright> P)) (CN_term A) = trace_restriction_state (trace_state_conc s (tr<s'> - tr<s>)) (CN_term A)"
    apply(auto simp add: trace_restriction_state_def trace_state_conc_def)
    by (simp add: trace_restriction_channels_def)
  then  have "(trace_restriction_state (trace_state_conc s ((tr<s'> - tr<s>)\<downharpoonright> P)) (CN_term A)) \<approx>\<^sub>S (trace_restriction_state (trace_state_conc s (tr<s'> - tr<s>)) (CN_term A)) on (\<Union>\<^sub>S (FV A))"
    apply(simp add: f0)
    by (meson Sup_scene_closed idem_scene_space scene_equiv_refl)
  then show ?thesis
    using coincidence_eff_prop_term_dlchp1 coincidence_eff_prop_term_dlchp_def
    by blast
qed
    



lemma non_inter_safe3:
  fixes s s' sa
  assumes "non_inter_dlchp Q P F" "(parallel P Q) (s, s')" "P(s, sa)" "ppl s' sa (tr<s'>-tr<s>) (tr<sa>-tr<s>) (BV_progs P - observables) (CN P)" "P is R1"
  shows "\<not>wait<s'> \<longrightarrow> (F sa = F s')" 
proof -
  {
    assume a0:"\<not> wait<s'>"
    obtain ns' where  a1:"(para_dl P Q) (s, ns')" and  a2:" ns' \<approx>\<^sub>S s' on -(\<Union>\<^sub>S observables)"
      using naive_para assms(2) by blast
    obtain ps' where  a3: "P (s, ps')" and a4:"partial_left ns' ps' P"
      using a1 partial_paral_left by blast
    have l0:"ps' \<approx>\<^sub>S sa on -\<Union>\<^sub>S (observables)"
      using naive_para_left
      by (metis a2 a3 a4 assms(3,4) observables_is_vars scene_comm scene_minus)
    then have l1:"ns' \<approx>\<^sub>S ps' on -\<Union>\<^sub>S (BV_progs Q \<union> observables)"
      using para_dl_non_inter4 a1 a3 a4 observables_is_vars
      by (smt (verit, ccfv_SIG) BV_is_vars Sup_scene_closed Un_commute mem_Vars_scene_space
          scene_compl_subset_iff scene_lessthan_equiv scene_space_uminus scene_subset_union_lessthan
          sup.bounded_iff sup_ge2)
    then have "ns' \<approx>\<^sub>S sa on -\<Union>\<^sub>S (BV_progs Q \<union> observables)"
    proof -
      have "set Vars - (BV_progs Q \<union> observables) \<subseteq> set Vars - observables"
        using BV_is_vars observables_is_vars by fastforce
      then have "ps' \<approx>\<^sub>S sa on -\<Union>\<^sub>S (BV_progs Q \<union> observables)"
        using l0 scene_minus scene_union_equiv BV_is_vars observables_is_vars set_Vars_scene_space
        by (smt (verit) Diff_partition scene_subset_equiv sup.bounded_iff)
      then show ?thesis
        using l1 
        by (metis scene_equiv_def scene_override_commute scene_override_overshadow_left)
    qed
    then have l2:"s' \<approx>\<^sub>S sa on  -\<Union>\<^sub>S (BV_progs Q \<union> observables)"
      using a2
      by (smt (verit, ccfv_threshold) BV_is_vars Diff_eq Diff_partition Int_commute
          Sup_scene_closed boolean_algebra.de_Morgan_disj idem_scene_space inf_le2 inf_left_commute
          le_sup_iff observables_is_vars scene_equiv_sym scene_minus scene_subset_agreement
          scene_subset_equiv set_Vars_scene_space)
    moreover have l3:"s' \<approx>\<^sub>S sa on (\<lbrakk>wait\<rbrakk>\<^sub>\<sim>)"
      using a0 ppl_def assms(4)
      by (smt (verit, best) Scenes_extra.scene_equiv_get_eq wait_vwb_lens)
    moreover have t1: "s' \<approx>\<^sub>S sa on (\<lbrakk>time\<rbrakk>\<^sub>\<sim>)"
      using a0 ppl_def assms(4)
      by (metis (no_types, lifting) Scenes.scene_equiv_get_eq ns_alpha_vwb st_vwb_lens
          time_var_vwb_lens)
    moreover have l4:"trace_restriction_channels (tr<s'>) (CN_term F) = trace_restriction_channels (tr<sa>) (CN_term F)"
      proof-
        have "(tr<sa>-tr<s>)  = trace_restriction_channels (tr<s'>-tr<s>) (CN P)"
          using ppl_def assms(4)
          by metis
        then have "trace_restriction_channels (tr<sa>-tr<s>) (CN_term F) =  trace_restriction_channels (trace_restriction_channels (tr<s'>-tr<s>) (CN P)) (CN_term F)"
          by argo
        moreover have "trace_restriction_channels (tr<s'>-tr<s>) (CN_term F) =  trace_restriction_channels (trace_restriction_channels (tr<s'>-tr<s>) (CN P)) (CN_term F)"
          proof -
            have "channels_from_trace (tr<s'>-tr<s>) \<subseteq> (CN P) \<union> (CN Q)"
              by (metis (no_types, lifting) assms(2) channel_names_paral channels_from_trace_cn
                  subset_trans trace_rest_contr)
            then have "channels_from_trace (trace_restriction_channels (tr<s'>-tr<s>) (CN_term F))  \<subseteq> (CN P) \<union> (CN Q)"
              using trace_rest_restricts by blast
            then have "channels_from_trace (trace_restriction_channels (tr<s'>-tr<s>) (CN_term F))  \<subseteq> (CN P)"
              using assms(1) non_inter_dlchp_def
              by (smt (verit) IntI UnE subset_eq trace_rest_channels)
            then show ?thesis
              by (metis (no_types, lifting) trace_rest_channels_comm2 trace_rest_subset)
          qed
        ultimately have tr1:"trace_restriction_channels (tr<s'>-tr<s>) (CN_term F) = trace_restriction_channels (tr<sa>-tr<s>) (CN_term F)"
          by argo
        then show ?thesis
          proof -
            have "(R1 (parallel P Q)) (s, s') "
              using r1_preservance_parallel assms(2) Healthy_def by metis
            then have f1:"tr<s> \<le> tr<s'>"
              by (pred_simp)
            have "(R1  P ) (s, sa) "
              using  assms(3,5) Healthy_def by metis
            then have f2:"tr<s> \<le> tr<sa>"
              by (pred_simp)
            show ?thesis
              using tr1 f1 f2 restriction_prefix
              by blast
          qed
        qed
    ultimately have "trace_restriction_state s' (CN_term F) \<approx>\<^sub>S trace_restriction_state sa (CN_term F) on (\<Union>\<^sub>S (FV F))"
    proof -
      have "trace_restriction_state s' (CN_term F) \<approx>\<^sub>S trace_restriction_state sa (CN_term F) on (\<lbrakk>wait\<rbrakk>\<^sub>\<sim>)"
        by (metis Scenes_extra.scene_equiv_get_eq l3 lens_indep.lens_put_irr1
            rea_vars.indeps(1) trace_restriction_state_def wait_vwb_lens)
      moreover have l5:"trace_restriction_state s' (CN_term F) \<approx>\<^sub>S trace_restriction_state sa (CN_term F) on (\<lbrakk>tr\<rbrakk>\<^sub>\<sim>)"
        using l4
        by (metis Scenes_extra.scene_equiv_get_eq tr_vwb_lens trace_restriction_state_def
            vwb_lens_def wb_lens.axioms(1) weak_lens.put_get)
      moreover have l6:"trace_restriction_state s' (CN_term F) \<approx>\<^sub>S trace_restriction_state sa (CN_term F) on (\<lbrakk>time\<rbrakk>\<^sub>\<sim>)"
        using t1 l5 scene_equiv_sym scene_space_put_preserved time_is_var  tr_is_var
            tr_vwb_lens trace_restriction_state_def vwb_impl_idem_scene
        by (metis ns_alpha_vwb st_vwb_lens time_var_vwb_lens)
      moreover have "trace_restriction_state s' (CN_term F) \<approx>\<^sub>S trace_restriction_state sa (CN_term F) on -\<Union>\<^sub>S (BV_progs Q \<union> observables)"
      proof-
        have "trace_restriction_state s' (CN_term F) \<approx>\<^sub>S s' on -(\<lbrakk>tr\<rbrakk>\<^sub>\<sim>)"
          using state_conservation_rest_trace
          by (metis idem_scene_uminus scene_equiv_sym tr_vwb_lens vwb_impl_idem_scene)
        moreover have "trace_restriction_state sa (CN_term F) \<approx>\<^sub>S sa on -(\<lbrakk>tr\<rbrakk>\<^sub>\<sim>)"
          using state_conservation_rest_trace
          by (metis idem_scene_uminus scene_equiv_sym tr_vwb_lens vwb_impl_idem_scene)
        moreover have " -\<Union>\<^sub>S (BV_progs Q \<union> observables) \<le>  -(\<lbrakk>tr\<rbrakk>\<^sub>\<sim>)"
          using observables_def BV_is_vars observables_is_vars
          by (metis (no_types, lifting) Sup_scene_closed Un_insert_right insertCI insert_subset
              le_Sup_scene le_sup_iff scene_compl_subset_iff set_Vars_scene_space subset_trans)
        ultimately show ?thesis
          by (metis (no_types, lifting)  Sup_scene_closed 
               idem_scene_space idem_scene_uminus l2
              less_eq_scene_def scene_equiv_def scene_equiv_sym wait_def)
      qed
      ultimately have "trace_restriction_state s' (CN_term F) \<approx>\<^sub>S trace_restriction_state sa (CN_term F) on -\<Union>\<^sub>S (BV_progs Q)"
        using observables_def
        by (smt (verit, ccfv_threshold) BV_is_vars Un_insert_right insert_is_Un insert_subset
            observables_is_vars scene_agreement_neg_comp set_Vars_scene_space
            ss_clat.weak_sup_of_singleton subset_trans sup_commute)
      then have "trace_restriction_state s' (CN_term F) \<approx>\<^sub>S trace_restriction_state sa (CN_term F) on \<Union>\<^sub>S((set Vars - BV_progs Q) \<union> {\<lbrakk>time\<rbrakk>\<^sub>\<sim>} \<union> {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>})"
        using l5 l6
        by (smt (verit) BV_is_vars Diff_subset Un_insert_right insert_iff para_obs_def
            para_obs_is_vars scene_neg_decomp scene_union_equiv set_Vars_scene_space subset_eq
            sup_bot_right time_is_var)
      moreover have "FV F \<subseteq> (set Vars - BV_progs Q) \<union> {\<lbrakk>time\<rbrakk>\<^sub>\<sim>} \<union> {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>}"
        using non_inter_dlchp_def
        by (smt (verit) BV_is_vars Diff_Diff_Int Diff_partition Diff_subset_conv FV_Vars Int_Diff
            Int_commute Un_Int_eq(3) Un_insert_left Un_insert_right assms(1) sup_bot_right)
      ultimately show ?thesis
        using scene_union_equiv
        by (smt (verit, ccfv_SIG) Diff_subset Un_insert_right insert_subset para_obs_def
            para_obs_is_vars scene_subset_equiv set_Vars_scene_space subset_trans sup_bot_right
            time_is_var) 
    qed
    then have "(F sa = F s')"
      using coincidence_eff_prop_term_dlchp1 coincidence_eff_prop_term_dlchp_def
      by metis
  }
  then show ?thesis by auto
qed


lemma paral_comm_prev:
  assumes "BV_progs P \<inter> BV_progs Q \<subseteq> observables"
  shows "(Q \<parallel>\<^sub>d P) \<sqsubseteq> (P \<parallel>\<^sub>d Q)"
proof -
  {
    fix s s'
    assume a1:"(P \<parallel>\<^sub>d Q) (s,s')"
    have "(Q \<parallel>\<^sub>d P) (s, s')"
    proof -
      obtain ps qs  ptr where ass1:"s' = put\<^bsub>time\<^esub>(put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P))) ( tr<s> @ ptr)) (wait<ps> \<or> wait<qs>))(if (wait<ps> \<or> wait<qs>) then (if (time<ps> = time<qs>) then time<ps> else -1 ) else time<ps>)" and  ass2:"P (s, ps)" 
                                             and ass3: "ptr \<downharpoonright> P = (tr<ps> - tr<s>)" and ass4: "time<ps> = time<qs> \<or> (wait<ps> \<or> wait<qs>)" and ass5: "Q (s, qs)" and ass6: "ptr \<downharpoonright> Q = (tr<qs> - tr<s>)" 
                                             and ass7: "trace_restriction_paral ptr P Q = ptr"
        using a1 parallel_def
        by (smt (verit) old.prod.case)
      obtain s'' where ass8:"s'' = put\<^bsub>time\<^esub>(put\<^bsub>wait\<^esub> (put\<^bsub>tr\<^esub> (ps \<oplus>\<^sub>S qs on (\<Union>\<^sub>S ( BV_progs Q))) ( tr<s> @ ptr)) (wait<ps> \<or> wait<qs>))(if (wait<ps> \<or> wait<qs>) then (if (time<ps> = time<qs>) then time<ps> else -1 ) else time<qs>)"
        by blast
      have "(Q \<parallel>\<^sub>d P) (s, s'')"
        using ass2 ass3 ass4 ass5 ass6 ass7 ass8 parallel_def
        by (smt (verit) case_prodI2 prod.inject sup_commute
            trace_restriction_paral_def)
      moreover have "s' = s''"
      proof -
        have "time<s'> = time<s''>"
          using ass1 ass4 ass8 vwb_lens_mwb by auto
        moreover have "wait<s'> = wait<s''>"
          by (simp add: ass1 ass8 )
        moreover have "tr<s'> = tr<s''>"
          by(simp add: ass1 ass8  )
        ultimately have "s' \<approx>\<^sub>S s'' on \<Union>\<^sub>S observables"
          using observables_def scene_union_equiv observables_is_vars Scenes_extra.scene_equiv_get_eq
              insert_absorb mem_Vars_scene_space singleton_iff time_var_vwb_lens tr_vwb_lens
              wait_vwb_lens
          by (smt (verit) Sup_scene_closed insert_subset ns_alpha_vwb scene_space_equiv_union squnion_to_union
              st_vwb_lens)
        moreover have "s' \<approx>\<^sub>S s'' on -\<Union>\<^sub>S observables"
          proof -
            {
              fix v
              {
                assume a1: "v \<in> ((set Vars - observables) \<inter> BV_progs P)"
                have vp1:"v \<in> BV_progs P"
                  using a1 by auto
                have vp2:"v \<notin> observables"
                  using a1 by auto
                have "s' \<approx>\<^sub>S (qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P)))   on v"
                  using vp2 ass1 observables_def
                  by (metis Diff_iff Int_iff a1 idem_scene_Vars insertCI ns_alpha_vwb scene_equiv_refl
                      scene_space_put_preserved st_vwb_lens time_is_var time_var_vwb_lens tr_is_var tr_vwb_lens wait_is_var
                      wait_vwb_lens)
                moreover have "(qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P))) \<approx>\<^sub>S ps on v"
                  by (meson BV_is_vars mem_Vars_scene_space scene_equiv_def scene_override_overshadow_left
                      scene_union_equiv vp1)
                ultimately have vp3:"s' \<approx>\<^sub>S ps on v"
                  by (metis (no_types, opaque_lifting) scene_equiv_def
                      scene_override_overshadow_right) 
                have "s'' \<approx>\<^sub>S (ps \<oplus>\<^sub>S qs on (\<Union>\<^sub>S ( BV_progs Q))) on v"
                  using vp2 ass8 observables_def
                  by (metis Diff_iff Int_iff a1 idem_scene_Vars insertCI ns_alpha_vwb scene_equiv_refl
                      scene_space_put_preserved st_vwb_lens time_is_var time_var_vwb_lens tr_is_var tr_vwb_lens wait_is_var
                      wait_vwb_lens)
                moreover have "(ps \<oplus>\<^sub>S qs on (\<Union>\<^sub>S ( BV_progs Q)))\<approx>\<^sub>S ps on v"
                  proof -
                    have f1: "v \<in> set Vars"
                      using BV_is_vars vp1 by blast
                    have "\<not> v \<in> BV_progs Q"
                      using assms vp1 vp2 by blast
                    then show ?thesis
                      using f1 by (metis (no_types) BV_is_vars Diff_iff mem_Vars_scene_space scene_composition_complement scene_neg_decomp)
                  qed
                  ultimately have vp4:"s'' \<approx>\<^sub>S ps on v"
                    by (metis (no_types, opaque_lifting) scene_equiv_def
                      scene_override_overshadow_right) 
                  have "s' \<approx>\<^sub>S s'' on v"
                    using vp3 vp4
                    by (metis (lifting) ext scene_equiv_def scene_override_overshadow_right)
                }
                moreover 
                {
                assume a1: "v \<in> ((set Vars - observables) \<inter> BV_progs Q)"
                have vq1:"v \<in> BV_progs Q"
                  using a1 by auto
                have vq2:"v \<notin> observables"
                  using a1 by auto
                have "s' \<approx>\<^sub>S (qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P)))   on v"
                  using vq2 ass1 observables_def
                  by (metis Diff_iff Int_iff a1 idem_scene_Vars insertCI ns_alpha_vwb scene_equiv_refl
                      scene_space_put_preserved st_vwb_lens time_is_var time_var_vwb_lens tr_is_var tr_vwb_lens wait_is_var
                      wait_vwb_lens)
                moreover have "(qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P))) \<approx>\<^sub>S qs on v"
                proof -
                  have "v \<in> set Vars \<inter> - BV_progs P"
                    by (metis BV_is_vars ComplI Int_iff assms inf.absorb2 vq1 vq2)
                  then show ?thesis
                    by (metis (no_types) BV_is_vars diff_eq mem_Vars_scene_space scene_composition_complement scene_neg_decomp)
                qed
                ultimately have vq3:"s' \<approx>\<^sub>S qs on v"
                  by (metis (no_types, opaque_lifting) scene_equiv_def
                      scene_override_overshadow_right) 
                have "s'' \<approx>\<^sub>S (ps \<oplus>\<^sub>S qs on (\<Union>\<^sub>S ( BV_progs Q))) on v"
                  using vq2 ass8 observables_def
                  by (metis Diff_iff Int_iff a1 idem_scene_Vars insertCI ns_alpha_vwb scene_equiv_refl
                      scene_space_put_preserved st_vwb_lens time_is_var time_var_vwb_lens tr_is_var tr_vwb_lens wait_is_var
                      wait_vwb_lens)
                moreover have "(ps \<oplus>\<^sub>S qs on (\<Union>\<^sub>S ( BV_progs Q)))\<approx>\<^sub>S qs on v"
                  by (meson BV_is_vars mem_Vars_scene_space scene_equiv_def scene_override_overshadow_left
                      scene_union_equiv vq1)
                ultimately have vq4:"s'' \<approx>\<^sub>S qs on v"
                    by (metis (no_types, opaque_lifting) scene_equiv_def
                      scene_override_overshadow_right) 
                have "s' \<approx>\<^sub>S s'' on v"
                    using vq3 vq4
                    by (metis (lifting) ext scene_equiv_def scene_override_overshadow_right)
                }
                moreover 
                {
                assume a1: "v \<in> (set Vars - observables - BV_progs Q - BV_progs P) "
                have vn1:"v \<notin> BV_progs Q"
                  using a1 by auto
                have vn2:"v \<notin> BV_progs P"
                  using a1 by auto
                have vn3:"v \<notin> observables"
                  using a1 by auto
                have vn4:"s \<approx>\<^sub>S qs on v"
                  using vn1
                  by (metis DiffD1 a1 ass5 bound_eff_2 idem_scene_space scene_equiv_sym
                      scene_space_class.scene_space.Vars_scene_space)
                have vn5:"s \<approx>\<^sub>S ps on v"
                  using vn2
                  by (metis Diff_iff a1 ass2 bound_eff_2 idem_scene_Vars scene_equiv_sym)
                have "s' \<approx>\<^sub>S (qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P)))   on v"
                  using vn3 ass1 observables_def a1
                  by (metis Diff_iff  a1 idem_scene_Vars insertCI ns_alpha_vwb scene_equiv_refl
                      scene_space_put_preserved st_vwb_lens time_is_var time_var_vwb_lens tr_is_var tr_vwb_lens wait_is_var
                      wait_vwb_lens)
                moreover have "(qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S ( BV_progs P))) \<approx>\<^sub>S qs   on v"
                  using vn2
                  by (metis (mono_tags, opaque_lifting) BV_is_vars Diff_iff a1 mem_Vars_scene_space
                      scene_composition_complement scene_neg_decomp)
                ultimately have "s' \<approx>\<^sub>S qs on v"
                  by (metis (no_types, opaque_lifting) scene_equiv_def
                      scene_override_overshadow_right) 
                then have vn6:"s' \<approx>\<^sub>S s on v"
                  using vn4
                  by (metis (no_types, opaque_lifting) scene_equiv_def
                      scene_override_overshadow_right)  
                have "s'' \<approx>\<^sub>S (ps \<oplus>\<^sub>S qs on (\<Union>\<^sub>S ( BV_progs Q))) on v"
                  using vn3 ass8 observables_def a1
                  by (metis Diff_iff  a1 idem_scene_Vars insertCI ns_alpha_vwb scene_equiv_refl
                      scene_space_put_preserved st_vwb_lens time_is_var time_var_vwb_lens tr_is_var tr_vwb_lens wait_is_var
                      wait_vwb_lens)
                moreover have "(ps \<oplus>\<^sub>S qs on (\<Union>\<^sub>S ( BV_progs Q)))\<approx>\<^sub>S ps on v"
                  using vn2
                  by (metis (mono_tags, opaque_lifting) BV_is_vars Diff_iff a1 mem_Vars_scene_space
                      scene_composition_complement scene_neg_decomp)
                ultimately have "s'' \<approx>\<^sub>S ps on v"
                  by (metis (no_types, opaque_lifting) scene_equiv_def
                      scene_override_overshadow_right) 
                then have vn7:"s'' \<approx>\<^sub>S s on v"
                  using vn5
                  by (metis (no_types, opaque_lifting) scene_equiv_def
                      scene_override_overshadow_right) 
                have "s' \<approx>\<^sub>S s'' on v"
                  using vn6 vn7
                  by (metis (no_types, opaque_lifting) scene_equiv_def
                      scene_override_overshadow_right)
              }
              ultimately have "v \<in> (set Vars - observables) \<longrightarrow> s' \<approx>\<^sub>S s'' on v"
                by auto
            }
            then show ?thesis
              using scene_neg_decomp observables_is_vars
              by blast
          qed                  
        ultimately show ?thesis
          by (metis scene_comm scene_equiv_def scene_override_commute) 
      qed
      ultimately show ?thesis
        by meson
    qed     
  }
  then show ?thesis
    using pred_refine_iff
    by (metis (no_types, opaque_lifting) old.prod.exhaust)
qed


lemma paral_comm:
  assumes "BV_progs P \<inter> BV_progs Q \<subseteq> observables" 
  shows " (P \<parallel>\<^sub>d Q) = (Q \<parallel>\<^sub>d P) "
proof -
  have "P \<parallel>\<^sub>d Q \<sqsubseteq> Q \<parallel>\<^sub>d P"
    using assms(1) paral_comm_prev
    by (metis Int_commute)
  moreover have " Q \<parallel>\<^sub>d P \<sqsubseteq> P \<parallel>\<^sub>d Q"
    using assms(1) paral_comm_prev
    by (metis)
  ultimately show ?thesis
    by simp
qed

  
end