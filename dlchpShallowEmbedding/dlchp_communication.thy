theory dlchp_communication
  imports "dlchp_operators" "dlchp_health"
begin

lemma receive_trace_length:
  assumes "\<not> wait<s'>" "( c?\<^sub>dx) (s, s')"
  shows "length (tr<s'> - tr<s>) = 1"
proof -
  have "\<not> wait<s>"
    using assms waits_wf_receive waits_wf_def
    by (metis (mono_tags, lifting) prod.simps(2) skip_def)
  then have "\<exists> e \<in> range c. tr<s'> = tr<s>@[(e, time<s>)]"
    using assms 
    by(auto simp add: inp_dlchp_def)
  then show ?thesis
    by fastforce
qed


lemma send_trace_length:
  assumes "\<not> wait<s'>" "( c!\<^sub>d e) (s, s')"
  shows "length (tr<s'> - tr<s>) = 1"
proof -
  have "\<not> wait<s>"
    using assms waits_wf_send waits_wf_def
    by (metis (mono_tags, lifting) prod.simps(2) skip_def)
  then have " tr<s'> = tr<s>@[(c (e (st<s>)), time<s>)]"
    using assms 
    by(auto simp add: out_dlchp_def)
  then show ?thesis
    by fastforce
qed

lemma sublens_agree:
"\<lbrakk> vwb_lens x; idem_scene a; get\<^bsub>x\<^esub> s = get\<^bsub>x\<^esub> s' \<rbrakk> \<Longrightarrow> s \<approx>\<^sub>S s' on (a ;\<^sub>S x)"
  by (simp add: lens_defs, metis scene_comp.rep_eq scene_comp_idem scene_override.rep_eq scene_override_idem)

lemma get_agree_lens:
"\<lbrakk>vwb_lens x; vwb_lens y; get\<^bsub>x\<^esub> s = get\<^bsub>x\<^esub> s' ;  x \<approx>\<^sub>L y\<rbrakk> \<Longrightarrow>  get\<^bsub>y\<^esub> s = get\<^bsub>y\<^esub> s'"
  by (metis Scenes.scene_equiv_get_eq scene_space_lemmas(2))

lemma send_vars:
  assumes  "( c!\<^sub>d e) (s, s')"
  shows "s' \<approx>\<^sub>S s on -(\<Union>\<^sub>S {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>, \<lbrakk>wait\<rbrakk>\<^sub>\<sim>})"
proof -
  {
    fix x::"('c, 'b) dlCHP_alpha scene"
    assume is_var:"x \<in> (set Vars - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>, \<lbrakk>wait\<rbrakk>\<^sub>\<sim>})"
    consider (waiting) "wait<s>"
      | (not_waiting) "\<not>wait<s>"
      by auto

    then have "s' \<approx>\<^sub>S s on x"
    proof(cases)
      case waiting
      then show ?thesis
        using is_var assms 
        by(auto simp add: out_dlchp_def)
    next
      case not_waiting
      then have l1:"(st<s'>) = (st<s>)  \<and> ok<s'> = ok<s>"
        using assms
        by(auto simp add: out_dlchp_def)
      then show ?thesis
      proof (cases "x \<in> observables")
        case True
        hence "x = \<lbrakk>time\<rbrakk>\<^sub>\<sim>"
          using is_var observables_def by auto
        moreover have "time<s'> = time<s>"
          using l1
          by (metis get_subst_ext subst_ext_def)
        ultimately show ?thesis
          by (simp add: Scenes_extra.scene_equiv_get_eq)
      next
        case False
        have "st<s'> = st<s> \<and> ok<s'> = ok<s>"
            using l1 by auto
        then show ?thesis
          using False is_var
          apply(simp add: observables_def alpha_scene_space'_def alpha_scene_space_def Vars_des_vars_ext_def Vars_rea_vars_ext_def )
          apply(erule disjE)
           apply(simp add: scene_equiv_get_eq)
          apply(subgoal_tac " \<^bold>v\<^sub>R<s> =  \<^bold>v\<^sub>R<s'> ")
          apply(auto)
             apply (simp add: sublens_agree)
            apply (simp add: sublens_agree)
           apply(rule get_agree_lens[of st])
              apply(simp)
             apply(simp)
            apply(simp)
           apply(simp add:st_is_vR)
          apply(rule get_agree_lens[of st])
             apply(simp)
             apply(simp)
            apply(simp)
           apply(simp add:st_is_vR)
          done
      qed
    qed
  }
  then show ?thesis
    by (metis para_obs_def para_obs_is_vars scene_neg_decomp)
qed

lemma send_states_rel:
  assumes "( c!\<^sub>d e) (s, s')" "\<not> wait<s'>"
  shows "s' = put\<^bsub>tr\<^esub> s  (tr<s>@[(c (e (st<s>)), time<s>)])"
proof -
    have n_wait:"\<not> wait<s>"
      using assms
      by(auto simp add: out_dlchp_def)
    show ?thesis
    proof -

      {
        fix x::"('c, 'b) dlCHP_alpha scene"
        assume ax:"x \<in> set Vars - {\<lbrakk>tr\<rbrakk>\<^sub>\<sim>}"

        have "s' \<approx>\<^sub>S s on x"
        proof (cases "x \<in> observables")
          case True
          hence "x \<in>  {\<lbrakk>wait\<rbrakk>\<^sub>\<sim>, \<lbrakk>time\<rbrakk>\<^sub>\<sim>}"
            using ax observables_def
            by blast
          moreover have "s' \<approx>\<^sub>S s on \<lbrakk>wait\<rbrakk>\<^sub>\<sim>"
            using assms(2) n_wait
            by (simp add: Scenes_extra.scene_equiv_get_eq) 
          moreover have "s' \<approx>\<^sub>S s on \<lbrakk>time\<rbrakk>\<^sub>\<sim>"
            using assms(1) n_wait
            by (smt (verit) Scenes.scene_equiv_get_eq get_subst_ext ns_alpha_vwb out_dlchp_def prod.simps(2)
                st_vwb_lens subst_ext_def time_var_vwb_lens)
          ultimately  show ?thesis
            by auto 
        next
          case False
          have "st<s'> = st<s>"
            using assms(1) n_wait
            by (auto simp add: out_dlchp_def Scenes_extra.scene_equiv_get_eq) 
          then show ?thesis
            using False ax
            by (metis (no_types, lifting) Diff_iff assms(1) insert_iff observables_def para_obs_def para_obs_is_vars
                scene_neg_decomp send_vars)
        qed

      }
      then have "s' \<approx>\<^sub>S s on - \<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
        by (metis (no_types, lifting) insert_subset para_obs_def para_obs_is_vars scene_minus scene_minus2
            scene_neg_decomp)
      hence "s' \<approx>\<^sub>S put\<^bsub>tr\<^esub> s  (tr<s>@[(c(e (st<s>)), time<s>)]) on - \<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
        by (metis (no_types, lifting) Diff_insert Diff_subset idem_scene_uminus insert_absorb2 scene_equiv_sym
            scene_minus2 scene_union_put_preserved tr_is_var tr_vwb_lens vwb_impl_idem_scene)
      moreover have "s' \<approx>\<^sub>S put\<^bsub>tr\<^esub> s  (tr<s>@[(c(e (st<s>)), time<s>)]) on  \<lbrakk>tr\<rbrakk>\<^sub>\<sim>"
      proof -
        have "tr<s'> = (tr<s>@[(c(e (st<s>)), time<s>)])"
          using assms n_wait by (auto simp add: out_dlchp_def)
        thus ?thesis
          by (metis Scenes_extra.scene_equiv_get_eq \<open>s' \<approx>\<^sub>S s on - \<lbrakk>tr\<rbrakk>\<^sub>\<sim>\<close> lens_override_def lens_scene_override
              scene_equiv_def scene_override_commute tr_vwb_lens vwb_lens_def)
      qed
      ultimately show ?thesis
        by (metis scene_equiv_def scene_equiv_sym scene_override_commute tr_vwb_lens
            vwb_impl_idem_scene)
    qed
  qed

lemma send_tr_states:
  assumes "( c!\<^sub>d e) (s, s')" "\<not> wait<s'>"
  shows "s' =(trace_state_conc s (tr<s'>-tr<s>))"
  using assms send_states_rel trace_state_conc_def
  by (metis (no_types, lifting) diff_add_cancel_left' list_singleton_iff not_Cons_self2 not_le_minus
      plus_list_def send_trace_length tr_vwb_lens vwb_lens.put_eq zero_list_def)

lemma time_nbound_ndet:
  assumes "x \<bowtie> time_var" "(x :=\<^sub>d \<star>) (s, s')"
  shows "s \<approx>\<^sub>S s' on \<lbrakk>time\<rbrakk>\<^sub>\<sim>"
  proof (cases "wait<s>")
    case True
    then have "s = s'"
      using assms(2) waits_wf_def waits_wf_ndet_assign
      by (metis (mono_tags, lifting) old.prod.case skip_def)
    then show ?thesis
      by (simp add: time_is_var)
  next
    case False
    obtain e where det_assign:"(x :=\<^sub>d e) (s, s')"
      using assms(2) ndet_assign_dlchp_def
      by (metis SUP1_E)
    
    from det_assign False
    consider (wait) "(s' = (put\<^bsub>wait\<^esub> s (True)))" |
             (nwait) "(st<s'> = put\<^bsub>x\<^esub> (st<s>) ((e)\<^sub>e (st<s>)) \<and> tr<s'> = tr<s> \<and> wait<s'> = wait<s> \<and> ok<s'> = ok<s>)"
          using assign_dlchp_def
          by (smt (verit, best) case_prodD)

        then show ?thesis
        proof (cases)
          case wait
          have "wait \<bowtie> time"
            using wait_is_var time_is_var
            using ns_alpha_indep_3 rea_vars.indeps(3) srea_vars.indeps(8) by blast
          then show ?thesis
            by (simp add: Scenes_extra.scene_equiv_get_eq wait) 


        next
          case nwait

          have "st<s'> = put\<^bsub>x\<^esub> (st<s>) ((e)\<^sub>e (st<s>))"
            using nwait by blast          

          then show ?thesis
            using assms(1)
            by (metis (no_types, lifting) Scenes.scene_equiv_get_eq get_subst_ext lens_indep_def ns_alpha_vwb
                st_vwb_lens subst_ext_def time_var_vwb_lens) 
        qed

qed


lemma send_eq_ndet_rec:
  assumes "x \<bowtie> time_var"  "vwb_lens x"
  shows "(c?\<^sub>dx) (s,s')  \<longleftrightarrow> (\<exists> s0. (x :=\<^sub>d \<star>) (s, s0) \<and> (c!\<^sub>d ($x)\<^sub>e ) (s0, s'))"
proof (cases "wait<s>")
  case True
  {
    assume lhs:"(c?\<^sub>dx) (s,s')"
    have id: "s = s'"
      using True lhs
      by (metis (mono_tags, lifting) prod.simps(2) skip_def waits_wf_def waits_wf_receive)
    have rhs: "(\<exists> s0. (x :=\<^sub>d \<star>) (s, s0) \<and> (c!\<^sub>d ($x)\<^sub>e ) (s0, s'))"
    proof -
      have "(x :=\<^sub>d \<star>) (s, s)"
        using True 
        by (metis (no_types, lifting) lhs local.id waits_wf_def waits_wf_ndet_assign
            waits_wf_receive) 
      moreover have "(c!\<^sub>d ($x)\<^sub>e ) (s, s')"
        using True
        by (metis (no_types, lifting) lhs local.id waits_wf_def waits_wf_send
            waits_wf_receive)
      ultimately show ?thesis
        by blast
    qed
    }
    moreover {
      assume rhs:"(\<exists> s0. (x :=\<^sub>d \<star>) (s, s0) \<and> (c!\<^sub>d ($x)\<^sub>e ) (s0, s'))"
      have "\<forall> s0. (x :=\<^sub>d \<star>) (s, s0) \<longrightarrow> s0 = s"
        using True waits_wf_def  waits_wf_ndet_assign
        by (metis (mono_tags, lifting) prod.simps(2) skip_def)

      hence "\<forall> s'. (\<exists> s0. (x :=\<^sub>d \<star>) (s, s0) \<and> (c!\<^sub>d ($x)\<^sub>e ) (s0, s')) \<longrightarrow> s = s'"
        by (metis (mono_tags, lifting) True case_prodD skip_def waits_wf_def waits_wf_send)

      hence "(c?\<^sub>dx) (s,s')"
        by (metis True \<open>\<forall>s0. x :=\<^sub>d \<star> (s, s0) \<longrightarrow> s0 = s\<close> rhs waits_wf_def waits_wf_ndet_assign
            waits_wf_receive)
    }

    ultimately show ?thesis 
      by blast

  
next
  case False
  { 
    assume lhs:"(c?\<^sub>dx) (s,s')"
    obtain e where  comm:"( ((tr<s'> \<le> tr<s>@[(c e, time<s>)] \<and> tr<s> \<le> tr<s'> \<and> wait<s'>) \<or> (tr<s'> = tr<s>@[(c e, time<s>)] \<and> \<not>wait<s'>) ) \<and> st<s'> = put\<^bsub>x\<^esub> (st<s>) e \<and> ok<s'> = ok<s>  )"
      using lhs False 
      apply(simp add:  inp_dlchp_def)
      by(auto)

    have state:"st<s'> = put\<^bsub>x\<^esub> (st<s>) e \<and> ok<s'> = ok<s>"
      using comm by blast

    hence esp:"e =  (get\<^bsub>x\<^esub> (get\<^bsub>st\<^esub> s'))"
    proof -
      have "st<s'> = put\<^bsub>x\<^esub> (st<s>) e"
        using state by blast

      hence  "(get\<^bsub>x\<^esub> (get\<^bsub>st\<^esub> s')) = e"
        using assms(2)
        by simp

      thus  ?thesis
        by presburger
    qed
    
    from comm
    consider  (wait) "(tr<s'> \<le> tr<s>@[(c e, time<s>)] \<and> tr<s> \<le> tr<s'> \<and> wait<s'>)" |
               (nwait) "(tr<s'> = tr<s>@[(c e, time<s>)] \<and> \<not>wait<s'>)"
      by blast

    then have rhs:"(\<exists> s0. (x :=\<^sub>d \<star>) (s, s0) \<and> (c!\<^sub>d ($x)\<^sub>e ) (s0, s'))"
    proof (cases)
      case wait
      have ext_wit:"\<exists> s0'. (x :=\<^sub>d e) (s, s0') \<and> \<not> wait<s0'>"
        using False 
        apply( simp add: assign_dlchp_def)
        apply (rule exI[where x = "put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) e)"])
        apply(simp)
        done

        

      obtain s0' where det_ass:"(x :=\<^sub>d e) (s, s0')" and nwaits0:"\<not> wait<s0'>"
        using ext_wit by blast

      have ndet_ass:"(x :=\<^sub>d \<star>) (s, s0')"
        using det_ass 
        apply(simp add:ndet_assign_dlchp_def)
        by (auto)

      have okays0:"ok<s'> = ok<s0'>"
        using state det_ass nwaits0
        by (smt (z3) assign_dlchp_def case_prodD vwb_lens.put_eq wait_vwb_lens)


      have xs0:"st<s0'> = put\<^bsub>x\<^esub> (st<s>) e"
        using det_ass False nwaits0 
        unfolding assign_dlchp_def
        by auto 


      hence states0: "st<s0'> = st<s'>"
        using state by auto

      have times0:"time<s0'> = time<s>"
        using assms(1) time_nbound_ndet ndet_ass
        by (metis Scenes_extra.scene_equiv_get_eq ns_alpha_vwb st_vwb_lens time_var_vwb_lens)

      have "tr<s> = tr<s0'>"
        using det_ass assign_dlchp_def False
        by (smt (verit, del_insts) case_prodD lens_indep.lens_put_irr2 rea_vars.indeps(1))

      hence trs0:"(tr<s'> \<le> tr<s0'>@[(c e, time<s0'>)] \<and> tr<s0'> \<le> tr<s'> \<and> wait<s'>)" 
        using times0 wait by auto

      have "(c!\<^sub>d ($x)\<^sub>e ) (s0', s')"
        using nwaits0
        unfolding out_dlchp_def 
        apply simp
        using trs0 states0 okays0
        apply simp
        using esp
        by auto

      then show ?thesis
        using ndet_ass by blast
    next
      case nwait
      have ext_wit:"\<exists> s0'. (x :=\<^sub>d e) (s, s0') \<and> \<not> wait<s0'>"
        using False 
        apply( simp add: assign_dlchp_def)
        apply (rule exI[where x = "put\<^bsub>st\<^esub> s (put\<^bsub>x\<^esub> (st<s>) e)"])
        apply(simp)
        done

        

      obtain s0' where det_ass:"(x :=\<^sub>d e) (s, s0')" and nwaits0:"\<not> wait<s0'>"
        using ext_wit by blast

      have ndet_ass:"(x :=\<^sub>d \<star>) (s, s0')"
        using det_ass 
        apply(simp add:ndet_assign_dlchp_def)
        by (auto)

      have okays0:"ok<s'> = ok<s0'>"
        using state det_ass nwaits0
        by (smt (z3) assign_dlchp_def case_prodD vwb_lens.put_eq wait_vwb_lens)


      have xs0:"st<s0'> = put\<^bsub>x\<^esub> (st<s>) e"
        using det_ass False nwaits0 
        unfolding assign_dlchp_def
        by auto 


      hence states0: "st<s0'> = st<s'>"
        using state by auto

      have times0:"time<s0'> = time<s>"
        using assms(1) time_nbound_ndet ndet_ass
        by (metis Scenes_extra.scene_equiv_get_eq ns_alpha_vwb st_vwb_lens time_var_vwb_lens)

      have "tr<s> = tr<s0'>"
        using det_ass assign_dlchp_def False
        by (smt (verit, del_insts) case_prodD lens_indep.lens_put_irr2 rea_vars.indeps(1))

      hence trs0:"(tr<s'> = tr<s0'>@[(c e, time<s0'>)] \<and> \<not>wait<s'>)"
        using times0 nwait by auto

      have "(c!\<^sub>d ($x)\<^sub>e ) (s0', s')"
        using nwaits0
        unfolding out_dlchp_def 
        apply simp
        using trs0 states0 okays0
        apply simp
        using esp
        by auto

      then show ?thesis
        using ndet_ass by blast
    qed
  }
  moreover  {
    assume rhs:"(\<exists> s0. (x :=\<^sub>d \<star>) (s, s0) \<and> (c!\<^sub>d ($x)\<^sub>e ) (s0, s'))"
    obtain s0 where ndet_ass:"(x :=\<^sub>d \<star>) (s, s0)" and  send:"(c!\<^sub>d ($x)\<^sub>e ) (s0, s')"
      using rhs by blast

    note nwaits_start = False

    have lhs:"(c?\<^sub>dx) (s,s')"
    proof (cases "wait<s0>")
      case True

      hence "s0 =  (put\<^bsub>wait\<^esub> s (True))"
        using True nwaits_start ndet_ass
        unfolding ndet_assign_dlchp_def assign_dlchp_def
        by auto

      moreover have "s' = s0"
        using send waits_wf_send waits_wf_def
        by (simp add: True out_dlchp_def)

      ultimately have s_rel:"s' = (put\<^bsub>wait\<^esub> s (True))"
        by simp

      hence  tr_rel:"\<forall> t. (tr<s'> \<le> (tr<s>@t) \<and> tr<s> \<le> tr<s'> \<and> wait<s'>)"
        by simp


      then show ?thesis 
        using s_rel
        unfolding inp_dlchp_def
        using nwaits_start
        apply auto
        by (metis assms(2) vwb_lens.put_eq)

    next
      case False
      hence value_req:"\<exists> v.(st<s0> = put\<^bsub>x\<^esub> (st<s>) v)"
        using ndet_ass nwaits_start
        unfolding ndet_assign_dlchp_def assign_dlchp_def
        apply simp
        by auto

      obtain v where val:"(st<s0> = put\<^bsub>x\<^esub> (st<s>) v)"
        using value_req by auto

      have xval: "get\<^bsub>x\<^esub> (st<s0>) = v"
        using val assms(2)
        by simp

      have trace:"tr<s> = tr<s0>"
        using ndet_ass  nwaits_start
        unfolding ndet_assign_dlchp_def assign_dlchp_def
        apply simp
        by auto

      have time_eq:"time<s> = time<s0>"
        using assms(1,2) ndet_ass time_nbound_ndet
        by (metis Scenes_extra.scene_equiv_get_eq ns_alpha_vwb st_vwb_lens time_var_vwb_lens)

      have ok_prev:"ok<s> = ok<s0> "
        using ndet_ass nwaits_start
        unfolding ndet_assign_dlchp_def assign_dlchp_def
        apply simp
        by auto


      have state:"(st<s'>) = (st<s0>)"
        using send False
        unfolding out_dlchp_def
        by simp
 
      have okay: "ok<s'> = ok<s0> "
        using send False
        unfolding out_dlchp_def
        by simp

      have send_cases:
        "(tr<s'> \<le> tr<s0> @ [(c v, time<s0>)] \<and>  tr<s0> \<le> tr<s'> \<and>  wait<s'>)
         \<or>
         (tr<s'> = tr<s0> @ [(c v, time<s0>)] \<and>   \<not> wait<s'>)"
        using send xval False
        unfolding out_dlchp_def
        by auto

      have cfun_app:"\<exists>e. c (get\<^bsub>x\<^esub> (get\<^bsub>st\<^esub> s0)) = c e"
        using xval
        by auto

      from send
      consider (fwait)  "(tr<s'> \<le> tr<s0>@[(c v, time<s0>)] \<and> tr<s0> \<le> tr<s'> \<and> wait<s'>)" | 
          (fnwait)  "(tr<s'> = tr<s0>@[(c v, time<s0>)] \<and> \<not>wait<s'> )"
        using send_cases
        by blast

      then show ?thesis 
      proof(cases)
        case fwait
        then show ?thesis
          using  okay state trace nwaits_start False time_eq val ok_prev
          unfolding inp_dlchp_def
          apply simp
          apply (rule exI[where x = v])
          by auto 
          
      next
        case fnwait
        then show ?thesis 
          using  okay state trace nwaits_start False time_eq val ok_prev
          unfolding inp_dlchp_def
          apply simp
          apply (rule exI[where x = v])
          by auto 
      qed
    qed
  }
  ultimately show ?thesis
    by blast
qed



end