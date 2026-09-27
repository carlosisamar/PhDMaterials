theory dlchp_loop
  imports "dlchp_operators" "dlchp_health" "dlchp_seq_comp"
begin

lemma bv_loop_prev:
  assumes "total P"
  shows "BV_progs P = BV_progs (P ;;\<^sub>d (?(True)\<^sub>e))" 
  apply(simp add: seq_comp_dlchp_def BV_progs_def test_dlchp_def)
  apply(auto)
  by (metis (no_types, opaque_lifting) Scenes_extra.scene_equiv_get_eq assms idem_scene_Vars
      scene_equiv_sym scene_space_put_preserved total_def wait_is_var wait_vwb_lens)


lemma bv_loop_prev2:
  "BV_progs ?(True)\<^sub>e = {\<lbrakk>wait\<rbrakk>\<^sub>\<sim> }"
  apply(simp add: BV_progs_def test_dlchp_def)
  apply(auto)
  apply (meson idem_scene_Vars scene_equiv_refl scene_equiv_sym scene_space_put_preserved
      wait_is_var wait_vwb_lens)
  using wait_is_var apply blast
  by (metis Scenes_extra.scene_equiv_get_eq vwb_lens_def wait_vwb_lens wb_lens.axioms(1)
      weak_lens_def)

lemma bv_loop_prev3:
  assumes "total P"
  shows "\<lbrakk>wait\<rbrakk>\<^sub>\<sim> \<in> BV_progs P"
  using assms
  apply(simp add: BV_progs_def total_def)
  by (metis Scenes_extra.scene_equiv_get_eq vwb_lens.axioms(1) wait_is_var wait_vwb_lens
      wb_lens.axioms(1) weak_lens.put_get)

lemma bv_loop_prev4:
  assumes "(P ^\<^sup>d n) (s, s')"  "\<not> (s \<approx>\<^sub>S s' on x)" "total P" "x \<in> set Vars"
  shows "x \<in> BV_progs P"
  using assms
proof (induction n arbitrary: s s')
  case 0
  have "x \<in> BV_progs ?(True)\<^sub>e"
    using 0 upower_dlchp.simps(1) BV_progs_def
    by auto
  then show ?case
    using bv_loop_prev2 bv_loop_prev3 0(3)
    by (metis singleton_iff)
next
  case (Suc n)

  have l1:"(P(s,s') \<and> wait<s'>) \<or> (\<exists> s\<^sub>0. P(s,s\<^sub>0) \<and> \<not>wait<s\<^sub>0> \<and> (P ^\<^sup>d n) (s\<^sub>0, s'))"
    using Suc.prems(1) seq_comp_dlchp_def upower_dlchp.simps(2)
    by (smt (verit) curryI curry_case_prod)
  {
    assume a1:"P(s,s') \<and> wait<s'>"
    have "x \<in> BV_progs P"
      using a1 BV_progs_def Suc(3,5)
      by blast
  }
  moreover {
    assume a1: " (\<exists> s\<^sub>0. P(s,s\<^sub>0) \<and> \<not>wait<s\<^sub>0> \<and> (P ^\<^sup>d n) (s\<^sub>0, s'))"
    obtain s0 where s1:"P(s,s0)" and s2:"(P ^\<^sup>d n) (s0, s')"
      using a1 by auto
    have "x \<in> BV_progs P"
    proof (cases "s \<approx>\<^sub>S s0 on x")
        case False
        then show ?thesis
          using s1 BV_progs_def Suc(3,5)
          by blast
      next
        case True
        have rest_changes: "\<not> (s0 \<approx>\<^sub>S s' on x)"
        proof
          assume t0: "s0 \<approx>\<^sub>S s' on x"
          have "s \<approx>\<^sub>S s' on x"
            using True t0
            by (metis (no_types, opaque_lifting) scene_equiv_def scene_override_overshadow_right)
          with Suc.prems(2) show False
            by contradiction
        qed   
        then show ?thesis
          using Suc.IH s2 assms
          by blast
      qed
    }
    ultimately show ?case
      using l1
      by blast
qed

lemma bv_loop:
  assumes "total P"
  shows "BV_progs P = BV_progs (P\<^sup>d)" 
proof -
  {
    fix x
    assume a1:"x \<in> BV_progs P"
    have "x \<in> BV_progs (P ^\<^sup>d 1)"
      using bv_loop_prev
      using a1 assms by auto
    then have "x \<in>  BV_progs (P\<^sup>d)"
      using loop_dlchp_def BV_progs_def
      by (smt (verit) SUP1_I UNIV_I mem_Collect_eq)
      
  }
  moreover {
    fix x
    assume a1:"x \<in> BV_progs (P\<^sup>d)"
    have "x \<in> BV_progs P"
      using loop_dlchp_def bv_loop_prev4 assms a1 BV_progs_def
      by (smt (verit) SUP1_E mem_Collect_eq)  
  }

  ultimately show ?thesis
    by auto
qed

lemma repetition_seq_decomp:
  shows "P\<^sup>d = ((P ^\<^sup>d 0) \<Union>\<^sub>d (P ;;\<^sub>d (P\<^sup>d)))"
proof -
  {
    fix s s'
    assume a1:"P\<^sup>d (s,s')"
    obtain n where n0:"(P ^\<^sup>d n) (s,s')"
      using a1 loop_dlchp_def
      by (metis SUP1_E)
    {
      assume n1:"n = 0"
      have "(?(True)\<^sub>e) (s,s')"
        using n1 n0 upower_dlchp.simps(1)
        by auto
      then have "((?(True)\<^sub>e) \<Union>\<^sub>d (P ;;\<^sub>d (P\<^sup>d))) (s,s')"
        using choice_dlchp_def
        by (metis (no_types, lifting) internal_case_prod_conv internal_case_prod_def)
    }
    moreover {
      assume n1:"n \<noteq> 0"
      have "(P ;;\<^sub>d (P ^\<^sup>d (n-1))) (s,s')"
        using n1 n0 upower_dlchp.simps(2)
        by (metis Suc_pred' not_gr0)
      then have "(P ;;\<^sub>d (P\<^sup>d)) (s,s')"
        using loop_dlchp_def
        by (smt (verit) SUP1_I UNIV_I curryD curryI curry_case_prod seq_comp_dlchp_def)
      then have "((?(True)\<^sub>e) \<Union>\<^sub>d (P ;;\<^sub>d (P\<^sup>d))) (s,s')"
        using choice_dlchp_def
        by (metis (no_types, lifting) internal_case_prod_conv internal_case_prod_def)
    }
    ultimately have "((?(True)\<^sub>e) \<Union>\<^sub>d (P ;;\<^sub>d (P\<^sup>d))) (s,s')"
      by auto
  }
  then have l1:"((?(True)\<^sub>e) \<Union>\<^sub>d (P ;;\<^sub>d (P\<^sup>d))) \<sqsubseteq>  P\<^sup>d "
    by (simp add: pred_refine_iff)
  {
    fix s s'
    assume a1:"((?(True)\<^sub>e) \<Union>\<^sub>d (P ;;\<^sub>d (P\<^sup>d))) (s,s')"
    {
      assume u1: "(?(True)\<^sub>e) (s,s')"
      have "P\<^sup>d (s,s')"
        using u1 loop_dlchp_def upower_dlchp.simps(1)
        by (metis SUP1_I UNIV_I)
    }
    moreover {
      assume u1: "(P ;;\<^sub>d (P\<^sup>d)) (s,s')"
      obtain n where n0:"(P ;;\<^sub>d (P ^\<^sup>d n)) (s,s')"
        using loop_dlchp_def
        by (smt (verit) SUP1_E curryD curryI curry_case_prod seq_comp_dlchp_def u1)
      have "(P ^\<^sup>d (n + 1)) (s,s')"
        using n0 upower_dlchp.simps(2)
        by auto
      then have "P\<^sup>d (s,s')"
        using loop_dlchp_def
        by (metis SUP1_I UNIV_I)
    }
    ultimately have "P\<^sup>d (s,s')"
      using a1 choice_dlchp_def
      by (metis (no_types, lifting) curryI curry_case_prod)
  }
  then have l2:"P\<^sup>d \<sqsubseteq> ((?(True)\<^sub>e) \<Union>\<^sub>d (P ;;\<^sub>d (P\<^sup>d)))"
    by (simp add: pred_refine_iff)
  show ?thesis
    using l1 l2 by simp
qed

    
lemma comm_well_formed_loop:
  assumes "comm_well_formed A P" "total P"
  shows "comm_well_formed A (P\<^sup>d)"
proof -
  have "BV_progs P = BV_progs (P\<^sup>d)"
    using bv_loop assms(2) by auto
  then show ?thesis 
    using assms(1) comm_well_formed_def
    by metis
qed

lemma upower_seq_into_loop_nwait:
  assumes  "\<not> wait<s'>"  "((P ^\<^sup>d n) ;;\<^sub>d P) (s, s')"
  shows "(P\<^sup>d) (s, s')"
  using assms
proof (induction n arbitrary: s)
  case 0

    obtain s0 where s1: "((?(True)\<^sub>e) (s, s0))"
    and s3: "\<not> wait<s0>" and s2: "P (s0, s')"
      using 0  by (auto simp add: seq_comp_dlchp_def)

  have "s0 = s"
    using s3 s1
    by(auto simp add: test_dlchp_def)

  then have "(P ^\<^sup>d Suc 0) (s, s')"
    using s2 
    by (auto simp add: seq_comp_dlchp_def test_dlchp_def)

  then show ?case
    using loop_dlchp_def
    by (metis Sup1_I range_eqI)
next
  case (Suc n)
  obtain s0 where s1: "(P ^\<^sup>d Suc n) (s, s0)"
    and s2: "\<not> wait<s0>" and s3: "P (s0, s')"
    using Suc
    by (auto simp add: seq_comp_dlchp_def)

    obtain s1 where
      p_first: "P (s, s1)"
    and nw1: "\<not> wait<s1>"
    and pow_rest: "(P ^\<^sup>d n) (s1, s0)"
      using s1 s2 s3
    by (auto simp add: seq_comp_dlchp_def)

  have tail: "((P ^\<^sup>d n) ;;\<^sub>d P) (s1, s')"
    using pow_rest s2 s3
    by (auto simp add: seq_comp_dlchp_def)

  have loop_tail: "(P\<^sup>d) (s1, s')"
    using Suc.IH[OF Suc.prems(1) tail] .

  then obtain k where pow_tail: "(P ^\<^sup>d k) (s1, s')"
    using loop_dlchp_def
    by (metis SUP1_E)

  have "(P ^\<^sup>d Suc k) (s, s')"
    using p_first nw1 pow_tail
    by (auto simp add: seq_comp_dlchp_def)

  then show ?case
  using loop_dlchp_def
    by (metis Sup1_I range_eqI)
qed

lemma upower_pos_into_loop_seq_nwait:
  assumes  "\<not> wait<s>" "\<not> wait<s'>" "(P ^\<^sup>d Suc n) (s, s')"
  shows "((P\<^sup>d) ;;\<^sub>d P) (s, s')"
  using assms
proof (induction n arbitrary: s)
  case 0

  from 0 obtain s0 where
      p0: "P (s, s0)"
    and nw0: "\<not> wait<s0>"
    and test0: "((?(True)\<^sub>e) (s0, s'))"
    by (auto simp add: seq_comp_dlchp_def)

  from test0 0 have "s0 = s'"
    by(auto simp add: test_dlchp_def)

  have loop_refl: "(P\<^sup>d) (s, s)"
     using loop_dlchp_def upower_dlchp.simps(1) test_dlchp_def
     by (smt (verit, ccfv_SIG) SEXP_def SUP1_I UNIV_I curryE curry_case_prod)

  show ?case
    using loop_refl 0 p0 \<open>s0 = s'\<close>
    by (auto simp add: seq_comp_dlchp_def)
next
  case (Suc n)

  from Suc.prems obtain s0 where
      p0: "P (s, s0)"
    and nw0: "\<not> wait<s0>"
    and rest: "(P ^\<^sup>d Suc n) (s0, s')"
    by (auto simp add: seq_comp_dlchp_def)

  have tail: "((P\<^sup>d) ;;\<^sub>d P) (s0, s')"
    using Suc.IH[OF nw0 Suc.prems(2) rest] .

  from tail Suc.prems obtain s1 where
      loop_mid: "(P\<^sup>d) (s0, s1)"
    and nw1: "\<not> wait<s1>"
    and p_last: "P (s1, s')"
    by (auto simp add: seq_comp_dlchp_def)

  from loop_mid obtain k where pow_mid: "(P ^\<^sup>d k) (s0, s1)"
    using loop_dlchp_def
    by (metis SUP1_E)

  have "(P ^\<^sup>d Suc k) (s, s1)"
    using p0 nw0 pow_mid
    by (auto simp add: seq_comp_dlchp_def)

  then have loop_left: "(P\<^sup>d) (s, s1)"
    using loop_dlchp_def
    by (metis SUP1_I UNIV_I)

  show ?case
    using loop_left nw1 p_last
    by (auto simp add: seq_comp_dlchp_def)
qed

lemma power_comm_nwait:
  assumes  "\<not> wait<s>" "\<not> wait<s'>"
  shows "(((P ^\<^sup>d n) ;;\<^sub>d P) (s, s')) =
         ((P ;;\<^sub>d (P ^\<^sup>d n)) (s, s'))"
  using assms
proof (induction n arbitrary: s s')
  case 0

  show ?case
  proof
    assume lhs: "((P ^\<^sup>d 0) ;;\<^sub>d P) (s, s')"
    then show "(P ;;\<^sub>d (P ^\<^sup>d 0)) (s, s')"
      using 0
      by (auto simp add: seq_comp_dlchp_def test_dlchp_def)
  next
    assume rhs: "(P ;;\<^sub>d (P ^\<^sup>d 0)) (s, s')"
    then show "((P ^\<^sup>d 0) ;;\<^sub>d P) (s, s')"
      using 0
      by (auto simp add: seq_comp_dlchp_def test_dlchp_def)
  qed

next
  case (Suc n)

  show ?case
  proof
    assume lhs: "((P ^\<^sup>d Suc n) ;;\<^sub>d P) (s, s')"

    from lhs Suc.prems obtain s0 where
        pow_s0: "(P ^\<^sup>d Suc n) (s, s0)"
      and nw0: "\<not> wait<s0>"
      and p_last: "P (s0, s')"
      by (auto simp add: seq_comp_dlchp_def)

    from pow_s0 nw0 obtain s1 where
        p_first: "P (s, s1)"
      and nw1: "\<not> wait<s1>"
      and pow_rest: "(P ^\<^sup>d n) (s1, s0)"
      by (auto simp add: seq_comp_dlchp_def)

    have tail_lhs: "((P ^\<^sup>d n) ;;\<^sub>d P) (s1, s')"
      using pow_rest nw0 p_last
      by (auto simp add: seq_comp_dlchp_def)

    have tail_rhs: "(P ;;\<^sub>d (P ^\<^sup>d n)) (s1, s')"
      using Suc.IH[OF nw1 Suc.prems(2)] tail_lhs
      by simp

    show "(P ;;\<^sub>d (P ^\<^sup>d Suc n)) (s, s')"
      using p_first nw1 tail_rhs
      by (auto simp add: seq_comp_dlchp_def)

  next
    assume rhs: "(P ;;\<^sub>d (P ^\<^sup>d Suc n)) (s, s')"

    from rhs Suc.prems obtain s0 where
        p_first: "P (s, s0)"
      and nw0: "\<not> wait<s0>"
      and pow_suc: "(P ^\<^sup>d Suc n) (s0, s')"
      by (auto simp add: seq_comp_dlchp_def)

    have tail_rhs: "(P ;;\<^sub>d (P ^\<^sup>d n)) (s0, s')"
      using pow_suc
      by simp

    have tail_lhs: "((P ^\<^sup>d n) ;;\<^sub>d P) (s0, s')"
      using Suc.IH[OF nw0 Suc.prems(2)] tail_rhs
      by simp

    from tail_lhs Suc.prems obtain u where
        pow_u: "(P ^\<^sup>d n) (s0, u)"
      and nwu: "\<not> wait<u>"
      and p_last: "P (u, s')"
      by (auto simp add: seq_comp_dlchp_def)

    have pow_s_u: "(P ^\<^sup>d Suc n) (s, u)"
      using p_first nw0 pow_u
      by (auto simp add: seq_comp_dlchp_def)

    show "((P ^\<^sup>d Suc n) ;;\<^sub>d P) (s, s')"
      using pow_s_u nwu p_last
      by (auto simp add: seq_comp_dlchp_def)
  qed
qed

lemma loop_comm_nwait:
  assumes "\<not> wait<s>" "\<not> wait<s'>"
    shows "((P\<^sup>d) ;;\<^sub>d P) (s, s') = (P ;;\<^sub>d (P\<^sup>d)) (s, s')"
proof 
  assume lhs: "((P\<^sup>d) ;;\<^sub>d P) (s, s')"
  have ext_n:"\<exists> n.(((P ^\<^sup>d n) ;;\<^sub>d P)) (s, s')"
    using lhs loop_dlchp_def
    by (smt (verit) SUP1_E curryD curryI curry_case_prod seq_comp_dlchp_def)

  obtain n where n1:"(((P ^\<^sup>d n) ;;\<^sub>d P)) (s, s')"
    using ext_n by auto

  have n_comm:"((P ;;\<^sub>d (P ^\<^sup>d n))) (s, s')"
    using power_comm_nwait n1 assms by metis
  
  thus "(P ;;\<^sub>d (P\<^sup>d)) (s, s')"
    using loop_dlchp_def
    by (smt (verit) SUP1_I UNIV_I curryD curryI curry_case_prod seq_comp_dlchp_def)
next
assume rhs: "(P ;;\<^sub>d (P\<^sup>d)) (s, s')"
  have ext_n:"\<exists> n.((P ;;\<^sub>d (P ^\<^sup>d n))) (s, s')"
    using rhs loop_dlchp_def
    by (smt (verit) SUP1_E curryD curryI curry_case_prod seq_comp_dlchp_def)

  obtain n where n1:"((P ;;\<^sub>d (P ^\<^sup>d n))) (s, s')"
    using ext_n by auto

  have n_comm:"(((P ^\<^sup>d n) ;;\<^sub>d P)) (s, s')"
    using power_comm_nwait n1 assms by metis
  
  thus "((P\<^sup>d) ;;\<^sub>d P) (s, s')"
    using loop_dlchp_def
    by (smt (verit) SUP1_I UNIV_I curryD curryI curry_case_prod seq_comp_dlchp_def)
qed

    

lemma loop_comm_ac_prev:
  assumes "(P ;;\<^sub>d (P\<^sup>d)) (s,s')" "waits_wf P" "total P"
  shows "\<exists> s''. ((P\<^sup>d) ;;\<^sub>d P) (s, s'') \<and> tr<s'> = tr<s''>"
proof(cases "wait<s>")
  case True
  note waitstart = True
  have  "waits_wf (P ;;\<^sub>d (P\<^sup>d))"
    using assms(2) waits_wf_loop waits_wf_seq_comp
    by blast
  then have s1:"s' = s"
    using waits_wf_def assms(1) waitstart skip_def
    by (metis (mono_tags, lifting) case_prodD)
  have "waits_wf ((P\<^sup>d) ;;\<^sub>d P)"
    using assms(2) waits_wf_loop waits_wf_seq_comp
    by blast
  then have "((P\<^sup>d) ;;\<^sub>d P) (s, s)"
    using waits_wf_def  waitstart skip_def assms(3) total_def
    by (smt (verit, del_insts) old.prod.case waits_wf_test)
  then have "((P\<^sup>d) ;;\<^sub>d P) (s, s')"
    using s1 by auto
  then show ?thesis
    by blast 
next
  case False
  note nwaits_start = False
  obtain n where n1:"(P ;;\<^sub>d (P ^\<^sup>d n)) (s,s')"
    using assms loop_dlchp_def
    by (smt (verit) SUP1_E curryD curryI curry_case_prod seq_comp_dlchp_def)
  then have p0:"(P  ^\<^sup>d (Suc n)) (s,s')"
    using n1 upower_dlchp.simps(2)
    by auto
  then have p1:"(P\<^sup>d) (s,s')"
    using loop_dlchp_def
    by (metis SUP1_I UNIV_I)
  show ?thesis 
  proof (cases "wait<s'>")
    case True
    note waits_end = True
    then have "((P\<^sup>d) ;;\<^sub>d P) (s, s')"
      using p1 seq_comp_dlchp_def waits_end
      by (metis (no_types, lifting) curryD curry_case_prod)
    then show ?thesis
      by blast
  next
    case False
    note nwaits_end = False
    then show ?thesis
      using nwaits_end nwaits_start assms(1) loop_comm_nwait
      by blast
  qed
qed

lemma seq_prepend_dlchp:
  assumes "P (s, s0)" "\<not> wait<s0>" "(Q ;;\<^sub>d R) (s0, u)"
  shows "((P ;;\<^sub>d Q) ;;\<^sub>d R) (s, u)"
  using assms
  by (auto simp add: seq_comp_dlchp_def)

lemma loop_comm_ac_prev_power_nwait:
  assumes "\<not> wait<s>" "(P ;;\<^sub>d (P ^\<^sup>d n)) (s, s')"
  shows "\<exists>s''. ((P ^\<^sup>d n) ;;\<^sub>d P) (s, s'') \<and> tr<s'> = tr<s''>"
  using assms
proof (induction n arbitrary: s s')
  case 0

  from 0 consider
      (wait) "P (s, s')" "wait<s'>"
    | (cont) s0 where "P (s, s0)" "\<not> wait<s0>" "(?(True)\<^sub>e) (s0, s')"
    by (auto simp add: seq_comp_dlchp_def)

  then show ?case
  proof cases
    case wait

    have "((P ^\<^sup>d 0) ;;\<^sub>d P) (s, s')"
      using wait 0
      by (auto simp add: seq_comp_dlchp_def test_dlchp_def)

    then show ?thesis
      by blast

  next
    case (cont s0)

    have tr_eq: "tr<s'> = tr<s0>"
      using cont(3)
      by (auto simp add: test_dlchp_def)

    have "((P ^\<^sup>d 0) ;;\<^sub>d P) (s, s0)"
      using cont(1) 0
      by (auto simp add: seq_comp_dlchp_def test_dlchp_def)

    then show ?thesis
      using tr_eq
      by blast
  qed

next
  case (Suc n)

  from Suc.prems(2) consider
      (wait) "P (s, s')" "wait<s'>"
    | (cont) s0 where "P (s, s0)" "\<not> wait<s0>" "(P ^\<^sup>d Suc n) (s0, s')"
    by (auto simp add: seq_comp_dlchp_def)

  then show ?case
  proof cases
    case wait

    have "(P ^\<^sup>d Suc n) (s, s')"
      using wait
      by (auto simp add: seq_comp_dlchp_def)

    then have "((P ^\<^sup>d Suc n) ;;\<^sub>d P) (s, s')"
      using wait
      by (auto simp add: seq_comp_dlchp_def)

    then show ?thesis
      by blast

  next
    case (cont s0)

    obtain u where u:
      "((P ^\<^sup>d n) ;;\<^sub>d P) (s0, u)"
      "tr<s'> = tr<u>"
      using Suc
      using cont(2,3) by auto


    have "((P ;;\<^sub>d (P ^\<^sup>d n)) ;;\<^sub>d P) (s, u)"
      using seq_prepend_dlchp
      using cont(1,2) u(1) by blast 

    then have "((P ^\<^sup>d Suc n) ;;\<^sub>d P) (s, u)"
      by simp

    then show ?thesis
      using u(2)
      by blast
  qed
qed

lemma seq_loop_into_loop:
  assumes "(P ;;\<^sub>d (P\<^sup>d)) (s, s')"
  shows "(P\<^sup>d) (s, s')"
proof -
  from assms show ?thesis
  proof (auto simp add: seq_comp_dlchp_def)
    assume "P (s, s')" and "wait<s'>"
    hence "(P ^\<^sup>d Suc 0) (s, s')"
      by (auto simp add: seq_comp_dlchp_def)
    thus "(P\<^sup>d) (s, s')"
      unfolding loop_dlchp_def
      by blast
  next
    fix s0
    assume p: "P (s, s0)"
      and nw0: "\<not> wait<s0>"
      and loop: "(P\<^sup>d) (s0, s')"

    from loop obtain n where pow: "(P ^\<^sup>d n) (s0, s')"
      unfolding loop_dlchp_def
      by (metis SUP1_E)

    have "(P ^\<^sup>d Suc n) (s, s')"
      using p nw0 pow
      by (auto simp add: seq_comp_dlchp_def)

    thus "(P\<^sup>d) (s, s')"
      unfolding loop_dlchp_def
      by blast
  qed
qed


lemma loop_comm_wait_end_aux:
  assumes "\<not> wait<s>"  "wait<s'>" "((P ^\<^sup>d n) ;;\<^sub>d P) (s, s')" "waits_wf P"  "total P"
  shows "\<exists>s''. (P ;;\<^sub>d (P\<^sup>d)) (s, s'') \<and> tr<s''> = tr<s'>"
  using assms
proof (induction n arbitrary: s s')
  case 0

  from 0 have run0:
    "((?(True)\<^sub>e) ;;\<^sub>d P) (s, s')"
    by force

  from run0 show ?case
  proof (auto simp add: seq_comp_dlchp_def)
    fix s0
    assume test: "(?(True)\<^sub>e) (s, s0)"
      and nw0: "\<not> wait<s0>"
      and p: "P (s0, s')"

    have "s0 = s"
      using test nw0
      by (auto simp add: test_dlchp_def)

    hence "(P ;;\<^sub>d (P\<^sup>d)) (s, s')"
      using p 0(2)
      by (auto simp add: seq_comp_dlchp_def)

    then show "\<exists>s''. (P (s, s'') \<and> get\<^bsub>wait\<^esub> s'' \<or>
           (\<exists>s\<^sub>0. P (s, s\<^sub>0) \<and> \<not> get\<^bsub>wait\<^esub> s\<^sub>0 \<and> P\<^sup>d (s\<^sub>0, s''))) \<and>
          get\<^bsub>tr\<^esub> s'' = get\<^bsub>tr\<^esub> s'"
      by (auto simp add: seq_comp_dlchp_def)
  next
    assume test_wait: "(?(True)\<^sub>e) (s, s')"
      and wait_s': "wait<s'>"

    have tr_eq: "tr<s'> = tr<s>"
      using test_wait wait_s'
      by (auto simp add: test_dlchp_def)

    have total_wait:
      "\<exists>u. (P ;;\<^sub>d (P\<^sup>d)) (s, u) \<and> tr<u> = tr<s>"
      using 0(5) total_def total_loop total_seq_comp by blast

    then show "\<exists>s''. (P (s, s'') \<and> get\<^bsub>wait\<^esub> s'' \<or>
           (\<exists>s\<^sub>0. P (s, s\<^sub>0) \<and> \<not> get\<^bsub>wait\<^esub> s\<^sub>0 \<and> P\<^sup>d (s\<^sub>0, s''))) \<and>
          get\<^bsub>tr\<^esub> s'' = get\<^bsub>tr\<^esub> s'"
      using tr_eq by (auto simp add: seq_comp_dlchp_def)
  qed

next
  case (Suc n)

  from Suc.prems(3) have run:
    "((P ;;\<^sub>d (P ^\<^sup>d n)) ;;\<^sub>d P) (s, s')"
    by simp

  from run consider
      (early) "(P ;;\<^sub>d (P ^\<^sup>d n)) (s, s')" "wait<s'>"
    | (late) s0 where "(P ;;\<^sub>d (P ^\<^sup>d n)) (s, s0)" "\<not> wait<s0>" "P (s0, s')"
    by (auto simp add: seq_comp_dlchp_def)

  then show ?case
  proof cases
    case early

    from early(1) consider
        (first_wait) "P (s, s')" "wait<s'>"
      | (after_first) s0 where "P (s, s0)" "\<not> wait<s0>" "(P ^\<^sup>d n) (s0, s')"
      by (auto simp add: seq_comp_dlchp_def)

    then show ?thesis
    proof cases
      case first_wait

      have "(P ;;\<^sub>d (P\<^sup>d)) (s, s')"
        using first_wait
        by (auto simp add: seq_comp_dlchp_def)

      then show ?thesis
        by blast

    next
      case (after_first s0)

      have "(P\<^sup>d) (s0, s')"
        using after_first(3)
        unfolding loop_dlchp_def
        by blast

      hence "(P ;;\<^sub>d (P\<^sup>d)) (s, s')"
        using after_first(1,2)
        by (auto simp add: seq_comp_dlchp_def)

      then show ?thesis
        by blast
    qed

  next
    case (late s0)

    from late(1) consider
        (bad_wait) "P (s, s0)" "wait<s0>"
      | (continue) s1 where "P (s, s1)" "\<not> wait<s1>" "(P ^\<^sup>d n) (s1, s0)"
      by (auto simp add: seq_comp_dlchp_def)

    then show ?thesis
    proof cases
      case bad_wait

      then show ?thesis
        using late(2)
        by blast

    next
      case (continue s1)

      have tail_run: "((P ^\<^sup>d n) ;;\<^sub>d P) (s1, s')"
        using continue(3) late(2,3)
        by (auto simp add: seq_comp_dlchp_def)

      obtain u where u1: "(P ;;\<^sub>d (P\<^sup>d)) (s1, u)"
        and u2: "tr<u> = tr<s'>"
        using Suc.IH[OF continue(2) Suc.prems(2) tail_run Suc.prems(4) Suc.prems(5)]
        by blast

      have loop_u: "(P\<^sup>d) (s1, u)"
        using seq_loop_into_loop[OF u1] .

      have "(P ;;\<^sub>d (P\<^sup>d)) (s, u)"
        using continue(1,2) loop_u
        by (auto simp add: seq_comp_dlchp_def)

      then show ?thesis
        using u2 by blast
    qed
  qed
qed

lemma loop_comm_ac_prev2:
  assumes "((P\<^sup>d) ;;\<^sub>d P) (s,s')" "waits_wf P" "total P"
  shows "\<exists> s''. (P ;;\<^sub>d (P\<^sup>d)) (s, s'') \<and> tr<s'> = tr<s''>"
proof(cases "wait<s>")
  case True
  note waitstart = True
  have  "waits_wf ((P\<^sup>d) ;;\<^sub>d P)"
    using assms(2) waits_wf_loop waits_wf_seq_comp
    by blast
  then have s1:"s' = s"
    using waits_wf_def assms(1) waitstart skip_def
    by (metis (mono_tags, lifting) case_prodD)
  have "waits_wf (P ;;\<^sub>d (P\<^sup>d))"
    using assms(2) waits_wf_loop waits_wf_seq_comp
    by blast
  then have "(P ;;\<^sub>d (P\<^sup>d)) (s, s)"
    using waits_wf_def  waitstart skip_def assms(3) total_def
    by (smt (verit, del_insts) old.prod.case waits_wf_test)
  then have "(P ;;\<^sub>d (P\<^sup>d)) (s, s')"
    using s1 by auto
  then show ?thesis
    by blast 
next
  case False
  note nwaits_start = False
  obtain n where n1:"((P ^\<^sup>d n) ;;\<^sub>d P) (s,s')"
    using assms loop_dlchp_def
    by (smt (verit) SUP1_E curryD curryI curry_case_prod seq_comp_dlchp_def)
  show ?thesis 
  proof (cases "wait<s'>")
    case True
    note waits_end = True
    then show ?thesis
      using loop_comm_wait_end_aux[
        OF nwaits_start waits_end n1 assms(2) assms(3)]
      by auto
  next
    case False
    note nwaits_end = False
    then show ?thesis
      using nwaits_end nwaits_start assms(1) loop_comm_nwait
      by blast
  qed
qed




lemma loop_comm_ac:
  assumes "total P" "waits_wf P"
  shows "([(P ;;\<^sub>d (P\<^sup>d))]\<^sub>P {A,C} F) s = ([((P\<^sup>d) ;;\<^sub>d P)]\<^sub>P {A,C} F) s"
proof -
  {
    assume a1:"([(P ;;\<^sub>d (P\<^sup>d))]\<^sub>P {A,C} F) s"
    have commit_lhs:"(commit_dlchp (P ;;\<^sub>d (P\<^sup>d)) A C s)"
      using a1 fbox_ac_def by metis
    have post_lhs:"(post_dlchp (P ;;\<^sub>d (P\<^sup>d)) A F s)"
      using a1 fbox_ac_def by metis
    have "(commit_dlchp ((P\<^sup>d) ;;\<^sub>d P) A C s)"
    proof -
      {
        fix s' t n
        assume s1:"((P\<^sup>d) ;;\<^sub>d P) (s,s')"
        assume tr_assump: "\<forall> t < tr<s'> - tr<s>.A (trace_state_conc s t)"
        
        have exists_sim_run:"\<exists> s''. (P ;;\<^sub>d (P\<^sup>d)) (s,s'') \<and> (tr<s'> = tr<s''>)"
          using s1 loop_comm_ac_prev2 assms
          by blast

        obtain s'' where s2_is_run:"(P ;;\<^sub>d (P\<^sup>d)) (s,s'')"  and trs2_eq_s1:"(tr<s'> = tr<s''>)"
          using exists_sim_run by auto

        have "\<forall> t < tr<s''> - tr<s>.A (trace_state_conc s t)"
          using tr_assump  trs2_eq_s1 by auto
        
        then have "C (trace_state_conc s (tr<s''>-tr<s>))"
          using commit_lhs commit_dlchp_def s2_is_run
          by metis

        then have "C (trace_state_conc s (tr<s'>-tr<s>))"
          using trs2_eq_s1 by auto
      }
      then show ?thesis
        using commit_dlchp_def by blast
    qed


    moreover have  "(post_dlchp ((P\<^sup>d) ;;\<^sub>d P) A F s)"
    proof -
      {
        fix s'
        assume is_run:"((P\<^sup>d) ;;\<^sub>d P) (s, s')"
        assume nwaits_end:"\<not> wait<s'>"
        assume tr_assump :"\<forall> t \<le> (tr<s'>-tr<s>).  A (trace_state_conc s t)"
        have "waits_wf ((P\<^sup>d) ;;\<^sub>d P)"
          using assms(2) waits_wf_loop waits_wf_seq_comp
          by blast
        hence nwaits_start: "\<not> wait<s>"
          using is_run waits_wf_def
          by (metis (mono_tags, lifting) curryI curry_case_prod nwaits_end skip_def)
        
        have "(P ;;\<^sub>d (P\<^sup>d))  (s, s')"
          using nwaits_end nwaits_start loop_comm_nwait is_run by blast
        hence "F s'" 
          using post_lhs post_dlchp_def nwaits_end tr_assump by metis
      }
      then show ?thesis
        using post_dlchp_def by blast
    qed
    
    ultimately have "([((P\<^sup>d) ;;\<^sub>d P)]\<^sub>P {A,C} F) s"
      using fbox_ac_def
      by metis
  }

  moreover {
    assume rhs:"([((P\<^sup>d) ;;\<^sub>d P)]\<^sub>P {A,C} F) s"
    have commit_rhs:"commit_dlchp ((P\<^sup>d) ;;\<^sub>d P) A C s"
      using rhs fbox_ac_def by metis
    have post_rhs:"post_dlchp ((P\<^sup>d) ;;\<^sub>d P) A F s"
      using rhs fbox_ac_def by metis

    have "commit_dlchp (P ;;\<^sub>d (P\<^sup>d)) A C s"
    proof-
      {
        fix s'
        assume is_run:"(P ;;\<^sub>d (P\<^sup>d)) (s,s')"
        assume tr_ass:"\<forall> t < (tr<s'>-tr<s>).  A (trace_state_conc s t )"

        have exists_sim_run:"\<exists> s''. ((P\<^sup>d) ;;\<^sub>d P) (s,s'') \<and> (tr<s'> = tr<s''>)"
          using is_run loop_comm_ac_prev assms
          by blast

        obtain s'' where s2_is_run:"((P\<^sup>d) ;;\<^sub>d P) (s,s'')"  and trs2_eq_s1:"(tr<s'> = tr<s''>)"
          using exists_sim_run by auto

        have "\<forall> t < tr<s''> - tr<s>.A (trace_state_conc s t)"
          using tr_ass trs2_eq_s1 by auto
        
        then have "C (trace_state_conc s (tr<s''>-tr<s>))"
          using commit_rhs commit_dlchp_def s2_is_run
          by metis

        then have "C (trace_state_conc s (tr<s'>-tr<s>))"
          using trs2_eq_s1 by auto
      }
      then show ?thesis
        using commit_dlchp_def by blast
    qed

    moreover have  "(post_dlchp (P ;;\<^sub>d (P\<^sup>d)) A F s)"
    proof -
      {
        fix s'
        assume is_run:"(P ;;\<^sub>d (P\<^sup>d)) (s, s')"
        assume nwaits_end:"\<not> wait<s'>"
        assume tr_assump :"\<forall> t \<le> (tr<s'>-tr<s>).  A (trace_state_conc s t)"
        have "waits_wf (P ;;\<^sub>d (P\<^sup>d))"
          using assms(2) waits_wf_loop waits_wf_seq_comp
          by blast
        hence nwaits_start: "\<not> wait<s>"
          using is_run waits_wf_def
          by (metis (mono_tags, lifting) curryI curry_case_prod nwaits_end skip_def)
        
        have "((P\<^sup>d) ;;\<^sub>d P)  (s, s')"
          using nwaits_end nwaits_start loop_comm_nwait is_run by blast
        hence "F s'" 
          using post_rhs post_dlchp_def nwaits_end tr_assump by metis
      }
      then show ?thesis
        using post_dlchp_def by blast
    qed
    
    ultimately have "([(P ;;\<^sub>d (P\<^sup>d))]\<^sub>P {A,C} F) s"
      using fbox_ac_def
      by metis
  }
  ultimately show ?thesis
    by auto
qed


lemma loop_pre_from_all_powers:
  assumes  "\<forall>n. ([P ^\<^sup>d n]\<^sub>P {A,C} F) s"
  shows "([P\<^sup>d]\<^sub>P {A,C} F) s"
proof -
  have comm: "\<forall> n. commit_dlchp (P ^\<^sup>d n) A C s"
    using assms unfolding fbox_ac_def
    by blast

  have post: "\<forall> n. post_dlchp (P ^\<^sup>d n) A F s"
    using assms unfolding fbox_ac_def by blast

  have commit_loop: "commit_dlchp (P\<^sup>d) A C s"
  proof -
    {
    fix s'
    assume is_run: "(P\<^sup>d) (s, s')"
    assume tr_ass: "\<forall>t < (tr<s'> - tr<s>). A (trace_state_conc s t)"

    obtain n where run_n: "(P ^\<^sup>d n) (s, s')"
      using is_run unfolding loop_dlchp_def 
      by (metis SUP1_E)

    have "C (trace_state_conc s (tr<s'> - tr<s>))"
      using comm run_n tr_ass unfolding commit_dlchp_def by blast
    }
    then show ?thesis 
      unfolding commit_dlchp_def by blast
  qed

  have post_loop: "post_dlchp (P\<^sup>d) A F s"
  proof -
    {
    fix s'
    assume is_run: "(P\<^sup>d) (s, s')"
    assume tr_ass: "(\<forall>t \<le> (tr<s'> - tr<s>). A (trace_state_conc s t)) \<and> \<not> wait<s'>"

    obtain n where run_n: "(P ^\<^sup>d n) (s, s')"
      using is_run unfolding loop_dlchp_def 
      by (metis SUP1_E)

    have "F s'"
      using post run_n tr_ass unfolding post_dlchp_def by blast
  }
  then show ?thesis 
    unfolding post_dlchp_def by blast
  qed

  show ?thesis
    using commit_loop post_loop  unfolding fbox_ac_def by simp
qed



end