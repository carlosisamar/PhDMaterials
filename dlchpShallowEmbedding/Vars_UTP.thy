theory Vars_UTP
  imports "UTP2.utp" "Scene_spaces_extra"
begin
unbundle UTP_Syntax

definition FV :: "('a::scene_space \<Rightarrow> 'b) \<Rightarrow> 'a scene set" where
[expr_defs]: "FV(P)= {x \<in> set Vars. \<not> (x \<sharp> P)}"

definition FV_list ::  "('a::scene_space \<Rightarrow> 'b) \<Rightarrow> 'a scene list" where
[expr_defs]: "FV_list(P)= filter (\<lambda> x. \<not> (x \<sharp> P)) Vars"

 (* "BV_progs_list P = filter (\<lambda> x. \<exists> s\<^sub>0 s\<^sub>0'. s\<^sub>0'\<in> P s\<^sub>0 \<and>  \<not>(s\<^sub>0 \<approx>\<^sub>S s\<^sub>0' on x)) Vars "*)

lemma FV_finite [simp]: "finite (FV P)"
  by (simp add: FV_def)

lemma FV_Vars [simp]: "FV(P) \<subseteq> set Vars"
  by (simp add: FV_def)

lemma FV_then_not_unrest: "a \<in> FV(P) \<Longrightarrow> \<not>(a \<sharp> P)"
  by (simp add:FV_def)

lemma FV_iff: "a \<in> FV(P) \<longleftrightarrow> (a \<in> set Vars \<and> \<not>(a \<sharp> P))"
  by (simp add:FV_def)

lemma FV_Platzer_def: "FV(P) = {x \<in> set Vars. \<exists> s s'. s \<approx>\<^sub>S s' on -x \<and> P s \<noteq> P s'}"
  apply (simp add: FV_def)
  apply safe
  apply (simp add:unrest_expr_def)
  apply (metis scene_equiv_def scene_override_commute scene_override_overshadow_left)
  by (metis scene_equiv_def scene_override_commute unrest_expr_def)

definition FV_progs :: "(('s::scene_space \<times> 's) \<Rightarrow> bool) \<Rightarrow> 's scene set" where
 [expr_defs]: "FV_progs P = {x \<in> set Vars. \<exists> s\<^sub>0 s\<^sub>1 s\<^sub>0'.  s\<^sub>0 \<approx>\<^sub>S s\<^sub>1 on -x \<and> P (s\<^sub>0, s\<^sub>0') \<and> (\<not> (\<exists> s\<^sub>1'. s\<^sub>0' \<approx>\<^sub>S s\<^sub>1' on -x \<and> P (s\<^sub>1, s\<^sub>1'))) }"

lemma FV_is_vars :  "FV_progs P \<subseteq> set Vars"
  using FV_progs_def by blast

definition BV_progs ::  "(('s::scene_space \<times> 's) \<Rightarrow> bool) \<Rightarrow> 's scene set" where
  [expr_defs]: "BV_progs P =  {x \<in> set Vars. \<exists> s\<^sub>0 s\<^sub>0'. P (s\<^sub>0, s\<^sub>0') \<and>  \<not>(s\<^sub>0 \<approx>\<^sub>S s\<^sub>0' on x)} "

lemma BV_is_vars: "BV_progs P \<subseteq> set Vars"
  using BV_progs_def by blast

definition bound_eff_prop :: "('s hrel) \<Rightarrow> 's scene \<Rightarrow> bool" where
  [expr_defs]: "bound_eff_prop P S = (\<forall> s s'. P (s, s') \<longrightarrow>  s  \<approx>\<^sub>S s' on S)  "


lemma bound_eff_1: "bound_eff_prop P (-(\<Union>\<^sub>S ( BV_progs P) )) "
proof -
  have "bound_eff_prop P ((\<Union>\<^sub>S(set Vars - ( BV_progs P) )))"
    by (smt (verit) BV_progs_def DiffD1 DiffD2 Diff_subset bound_eff_prop_def mem_Collect_eq
        order.trans scene_union_equiv set_Vars_scene_space)
  thus ?thesis
    by  (metis scene_minus BV_is_vars)
qed
      

lemma bound_effect:
  assumes "S \<subseteq> set Vars" " bound_eff_prop P (-( \<Union>\<^sub>S  S ))" 
  shows "BV_progs P \<subseteq> S "
proof -
  have "bound_eff_prop P ((\<Union>\<^sub>S(set Vars - S )))"
    using assms
    by (metis  scene_minus)
  thus ?thesis
    by (smt (verit) BV_progs_def DiffI Diff_subset bound_eff_prop_def le_Sup_scene mem_Collect_eq
        scene_lessthan_equiv set_Vars_scene_space ss_clat.sup_closed subset_eq)
qed

lemma bound_eff_2:
  assumes "P (s, s')" "v \<in> set Vars" "v \<notin> (BV_progs P)"
  shows  "s' \<approx>\<^sub>S s on v"
  by (metis (mono_tags, lifting) BV_progs_def assms(1,2,3) idem_scene_Vars mem_Collect_eq
      scene_equiv_sym)

lemma bound_eff_3:
  assumes "P (s, s')" "V \<subseteq> set Vars" "V \<inter> (BV_progs P) = {}"
  shows  "s' \<approx>\<^sub>S s on (\<Union>\<^sub>S V)"
  by (smt (verit, ccfv_SIG) assms(1,2,3) bound_eff_2 disjoint_iff_not_equal scene_union_equiv
      set_Vars_scene_space subset_iff)

definition coincidence_eff_term_prop :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a scene set \<Rightarrow> bool" where
 [expr_defs]: "coincidence_eff_term_prop T S = (\<forall> s s'.(\<forall> x \<in> S.  s  \<approx>\<^sub>S s' on x) \<longrightarrow> T s = T s' )"

lemma unrest_scene_equiv: "(a \<sharp> P) \<longleftrightarrow> (\<forall> s s'. s \<approx>\<^sub>S s' on (-a) \<longrightarrow> P s = P s')"
  by (metis scene_equiv_def scene_override_commute scene_override_overshadow_left
      unrest_expr_def)

lemma unrest_Union_Vars:
  fixes P :: "'s::scene_space \<Rightarrow> 'a"
  assumes "set S \<subseteq> set Vars" "\<forall>x \<in> set S. (x \<sharp> P)"
  shows "unrest_expr (\<Squnion>\<^sub>S S) P"
  using assms
proof (induct S)
  case Nil
  then show ?case
    by (metis emp_alpha_def foldr.simps(1) id_apply unrest_empty) 
next
  case (Cons a S)
  then show ?case
    by (metis foldr.simps(2) insert_subset list.set_intros(1,2) list.simps(15) o_apply
        unrest_var_union) 
qed


lemma unrest_all_Vars:
  fixes P :: "'s::scene_space \<Rightarrow> 'a"
  assumes "\<forall>x \<in> set Vars. (x \<sharp> P)"
  shows "\<Sigma> \<sharp> P"
  by (simp add: assms order.refl top_scene_eq univ_alpha_def unrest_Union_Vars)
  
lemma unrest_not_FV:
  assumes "set xs = FV P"
  shows "unrest_expr (- (\<Squnion>\<^sub>S xs)) P"
  using assms
  by (auto intro: unrest_Union_Vars simp add: uminus_vars_other_vars FV_iff)

lemma coin_eff_term_1: "coincidence_eff_term_prop P (FV P)"
proof -
  obtain xs where xs: "set xs = FV P" "distinct xs"
    using FV_finite finite_distinct_list by blast
  show ?thesis
  proof (simp add: coincidence_eff_term_prop_def, safe)
    fix s s'
    assume "\<forall>x\<in>FV P. s \<approx>\<^sub>S s' on x"
    hence "s \<approx>\<^sub>S s' on \<Squnion>\<^sub>S xs"
      by (metis FV_iff all_Vars_equiv_scene subsetI xs(1))
    thus "P s = P s'"
      by (metis uminus_scene_twice unrest_not_FV unrest_scene_equiv xs(1))
  qed
qed

lemma coin_eff_term_2: "coincidence_eff_term_prop P UNIV"
    apply (simp add: coincidence_eff_term_prop_def FV_Platzer_def)
  by (metis scene_equiv_def scene_override_id)
     
lemma coin_effect_prop: 
  assumes " S \<subseteq> set Vars" "coincidence_eff_term_prop P  S"
  shows "(FV P) \<subseteq> S"
  using assms
proof -
  {
    fix x
    assume "x \<in> (FV P)"
    assume nx: "x \<notin> S"
    obtain s s' where  fvx:"s \<approx>\<^sub>S s' on -x \<and> P s \<noteq> P s'"
      using FV_Platzer_def \<open>x \<in> FV P\<close> by blast
    then have "\<not> ((\<forall> y \<in> S. s  \<approx>\<^sub>S s' on y) \<longrightarrow> P s = P s')"
      using nx fvx
      by (metis (no_types, lifting) ext FV_iff \<open>x \<in> FV P\<close> assms(1) equalityD2 foldr_scene_union_removeAll le_vars_then_equal scene_equiv_bot
          scene_in_foldr scene_lessthan_equiv scene_space_compats scene_space_uminus set_Vars_scene_space subsetD uminus_var_other_vars
          var_le_union_iff)
    then have "\<not> (coincidence_eff_term_prop P  S)"
      using coincidence_eff_term_prop_def
      by (metis FV_iff \<open>s \<approx>\<^sub>S s' on - x \<and> \<not> P s = P s'\<close> \<open>x \<in> FV P\<close> idem_scene_space scene_equiv_def
          scene_equiv_sym scene_override_commute set_Vars_scene_space subset_eq)
  }
  thus ?thesis
    using assms
    by blast
qed

definition coincidence_eff_prog_prop :: "('s::scene_space hrel) \<Rightarrow> 's scene set  \<Rightarrow> bool" where
 [expr_defs]: "coincidence_eff_prog_prop P S = (\<forall> V. S \<subseteq> V \<and> V \<subseteq> set Vars \<longrightarrow> (\<forall> s1 s2 s1'.(((s1  \<approx>\<^sub>S s2 on \<Union>\<^sub>S V) \<and> P(s1,s1')) \<longrightarrow> (\<exists> s2'. (P(s2,s2')\<and> ( s1'  \<approx>\<^sub>S s2' on \<Union>\<^sub>S V) ) ))))"

lemma coincidence_eff_prog_1:
  shows "coincidence_eff_prog_prop P (FV_progs P)"
proof-
  {
  fix S s1 s1' s3 s2
  assume a1:"S \<subseteq> (set Vars - (FV_progs P))"
  assume a2:"P (s1, s1')"
  assume a4:"s1  \<approx>\<^sub>S s3 on -(\<Union>\<^sub>S S)" and a5: "s2  \<approx>\<^sub>S s3 on (\<Union>\<^sub>S S)"
  have "\<exists> s3'. (P(s3,s3') \<and> s1'\<approx>\<^sub>S s3' on -(\<Union>\<^sub>S S))"
  proof-
    have "finite S"
      by (metis List.finite_set a1 finite_Diff rev_finite_subset)
    thus ?thesis
      using a1 a2 a4 a5
    proof (induct S arbitrary:s3)
      case empty
      then show ?case 
        using equiv_vars_is_eq empty_neg_is_vars
        by (simp add: scene_equiv_def)
    next
      case (insert x F)
      have h1:"F \<subseteq> set Vars - FV_progs P"
        using insert.prems(1) by blast
      have h8:"(insert x F) \<subseteq> set Vars"
          by (meson Diff_subset insert.prems(1) order.trans)
      obtain ss3 where h2:"s1 \<approx>\<^sub>S ss3 on - \<Union>\<^sub>S F" and h3:"s2  \<approx>\<^sub>S ss3 on (\<Union>\<^sub>S F)"
        using insert.prems(2) insert.hyps(3) h1
        by (metis Sup_scene_closed idem_scene_space scene_equiv_def scene_equiv_sym
            scene_override_commute scene_override_overshadow_left)
      obtain ss3' where h4:"P (ss3, ss3')" and h5: " s1' \<approx>\<^sub>S ss3' on - \<Union>\<^sub>S F"
        using  insert.hyps(3) h1 h2 h3 a2 by blast
      have x1:"x \<notin> FV_progs P"
        by (meson DiffD2 insert.prems(1) insert_subset)
      have "ss3 \<approx>\<^sub>S s3 on - x"
        using h2 h3 insert.prems(3) insert.prems(4) scene_agree_single_var
        by (smt (verit, del_insts) Diff_subset Sup_scene_closed idem_scene_space idem_scene_uminus
            insert.prems(1) insert_subset le_iff_sup le_sup_iff scene_equiv_sym)
      obtain s3' where h6:"ss3' \<approx>\<^sub>S s3' on - x" and h7:"P (s3, s3')"
        using x1 h4 FV_progs_def
        by (smt (verit, del_insts) Diff_insert0 \<open>ss3 \<approx>\<^sub>S s3 on - x\<close> insert.prems(1) insertI1
            mem_Collect_eq subset_Diff_insert)
      have "ss3' \<approx>\<^sub>S s3' on - \<Union>\<^sub>S (insert x F)"
          using h6 scene_subset_equiv scene_minus h8
          by (smt (verit) insertI1 le_Sup_scene scene_compl_subset_iff scene_lessthan_equiv
              scene_space_uminus set_Vars_scene_space ss_clat.sup_closed subsetD subset_trans)
      moreover have "s1' \<approx>\<^sub>S ss3' on - \<Union>\<^sub>S (insert x F)"
        using h5 h8 scene_subset_equiv scene_minus
        by (smt (verit, del_insts) Sup_scene_closed dual_order.trans insert.hyps(2)
            order_class.order_eq_iff scene_compl_subset_iff scene_lessthan_equiv
            scene_subset_union_lessthan set_Vars_scene_space subset_insert_iff)
      ultimately have "s1' \<approx>\<^sub>S s3' on - \<Union>\<^sub>S (insert x F)"
        by (metis (no_types, lifting) ext scene_equiv_def scene_override_overshadow_right)
      then show ?case
        using h7 by blast
    qed
  qed
} 
  note thmname = this
  show ?thesis
  proof -
    {
    fix V
    assume a1:"FV_progs P \<subseteq> V" and  a2:"V \<subseteq> set Vars"
    fix s1 s1' s3
    assume a3:"s1 \<approx>\<^sub>S s3 on \<Union>\<^sub>S V" and a4:"P (s1, s1')" 
    obtain s2 where a5:"s2 \<approx>\<^sub>S s3 on -\<Union>\<^sub>S V"
      by (meson a2 dual_order.trans scene_composition_complement set_Vars_scene_space)
    have "set Vars - V \<subseteq> set Vars - FV_progs P"
      using a1 a2 by blast
    then have "\<exists>s3'. P (s3, s3') \<and> s1' \<approx>\<^sub>S s3' on  \<Union>\<^sub>S V"
      using thmname[where ?S2="set Vars - V"] a3 a4 a5
      by (simp add: a2 scene_equiv_def scene_minus)
  }
  note thmname2 = this
  have "\<forall>V. FV_progs P \<subseteq> V \<and>
         V \<subseteq> set Vars \<longrightarrow>
         (\<forall>s1 s2 s1'.
             s1 \<approx>\<^sub>S s2 on \<Union>\<^sub>S V \<and> P (s1, s1') \<longrightarrow>
             (\<exists>s2'. P (s2, s2') \<and> s1' \<approx>\<^sub>S s2' on \<Union>\<^sub>S V))"
    apply (safe)
    apply (rule thmname2)
       apply (simp_all)
    done
    then show ?thesis
       by (simp add: coincidence_eff_prog_prop_def)
   qed
qed



lemma coincidence_lemma_progs:
  assumes  "coincidence_eff_prog_prop P S" "S \<subseteq> set Vars"
  shows "FV_progs P \<subseteq> S"
proof -
  {
    fix v S
    assume a1:"v \<in> (FV_progs P) - S"
    assume a2: "S \<subseteq> set Vars"
    have "\<not> coincidence_eff_prog_prop P S"
    proof -
      have "v \<in> FV_progs P"
        using a1 by blast
      then have "\<exists> s\<^sub>0 s\<^sub>1 s\<^sub>0'.  s\<^sub>0 \<approx>\<^sub>S s\<^sub>1 on -v \<and> P (s\<^sub>0, s\<^sub>0') \<and> (\<not> (\<exists> s\<^sub>1'. s\<^sub>0' \<approx>\<^sub>S s\<^sub>1' on -v \<and> P (s\<^sub>1, s\<^sub>1')))"
        using FV_progs_def by blast
      moreover have"S \<subseteq> set Vars -{v}"
        by (metis Diff_empty Diff_iff a1 a2 subset_Diff_insert)
      ultimately show ?thesis
        using coincidence_eff_prog_prop_def
        by (smt (verit, best) Diff_subset FV_is_vars a1 dual_order.trans scene_minus2
            subset_Compl_singleton)
    qed
  }
  note thmname = this
  show ?thesis
    using thmname[where ?Sa2 = S] assms
    by blast
qed

        
lemma seq_comm:
  fixes P :: "'s::scene_space hrel" and Q :: "'s hrel"
  assumes "(BV_progs P) \<inter> (BV_progs Q) = {}" "(FV_progs P)  \<inter> (BV_progs Q) = {}" "(FV_progs Q)  \<inter> (BV_progs P) = {}"
  shows "P;;Q = Q;;P"
proof -
  {
    fix s s' P Q
    assume as1:"(BV_progs P) \<inter> (BV_progs Q) = {}" and as2:"(FV_progs P)  \<inter> (BV_progs Q) = {}" and 
            as3:"(FV_progs Q)  \<inter> (BV_progs P) = {}"
    have "(P;;Q)(s,s') \<longrightarrow> (Q;;P)(s, s')"
    proof-
      {
      assume a1:"(P;;Q)(s,s')"
      obtain s\<^sub>P where  h1:"P(s,s\<^sub>P)" and h2:"Q(s\<^sub>P,s')"
        using a1 seq_def
        by (smt (verit, ccfv_SIG) old.prod.case)
      have l1:"s  \<approx>\<^sub>S s\<^sub>P on -(\<Union>\<^sub>S(BV_progs P))"
        using  a1
        by (meson h1 bound_eff_1 bound_eff_prop_def)
      then have "s\<^sub>P  \<approx>\<^sub>S s' on -(\<Union>\<^sub>S(BV_progs Q))"
        using h2
        by (meson bound_eff_1 bound_eff_prop_def)
      have "\<exists> s\<^sub>Q. (Q(s,s\<^sub>Q) \<and> s\<^sub>Q  \<approx>\<^sub>S s' on -(\<Union>\<^sub>S(BV_progs P)))"
      proof -
        have "s\<^sub>P  \<approx>\<^sub>S s on (\<Union>\<^sub>S(set Vars -BV_progs P))"
          using l1
          by (metis BV_is_vars scene_comm scene_minus)
        moreover have "FV_progs Q \<subseteq> set Vars - BV_progs P"
          using as3
          by (simp add: Diff_eq FV_is_vars inf_shunt)
        ultimately have "\<exists>s\<^sub>Q. Q (s, s\<^sub>Q) \<and> s' \<approx>\<^sub>S s\<^sub>Q  on  \<Union>\<^sub>S (set Vars - BV_progs P)"
          using h2 coincidence_eff_prog_prop_def coincidence_eff_prog_1
          using Diff_subset by blast
        thus ?thesis
          by (metis BV_is_vars scene_comm scene_minus)
      qed

      obtain s\<^sub>Q where h3:"Q(s,s\<^sub>Q)" and  h4:"s\<^sub>Q  \<approx>\<^sub>S s' on -(\<Union>\<^sub>S(BV_progs P))"
        using \<open>\<exists>s\<^sub>Q. Q (s, s\<^sub>Q) \<and> s\<^sub>Q \<approx>\<^sub>S s' on - \<Union>\<^sub>S (BV_progs P)\<close> by blast

      have l2:"s\<^sub>Q \<approx>\<^sub>S s on -\<Union>\<^sub>S (BV_progs Q)"
        using h3
        by (metis BV_is_vars bound_eff_1 bound_eff_prop_def scene_comm scene_minus)

      have "\<exists> s''. (P(s\<^sub>Q,s'') \<and> s''  \<approx>\<^sub>S s' on -(\<Union>\<^sub>S(BV_progs Q)))"
      proof -
        have "s  \<approx>\<^sub>S s\<^sub>Q on (\<Union>\<^sub>S(set Vars -BV_progs Q))"
          using l2
          by (metis BV_is_vars scene_comm scene_minus)
        moreover have "FV_progs P \<subseteq> set Vars - BV_progs Q"
          using as2
          by (simp add: Diff_eq FV_is_vars inf_shunt)
        ultimately have "\<exists>s''. P (s\<^sub>Q, s'') \<and> s' \<approx>\<^sub>S s''  on  \<Union>\<^sub>S (set Vars - BV_progs Q)"
          using h1 coincidence_eff_prog_prop_def coincidence_eff_prog_1
          by (smt (verit, ccfv_threshold) BV_is_vars Diff_subset \<open>s\<^sub>P \<approx>\<^sub>S s' on - \<Union>\<^sub>S (BV_progs Q)\<close> equalityD1 scene_comm scene_minus scene_subset_agreement)
        thus ?thesis
          by (metis BV_is_vars scene_comm scene_minus)      
      qed
      obtain s'' where h5:"P(s\<^sub>Q,s'')" and  h6:"s''  \<approx>\<^sub>S s' on -(\<Union>\<^sub>S(BV_progs Q))"
        using \<open>\<exists>s''. P (s\<^sub>Q, s'') \<and> s'' \<approx>\<^sub>S s' on - \<Union>\<^sub>S (BV_progs Q)\<close> by blast
      have "s'' \<approx>\<^sub>S s' on \<Union>\<^sub>S (set Vars)"
      proof -
        have "s'' \<approx>\<^sub>S s\<^sub>Q on \<Union>\<^sub>S (set Vars - BV_progs P)"
          using h5
          by (metis BV_is_vars bound_eff_1 bound_eff_prop_def scene_comm scene_minus)
        then have "s''  \<approx>\<^sub>S s' on (\<Union>\<^sub>S(set Vars - BV_progs P))"
          using h4
          by (metis BV_is_vars scene_equiv_def scene_minus scene_override_overshadow_right)
        moreover have "s''  \<approx>\<^sub>S s' on (\<Union>\<^sub>S(set Vars - BV_progs Q))"
          using h6
          by (metis BV_is_vars scene_minus)
        ultimately show ?thesis
          using as1
          by (metis BV_is_vars Diff_iff Int_iff empty_neg_is_vars empty_subsetI scene_minus
              scene_neg_decomp)
      qed
      then have "(Q;;P)(s, s')"
        by (metis (mono_tags, lifting) equiv_vars_is_eq h3 h5 prod.simps(2) utp_rel.seq_def)
    }
    then show ?thesis by auto
  qed
}
  note generic = this
  have "\<forall> s s'.(P;;Q)(s,s') \<longrightarrow> (Q;;P)(s, s')"
    using generic assms
    by blast
  moreover have  "\<forall> s s'.(Q;;P)(s,s') \<longrightarrow> (P;;Q)(s, s')"
    using generic assms
    by blast
  ultimately show ?thesis by auto
qed


lemma nmods_then_BV:
  assumes "vwb_lens x" "P nmods ($x)"
  shows "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<notin> BV_progs(P)"
  using assms
  apply (simp add: BV_progs_def pred)
  apply (meson Scenes_extra.scene_equiv_get_eq)
  apply (metis assms(2) nmods_iff var_alpha_def)
  done

lemma nBV_iff_nmods:
  assumes "vwb_lens x" "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> set Vars"
  shows "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<notin> BV_progs(P) \<longleftrightarrow> P nmods ($x)"
  using assms
  apply (simp add: BV_progs_def pred)
  apply (meson Scenes_extra.scene_equiv_get_eq)
  apply (smt (verit) Scenes_extra.scene_equiv_get_eq cond_case_prod_eta lens_override_def
      lens_override_idem)
  apply (metis (mono_tags, lifting) case_prod_conv lens_scene_override scene_equiv_def
      vwb_lens_def)
  done


definition para_dl :: "'s::scene_space hrel \<Rightarrow> 's hrel \<Rightarrow> 's hrel" where
  "para_dl P Q = (\<lambda> (s, s\<^sub>0). (\<exists> s' s''. s\<^sub>0 = s'' \<oplus>\<^sub>S s' on (\<Union>\<^sub>S (BV_progs P)) \<and> P (s, s') \<and> Q (s, s'')))"


definition partial_left :: "'s::scene_space \<Rightarrow> 's \<Rightarrow> 's hrel \<Rightarrow> bool" where
  "partial_left w s' P = (w \<approx>\<^sub>S s' on (\<Union>\<^sub>S (BV_progs P))) "

definition partial_right :: "'s::scene_space \<Rightarrow> 's \<Rightarrow> 's hrel \<Rightarrow> bool" where
  "partial_right w wq P  = (w \<approx>\<^sub>S wq on -(\<Union>\<^sub>S (BV_progs P))) "

lemma partial_paral:
  assumes "(para_dl P Q) (s, w)" "partial_right w wq P " "partial_left w s' P"
  shows "w = wq \<oplus>\<^sub>S s' on (\<Union>\<^sub>S (BV_progs P))"
  by (metis assms(2,3) partial_left_def partial_right_def scene_equiv_def
      scene_override_commute scene_override_overshadow_left)

lemma partial_paral_left:
  assumes "(para_dl P Q) (s, w)"
  shows "\<exists> s'. P (s, s') \<and> (partial_left w s' P)"
  by (smt (verit, del_insts) assms curry_case_prod curry_conv para_dl_def partial_left_def
      scene_equiv_def scene_override_overshadow_left)


lemma partial_paral_right:
  assumes  "(para_dl P Q) (s, w)"
  shows "\<exists> s'. Q (s, s') \<and> (partial_right w s' P)"
  by (smt (verit, ccfv_SIG) assms internal_case_prod_conv internal_case_prod_def para_dl_def
      partial_right_def scene_equiv_def scene_override_commute scene_override_overshadow_left)


lemma partial_paral_right_extra:
  assumes "(para_dl P Q) (s, w)" "Q (s, s')" "partial_right w s' P" "(BV_progs P) \<inter> (BV_progs Q) = {}"
  shows  "w \<approx>\<^sub>S s' on \<Union>\<^sub>S(BV_progs Q)"
proof -
  have " (\<Union>\<^sub>S(BV_progs Q)) \<le> (-(\<Union>\<^sub>S (BV_progs P)))"
    using assms(4)
    by (smt (verit) BV_is_vars Diff_eq Diff_subset Int_commute dual_order.trans inf_shunt le_inf_iff
        scene_minus scene_subset_union_lessthan set_Vars_scene_space)
  thus ?thesis
    by (meson BV_is_vars Sup_scene_closed assms(3) dual_order.trans partial_right_def
        scene_lessthan_equiv scene_space_uminus set_Vars_scene_space)
qed


lemma partial_paral_left_inv:
  assumes " P (s, ps)" "Q (s, qs)"
  shows "\<exists> w. ((para_dl P Q) (s,w))\<and> (partial_left w ps P)"
proof -
  obtain w where "w = qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S (BV_progs P))"
    by simp
  have "((para_dl P Q) (s,w))"
    using  para_dl_def
    by (metis (mono_tags, lifting) \<open>w = qs \<oplus>\<^sub>S ps on \<Union>\<^sub>S (BV_progs P)\<close> assms(1,2) curryD
        curry_case_prod)
  thus ?thesis
    by (metis \<open>w = qs \<oplus>\<^sub>S ps on \<Union>\<^sub>S (BV_progs P)\<close> partial_left_def scene_equiv_def
        scene_override_overshadow_left)
qed


lemma partial_paral_right_inv:
  assumes " P (s, ps)" "Q (s, qs)"
  shows "\<exists> w. ((para_dl P Q) (s,w))\<and> (partial_right w qs P)"
proof -
  obtain w where "w = qs \<oplus>\<^sub>S ps on (\<Union>\<^sub>S (BV_progs P))"
    by simp
  have "((para_dl P Q) (s,w))"
    using  para_dl_def
    by (metis (mono_tags, lifting) \<open>w = qs \<oplus>\<^sub>S ps on \<Union>\<^sub>S (BV_progs P)\<close> assms(1,2) curryD
        curry_case_prod)
  thus ?thesis
    by (metis \<open>w = qs \<oplus>\<^sub>S ps on \<Union>\<^sub>S (BV_progs P)\<close> partial_right_def scene_equiv_def
        scene_override_commute scene_override_overshadow_right)
qed
  
    

lemma para_dl_non_inter2: 
  assumes "((para_dl P Q) (s,w))" "P (s, ps)" "partial_left w ps P"
  shows "w \<approx>\<^sub>S ps on ((\<Union>\<^sub>S (BV_progs P)) \<sqinter>\<^sub>S  - (\<Union>\<^sub>S (BV_progs Q) )) "
proof -
  have "w \<approx>\<^sub>S ps on (\<Union>\<^sub>S (BV_progs P))"
    using assms partial_left_def
    by blast
  thus ?thesis
    by (metis (mono_tags, lifting) Sup_scene_closed scene_intersect_equiv  scene_space_uminus )
qed

lemma para_dl_non_inter3: 
  assumes "((para_dl P Q) (s,w))" "P (s, ps)" "partial_left w ps P"
  shows "w \<approx>\<^sub>S ps on (((\<Union>\<^sub>S (BV_progs P)) \<sqinter>\<^sub>S  ((-\<Union>\<^sub>S(BV_progs Q) ) )) \<squnion>\<^sub>S 
                   ((-(\<Union>\<^sub>S(BV_progs P))) \<sqinter>\<^sub>S  (-(\<Union>\<^sub>S(BV_progs Q) ) ))) "
proof -
    obtain qs where "Q (s,qs)" "partial_right w qs P"
      using partial_paral_right assms(1)
      by blast
    have "w \<approx>\<^sub>S ps on  ((-(\<Union>\<^sub>S (BV_progs P))) \<sqinter>\<^sub>S  (-(\<Union>\<^sub>S (BV_progs Q))))"
    proof -
      have  "s \<approx>\<^sub>S ps on (-(\<Union>\<^sub>S (BV_progs P)))"
        by (meson \<open>P (s, ps)\<close> bound_eff_1 bound_eff_prop_def)
      moreover have "s \<approx>\<^sub>S qs on (-(\<Union>\<^sub>S (BV_progs Q)))"
        by (meson \<open>Q (s,qs)\<close> bound_eff_1 bound_eff_prop_def)
      moreover have "w  \<approx>\<^sub>S qs on (-(\<Union>\<^sub>S (BV_progs P)))"
        using \<open>partial_right w qs P\<close> partial_right_def by blast
      ultimately have "qs \<approx>\<^sub>S ps on ((-(\<Union>\<^sub>S(BV_progs P))) \<sqinter>\<^sub>S (-(\<Union>\<^sub>S(BV_progs Q))))"
        using scene_intersect_equiv_trans
        by (smt (verit, ccfv_threshold) BV_progs_def Collect_mono_iff Sup_scene_closed
            idem_scene_space scene_equiv_sym scene_space_def scene_space_inter scene_space_uminus
            scene_spacep.intros(2))
      then show ?thesis
        by (smt (verit, del_insts) BV_progs_def Collect_mono_iff Sup_scene_closed
            \<open>w \<approx>\<^sub>S qs on - \<Union>\<^sub>S (BV_progs P)\<close> scene_equiv_def scene_intersect_equiv
            scene_override_overshadow_right scene_space_def scene_space_uminus
            scene_spacep.intros(2))        
    qed
    show "w \<approx>\<^sub>S ps on (\<Union>\<^sub>S (BV_progs P) \<sqinter>\<^sub>S - \<Union>\<^sub>S (BV_progs Q) \<squnion>\<^sub>S
                  - \<Union>\<^sub>S (BV_progs P) \<sqinter>\<^sub>S - \<Union>\<^sub>S (BV_progs Q))"
      by (metis \<open>w \<approx>\<^sub>S ps on - \<Union>\<^sub>S (BV_progs P) \<sqinter>\<^sub>S - \<Union>\<^sub>S (BV_progs Q)\<close> assms(1,2,3)
          para_dl_non_inter2 scene_equiv_bot scene_equiv_def scene_override_union
          scene_union_incompat)
qed
    
    
lemma para_dl_non_inter4: 
  assumes "((para_dl P Q) (s,w))"  "P (s, ps)" "partial_left w ps P"
  shows "(w \<approx>\<^sub>S ps on ( (-\<Union>\<^sub>S (BV_progs Q)))) "
proof -
  have "w \<approx>\<^sub>S ps on (((\<Union>\<^sub>S (BV_progs P)) \<sqinter>\<^sub>S  ((-\<Union>\<^sub>S(BV_progs Q) ) )) \<squnion>\<^sub>S 
                   ((-(\<Union>\<^sub>S(BV_progs P))) \<sqinter>\<^sub>S  (-(\<Union>\<^sub>S(BV_progs Q) ) ))) "
    using para_dl_non_inter3 assms(1,2,3) by blast
  then show ?thesis
    by (smt (verit) BV_progs_def Collect_mono_iff Sup_scene_closed idem_scene_space
        scene_demorgan1 scene_inter_commute scene_inter_compl
        scene_space_class.scene_union_inter_distrib scene_space_def scene_space_uminus
        scene_spacep.intros(2) scene_union_unit(1) uminus_scene_twice)
  qed

definition non_inter :: "'s::scene_space hrel \<Rightarrow> 's pred \<Rightarrow> bool" where
  "non_inter F P = (\<forall> x \<in> (BV_progs F).(x \<notin> (FV P)))"

lemma non_inter_comp :
  assumes  "non_inter G P"
  shows "(FV P) \<subseteq> (set Vars - (BV_progs G))"
  by (meson DiffI FV_Vars assms non_inter_def subset_iff)

lemma non_inter_comp2: 
 assumes  "non_inter G P"
 shows "\<Union>\<^sub>S (FV P) \<le>  -(\<Union>\<^sub>S (BV_progs G))"
proof -
  have "(FV P) \<subseteq> (set Vars - (BV_progs G))"
    using non_inter_comp assms by blast
  then have "\<Union>\<^sub>S (FV P) \<le>  (\<Union>\<^sub>S  (set Vars - (BV_progs G)))"
    using scene_subset_union_lessthan
    by (metis Diff_subset dual_order.trans set_Vars_scene_space)
  thus ?thesis
    using  scene_minus 
    by (metis BV_is_vars)
qed

lemma   para_dl_non_inter5:
  assumes "((para_dl P Q) (s,w))"  "P (s, ps)" "partial_left w ps P"  "non_inter Q F"
  shows "(w \<approx>\<^sub>S ps on (\<Union>\<^sub>S (FV F))) "
proof -
  have "\<Union>\<^sub>S (FV F) \<le>  -(\<Union>\<^sub>S (BV_progs Q))"
    using assms(4) non_inter_comp2 by blast
  moreover have  "(w \<approx>\<^sub>S ps on ( (-\<Union>\<^sub>S (BV_progs Q)))) "
    using assms(1,2,3) para_dl_non_inter4 by blast
  ultimately show ?thesis
    by (metis Sup_scene_closed  idem_scene_space less_eq_scene_def
        scene_equiv_def scene_override_idem)
qed

lemma non_inter_thm:
  assumes "((para_dl P Q) (s,w))"  "P (s, ps)" "partial_left w ps P"  "non_inter Q F"
  shows "F w \<longleftrightarrow> F ps"
proof -
  have  "(w \<approx>\<^sub>S ps on (\<Union>\<^sub>S (FV F))) "
    using assms para_dl_non_inter5 by blast
  thus ?thesis 
    using coincidence_eff_term_prop_def scene_union_equiv
    by (metis (mono_tags, lifting) FV_Vars coin_eff_term_1 dual_order.trans
        set_Vars_scene_space)
qed

lemma "(para_dl skip skip) = skip"
  apply (simp add: skip_def para_dl_def BV_progs_def)
proof -
    have "{s \<in> set Vars. \<exists>a. \<not> (a::'a) \<approx>\<^sub>S a on s} \<subseteq> scene_space"
          by blast
     then show "(\<lambda>(s, s\<^sub>0). s\<^sub>0 = s \<oplus>\<^sub>S s on \<Union>\<^sub>S {x. x \<in> set Vars \<and> (\<exists>s\<^sub>0. \<not> s\<^sub>0 \<approx>\<^sub>S s\<^sub>0 on x)}) =
    (\<lambda>(s, s'). s' = s)"
     proof -
       have "{} = {s. s \<in> set Vars \<and> (\<exists>b. \<not> (b::'b) \<approx>\<^sub>S b on s)}"
         by simp
       then show ?thesis
         by (metis (no_types) Sup_scene_bot scene_override_unit)
     qed
qed
  
         

lemma parallel_intro:
  fixes s
  assumes "non_inter Q \<psi>"  " (P wlp \<psi> ) s "
  shows " ((para_dl P Q) wlp  \<psi>) s "
proof- 
  {
  fix w
  assume A: "(para_dl P Q) (s, w)" 
  obtain ps where ps1:"P (s, ps)" and ps2:"partial_left w ps P "
    using partial_paral_left A by blast
  have "\<psi> ps"
    using assms(2) ps1 wlp_pred_def
    by (smt (verit) SEXP_def expr_post post_def wlp_as_wprespec wprespec10)

  then have "\<psi> w"
    using non_inter_thm ps2 A ps1 assms(1) by blast
  }
  thus "?thesis"
    by (metis (mono_tags, lifting) SEXP_def expr_post post_def wlp_as_wprespec wprespec10)
qed

declare [[literal_variables=false]]

lemma
  assumes "H{P} C\<^sub>1 {Q}" "non_inter C\<^sub>2 Q"
  shows "H{P} (para_dl C\<^sub>1 C\<^sub>2) {Q}"
  by (smt (verit, ccfv_SIG) SEXP_def assms(1,2) hoare_rel_r_def non_inter_thm
      partial_paral_left)


lemma parallel_comm:
  assumes "(BV_progs P) \<inter> (BV_progs Q) = {}"
  shows "para_dl P Q = para_dl Q P"
proof -
  {fix s w
  have explicit_state:"para_dl P Q (s, w) = para_dl Q P (s, w)"
  proof -
    have "(para_dl P Q) (s,w) \<longrightarrow> (para_dl Q P) (s,w)"
    proof -
      {
        assume w1: "(para_dl P Q) (s,w)"
        obtain ps where ps1: "P (s, ps)" and ps2: "partial_left w ps P"
          using w1 partial_paral_left by blast
        obtain qs where qs1:"Q (s,qs)" and qs2:"partial_right w qs P"
          using w1 partial_paral_right by blast
        have "ps \<approx>\<^sub>S s on \<Union>\<^sub>S(BV_progs Q)"
          by (metis BV_is_vars Int_ac(3) ps1 assms bound_eff_3)
        moreover have "qs \<approx>\<^sub>S s on \<Union>\<^sub>S(BV_progs P)"
          by (metis BV_is_vars qs1 assms bound_eff_3)
        moreover have "w \<approx>\<^sub>S qs on \<Union>\<^sub>S(BV_progs Q)"
          using partial_paral_right_extra qs1 qs2 w1 assms by blast
        ultimately have "w = ps \<oplus>\<^sub>S qs on \<Union>\<^sub>S(BV_progs Q)"
          by (metis (no_types, lifting) ext ps2 w1 ps1
              para_dl_non_inter4 scene_equiv_def scene_override_commute
              scene_override_overshadow_right)
        then have "(para_dl Q P) (s,w)"
          using para_dl_def
          by (metis (mono_tags, lifting) curryD curry_case_prod ps1 qs1)
     }
      thus ?thesis
        by blast
    qed
    moreover have  "(para_dl Q P) (s,w) \<longrightarrow> (para_dl P Q) (s,w)"
    proof -
      {
        assume w1: "(para_dl Q P) (s,w)"
        obtain ps where ps1: "P (s, ps)" and ps2: "partial_right w ps Q"
          using w1 partial_paral_right by blast
        obtain qs where qs1:"Q (s,qs)" and qs2:"partial_left w qs Q"
          using w1 partial_paral_left by blast
        have "qs \<approx>\<^sub>S s on \<Union>\<^sub>S(BV_progs P)"
          by (metis BV_is_vars  qs1 assms bound_eff_3)
        moreover have "ps \<approx>\<^sub>S s on \<Union>\<^sub>S(BV_progs Q)"
          by (metis BV_is_vars assms bound_eff_3 inf_sup_aci(1) ps1)
        moreover have "w \<approx>\<^sub>S ps on \<Union>\<^sub>S(BV_progs P)"
          using partial_paral_right_extra ps1 ps2 w1 assms by blast
        ultimately have "w = qs \<oplus>\<^sub>S ps on \<Union>\<^sub>S(BV_progs P)"
          by (metis (no_types, lifting) ext qs2 w1 qs1
              para_dl_non_inter4 scene_equiv_def scene_override_commute
              scene_override_overshadow_right)
        then have "(para_dl P Q) (s,w)"
          using para_dl_def
          by (metis (mono_tags, lifting) curryD curry_case_prod ps1 qs1)
     }
      thus ?thesis
        by blast
    qed
    ultimately show ?thesis
      by blast
  qed
  }
  then show ?thesis
    apply auto
    done
qed


lemma parallel_intro_comm:
  fixes s
  assumes "non_inter P \<psi>" "(BV_progs P) \<inter> (BV_progs Q) = {}" "(Q wlp \<psi> ) s "
  shows " ((para_dl P Q) wlp  \<psi>) s "
proof- 
  have  " ((para_dl Q P) wlp  \<psi>) s "
    using assms parallel_intro by blast
  thus ?thesis
    using parallel_comm assms(2)
    by metis
qed

thm wlp_conj

lemma wlp_conj [wp]: "(P wlp (b \<and> c)) = ((P wlp b)\<^sub>e \<and> (P wlp c)\<^sub>e)"
  by pred_auto  

lemma parallel_decomp:
  fixes s
  assumes "non_inter P \<psi>2"  "non_inter Q \<psi>1" "(P wlp \<psi>1 ) s" "(Q wlp \<psi>2 ) s"  "(BV_progs P) \<inter> (BV_progs Q) = {}"
  shows " ((para_dl P Q) wlp (\<psi>1 \<and> \<psi>2)) s"
proof -
  have "((para_dl P Q) wlp  \<psi>1) s"
    using parallel_intro assms(2) assms(3) by blast
  moreover have  "((para_dl P Q) wlp  \<psi>2) s"
    using parallel_intro_comm assms(1) assms(4) assms(5) by blast
  ultimately show ?thesis
    by (simp add: wp, pred_simp)
qed


declare [[literal_variables=true]]

  


end