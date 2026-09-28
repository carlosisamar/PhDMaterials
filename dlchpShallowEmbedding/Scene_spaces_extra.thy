theory Scene_spaces_extra
  imports "Optics.Optics" "HOL-Algebra.Complete_Lattice"  "Scenes_extra"
begin

(* Add this to Optics *)
lemma  scene_lessthan_equiv:
  assumes "A \<in> scene_space" "B \<in> scene_space" "s \<approx>\<^sub>S s' on A" "B \<le> A" 
  shows " s \<approx>\<^sub>S s' on B"
  by (metis assms(2,3,4) idem_scene_space less_eq_scene_def scene_equiv_def
      scene_override_idem)

lemma squnion_to_union:
  assumes "S \<subseteq> scene_space" "s \<in> scene_space"
  shows " \<Union>\<^sub>S (insert s S) = s \<squnion>\<^sub>S \<Union>\<^sub>S S"
  by (simp add: Sup_scene_closed assms(1,2) sup_scene_union)

lemma scene_union_equiv:
  assumes "S \<subseteq> scene_space"
  shows "(\<forall> x \<in> S. s \<approx>\<^sub>S s' on x) \<longleftrightarrow> (s \<approx>\<^sub>S s' on (\<Union>\<^sub>S S))"
proof -
  have "finite S"
    using assms(1) finite_scene_space rev_finite_subset by auto
  thus ?thesis
    using assms
  proof (induct rule: finite_induct)
    case empty
    then show ?case
      by simp 
  next
    case (insert x F)
    moreover have "\<Union>\<^sub>S (insert x F) = x \<squnion>\<^sub>S \<Union>\<^sub>S F"
      using squnion_to_union
      by (metis insert.prems insert_subset)
    ultimately show ?case
      by (metis Sup_scene_closed insert_iff insert_subset scene_space_equiv_union)
  qed
qed

lemma scene_inter_lessthan:
  assumes "A \<in> scene_space" "B \<in> scene_space"
  shows  "(A \<sqinter>\<^sub>S B) \<le>  A"
  by (metis assms(1,2) scene_compl_subset_iff scene_demorgan2 scene_space_inter
      scene_space_ub scene_space_uminus)


lemma scene_composition_complement:
  assumes "C \<subseteq> scene_space"  "s =  B \<oplus>\<^sub>S A on (\<Union>\<^sub>S C)"
  shows "s \<approx>\<^sub>S B on (-(\<Union>\<^sub>S C))"
  by (simp add: assms(2) scene_equiv_def scene_override_commute)

lemma scene_minus:
  assumes "S \<subseteq> set Vars"
  shows "(\<Union>\<^sub>S(set Vars - S)) = -(\<Union>\<^sub>S S)"
  by (auto intro: scene_decomp_eq_transfer simp add: assms Sup_scene_decomp_Vars_transfer scene_space_uminus scene_decomp_uminus subset_trans)
  
lemma scene_minus2:
  assumes "x \<in> set Vars"
  shows "(\<Union>\<^sub>S(set Vars - {x})) =-x"
  by (metis assms bot.extremum insert_subsetI scene_minus scene_space.simps
      ss_clat.weak_sup_of_singleton)  


lemma scene_subset_union_lessthan:
  assumes "A \<subseteq> scene_space" "B \<subseteq> A"
  shows " ( \<Union>\<^sub>S B ) \<le>  ( \<Union>\<^sub>S A)"
  by (meson Sup_scene_closed Sup_scene_le assms(1,2) in_mono le_Sup_scene order.trans)
  

(* scene_override_commute )*)
    

lemma scene_intersect_equiv:
  assumes "A \<in> scene_space" "B \<in> scene_space" "s \<approx>\<^sub>S s' on A"
  shows  "s \<approx>\<^sub>S s' on (A  \<sqinter>\<^sub>S B)"
  by (meson assms(1,2,3) idem_scene_space scene_inter_lessthan scene_le_equiv scene_space_inter)
  
lemma scene_intersect_equiv_trans:
  assumes "A \<in> scene_space" "B \<in> scene_space" "s \<approx>\<^sub>S s' on A" "s' \<approx>\<^sub>S s'' on B"
  shows  "s \<approx>\<^sub>S s'' on (A  \<sqinter>\<^sub>S B)"
  by (metis (no_types, lifting) assms ext scene_equiv_def scene_inter_commute scene_intersect_equiv scene_override_overshadow_right)

lemma scene_subset_equiv:
  assumes "A \<subseteq> scene_space"  "s \<approx>\<^sub>S s' on (\<Union>\<^sub>S A)" "B \<subseteq> A"
  shows "s \<approx>\<^sub>S s' on (\<Union>\<^sub>S B)"
  by (metis Sup_scene_closed assms idem_scene_space scene_le_equiv scene_subset_union_lessthan)

lemma scene_neg_decomp:
  assumes "S \<subseteq> set Vars"
  shows "(\<forall> v \<in> (set Vars - S).( s \<approx>\<^sub>S s' on v)) \<longleftrightarrow> (s \<approx>\<^sub>S s' on -(\<Union>\<^sub>S S))"
proof -
  have "(set Vars - S) \<subseteq> scene_space"
    by blast
  thus ?thesis
    using scene_union_equiv scene_minus assms
    by metis
qed


lemma scene_agreement_decomp:
  assumes "A \<subseteq> set Vars" "B \<subseteq> set Vars" "w  \<approx>\<^sub>S s' on (\<Union>\<^sub>S (A - B))" "w  \<approx>\<^sub>S s on -(\<Union>\<^sub>S (A - B))"
  shows "w \<approx>\<^sub>S (s \<oplus>\<^sub>S s' on (\<Union>\<^sub>S A)) on -(\<Union>\<^sub>S B )"
proof -
  {
  fix v
  assume v1:"v \<in> set Vars" and v2:"v \<notin> B"
  have  "w \<approx>\<^sub>S (s \<oplus>\<^sub>S s' on (\<Union>\<^sub>S A)) on v"
    using assms v1 v2
    proof (cases "v \<in> A")
      case True
      then show ?thesis
        by (metis (lifting) ext DiffI Diff_subset assms(1,3) dual_order.trans idem_scene_Vars le_Sup_scene less_eq_scene_def mem_Vars_scene_space scene_equiv_def
            scene_equiv_sym scene_union_equiv v1 v2)
    next
      case False
      have v3:"v \<notin> (A-B)"
        using False by blast
      then have "w \<approx>\<^sub>S s on v"
        using assms(4)
        by (metis (no_types, lifting) DiffI Diff_subset assms(1) scene_neg_decomp subset_Un_eq
            sup.coboundedI1 v1)
      thus ?thesis
        using False
        by (smt (verit, del_insts) Diff_subset Sup_scene_is_foldr_scene assms(1) diff_shunt_var
            idem_scene_space insert_Diff insert_subset scene_equiv_def scene_minus scene_override_commute
            scene_space_foldr scene_subset_union_lessthan set_Vars_scene_space set_removeAll
            ss_clat.weak_sup_of_singleton subscene_eliminate subset_insert v1)
    qed   
  }
  thus ?thesis
    using scene_neg_decomp assms
    by (metis DiffE)
qed

lemma scene_agreement_decomp2:
  assumes "A \<subseteq> set Vars" "B \<subseteq> set Vars" "w  \<approx>\<^sub>S s' on (\<Union>\<^sub>S (A - B))" "w  \<approx>\<^sub>S s on -(\<Union>\<^sub>S (A \<union> B))"
  shows "w \<approx>\<^sub>S (s \<oplus>\<^sub>S s' on (\<Union>\<^sub>S A)) on -(\<Union>\<^sub>S B )"
proof -
  {
  fix v
  assume v1:"v \<in> set Vars" and v2:"v \<notin> B"
  have  "w \<approx>\<^sub>S (s \<oplus>\<^sub>S s' on (\<Union>\<^sub>S A)) on v"
    using assms v1 v2
    proof (cases "v \<in> A")
      case True
      then show ?thesis
        by (smt (verit, del_insts) Diff_iff Diff_subset assms(1,3) order.trans scene_composition_complement
            scene_equiv_def scene_minus scene_override_commute scene_override_overshadow_right
            scene_union_equiv set_Vars_scene_space uminus_scene_twice v2) 
    next
      case False
      have v3:"v \<in> set Vars - (A \<union> B)"
        using False v1 v2 assms(1,2) by blast
      then have "w \<approx>\<^sub>S s on v"
        by (meson assms(1,2,4) le_sup_iff scene_neg_decomp)
      thus ?thesis
        using False
        by (smt (verit, del_insts) Diff_subset Sup_scene_is_foldr_scene assms(1) diff_shunt_var
            idem_scene_space insert_Diff insert_subset scene_equiv_def scene_minus scene_override_commute
            scene_space_foldr scene_subset_union_lessthan set_Vars_scene_space set_removeAll
            ss_clat.weak_sup_of_singleton subscene_eliminate subset_insert v1)
    qed   
  }
  thus ?thesis
    using scene_neg_decomp assms
    by (metis DiffE)
qed


lemma scene_equiv_minus_sets:
  assumes "S \<subseteq> set Vars" "x \<in> S" "s \<approx>\<^sub>S s' on - \<Union>\<^sub>S S" "s \<approx>\<^sub>S s' on x"
  shows "s \<approx>\<^sub>S s' on - \<Union>\<^sub>S (S-{x})"
proof - 
  have "(\<forall> v \<in> (set Vars - S).( s \<approx>\<^sub>S s' on v))"
    using assms(1,3) scene_neg_decomp
    by blast
  then have  "(\<forall> v \<in> (set Vars - (S-{x})).( s \<approx>\<^sub>S s' on v))"
    using assms(2,4)
    by blast
  thus ?thesis
    using scene_neg_decomp
    by (metis assms(1,2) subset_insertI2 subset_insert_iff)
qed

lemma all_Vars_equiv_scene:
  assumes "set S \<subseteq> set Vars" "(\<forall> x \<in> set S.  s \<approx>\<^sub>S s' on x)"
  shows "s \<approx>\<^sub>S s' on \<Squnion>\<^sub>S S"
  using assms
  by (induct S)
     (auto simp add: scene_equiv_def, metis scene_override_union scene_override_unit scene_union_incompat)

lemma scene_space_put_preserved:
  assumes "vwb_lens x" "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> set Vars" "y \<noteq> \<lbrakk>x\<rbrakk>\<^sub>\<sim>" "y \<in> set Vars" "s \<approx>\<^sub>S s' on y"
  shows "put\<^bsub>x\<^esub> s foo \<approx>\<^sub>S s' on y"
  by (metis assms indep_Vars pairwiseD scene_indeps_def scene_put_preserved)




lemma scene_union_put_preserved:
  assumes "vwb_lens x" "S \<subseteq> set Vars" "s \<approx>\<^sub>S s' on \<Union>\<^sub>S S" "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> set Vars"
  shows "put\<^bsub>x\<^esub> s foo \<approx>\<^sub>S s' on  \<Union>\<^sub>S (S-{\<lbrakk>x\<rbrakk>\<^sub>\<sim>})"
proof (cases "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> S")
  case True
  then show ?thesis
  proof -
  {
      fix y
      assume asy1:"y \<noteq> \<lbrakk>x\<rbrakk>\<^sub>\<sim>" and asy2:"y \<in> S"
      have "s \<approx>\<^sub>S s' on y"
        using asy2 assms(2,3) scene_union_equiv set_Vars_scene_space
        by blast
      then have "put\<^bsub>x\<^esub> s foo \<approx>\<^sub>S s' on y"
        using assms(1,2,3) scene_space_put_preserved True
        by (metis asy1 asy2 subset_eq)
    }
  thus ?thesis
    using scene_union_equiv assms(2) set_Vars_scene_space
    by (smt (verit, del_insts) DiffE True dual_order.trans insert_Diff insert_subset
        singletonI)
qed
next
  case False
  then show ?thesis
  proof -
  {
      fix y
      assume asy1:"y \<in> S"
      have "s \<approx>\<^sub>S s' on y"
        using asy1 assms(2,3) scene_union_equiv set_Vars_scene_space
        by blast
      moreover have "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<bowtie>\<^sub>S y"
        using assms(2,4) False
        by (metis asy1 indep_Vars pairwiseD scene_indeps_def ss_clat.elem_subsetD)
      ultimately have "put\<^bsub>x\<^esub> s foo \<approx>\<^sub>S s' on y"
        by (meson assms(1) scene_indep_sym scene_put_preserved)
    }
    moreover have "S - {\<lbrakk>x\<rbrakk>\<^sub>\<sim>}= S"
      using False
      by blast
    ultimately show ?thesis
    using scene_union_equiv assms(2) set_Vars_scene_space
    by (metis dual_order.trans)
qed
  
qed

lemma scene_union_neg_put_preserved:
  assumes "vwb_lens x" "S \<subseteq> set Vars" "s \<approx>\<^sub>S s' on -\<Union>\<^sub>S S" "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> set Vars"
  shows "put\<^bsub>x\<^esub> s foo \<approx>\<^sub>S s' on  - \<Union>\<^sub>S (S \<union>{\<lbrakk>x\<rbrakk>\<^sub>\<sim>})"
proof (cases "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<in> S")
  case True
  then show ?thesis
  proof -
  {
      fix y
      assume asy1:"y \<in> (set Vars - S)"
      have "(s \<approx>\<^sub>S s' on y)"
        using asy1 assms(2,3) scene_neg_decomp 
        by blast
      then have "put\<^bsub>x\<^esub> s foo \<approx>\<^sub>S s' on y"
        using scene_space_put_preserved True asy1 assms(1,2)
        by (metis Diff_iff assms(4))
    }
  thus ?thesis
    using scene_neg_decomp True
    by (metis Un_insert_right assms(2) insert_absorb sup_bot_right)
qed
next
  case False
  then show ?thesis
  proof -
  {
      fix y
      assume asy1:"y \<in> (set Vars - S)" and asy2: "y \<noteq> \<lbrakk>x\<rbrakk>\<^sub>\<sim>"
      have "s \<approx>\<^sub>S s' on y"
        using asy1 assms(3) scene_neg_decomp
        using assms(2) by blast
      moreover have "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<bowtie>\<^sub>S y"
        using assms(2,4) asy2 asy1
        by (metis Diff_iff indep_Vars pairwiseD scene_indeps_def)
      ultimately have "put\<^bsub>x\<^esub> s foo \<approx>\<^sub>S s' on y"
        by (meson assms(1) scene_indep_sym scene_put_preserved)
    }
    then show ?thesis
    using scene_neg_decomp
    by (metis (no_types, lifting) Diff_iff Un_insert_right assms(2,4) insert_iff insert_subset
        sup_bot_right)
qed
qed

lemma lens_preserve_vars_comp_right:
  assumes "get\<^bsub>v\<^esub> w = get\<^bsub>v\<^esub> (s \<oplus>\<^sub>S s' on \<Union>\<^sub>S S)" "get\<^bsub>v\<^esub> s = get\<^bsub>v\<^esub> s'" "vwb_lens v" "\<lbrakk>v\<rbrakk>\<^sub>\<sim> \<in> set Vars" "S \<subseteq> set Vars"
  shows  "get\<^bsub>v\<^esub> w = get\<^bsub>v\<^esub> s'"
  by (metis (no_types, lifting) Diff_partition UnE assms(1,2,3,4,5) get_scene_override_le
      le_Sup_scene le_sup_iff scene_minus scene_override_commute set_Vars_scene_space)


lemma empty_neg_is_vars: "- \<Union>\<^sub>S {} = \<Union>\<^sub>S (set Vars)"
  by (simp add: Sup_scene_is_foldr_scene top_scene_eq) 

lemma equiv_vars_is_eq:
  assumes "s \<approx>\<^sub>S s' on  \<Union>\<^sub>S (set Vars)"
  shows "s = s'"
  by (metis assms empty_iff empty_neg_is_vars empty_subsetI scene_equiv_def
      scene_override_commute scene_union_equiv)

lemma scene_subset_agreement:
  assumes "S\<^sub>1 \<subseteq> set Vars" "S\<^sub>2 \<subseteq> S\<^sub>1" "s \<approx>\<^sub>S s' on \<Union>\<^sub>S S\<^sub>1"  "s'' \<approx>\<^sub>S s' on \<Union>\<^sub>S S\<^sub>2"
  shows "s \<approx>\<^sub>S s'' on \<Union>\<^sub>S S\<^sub>2"
proof -
  have "s \<approx>\<^sub>S s' on \<Union>\<^sub>S S\<^sub>2"
    using assms(1,2,3)
    by (meson dual_order.trans scene_subset_equiv set_Vars_scene_space)
  then show ?thesis
    by (metis assms(4) scene_equiv_def scene_override_overshadow_right)
qed

lemma scene_comm:
  assumes "s \<approx>\<^sub>S s' on \<Union>\<^sub>S S"
  shows "s' \<approx>\<^sub>S s on \<Union>\<^sub>S S"
  by (metis Sup_scene_closed assms idem_scene_space scene_equiv_sym)
 
lemma scene_agreement_neg_comp:
  assumes  "s \<approx>\<^sub>S s' on \<Union>\<^sub>S S" "s \<approx>\<^sub>S s' on -\<Union>\<^sub>S (S \<union> S')" "S \<subseteq> set Vars" "S' \<subseteq> set Vars"
  shows "s \<approx>\<^sub>S s' on -\<Union>\<^sub>S S'"
proof -
  {
    fix x
    assume a1:"x \<in> (set Vars - S')"
    have "s \<approx>\<^sub>S s' on x"
      proof(cases "x \<in> S")
        case True
        then show ?thesis
          using assms(1)
          by (meson assms(3) order_trans scene_union_equiv set_Vars_scene_space)
      next
        case False
        then show ?thesis
          using assms(2)
          by (metis Diff_iff Un_iff a1 assms(3,4) le_sup_iff
              scene_neg_decomp)
      qed
    }
    then show ?thesis
      using assms(4) scene_neg_decomp by blast
  qed

lemma scene_agree_single_var:
  assumes "S \<subseteq> set Vars" "x \<in> set Vars" "s \<approx>\<^sub>S s\<^sub>1 on \<Union>\<^sub>S S" "s \<approx>\<^sub>S s\<^sub>2 on -\<Union>\<^sub>S S" "s' \<approx>\<^sub>S s\<^sub>1 on \<Union>\<^sub>S (insert x S)" "s' \<approx>\<^sub>S s\<^sub>2 on -\<Union>\<^sub>S (insert x S)"
  shows "s \<approx>\<^sub>S s' on -x"
proof -
  have h1:"(insert x S) \<subseteq> set Vars"
    using assms(1,2) by blast
  have "s \<approx>\<^sub>S s' on \<Union>\<^sub>S S"
    using assms(1) assms(2) assms(3) assms(5) scene_subset_agreement h1
    by (metis dual_order.refl subset_insertI)
  moreover have "s \<approx>\<^sub>S s' on -\<Union>\<^sub>S (insert x S)"
    proof -
      have "s \<approx>\<^sub>S s\<^sub>2 on \<Union>\<^sub>S (set Vars -S)"
        by (simp add: assms(1,4) scene_minus)
      moreover have  "s' \<approx>\<^sub>S s\<^sub>2 on \<Union>\<^sub>S (set Vars - S - {x})"
        by (metis Diff_insert assms(6) h1 scene_minus)
      ultimately have "s \<approx>\<^sub>S s' on  \<Union>\<^sub>S (set Vars - S - {x})"
        using assms(1) assms(2) scene_subset_agreement
        by (metis (no_types, lifting) Diff_subset)
      thus ?thesis
        by (metis Diff_insert h1 scene_minus)
    qed 
  ultimately show ?thesis
    using  scene_agreement_neg_comp
    by (metis assms(2) h1 insert_is_Un le_supE scene_space_class.scene_space.Vars_scene_space
        ss_clat.weak_sup_of_singleton sup.commute)
qed


end