theory Scenes_extra
  imports "Optics.Optics"
begin

lemma 
  assumes "vwb_lens x" "s \<approx>\<^sub>S s' on (- \<lbrakk>x\<rbrakk>\<^sub>\<sim>)"
  shows "s \<simeq>\<^bsub>x\<^esub> s'"
  by (metis assms(1,2) idem_scene_uminus lens_obs_eq_as_override lens_scene_override scene_equiv_def
      scene_equiv_sym scene_override_commute vwb_impl_idem_scene vwb_lens_def)

lemma scene_equiv_get_eq:
  assumes "vwb_lens x" 
  shows "s \<approx>\<^sub>S s' on \<lbrakk>x\<rbrakk>\<^sub>\<sim> \<longleftrightarrow> get\<^bsub>x\<^esub> s = get\<^bsub>x\<^esub> s'"
  by (metis assms get_scene_override_le lens_override_def lens_override_idem lens_scene_override
      scene_equiv_def subscene_refl vwb_lens_def)


lemma scene_put_preserved:
  assumes "vwb_lens x" "y \<bowtie>\<^sub>S \<lbrakk>x\<rbrakk>\<^sub>\<sim>" "s \<approx>\<^sub>S s' on y"
  shows "put\<^bsub>x\<^esub> s foo \<approx>\<^sub>S s' on y"
proof -
  from assms(3) have a: "s \<oplus>\<^sub>S s' on y = s"
    by (simp add: scene_equiv_def)
  hence "(put\<^bsub>x\<^esub> s foo) \<oplus>\<^sub>S s on y = put\<^bsub>x\<^esub> s foo"
    by (metis assms(1,2) put_scene_override_indep scene_indep_sym scene_override_overshadow_right)
  with a show ?thesis
    by (metis scene_equiv_def scene_override_overshadow_right)
qed


lemma lens_scene_comp_eq [simp]:
  assumes "vwb_lens x" "vwb_lens y" "x \<subseteq>\<^sub>L y"
  shows "\<lbrakk>x /\<^sub>L y\<rbrakk>\<^sub>\<sim> ;\<^sub>S y = \<lbrakk>x\<rbrakk>\<^sub>\<sim>"
  by (simp add: assms(1,2,3) lens_scene_quotient scene_quotient_comp scene_space_lemmas(9))

lemma scene_comp_quot_eq [simp]:
  assumes "vwb_lens y" "vwb_lens z" "y \<subseteq>\<^sub>L z"
  shows "x ;\<^sub>S (y /\<^sub>L z) ;\<^sub>S z = x ;\<^sub>S y"
  by (simp add: assms(1,2,3) lens_quotient_comp lens_quotient_vwb scene_comp_assoc)

lemma scene_lens_indep_neq:
  fixes x :: "'a::two \<Longrightarrow> 's" and y :: "'b::two \<Longrightarrow> 's"
  assumes "vwb_lens x" "vwb_lens y" "x \<bowtie> y"
  shows "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<noteq> \<lbrakk>y\<rbrakk>\<^sub>\<sim>"
  using assms(1,2,3) indep_eff_implies_not_equiv lens_equiv_scene vwb_lens_wb by blast 


lemma lens_put_get_preserved_indep:
  assumes "vwb_lens x" "vwb_lens y" "x \<bowtie> y"   "get\<^bsub>x\<^esub> s =get\<^bsub>x\<^esub> ( put\<^bsub>y\<^esub> s' foo)"
  shows "get\<^bsub>x\<^esub> s = get\<^bsub>x\<^esub> s'"
  using assms(3,4) by auto

lemma lens_put_get_preserved_indep2:
  assumes  "x \<bowtie> y"
  shows "get\<^bsub>x\<^esub> s = get\<^bsub>x\<^esub> ( put\<^bsub>y\<^esub> s foo)"
  using assms(1) by force

end