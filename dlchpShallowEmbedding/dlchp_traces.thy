theory dlchp_traces
  imports  "dlCHP_alpha"
begin

unbundle UTP_Syntax

notation lens_get ("(_<_>)" [76, 0] 75)

class channel =
  fixes chan_of :: "'a \<Rightarrow> 'a set"
  assumes chan_of_self: "x \<in> chan_of x"
  and finite_chans: "finite (range chan_of)" 

abbreviation "chan_univ \<equiv> range chan_of"

(* set of possible traces of program P *)
definition traces ::  "('s, 'e) dlCHP_rel => ('e \<times> real) list set" where
  "traces P = {tr<s'> - tr<s> | s s'. P (s, s')}"

(* set of possible traces of program P with initial state s *)
definition traces_from_state :: "('s, 'e) dlCHP_rel => ('s, 'e) dlCHP_alpha \<Rightarrow> ('e \<times> real) list set" where
   "traces_from_state P s = {tr<s'> - tr<s> | s'. P (s, s')}"

definition trace_state_conc :: " ('s, 'e) dlCHP_alpha \<Rightarrow> ('e \<times> real) list \<Rightarrow> ('s, 'e) dlCHP_alpha" where
  "trace_state_conc s t = put\<^bsub>tr\<^esub> s (tr<s> @ t) "

(* set of events that happen in a trace t *)
definition events_from_trace :: " ('e \<times> real) list \<Rightarrow> 'e set" where
  "events_from_trace t = set (map fst t) "

definition events_from_traces_set ::  "('e \<times> real) list set  \<Rightarrow> 'e set" where
   "events_from_traces_set ts = \<Union> {events_from_trace(t) |t. t \<in> ts} "

definition channels_from_trace :: "('e::channel \<times> real) list \<Rightarrow> 'e set set" where
  "channels_from_trace t = set (map chan_of (map fst t))"

definition trace_restriction_channels :: "('e::channel \<times> real) list \<Rightarrow> 'e set set \<Rightarrow> ('e::channel \<times> real) list" where
  "trace_restriction_channels t CNP = filter (\<lambda>x :: ('e \<times> real).\<exists> C \<in> CNP. chan_of (fst x) =  C) t"

definition trace_restriction_channel :: "('e::channel \<times> real) list \<Rightarrow> 'e set \<Rightarrow> ('e::channel \<times> real) list" where
  "trace_restriction_channel t ch  =  filter (\<lambda>x :: ('e \<times> real). chan_of (fst x) =  ch) t "

lemma trace_rest_channels_idem :
  "trace_restriction_channels t ch  = trace_restriction_channels (trace_restriction_channels t ch ) ch"
  apply(simp add: trace_restriction_channels_def)
  done

lemma trace_rest_exist:
  assumes "ch \<in> channels_from_trace t"
  shows "trace_restriction_channel t ch \<noteq> []"
  by (smt (verit) assms channels_from_trace_def filter_empty_conv imageE list.set_map
      trace_restriction_channel_def)



lemma trace_rest_subset:
  assumes "channels_from_trace t \<subseteq> chs"
  shows "trace_restriction_channels t chs = t"
  by (metis (no_types, lifting) ext assms channels_from_trace_def filter_id_conv image_eqI
      list.set_map subset_eq trace_restriction_channels_def)

lemma trace_rest_channels_comm :
  assumes "trace_restriction_channels t chs1 = t'" "trace_restriction_channels t chs2 = t'"
  shows "trace_restriction_channels t (chs1 \<inter> chs2) = t'"
  using assms
  apply(simp add: trace_restriction_channels_def)
  by (metis filter_filter trace_rest_channels_idem trace_restriction_channels_def)

lemma trace_rest_channels_comm2 :
  "trace_restriction_channels (trace_restriction_channels t chs1) chs2 = trace_restriction_channels (trace_restriction_channels t chs2) chs1"
  apply(simp add: trace_restriction_channels_def)
  by meson


lemma trace_rest_channels_dist :
  shows "trace_restriction_channels (trace_restriction_channels s chs1) chs2 = trace_restriction_channels s (chs1 \<inter> chs2)"
  by(simp add: trace_restriction_channels_def)


lemma trace_rest_channels_id :
   "trace_restriction_channels t chan_univ = t"
  by(simp add: trace_restriction_channels_def)

lemma trace_rest_restricts: "channels_from_trace (trace_restriction_channels t chs) \<subseteq> channels_from_trace t"
  apply(simp add: channels_from_trace_def trace_restriction_channels_def)
  apply(auto)
  done

lemma trace_rest_channels: "channels_from_trace (trace_restriction_channels t chs) \<subseteq> chs"
  apply(simp add: channels_from_trace_def trace_restriction_channels_def)
  apply(auto)
  done

lemma trace_res_empty:
  assumes "chs \<subseteq> chan_univ"
  shows "trace_restriction_channels t chs = [] \<longleftrightarrow> (\<forall> ch \<in> chs. (trace_restriction_channel t ch = []))"
  apply(simp add: trace_restriction_channels_def trace_restriction_channel_def)
  apply(pred_auto)
   apply (metis (lifting) filter_empty_conv)
  by (metis (lifting) filter_empty_conv)

definition trace_restriction_state :: "('s, 'e::channel) dlCHP_alpha \<Rightarrow> 'e set set \<Rightarrow> ('s, 'e) dlCHP_alpha" where
 "trace_restriction_state s chs = (put\<^bsub>tr\<^esub> s (trace_restriction_channels (tr<s>) chs))  "


lemma state_conservation_rest_trace :
  assumes "s' = trace_restriction_state s chs"
  shows "s \<approx>\<^sub>S s' on -(\<lbrakk>tr\<rbrakk>\<^sub>\<sim>)"
  by (metis assms put_scene_override_le scene_equiv_def scene_override_commute
      scene_override_idem subscene_refl tr_vwb_lens trace_restriction_state_def
      vwb_impl_idem_scene)  

lemma trace_rest_state_idem :
  "trace_restriction_state s chs = trace_restriction_state (trace_restriction_state s chs) chs "
  apply(simp add: trace_restriction_state_def)
  using trace_rest_channels_idem
  by metis

lemma trace_rest_state_comm :
  assumes "trace_restriction_state s chs1 = s'" "trace_restriction_state s chs2 = s'"
  shows "trace_restriction_state s (chs1 \<inter> chs2) = s'"
  using assms
  apply(simp add: trace_restriction_state_def)
  by (metis mwb_lens_def tr_vwb_lens trace_rest_channels_comm vwb_lens_mwb
      weak_lens.put_get)

lemma trace_rest_state_dist :
  shows "trace_restriction_state (trace_restriction_state s chs1) chs2 = trace_restriction_state s (chs1 \<inter> chs2)"
  apply(simp add: trace_restriction_state_def)
  by (simp add: trace_rest_channels_dist)

lemma trace_rest_state_id :
   "trace_restriction_state t chan_univ = t"
  by(simp add: trace_restriction_state_def trace_rest_channels_id)

definition CN :: "('s, 'e::channel) dlCHP_rel \<Rightarrow> 'e set set" where
"CN P =  {ch \<in> chan_univ. \<exists> t \<in> traces P. ch \<in> (channels_from_trace t)}"

definition CN_term :: "('a, 's::scene_space, 'e::channel) dlCHP_expr \<Rightarrow> 'e set set" where
  "CN_term T =  {ch \<in> chan_univ. (\<exists> s1 s2. trace_restriction_state s1 (chan_univ-{ch}) = trace_restriction_state s2 (chan_univ-{ch})  \<and> T s1 \<noteq> T s2 ) } "

lemma cn_term_dist :
  assumes "ch1 \<in> chan_univ - CN_term T" "ch2 \<in> chan_univ -CN_term T"
  shows "T s = T (trace_restriction_state s (chan_univ - {ch1, ch2}))"
proof -
  have f0:"\<forall> ch \<in> chan_univ.   ch \<notin> (CN_term T) \<longrightarrow> (\<forall> s1 s2.
         trace_restriction_state s1 (chan_univ - {ch}) \<noteq>
         trace_restriction_state s2 (chan_univ - {ch}) \<or>
         T s1 = T s2)"
    using CN_term_def by blast
  have "T s = T (trace_restriction_state s (chan_univ - {ch1}))"
    using f0 assms(1) trace_rest_state_idem by blast
  moreover have "T s = T (trace_restriction_state s (chan_univ - {ch2}))"
    using f0 assms(2) trace_rest_state_idem by blast
  moreover have "(chan_univ - {ch1}) \<inter>  (chan_univ - {ch2}) = (chan_univ - {ch1, ch2})"
    by blast
  ultimately show ?thesis
    using trace_rest_state_dist assms f0
    by (metis (no_types, lifting) DiffE Int_absorb)
qed

lemma cn_term_dist_set :
  assumes "chs \<subseteq> (chan_univ - CN_term T)"
  shows "T s = T (trace_restriction_state s (chan_univ - chs))"
proof -
  have "finite chs"
    by (meson assms finite_Diff finite_chans rev_finite_subset)
  thus ?thesis
    using assms
  proof (induct rule:finite_induct)
    case empty
    then show ?case 
      using trace_rest_state_id by (metis Diff_empty)
  next
    case (insert x F)
    have "(chan_univ - insert x F) = (chan_univ -  {x} ) \<inter> (chan_univ - F)"
      by blast
    then show ?case
      using cn_term_dist
      by (smt (verit, ccfv_SIG) Diff_Un Int_absorb Int_commute insert.hyps(3) insert.prems
          insert_is_Un insert_subset trace_rest_state_dist)
  qed
qed
  
(* restriction of trace t to program P, defined as communication events in t with a channel in P  *)
definition trace_restriction_prog ::  "('e::channel \<times> real) list \<Rightarrow> ('s, 'e) dlCHP_rel \<Rightarrow> ('e \<times> real) list "    where 
  "trace_restriction_prog t P = trace_restriction_channels t (CN P)  "

(*symbol \<down> is already in use so using \<downharpoonright> instead*)
syntax "_trace_restriction_prog" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("(_\<downharpoonright>_)" [75,75])
translations "t\<downharpoonright>P" ==  "CONST trace_restriction_prog t P"

 

lemma trace_res_dist:  "(t1 @ t2)\<downharpoonright>P = (t1\<downharpoonright>P) @ (t2\<downharpoonright>P)"
  apply(simp add: trace_restriction_prog_def trace_restriction_channels_def)
  done

lemma trace_rest_contr:
  assumes "P (s, s')"
  shows " (tr<s'> - tr<s>)\<downharpoonright>P = tr<s'> - tr<s>"
  apply(simp add: trace_restriction_prog_def trace_restriction_channels_def CN_def events_from_trace_def traces_def)
  by (metis (mono_tags, lifting) assms channels_from_trace_def filter_True imageI
      list.set_map)

  
lemma trace_rest_fixed_point: "t\<downharpoonright>P = ((t\<downharpoonright>P)\<downharpoonright>P)"
  using trace_restriction_prog_def trace_restriction_channels_def
  by (metis (mono_tags, lifting) filter_cong filter_filter) 


lemma trace_res_events:
  assumes "P is R1" "P (s, s')"
  shows "(tr<s'>)\<downharpoonright>P = ((tr<s>)\<downharpoonright>P) @ (tr<s'> - tr<s>)"
proof -
  have "(R1 P) (s, s')"
    by (metis Healthy_def assms(1,2))
  then have "tr<s> \<le> tr<s'>"
    by (pred_simp)
  hence "tr<s'> = tr<s> @ (tr<s'> - tr<s>)"
    by (metis Prefix_Order.prefixE append_minus)
  then have " (tr<s'>)\<downharpoonright>P =  ((tr<s>)\<downharpoonright>P) @ ( (tr<s'> - tr<s>)\<downharpoonright>P)"
    by (metis trace_res_dist)
  thus ?thesis
    by (simp add: assms(2) trace_rest_contr)
qed

lemma channels_from_trace_cn: "channels_from_trace (t\<downharpoonright>P) \<subseteq> CN P"
  apply(simp add: channels_from_trace_def CN_def trace_restriction_prog_def)
  apply(auto)
  by (smt (verit) filter_id_conv mem_Collect_eq prod.sel(1) trace_rest_channels_idem
      trace_restriction_channels_def)


lemma restriction_prefix:
  assumes "trace_restriction_channels (t1-t) chs = trace_restriction_channels (t2-t) chs" "t\<le>t1" "t\<le>t2"
  shows "trace_restriction_channels (t1) chs = trace_restriction_channels (t2) chs"
  using assms
  apply(simp add: trace_restriction_channels_def)
  using Prefix_Order.prefixE append_minus filter_append by fastforce

lemma channels_from_trace_transit:
  assumes "channels_from_trace (t :: ('e::channel \<times> real) list) \<subseteq> (chs:: 'e set set)" "(t' :: ('e \<times> real) list)\<le> t"
  shows "channels_from_trace t' \<subseteq> chs"
proof-
  have "(map fst t') \<le> (map fst t)"
    using assms(2)
    by fastforce
  then have " (map chan_of (map fst t')) \<le>  (map chan_of (map fst t))"
    by fastforce
  then have "(set (map chan_of (map fst t'))) \<subseteq> set (map chan_of (map fst t))"
    by fastforce
  then have "channels_from_trace t' \<subseteq> channels_from_trace t"
    using channels_from_trace_def by blast
  then show ?thesis
    using assms(1) by order
qed


definition trace_state_comp::"('e::channel \<times> real) list \<Rightarrow> ('s, 'e) dlCHP_alpha \<Rightarrow> ('e::channel \<times> real) list \<Rightarrow> ('s, 'e) dlCHP_alpha \<Rightarrow> bool " where
 "trace_state_comp t1 s1 t2 s2 = ((t1 = t2 \<and> s1 = s2) \<or> (t1 \<le> t2 \<and> wait<s1> )) "

syntax "_trace_state_comp" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("'(_, _') \<preceq> '(_, _')" [0, 0, 0, 0] 75)
translations "(t1,s1) \<preceq> (t2,s2)" ==  "CONST trace_state_comp t1 s1 t2 s2"



lemma trace_strict_prefix_wait:
  fixes t1 t2 :: "('e::channel \<times> real) list"
  assumes "t1<t2" "channels_from_trace t1 \<subseteq> chs1 \<union> chs2" "channels_from_trace t2 \<subseteq> chs1 \<union> chs2"
  shows "trace_restriction_channels t1 chs1 < trace_restriction_channels t2 chs1 \<or> trace_restriction_channels t1 chs2 < trace_restriction_channels t2 chs2"
proof -
  obtain x  where ax1:"x \<noteq> []" and ax2:"t2 = t1@x"
    using assms(1)
    by (meson Prefix_Order.strict_prefixE' list.discI)
  have  l1:"channels_from_trace x \<subseteq> chs1 \<union> chs2"
    using ax2
    by (metis assms(3) channels_from_trace_def le_sup_iff map_append set_append)
  then show ?thesis
  proof (cases "channels_from_trace x \<subseteq> chs1")
    case True
    have "trace_restriction_channels t1 chs1 < trace_restriction_channels t2 chs1"
      using ax2 True
      by (metis Prefix_Order.prefixI Prefix_Order.same_prefix_nil ax1 filter_append less_list_def
          trace_rest_subset trace_restriction_channels_def)
    then show ?thesis
      by blast 
  next
    case False
    have "trace_restriction_channels x chs2 \<noteq> []"
      using l1 False
        apply (simp add:trace_restriction_channels_def channels_from_trace_def)
      by (smt (verit) UnE filter_empty_conv image_subset_iff)
    then have "trace_restriction_channels t1 chs2 < trace_restriction_channels t2 chs2"
      using ax2
      by (simp add: less_list_def trace_restriction_channels_def)
    then show ?thesis 
      by blast
  qed
qed

lemma trace_rest_dist_ext:
  assumes "tp \<le> trace_restriction_channels t chs"
  shows "\<exists> t' \<le> t. tp = trace_restriction_channels t' chs"
  using assms
  apply(simp add: trace_restriction_channels_def)
  proof (induction t arbitrary: tp)
    case Nil
    then show ?case by auto
  next
    case (Cons a t)
    then show ?case
    proof (cases " chan_of (fst a) \<in> chs")
      case True
      then show ?thesis
        by (metis (no_types, lifting) Cons.IH Cons.prems Prefix_Order.prefix_Cons
            filter.simps(1,2)) 
    next
      case False
      then show ?thesis
        by (metis (no_types, lifting) Cons.IH Cons.prems Prefix_Order.Cons_prefix_Cons
            filter.simps(2)) 
    qed
  qed

(*lemma list_decomp_traces:
  fixes l:: "'a list"
  assumes "l0 \<le> l1" "l1 \<le> l2" "l \<le> l2-l0"
  shows "l \<le> l1-l0 \<or> (\<exists> l'. l' \<le> l2-l1 \<and> l=l1@l')" *)

lemma empty_cn:
  assumes "CN P = {}" "P(s,s')" "P is R1"
  shows "tr<s'> = tr<s>"
proof -
  have "tr<s> \<le> tr<s'>"
    using assms(2,3) Healthy_def R1_def
    by (metis (no_types, lifting) SEXP_def conj_pred_def get_post get_pre inf_apply
                          inf_bool_def)
  moreover have "tr<s'> -tr<s> \<in> traces P"
    using assms(2) traces_def
    by auto 
  moreover {
    fix t
    assume t1:"t \<in> traces P"
    have "\<nexists> ch. ch \<in> channels_from_trace t"
      using assms(1) CN_def
      by (metis (mono_tags, lifting) empty_Collect_eq subset_iff t1 trace_rest_channels
          trace_rest_channels_id)
    then have "t = []"
      using channels_from_trace_def
      by (metis Nil_is_map_conv all_not_in_conv set_empty2)
  }
  ultimately  show ?thesis by auto
qed
    
end