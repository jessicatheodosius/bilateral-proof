theory Example imports Soundness begin

section \<open>Example: Distributed Counter\<close>

text \<open>
  This is the mechanisation of the safety property proof of the distributed counter example
  from the paper.
\<close>

subsection \<open>Distributed Counter Formalisation\<close>

definition Assign :: "bexp \<Rightarrow> vname \<Rightarrow> (state \<Rightarrow> nat) \<Rightarrow> state_rel" where
  "Assign G n v \<equiv> {(s, s'). G s \<and> s' = s(n := v s)}"

definition dist_ctr_com :: "vname \<Rightarrow> vname \<Rightarrow> vname \<Rightarrow> com" where
  "dist_ctr_com ctr old new \<equiv>
    \<lbrace>true\<rbrace>
    ACTION {(s, s'). s' = (s(old := 0))(new := 0)};;
    \<lbrace>true\<rbrace> \<lbrace>true\<rbrace>
    WHILE true true DO
      (\<lbrace>true\<rbrace>
      ACTION (Assign true new (\<lambda>s. s old + 1));;
      \<lbrace>\<lambda>s. s new = s old + 1\<rbrace>
      ACTION 
        ( Assign (\<lambda>s. s ctr = s old) ctr (\<lambda>s. s new)
        \<union> Assign (\<lambda>s. s ctr \<noteq> s old) old (\<lambda>s. s ctr)))"

definition dist_ctr_com1 where
  "dist_ctr_com1 \<equiv> dist_ctr_com ''ctr'' ''old1'' ''new1''"

definition dist_ctr_com2 where
  "dist_ctr_com2 \<equiv> dist_ctr_com ''ctr'' ''old2'' ''new2''"

abbreviation dist_ctr where
  "dist_ctr \<equiv> PARALLEL [dist_ctr_com1, dist_ctr_com2] [true, true]"


subsection \<open>Safety Property Proof\<close>

lemma dist_ctr_com1_derivable:
  "\<turnstile> {true} dist_ctr_com1 {true}"
  apply (simp add: dist_ctr_com1_def dist_ctr_com_def)
  apply (rule b_semi; simp)+
   apply (rule b_action; simp add: true_def)
  apply (rule b_while; simp)
  apply (rule b_semi; simp)
  by (rule b_action; simp add: Assign_def true_def)+

lemma dist_ctr_com2_derivable:
  "\<turnstile> {true} dist_ctr_com2 {true}"
  apply (simp add: dist_ctr_com2_def dist_ctr_com_def)
  apply (rule b_semi; simp)+
   apply (rule b_action; simp add: true_def)
  apply (rule b_while; simp)
  apply (rule b_semi; simp)
  by (rule b_action; simp add: Assign_def true_def)+

lemma is_com_stable_dist_ctr_com12:
  "is_com_stable dist_ctr_com1 dist_ctr_com2"
  by (auto simp: is_com_stable_def is_ann_stable_def dist_ctr_com1_def dist_ctr_com2_def dist_ctr_com_def true_def Assign_def)

lemma is_com_stable_dist_ctr_com21:
  "is_com_stable dist_ctr_com2 dist_ctr_com1"
  by (auto simp: is_com_stable_def is_ann_stable_def dist_ctr_com1_def dist_ctr_com2_def dist_ctr_com_def true_def Assign_def)

lemma is_ann_stable_true:
  "is_ann_stable true f"
  by (simp add: is_ann_stable_def true_def)

lemma valid_ann_dist_ctr_com:
  "valid_ann [dist_ctr_com1, dist_ctr_com2] [true, true]"
  apply (simp add: valid_ann_def valid_ann'_def)
  apply clarsimp
  apply (case_tac i; simp add: is_ann_stable_true)
   apply (simp add: is_com_stable_dist_ctr_com12)
  apply (case_tac j; simp)
  by (simp add: is_com_stable_dist_ctr_com21)

lemma com_pre_dist_ctr_com1:
  "com_pre dist_ctr_com1 = true"
  by (simp add: dist_ctr_com1_def dist_ctr_com_def)

lemma com_pre_dist_ctr_com2:
  "com_pre dist_ctr_com2 = true"
  by (simp add: dist_ctr_com2_def dist_ctr_com_def)

lemma dist_ctr_com1_co'_1:
  "\<lbrakk> p = (\<lambda>s. s ''ctr'' = m); q = (\<lambda>s. s ''ctr'' = m \<or> s ''ctr'' = m + 1) \<rbrakk> \<Longrightarrow>
  \<tturnstile> {com_pre dist_ctr_com1} dist_ctr_com1 {{} | true}"
  by (simp add: com_pre_dist_ctr_com1 bl_biloof_no_perpetual dist_ctr_com1_derivable)

lemma dist_ctr_com1_co'_2:
  "\<lbrakk> p = (\<lambda>s. s ''ctr'' = m); q = (\<lambda>s. s ''ctr'' = m \<or> s ''ctr'' = m + 1) \<rbrakk> \<Longrightarrow> 
  \<forall>a. a \<in> actions_of dist_ctr_com1 \<longrightarrow>
    (\<forall>pre state_rel. (pre, state_rel) = action_state_rel a \<longrightarrow> 
      (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> pre s \<and> p s \<longrightarrow> q s'))"
  by (auto simp: dist_ctr_com1_def dist_ctr_com_def Assign_def)

lemma dist_ctr_com1_co':
  "\<lbrakk> p = (\<lambda>s. s ''ctr'' = m); q = (\<lambda> s. s ''ctr'' = m \<or> s ''ctr'' = m + 1); Q = {} \<rbrakk> \<Longrightarrow>
  \<tturnstile> {com_pre dist_ctr_com1} dist_ctr_com1 {Q \<union> {p CO q} | true}"
  apply (rule b_co; simp)
   apply (simp add: dist_ctr_com1_co'_1)
  by (frule dist_ctr_com1_co'_2; simp)

lemma dist_ctr_com1_co:
  "\<lbrakk> p = (\<lambda>s. s ''ctr'' = m); q = (\<lambda> s. s ''ctr'' = m \<or> s ''ctr'' = m + 1) \<rbrakk> \<Longrightarrow>
  \<tturnstile> {com_pre dist_ctr_com1} dist_ctr_com1 {{p CO q} | true}"
  apply (frule dist_ctr_com1_co')
  by auto

lemma dist_ctr_com2_co':
  "\<lbrakk> p = (\<lambda>s. s ''ctr'' = m); q = (\<lambda> s. s ''ctr'' = m \<or> s ''ctr'' = m + 1); Q = {} \<rbrakk> \<Longrightarrow>
  \<tturnstile> {com_pre dist_ctr_com2} dist_ctr_com2 {Q \<union> {p CO q} | true}"
  apply (rule b_co; simp)
   apply (simp add: com_pre_dist_ctr_com2 bl_biloof_no_perpetual dist_ctr_com2_derivable)
  by (auto simp: dist_ctr_com2_def dist_ctr_com_def Assign_def)

lemma dist_ctr_com2_co:
  "\<lbrakk> p = (\<lambda>s. s ''ctr'' = m); q = (\<lambda> s. s ''ctr'' = m \<or> s ''ctr'' = m + 1) \<rbrakk> \<Longrightarrow>
  \<tturnstile> {com_pre dist_ctr_com2} dist_ctr_com2 {{p CO q} | true}"
  apply (frule dist_ctr_com2_co')
  by auto

lemma dist_ctr_com_par_co:
  "\<lbrakk> Ps = [dist_ctr_com1, dist_ctr_com2]; Ts = [true, true];
  p = (\<lambda>s. s ''ctr'' = m); q = (\<lambda> s. s ''ctr'' = m \<or> s ''ctr'' = m + 1) \<rbrakk> \<Longrightarrow>
  \<tturnstile> {com_pre (PARALLEL Ps Ts)} PARALLEL Ps Ts {{p CO q} | And Ts}"
  apply (rule_tac Qs="[{p CO q}, {p CO q}]" in b_co_inheritance_parallel; simp)
  using valid_ann_dist_ctr_com apply blast
  using derivable_implies_com_pre_derivable dist_ctr_com1_derivable dist_ctr_com2_derivable less_Suc_eq apply auto[1]
   apply clarsimp
   apply (case_tac i; simp)
    apply (insert dist_ctr_com1_co; simp)
   apply (insert dist_ctr_com2_co; simp)
  by (simp add: nth_Cons')

lemma example_co': 
  "\<lbrakk> p = (\<lambda>s. s ''ctr'' = m); q = (\<lambda> s. s ''ctr'' = m \<or> s ''ctr'' = m + 1) \<rbrakk> \<Longrightarrow>
  \<tturnstile> {true} dist_ctr {{p CO q} | true}"
  apply (frule dist_ctr_com_par_co[rotated 2]; simp)
  by (insert com_pre_dist_ctr_com1 com_pre_dist_ctr_com2; simp)

theorem dist_ctr_co: 
  "\<lbrakk> p = (\<lambda>s. s ''ctr'' = m); q = (\<lambda> s. s ''ctr'' = m \<or> s ''ctr'' = m + 1) \<rbrakk> \<Longrightarrow>
  \<Turnstile> {true} dist_ctr {{p CO q} | true}"
  apply (rule biloof_sound)
  by (rule example_co')
  
end