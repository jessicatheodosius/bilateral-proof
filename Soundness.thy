theory Soundness
imports Rules
begin

section \<open>Soundness\<close>

subsection \<open>Common lemmas that are used in multiple lemmas\<close>

lemma done_one_step:
  "(DONE, s) \<rightarrow> (f', s') \<Longrightarrow> f' = DONE \<and> s' = s"
  by (erule DoneE; simp add: true_def)

lemma done_star:
  "\<lbrakk> (f, s) \<rightarrow>* (f', s'); f = DONE \<rbrakk> \<Longrightarrow> f' = DONE \<and> s' = s"
  apply (induction rule: star_induct; clarsimp)
  by (simp add: done_one_step)

lemma aborted_one_step:
  "(ABORTED, s) \<rightarrow> (f', s') \<Longrightarrow> f' = ABORTED \<and> s' = s"
  by (erule AbortE; simp add: true_def)

lemma aborted_star:
  "\<lbrakk> (f, s) \<rightarrow>* (f', s'); f = ABORTED \<rbrakk> \<Longrightarrow> f' = ABORTED \<and> s' = s"
  apply (induction rule: star_induct; clarsimp)
  by (simp add: aborted_one_step)

(* if f makes a step to f', the actions of f' is a subset of the actions of f *)
lemma actions_of_one_step:
  "\<lbrakk> (f, s) \<rightarrow> (f', s'); action \<in> actions_of f' \<rbrakk> \<Longrightarrow> action \<in> actions_of f"
  apply (induction rule: small_step_induct; clarsimp)
   apply (metis actions_of.simps(8) empty_iff in_set_conv_nth length_list_update nth_list_update_eq nth_list_update_neq nth_mem)
  using set_update_subset_insert by fastforce

lemma invariant_all_reachable_sat':
  "\<lbrakk> (f, s) \<rightarrow>* (f', s'); i s; \<forall>f' s'. (f, s) \<rightarrow>* (f', s') \<longrightarrow> 
  (\<forall>f'' s''. i s' \<and> (f', s') \<rightarrow> (f'', s'') \<longrightarrow> i s'') \<rbrakk> \<Longrightarrow> 
  i s'"
  apply (induction rule: star_induct, simp)
  by (metis star.refl star.step)

(* i holds at any point in the execution *)
lemma invariant_all_reachable_sat:
  "invariant i f s \<Longrightarrow> reachable_sat (\<lambda>f' s'. i s') f s"
  apply (clarsimp simp: invariant_def stable_def co_def reachable_sat_def)
  by (metis invariant_all_reachable_sat')

lemma not_aborted:
  "\<Turnstile> {r} f {Q | t} \<Longrightarrow> \<forall>s. r s \<longrightarrow> reachable_sat (\<lambda>f' s'. f' \<noteq> ABORTED) f s"
  apply (clarsimp simp: valid_spec_def reachable_sat_def holds_def)
  by (metis has_terminated.simps(2))


subsection \<open>Sequential Programs\<close>

lemma action_sound':
  "\<lbrakk> (f, s) \<rightarrow>* (f', s'); f = \<lbrace>pre\<rbrace> ACTION state_rel; pre s; 
  \<forall>s s'. (s, s') \<in> state_rel \<and> pre s \<longrightarrow> t s'; has_terminated f' \<rbrakk> \<Longrightarrow> 
  holds t f' s'"
  apply (induction rule: star_induct; simp)
  apply (erule ActionE, simp)
   apply (metis Validity.holds_def com.distinct(1) done_star)
  by blast

lemma action_sound[simp]:
  "\<lbrakk> \<forall>s. r s \<longrightarrow> pre s; \<forall>s s'. (s, s') \<in> state_rel \<and> pre s \<longrightarrow> t s' \<rbrakk> \<Longrightarrow> 
  \<Turnstile> {r} \<lbrace>pre\<rbrace> ACTION state_rel {{} | t}"
  by (clarsimp simp: valid_spec_def reachable_sat_def action_sound')

lemma pre_implies_annotation:
  "\<lbrakk> \<Turnstile> {r} f {{} | t}; r s \<rbrakk> \<Longrightarrow> com_pre f s" 
  apply (clarsimp simp: valid_spec_def reachable_sat_def holds_def)
  by (metis Abort has_terminated.simps(2) star.refl star.step)

lemma semi_sound':
  "\<lbrakk> (f, s) \<rightarrow>* (f', s'); f = c\<^sub>1;;c\<^sub>2; \<Turnstile> {r} c\<^sub>1 {{} | m}; \<Turnstile> {m} c\<^sub>2 {{} | t}; r s; 
  has_terminated f' \<rbrakk> \<Longrightarrow> 
  holds t f' s'"
  apply (induction arbitrary: c\<^sub>1 c\<^sub>2 r rule: star_induct, simp_all)
  apply (erule SemiE, simp add: pre_implies_annotation)
  apply (unfold valid_spec_def reachable_sat_def)
   apply (subgoal_tac "m s'", simp+)
   apply (simp add: holds_def)
  using has_terminated.simps(1) apply blast
  by (clarsimp, metis curryD curryI star.step)

lemma semi_sound[simp]: 
  "\<lbrakk> \<Turnstile> {r} c\<^sub>1 {{} | m}; \<Turnstile> {m} c\<^sub>2 {{} | t} \<rbrakk> \<Longrightarrow> \<Turnstile> {r} c\<^sub>1;;c\<^sub>2 {{} | t}"
  by (auto simp: valid_spec_def reachable_sat_def semi_sound')

lemma if_sound':
  "\<lbrakk> (\<lbrace>pre\<rbrace> IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow>* (f', s'); r s; pre s; has_terminated f'; 
  \<Turnstile> {r and b} c\<^sub>1 {{} | t}; \<Turnstile> {r and not b} c\<^sub>2 {{} | t} \<rbrakk> \<Longrightarrow>
  holds t f' s'"
  apply (erule StarE, simp)
  apply (erule IfE, simp)
  by (clarsimp simp: valid_spec_def reachable_sat_def holds_def)+

lemma if_sound[simp]:
  "\<lbrakk> \<forall>s. r s \<longrightarrow> pre s; \<Turnstile> {r and b} c\<^sub>1 {{} | t}; \<Turnstile> {r and not b} c\<^sub>2 {{} | t} \<rbrakk> \<Longrightarrow>
  \<Turnstile> {r} \<lbrace>pre\<rbrace> IF b THEN c\<^sub>1 ELSE c\<^sub>2 {{} | t}"
  by (clarsimp simp: valid_spec_def reachable_sat_def if_sound')

text \<open>
  @{text "exec c n c'"} returns true if @{text c} can reach @{text "c'"} by executing small 
  step (@{text "\<rightarrow>"}) n times, and return false otherwise. This is useful to prove the soundness of
  while loop so that we can do induction on the number of steps.
\<close>
primrec exec :: "(com \<times> state) \<Rightarrow> nat \<Rightarrow> (com \<times> state) \<Rightarrow> bool"  ("_ \<rightarrow>^_ _" [55, 1000, 55] 55)
  where
  "c \<rightarrow>^0 c' = (c = c')"
| "c \<rightarrow>^(Suc n) c' = (\<exists>c''. c \<rightarrow> c'' \<and> c'' \<rightarrow>^n c')"

lemma star_implies_exec: "c \<rightarrow>* c' \<Longrightarrow> \<exists>n. c \<rightarrow>^n c'"
  apply (induction rule: star.induct)
  using exec.simps by blast+

lemma exec_implies_star: "c \<rightarrow>^n c' \<Longrightarrow> c \<rightarrow>* c'"
  apply (induction n arbitrary: c, simp)
  by (clarsimp simp: star.step)

lemma exec_eq_star: "c \<rightarrow>* c' = (\<exists>n. c \<rightarrow>^n c')"
  by (auto simp: star_implies_exec exec_implies_star)

lemma semi_exec_done:
  "\<lbrakk> (c\<^sub>1;;c\<^sub>2, s) \<rightarrow>^n (DONE, s') \<rbrakk> \<Longrightarrow>
  \<exists>i j s''. (c\<^sub>1, s) \<rightarrow>^i (DONE, s'') \<and> j < n \<and> (c\<^sub>2, s'') \<rightarrow>^j (DONE, s')"
  apply (induction n arbitrary: c\<^sub>1 s, simp)
  apply (clarsimp, erule SemiE)
  using aborted_star exec_implies_star apply blast
  using exec.simps apply blast
  by (clarsimp, meson exec.simps(2) less_Suc_eq)

lemma semi_exec_aborted:
  "\<lbrakk> (c\<^sub>1;;c\<^sub>2, s) \<rightarrow>^n (ABORTED, s') \<rbrakk> \<Longrightarrow>
  (\<exists>i. (c\<^sub>1, s) \<rightarrow>^i (ABORTED, s')) \<or> 
  (\<exists>i j s''. (c\<^sub>1, s) \<rightarrow>^i (DONE, s'') \<and> j < n \<and> (c\<^sub>2, s'') \<rightarrow>^j (ABORTED, s'))"
  apply (induct n arbitrary: c\<^sub>1 s, simp)
  apply (clarsimp, erule SemiE)
    apply (simp, metis Abort exec.simps(2))
   apply (clarsimp, erule_tac x=1 in allE, clarsimp)
  by (clarsimp, meson exec.simps(2) less_Suc_eq)

lemma not_aborted_exec:
  "\<lbrakk> \<Turnstile> {r} c {{} | i}; r s; (c, s) \<rightarrow>^j (ABORTED, s') \<rbrakk> \<Longrightarrow> False"
  apply (frule not_aborted, clarsimp simp: reachable_sat_def exec_eq_star)
  by blast

lemma while_body_invariant:
  "\<lbrakk> \<Turnstile> {r} c {{} | i}; r s; (c, s) \<rightarrow>^n (DONE, s') \<rbrakk> \<Longrightarrow> i s'"
  apply (simp add: valid_spec_def reachable_sat_def holds_def)
  using exec_implies_star has_terminated.simps(1) by blast

lemma has_terminated_aborted_or_done:
  "has_terminated f \<Longrightarrow> f = ABORTED \<or> f = DONE"
  using has_terminated.elims(2) by blast

lemma action_skip_one_step:
  "\<lbrakk> (f, s) \<rightarrow> (f', s'); f = \<lbrace>i\<rbrace> ACTION {(x, y). x = y}; i s \<rbrakk> \<Longrightarrow> s = s'"
  by blast

lemma action_skip_star:
  "\<lbrakk> (f, s) \<rightarrow>* (f', s'); f = \<lbrace>i and not b\<rbrace> ACTION {(x, y). x = y}; (not b) s; i s \<rbrakk> \<Longrightarrow> 
  f' \<noteq> ABORTED \<and> s = s'"
  apply (induction rule: star_induct; simp)
  by (metis (no_types, lifting) ActionE action_skip_one_step com.distinct(1) com_pre.simps(3) done_star prod.inject)

lemma while_sounds'':
  "\<lbrakk> (f, s) \<rightarrow>^n (f', s'); f = \<lbrace>i\<rbrace> \<lbrace>local_b\<rbrace> WHILE b i DO c; i s; \<forall>s. (i and b) s \<longrightarrow> com_pre c s;
  \<Turnstile> {com_pre c} c {{} | i}; \<forall>s. (not b) s \<longrightarrow> (not local_b) s; \<forall>s. (i and not local_b) s \<longrightarrow> t s; 
  has_terminated f' \<rbrakk> \<Longrightarrow>
  holds t f' s'"
  apply (unfold holds_def)
  apply (induction n arbitrary: s rule: nat_less_induct)
  apply (case_tac n, clarsimp+)
  apply (erule WhileE, simp add: true_def)
   apply (frule has_terminated_aborted_or_done, erule disjE; simp)
    apply (clarsimp, drule semi_exec_aborted)
    apply (meson less_SucI not_aborted_exec while_body_invariant)
   apply (metis less_SucI semi_exec_done while_body_invariant)
  apply (frule exec_implies_star)
  by (frule_tac i=i and b="local_b" in action_skip_star; simp)

lemma while_semi_sound':
  "\<lbrakk> (f, s) \<rightarrow>^n (f', s'); f = c;;\<lbrace>i\<rbrace> \<lbrace>local_b\<rbrace> WHILE b i DO c; i s; b s;
  \<forall>s. (i and b) s \<longrightarrow> com_pre c s; \<Turnstile> {com_pre c} c {{} | i};
  \<forall>s. (not b) s \<longrightarrow> (not local_b) s; \<forall>s. (i and not local_b) s \<longrightarrow> t s; has_terminated f' \<rbrakk> \<Longrightarrow>
  holds t f' s'"
  apply (frule has_terminated_aborted_or_done, erule disjE; simp)
   apply (drule semi_exec_aborted, erule disjE; clarsimp?)
  using not_aborted_exec apply blast
  using has_terminated.simps(2) while_body_invariant while_sounds'' apply blast
  apply (drule semi_exec_done, clarsimp)
  using has_terminated.simps(1) while_body_invariant while_sounds'' by blast

lemma while_sound':
  "\<lbrakk> (f, s) \<rightarrow>^n (f', s'); f = \<lbrace>pre\<rbrace> \<lbrace>local_b\<rbrace> WHILE b i DO c;  \<forall>s. pre s \<longrightarrow> i s; 
  \<forall>s. (i and b) s \<longrightarrow> com_pre c s; \<Turnstile> {com_pre c} c {{} | i}; pre s;
  \<forall>s. (not b) s \<longrightarrow> (not local_b) s; \<forall>s. (i and not local_b) s \<longrightarrow> t s; has_terminated f' \<rbrakk> \<Longrightarrow>
  holds t f' s'"
  apply (case_tac n, clarsimp+)
  apply (erule WhileE; simp add: while_semi_sound')
  apply (frule exec_implies_star, unfold holds_def)
  by (frule_tac b="local_b" and i=i in action_skip_star; simp)
 
lemma while_sound[simp]:
  "\<lbrakk> \<forall>s. pre s \<longrightarrow> i s; \<forall>s. (i and b) s \<longrightarrow> com_pre c s; \<Turnstile> {com_pre c} c {{} | i}; 
  \<forall>s. (not b) s \<longrightarrow> (not local_b) s; \<forall>s. (i and not local_b) s \<longrightarrow> t s \<rbrakk> \<Longrightarrow> 
  \<Turnstile> {pre} \<lbrace>pre\<rbrace> \<lbrace>local_b\<rbrace> WHILE b i DO c {{} | t}"
  by (clarsimp simp: valid_spec_def reachable_sat_def while_sound' exec_eq_star)


subsection \<open>Parallel Programs\<close>

lemma and_map_com_pre_Ps1:
  "And (map com_pre Ps) s \<Longrightarrow> \<forall>i<length Ps. com_pre (Ps!i) s"
  by (induction Ps; simp add: nth_Cons')

lemma and_map_com_pre_Ps2:
  "\<forall>i<length Ps. com_pre (Ps!i) s \<Longrightarrow> And (map com_pre Ps) s"
  apply (induction Ps, simp add: true_def)
  by fastforce

lemma and_Ts:
  "\<forall>i<length Ts. (Ts!i) s \<Longrightarrow> And Ts s"
  apply (induction Ts, simp add: true_def)
  by fastforce

(* if p is stable in f, and f makes a step to f', then p is stable in f' *)
lemma is_ann_stable_one_step:
  "\<lbrakk> (f, s) \<rightarrow> (f', s'); is_ann_stable p f \<rbrakk> \<Longrightarrow> is_ann_stable p f'"
  apply (unfold is_ann_stable_def)
  by (blast dest: actions_of_one_step)

lemma all_anns_post_ann:
  "\<lbrakk> p \<in> all_anns_par (map all_anns (Ps[i := \<lbrace>Ts ! i\<rbrace> POSTANN])) Ts; i < length Ps;
  length Ps = length Ts \<rbrakk> \<Longrightarrow> 
  p \<in> all_anns_par (map all_anns Ps) Ts"
  apply (induction Ps arbitrary: i p Ts; simp)
  apply (case_tac i; simp)
   apply (case_tac Ts; simp)
   apply blast
  apply (case_tac Ts; simp)
  by auto

lemma all_anns_one_step:
  "\<lbrakk> Ps' = Ps[i := c']; i < length Ps; p \<in> all_anns_par (map all_anns Ps') Ts; 
  \<And>p. p \<in> all_anns c' \<Longrightarrow> p \<in> all_anns (Ps ! i); length Ps = length Ts;
  (Ps ! i, s) \<rightarrow> (c', s'); c' \<noteq> DONE \<rbrakk> \<Longrightarrow>
  p \<in> all_anns_par (map all_anns Ps) Ts"
  apply (induction Ps arbitrary: Ps' i p c' s s' Ts; simp)
  apply (case_tac i; auto)
   apply (case_tac Ts; simp)
   apply meson
  apply (case_tac Ts; simp)
  by auto

lemma all_anns_is_subset:     
  "\<lbrakk> (g, s) \<rightarrow> (g', s'); p \<in> all_anns g'; com_pre g s; \<turnstile> {com_pre g} g {t}; g' \<noteq> DONE \<rbrakk> \<Longrightarrow> 
  p \<in> all_anns g"
  apply (induction arbitrary: p t rule: small_step_induct; clarsimp)
  using semi_elim apply blast
  using all_anns_post_ann par_elim apply blast
  apply (frule par_elim; simp; clarsimp)
  by (metis (mono_tags, lifting) Post_annE all_anns_one_step and_map_com_pre_Ps1)

(* if g is stable in h and g makes a step to g', g' is also stable in h *)
lemma is_com_stable_one_step1:
  "\<lbrakk> (g, s) \<rightarrow> (g', s'); is_com_stable g h; com_pre g s; \<turnstile> {com_pre g} g {t} \<rbrakk> \<Longrightarrow> 
  is_com_stable g' h"
  apply (clarsimp simp: is_com_stable_def all_anns_is_subset)
  apply (case_tac "g' = DONE", clarsimp)
   apply (simp add: is_ann_stable_def true_def)
  by (simp add: all_anns_is_subset)

(* if g is stable in h and h makes a step to h', g is also stable in h' *)
lemma is_com_stable_one_step2:
  "\<lbrakk> (h, s) \<rightarrow> (h', s'); is_com_stable g h \<rbrakk> \<Longrightarrow> is_com_stable g h'"
  by (simp add: is_com_stable_def is_ann_stable_one_step)

lemma com_pre_all_anns_par:
  "\<lbrakk> \<And>c r t. \<lbrakk> c \<in> set Ps; \<turnstile> {r} c {t} \<rbrakk> \<Longrightarrow> com_pre c \<in> all_anns c; length Ps = length Ts;
  \<forall>i<length Ts. \<turnstile> {com_pre (Ps ! i)} Ps ! i {Ts ! i} \<or> Ps ! i = \<lbrace>Ts ! i\<rbrace> POSTANN \<rbrakk> \<Longrightarrow> 
  com_pre (PARALLEL Ps Ts) \<in> all_anns (PARALLEL Ps Ts)"
  apply (induction Ps arbitrary: Ts; auto)
  apply (case_tac Ts; simp)
  apply (drule_tac x=list in meta_spec)
  apply (drule meta_mp; clarsimp)
  by (drule meta_mp; fastforce)

(* the local annotation of a component is in its set of annotations *)
lemma com_pre_in_all_anns:
  "\<turnstile> {r} f {t} \<Longrightarrow> com_pre f \<in> all_anns f"
  apply (induction f arbitrary: r t; auto)
  using semi_elim apply blast
  apply (rename_tac Ps Ts r t)
  apply (frule par_elim; simp; clarsimp)
  using com_pre_all_anns_par by auto

lemma ann_stable_holds_one_step:
  "\<lbrakk> (f, s) \<rightarrow> (f', s'); is_ann_stable p f; p s \<rbrakk> \<Longrightarrow> p s'"
  apply (unfold is_ann_stable_def)
  apply (induction rule: small_step_induct; simp)
  by fastforce+

lemma com_pre_and_derivable_done_par:
  "\<lbrakk> i < length Ps; \<forall>j<length Ps. (not (=) j) i \<longrightarrow> Ps ! j = \<lbrace>Ts ! j\<rbrace> POSTANN; Ps ! i = c; 
  (c, s) \<rightarrow> (DONE, s'); \<And>t. \<lbrakk>com_pre c s; \<turnstile> {com_pre c} c {t}\<rbrakk> \<Longrightarrow> t s';
  And (map com_pre Ps) s; \<turnstile> {And (map com_pre Ps)} PARALLEL Ps Ts {t} \<rbrakk> \<Longrightarrow> 
  t s'"
  apply (frule par_elim; simp; clarsimp)
  apply (drule_tac x="Ts ! i" in meta_spec)
  apply (drule meta_mp, simp add: and_map_com_pre_Ps1)
  apply (subgoal_tac "And Ts s'"; simp?)
  apply (rule and_Ts; clarsimp)
  apply (case_tac "iaa = i", fastforce)
  apply (erule_tac x=iaa in allE; clarsimp)
  apply (frule and_map_com_pre_Ps1)
  apply (erule_tac x=iaa in allE; clarsimp)+
  apply (clarsimp simp: valid_ann_def valid_ann'_def)
  by (frule ann_stable_holds_one_step; simp)

(* a component that goes to DONE satisfies its postcondition *)
lemma com_pre_and_derivable_done:
  "\<lbrakk> (f, s) \<rightarrow> (f', s'); com_pre f s; \<turnstile> {com_pre f} f {t}; f' = DONE \<rbrakk> \<Longrightarrow> t s'"
  apply (induction arbitrary: t rule: small_step_induct; simp)
       apply (metis done_elim)
      apply (metis action_elim)
     apply (metis semi_elim done_elim)
    apply (metis if_elim done_elim)
   apply (metis if_elim done_elim)
  by (metis com_pre_and_derivable_done_par)

(* the precondition of a parallel composition remains valid after making a step *)
lemma par_done_pre_holds_one_step:
  "\<lbrakk> (Ps ! i, s) \<rightarrow> (DONE, s'); And (map com_pre Ps) s; i < length Ps; valid_ann Ps Ts;
  length Ps = length Ts; Ps' = Ps[i := \<lbrace>Ts ! i\<rbrace> POSTANN];
  \<forall>i<length Ts. \<turnstile> {com_pre (Ps ! i)} Ps ! i {Ts ! i} \<or> Ps ! i = \<lbrace>Ts ! i\<rbrace> POSTANN \<rbrakk> \<Longrightarrow>
  And (map com_pre Ps') s'"
  apply (rule and_map_com_pre_Ps2)
  apply (clarsimp simp: valid_ann_def valid_ann'_def)
  apply (case_tac "i = ia"; simp)
   apply (erule_tac x=ia in allE; simp)+
   apply (erule disjE)
    apply (frule_tac t = "Ts!i" in com_pre_and_derivable_done)
       apply (simp add: and_map_com_pre_Ps1)+
   apply (erule Post_annE; simp)
  apply (erule_tac x=ia in allE)+
  apply clarsimp
  apply (erule_tac x=i in allE; clarsimp)+
  apply (erule disjE)
   apply (frule_tac f="Ps!i" and p="com_pre (Ps!ia)" in ann_stable_holds_one_step)
  using com_pre_in_all_anns is_com_stable_def apply blast
    apply (simp add: and_map_com_pre_Ps1)+
  using and_map_com_pre_Ps1 ann_stable_holds_one_step com_pre.simps(8) by fastforce

(* after the parallel composition makes a step, it is still derivable *)
lemma par_done_derivable_one_step:
  "\<lbrakk> valid_ann Ps Ts; \<forall>i<length Ts. \<turnstile> {com_pre (Ps ! i)} Ps ! i {Ts ! i} \<or> Ps ! i = \<lbrace>Ts ! i\<rbrace> POSTANN; 
  \<forall>s. And Ts s \<longrightarrow> t s; Ps' = Ps[i := \<lbrace>Ts ! i\<rbrace> POSTANN]; length Ps = length Ts; length Ps > 0;
  j < length Ts; (not (=) j) i; (not (=) (Ps ! j)) (\<lbrace>Ts ! j\<rbrace> POSTANN) \<rbrakk> \<Longrightarrow> 
  \<turnstile> {com_pre (PARALLEL Ps' Ts)} PARALLEL Ps' Ts {And Ts}"
  apply (rule b_par; simp)
    apply (clarsimp simp: valid_ann_def valid_ann'_def)
    apply (rule conjI)
     apply (metis actions_of.simps(8) empty_iff is_ann_stable_def nth_list_update nth_list_update_neq)
    apply (case_tac "i = ia"; simp add: is_com_stable_def)
    apply (metis actions_of.simps(8) empty_iff is_ann_stable_def is_com_stable_def nth_list_update_eq nth_list_update_neq)
   apply (metis nth_list_update nth_list_update_neq)
  by auto

lemma com_pre_one_step:
  "\<lbrakk> (c, s) \<rightarrow> (c', s'); com_pre c s; \<turnstile> {com_pre c} c {t} \<rbrakk> \<Longrightarrow> com_pre c' s'"
  apply (induction arbitrary: t rule: small_step_induct; clarsimp simp: true_def)
         apply (simp add: com_pre_and_derivable_done semi_elim)
        apply (blast dest: semi_elim)
       apply (simp add: if_elim)
      apply (simp add: if_elim)
     apply (simp add: while_elim)
    apply (simp add: while_elim)
  using par_done_pre_holds_one_step par_elim apply auto[1]
  apply (frule par_elim; simp; clarsimp)
  apply (rule and_map_com_pre_Ps2; clarsimp)
  apply (case_tac "i = ib"; simp)
  using and_map_com_pre_Ps1 apply fastforce
  apply (clarsimp simp: valid_ann_def valid_ann'_def)
  apply (subgoal_tac "\<turnstile> {com_pre (Ps!ib)} Ps!ib {Ts!ib} \<or> Ps!ib = \<lbrace>Ts!ib\<rbrace> POSTANN")
   apply (erule disjE)
   apply (frule_tac r="com_pre (Ps!ib)" in com_pre_in_all_anns)
    apply (simp add: and_map_com_pre_Ps1 ann_stable_holds_one_step is_com_stable_def)
   apply (metis and_map_com_pre_Ps1 ann_stable_holds_one_step com_pre.simps(8))
  by auto

lemma par_not_done_pre_holds_one_step:
  "\<lbrakk> (Ps ! i, s) \<rightarrow> (c', s'); c' \<noteq> DONE; And (map com_pre Ps) s; i < length Ps; valid_ann Ps Ts;
  length Ps = length Ts; Ps' = Ps[i := c']; 
  \<forall>i<length Ts. \<turnstile> {com_pre (Ps ! i)} Ps ! i {Ts ! i} \<or> Ps ! i = \<lbrace>Ts ! i\<rbrace> POSTANN \<rbrakk> \<Longrightarrow>
  And (map com_pre Ps') s'"
  apply (rule and_map_com_pre_Ps2)
  apply (clarsimp simp: valid_ann_def valid_ann'_def)
  apply (case_tac "i = ia"; simp)
   apply (erule_tac x=i in allE)+
   apply simp
   apply (erule disjE)
    apply (simp add: and_map_com_pre_Ps1 com_pre_one_step)
   apply clarsimp
   apply (erule Post_annE; simp add: false_def)
  using and_map_com_pre_Ps1 apply force
  apply (subgoal_tac "\<turnstile> {com_pre (Ps!ia)} Ps!ia {Ts!ia} \<or> Ps!ia = \<lbrace>Ts!ia\<rbrace> POSTANN")
   apply (erule disjE)
    apply (frule_tac r="com_pre (Ps!ia)" in com_pre_in_all_anns)
    apply (simp add: and_map_com_pre_Ps1 ann_stable_holds_one_step is_com_stable_def)
   apply (metis and_map_com_pre_Ps1 ann_stable_holds_one_step com_pre.simps(8))
  by auto

lemma valid_ann_step:
  "\<lbrakk> (Ps!i, s) \<rightarrow> (c', s'); i < length Ps; valid_ann Ps Ts;
  com_pre (Ps!i) s; \<turnstile> {com_pre (Ps ! i)} Ps!i {t} \<rbrakk> \<Longrightarrow>
  valid_ann (Ps[i:=c']) Ts"
  apply (clarsimp simp: valid_ann_def valid_ann'_def)
  apply (case_tac "ia = i")
  by (simp add: is_ann_stable_one_step is_com_stable_one_step1 is_com_stable_one_step2 nth_list_update)+

lemma par_not_done_derivable_one_step:
  "\<lbrakk> i < length Ts; (Ps ! i, s) \<rightarrow> (c', s'); And (map com_pre Ps) s; 
  \<turnstile> {And (map com_pre Ps)} PARALLEL Ps Ts {t}; Ps' = Ps[i := c'];
  com_pre c' s'; \<turnstile> {com_pre c'} c' {Ts ! i} \<rbrakk> \<Longrightarrow>
  \<turnstile> {com_pre (PARALLEL Ps' Ts)} PARALLEL Ps' Ts {And Ts}"
  apply (frule par_elim, simp)
  apply (rule b_par; clarsimp)
    apply (metis Post_annE and_map_com_pre_Ps1 valid_ann_step)
   apply (metis nth_list_update)
  by (metis nth_list_update_eq post_ann_elim)

(* derivability is preserved here. this lemma can't be proved if the rules are not stratified. *)
lemma com_pre_and_derivable_one_step:
  "\<lbrakk> (f, s) \<rightarrow> (f', s'); com_pre f s; \<turnstile> {com_pre f} f {t}; f' \<noteq> DONE \<rbrakk> \<Longrightarrow> 
  (com_pre f') s' \<and> \<turnstile> {com_pre f'} f' {t}"
  apply (induction arbitrary: t rule: small_step_induct; simp)
         apply (simp add: com_pre_and_derivable_done semi_elim)
        apply (meson b_semi semi_elim)
       apply (simp add: if_elim)
      apply (simp add: if_elim)
     apply (simp add: b_semi b_while while_elim)
    apply (simp add: b_action while_elim)
   apply (frule par_elim; simp; clarsimp)
   apply (rule conjI)
    apply (simp add: par_done_pre_holds_one_step)
   apply (frule_tac Ps'="Ps[i := \<lbrace>Ts ! i\<rbrace> POSTANN]" in par_done_derivable_one_step; simp?)
    apply auto[1]
   apply (blast intro: b_strengthen_weaken)
  apply (frule par_elim; simp; clarsimp)
  apply (rule conjI)
   apply (simp add: par_not_done_pre_holds_one_step)
  apply (drule_tac x="Ts!i" in meta_spec)
  apply (drule meta_mp)
   apply (simp add: and_map_com_pre_Ps1)
  apply (drule meta_mp)
  using and_map_com_pre_Ps1 apply fastforce
  apply clarsimp
  apply (frule par_not_done_derivable_one_step; simp)
  apply (frule par_elim; simp; clarsimp)
  by (blast intro: b_strengthen_weaken)

lemma par_post_ann_valid_ann:
  "\<lbrakk> valid_ann Ps Ts; length Ps = length Ts; Ps' = Ps[i := \<lbrace>Ts ! i\<rbrace> POSTANN] \<rbrakk> \<Longrightarrow> 
  valid_ann Ps' Ts"
  apply (clarsimp simp: valid_ann_def valid_ann'_def)
  apply (rule conjI)
   apply (case_tac "i = j"; simp add: is_ann_stable_def)
  apply (case_tac "i = j"; simp)
   apply (simp add: is_com_stable_def is_ann_stable_def)
  by (case_tac "i = ia"; simp add: is_com_stable_def)

(* b_par is sound for the Par (small-step) case *)
lemma par_Par_sound:
  "\<lbrakk> \<forall>i<length Ts. \<turnstile> {com_pre (Ps ! i)} Ps ! i {Ts ! i} \<or> Ps ! i = \<lbrace>Ts ! i\<rbrace> POSTANN; 
  valid_ann Ps Ts; And (map com_pre Ps) b; length Ps = length Ts;
  Ps' = Ps[i := c']; i < length Ts; (Ps ! i, b) \<rightarrow> (c', s'); c' \<noteq> DONE \<rbrakk> \<Longrightarrow>
  valid_ann Ps' Ts \<and> length Ps' = length Ts \<and> (And (map com_pre Ps') s') \<and> Ts \<noteq> [] \<and>
  (\<forall>j<length Ts. \<turnstile> {com_pre (Ps' ! j)} Ps' ! j {Ts ! j} \<or> Ps' ! j = \<lbrace>Ts ! j\<rbrace> POSTANN)"
  apply auto
    apply (metis Post_annE and_map_com_pre_Ps1 valid_ann_step)
   apply (simp add: par_not_done_pre_holds_one_step)
  by (metis Post_annE and_map_com_pre_Ps1 com_pre_and_derivable_one_step nth_list_update)

lemma par_sound':
  "\<lbrakk> (f, s) \<rightarrow>* (f', s'); f = PARALLEL Ps Ts; valid_ann Ps Ts; has_terminated f';
  length Ps = length Ts; (not (=) Ts) []; And (map com_pre Ps) s; 
  \<forall>j<length Ts. \<turnstile> {com_pre (Ps ! j)} Ps ! j {Ts ! j} \<or> Ps ! j = \<lbrace>Ts ! j\<rbrace> POSTANN \<rbrakk> \<Longrightarrow> 
  (And Ts) s' \<and> f' \<noteq> ABORTED"
  apply (induction arbitrary: Ps Ts rule: star_induct; simp)
  apply (erule ParE; simp)
    apply (metis (no_types, lifting) ParA Post_annE b_par com.distinct(1) com_pre.simps(7) com_pre_and_derivable_done done_star length_greater_0_conv)
   apply (simp add: par_done_pre_holds_one_step nth_list_update par_post_ann_valid_ann)
  apply (frule par_Par_sound; simp)
  by blast

lemma par_sound[simp]:
  "\<lbrakk> valid_ann Ps Ts; length Ps = length Ts; 0 < length Ps; 
  \<forall>i. i < length Ps \<longrightarrow> \<turnstile> {com_pre (Ps!i)} Ps!i {Ts!i} \<or> Ps!i = \<lbrace>Ts!i\<rbrace> POSTANN;
  \<forall>i. i < length Ps \<longrightarrow> \<Turnstile> {com_pre (Ps!i)} Ps!i {{} | Ts!i} \<or> Ps!i = \<lbrace>Ts!i\<rbrace> POSTANN \<rbrakk> \<Longrightarrow>
  \<Turnstile> {And (map com_pre Ps)} PARALLEL Ps Ts {{} | And Ts}"
  by (clarsimp simp: valid_spec_def holds_def reachable_sat_def par_sound')


subsection \<open>Meta Rules\<close>

lemma strengthen_weaken_sound[simp]:
  "\<lbrakk> \<Turnstile> {r} f {Q | t}; \<forall>s. r' s \<longrightarrow> r s; \<forall>s. t s \<longrightarrow> t' s; Q' \<subseteq> Q  \<rbrakk> \<Longrightarrow> \<Turnstile> {r'} f {Q' | t'}"
  apply (clarsimp simp: valid_spec_def reachable_sat_def holds_def)
  by (metis set_rev_mp)

lemma conjunction_sound[simp]:
  "\<lbrakk> \<Turnstile> {r} f {Q | t}; \<Turnstile> {r'} f {Q' | t'} \<rbrakk> \<Longrightarrow> \<Turnstile> {r and r'} f {Q \<union> Q' | t and t'}"
  apply (clarsimp simp: valid_spec_def reachable_sat_def holds_def)
  by auto

lemma disjunction_sound[simp]:
  "\<lbrakk> \<Turnstile> {r} f {Q | t}; \<Turnstile> {r'} f {Q' | t'} \<rbrakk> \<Longrightarrow> \<Turnstile> {r or r'} f {Q \<inter> Q' | t or t'}"
  by (clarsimp simp: valid_spec_def reachable_sat_def holds_def)

lemma conjunction_sound_empty[simp]:
  "\<lbrakk> \<Turnstile> {r} f {{} | t}; \<Turnstile> {r'} f {{} | t'} \<rbrakk> \<Longrightarrow> \<Turnstile> {r and r'} f {{} | t and t'}"
  by (clarsimp simp: valid_spec_def reachable_sat_def holds_def)

lemma disjunction_sound_empty[simp]:
  "\<lbrakk> \<Turnstile> {r} f {{} | t}; \<Turnstile> {r'} f {{} | t'} \<rbrakk> \<Longrightarrow> \<Turnstile> {r or r'} f {{} | t or t'}"
  by (clarsimp simp: valid_spec_def reachable_sat_def holds_def)


subsection \<open>Soundness of @{term biloof_no_perpetual_sound}\<close>

lemma biloof_no_perpetual_sound[simp]:
  "\<turnstile> {r} f {t} \<Longrightarrow> \<Turnstile> {r} f {{} | t}"
  apply (induction rule: biloof_no_perpetual.induct; clarsimp?)
  by (metis length_greater_0_conv par_sound)


subsection \<open>CO\<close>

lemma actions_of_subset:
  "\<lbrakk> (f, s) \<rightarrow>* (f', s'); \<forall>a. a \<in> actions_of f \<longrightarrow> X a \<rbrakk> \<Longrightarrow> \<forall>a. a \<in> actions_of f' \<longrightarrow> X a"
  apply (induction rule: star_induct, simp)
  by (simp add: actions_of_one_step)

lemma co_sound':
  "\<lbrakk> (f', s') \<rightarrow> (f'', s''); p s'; \<forall>s. p s \<longrightarrow> q s;
  \<forall>a pre state_rel. a \<in> actions_of f' \<longrightarrow> (pre, state_rel) = action_state_rel a \<longrightarrow> 
  (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> (pre and p) s \<longrightarrow> q s') \<rbrakk> \<Longrightarrow> 
  q s''"
  apply (induct rule: small_step_induct; simp)
  by fastforce+

lemma co_sound[simp]:
  "\<lbrakk> \<Turnstile> {r} f {Q | t}; \<forall>s. p s \<longrightarrow> q s;
  \<forall>a pre state_rel. a \<in> actions_of f \<longrightarrow> (pre, state_rel) = action_state_rel a
  \<longrightarrow> (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> (pre and p) s \<longrightarrow> q s') \<rbrakk> \<Longrightarrow> 
  \<Turnstile> {r} f {Q \<union> {p CO q} | t}"
  apply (clarsimp simp: valid_spec_def)
  apply (erule disjE; simp)
  apply (clarsimp simp: co_def)
  apply (erule_tac x="s" in allE, simp)+
  apply (clarsimp simp: reachable_sat_def)
  apply (frule actions_of_subset, simp)
  by (frule co_sound'; simp)

subsubsection \<open>Inheritance Meta Rule\<close>

lemma co_inheritance_semi_sound[simp]:
  "\<lbrakk> \<turnstile> {r} c\<^sub>1 {com_pre c\<^sub>2}; \<turnstile> {com_pre c\<^sub>2} c\<^sub>2 {t};
  \<tturnstile> {r} c\<^sub>1 {Q | com_pre c\<^sub>2}; \<Turnstile> {r} c\<^sub>1 {Q | com_pre c\<^sub>2}; (p CO q) \<in> Q; 
  \<tturnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q' | t}; \<Turnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q' | t}; (p CO q) \<in> Q' \<rbrakk> \<Longrightarrow> 
  \<Turnstile> {r} c\<^sub>1;;c\<^sub>2 {{p CO q} | t}"
  apply (drule b_semi; simp?)
  apply (frule_tac r=r in biloof_no_perpetual_sound)
  apply (frule_tac f=c\<^sub>1 in co_elim, simp)
  apply (frule_tac f=c\<^sub>2 in co_elim, simp)
  by (frule co_sound; simp)

lemma co_inheritance_if_sound[simp]:
  "\<lbrakk> \<forall>s. (pre and b) s \<longrightarrow> com_pre c\<^sub>1 s; \<forall>s. (pre and not b) s \<longrightarrow> com_pre c\<^sub>2 s;
  \<turnstile> {com_pre c\<^sub>1} c\<^sub>1 {t}; \<turnstile> {com_pre c\<^sub>2} c\<^sub>2 {t};
  \<tturnstile> {com_pre c\<^sub>1} c\<^sub>1 {Q | t}; \<Turnstile> {com_pre c\<^sub>1} c\<^sub>1 {Q | t}; (p CO q) \<in> Q; 
  \<tturnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q'| t}; \<Turnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q'| t}; (p CO q) \<in> Q' \<rbrakk> \<Longrightarrow>
  \<Turnstile> {pre} \<lbrace>pre\<rbrace> IF b THEN c\<^sub>1 ELSE c\<^sub>2 {{p CO q} | t}"
  apply (frule_tac b_if, simp+)
  apply (frule_tac r=pre in biloof_no_perpetual_sound)
  apply (frule_tac f=c\<^sub>1 in co_elim, simp)
  apply (frule_tac f=c\<^sub>2 in co_elim, simp)
  by (frule co_sound; simp)

lemma co_inheritance_while_sound[simp]:
  "\<lbrakk> \<forall>s. pre s \<longrightarrow> i s; \<forall>s. (i and b) s \<longrightarrow> com_pre c s; 
  \<turnstile> {com_pre c} c {i}; \<tturnstile> {com_pre c} c {Q | t}; 
  \<Turnstile> {com_pre c} c {Q | t}; (p CO q) \<in> Q;
  \<forall>s. (not b) s \<longrightarrow> (not local_b) s; \<forall>s. (i and not local_b) s \<longrightarrow> t s \<rbrakk> \<Longrightarrow>
  \<Turnstile> {pre} \<lbrace>pre\<rbrace> \<lbrace>local_b\<rbrace> WHILE b i DO c {{p CO q} | t}"
  apply (frule_tac b_while, simp+)
  apply (frule_tac r=pre in biloof_no_perpetual_sound)
  apply (frule_tac f=c in co_elim, simp)
  by (frule co_sound; simp)

lemma co_inheritance_parallel_sound[simp]:
  "\<lbrakk> valid_ann Ps Ts; length Ps = length Ts; length Ts = length Qs; 0 < length Ps;
  \<forall>i<length Ps. \<turnstile> {com_pre (Ps ! i)} Ps ! i {Ts ! i};
  \<forall>i<length Ps. \<tturnstile> {com_pre (Ps ! i)} Ps ! i {Qs ! i | Ts ! i};
  \<forall>i<length Ps. \<Turnstile> {com_pre (Ps ! i)} Ps ! i {Qs ! i | Ts ! i};
  \<forall>i<length Qs. (p CO q) \<in> Qs ! i \<rbrakk> \<Longrightarrow> 
  \<Turnstile> {And (map com_pre Ps)} PARALLEL Ps Ts {{p CO q} | And Ts}"
  apply (frule b_par; simp)
   apply (erule_tac x=0 in allE; clarsimp)
  using post_ann_elim apply fastforce
  apply (frule biloof_no_perpetual_sound)
  apply (frule co_sound; simp; clarsimp)
   apply (erule_tac x=0 in allE; clarsimp)+
   apply (frule co_elim; simp; blast)
  apply (simp add: in_set_conv_nth; clarsimp)
  apply (erule_tac x=i in allE; clarsimp)+
  by (frule co_elim; simp; blast)

subsubsection \<open>Invariance Meta Rule\<close>

lemma invariant_sound':
  "\<lbrakk> \<Turnstile> {r} f {Q | t}; (i CO i) \<in> Q; \<forall>s. r s \<longrightarrow> i s\<rbrakk> \<Longrightarrow> \<Turnstile> {r} f {Q \<union> {INVARIANT i} | t}"
  using valid_spec_def invariant_def stable_def by fastforce

lemma invariant_sound[simp]:
  "\<lbrakk> \<Turnstile> {r} f {Q | t};
  \<forall>a pre state_rel. a \<in> actions_of f \<longrightarrow> (pre, state_rel) = action_state_rel a
  \<longrightarrow> (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> (pre and i) s \<longrightarrow> i s'); \<forall>s. r s \<longrightarrow> i s \<rbrakk> \<Longrightarrow> 
  \<Turnstile> {r} f {Q \<union> {INVARIANT i} | t}"
  apply (frule_tac p=i and q=i in co_sound; simp)
  apply (frule invariant_sound'; simp?)
  by (simp add: Un_insert_right valid_spec_def)

lemma invariant_pre_post_sound[simp]:
  "\<lbrakk> \<Turnstile> {r} f {Q | t}; (INVARIANT i) \<in> Q \<rbrakk> \<Longrightarrow> \<Turnstile> {r and i} f {Q | t and i}"
  apply (clarsimp simp: valid_spec_def)
  apply (erule_tac x=s in allE, clarsimp)+
  apply (subgoal_tac "invariant i f s")
   apply (drule invariant_all_reachable_sat)
   apply (clarsimp simp: reachable_sat_def holds_def)
  by fastforce

lemma invariant_co_sound[simp]:
  "\<lbrakk> \<Turnstile> {r} f {Q | t}; (p CO q) \<in> Q; (INVARIANT i) \<in> Q \<rbrakk> \<Longrightarrow> \<Turnstile> {r} f {Q \<union> {p and i CO q and i} | t}"
  apply (clarsimp simp: valid_spec_def)
  apply (erule_tac x=s in allE, clarsimp)+
  apply (subgoal_tac "invariant i f s \<and> co p q f s"; clarsimp?)
   apply (drule invariant_all_reachable_sat)
   apply (clarsimp simp: reachable_sat_def co_def)
   apply (meson star_step1 star_trans)
   apply (clarsimp simp: co_def reachable_sat_def)
   apply (meson star_step1 star_trans)
  by fastforce

(* 
  an additional proof of the semi inheritance rule for invariants. the rule does not 
  actually exist in biloof as it is redundant.
*)
lemma invariant_inheritance_semi[simp]:
  "\<lbrakk> \<turnstile> {r} c\<^sub>1 {com_pre c\<^sub>2}; \<tturnstile> {r} c\<^sub>1 {Q | com_pre c\<^sub>2}; \<Turnstile> {r} c\<^sub>1 {Q | com_pre c\<^sub>2}; 
  (INVARIANT i) \<in> Q; \<turnstile> {com_pre c\<^sub>2} c\<^sub>2 {t}; \<tturnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q' | t}; 
  \<Turnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q' | t}; (INVARIANT i) \<in> Q' \<rbrakk> \<Longrightarrow> 
  \<Turnstile> {r} c\<^sub>1;;c\<^sub>2 {{INVARIANT i} | t}"
  apply (drule b_semi; simp?)
  apply (frule_tac r=r in biloof_no_perpetual_sound)
  apply (frule_tac f=c\<^sub>1 in invariant_elim, simp)
  apply (frule_tac f=c\<^sub>2 in invariant_elim, simp)
  by (frule_tac f="c\<^sub>1;;c\<^sub>2" in invariant_sound; simp)


subsection \<open>TRANSIENT\<close>

(* overapproximates the number of steps taken at most to reach an action *)
fun num_same_state :: "com \<Rightarrow> nat" where
  "num_same_state DONE = 1"
| "num_same_state ABORTED = 1"
| "num_same_state (\<lbrace>_\<rbrace> ACTION _) = 0"
| "num_same_state (c\<^sub>1;;c\<^sub>2) = num_same_state c\<^sub>1"
| "num_same_state (\<lbrace>_\<rbrace> IF _ THEN c\<^sub>1 ELSE c\<^sub>2) = 1 + max (num_same_state c\<^sub>1) (num_same_state c\<^sub>2)"
| "num_same_state (\<lbrace>_\<rbrace> \<lbrace>_\<rbrace> WHILE b i DO c) = 1 + num_same_state c"
| "num_same_state (PARALLEL Ps Ts) = sum_list (map num_same_state Ps)"
| "num_same_state (\<lbrace>_\<rbrace> POSTANN) = 0"

lemma is_path_0:
  "is_path path f s \<Longrightarrow> path 0 = (f, s)"
  by (simp add: is_path_def)

lemma is_path_subpath:
  "\<lbrakk> is_path path f s; path n = (f', s') \<rbrakk> \<Longrightarrow> is_path (\<lambda>i. path (n + i)) f' s'"
  by (clarsimp simp: is_path_def)

lemma is_path_star':
  "\<lbrakk> m \<le> n; \<forall>n. path n \<rightarrow> path (Suc n) \<rbrakk> \<Longrightarrow> path m \<rightarrow>* path n"
  apply (induct n arbitrary: m; simp)
  apply (case_tac "m=Suc n"; simp?)
  by (meson le_Suc_eq star.refl star.step star_trans)

lemma is_path_star: 
  "is_path path f s \<Longrightarrow> \<forall>m n. n \<ge> m \<longrightarrow> path m \<rightarrow>* path n"
  by (simp add: is_path_def is_path_star')

lemma is_path_one_step:
  "is_path path f s \<Longrightarrow> \<exists>f' s'. path 1 = (f', s') \<and> (f, s) \<rightarrow> (f', s')"
  apply (simp add: is_path_def)
  by (metis old.prod.exhaust)

(* derivability is preserved or the component is DONE *)
lemma derivable_one_step:
  "\<lbrakk> (f, s) \<rightarrow> (f', s'); \<turnstile> {r} f {t}; r s \<rbrakk> \<Longrightarrow> (\<exists>r' t'. \<turnstile> {r'} f' {t'} \<and> r' s') \<or> f' = DONE"
  apply (case_tac "f' = DONE"; simp)
  apply (frule derivable_implies_com_pre)
  apply (drule derivable_implies_com_pre_derivable)
  apply (frule com_pre_and_derivable_one_step; simp?)
  by blast

lemma derivable_star:
  "\<lbrakk> (f, s) \<rightarrow>* (f', s'); r s; \<turnstile> {r} f {t} \<rbrakk> \<Longrightarrow> (\<exists>r' t'. \<turnstile> {r'} f' {t'} \<and> r' s') \<or> f' = DONE"
  apply (induction arbitrary: r t rule: star_induct)
   apply fastforce
  apply (case_tac "ab = DONE"; simp)
  apply (frule_tac r=r and t=t in derivable_one_step; simp)
  by (metis done_star)

(* 
  if f goes to DONE (and f is not DONE), then it must be an action or
  a parallel composition that has one action. therefore, num_same_state = 0 
*)
lemma done_0_num_same_state:
  "\<lbrakk> (f, s) \<rightarrow> (f', s'); f' = DONE; \<turnstile> {r} f {t} \<rbrakk> \<Longrightarrow> num_same_state f = 0"
  apply (induction arbitrary: r t rule: small_step_induct; simp)
      apply (blast dest: done_elim)
     apply (blast dest: done_elim semi_elim)
    apply (blast dest: done_elim if_elim)
   apply (blast dest: done_elim if_elim)
  apply (frule par_elim; simp; clarsimp)
  by (metis in_set_conv_nth num_same_state.simps(8))

lemma num_same_state_parallel_one_step:
  "\<lbrakk> i < length Ps; Ps ! i = c; num_same_state c' < num_same_state c \<rbrakk> \<Longrightarrow> 
  num_same_state (PARALLEL Ps[i := c'] Ts) < num_same_state (PARALLEL Ps Ts)"
  apply (induction Ps arbitrary: i; simp)
  by (case_tac i; simp)

lemma num_same_state_one_component:
  "\<lbrakk> i < length Ps; Ps ! i = c; n < num_same_state c \<rbrakk> \<Longrightarrow> 
  n < num_same_state (PARALLEL Ps Ts)"
  apply (induction Ps arbitrary: i n c; simp)
  apply (case_tac i; simp)
  using trans_less_add2 by blast

lemma num_same_state_post_ann:
  "\<lbrakk> Suc 0 < num_same_state c; i < length Ps; Ps ! i = c \<rbrakk> \<Longrightarrow> 
  sum_list (map num_same_state (Ps[i := \<lbrace>Ts ! i\<rbrace> POSTANN])) < sum_list (map num_same_state Ps)"
  apply (induction Ps arbitrary: i c; simp)
  apply (case_tac i; simp)
  by (simp add: map_update)

(* whenever a component makes a step, either num_same_state decreases or (not p) holds *)
lemma num_same_state_decreases_or_not_p:
  "\<lbrakk> (f, s) \<rightarrow> (f', s'); \<turnstile> {r} f {t}; r s; p s;
  \<forall>a pre state_rel. a \<in> actions_of f \<longrightarrow> (pre, state_rel) = action_state_rel a \<longrightarrow>
  (\<forall>s. (pre and p) s \<longrightarrow> (\<exists>s'. (s, s') \<in> state_rel)) \<and> 
  (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> (pre and p) s \<longrightarrow> (not p) s') \<rbrakk> \<Longrightarrow> 
  num_same_state f > num_same_state f' \<or> (not p) s'"
  apply (induction arbitrary: r t rule: small_step_induct; simp)
         apply (simp add: derivable_implies_com_pre)
        apply (blast dest: done_elim)
       apply blast
      apply (metis done_0_num_same_state not_less_zero semi_elim)
     apply (meson semi_elim)
    apply (drule_tac x="com_pre (Ps ! i)" in meta_spec; drule_tac x="Ts ! i" in meta_spec)
    apply (drule meta_mp)
     apply (frule par_elim; simp)
     apply fastforce
    apply (metis Suc_lessD Suc_lessI and_map_com_pre_Ps1 in_set_conv_nth num_same_state.simps(7) num_same_state_one_component)
   apply (drule_tac x="com_pre (Ps ! i)" in meta_spec; drule_tac x="Ts ! i" in meta_spec)
   apply (drule meta_mp)
    apply (frule par_elim; simp)
    apply fastforce
   apply (metis Suc_lessD and_map_com_pre_Ps1 in_set_conv_nth num_same_state.simps(7) num_same_state.simps(8) num_same_state_parallel_one_step)
  apply (drule_tac x="com_pre (Ps ! i)" in meta_spec; drule_tac x="Ts ! i" in meta_spec)
  apply (drule meta_mp)
   apply (frule par_elim; simp)
   apply (metis Post_annE and_map_com_pre_Ps1 com_pre.simps(8))
  using and_map_com_pre_Ps1 num_same_state_parallel_one_step by fastforce

lemma eventually_not_p_num_same_state'':
  "\<lbrakk> (f, s) \<rightarrow> (f', s'); 
  \<And>f r t s.
    \<lbrakk> num_same_state f < n; \<turnstile> {r} f {t}; r s;
    \<forall>a pre state_rel. a \<in> actions_of f \<longrightarrow> (pre, state_rel) = action_state_rel a \<longrightarrow>
    (\<forall>s. (pre and p) s \<longrightarrow> (\<exists>s'. (s, s') \<in> state_rel)) \<and> 
    (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> (pre and p) s \<longrightarrow> (not p) s'); p s \<rbrakk> \<Longrightarrow> 
    \<forall>path. is_path path f s \<longrightarrow> (\<exists>i f'' s''. path i = (f'', s'') \<and> (not p) s'');
  num_same_state f < Suc n; \<turnstile> {r} f {t}; r s;
  \<forall>a pre state_rel. a \<in> actions_of f \<longrightarrow> (pre, state_rel) = action_state_rel a \<longrightarrow>
  (\<forall>s. (pre and p) s \<longrightarrow> (\<exists>s'. (s, s') \<in> state_rel)) \<and> 
  (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> (pre and p) s \<longrightarrow> (not p) s');
  p s; is_path path f s; path (Suc 0) = (f', s'); (f, s) \<rightarrow> (f', s') \<rbrakk> \<Longrightarrow> 
  \<exists>i f'' s''. path i = (f'', s'') \<and> (not p) s''"
  apply (frule_tac r=r and t=t in num_same_state_decreases_or_not_p; simp?)
  apply (erule disjE)
   prefer 2
   apply (rule_tac x="Suc 0" in exI; simp)
  apply (drule_tac x=f' in meta_spec; simp)
  apply (subgoal_tac "\<forall>path. is_path path f' s' \<longrightarrow> (\<exists>i f'' s''. path i = (f'', s'') \<and> (not p) s'')")
   apply (erule_tac x="\<lambda>i. path (Suc i)" in allE; simp?)
   apply (frule is_path_subpath; simp?; clarsimp)
   apply (rule_tac x="Suc i" in exI; clarsimp)
  apply (frule_tac r=r and t=t in derivable_one_step; simp?)
  apply (erule disjE; clarsimp)
   apply (drule_tac x=r' in meta_spec)
   apply (drule_tac x=t' in meta_spec)
   apply (drule_tac x=s' in meta_spec)
   apply (drule meta_mp; simp)
   apply (drule meta_mp)
    apply (rule_tac s=s and s'=s' in actions_of_subset; simp?)
   apply (meson is_path_0)
  by (simp add: done_0_num_same_state)

lemma eventually_not_p_num_same_state':
  "\<lbrakk> n > num_same_state f; \<turnstile> {r} f {t}; r s; p s;
  \<forall>a pre state_rel. a \<in> actions_of f \<longrightarrow> (pre, state_rel) = action_state_rel a \<longrightarrow>
  (\<forall>s. (pre and p) s \<longrightarrow> (\<exists>s'. (s, s') \<in> state_rel)) \<and> 
  (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> (pre and p) s \<longrightarrow> (not p) s') \<rbrakk> \<Longrightarrow>
  \<forall>path. is_path path f s \<longrightarrow> (\<exists>i f'' s''. path i = (f'', s'') \<and> (not p) s'')"
  apply (induction n arbitrary: f r t s; simp; clarsimp)
  apply (subgoal_tac "\<exists>f' s'. path 1 = (f', s') \<and> (f, s) \<rightarrow> (f', s')"; clarsimp)
  apply (frule_tac r=r and t=t in eventually_not_p_num_same_state'')
  using is_path_one_step by auto

(* added n > num_same_state f and apply induction on n *)
lemma eventually_not_p_num_same_state:
  "\<lbrakk> n > num_same_state f; \<turnstile> {r} f {t}; r s; p s;
  \<forall>a pre state_rel. a \<in> actions_of f \<longrightarrow> (pre, state_rel) = action_state_rel a \<longrightarrow>
  (\<forall>s. (pre and p) s \<longrightarrow> (\<exists>s'. (s, s') \<in> state_rel)) \<and> 
  (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> (pre and p) s \<longrightarrow> (not p) s'); is_path path f s \<rbrakk> \<Longrightarrow>
  \<exists>i f'' s''. path i = (f'', s'') \<and> (not p) s''"
  by (simp add: eventually_not_p_num_same_state')

lemma eventually_not_p:
  "\<lbrakk> \<turnstile> {r} f {t}; r s; p s;
  \<forall>a pre state_rel. a \<in> actions_of f \<longrightarrow> (pre, state_rel) = action_state_rel a \<longrightarrow>
  (\<forall>s. (pre and p) s \<longrightarrow> (\<exists>s'. (s, s') \<in> state_rel)) \<and> 
  (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> (pre and p) s \<longrightarrow> (not p) s');
  is_path path f s \<rbrakk> \<Longrightarrow>
  \<exists>i f'' s''. path i = (f'', s'') \<and> (not p) s''"
  apply (subgoal_tac "\<exists>n. n > num_same_state f"; clarsimp)
   apply (frule_tac r=r and t=t in eventually_not_p_num_same_state; simp?)
  by auto

lemma transient_basis_sound':
  "\<lbrakk> \<turnstile> {r} f {t}; r s;
  \<forall>a pre state_rel. a \<in> actions_of f \<longrightarrow> (pre, state_rel) = action_state_rel a \<longrightarrow>
  (\<forall>s. (pre and p) s \<longrightarrow> (\<exists>s'. (s, s') \<in> state_rel)) \<and> 
  (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> (pre and p) s \<longrightarrow> (not p) s') \<rbrakk> \<Longrightarrow> 
  transient p f s"
  apply (clarsimp simp: transient_def paths_def)
  apply (frule is_path_subpath; simp?)
  apply (subgoal_tac "(f, s) \<rightarrow>* (fa, sa)")
  apply (frule_tac s=s and f'=fa and s'=sa in derivable_star; simp)
   apply (erule disjE; clarsimp)
   apply (frule_tac f=fa and s=sa and p=p in eventually_not_p; simp?)
    apply (rule_tac f=f and s=s and f'=fa and s'=sa in actions_of_subset; simp)
   apply (meson le_add1)
  using is_path_0 is_path_star by auto

lemma transient_basis_sound[simp]:
  "\<lbrakk> \<tturnstile> {r} f {Q | t}; \<Turnstile> {r} f {Q | t};
  \<forall>a pre state_rel. a \<in> actions_of f \<longrightarrow> (pre, state_rel) = action_state_rel a \<longrightarrow>
  (\<forall>s. (pre and p) s \<longrightarrow> (\<exists>s'. (s, s') \<in> state_rel)) \<and> 
  (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> (pre and p) s \<longrightarrow> (not p) s') \<rbrakk> \<Longrightarrow> 
  \<Turnstile> {r} f {Q \<union> {TRANSIENT p} | t}"
  apply (clarsimp simp: valid_spec_def)
  apply (erule disjE; clarsimp)
  apply (frule biloof_to_biloof_no_perpetual; simp)
  by (clarsimp simp: transient_basis_sound')

lemma com_semi_com[dest]: 
  "f;;c\<^sub>2 = c\<^sub>2 \<Longrightarrow> False"
  by (metis One_nat_def add.commute com.size_gen(4) less_Suc_eq not_add_less2 plus_1_eq_Suc)

lemma one_step_semi:
  "\<lbrakk> (f;;c\<^sub>2, s) \<rightarrow> (f';;c\<^sub>2, s') \<rbrakk> \<Longrightarrow> (f, s) \<rightarrow> (f', s')" 
  by auto

(* if you always have (f;;c\<^sub>2), it means that c\<^sub>1 never terminates *)
lemma construct_path_from_semi_never_terminated:
  "\<lbrakk> is_path path (c\<^sub>1;;c\<^sub>2) s; (\<forall>i. \<exists>f s. path i = (f;;c\<^sub>2, s)) \<rbrakk> \<Longrightarrow>
  is_path (\<lambda>i. case path i of (c\<^sub>1';;c\<^sub>2, s) \<Rightarrow> (c\<^sub>1', s)) c\<^sub>1 s"
  apply (clarsimp simp: is_path_def)
  apply (frule_tac x=n in spec)
  apply (drule_tac x="Suc n" in spec; clarsimp)
  by (metis one_step_semi)

lemma one_step_semi_aborted:
  "\<lbrakk> (f;;c\<^sub>2, s) \<rightarrow> (ABORTED, s'); c\<^sub>2 \<noteq> ABORTED \<rbrakk> \<Longrightarrow> s = s' \<and> (f, s) \<rightarrow> (ABORTED, s)"
  apply (erule SemiE; simp)
  by (rule Abort; assumption)

lemma one_step_semi_done:
  "\<lbrakk> (f;;c\<^sub>2, s) \<rightarrow> (c\<^sub>2, s'); c\<^sub>2 \<noteq> ABORTED \<rbrakk> \<Longrightarrow> (f, s) \<rightarrow> (DONE, s')"
  by (metis (no_types, lifting) Pair_inject SemiE com_semi_com)

lemma semi_path_all_possible_cases':
  "\<lbrakk> is_path path (c\<^sub>1;;c\<^sub>2) s; \<forall>f s. (not (=) (path i)) (f;;c\<^sub>2, s) \<rbrakk> \<Longrightarrow>
  \<exists>n. (\<forall>i < n. \<exists>f s. path i = (f;;c\<^sub>2, s)) \<and> \<not> (\<exists>f' s'. path n = (f';;c\<^sub>2, s'))"
  apply (induction rule: nat_less_induct; simp)
  by blast

(* 
  the path for sequential composition is either
  - path i = (f';;c\<^sub>2, s) for all i ---- c\<^sub>1 never terminates
  - path i = (ABORTED;;c\<^sub>2, s) and path (Suc i) = (ABORTED, s) --- c\<^sub>1 goes to ABORTED
  - path i = (f';;c\<^sub>2, s) and path (Suc i) = (c\<^sub>2, s') ---- c\<^sub>2 goes to DONE
*)
lemma semi_path_all_possible_cases:
  "\<lbrakk> is_path path (c\<^sub>1;;c\<^sub>2) s; \<not> (\<forall>i. \<exists>f s. path i = (f;;c\<^sub>2, s)) \<rbrakk> \<Longrightarrow>
  (\<exists>n s'. n > 0 \<and> (\<forall>i < n. \<exists>f s. path i = (f;;c\<^sub>2, s)) \<and> path n = (ABORTED, s')) \<or>
  (\<exists>n s'. n > 0 \<and> (\<forall>i < n. \<exists>f s. path i = (f;;c\<^sub>2, s)) \<and> path n = (c\<^sub>2, s'))"
  apply clarsimp
  apply (frule semi_path_all_possible_cases'; simp; clarsimp)
  apply (rule_tac x=n in exI)
  apply (erule_tac x=n in allE; clarsimp)
  apply (subgoal_tac "n > 0"; simp?)
   apply (erule disjE, blast)
   apply (metis SemiE Suc_pred add.commute is_path_def lessI plus_1_eq_Suc)
  using is_path_0 less_linear by blast

lemma done_semi_one_step: 
  "(DONE;;c\<^sub>2, s) \<rightarrow> (f;;c\<^sub>2, s') \<Longrightarrow> False" 
  using done_one_step by auto

lemma aborted_semi_one_step: 
  "(ABORTED;;c\<^sub>2, s) \<rightarrow> (f;;c\<^sub>2, s') \<Longrightarrow> False"
  by (metis Pair_inject SemiE aborted_one_step com.distinct(17) com_pre.simps(2) com_semi_com false_def one_step_semi)

lemma is_path_never_terminated:
  "\<lbrakk> is_path path (c\<^sub>1;;c\<^sub>2) s; \<forall>i. \<exists>f s. path i = (f;;c\<^sub>2, s); 
  path' = (\<lambda>i. case path i of (c\<^sub>1';;c\<^sub>2, s) \<Rightarrow> (c\<^sub>1', s)); is_path path' c\<^sub>1 s \<rbrakk> \<Longrightarrow>
  \<not> path_will_terminate path'"
  apply (clarsimp simp: is_path_def path_will_terminate_def)
  apply (frule_tac x=i in spec)
  apply (drule_tac x="Suc i" in spec)
  apply clarsimp
  apply (rotate_tac 3)
  apply (frule_tac x=i in spec; clarsimp)
  apply (case_tac f; simp)
   apply (blast dest: done_semi_one_step)
  by (blast dest: aborted_semi_one_step)

lemma never_terminated_case:
  "\<lbrakk> transient p c\<^sub>1 s; is_path path (c\<^sub>1;;c\<^sub>2) s; path i = (f, sa); p sa; (not has_terminated) f;
   \<forall>i. \<exists>f s. path i = (f;;c\<^sub>2, s) \<rbrakk> \<Longrightarrow> 
  \<exists>j\<ge>i. \<exists>f' s'. path j = (f', s') \<and> ((not p) s' \<or> has_terminated f')"
  apply (simp add: transient_def paths_def)
  apply (frule construct_path_from_semi_never_terminated; simp?)
  apply (frule is_path_never_terminated; simp?)
  apply (erule_tac x="\<lambda>i. case path i of (c\<^sub>1';;c\<^sub>2, s) \<Rightarrow> (c\<^sub>1', s)" in allE)
  apply (clarsimp simp: path_will_terminate_def)
  apply (frule_tac x=i in spec; rotate_tac 5)
  apply (frule_tac x=i in spec; rotate_tac 2)
  apply (erule_tac x=i in allE; clarsimp)
  apply (frule_tac x=j in spec)
  apply (erule exE)+
  apply clarsimp
  apply (case_tac "(not p) s'"; clarsimp)
   apply blast
  apply (erule_tac x=j in allE)+
  by clarsimp

lemma paths_won't_aborted:
  "\<lbrakk> \<Turnstile> {r} f {Q | t}; is_path path f s; r s \<rbrakk> \<Longrightarrow> \<forall>i f' s'. path i = (f', s') \<longrightarrow> f' \<noteq> ABORTED"
  apply (drule not_aborted)
  apply (erule_tac x=s in allE; clarsimp)
  apply (clarsimp simp: is_path_def reachable_sat_def)
  by (metis is_path_star' less_eq_nat.simps(1))

lemma semi_path_star:
  "\<lbrakk> n > 0; \<forall>i<n. \<exists>f s. path i = (f;;c\<^sub>2, s); path 0 = (c\<^sub>1;;c\<^sub>2, s); \<forall>n. path n \<rightarrow> path (Suc n); 
  path (n - 1) = (f;;c\<^sub>2, sa) \<rbrakk> \<Longrightarrow> 
  (c\<^sub>1, s) \<rightarrow>* (f, sa)"
  apply (induction n arbitrary: c\<^sub>1 s f sa; simp)
  apply (case_tac n; simp)
  by (metis (no_types, lifting) lessI less_SucI one_step_semi star_step1 star_trans)

lemma pre_snd_com':
  "\<lbrakk> \<Turnstile> {r} c\<^sub>1 {Q | t}; r s; (c\<^sub>1, s) \<rightarrow>* (f, sa); (f, sa) \<rightarrow> (DONE, s') \<rbrakk> \<Longrightarrow> t s'"
  apply (simp add: valid_spec_def reachable_sat_def holds_def)
  by (meson has_terminated.simps(1) star.refl star.step star_trans)

(* in sequential composition, once the first component is DONE, the postcondition holds *)
lemma pre_snd_com:
  "\<lbrakk> \<Turnstile> {r} c\<^sub>1 {Q | t}; r s; is_path path (c\<^sub>1;;c\<^sub>2) s; 
  \<forall>i<n. \<exists>f s. path i = (f;;c\<^sub>2, s); n > 0; path n = (c\<^sub>2, s'); c\<^sub>2 \<noteq> ABORTED \<rbrakk> \<Longrightarrow>
  t s'"
  apply (simp add: is_path_def; clarsimp)
  apply (frule_tac x="n - 1" in spec)
  apply (erule impE, simp)
  apply (erule exE)+
  apply (frule_tac n=n and path=path in semi_path_star; simp)
  apply (frule not_aborted)
  apply (erule_tac x=s in allE; simp add: reachable_sat_def)
  by (metis Suc_pred one_step_semi_done pre_snd_com')

(* if all the paths of c\<^sub>1 terminate, then (c\<^sub>1;;c\<^sub>2, s) will get to (c\<^sub>2, s') *)
lemma always_terminate_path:
  "\<lbrakk> \<turnstile> {r} c\<^sub>1;;c\<^sub>2 {t}; r s; is_path path (c\<^sub>1;;c\<^sub>2) s; 
  \<forall>path. is_path path c\<^sub>1 s \<longrightarrow> path_will_terminate path \<rbrakk> \<Longrightarrow>
  \<exists>n s'. n > 0 \<and> (\<forall>i < n. \<exists>f s. path i = (f;;c\<^sub>2, s)) \<and> path n = (c\<^sub>2, s')"
  apply (case_tac "\<forall>i. \<exists>f s. path i = (f;;c\<^sub>2, s)")
   apply (frule construct_path_from_semi_never_terminated; simp?)
   apply (frule is_path_never_terminated; simp?)
   apply blast
  apply (case_tac "\<exists>n s'. n > 0 \<and> (\<forall>i < n. \<exists>f s. path i = (f;;c\<^sub>2, s)) \<and> path n = (c\<^sub>2, s')")
   apply simp
  by (metis (mono_tags, hide_lams) biloof_no_perpetual_sound paths_won't_aborted semi_path_all_possible_cases)

lemma terminated_case':
  "\<lbrakk> \<Turnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q' | t}; c\<^sub>2 \<noteq> DONE; (TRANSIENT p) \<in> Q'; 
  is_path path (c\<^sub>1;;c\<^sub>2) s; path i = (f, sa); p sa; (not has_terminated) f;
  0 < n; \<forall>i<n. \<exists>f s. path i = (f;;c\<^sub>2, s); path n = (c\<^sub>2, s'); com_pre c\<^sub>2 s' \<rbrakk> \<Longrightarrow> 
  \<exists>j\<ge>i. \<exists>f' s'. path j = (f', s') \<and> ((not p) s' \<or> has_terminated f')"
  apply (subgoal_tac "transient p c\<^sub>2 s'")
   defer
  using valid_spec_def apply fastforce
  apply (simp add: transient_def paths_def)
  apply (frule_tac n=n in is_path_subpath; simp?)
  apply (erule_tac x="\<lambda>i. path (n + i)" in allE; simp)
  apply (case_tac "i < n")
   apply (rotate_tac -2)
   apply (case_tac "(not p) s'")
  using less_imp_le_nat apply blast
   apply (erule_tac x=0 in allE; clarsimp)
   apply (metis com_pre.simps(2) false_def has_terminated.elims(2) le_add1 le_trans less_imp_le_nat)
  apply (erule_tac x="i - n" in allE; clarsimp)
  by (metis add.commute le_diff_conv)

lemma terminated_case:
  "\<lbrakk> \<turnstile> {r} c\<^sub>1;;c\<^sub>2 {t}; r s; \<Turnstile> {r} c\<^sub>1 {Q | com_pre c\<^sub>2};
  \<Turnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q' | t}; (TRANSIENT p) \<in> Q';
  is_path path (c\<^sub>1;;c\<^sub>2) s; path i = (f, sa); p sa; (not has_terminated) f;
  \<exists>n s'. 0 < n \<and> (\<forall>i<n. \<exists>f s. path i = (f;;c\<^sub>2, s)) \<and> path n = (c\<^sub>2, s') \<rbrakk> \<Longrightarrow> 
  \<exists>j\<ge>i. \<exists>f' s'. path j = (f', s') \<and> ((not p) s' \<or> has_terminated f')"
  apply clarsimp
  apply (frule_tac path=path and c\<^sub>2=c\<^sub>2 in pre_snd_com; simp?)
  apply (meson aborted_elim semi_elim)
  apply (frule_tac path=path and c\<^sub>2=c\<^sub>2 in terminated_case'; simp?)
  by (meson done_elim semi_elim)

lemma transient_sequencing_sound[simp]:
  "\<lbrakk> \<turnstile> {r} c\<^sub>1 {com_pre c\<^sub>2}; \<turnstile> {com_pre c\<^sub>2} c\<^sub>2 {t}; \<Turnstile> {r} c\<^sub>1 {Q | com_pre c\<^sub>2}; 
  \<forall>s. r s \<longrightarrow> (\<forall>path\<in>paths c\<^sub>1 s. path_will_terminate path);
  \<Turnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q' | t}; (TRANSIENT p) \<in> Q' \<rbrakk> \<Longrightarrow> 
  \<Turnstile> {r} c\<^sub>1;;c\<^sub>2 {{TRANSIENT p} | t}"
  apply (drule b_semi; simp?)
  apply (simp (no_asm) add: valid_spec_def; clarsimp)
  apply (rule conjI)
   apply (frule_tac r=r in biloof_no_perpetual_sound)
   apply (clarsimp simp: valid_spec_def)
  apply (simp (no_asm) add: transient_def paths_def; clarsimp)
  apply (frule always_terminate_path; simp add: paths_def)
   apply blast
  by (frule terminated_case; simp)

lemma transient_inheritance_semi':
  "\<lbrakk> \<turnstile> {r} c\<^sub>1;;c\<^sub>2 {t}; r s; \<Turnstile> {r} c\<^sub>1 {Q | com_pre c\<^sub>2}; (TRANSIENT p) \<in> Q;
  \<Turnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q' | t}; (TRANSIENT p) \<in> Q' \<rbrakk> \<Longrightarrow> 
  transient p (c\<^sub>1;;c\<^sub>2) s"
  apply (subgoal_tac "transient p c\<^sub>1 s")
   apply (simp (no_asm) add: transient_def paths_def; clarsimp)
   apply (case_tac "\<forall>i. \<exists>f s. path i = (f;;c\<^sub>2, s)")
  using never_terminated_case apply blast
   apply (case_tac "\<exists>n s'. n > 0 \<and> (\<forall>i < n. \<exists>f s. path i = (f;;c\<^sub>2, s)) \<and> path n = (c\<^sub>2, s')")
    apply (frule_tac Q'=Q' in terminated_case; simp)
   apply (metis (mono_tags, hide_lams) biloof_no_perpetual_sound paths_won't_aborted semi_path_all_possible_cases)
  using valid_spec_def by fastforce

lemma transient_inheritance_semi_sound[simp]:
  "\<lbrakk> \<turnstile> {r} c\<^sub>1 {com_pre c\<^sub>2}; \<turnstile> {com_pre c\<^sub>2} c\<^sub>2 {t}; \<Turnstile> {r} c\<^sub>1 {Q | com_pre c\<^sub>2}; 
  (TRANSIENT p) \<in> Q; \<Turnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q' | t}; (TRANSIENT p) \<in> Q' \<rbrakk> \<Longrightarrow> 
  \<Turnstile> {r} c\<^sub>1;;c\<^sub>2 {{TRANSIENT p} | t}"
  apply (drule b_semi; simp?)
  apply (simp (no_asm) add: valid_spec_def; clarsimp)
  apply (rule conjI)
   apply (frule_tac r=r in biloof_no_perpetual_sound)
   apply (clarsimp simp: valid_spec_def)
  by (rule_tac r=r and t=t and Q'=Q' in transient_inheritance_semi'; simp?)

lemma transient_inheritance_if_sound_if:
  "\<lbrakk> pre s; b s; com_pre c\<^sub>1 s; transient p c\<^sub>1 s \<rbrakk> \<Longrightarrow> 
  transient p (\<lbrace>pre\<rbrace> IF b THEN c\<^sub>1 ELSE c\<^sub>2) s"
  apply (clarsimp simp: transient_def paths_def)
  apply (subgoal_tac "path 1 = (c\<^sub>1, s)")
   apply (frule_tac n=1 in is_path_subpath; simp)
   apply (erule_tac x="(\<lambda>i. path (Suc i))" in allE; simp)
   apply (case_tac i; simp)
    apply (erule_tac x=0 in allE; simp; blast)
   apply (erule_tac x="i - 1" in allE; simp; blast)
  apply (simp add: is_path_def; clarsimp)
  apply (erule_tac x=0 in allE; simp)
  by (erule IfE; simp)

lemma transient_inheritance_if_sound_else:
  "\<lbrakk> pre s; \<not> b s; com_pre c\<^sub>2 s; transient p c\<^sub>2 s \<rbrakk> \<Longrightarrow> 
  transient p (\<lbrace>pre\<rbrace> IF b THEN c\<^sub>1 ELSE c\<^sub>2) s"
  apply (clarsimp simp: transient_def paths_def)
  apply (subgoal_tac "path 1 = (c\<^sub>2, s)")
   apply (frule_tac n=1 in is_path_subpath; simp)
   apply (erule_tac x="(\<lambda>i. path (Suc i))" in allE; simp)
   apply (case_tac i; simp)
    apply (erule_tac x=0 in allE; simp; blast)
   apply (erule_tac x="i - 1" in allE; simp; blast)
  apply (simp add: is_path_def; clarsimp)
  apply (erule_tac x=0 in allE; simp)
  by (erule IfE; simp)

lemma transient_inheritance_if_sound[simp]:
  "\<lbrakk> \<forall>s. (pre and b) s \<longrightarrow> com_pre c\<^sub>1 s; \<forall>s. (pre and not b) s \<longrightarrow> com_pre c\<^sub>2 s;
  \<turnstile> {com_pre c\<^sub>1} c\<^sub>1 {t}; \<turnstile> {com_pre c\<^sub>2} c\<^sub>2 {t}; 
  \<Turnstile> {com_pre c\<^sub>1} c\<^sub>1 {Q | t}; (TRANSIENT p) \<in> Q; 
  \<Turnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q' | t}; (TRANSIENT p) \<in> Q' \<rbrakk> \<Longrightarrow> 
  \<Turnstile> {pre} \<lbrace>pre\<rbrace> IF b THEN c\<^sub>1 ELSE c\<^sub>2 {{TRANSIENT p} | t}"
  apply (frule_tac c\<^sub>2=c\<^sub>2 in b_if; simp?)
  apply (simp (no_asm) add: valid_spec_def; clarsimp)
  apply (rule conjI)
   apply (frule_tac r=pre in biloof_no_perpetual_sound)
   apply (clarsimp simp: valid_spec_def)
  apply (case_tac "b s")
   apply (frule_tac c\<^sub>1=c\<^sub>1 and b=b and pre=pre in transient_inheritance_if_sound_if; simp?)
  using valid_spec_def apply fastforce
  apply (frule_tac c\<^sub>2=c\<^sub>2 and b=b and pre=pre in transient_inheritance_if_sound_else; simp?)
  using valid_spec_def by fastforce


subsection \<open>ENSURES\<close>

lemma ensures_eventually_q_or_terminated'':
  "\<lbrakk> co (p and not q) (p or q) f s; is_path path f s; path (Suc j) = (f', s'); i \<le> j;
  (not p) s'; path j = (fb, sb); p sb; (not q) sb; (not has_terminated) fb \<rbrakk> \<Longrightarrow> 
  \<exists>j\<ge>i. \<exists>f' s'. path j = (f', s') \<and> (p s' \<and> has_terminated f' \<or> q s')"
  apply (simp add: co_def reachable_sat_def holds_def)
  apply (erule_tac x=fb in allE; erule_tac x=sb in allE)
  apply (frule is_path_star)
  apply (erule_tac x=0 in allE; erule_tac x=j in allE)
  apply (simp add: is_path_0)
  apply (clarsimp simp: is_path_def)
  by (metis le_SucI)

lemma ensures_eventually_q_or_terminated':
  "\<lbrakk> co (p and not q) (p or q) f s; is_path path f s; path i = (fa, sa); p sa; (not q) sa; 
  (not has_terminated) fa; i \<le> j; path j = (f', s'); (not p) s' \<rbrakk> \<Longrightarrow> 
  \<exists>j\<ge>i. \<exists>f' s'. path j = (f', s') \<and> (p s' \<and> has_terminated f' \<or> q s')"
  apply (induct j arbitrary: f' s' i fa sa; simp)
  apply (case_tac "i = Suc j"; clarsimp?)
  apply (subgoal_tac "i \<le> j"; simp)
  apply (subgoal_tac "\<exists>f s. path j = (f, s)")
  apply (erule exE)+
   apply (case_tac "p sb"; simp)
   apply (case_tac "q sb", blast)
   apply (case_tac "has_terminated fb", blast)
   apply (simp add: ensures_eventually_q_or_terminated'')
  by simp

lemma ensures_eventually_q_or_terminated:
  "\<lbrakk> co (p and not q) (p or q) f s; transient (p and not q) f s; path \<in> paths f s; 
  path i = (fa, sa); p sa \<rbrakk> \<Longrightarrow> 
  \<exists>j\<ge>i. \<exists>f' s'. path j = (f', s') \<and> (p s' \<and> has_terminated f' \<or> q s')"
  apply (simp add: transient_def paths_def)
  apply (erule_tac x=path in allE; simp)
  apply (erule_tac x=i in allE; simp)
  apply (case_tac "q sa", blast)
  apply (case_tac "has_terminated fa", blast)
  apply clarsimp
  apply (case_tac "p s'", blast)
  by (simp add: ensures_eventually_q_or_terminated')

lemma ensures_next_step_p_or_q:
  "\<lbrakk> co (p and not q) (p or q) f s; transient (p and not q) f s; path \<in> paths f s; 
  path i = (fa, sa); p sa; (not q) sa \<rbrakk> \<Longrightarrow> 
  \<exists>f' s'. path (Suc i) = (f', s') \<and> (p or q) s'"
  apply (simp add: co_def reachable_sat_def paths_def)
  apply (erule_tac x=fa in allE; erule_tac x=sa in allE)
  apply (frule is_path_star)
  apply (erule_tac x=0 in allE; erule_tac x=i in allE)
  apply (clarsimp simp: is_path_0)
  apply (subgoal_tac "\<exists>f s. path (Suc i) = (f, s)")
   apply (erule exE)+
   apply (erule_tac x=fb in allE; erule_tac x=sb in allE)
   apply (simp add: is_path_def; clarsimp)
   apply (erule_tac x=i in allE; simp)
  by clarsimp

lemma co_transient_implies_ensures:
  "\<lbrakk> co (p and not q) (p or q) f s; transient (p and not q) f s \<rbrakk> \<Longrightarrow> 
  ensures p q f s"
  by (clarsimp simp: ensures_def ensures_next_step_p_or_q ensures_eventually_q_or_terminated)

lemma ensures_sound[simp]:
  "\<lbrakk> \<Turnstile> {r} f {Q | t}; (p and not q CO p or q) \<in> Q; (TRANSIENT p and not q) \<in> Q \<rbrakk> \<Longrightarrow> 
  \<Turnstile> {r} f {Q \<union> {p EN q} | t}"
  apply (clarsimp simp: valid_spec_def)
  apply (erule disjE; clarsimp)
  apply (erule_tac x=s in allE; clarsimp)
  apply (subgoal_tac "co (p and not q) (p or q) f s \<and> transient (p and not q) f s"; clarsimp?)
   apply (simp add: co_transient_implies_ensures)
  by auto


subsection \<open>LEADS-TO\<close>

lemma leads_to_ensures_sound[simp]:
  "\<lbrakk> \<Turnstile> {r} f {Q | t}; (p EN q) \<in> Q \<rbrakk> \<Longrightarrow> \<Turnstile> {r} f {Q \<union> {p \<mapsto> q} | t}"
  apply (clarsimp simp: valid_spec_def)
  apply (erule disjE; simp)
  apply (erule_tac x=s in allE; clarsimp)
  apply (subgoal_tac "ensures p q f s")
   apply (clarsimp simp: leads_to_def ensures_def)
   apply blast
  by auto

lemma leads_to_transitive_sound[simp]:
  "\<lbrakk> \<Turnstile> {r} f {Q | t}; (p \<mapsto> q) \<in> Q; (q \<mapsto> r) \<in> Q \<rbrakk> \<Longrightarrow> \<Turnstile> {r} f {Q \<union> {p \<mapsto> r} | t}"
  apply (clarsimp simp: valid_spec_def)
  apply (erule disjE; simp)
  apply (erule_tac x=s in allE; clarsimp)
  apply (subgoal_tac "leads_to p q f s \<and> leads_to q r f s")
   defer
   apply auto[1]
  apply (clarsimp simp: leads_to_def paths_def)
  apply (erule_tac x=path in allE; clarsimp)+
  apply (erule_tac x=i in allE; clarsimp)
  apply (case_tac "has_terminated f'"; simp)
   apply blast
  apply (erule_tac x=j in allE; clarsimp)
  using le_trans by blast

lemma leads_to_disjunction':
  "\<forall>p\<in>set S. leads_to p q f s \<Longrightarrow> leads_to (Or S) q f s"
  apply (induct S; clarsimp)
   apply (simp add: leads_to_def false_def)
  using leads_to_def false_def by auto

lemma leads_to_disjunction_sound[simp]:
  "\<lbrakk> \<Turnstile> {r} f {Q | t}; \<forall>p\<in>set S. (p \<mapsto> q) \<in> Q \<rbrakk> \<Longrightarrow> \<Turnstile> {r} f {Q \<union> {(Or S) \<mapsto> q} | t}"
  apply (clarsimp simp: valid_spec_def)
  apply (erule disjE; simp)
  apply (erule_tac x=s in allE; clarsimp)
  apply (subgoal_tac "\<forall>p\<in>set S. leads_to p q f s")
   apply (simp add: leads_to_disjunction')
  by fastforce

subsection \<open>Soundness of Everything\<close>

lemma biloof_sound:
  "\<tturnstile> {r} f {Q | t} \<Longrightarrow> \<Turnstile> {r} f {Q | t}"
  by (induction rule: biloof.induct; clarsimp)
 
end