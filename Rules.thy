theory Rules imports Local begin

section \<open>Formalisation of Proof Rules\<close>

text \<open>
  These proof rules are stratified into two layers. The first layer concerns about
  rules that do not involve perpetual properties. The second layer includes rules
  that mention perpetual properties as well as the rules from the first layer.
\<close>

subsection \<open>First Layer: @{term biloof_no_perpetual}\<close>

inductive biloof_no_perpetual:: "ann \<Rightarrow> com \<Rightarrow> ann \<Rightarrow> bool" ("\<turnstile> {_} _ {_}" [0, 0, 0] 61) where
  b_action[intro]: 
  "\<lbrakk> \<forall>s s'. (s, s') \<in> state_rel \<and> pre s \<longrightarrow> t s' \<rbrakk> \<Longrightarrow>
  \<turnstile> {pre} \<lbrace>pre\<rbrace> ACTION state_rel {t}"

| b_semi[intro]:
  "\<lbrakk> \<turnstile> {r} c\<^sub>1 {com_pre c\<^sub>2}; \<turnstile> {com_pre c\<^sub>2} c\<^sub>2 {t} \<rbrakk> \<Longrightarrow> \<turnstile> {r} c\<^sub>1;;c\<^sub>2 {t}"

| b_if[intro]:
  "\<lbrakk> \<forall>s. (pre and b) s \<longrightarrow> com_pre c\<^sub>1 s; \<forall>s. (pre and not b) s \<longrightarrow> com_pre c\<^sub>2 s;
  \<turnstile> {com_pre c\<^sub>1} c\<^sub>1 {t}; \<turnstile> {com_pre c\<^sub>2} c\<^sub>2 {t} \<rbrakk> \<Longrightarrow> 
  \<turnstile> {pre} \<lbrace>pre\<rbrace> IF b THEN c\<^sub>1 ELSE c\<^sub>2 {t}"

| b_while[intro]:
  "\<lbrakk> \<forall>s. pre s \<longrightarrow> i s; \<forall>s. (i and b) s \<longrightarrow> com_pre c s; \<turnstile> {com_pre c} c {i};
  \<forall>s. (not b) s \<longrightarrow> (not local_b) s; \<forall>s. (i and not local_b) s \<longrightarrow> t s \<rbrakk> \<Longrightarrow>
  \<turnstile> {pre} \<lbrace>pre\<rbrace> \<lbrace>local_b\<rbrace> WHILE b i DO c {t}"

| b_par:
  "\<lbrakk> valid_ann Ps Ts; length Ps = length Ts; length Ps > 0; 
  \<forall>i<length Ps. \<turnstile> {com_pre (Ps!i)} Ps!i {Ts!i} \<or> Ps!i = \<lbrace>Ts!i\<rbrace> POSTANN;  
  \<exists>i<length Ps. Ps!i \<noteq> \<lbrace>Ts!i\<rbrace> POSTANN \<rbrakk> \<Longrightarrow>
  \<turnstile> {com_pre (PARALLEL Ps Ts)} PARALLEL Ps Ts {And Ts}"

| b_strengthen_weaken:
  "\<lbrakk> \<turnstile> {r} f {t}; \<forall>s. r' s \<longrightarrow> r s; \<forall>s. t s \<longrightarrow> t' s  \<rbrakk> \<Longrightarrow> \<turnstile> {r'} f {t'}"

| b_conjunction:
  "\<lbrakk> \<turnstile> {r} f {t}; \<turnstile> {r'} f {t'} \<rbrakk> \<Longrightarrow> \<turnstile> {r and r'} f {t and t'}"

| b_disjunction:
  "\<lbrakk> \<turnstile> {r} f {t}; \<turnstile> {r'} f {t'} \<rbrakk> \<Longrightarrow> \<turnstile> {r or r'} f {t or t'}"


subsection \<open>Second Layer: @{term biloof}\<close>

primrec Or :: "ann list \<Rightarrow> ann" where
  "Or [] = false"
| "Or (p # ps) = (p or Or ps)"

inductive biloof:: "ann \<Rightarrow> com \<Rightarrow> perpetual set \<Rightarrow> ann \<Rightarrow> bool" ("\<tturnstile> {_} _ {_ | _}" [0, 0, 0, 0] 61) where
  bl_biloof_no_perpetual:
  "\<turnstile> {r} f {t} \<Longrightarrow> \<tturnstile> {r} f {{} | t}"

| bl_strengthen_weaken:
  "\<lbrakk> \<tturnstile> {r} f {Q | t}; \<forall>s. r' s \<longrightarrow> r s; Q' \<subseteq> Q; \<forall>s. t s \<longrightarrow> t' s  \<rbrakk> \<Longrightarrow>
  \<tturnstile> {r'} f {Q' | t'}"

| bl_conjunction:
  "\<lbrakk> \<tturnstile> {r} f {Q | t}; \<tturnstile> {r'} f {Q' | t'} \<rbrakk> \<Longrightarrow> \<tturnstile> {r and r'} f {Q \<union> Q' | t and t'}"

| bl_disjunction:
  "\<lbrakk> \<tturnstile> {r} f {Q | t}; \<tturnstile> {r'} f {Q' | t'} \<rbrakk> \<Longrightarrow> \<tturnstile> {r or r'} f {Q \<inter> Q' | t or t'}"

| b_co:
  "\<lbrakk> \<tturnstile> {r} f {Q | t}; \<forall>s. p s \<longrightarrow> q s;
  \<forall>a pre state_rel. a \<in> actions_of f \<longrightarrow> (pre, state_rel) = action_state_rel a
  \<longrightarrow> (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> (pre and p) s \<longrightarrow> q s') \<rbrakk> \<Longrightarrow>
  \<tturnstile> {r} f {Q \<union> {p CO q} | t}"

| b_co_inheritance_semi:
  "\<lbrakk> \<turnstile> {r} c\<^sub>1 {com_pre c\<^sub>2}; \<turnstile> {com_pre c\<^sub>2} c\<^sub>2 {t}; 
  \<tturnstile> {r} c\<^sub>1 {Q | com_pre c\<^sub>2}; (p CO q) \<in> Q; 
  \<tturnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q'| t}; (p CO q) \<in> Q' \<rbrakk> \<Longrightarrow> 
  \<tturnstile> {r} c\<^sub>1;;c\<^sub>2 {{p CO q} | t}"

| b_co_inheritance_if:
  "\<lbrakk> \<forall>s. (pre and b) s \<longrightarrow> com_pre c\<^sub>1 s; \<forall>s. (pre and not b) s \<longrightarrow> com_pre c\<^sub>2 s;
  \<turnstile> {com_pre c\<^sub>1} c\<^sub>1 {t}; \<turnstile> {com_pre c\<^sub>2} c\<^sub>2 {t}; \<tturnstile> {com_pre c\<^sub>1} c\<^sub>1 {Q | t}; 
  (p CO q) \<in> Q; \<tturnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q'| t}; (p CO q) \<in> Q' \<rbrakk> \<Longrightarrow>
  \<tturnstile> {pre} \<lbrace>pre\<rbrace> IF b THEN c\<^sub>1 ELSE c\<^sub>2 {{p CO q} | t}"

| b_co_inheritance_while:
  "\<lbrakk> \<forall>s. pre s \<longrightarrow> i s; \<forall>s. (i and b) s \<longrightarrow> com_pre c s; 
  \<turnstile> {com_pre c} c {i}; \<tturnstile> {com_pre c} c {Q | t}; (p CO q) \<in> Q;
  \<forall>s. (not b) s \<longrightarrow> (not local_b) s; \<forall>s. (i and not local_b) s \<longrightarrow> t s \<rbrakk> \<Longrightarrow>
  \<tturnstile> {pre} \<lbrace>pre\<rbrace> \<lbrace>local_b\<rbrace> WHILE b i DO c {{p CO q} | t}"

| b_co_inheritance_parallel:
  "\<lbrakk> valid_ann Ps Ts; length Ps = length Ts; length Ts = length Qs; 
  length Ps > 0; \<forall>i. i < length Ps \<longrightarrow> \<turnstile> {com_pre (Ps!i)} Ps!i {Ts!i}; 
  \<forall>i. i < length Ps \<longrightarrow> \<tturnstile> {com_pre (Ps!i)} Ps!i {Qs!i | Ts!i}; 
  \<forall>i. i < length Qs \<longrightarrow> (p CO q) \<in> (Qs!i) \<rbrakk>
  \<Longrightarrow> \<tturnstile> {com_pre (PARALLEL Ps Ts)} PARALLEL Ps Ts {{p CO q} | And Ts}"

| b_invariant:
  "\<lbrakk> \<tturnstile> {r} f {Q | t}; \<forall>s. r s \<longrightarrow> i s;
  \<forall>a pre state_rel. a \<in> actions_of f \<longrightarrow> (pre, state_rel) = action_state_rel a
  \<longrightarrow> (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> (pre and i) s \<longrightarrow> i s') \<rbrakk> \<Longrightarrow>
   \<tturnstile> {r} f {Q \<union> {INVARIANT i} | t}"

| b_invariant_pre_post:
  "\<lbrakk> \<tturnstile> {r} f {Q | t}; (INVARIANT i) \<in> Q \<rbrakk> \<Longrightarrow> \<tturnstile> {r and i} f {Q | t and i}"

| b_invariant_co:
  "\<lbrakk> \<tturnstile> {r} f {Q | t}; (p CO q) \<in> Q; (INVARIANT i) \<in> Q \<rbrakk> \<Longrightarrow> 
  \<tturnstile> {r} f {Q \<union> {p and i CO q and i} | t}"

| b_transient_basis:
  "\<lbrakk> \<tturnstile> {r} f {Q | t};
  \<forall>a pre state_rel. a \<in> actions_of f \<longrightarrow> (pre, state_rel) = action_state_rel a
  \<longrightarrow> (\<forall>s. (pre and p) s \<longrightarrow> (\<exists>s'. (s, s') \<in> state_rel)) \<and> 
  (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> (pre and p) s \<longrightarrow> (not p) s') \<rbrakk> \<Longrightarrow>
  \<tturnstile> {r} f {Q \<union> {TRANSIENT p} | t}"

| b_transient_sequencing:
  "\<lbrakk> \<turnstile> {r} c\<^sub>1 {com_pre c\<^sub>2}; \<turnstile> {com_pre c\<^sub>2} c\<^sub>2 {t}; \<tturnstile> {r} c\<^sub>1 {Q | com_pre c\<^sub>2};
  \<forall>s. r s \<longrightarrow> (\<forall>path\<in>paths c\<^sub>1 s. path_will_terminate path);
  \<tturnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q'| t}; (TRANSIENT p) \<in> Q' \<rbrakk> \<Longrightarrow>
  \<tturnstile> {r} c\<^sub>1;;c\<^sub>2 {{TRANSIENT p} | t}"

| b_transient_inheritance_semi:
  "\<lbrakk> \<turnstile> {r} c\<^sub>1 {com_pre c\<^sub>2}; \<turnstile> {com_pre c\<^sub>2} c\<^sub>2 {t}; \<tturnstile> {r} c\<^sub>1 {Q | com_pre c\<^sub>2}; 
  (TRANSIENT p) \<in> Q; \<tturnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q'| t}; (TRANSIENT p) \<in> Q' \<rbrakk> \<Longrightarrow>
  \<tturnstile> {r} c\<^sub>1;;c\<^sub>2 {{TRANSIENT p} | t}"

| b_transient_inheritance_if:
  "\<lbrakk> \<forall>s. (pre and b) s \<longrightarrow> com_pre c\<^sub>1 s; \<forall>s. (pre and not b) s \<longrightarrow> com_pre c\<^sub>2 s;
  \<turnstile> {com_pre c\<^sub>1} c\<^sub>1 {t}; \<turnstile> {com_pre c\<^sub>2} c\<^sub>2 {t}; \<tturnstile> {com_pre c\<^sub>1} c\<^sub>1 {Q | t}; 
  (TRANSIENT p) \<in> Q; \<tturnstile> {com_pre c\<^sub>2} c\<^sub>2 {Q'| t}; (TRANSIENT p) \<in> Q' \<rbrakk> \<Longrightarrow>
  \<tturnstile> {pre} \<lbrace>pre\<rbrace> IF b THEN c\<^sub>1 ELSE c\<^sub>2 {{TRANSIENT p} | t}"

| b_ensures:
  "\<lbrakk> \<tturnstile> {r} f {Q | t}; ((p and not q) CO (p or q)) \<in> Q; 
  (TRANSIENT (p and not q)) \<in> Q \<rbrakk> \<Longrightarrow>
  \<tturnstile> {r} f {Q \<union> {p EN q} | t}"

| b_leads_to_ensures:
  "\<lbrakk> \<tturnstile> {r} f {Q | t}; (p EN q) \<in> Q \<rbrakk> \<Longrightarrow> \<tturnstile> {r} f {Q \<union> {p \<mapsto> q} | t}"

| b_leads_to_transitive:
  "\<lbrakk> \<tturnstile> {r} f {Q | t}; (p \<mapsto> q) \<in> Q; (q \<mapsto> r) \<in> Q \<rbrakk> \<Longrightarrow> 
  \<tturnstile> {r} f {Q \<union> {p \<mapsto> r} | t}"

| b_leads_to_disjunction:
  "\<lbrakk> \<tturnstile> {r} f {Q | t}; \<forall>p\<in>set S. (p \<mapsto> q) \<in> Q \<rbrakk> \<Longrightarrow> 
  \<tturnstile> {r} f {Q \<union> {(Or S) \<mapsto> q} | t}"


subsection \<open>Elimination Rules\<close>

declare Un_insert_right[simp del]

lemma and_pre: "\<turnstile> {r and r} c {t} \<Longrightarrow>  \<turnstile> {r} c {t}" by auto
lemma and_post: "\<turnstile> {r} c {t and t} \<Longrightarrow>  \<turnstile> {r} c {t}" by auto

lemma or_pre: "\<turnstile> {r or r} c {t} \<Longrightarrow>  \<turnstile> {r} c {t}" by auto
lemma or_post: "\<turnstile> {r} c {t or t} \<Longrightarrow>  \<turnstile> {r} c {t}" by auto

lemma derivable_implies_com_pre:
  "\<lbrakk> \<turnstile> {r} f {t} \<rbrakk> \<Longrightarrow> \<forall>s. r s \<longrightarrow> com_pre f s"
  by (induction rule: biloof_no_perpetual.induct; clarsimp)

lemma derivable_implies_com_pre_derivable:
  "\<turnstile> {r} f {t} \<Longrightarrow> \<turnstile> {com_pre f} f {t}"
  apply (induction rule: biloof_no_perpetual.induct; auto?)
     apply (frule b_par; simp)
     apply blast
  by (auto intro: b_strengthen_weaken b_conjunction b_disjunction)

lemma invariant_elim:  
  "\<lbrakk> \<tturnstile> {r} f {Q | t}; (INVARIANT i) \<in> Q \<rbrakk> \<Longrightarrow>
  (\<forall>a pre state_rel. a \<in> actions_of f \<longrightarrow> (pre, state_rel) = action_state_rel a
  \<longrightarrow> (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> (pre and i) s \<longrightarrow> i s')) \<and> (\<forall>s. r s \<longrightarrow> i s)"
  apply (induction arbitrary: i rule: biloof.induct; clarsimp)
  by fastforce+

lemma co_elim:  
  "\<lbrakk> \<tturnstile> {r} f {Q | t}; (p CO q) \<in> Q \<rbrakk> \<Longrightarrow>
  (\<forall>a pre state_rel. a \<in> actions_of f \<longrightarrow> (pre, state_rel) = action_state_rel a
  \<longrightarrow> (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> (pre and p) s \<longrightarrow> q s')) \<and> (\<forall>s. p s \<longrightarrow> q s)"
  apply (induction arbitrary: p q rule: biloof.induct; clarsimp)
                 prefer 8
                 apply auto[1]
                  apply (simp add: in_set_conv_nth; meson)
                 prefer 11
                 apply (meson invariant_elim)
  by fastforce+

lemma post_ann_elim:
  "\<lbrakk> \<turnstile> {r} f {t}; f = \<lbrace>pre\<rbrace> POSTANN \<rbrakk> \<Longrightarrow> False"
  by (induction rule: biloof_no_perpetual.induct, auto)
  
lemma aborted_elim:
  "\<lbrakk> \<turnstile> {r} f {t}; f = ABORTED \<rbrakk> \<Longrightarrow> False"
  by (induction rule: biloof_no_perpetual.induct, auto)

lemma done_elim:
  "\<lbrakk> \<turnstile> {r} f {t}; f = DONE \<rbrakk> \<Longrightarrow> False"
  by (induction rule: biloof_no_perpetual.induct, auto)

lemma action_elim:
  "\<lbrakk> \<turnstile> {r} f {t}; f = \<lbrace>pre\<rbrace> ACTION state_rel \<rbrakk> \<Longrightarrow> 
  \<forall>s s'. (s, s') \<in> state_rel \<and> r s \<longrightarrow> t s'"
  apply (induction rule: biloof_no_perpetual.induct; clarsimp)
  by (blast intro: b_strengthen_weaken)+

lemma semi_elim:
  "\<lbrakk> \<turnstile> {r} f {t}; f = c\<^sub>1;;c\<^sub>2 \<rbrakk> \<Longrightarrow> \<turnstile> {r} c\<^sub>1 {com_pre c\<^sub>2} \<and> \<turnstile> {com_pre c\<^sub>2} c\<^sub>2 {t}"
  apply (induction rule: biloof_no_perpetual.induct; clarsimp)
    apply (blast intro: b_strengthen_weaken)
   apply (blast intro: and_pre and_post b_conjunction)
  by (blast intro: or_pre or_post b_disjunction)

lemma if_elim:
  "\<lbrakk> \<turnstile> {r} f {t}; f = \<lbrace>pre\<rbrace> IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<rbrakk> \<Longrightarrow> 
  (\<forall>s. (r and b) s \<longrightarrow> com_pre c\<^sub>1 s) \<and> (\<forall>s. (r and not b) s \<longrightarrow> com_pre c\<^sub>2 s) \<and>
  \<turnstile> {com_pre c\<^sub>1} c\<^sub>1 {t} \<and> \<turnstile> {com_pre c\<^sub>2} c\<^sub>2 {t}"
  apply (induction rule: biloof_no_perpetual.induct; clarsimp)
    apply (blast intro: b_strengthen_weaken)
   apply (blast intro: and_pre and_post b_conjunction)
  by (blast intro: or_pre or_post b_disjunction)

lemma while_elim:
  "\<lbrakk> \<turnstile> {r} f {t}; f = \<lbrace>pre\<rbrace> \<lbrace>local_b\<rbrace> WHILE b i DO c \<rbrakk> \<Longrightarrow> 
  (\<forall>s. r s \<longrightarrow> i s) \<and> (\<forall>s. (i and b) s \<longrightarrow> com_pre c s) \<and>
  \<turnstile> {com_pre c} c {i} \<and> (\<forall>s. (not b) s \<longrightarrow> (not local_b) s) \<and> (\<forall>s. (i and not local_b) s \<longrightarrow> t s)"
  by (induction rule: biloof_no_perpetual.induct; clarsimp)

lemma par_elim:
  "\<lbrakk> \<turnstile> {r} f {t}; f = PARALLEL Ps Ts \<rbrakk> \<Longrightarrow> 
  valid_ann Ps Ts \<and> length Ps = length Ts \<and> length Ps > 0 \<and>
  (\<forall>s. r s \<longrightarrow> (And (map com_pre Ps)) s) \<and>
  (\<forall>i. i < length Ps \<longrightarrow> \<turnstile> {com_pre (Ps!i)} Ps!i {Ts!i} \<or> Ps!i = \<lbrace>Ts!i\<rbrace> POSTANN) \<and>
  (\<exists>i. i < length Ps \<longrightarrow> Ps!i \<noteq> \<lbrace>Ts!i\<rbrace> POSTANN) \<and>
  (\<forall>s. And Ts s \<longrightarrow> t s)"
  apply (induction rule: biloof_no_perpetual.induct; clarsimp)
   apply blast
  by auto

lemma biloof_to_biloof_no_perpetual:
  "\<lbrakk> \<tturnstile> {r} f {Q | t}; r s \<rbrakk> \<Longrightarrow> \<exists>r' t'. \<turnstile> {r'} f {t'} \<and> r' s"
  apply (induction arbitrary: s rule: biloof.induct; simp?)
          prefer 6
          apply (metis b_par com_pre.simps(7) length_greater_0_conv post_ann_elim)
  by blast+
  
end