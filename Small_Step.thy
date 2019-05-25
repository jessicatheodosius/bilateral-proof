theory Small_Step
  imports Com "~~/src/HOL/IMP/Star"  
begin

subsection \<open>Small-Step Semantics\<close>

primrec And :: "ann list \<Rightarrow> ann" where
  "And [] = true"
| "And (p # ps) = (p and And ps)"

text \<open>Retrieve local annotations of a component\<close>
fun com_pre :: "com \<Rightarrow> ann" where
  "com_pre DONE = true"
| "com_pre ABORTED = false"
| "com_pre (\<lbrace>pre\<rbrace> ACTION _) = pre"
| "com_pre (c\<^sub>1;;_) = com_pre c\<^sub>1"
| "com_pre (\<lbrace>pre\<rbrace> IF _ THEN _ ELSE _) = pre"
| "com_pre (\<lbrace>pre\<rbrace> \<lbrace>local_b\<rbrace> WHILE _ _ DO _) = pre"
| "com_pre (PARALLEL Ps Ts) = And (map com_pre Ps)"
| "com_pre (\<lbrace>pre\<rbrace> POSTANN) = pre"


subsubsection \<open>Semantics\<close>

inductive small_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>" 55) where
  Abort:   "\<not> com_pre c s \<Longrightarrow> (c, s) \<rightarrow> (ABORTED, s)"

| DoneR:   "(DONE, s) \<rightarrow> (DONE, s)"

| Action:  "\<lbrakk> (s, s') \<in> state_rel; pre s \<rbrakk> \<Longrightarrow> 
           (\<lbrace>pre\<rbrace> ACTION state_rel, s) \<rightarrow> (DONE, s')"
| ActionR: "\<lbrakk> \<forall>s'. (s, s') \<notin> state_rel; pre s \<rbrakk> \<Longrightarrow> 
           (\<lbrace>pre\<rbrace> ACTION state_rel, s) \<rightarrow> (\<lbrace>pre\<rbrace> ACTION state_rel, s)"

| Semi1:   "\<lbrakk> (c\<^sub>1, s) \<rightarrow> (DONE, s') \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s) \<rightarrow> (c\<^sub>2, s')"
| Semi2:   "\<lbrakk> (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s'); com_pre c\<^sub>1 s; c\<^sub>1' \<noteq> DONE \<rbrakk> \<Longrightarrow> 
           (c\<^sub>1;;c\<^sub>2, s) \<rightarrow> (c\<^sub>1';;c\<^sub>2, s')"
  
| IfT:     "\<lbrakk> b s; pre s \<rbrakk> \<Longrightarrow> (\<lbrace>pre\<rbrace> IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> (c\<^sub>1, s)"
| IfF:     "\<lbrakk> \<not> b s; pre s \<rbrakk> \<Longrightarrow> (\<lbrace>pre\<rbrace> IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> (c\<^sub>2, s)" 

| WhileT:  "\<lbrakk> b s; pre s \<rbrakk> \<Longrightarrow> 
           (\<lbrace>pre\<rbrace> \<lbrace>local_b\<rbrace> WHILE b i DO c, s) \<rightarrow> 
           (c;;\<lbrace>i\<rbrace> \<lbrace>local_b\<rbrace> WHILE b i DO c, s)"
| WhileF:  "\<lbrakk> \<not> b s; pre s \<rbrakk> \<Longrightarrow> 
           (\<lbrace>pre\<rbrace> \<lbrace>local_b\<rbrace> WHILE b i DO c, s) \<rightarrow> 
           (\<lbrace>i and not local_b\<rbrace> ACTION {(s, s'). s = s'}, s)"

| ParA:    "\<lbrakk> i < length Ps; \<forall>j<length Ps. j \<noteq> i \<longrightarrow> Ps!j = \<lbrace>Ts!j\<rbrace> POSTANN;
           Ps!i = c; (c, s) \<rightarrow> (DONE, s'); com_pre (PARALLEL Ps Ts) s \<rbrakk> \<Longrightarrow> 
           (PARALLEL Ps Ts, s) \<rightarrow> (DONE, s')"

| ParD:    "\<lbrakk> i < length Ps;  \<exists>j<length Ps. j \<noteq> i \<and> Ps!j \<noteq> \<lbrace>Ts!j\<rbrace> POSTANN;
           Ps!i = c; (c, s) \<rightarrow> (DONE, s'); Ps' = Ps[i:=(\<lbrace>Ts!i\<rbrace> POSTANN)];
           com_pre (PARALLEL Ps Ts) s \<rbrakk> \<Longrightarrow> 
           (PARALLEL Ps Ts, s) \<rightarrow> (PARALLEL Ps' Ts, s')"

| Par:     "\<lbrakk> i < length Ps; Ps!i = c; (c, s) \<rightarrow> (c', s'); c' \<noteq> DONE;
           Ps' = Ps[i:=c']; com_pre (PARALLEL Ps Ts) s \<rbrakk> \<Longrightarrow> 
           (PARALLEL Ps Ts, s) \<rightarrow> (PARALLEL Ps' Ts, s')"

lemmas small_step_induct = small_step.induct[split_format(complete)]

inductive_cases 
  DoneE[elim]: "(DONE, s) \<rightarrow> ct" and
  AbortE[elim]: "(ABORTED, s) \<rightarrow> ct" and
  ActionE[elim]: "(\<lbrace>pre\<rbrace> ACTION c, s) \<rightarrow> ct" and
  SemiE[elim]: "(c1;;c2, s) \<rightarrow> ct" and
  IfE[elim]: "(\<lbrace>pre\<rbrace> IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> ct" and
  WhileE[elim]: "(\<lbrace>pre\<rbrace> \<lbrace>local_b\<rbrace> WHILE b i DO c, s) \<rightarrow> ct" and
  ParE[elim]: "(PARALLEL Ps Ts, s) \<rightarrow> ct" and
  Post_annE[elim]: "(\<lbrace>pre\<rbrace> POSTANN, s) \<rightarrow> ct"

abbreviation
  small_steps_star :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where 
  "x \<rightarrow>* y \<equiv> star small_step x y"

inductive_cases StarE[elim!]: "(f, s) \<rightarrow>* (f', s')"


subsubsection \<open>Examples\<close>

lemma "(\<lbrace>true\<rbrace> ACTION UNIV, s) \<rightarrow> (DONE, s')"
  by (auto simp: true_def intro: small_step.intros)

lemma "(\<lbrace>false\<rbrace> ACTION UNIV, s) \<rightarrow> (ABORTED, s)"
  by (auto simp: false_def intro: small_step.intros)


text \<open>Simple programs to check the behaviour of the small step semantics:\<close>

abbreviation "x \<equiv> ''x''"
abbreviation "y \<equiv> ''y''"

definition semi_assign_sub :: com where
  "semi_assign_sub \<equiv> \<lbrace>\<lambda>s. s x = 1\<rbrace> ACTION (Assign true y (\<lambda>s. s x + 2))"

definition semi_assign :: com where
  "semi_assign \<equiv>
    \<lbrace>true\<rbrace>
      ACTION (Assign true x (\<lambda>s. 1));;
    semi_assign_sub"

lemma semi_assign_step: 
  "(semi_assign, s) \<rightarrow> (semi_assign_sub, s(x := 1))"
  by (auto simp: true_def semi_assign_def Assign_def intro: small_step.intros)

lemma semi_assign_steps:
  "(semi_assign, s) \<rightarrow>* (DONE, s(x := 1, y := 3))"
  apply (rule star.step, rule semi_assign_step)
  apply (rule star_step1)
  by (auto simp: true_def Assign_def semi_assign_sub_def intro!: small_step.intros)

definition semi_assign_abort :: com where
  "semi_assign_abort \<equiv>
    \<lbrace>true\<rbrace>
      ACTION (Assign true x (\<lambda>s. 1));;
    \<lbrace>\<lambda>s. s x = 2\<rbrace>
      ACTION (Assign true y (\<lambda>s. s x + 2))"

lemma semi_assign_abort_step: 
  "(semi_assign_abort, s) \<rightarrow> (\<lbrace>\<lambda>s. s x = 2\<rbrace> ACTION (Assign true y (\<lambda>s. s x + 2)), s(x := 1))"
  by (auto simp: true_def semi_assign_abort_def Assign_def intro: small_step.intros)

lemma semi_assign_steps_aborted: "(semi_assign_abort, s) \<rightarrow>* (ABORTED, s(x := 1))"
  apply (rule star.step, rule semi_assign_abort_step)
  apply (rule star_step1)
  by (auto simp: true_def Assign_def intro!: small_step.intros)

definition is_even :: com where
  "is_even \<equiv>
    \<lbrace>true\<rbrace>
      ACTION 
        ( Assign (\<lambda>s. s x mod 2 = 0) y (\<lambda>s. 1)
        \<union> Assign (\<lambda>s. s x mod 2 \<noteq> 0) y (\<lambda>s. 0))"

lemma is_even_even:
  "(is_even, s(x := 0)) \<rightarrow> (DONE, s(x := 0, y := 1))"
  by (auto simp: is_even_def Assign_def true_def intro: small_step.intros)

lemma is_even_odd:
  "(is_even, s(x := 5)) \<rightarrow> (DONE, s(x := 5, y := 0))"
  by (auto simp: is_even_def Assign_def true_def intro: small_step.intros)


text \<open>Distributed counter example:\<close>

lemma dist_ctr_single_step:
  "let ctr = ''ctr''; old = ''old''; new = ''new'' in
   (dist_ctr_com ctr old new, s) \<rightarrow>
   (\<lbrace>true\<rbrace> \<lbrace>true\<rbrace>
    WHILE true true DO
      (\<lbrace>true\<rbrace>
        ACTION (Assign true new (\<lambda>s. s old + 1));;
      \<lbrace>\<lambda>s. s new = s old + 1\<rbrace>
        ACTION 
          ( Assign (\<lambda>s. s ctr = s old) ctr (\<lambda>s. s new)
          \<union> Assign (\<lambda>s. s ctr \<noteq> s old) old (\<lambda>s. s ctr)))
    , s(old := 0, new := 0))"
  by (auto simp: Action Semi1 Semi2 true_def dist_ctr_com_def Assign_def Let_def
     intro: small_step.intros)


text \<open>Blocking action\<close>

definition blocking_action :: com where
  "blocking_action \<equiv> \<lbrace>true\<rbrace> ACTION (Assign false x (\<lambda>s. s x + 1))" 

lemma "(blocking_action, s) \<rightarrow> (f', s') \<Longrightarrow> f' = blocking_action"
  apply (simp add: blocking_action_def)
  by (erule ActionE; clarsimp simp: Assign_def true_def false_def)


text \<open>Parallel execution of @{text "x := x + 1 || x := x + 2 || x := x + 3"}:\<close>

definition com1 :: com where
  "com1 \<equiv> \<lbrace>true\<rbrace> ACTION (Assign true x (\<lambda>s. s x + 1))"

definition com2 :: com where
  "com2 \<equiv> \<lbrace>true\<rbrace> ACTION (Assign true x (\<lambda>s. s x + 2))"

definition com3 :: com where
  "com3 \<equiv> \<lbrace>true\<rbrace> ACTION (Assign true x (\<lambda>s. s x + 3))"

abbreviation "trues \<equiv> [true, true, true]"

definition parallel_program :: com where
  "parallel_program \<equiv> PARALLEL [com1, com2, com3] trues"

lemma parallel_step1: 
  "Ps = [com1, com2, com3] \<Longrightarrow> 
  (PARALLEL Ps trues, s(x := 0)) \<rightarrow> (PARALLEL [\<lbrace>true\<rbrace> POSTANN, com2, com3] trues, s(x := 1))"
  apply (rule_tac i=0 in ParD)
  by (auto simp: com1_def com2_def com3_def Assign_def true_def intro!: small_step.intros)

lemma parallel_step2: 
  "Ps = [\<lbrace>true\<rbrace> POSTANN, com2, com3] \<Longrightarrow> 
  (PARALLEL Ps trues, s(x := 1)) \<rightarrow> (PARALLEL [\<lbrace>true\<rbrace> POSTANN, com2, \<lbrace>true\<rbrace> POSTANN] trues, s(x := 4))"
  apply (rule_tac i=2 in ParD)
  by (auto simp: com2_def com3_def Assign_def true_def intro!: small_step.intros)

lemma parallel_step3: 
  "Ps = [\<lbrace>true\<rbrace> POSTANN, com2, \<lbrace>true\<rbrace> POSTANN] \<Longrightarrow> 
  (PARALLEL Ps trues, s(x := 4)) \<rightarrow> (DONE, s(x := 6))"
  apply (rule_tac i=1 in ParA)
  by (auto simp: nth_Cons' com2_def Assign_def true_def intro!: small_step.intros)

lemma parallel_steps: 
  "(parallel_program, s(x := 0)) \<rightarrow>* (DONE, s(x := 6))"
  apply (simp add: parallel_program_def)
  apply (rule star.step, rule parallel_step1, simp)
  apply (rule star.step, rule parallel_step2, simp)
  apply (rule star.step, rule parallel_step3, simp)
  by (simp add: nth_Cons')

end