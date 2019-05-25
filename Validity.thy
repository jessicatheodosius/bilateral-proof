theory Validity imports Small_Step begin

section \<open>Validity of Program Specifications\<close>

subsection \<open>Perpetual Properties\<close>

text \<open>
  Similar to the language formalisation, we separate the syntax and the semantics of 
  perpetual properties. Below is a @{command datatype} called @{text perpetual} that 
  represents the syntax.
\<close>

datatype perpetual = 
    Co ann ann          ("_ CO _" [20, 21] 20)
  | Stable ann          ("STABLE _" [21] 20)
  | Constant vname      ("CONSTANT _" [21] 20)
  | Invariant ann       ("INVARIANT _" [21] 20)
  | Transient ann       ("TRANSIENT _" [21] 20)
  | Ensure ann ann      ("_ EN _" [20, 21] 20)
  | Leads_to ann ann    ("_ \<mapsto> _" [20, 21] 20)

text \<open>
  @{term "reachable_sat P f s"} means that every reachable program and state starting from
  @{term "(f, s)"} satisfies @{term P}.
\<close>
definition reachable_sat :: "(com \<Rightarrow> state \<Rightarrow> bool) \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool" where
  "reachable_sat P f s \<equiv> \<forall>f' s'. (f, s) \<rightarrow>* (f', s') \<longrightarrow> P f' s'"


subsubsection \<open>Safety Properties\<close>

text \<open>
  For any reachable program that starts from the initial program and state pair, if the program 
  makes a step and @{term p} holds before, then @{term q} holds after the step.
\<close>
definition co :: "ann \<Rightarrow> ann \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool" where
  "co p q f s \<equiv> 
    reachable_sat 
      (\<lambda>f' s'. \<forall>f'' s''. p s' \<and> (f', s') \<rightarrow> (f'', s'') \<longrightarrow> q s'') f s"

definition stable :: "ann \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool" where
  "stable p \<equiv> co p p"

definition "constant" :: "vname \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool" where
  "constant e f s \<equiv> \<forall>c. (stable (\<lambda>s. s e = s c)) f s"

definition invariant :: "ann \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool" where
  "invariant p f s \<equiv> p s \<and> stable p f s"


subsubsection \<open>Progress Properties\<close>

text \<open>
  @{term "is_path P f s"} is true iff @{term P} is a valid path that starts from
  @{term "(f, s)"}. Here, paths are functions from indices (natural number) to configurations.
\<close>
definition is_path :: "(nat \<Rightarrow> com \<times> state) \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool" where
  "is_path P f s \<equiv> P 0 = (f, s) \<and> (\<forall>n. P n \<rightarrow> P (n + 1))"

definition paths :: "com \<Rightarrow> state \<Rightarrow> (nat \<Rightarrow> com \<times> state) set" where
  "paths f s = {P. is_path P f s}"


text \<open>Example of a path for semi\_assign (defined in Small\_Step)\<close>
fun semi_assign_path :: "nat \<Rightarrow> com \<times> state" where
  "semi_assign_path 0 = (semi_assign, \<lambda>v. 0)"
| "semi_assign_path (Suc 0) = (semi_assign_sub, (\<lambda>v. 0)(x := 1))"
| "semi_assign_path _ = (DONE, (\<lambda>v. 0)(x := 1, y := 3))"

lemma semi_assign_path_legit:
  "semi_assign_path n \<rightarrow> semi_assign_path (Suc n)"
  apply (induction n rule: semi_assign_path.induct; simp)
    apply (simp add: semi_assign_def)
    apply (rule Semi1, rule Action; simp add: Assign_def true_def)
   apply (simp add: semi_assign_sub_def)
   apply (rule Action; simp add: Assign_def true_def ext)
  by (rule DoneR)
  
lemma "is_path semi_assign_path semi_assign (\<lambda>v. 0)"
  by (simp add: is_path_def semi_assign_path_legit)

fun has_terminated :: "com \<Rightarrow> bool" where
  "has_terminated DONE    = True"
| "has_terminated ABORTED = True"
| "has_terminated _       = False"

text \<open>A predicate over paths, is true if the execution in the path terminates\<close>
definition path_will_terminate :: "(nat \<Rightarrow> com \<times> state) \<Rightarrow> bool" where
  "path_will_terminate path \<equiv> \<exists>i f s. path i = (f, s) \<and> has_terminated f"

text \<open>
  We include the $post_f$ mentioned in the basis rule. The definition of transient
  becomes if @{term p} holds and @{term f} has not terminated, then eventually either @{term "not p"} 
  holds or @{term f} terminates.
\<close>
definition transient :: "ann \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool" where
  "transient p f s \<equiv> 
    (\<forall>path\<in>paths f s. 
      \<forall>i f s. path i = (f, s) \<and> p s \<and> \<not> has_terminated f \<longrightarrow> 
        (\<exists>j f' s'. j \<ge> i \<and> path j = (f', s') \<and> ((not p) s' \<or> has_terminated f')))"

definition ensures :: "ann \<Rightarrow> ann \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool" where
  "ensures p q f s \<equiv> 
    (\<forall>path\<in>paths f s. 
      \<forall>i f s. path i = (f, s) \<and> p s \<longrightarrow> 
        ((not q) s \<longrightarrow> (\<exists>f' s'. path (Suc i) = (f', s') \<and> (p or q) s')) \<and>
        (\<exists>j f' s'. j \<ge> i \<and> path j = (f', s') \<and> (p s' \<and> has_terminated f' \<or> q s')))"

definition leads_to :: "ann \<Rightarrow> ann \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool" where
  "leads_to p q f s \<equiv> 
    (\<forall>path\<in>paths f s. 
      \<forall>i f s. path i = (f, s) \<and> p s \<and> \<not> has_terminated f \<longrightarrow> 
        (\<exists>j f' s'. j \<ge> i \<and> path j = (f', s') \<and> (q s' \<or> has_terminated f')))"


subsubsection \<open>Syntax to Semantics\<close>

primrec eval :: "perpetual \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool" where
  "eval (p CO q) = co p q"
| "eval (STABLE p) = stable p"
| "eval (CONSTANT e) = constant e"
| "eval (INVARIANT i) = invariant i"
| "eval (TRANSIENT p) = transient p"
| "eval (p EN q) = ensures p q"                                
| "eval (p \<mapsto> q) = leads_to p q"


subsection \<open>Valid Specification\<close>

text \<open>
  The function @{term holds} checks if a state satisfies a predicate given that the program is 
  not @{term ABORTED}.
\<close>
definition holds :: "ann \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool" where
  "holds q f s \<equiv> q s \<and> f \<noteq> ABORTED"

text \<open>Valid Specification\<close>
definition
  valid_spec :: "ann \<Rightarrow> com \<Rightarrow> perpetual set \<Rightarrow> ann \<Rightarrow> bool" ("\<Turnstile> {_} _ {_ | _}" [0, 0, 0, 0] 61)
where
  "\<Turnstile> {r} f {Q | t} \<equiv> 
    (\<forall>s. r s \<longrightarrow> 
      reachable_sat (\<lambda>f' s'. has_terminated f' \<longrightarrow> holds t f' s') f s \<and>
      (\<forall>op \<in> Q. eval op f s))"

end