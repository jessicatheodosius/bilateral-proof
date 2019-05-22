theory Local imports Validity begin

section \<open>Formalisation of Local Annotations\<close>

text \<open>
  We use an approach inspired from Owicki-Gries' interference-freedom proof.
  For each annotation, we check if it remains valid upon execution of any action in another
  thread, i.e. $\models\{ann\}~action~\{ann\}$. This is similar to \textbf{stable}
  in safety properties.
\<close>

fun all_anns_par :: "ann set list \<Rightarrow> ann list \<Rightarrow> ann set" where
  "all_anns_par [] [] = {true}"
| "all_anns_par [] Ts = {}"
| "all_anns_par Ps [] = {}"
| "all_anns_par (p # ps) (t # ts) =
  (\<Union>tail_ann \<in> (all_anns_par ps ts). (\<Union>ann \<in> p \<union> {t}. {ann and tail_ann}))"

text \<open>Retrieve all annotations in a component\<close>
fun all_anns :: "com \<Rightarrow> ann set" where
  "all_anns DONE = {true}"
| "all_anns ABORTED = {false}"
| "all_anns (\<lbrace>pre\<rbrace> ACTION _) = {pre}"
| "all_anns (c1;;c2) = all_anns c1 \<union> all_anns c2"
| "all_anns (\<lbrace>pre\<rbrace> IF b THEN c1 ELSE c2) = {pre} \<union> all_anns c1 \<union> all_anns c2"
| "all_anns (\<lbrace>pre\<rbrace> \<lbrace>local_b\<rbrace> WHILE b i DO c) = 
  {pre, i, i and not local_b} \<union> all_anns c"
| "all_anns (PARALLEL Ps Ts) = (all_anns_par (map all_anns Ps) Ts)"
| "all_anns (\<lbrace>pre\<rbrace> POSTANN) = {pre}"

text \<open>Retrieve all actions of a component\<close>
fun actions_of :: "com \<Rightarrow> com set" where
  "actions_of (\<lbrace>pre\<rbrace> ACTION c) = {\<lbrace>pre\<rbrace> ACTION c}"
| "actions_of (c1;;c2) = actions_of c1 \<union> actions_of c2"
| "actions_of (\<lbrace>_\<rbrace> IF _ THEN c1 ELSE c2) = actions_of c1 \<union> actions_of c2"
| "actions_of (\<lbrace>_\<rbrace> \<lbrace>local_b\<rbrace> WHILE b i DO c) = 
  actions_of c \<union> {\<lbrace>i and not local_b\<rbrace> ACTION {(s, s'). s = s'}}"
| "actions_of (PARALLEL Ps Ts) = (\<Union>c \<in> set Ps . actions_of c)"
| "actions_of _ = {}"

text \<open>Extracts the local annotation and the state relation from an action.\<close>
fun action_state_rel :: "com \<Rightarrow> (ann * state_rel)" where
  "action_state_rel (\<lbrace>pre\<rbrace> ACTION c) = (pre, c)"
| "action_state_rel _ = (true, {})"

text \<open>
  @{term is_ann_stable} to is a predicate that asserts if an annotation 
  or a postcondition is valid upon the execution of actions in a component, i.e. stable.
\<close>
definition is_ann_stable :: "ann \<Rightarrow> com \<Rightarrow> bool" where
  "is_ann_stable p f \<equiv>
   (\<forall>a pre state_rel. a \<in> actions_of f \<longrightarrow> 
     (pre, state_rel) = action_state_rel a \<longrightarrow> 
       (\<forall>s s'. (s, s') \<in> state_rel \<longrightarrow> p s \<longrightarrow> p s'))"

text \<open>@{term "is_com_stable f g"} means that the annotations @{term f} are stable in @{term g}.\<close>
definition is_com_stable :: "com \<Rightarrow> com \<Rightarrow> bool" where
  "is_com_stable f g \<equiv> \<forall>p. p \<in> all_anns f \<longrightarrow> is_ann_stable p g"

definition valid_ann' :: "com \<Rightarrow> ann \<Rightarrow> com \<Rightarrow> bool" where
  "valid_ann' f t g \<equiv> is_ann_stable t g \<and> is_com_stable f g"

text \<open>
  Check if the annotations and the corresponding postcondition of each component
  are local.
\<close>
definition valid_ann :: "com list \<Rightarrow> ann list \<Rightarrow> bool" where
  "valid_ann Ps Ts = 
    (\<forall>i. i < length Ps \<longrightarrow> 
      (\<forall>j. j < length Ps \<longrightarrow> i \<noteq> j \<longrightarrow> valid_ann' (Ps!i) (Ts!i) (Ps!j)))"

end