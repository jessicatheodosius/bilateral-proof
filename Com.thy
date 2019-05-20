theory Com imports Main begin

section \<open>Formalisation of the Language\<close>

subsection \<open>State Space\<close>

text \<open>
  We choose @{text "state"} to be a function from variable names (string) to values (natural 
  number). Boolean expressions, annotations, and invariants are represented as predicates over 
  states.\<^medskip>
\<close>

type_synonym vname = string
type_synonym state = "vname \<Rightarrow> nat"

type_synonym bexp = "state \<Rightarrow> bool"
type_synonym ann = "state \<Rightarrow> bool"
type_synonym inv = "state \<Rightarrow> bool"


subsection \<open>Syntax\<close>

text \<open>
  We define the syntax of the language with @{command datatype} @{text com}.\<^medskip>
\<close>

type_synonym state_rel = "(state * state) set"

datatype com = 
    DONE
  | ABORTED
  | Action ann state_rel            ("\<lbrace>_\<rbrace> ACTION _" [0, 61] 61)
  | Semi com com                    ("_;;_"[60, 61] 60)
  | If ann bexp com com             ("\<lbrace>_\<rbrace> IF _ THEN _ ELSE _"[0,0,0,61] 61)
  | While ann ann bexp inv com      ("\<lbrace>_\<rbrace> \<lbrace>_\<rbrace> WHILE _ _ DO _"[0,0,50,50,61] 61)
  | Parallel "com list" "ann list"  ("PARALLEL _ _"[60, 61] 60)
  | Post_ann ann                    ("\<lbrace>_\<rbrace> POSTANN"[0] 61)

text \<open>
  \<^item> @{text "DONE"} indicates the program has terminated.

  \<^item> @{text "ABORTED"} indicates the program does not satisfy some of its local annotations.

  \<^item> @{text "Action"} is represented as a relation over states. 
  As a consequence, the actions in this system can have non-determinism. 
  The actions are done this way to allow the if statement with 
  multiple guards shown in the distributed counter example (Section \ref{section:dist_counter}). 

  \<^item> @{text "Semi"} is the sequential composition (or semicolon) of two components. It does not have
  its own local annotation but it gets the annotation from the first component.

  \<^item> @{text "If"} is the usual if/else statement.

  \<^item> @{text" While"} is the standard while loop with invariant.
  A while loop has two annotations at the front. The first annotation is the local annotation.
  The second annotation represents the local part of the while loop's conditional, which 
  is there solely to help prove progress properties.

  \<^item> @{text "Parallel"} is the parallel composition which takes in a list of @{text "com"}
  rather than limiting it to two components. It also takes in a list of postconditions
  (@{text "ann list"}) to simplify the soundness proof of parallel composition.

  \<^item> @{term Post_ann} is used to help prove the soundness of parallel composition.
  Every time a component running in parallel terminates, it will be substituted with
  a @{term Post_ann} with local annotation the same as the postcondition of the
  terminated component. @{term Post_ann} is intended only to help prove the soundness of
  parallel composition, no program should naturally contain a @{term Post_ann}.
\<close>


subsection \<open>Distributed Counter Example Formalisation\<close>
  
definition "true \<equiv> \<lambda>_. True"
definition "false \<equiv> \<lambda>_. False"

abbreviation
  "and" :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool)" (infixr "and" 35)
where
  "a and b \<equiv> \<lambda>s. a s \<and> b s"

abbreviation
  "or" :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool)" (infixr "or" 30)
where
  "a or b \<equiv> \<lambda>s. a s \<or> b s"

abbreviation
  "not" :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool)" ("not _" [40] 40)
where
  "not a \<equiv> \<lambda>s. \<not> a s"

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

end