section "MOV Compiler"

theory Mov
  imports Main "HOL-IMP.AExp" "HOL-IMP.Big_Step" "HOL-IMP.Star" "HOL-IMP.Small_Step"
begin

text \<open>This project aims at proving the general idea of the MOVfuscator
(https://github.com/xoreaxeaxeax/movfuscator)

The idea is, that a program can be compiled (almost) exclusively to the x86-MOV instruction.
We show in this project, that this is semantically true, by defining a set of instructions similar
to the x86 MOV instruction (https://www.felixcloutier.com/x86/mov), defining a compilation procedure
and finally proving semantic equivalence.

Due to the nature of working with the HOL-IMP definition of expressions, we must work with
infinitely sized numbers, therefore, we emulate infinitely large lookup-tables for the arithmetic
calculations by functions in the instruction set. This is no violation of the Turing completeness,
but redefining the entire Com, BExp, AExp and BigStep would exceed the scope of this project.

This section mirrors the structure of HOL-IMP.Compiler

We begin with some list setup and the definition of the Instruction Set.
The section Verification Infrastructure provides lemmas which shorten the later proofs, some lemmas
are not proved, but they are intuitively true and possible to prove, we just lacked the time to
complete these proofs.
The section Compilation is of greater interest, since we show the equivalence to Big_Step.

Since the compilation only works on arbitrary "outer-loop" programs (i.e. where only one WHILE exists
at the root of the program syntax tree), we introduce a notion of expressing a program complying to
this property.

In the section "One Loop", we lay out the intuition that arbitrary programs can be transformed into
a program of the "outer-loop" property, but we do not prove this (this file is already too long
anyway).\<close>

(* List Setup from "HOL-IMP.Compiler" *)
subsection "List Setup"
declare [[coercion_enabled]] 
declare [[coercion "int :: nat \<Rightarrow> int"]]

fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
"(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))"

lemma inth_append [simp]:
  "0 \<le> i \<Longrightarrow>
  (xs @ ys) !! i = (if i < size xs then xs !! i else ys !! (i - size xs))"
  by (induction xs arbitrary: i) (auto simp: algebra_simps)

lemma inth_exists:
  "x \<in> set xs \<Longrightarrow> \<exists>i. xs !! i = x \<and> 0 \<le> i \<and> i < size xs"
proof (induction xs)
  case (Cons y ys)
  then show ?case
  proof (cases "x = y")
    case False
    then have "x \<in> set ys" using Cons by auto
    then obtain i where "ys !! i = x" "0 \<le> i \<and> i < size ys"
      using Cons.IH by auto
    then have "(y#ys) !! (i+1) = x" "0 \<le> (i+1) \<and> (i+1) < size (y#ys)" by auto
    then show ?thesis by blast
  qed auto
qed auto

abbreviation (output)
  "isize xs == int (length xs)"

notation isize ("size")
(* End List Setup *)

subsection "Instruction Set"
type_synonym val = int (* maybe nat? *)

(* Register definition *)
type_synonym rname = string
type_synonym rstate = "rname \<Rightarrow> val"

(* Memory definition *)
type_synonym maddr = val
type_synonym mstate = "maddr \<Rightarrow> val"
type_synonym ltable = "maddr \<Rightarrow> val"
type_synonym l2table = "maddr \<Rightarrow> maddr \<Rightarrow> val"

text \<open>We define the instruction set based on the x86 MOV instruction with three alterations:

Since we must work with infinitely-sized integers in IMP, we define the lookup tables required for
logic and arithmetic of possibly infinite size. We simulate these lookup tables with functions, that
are not in the memory, but are separate arguments for specific instructions. This necessitates an
instruction with two-dimensional lookup (MOVT2) since we cannot use index-offsets to access the
lookup table (which is not in memory).

In the MOVfuscator, arithmetic operations have been reduced to increment and decrement operations,
but to simplify the proves, we use lookup table (functions) for arbitrary values.

We also retain the jump instruction JMPZ for loops.\<close>

(* Simplified Turing-complete MOV instruction set from x86 with distinct Lookup-Table calls *)
datatype instr =
(* Move Immediate to Memory *)
  MOVI rname val
(* Move Register to Register *)
| MOVR rname rname
(* Move Memory at Register r1 with offset c to Register r0 (Load) *)
| MOVL rname rname maddr (* r0 r1 c *)
(* Move Register r1 to Memory at Register r0 with offset c (Store) *)
| MOVS rname maddr rname (* r0 c r1 *)
(* Move from Lookup Table to Register *)
| MOVT rname ltable rname 
(* Move from 2-dimensional Lookup Table to Register *)
| MOVT2 rname l2table rname rname
(* The JUMP instruction is emulated by invalid instruction handlers in the MOVfuscator,
   we use a JUMP instruction that only jumps if a register is zero *)
| JMPZ rname int


text \<open>To assist with the later proves which heavily rely on repetitive computation of
MOV-instructions and only in one case include a JUMP instruction (for the WHILE command), we define
the instruction execution in two steps\<close>

type_synonym state = "rstate \<times> mstate"

fun mexec :: "instr \<Rightarrow> state \<Rightarrow> state" where
  "mexec (MOVI r v)   (reg,mem) = (reg(r := v),mem)"
| "mexec (MOVR r2 r1) (reg,mem) = (reg(r2 := reg r1),mem)"
| "mexec (MOVL r m c) (reg,mem) = (reg(r := mem (reg m + c)),mem)"
| "mexec (MOVS m c r) (reg,mem) = (reg,mem(reg m + c := reg r))"
| "mexec (MOVT r t m) (reg,mem) = (reg(r := t (reg m)),mem)"
| "mexec (MOVT2 r t m1 m2) (reg,mem) = (reg(r := t (reg m1) (reg m2)),mem)"
| "mexec (JMPZ r n)   (reg,mem) = (reg,mem)"

type_synonym config = "int \<times> state"

fun iexec :: "instr \<Rightarrow> config \<Rightarrow> config" where
  "iexec (JMPZ r n) (j,(reg,mem)) = ((if reg r = 0 then j+n+1 else j+1), mexec (JMPZ r n) (reg,mem))"
| "iexec i          (j,s)         = (j+1, mexec i s)"

(* List execution from "HOL-IMP.Compiler" *)
definition
  exec1 :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
     ("(_/ \<turnstile> (_ \<rightarrow>/ _))" [59,0,59] 60) 
where
  "P \<turnstile> c \<rightarrow> c' = 
  (\<exists>i reg mem. c = (i,reg,mem) \<and> c' = iexec(P!!i) (i,reg,mem) \<and> 0 \<le> i \<and> i < size P)"

lemma exec1I [intro, code_pred_intro]:
  "c' = iexec (P!!i) (i,s,stk) \<Longrightarrow> 0 \<le> i \<Longrightarrow> i < size P
  \<Longrightarrow> P \<turnstile> (i,s,stk) \<rightarrow> c'"
by (simp add: exec1_def)

abbreviation 
  exec :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("(_/ \<turnstile> (_ \<rightarrow>*/ _))" 50)
where
  "exec P \<equiv> star (exec1 P)"

lemmas exec_induct = star.induct [of "exec1 P", split_format(complete)]

lemmas exec_cases = star.cases [of "exec1 P", split_format(complete)]

lemmas exec_intros = star.intros [of "exec1 P", split_format(complete)]

code_pred exec1 by (metis exec1_def)
(* End List execution *)


(* Verification infrastructure from "HOL-IMP.Compiler" *)
subsection "Verification infrastructure"

lemma iexec_shift [simp]: 
  "((n+i',s',stk') = iexec x (n+i,s,stk)) = ((i',s',stk') = iexec x (i,s,stk))"
by (cases x) (auto split:instr.split)

lemma exec1_appendR: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P@P' \<turnstile> c \<rightarrow> c'"
by (auto simp: exec1_def)

lemma exec_appendR: "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P@P' \<turnstile> c \<rightarrow>* c'"
by (induction rule: star.induct) (fastforce intro: star.step exec1_appendR)+

lemma exec1_appendL:
  fixes i i' :: int 
  shows
  "P \<turnstile> (i,s,stk) \<rightarrow> (i',s',stk') \<Longrightarrow>
   P' @ P \<turnstile> (size(P')+i,s,stk) \<rightarrow> (size(P')+i',s',stk')"
  unfolding exec1_def
  by (auto simp del: iexec.simps)

lemma exec_appendL:
  fixes i i' :: int 
  shows
 "P \<turnstile> (i,s,stk) \<rightarrow>* (i',s',stk')  \<Longrightarrow>
  P' @ P \<turnstile> (size(P')+i,s,stk) \<rightarrow>* (size(P')+i',s',stk')"
  by (induction rule: exec_induct) (blast intro: star.step exec1_appendL)+

(* added *)
lemma exec1_subtractL:
  fixes i i' :: int 
  shows
  "\<lbrakk> P' @ P \<turnstile> (size(P')+i,s,stk) \<rightarrow> (size(P')+i',s',stk'); 0 < i \<rbrakk> \<Longrightarrow>
   P \<turnstile> (i,s,stk) \<rightarrow> (i',s',stk')"
  unfolding exec1_def
  by (auto simp del: iexec.simps)

text\<open>Now we specialise the above lemmas to enable automatic proofs of
\<^prop>\<open>P \<turnstile> c \<rightarrow>* c'\<close> where \<open>P\<close> is a mixture of concrete instructions and
pieces of code that we already know how they execute (by induction), combined
by \<open>@\<close> and \<open>#\<close>. Backward jumps are not supported.
The details should be skipped on a first reading.

If we have just executed the first instruction of the program, drop it:\<close>

lemma exec_Cons_1 [intro]:
  "P \<turnstile> (0,s,stk) \<rightarrow>* (j,t,stk') \<Longrightarrow>
  instr#P \<turnstile> (1,s,stk) \<rightarrow>* (1+j,t,stk')"
by (drule exec_appendL[where P'="[instr]"]) simp

lemma exec_appendL_if[intro]:
  fixes i i' j :: int
  shows
  "size P' <= i
   \<Longrightarrow> P \<turnstile> (i - size P',s,stk) \<rightarrow>* (j,s',stk')
   \<Longrightarrow> i' = size P' + j
   \<Longrightarrow> P' @ P \<turnstile> (i,s,stk) \<rightarrow>* (i',s',stk')"
by (drule exec_appendL[where P'=P']) simp

text\<open>Split the execution of a compound program up into the execution of its
parts:\<close>

lemma exec_append_trans[intro]:
  fixes i' i'' j'' :: int
  shows
"P \<turnstile> (0,s,stk) \<rightarrow>* (i',s',stk') \<Longrightarrow>
 size P \<le> i' \<Longrightarrow>
 P' \<turnstile>  (i' - size P,s',stk') \<rightarrow>* (i'',s'',stk'') \<Longrightarrow>
 j'' = size P + i''
 \<Longrightarrow>
 P @ P' \<turnstile> (0,s,stk) \<rightarrow>* (j'',s'',stk'')"
  by(metis star_trans[OF exec_appendR exec_appendL_if])

corollary exec_append_trans_0[intro]:
  fixes j'' :: int
  shows
"P \<turnstile> (0,s,stk) \<rightarrow>* (size P,s',stk') \<Longrightarrow>
 P' \<turnstile>  (0,s',stk') \<rightarrow>* (size P',s'',stk'') \<Longrightarrow>
 j'' = size P + size P'
 \<Longrightarrow>
 P @ P' \<turnstile> (0,s,stk) \<rightarrow>* (j'',s'',stk'')"
  using exec_append_trans by simp

corollary exec_append_trans_1[intro]:
  fixes j'' :: int
  shows
"P \<turnstile> (0,s,stk) \<rightarrow>* (size P,s',stk') \<Longrightarrow>
 P' \<turnstile>  (0,s',stk') \<rightarrow>* (size P',s'',stk'')
 \<Longrightarrow>
 P @ P' \<turnstile> (0,s,stk) \<rightarrow>* (size (P @ P'),s'',stk'')"
  using exec_append_trans by simp
  


declare Let_def[simp]
(* End Verification Infrastructure from "HOL-IMP.Compiler" *)

subsubsection \<open>Proving infrastructure for dealing with many MOVes\<close>


(* Proving infrastructure *)
primrec jump_free :: "instr list \<Rightarrow> bool" where
  "jump_free [] = True"
| "jump_free (i#is) = (case i of (JMPZ a b) \<Rightarrow> (False) | _ \<Rightarrow> (jump_free is))"

lemma jump_free_conc[simp]: "jump_free (p#P) \<Longrightarrow> jump_free P"
  by (cases p) auto

lemma jump_free_app[simp]: "\<lbrakk> jump_free P; jump_free P' \<rbrakk> \<Longrightarrow> jump_free (P @ P')"
proof (induction P)
  case (Cons p P)
  thus ?case
    by (cases p) simp+
qed simp

lemma jump_at: "\<lbrakk> 0 \<le> i; i < size P; P !! i = JMPZ r n \<rbrakk> \<Longrightarrow> \<not>jump_free P"
proof (induction P arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a P)
  then show ?case
  proof (cases "i = 0")
    case True
    then have "(a # P) !! i = a" by simp
    then show ?thesis using Cons.prems(3) by simp
  next
    case False
    with \<open>0 \<le> i\<close> have "0 < i" and "0 \<le> i - 1" by simp+
    with \<open>i < size (a # P)\<close> have "i - 1 < size P" by simp
    from Cons.prems(3) have "P !! (i - 1) = JMPZ r n" using \<open>0 < i\<close> by simp
    from Cons.IH[of "i - 1"] have "\<not>jump_free P"
      using \<open>0 \<le> i - 1\<close> \<open>i - 1 < size P\<close> \<open>P !! (i - 1) = JMPZ r n\<close> by simp
    then show ?thesis by (cases a) auto
  qed
qed

lemma jump_free_advances_pc:
  assumes "jump_free P"
  assumes "P \<turnstile> (i,s,mem) \<rightarrow> (j,s',mem')"
  assumes i_bounds: "0 \<le> i \<and> i < size P"
  shows "j = i+1"
proof -
  from assms(2) have c': "(j,s',mem') = iexec(P!!i) (i,s,mem)"
    unfolding exec1_def by simp
  then show "j = i + 1"
  proof (cases "P !! i")
    case (JMPZ r n)
    then have "\<not>jump_free P" using jump_at i_bounds by auto
    then show ?thesis using \<open>jump_free P\<close> by simp (* contradiction *)
  qed auto
qed

lemma step_expandE [elim]:
  assumes "P \<turnstile> (i,s,mem) \<rightarrow>* (k,s'',mem'')"
  assumes "jump_free P"
  assumes "(k,s'',mem'') = (i,s,mem) \<Longrightarrow> R"
  assumes "\<And>s' mem'. \<lbrakk> P \<turnstile> (i,s,mem) \<rightarrow> (i+1,s',mem');  P \<turnstile> (i+1,s',mem') \<rightarrow>* (k,s'',mem'')\<rbrakk>
     \<Longrightarrow> R"
  shows R
  using assms
proof (cases)
  case refl
  then show ?thesis using assms by simp
next
  case (step c')
  from step(1) obtain j s' mem' where [simp]: "c' = (j,s',mem')" unfolding exec1_def
    using prod_cases3 by blast
  from step(1) have "0 \<le> i" "i < size P" unfolding exec1_def by simp+
  with step(1) \<open>jump_free P\<close> have "j = i+1" using jump_free_advances_pc by simp
  then show ?thesis using step assms(4) by simp
qed

thm step_expandE

(* earlier attempt at auto-proving instruction steps *)
lemma step_expand [intro]:
  assumes "P \<turnstile> (i+1,s',mem') \<rightarrow>* (k,s'',mem'')"
  assumes "P \<turnstile> (i,s,mem) \<rightarrow> (i+1,s',mem')"
  shows "P \<turnstile> (i,s,mem) \<rightarrow>* (k,s'',mem'')"
  using assms star.step by metis

lemma exec_determ:
  "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P \<turnstile> c \<rightarrow> c'' \<Longrightarrow> c = c''"
  sorry

lemma force_update:
  "jump_free (i#is) \<Longrightarrow> (i#is) \<turnstile> c \<rightarrow> c' \<Longrightarrow> c \<noteq> c'"
  sorry

lemma step1:
  assumes "jump_free (i#is)"
  shows "((i#is) \<turnstile> (0,s,mem) \<rightarrow>* (1,s',mem')) = ((iexec i (0,s,mem)) = (1,s',mem'))"
proof
  assume assm: "i # is \<turnstile> (0,s,mem) \<rightarrow>* (1,s',mem')"
  have step1: "i # is \<turnstile> (0,s,mem) \<rightarrow> (1,mexec i (s,mem))"
    using \<open>jump_free (i#is)\<close> by (cases i) auto
  have steps: "i # is \<turnstile> (1,s',mem') \<rightarrow>* (1,s',mem')" by blast

  have "(s',mem') = mexec i (s,mem)" using assm step1 steps
  proof (induction rule: exec_induct)
    case (refl j s' mem')
    then have "0 \<le> j" "j < size (i # is)" using exec1_def by blast+
    with refl(1) have "j = j+1"
      using \<open>jump_free (i#is)\<close> jump_free_advances_pc[OF assms]
      using exec_determ by blast
    then show ?case by simp
  next
    case (step j s' mem' k s'' mem'' l s''' mem''')
    then show ?case using exec_determ by blast
  qed

  then show "iexec i (0, s, mem) = (1, s', mem')"
    using step1 exec1_def by simp
next
  assume "iexec i (0, s, mem) = (1, s', mem')" 
  show "i # is \<turnstile> (0, s, mem) \<rightarrow>* (1, s', mem')"
    by (smt (verit, del_insts) One_nat_def assms exec1I exec_determ force_update int_ops(2) list.size(4) of_nat_add of_nat_less_0_iff)
qed

(* one of the missing proves which just shortens the later proofs *)
lemma exec_subtract1L:
  fixes i i' :: int 
  shows
 "\<lbrakk> p#P \<turnstile> (i+1,s) \<rightarrow>* (i'+1,s'); jump_free (p#P) \<rbrakk> \<Longrightarrow>
  P \<turnstile> (i,s) \<rightarrow>* (i',s')"
  sorry

lemma step_consume:
  assumes "jump_free (i#is)"
  assumes "0 < k"
  shows "((i#is) \<turnstile> (0,s,mem) \<rightarrow>* (k,s'',mem'')) = (is \<turnstile> (0,mexec i (s,mem)) \<rightarrow>* (k-1,s'',mem''))"
proof
  assume "(i#is) \<turnstile> (0,s,mem) \<rightarrow>* (k,s'',mem'')"
  then obtain j s' mem' where 
    step1: "(i#is) \<turnstile> (0,s,mem) \<rightarrow> (j,s',mem')" and
    steps: "(i#is) \<turnstile> (j,s',mem') \<rightarrow>* (k,s'',mem'')"
    using assms(1) assms(2) by auto
  moreover
  from assms(1) step1 have "j = 1"
    using jump_free_advances_pc by fastforce
  moreover
  from step1 have "(s', mem') = mexec i (s,mem)" unfolding exec1_def
    by (cases i) auto
  ultimately
  show "is \<turnstile> (0,mexec i (s, mem)) \<rightarrow>* (k-1,s'',mem'')"
    using assms exec_subtract1L[of i "is" 0 "mexec i (s,mem)" "k - 1" "(s'',mem'')"] by auto
next
  assume steps: "is \<turnstile> (0,mexec i (s, mem)) \<rightarrow>* (k-1,s'',mem'')"
  obtain s' mem' where "(s',mem') = mexec i (s,mem)"
    by (metis surj_pair)
  with assms(1) have "iexec i (0,s,mem) = (1,s',mem')"
    by (cases i) auto
  then have step1: "[i] \<turnstile> (0,s,mem) \<rightarrow> (1,s',mem')" unfolding exec1_def by simp
  then show "(i#is) \<turnstile> (0,s,mem) \<rightarrow>* (k,s'',mem'')"
    using \<open>(s', mem') = mexec i (s, mem)\<close> \<open>iexec i (0, s, mem) = (1, s', mem')\<close> assms(1)
    by (smt (verit, ccfv_threshold) Mov.step1 exec_Cons_1 star_trans steps)
qed

lemma steps_consume:
  assumes "jump_free P'"
  assumes "jump_free P"
  assumes "size P \<le> k"
  assumes "P \<turnstile> (0,s,mem) \<rightarrow>* (size P,s',mem')"
  shows "(P @ P' \<turnstile> (0,s,mem) \<rightarrow>* (k,s'',mem'')) = (P' \<turnstile> (0,s',mem') \<rightarrow>* (k-size P,s'',mem''))"
  using assms
proof (induction P arbitrary: k s mem)
  case Nil
  from \<open>[] \<turnstile> (0, s, mem) \<rightarrow>* (size [], s', mem')\<close> have "(0, s, mem) = (size [], s', mem')"
    by (cases rule: exec_cases) (auto simp: exec1_def)
  then show ?case by simp
next
  case (Cons p P)
  from Cons have "jump_free P" by simp
  from \<open>jump_free (p#P)\<close> \<open>jump_free P'\<close> have "jump_free ((p # P) @ P')"
    apply -
    by (rule jump_free_app) auto
    
  obtain s0 mem0 where "(s0,mem0) = mexec p (s,mem)"
    by (metis surj_pair)
  with Cons.prems(2,4) have "P \<turnstile> (0, s0, mem0) \<rightarrow>* (size P, s', mem')"
    by (auto simp: step_consume)

  then have eq: "(P @ P' \<turnstile> (0, s0, mem0) \<rightarrow>* (k-1, s'', mem'')) = (P' \<turnstile> (0, s', mem') \<rightarrow>* (k-1 - size P, s'', mem''))"
    using Cons.IH[of] Cons.prems(1,3) \<open>jump_free P\<close> by simp

  (* expand left side *)
  have "(p # P @ P' \<turnstile> (0, s, mem) \<rightarrow>* (k, s'', mem'')) = (P @ P' \<turnstile> (0, mexec p (s, mem)) \<rightarrow>* (k - 1, s'', mem''))"
    using \<open>jump_free ((p # P) @ P')\<close> \<open>size (p # P) \<le> k\<close> by (auto simp: step_consume)

  then show ?case using eq
    by (smt (verit) One_nat_def \<open>(s0, mem0) = mexec p (s, mem)\<close> append_Cons int_ops(2) list.size(4) of_nat_add)
      (* sledgehammer proof to get the details with the tuples right *)
qed

subsection "Compilation"

text \<open>We use the registers ''0'', ''1'' as accumulator registers for arithmetic expressions. This
avoids us having to define separate registers from the state, but introduces complexity to the
compilation, since we have to carry the assumption that the registers are safe to overwrite through
the entire proof.

The integer value i serves as a "stack marker", i.e., a guarantee that the memory below i is
unchanged during execution of a program\<close>

subsubsection \<open>AExp\<close>

(* The addition lookup table is implemented as a function *)
(* temporarily *)
fun acomp :: "aexp \<Rightarrow> int \<Rightarrow> instr list" where
"acomp (N n) i = [MOVI ''0'' n, MOVI ''1'' i, MOVS ''1'' 0 ''0'', MOVI ''0'' 0, MOVI ''1'' 0]" |
"acomp (V x) i = [MOVR ''0'' x, MOVI ''1'' i, MOVS ''1'' 0 ''0'', MOVI ''0'' 0, MOVI ''1'' 0]" |
"acomp (Plus a1 a2) i = (acomp a1 i) @ (acomp a2 (i+1))
  @ [MOVI ''0'' i, MOVL ''0'' ''0'' 0,
     MOVI ''1'' (i+1), MOVL ''1'' ''1'' 0,
     MOVT2 ''0'' (\<lambda>x y. x + y) ''0'' ''1'',
     MOVI ''1'' i, MOVS ''1'' 0 ''0'',
     MOVI ''0'' 0, MOVI ''1'' 0]"

lemma acomp_jump_free[simp,intro]: "jump_free (acomp a i)"
  by (induction a arbitrary: i) (auto simp: jump_free_app)

lemma state_identity_0[simp]:
  assumes "s ''0'' = 0"
  shows "s(''0'' := 0) = s"
  using assms
  by auto

lemma state_identity_1[simp]:
  assumes "s ''1'' = 0"
  shows "s(''1'' := 0) = s"
  using assms
  by auto

text \<open>This proof makes little use of lemmas, so it is rather long and hard to read. We make use of
the proof infrastructure later during the BExp and Com sections\<close>
lemma acomp_correct[intro]:
  assumes "s ''0'' = 0"
  assumes "s ''1'' = 0"
  shows "\<exists>mem'. ((acomp a i) \<turnstile> (0,s,mem) \<rightarrow>* (size(acomp a i),s,mem')) \<and> mem' i = aval a s
    \<and> (\<forall>j < i. mem j = mem' j)"
proof (induction a arbitrary: i mem)
  case (N n)
  then show ?case using assms
    by (auto simp: step_consume)
next
  case (V x)
  then show ?case using assms
    by (auto simp: step_consume)
next
  case (Plus a1 a2)
  let ?Ia1 = "acomp a1 i"
  let ?Ia2 = "acomp a2 (i+1)"
  let ?r1 = "aval a1 s"
  let ?r2 = "aval a2 s"

  from Plus.IH(1) obtain mem' where exec_1: "?Ia1 \<turnstile> (0, s, mem) \<rightarrow>* (size ?Ia1, s, mem')"
    and "mem' i = ?r1" "\<forall>j < i. mem j = mem' j" by blast
  from Plus.IH(2) obtain mem'' where exec_2: "?Ia2 \<turnstile> (0, s, mem') \<rightarrow>* (size ?Ia2, s, mem'')"
    and result_2: "mem'' (i+1) = ?r2" and "\<forall>j < (i+1). mem' j = mem'' j" by blast
  then have result_1: "mem'' i = ?r1" using \<open>mem' i = ?r1\<close> by simp  

  let ?Ip = "[MOVI ''0'' i, MOVL ''0'' ''0'' 0,
     MOVI ''1'' (i+1), MOVL ''1'' ''1'' 0,
     MOVT2 ''0'' (\<lambda>x y. x + y) ''0'' ''1'',
     MOVI ''1'' i, MOVS ''1'' 0 ''0'',
     MOVI ''0'' 0, MOVI ''1'' 0]"
  let ?I = "?Ia1 @ ?Ia2 @ ?Ip"
  let ?k = "size ?Ia1 + size ?Ia2"

  have steps: "?I \<turnstile> (0,s,mem) \<rightarrow>* (9+?k,s,mem''(i:=?r1+?r2))"
    using exec_1 result_1 exec_2 result_2 assms
    by (simp add: steps_consume step_consume)
  moreover
  have "\<forall>j < i. mem j = (mem''(i:=?r1+?r2)) j"
    using \<open>\<forall>j < i. mem j = mem' j\<close> \<open>\<forall>j < (i+1). mem' j = mem'' j\<close> by simp
  moreover
  have "(mem''(i:=?r1+?r2)) i = ?r1 + ?r2" by simp
  ultimately show ?case by auto
qed

subsubsection \<open>BExp\<close>

lemma table_comp:
  assumes "s ''0'' = 0"
  assumes "s ''1'' = 0"
  assumes "jump_free c1"
  assumes "jump_free c2"
  assumes hyp1: "\<forall>mem. \<exists>mem'. c1 \<turnstile> (0,s,mem) \<rightarrow>* (size c1,s,mem') \<and> mem' i = v1 \<and> (\<forall>j<i. mem j = mem' j)"
  assumes hyp2: "\<forall>mem. \<exists>mem'. c2 \<turnstile> (0,s,mem) \<rightarrow>* (size c2,s,mem') \<and> mem' (i+1) = v2 \<and> (\<forall>j<(i+1). mem j = mem' j)"
  assumes "P = c1 @ c2 @ [MOVI ''0'' i, MOVL ''0'' ''0'' 0,  MOVI ''1'' (i+1), MOVL ''1'' ''1'' 0,
    MOVT2 ''0'' f ''0'' ''1'',  MOVI ''1'' i, MOVS ''1'' 0 ''0'', MOVI ''0'' 0, MOVI ''1'' 0]"
  shows "\<exists>mem'. (P
    \<turnstile> (0,s,mem) \<rightarrow>* (size P,s,mem'))
    \<and> mem' i = f v1 v2
    \<and> (\<forall>j < i. mem j = mem' j)"
proof -
  (* hyps *)
  from hyp1 obtain mem' where
    exec_c1: "c1 \<turnstile> (0,s,mem) \<rightarrow>* (size c1,s,mem')"
    and "mem' i = v1" and "\<forall>j<i. mem j = mem' j"  by auto
  from hyp2 obtain mem'' where
    exec_c2: "c2 \<turnstile> (0,s,mem') \<rightarrow>* (size c2,s,mem'')"
    and "mem'' (i+1) = v2" and "\<forall>j<(i+1). mem' j = mem'' j" by auto
  from \<open>mem' i = v1\<close> \<open>\<forall>j<(i+1). mem' j = mem'' j\<close> have "mem'' i = v1" by auto

  let ?I = "[MOVI ''0'' i, MOVL ''0'' ''0'' 0,  MOVI ''1'' (i+1), MOVL ''1'' ''1'' 0,
    MOVT2 ''0'' f ''0'' ''1'',  MOVI ''1'' i, MOVS ''1'' 0 ''0'', MOVI ''0'' 0, MOVI ''1'' 0]"
  let ?MEM' = "mem''(i := f v1 v2)"

  (* core proof *)
  have "c1 @ c2 @ ?I \<turnstile> (0,s,mem) \<rightarrow>* (size c1+size c2+9,s,?MEM')"
    using \<open>jump_free c1\<close> \<open>jump_free c2\<close> exec_c1 \<open>mem' i = v1\<close> exec_c2 \<open>mem'' (i+1) = v2\<close>
      \<open>mem'' i = v1\<close> assms
    by (simp add: steps_consume step_consume)
  (* summary *)
  moreover
  have "?MEM' i = f v1 v2" by simp
  moreover
  have "\<forall>j<i. mem j = ?MEM' j" using \<open>\<forall>j<i. mem j = mem' j\<close> \<open>\<forall>j<(i+1). mem' j = mem'' j\<close> by simp
  moreover
  have "size P = size c1 + size c2 + 9" using assms(7) by simp
  ultimately
  have "(P \<turnstile> (0, s, mem) \<rightarrow>* (size P, s, ?MEM')) \<and> ?MEM' i = f v1 v2 \<and> (\<forall>j<i. mem j = ?MEM' j)"
    using assms(7) by metis
  then show ?thesis by blast
qed

fun bcomp :: "bexp \<Rightarrow> int \<Rightarrow> instr list" where
"bcomp (Bc v) i =  [MOVI ''0'' i, MOVI ''1'' (if v then 1 else 0), MOVS ''0'' 0 ''1'', MOVI ''0'' 0, MOVI ''1'' 0]" |
"bcomp (Not b) i = bcomp b i
  @ [MOVI ''0'' i, MOVL ''0'' ''0'' 0,
  MOVT ''1'' (\<lambda>x. if x = 1 then 0 else 1) ''0'',
  MOVI ''0'' i, MOVS ''0'' 0 ''1'',
  MOVI ''0'' 0, MOVI ''1'' 0]" |
"bcomp (And b1 b2) i = bcomp b1 i @ bcomp b2 (i+1)
  @ [MOVI ''0'' i, MOVL ''0'' ''0'' 0, MOVI ''1'' (i+1), MOVL ''1'' ''1'' 0,
  MOVT2 ''0'' (\<lambda>x y. if x = 0 then 0 else (if y = 0 then 0 else 1)) ''0'' ''1'',
  MOVI ''1'' i, MOVS ''1'' 0 ''0'', MOVI ''0'' 0, MOVI ''1'' 0]" |
"bcomp (Less a1 a2) i = (acomp a1 i) @ (acomp a2 (i+1))
  @ [MOVI ''0'' i, MOVL ''0'' ''0'' 0,  MOVI ''1'' (i+1), MOVL ''1'' ''1'' 0,
  MOVT2 ''0'' (\<lambda>x y. if x < y then 1 else 0) ''0'' ''1'',
  MOVI ''1'' i, MOVS ''1'' 0 ''0'', MOVI ''0'' 0, MOVI ''1'' 0]"
(* equality different *)

lemma bcomp_jump_free [simp,intro]: "jump_free (bcomp b i)"
  by (induction b arbitrary: i) auto

lemma bcomp_correct[intro]:
  assumes "s ''0'' = 0"
  assumes "s ''1'' = 0"
  shows "\<exists>mem'. ((bcomp b i) \<turnstile> (0,s,mem) \<rightarrow>* (size(bcomp b i),s,mem'))
    \<and> mem' i = (if bval b s then 1 else 0)
    \<and> (\<forall>j < i. mem j = mem' j)"
proof (induction b arbitrary: i mem)
  case (Bc x)
  then show ?case using assms
    by (auto simp: step_consume)
next
  case (Not b)
  let ?B = "if bval b s then 1 else 0"
  let ?NB = "if bval b s then 0 else 1"
  let ?J = "size (bcomp b i)"
  let ?I1 = "bcomp b i"
  let ?I2 = "[MOVI ''0'' i, MOVL ''0'' ''0'' 0, MOVT ''1'' (\<lambda>x. if x = 1 then 0 else 1) ''0'', MOVI ''0'' i, MOVS ''0'' 0 ''1'', MOVI ''0'' 0, MOVI ''1'' 0]"

  (* IH *)
  from Not.IH[of i mem] obtain mem' where
    exec_cb: "bcomp b i \<turnstile> (0,s,mem) \<rightarrow>* (?J,s,mem')"
    and "mem' i = ?B" and "\<forall>j<i. mem j = mem' j"  by auto

  (* More preparation *)
  let ?MEM' = "mem'(i := ?NB)"

  (* core proof, very short thanks to lemmas *)
  have "bcomp (Not b) i \<turnstile> (0,s,mem) \<rightarrow>* (?J+7,s,?MEM')"
    using exec_cb \<open>mem' i = ?B\<close> assms
    by (simp add: steps_consume step_consume)
  (* summary *)
  moreover
  have "size (bcomp (Not b) i) = size ?I1 + 7" by simp
  moreover
  have "?MEM' i = (if bval (Not b) s then 1 else 0)" by simp
  moreover
  have "\<forall>j<i. mem j = ?MEM' j" using \<open>\<forall>j<i. mem j = mem' j\<close> by simp
  ultimately
  have "bcomp (bexp.Not b) i \<turnstile> (0,s,mem) \<rightarrow>* (size (bcomp (bexp.Not b) i), s, ?MEM') \<and> ?MEM' i = (if bval (bexp.Not b) s then 1 else 0) \<and> (\<forall>j<i. mem j = ?MEM' j)" 
    by metis
  then show ?case by blast (* in two steps to prevent the solver from overheating *)
next
  text \<open>The And case follow exactly the same structure as the Not case, just with 2 IHs and some
  intermediate facts to apply the lemmas\<close>
  case (And b1 b2)
  let ?B1 = "if bval b1 s then 1 else 0"
  let ?B2 = "if bval b2 s then 1 else 0"
  let ?AND = "if \<not>bval b1 s then 0 else (if \<not>bval b2 s then 0 else 1)"
  let ?I1 = "bcomp b1 i"
  let ?I2 = "bcomp b2 (i+1)"
  let ?I3 = "[MOVI ''0'' i, MOVL ''0'' ''0'' 0, MOVI ''1'' (i+1), MOVL ''1'' ''1'' 0,
    MOVT2 ''0'' (\<lambda>x y. if x = 0 then 0 else (if y = 0 then 0 else 1)) ''0'' ''1'',
    MOVI ''1'' i, MOVS ''1'' 0 ''0'', MOVI ''0'' 0, MOVI ''1'' 0]"
  let ?J = "size ?I1"
  let ?K = "size ?I2"

  (* IHs *)
  from And.IH(1)[of i mem] obtain mem' where
    exec_cb1: "bcomp b1 i \<turnstile> (0,s,mem) \<rightarrow>* (?J,s,mem')"
    and "mem' i = ?B1" and "\<forall>j<i. mem j = mem' j"  by auto
  from And.IH(2)[of "i+1" mem'] obtain mem'' where
    exec_cb2: "bcomp b2 (i+1) \<turnstile> (0,s,mem') \<rightarrow>* (?K,s,mem'')"
    and "mem'' (i+1) = ?B2" and "\<forall>j<(i+1). mem' j = mem'' j" by auto
  from \<open>mem' i = ?B1\<close> \<open>\<forall>j<(i+1). mem' j = mem'' j\<close> have "mem'' i = ?B1" by auto

  (* More preparation *)
  let ?MEM' = "mem''(i := ?AND)"
  have "s(''0'' := 0, ''1'' := 0) = s" using assms by auto

  (* core proof *)
  have "bcomp (And b1 b2) i \<turnstile> (0,s,mem) \<rightarrow>* (?J+?K+9,s,?MEM')"
    using exec_cb1 \<open>mem' i = ?B1\<close> exec_cb2 \<open>mem'' (i+1) = ?B2\<close> \<open>mem'' i = ?B1\<close> assms
    by (simp add: steps_consume step_consume)
  (* summary *)
  moreover
  have "size (bcomp (And b1 b2) i) = ?J + ?K + 9" by simp
  moreover
  have "?MEM' i = (if bval (And b1 b2) s then 1 else 0)" by simp
  moreover
  have "\<forall>j<i. mem j = ?MEM' j" using \<open>\<forall>j<i. mem j = mem' j\<close> \<open>\<forall>j<(i+1). mem' j = mem'' j\<close> by simp
  ultimately
  have "bcomp (And b1 b2) i \<turnstile> (0, s, mem) \<rightarrow>* (size (bcomp (And b1 b2) i), s, ?MEM') \<and> ?MEM' i = (if bval (And b1 b2) s then 1 else 0) \<and> (\<forall>j<i. mem j = ?MEM' j)"
    by metis
  then show ?case by blast
next
  (* We can make use of the lemma table_comp to further compact this proof *)
  case (Less a1 a2)
  let ?A1 = "aval a1 s"
  let ?A2 = "aval a2 s"
  let ?F = "(\<lambda>x y. if x < y then 1 else 0)"

  have "?F ?A1 ?A2 = (if bval (Less a1 a2) s then 1 else 0)" by simp
  then show ?case
    using acomp_jump_free assms
      acomp_correct
      acomp_correct[of s a2 "i+1"] 
      table_comp[of s "acomp a1 i" "acomp a2 (i+1)" i ?A1 ?A2 "bcomp (Less a1 a2) i" ?F]
    by simp
qed

subsubsection \<open>Com Definitions\<close>

text \<open>vars collects all variables which are read or overwritten during the execution of a command\<close>
fun avars :: "aexp \<Rightarrow> vname list" where
  "avars (N n) = []"
| "avars (V x) = [x]"
| "avars (Plus a\<^sub>1 a\<^sub>2) = avars a\<^sub>1 @ avars a\<^sub>2"

fun vars :: "com \<Rightarrow> vname list" where
  "vars SKIP = []"
| "vars (x ::= a) = [x] @ avars a"
| "vars (c\<^sub>1;;c\<^sub>2) = vars c\<^sub>1 @ vars c\<^sub>2"
| "vars (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = vars c\<^sub>1 @ vars c\<^sub>2"
| "vars (WHILE b DO c) = vars c"

text \<open>We prove all variables not in vars are untouched by the execution of c\<close>
lemma not_in_vars_unchanged: "(c,s) \<Rightarrow> t \<Longrightarrow> v \<notin> set (vars c) \<Longrightarrow> s v = t v"
  by (induction rule: big_step_induct) auto

text \<open>store generates a series of instructions that stores all variables in 'vs' to memory beginning
at 'i' with a gap of one memory cell between each stored value\<close>
fun store :: "vname list \<Rightarrow> int \<Rightarrow> instr list" where
  "store [] _ = []"
| "store (v#vs) i = [MOVI ''0'' 0, MOVS ''0'' i v] @ store vs (i+2)"

lemma store_jump_free [intro]: "jump_free (store vs i)"
  by (induction vs arbitrary: i) auto

text \<open>This lemma shows three properties:
  1. store can be fully executed without altering the state
  2. executing store preserves the memory below i
  3. at the memory addresses starting from i, the variables in vs are stored in interlacing order,
    while the skipped memory cells are untouched

This is important for storing the variables in the IF Com, since we want to compute IF without
jump instructions.\<close>
lemma store_correct:
  assumes "''0'' \<notin> set vs" "s ''0'' = 0"
  shows "\<exists>mem'. (store vs i \<turnstile> (0,s,mem) \<rightarrow>* (size (store vs i),s,mem'))
    \<and> (\<forall>j. j<i \<longrightarrow> mem j = mem' j)
    \<and> (\<forall>j. (0 \<le> j \<and> j<size vs) \<longrightarrow> mem (i+(2*j)+1) = mem' (i+(2*j)+1) \<and> s (vs !! j) = mem' (i + 2*j))"
  using assms
proof (induction vs arbitrary: i mem)
  case (Cons v vs)
  from Cons.prems have "v \<noteq> ''0''" by (induction vs) auto
  from Cons.prems have "s(''0'' := 0) = s" by auto

  let ?MEM' = "mem(i := s v)"
  from Cons.IH[of "i+2" ?MEM'] Cons.prems obtain mem' where
    exec_IH: "store vs (i+2) \<turnstile> (0,s,?MEM') \<rightarrow>* (size (store vs (i+2)), s, mem')" and
    mem_IH: "\<forall>j. j<(i+2) \<longrightarrow> ?MEM' j = mem' j" and
    store_IH: "\<forall>j. (0 \<le> j \<and> j<size vs) \<longrightarrow> ?MEM' (i+2+(2*j)+1) = mem' (i+2+(2*j)+1)
      \<and> s (vs !! j) = mem' ((i+2) + 2*j)"
    by (metis insert_iff list.set(2))
  have exec_hd: "[MOVI ''0'' 0, MOVS ''0'' i v] \<turnstile> (0,s,mem) \<rightarrow>* (2,s,?MEM')"
    using store_jump_free \<open>v \<noteq> ''0''\<close> by (simp add: step_consume \<open>s(''0'' := 0) = s\<close> \<open>s ''0'' = 0\<close>)

  have "[MOVI ''0'' 0, MOVS ''0'' i v] @ store (vs) (i+2) \<turnstile> (0,s,mem) \<rightarrow>* (2+size (store vs (i+2)),s,mem')"
    by (rule exec_append_trans_0[of _ s mem s ?MEM']) (auto simp: exec_hd exec_IH)
  moreover
  have "\<forall>j. j<i \<longrightarrow> ?MEM' j = mem' j" 
  proof
    fix j show "j < i \<longrightarrow> ?MEM' j = mem' j"
    proof
      assume "j < i"
      then have "j < (i+2)" by simp
      then show "(mem(i := s v)) j = mem' j" using \<open>\<forall>j. j<(i+2) \<longrightarrow> ?MEM' j = mem' j\<close> by simp
    qed
  qed
  moreover
  have "\<forall>j. 0\<le>j \<and> j<size (v#vs) \<longrightarrow> mem (i+2*j+1) = mem' (i+2*j+1) \<and> s ((v#vs) !! j) = mem' (i+2*j)"
  proof (rule allI, rule impI)
    fix j 
    assume bounds: "0\<le>j \<and> j<size (v#vs)"
    show "mem (i+2*j+1) = mem' (i+2*j+1) \<and> s ((v#vs) !! j) = mem' (i+2*j)"
    proof (cases "j=0")
      case True
      have "i+1 < i+2" by simp
      with mem_IH have "mem' (i+1) = ?MEM' (i+1)" by metis
      then have 1: "mem (i+2*j+1) = mem' (i+2*j+1)" using True by auto
      have "i < i+2" by simp
      with mem_IH have "mem' i = ?MEM' i" by metis
      then have 2: "s ((v#vs) !! j) = mem' (i+2*j)" using True by auto
      from 1 2 show ?thesis by auto
    next
      case False
      then have bounds: "0 \<le> j-1" "j-1 < size vs" using bounds by simp+
      have calc: "i+2+2*(j-1)+1 = i+2*j+1" by simp
      from bounds store_IH have "mem' (i+2+2*(j-1)+1) = ?MEM' (i+2+2*(j-1)+1)" by metis
      hence 1: "mem' (i+2*j+1) = ?MEM' (i+2*j+1)" using calc by simp
      have "i \<noteq> i+2*j+1" by presburger
      hence 1: "mem' (i+2*j+1) = mem (i+2*j+1)" using 1 by auto
      have "s ((v#vs) !! j) = s (vs !! (j-1))"
        using False bounds by simp
      then have 2: "s ((v#vs) !! j) = mem' (i+2*j)" using store_IH bounds by auto
      from 1 2 show ?thesis by auto
    qed
  qed
  ultimately show ?case by auto
qed auto

text \<open>load is the counterpart that re-loads the stored values of variables back into the state. Depending
on the register value of ''0'' (expected to be either 0 or 1), the values at i, i+2, i+4... or i+1,
i+3, i+5... are loaded\<close>
fun load :: "vname list \<Rightarrow> int \<Rightarrow> instr list" where
  "load [] _ = []"
| "load (v#vs) i = [MOVL ''1'' ''0'' i, MOVR v ''1'', MOVI ''1'' 0] @ load vs (i+2)"

lemma load_jump_free[simp,intro]: "jump_free (load vs i)"
  by (induction vs arbitrary: i) auto

text \<open>The counterpart to store_correct. We again show three properties:
  1. load can be fully executed without altering the memory
  2. executing load preserves the state for all variables not in vs
  3. the variables in vs are loaded from memory beginning at address i + s ''0''. The s ''0'' offset
allows us to dynamically load the variables depending on s''0'', e.g., either from i or from i+1\<close>
lemma load_correct:
  assumes "''0'' \<notin> set vs" "''1'' \<notin> set vs" "s ''1'' = 0" "distinct vs"
  shows "\<exists>t. (load vs i \<turnstile> (0,s,mem) \<rightarrow>* (size (load vs i),t,mem))
    \<and> (\<forall>v. v \<notin> set vs \<longrightarrow> s v = t v)
    \<and> (\<forall>j. (0 \<le> j \<and> j<size vs) \<longrightarrow> t (vs !! j) = mem (i + 2*j + s ''0''))"
  using assms
proof (induction vs arbitrary: i s)
  case (Cons v vs)
  from Cons.prems have "v \<noteq> ''0''" "v \<noteq> ''1''" by (induction vs) auto
  from Cons.prems have "s(v := mem (s ''0'' + i), ''1'' := 0) = s(v := mem (s ''0'' + i))" by auto

  let ?S = "s(v := mem (s ''0'' + i))"
  let ?I = "[MOVL ''1'' ''0'' i, MOVR v ''1'', MOVI ''1'' 0]"

  from Cons.IH[of ?S "i+2"] Cons.prems obtain t where
    exec_IH: "load vs (i+2) \<turnstile> (0,?S,mem) \<rightarrow>* (size (load vs (i+2)), t, mem)" and
    state_IH: "\<forall>v. v \<notin> set vs \<longrightarrow> ?S v = t v" and
    load_IH: "\<forall>j. (0 \<le> j \<and> j<size vs) \<longrightarrow> t (vs !! j) = mem ((i+2) + 2*j + s ''0'')"
    by fastforce
  have exec_hd: "?I \<turnstile> (0,s,mem) \<rightarrow>* (3,?S,mem)"
    using load_jump_free \<open>v \<noteq> ''0''\<close> \<open>v \<noteq> ''1''\<close>
    by (simp add: step_consume \<open>s(v := mem (s ''0'' + i), ''1'' := 0) = s(v := mem (s ''0'' + i))\<close>)

  have "?I @ load (vs) (i+2) \<turnstile> (0,s,mem) \<rightarrow>* (3+size (load vs (i+2)),t,mem)"
    by (rule exec_append_trans_0[of _ s mem ?S mem]) (auto simp: exec_hd exec_IH)
  then have "load (v#vs) (i) \<turnstile> (0,s,mem) \<rightarrow>* (3+size (load vs (i+2)),t,mem)" by simp
  moreover
  have "\<forall>u. u \<notin> set (v#vs) \<longrightarrow> s u = t u" 
  proof
    fix u show "u \<notin> set (v#vs) \<longrightarrow> s u = t u"
    proof
      assume "u \<notin> set (v#vs)"
      then have "u \<notin> set vs" "u \<noteq> v" by simp+
      then show "s u = t u" using state_IH by auto
    qed
  qed
  moreover
  have "\<forall>j. (0\<le>j \<and> j<size (v#vs)) \<longrightarrow> t ((v#vs) !! j) = mem (i+2*j + s ''0'')"
  proof
    fix j show "0\<le>j \<and> j<size (v#vs) \<longrightarrow> t ((v#vs) !! j) = mem (i+2*j + s ''0'')"
    proof
      assume bounds: "0\<le>j \<and> j<size (v#vs)"
      show "t ((v#vs) !! j) = mem (i+2*j + s ''0'')"
      proof (cases "j=0")
        case True
        then have "t ((v#vs) !! j) = t v" by simp
        then show ?thesis
        proof (cases "v \<in> set vs")
          case True
          then show ?thesis using \<open>distinct (v#vs)\<close> by simp
        next
          case False
          then have "t v = mem (s ''0'' + i)" using state_IH by auto
          then show ?thesis using \<open>t ((v#vs) !! j) = t v\<close> \<open>j = 0\<close>
            by (smt (verit, del_insts))
        qed
      next
        case False
        then have "s ((v#vs) !! j) = s (vs !! (j-1))" "0 \<le> j-1" "j-1 < size vs"
          using bounds by simp+
        then show ?thesis using load_IH by auto
      qed
    qed
  qed
  ultimately show ?case by force
qed auto

(*
"ccomp SKIP i = []" |
"ccomp (x ::= a) i = (acomp a i) @ [MOVI ''0'' i, MOVL ''0'' ''0'' 0, MOVR x ''0'', MOVI ''0'' 0]" |
"ccomp (c\<^sub>1;;c\<^sub>2) i = ccomp c\<^sub>1 i @ ccomp c\<^sub>2 i" |
"ccomp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) i = (let vs = remdups (vars c\<^sub>1 @ vars c\<^sub>2) in
  (bcomp b i) @ store vs (i+1)
  @ ccomp c\<^sub>1 (i + 1 + size vs + size vs) @ [MOVI ''0'' 0] @ store vs (i+2)
  @ [MOVI ''0'' 0, MOVL ''0'' ''0'' i, MOVI ''1'' 0] @ load vs (i+1)
  @ [MOVI ''0'' 0, MOVI ''1'' 0]
  @ ccomp c\<^sub>2 (i + 1 + size vs + size vs) @ [MOVI ''0'' 0] @ store vs (i+1)
  @ [MOVI ''0'' 0, MOVL ''0'' ''0'' i, MOVI ''1'' 0] @ load vs (i+1))
  @ [MOVI ''0'' 0, MOVI ''1'' 0]" |

"ccomp (WHILE b DO c) i = (let vs = vars c;
  is = (bcomp (Not b) i) @ store vs (i+1)
  @ ccomp c (i + 1 + size vs + size vs) @ store vs (i+2)
  @ [MOVI ''0'' 0, MOVL ''0'' ''0'' i] @ load vs (i+1)
  @ [MOVI ''0'' 0, MOVL ''0'' ''0'' i] in
  is @ [JMPZ ''0'' (-(size is + 1))])" *)


subsubsection "Preservation of semantics"

text \<open>We define the loop_free and outer_loop properties. These are important, since we must execute
all branches in the compiled Com. Therefore, we must introduce a property which guarantees
termination. This property is loop_free. In a one-loop-program "WHILE b DO c" the Com c is loop-free,
we call this property outer_loop\<close>

inductive loop_free :: "com \<Rightarrow> bool" where
  "loop_free SKIP"
| "loop_free (x ::= a)"
| "loop_free c\<^sub>1 \<Longrightarrow> loop_free c\<^sub>2 \<Longrightarrow> loop_free (c\<^sub>1;; c\<^sub>2)"
| "loop_free c\<^sub>1 \<Longrightarrow> loop_free c\<^sub>2 \<Longrightarrow> loop_free (IF b THEN c\<^sub>1 ELSE c\<^sub>2)"

declare loop_free.intros[simp,intro]
inductive_cases loop_freeE[elim!]: "loop_free SKIP" "loop_free (x ::= a)" "loop_free (c\<^sub>1;; c\<^sub>2)"
  "loop_free (IF b THEN c\<^sub>1 ELSE c\<^sub>2)" "loop_free (WHILE b DO c)"
thm loop_freeE

text \<open>Com has only an outer loop and no internal loops\<close>
inductive outer_loop :: "com \<Rightarrow> bool" where
  "outer_loop SKIP"
| "outer_loop (x ::= a)"
| "loop_free c\<^sub>1 \<Longrightarrow> loop_free c\<^sub>2 \<Longrightarrow> outer_loop (c\<^sub>1;; c\<^sub>2)"
| "loop_free c\<^sub>1 \<Longrightarrow> loop_free c\<^sub>2 \<Longrightarrow> outer_loop (IF b THEN c\<^sub>1 ELSE c\<^sub>2)"
| "loop_free c \<Longrightarrow> outer_loop (WHILE b DO c)"

declare outer_loop.intros[simp,intro]
inductive_cases outer_loopE[elim!]: "outer_loop SKIP" "outer_loop (x ::= a)" "outer_loop (c\<^sub>1;; c\<^sub>2)"
  "outer_loop (IF b THEN c\<^sub>1 ELSE c\<^sub>2)" "outer_loop (WHILE b DO c)"
thm outer_loopE

lemma loop_outer[simp,intro]: "loop_free c \<Longrightarrow> outer_loop c"
  by (induction rule: loop_free.induct) auto

text \<open>This property would combine the definitions, we do not need it\<close>
theorem loop_jump_free[simp,intro]: "loop_free c = jump_free (ccomp c i)"
  sorry (* solvable by induction, but quite lengthy *)

text \<open>This is a key theorem we use to reason about the If-Clause. In a loop-preserving program, a
compiled ITE-branch which is not chosen during execution does not need to terminate for all possible
configurations, since it is not executed. However, in the MOV-compiled program, all branches are
executed during an If clause (since we don't use a JUMP instruction). The branches again don't have
any jump instructions, so we know that they are safe to execute on dummy data by knowing that they
terminate.\<close>
theorem loop_free_terminates:
  "loop_free c \<Longrightarrow> \<exists>t. (c,s) \<Rightarrow> t"
proof (induction arbitrary: s rule: loop_free.induct)
  case (3 c\<^sub>1 c\<^sub>2)
  from 3 obtain s\<^sub>2 where "(c\<^sub>1, s) \<Rightarrow> s\<^sub>2" by auto
  moreover from 3 obtain s\<^sub>3 where "(c\<^sub>2, s\<^sub>2) \<Rightarrow> s\<^sub>3" by auto
  ultimately show ?case by blast
next
  case (4 c\<^sub>1 c\<^sub>2 b)
  from 4 obtain t\<^sub>1 where "(c\<^sub>1, s) \<Rightarrow> t\<^sub>1" by auto
  moreover from 4 obtain t\<^sub>2 where "(c\<^sub>2, s) \<Rightarrow> t\<^sub>2" by auto
  ultimately show ?case
    by (cases "bval b s") auto
qed auto

subsubsection \<open>Com Correctness\<close>


text \<open>This is the most interesting part. We compile loop-free programs using ccomp_if, which does
not require jump instructions.

The reason is storing/loading of state for IF-THEN-ELSE, i.e., before executing a
branch, the entire state (that would be overwritten during execution) is saved to memory and again
saved after the execution. Afterwards, we load the state according to the boolean expression.

In practice, this is a little more complicated, since the original state must be available for the
execution of the second branch. Therefore, we compile an "If b THEN c1 ELSE c2" like this:
1. Store the evaluation of b depending on the state s to memory
2. Store s to memory
3. Execute c1
4. Store the updated state s1 to memory
5. Load stored s from memory and reset state (to before c1)
6. Execute c2
7. Store the updated state s2 to memory
8. Load the value of b into a register
9. Load s1 or s2 depending on the value of b
\<close>

text \<open>ccomp_if only compiles loop-free programs\<close>
fun ccomp_if :: "com \<Rightarrow> int \<Rightarrow> instr list" where
"ccomp_if SKIP i = []" |
"ccomp_if (x ::= a) i = (acomp a i) @ [MOVI ''0'' i, MOVL ''0'' ''0'' 0, MOVR x ''0'', MOVI ''0'' 0]" |
"ccomp_if (c\<^sub>1;;c\<^sub>2) i = ccomp_if c\<^sub>1 i @ ccomp_if c\<^sub>2 i" |
"ccomp_if (IF b THEN c\<^sub>1 ELSE c\<^sub>2) i = (let vs = remdups (vars c\<^sub>1 @ vars c\<^sub>2) in
  (bcomp b i) @ store vs (i+1)
  @ ccomp_if c\<^sub>1 (i + 1 + size vs + size vs) @ [MOVI ''0'' 0] @ store vs (i+2)
  @ [MOVI ''0'' 0, MOVL ''0'' ''0'' i, MOVI ''1'' 0] @ load vs (i+1)
  @ [MOVI ''0'' 0, MOVI ''1'' 0]
  @ ccomp_if c\<^sub>2 (i + 1 + size vs + size vs) @ [MOVI ''0'' 0] @ store vs (i+1)
  @ [MOVI ''0'' 0, MOVL ''0'' ''0'' i, MOVI ''1'' 0] @ load vs (i+1))
  @ [MOVI ''0'' 0, MOVI ''1'' 0]" |
"ccomp_if (WHILE b DO c) i = []"

text \<open>We make use of the property, that a WHILE program behaves like an IF-THEN-ELSE with a JUMP to
compile it. We just have to store the boolean value to memory before executing the loop body, since
the loop body changes the state, and we need to jump depending on the boolean value after the loop
body\<close>

text \<open>ccomp compiles outer-loop programs\<close>
fun ccomp :: "com \<Rightarrow> int \<Rightarrow> instr list" where
  "ccomp (WHILE b DO c) i = (let cc = (bcomp b i) @ ccomp_if (IF b THEN c ELSE SKIP) (i+1)
    @ [MOVI ''0'' 0, MOVL ''0'' ''0'' i, MOVT ''0'' (\<lambda>x. if x = 0 then 1 else 0) ''0''] in
    cc @ [JMPZ ''0'' (-(size cc + 1)), MOVI ''0'' 0])"
| "ccomp c i = ccomp_if c i"


text \<open>The full correctness proof of ccomp_if. We assume a program to have the loop_freey property and
that it does not conflict with our registers. We show that the memory below the address i is preserved\<close>
lemma ccomp_if_bigstep:
  assumes "(c,s) \<Rightarrow> t"
  assumes "loop_free c"
  assumes "s ''0'' = 0" "s ''1'' = 0" "''0'' \<notin> set (vars c)" "''1'' \<notin> set (vars c)" (* registers excluded *)
  shows "\<exists>mem'. (ccomp_if c i \<turnstile> (0,s,mem) \<rightarrow>* (size(ccomp_if c i),t,mem'))
    \<and> (\<forall>j<i. mem j = mem' j)"
  using assms
proof (induction c arbitrary: s t i mem)
  case (Assign x a)
  let ?A = "aval a s"
  let ?I1 = "acomp a i"
  let ?I2 = "[MOVI ''0'' i, MOVL ''0'' ''0'' 0, MOVR x ''0'', MOVI ''0'' 0]"
  let ?J = "size ?I1"
  from Assign.prems(1) have [simp]: "t = s(x := ?A)" by auto

  from acomp_correct[of s a i] Assign.prems obtain mem' where
    exec_ca: "?I1 \<turnstile> (0,s,mem) \<rightarrow>* (?J,s,mem')"
    and "mem' i = ?A" and "\<forall>j<i. mem j = mem' j" by auto

  (* More preparation *)
  have "s(x := ?A, ''0'' := 0) = s(x := ?A)" using Assign.prems by auto

  (* core proof, very short thanks to lemmas *)
  have "ccomp_if (x ::= a) i \<turnstile> (0,s,mem) \<rightarrow>* (?J+4,s(x := ?A),mem')"
    using exec_ca \<open>mem' i = ?A\<close>
    apply -
    apply (simp add: steps_consume step_consume \<open>s(x := ?A, ''0'' := 0) = s(x := ?A)\<close>)
    done
  (* summary *)
  moreover
  have "ccomp_if (x ::= a) i = ?I1 @ ?I2" by simp
  moreover
  have "size (ccomp_if (x ::= a) i) = ?J + 4" by simp
  moreover
  have "\<forall>j<i. mem j = mem' j" using \<open>\<forall>j<i. mem j = mem' j\<close> by simp
  ultimately
  have "ccomp_if (x ::= a) i \<turnstile> (0,s,mem) \<rightarrow>* (size (ccomp_if (x ::= a) i), t, mem') \<and> (\<forall>j<i. mem j = mem' j)"
    using \<open>t = s(x := ?A)\<close> by metis
  then show ?case by blast
next
  case (Seq c\<^sub>1 c\<^sub>2) (* case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3) *)
  from Seq.prems(1) obtain s\<^sub>2 where
    [simp]: "(c\<^sub>1,s) \<Rightarrow> s\<^sub>2" "(c\<^sub>2,s\<^sub>2) \<Rightarrow> t" by blast
  have "''0'' \<notin> set (vars c\<^sub>1)" "''1'' \<notin> set (vars c\<^sub>1)" using Seq.prems by simp+
  then have "s\<^sub>2 ''0'' = 0" "s\<^sub>2 ''1'' = 0"
    using \<open>(c\<^sub>1,s) \<Rightarrow> s\<^sub>2\<close> not_in_vars_unchanged Seq.prems by metis+

  (* IHs *)
  from Seq.IH(1)[of s s\<^sub>2 i] Seq.prems \<open>(c\<^sub>1,s) \<Rightarrow> s\<^sub>2\<close> obtain mem' where
    exec1: "ccomp_if c\<^sub>1 i \<turnstile> (0, s, mem) \<rightarrow>* (size (ccomp_if c\<^sub>1 i), s\<^sub>2, mem')" and
    mem1: "(\<forall>j<i. mem j = mem' j)" by auto
  from Seq.IH(2)[of s\<^sub>2 t i mem'] \<open>s\<^sub>2 ''0'' = 0\<close> \<open>s\<^sub>2 ''1'' = 0\<close> Seq.prems \<open>(c\<^sub>2,s\<^sub>2) \<Rightarrow> t\<close> obtain mem'' where
    exec2: "ccomp_if c\<^sub>2 i \<turnstile> (0, s\<^sub>2, mem') \<rightarrow>* (size (ccomp_if c\<^sub>2 i), t, mem'')" and
    mem2: "(\<forall>j<i. mem' j = mem'' j)" by auto

  (* combine *)
  from exec1 have "ccomp_if (c\<^sub>1;; c\<^sub>2) i \<turnstile> (0, s, mem) \<rightarrow>* (size (ccomp_if c\<^sub>1 i), s\<^sub>2, mem')"
    using exec_appendR by simp
  moreover
  from exec2 have "ccomp_if (c\<^sub>1;; c\<^sub>2) i \<turnstile> (size (ccomp_if c\<^sub>1 i), s\<^sub>2, mem') \<rightarrow>* (size (ccomp_if c\<^sub>2 i) + size (ccomp_if c\<^sub>1 i), t, mem'')"
    using exec_appendL by auto
  moreover
  have "size (ccomp_if (c\<^sub>1;; c\<^sub>2) i) = size (ccomp_if c\<^sub>2 i) + size (ccomp_if c\<^sub>1 i)" by simp
  moreover
  from  mem1 mem2 have "\<forall>j<i. mem j = mem'' j"  by simp
  ultimately show ?case
    by (metis (no_types, lifting) star_trans)
next
  case (If b c\<^sub>1 c\<^sub>2)
  text \<open>This prove needs to combine many different assumptions, so it will be very lengthy.
We split the work into a setup, where we collect the states resulting from each sub-command (e.g.,
store/load) and combine it all together in the end\<close>

  from If.prems(1,2) loop_free_terminates obtain t\<^sub>1 where
    [simp]: "(c\<^sub>1,s) \<Rightarrow> t\<^sub>1" by blast
  (* We don't know the branch yet, so we obtain two states
    and choose later which one is equal to t *)
  let ?VS = "remdups (vars c\<^sub>1 @ vars c\<^sub>2)"
  let ?J = "i+1+size ?VS+size ?VS"

  let ?I1 = "(bcomp b i)"
  let ?I2 = "store ?VS (i+1)"
  let ?I3 = "ccomp_if c\<^sub>1 ?J"
  let ?I3_1 = "[MOVI ''0'' 0]"
  let ?I4 = "store ?VS (i+2)"
  let ?I4_1 = "[MOVI ''0'' 0, MOVL ''0'' ''0'' i, MOVI ''1'' 0]"
  let ?I5 = "load ?VS (i+1)"
  let ?I5_1 = "[MOVI ''0'' 0, MOVI ''1'' 0]"
  let ?I6 = "ccomp_if c\<^sub>2 ?J"
  let ?I6_1 = "[MOVI ''0'' 0]"
  let ?I7 = "store ?VS (i+1)"
  let ?I7_1 = "[MOVI ''0'' 0, MOVL ''0'' ''0'' i, MOVI ''1'' 0]"
  let ?I8 = "load ?VS (i+1)"
  let ?I8_1 = "[MOVI ''0'' 0, MOVI ''1'' 0]"

  let ?B = "if bval b s then 1 else 0"

  (* setup *)

  (* b *)
  from bcomp_correct[of s b i] If.prems obtain mem\<^sub>b where
    exec_cb: "?I1 \<turnstile> (0,s,mem) \<rightarrow>* (size ?I1,s,mem\<^sub>b)" and
    b: "mem\<^sub>b i = ?B" and mem_cb: "\<forall>j<i. mem j = mem\<^sub>b j" by auto

  (* first store *)
  from store_correct[of ?VS s "i+1" mem\<^sub>b] If.prems obtain mem\<^sub>s\<^sub>1 where
    exec_s1: "?I2 \<turnstile> (0,s,mem\<^sub>b) \<rightarrow>* (size ?I2,s,mem\<^sub>s\<^sub>1)" and
    mem_s1: "\<forall>j<i+1. mem\<^sub>b j = mem\<^sub>s\<^sub>1 j" and
    store_s1: "\<forall>j. 0\<le>j \<and> j<size ?VS \<longrightarrow> s (?VS !! j) = mem\<^sub>s\<^sub>1 (i+1+2*j)" by auto
  (* we also construct the full execution sequence in each step *)
  let ?I = "?I1 @ ?I2" 
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,s,mem\<^sub>s\<^sub>1)"
    using exec_append_trans_0 exec_cb exec_s1 by simp
  (* and we show the preservation of memory in each step *)
  have mem: "\<forall>j<i. mem j = mem\<^sub>s\<^sub>1 j" using mem_cb mem_s1 by fastforce

  (* IH 1 *)
  from If.IH(1)[of s t\<^sub>1 ?J mem\<^sub>s\<^sub>1] If.prems \<open>(c\<^sub>1,s) \<Rightarrow> t\<^sub>1\<close> obtain mem\<^sub>c\<^sub>1 where
    exec_c1: "?I3 \<turnstile> (0,s,mem\<^sub>s\<^sub>1) \<rightarrow>* (size ?I3,t\<^sub>1,mem\<^sub>c\<^sub>1)" and
    mem_c1: "(\<forall>j<(i+1+size ?VS+size ?VS). mem\<^sub>s\<^sub>1 j = mem\<^sub>c\<^sub>1 j)" by auto
  let ?I = "?I @ ?I3"
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,t\<^sub>1,mem\<^sub>c\<^sub>1)"
    by (rule exec_append_trans_1[OF exec exec_c1])
  have mem: "\<forall>j<i. mem j = mem\<^sub>c\<^sub>1 j" using mem mem_c1 by fastforce

  (* cleanup *)
  have exec_c1_1: "?I3_1 \<turnstile> (0,t\<^sub>1,mem\<^sub>c\<^sub>1) \<rightarrow>* (size ?I3_1,t\<^sub>1(''0'':=0),mem\<^sub>c\<^sub>1)"
    by (simp add: step_consume)
  let ?I = "?I @ ?I3_1"
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,t\<^sub>1(''0'':=0),mem\<^sub>c\<^sub>1)"
    by (rule exec_append_trans_1[OF exec exec_c1_1])

  (* store vars of c\<^sub>1 *)
  from store_correct[of ?VS "t\<^sub>1(''0'':=0)" "i+2" mem\<^sub>c\<^sub>1] If.prems obtain mem\<^sub>s\<^sub>2 where
    exec_s2: "?I4 \<turnstile> (0,t\<^sub>1(''0'':=0),mem\<^sub>c\<^sub>1) \<rightarrow>* (size ?I4,t\<^sub>1(''0'':=0),mem\<^sub>s\<^sub>2)" and
    mem_s2: "\<forall>j<i+2. mem\<^sub>c\<^sub>1 j = mem\<^sub>s\<^sub>2 j" and
    store_s2: "\<forall>j. 0\<le>j \<and> j<size ?VS \<longrightarrow> mem\<^sub>c\<^sub>1 (i+2+2*j+1) = mem\<^sub>s\<^sub>2 (i+2+2*j+1) \<and> (t\<^sub>1(''0'':=0)) (?VS !! j) = mem\<^sub>s\<^sub>2 (i+2+2*j)" by auto
  let ?I = "?I @ ?I4"
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,t\<^sub>1(''0'':=0),mem\<^sub>s\<^sub>2)"
    by (rule exec_append_trans_1[OF exec exec_s2])
  have mem: "\<forall>j<i. mem j = mem\<^sub>s\<^sub>2 j" using mem mem_s2 by fastforce

  (* load the boolean result *)
  have "mem\<^sub>s\<^sub>2 i = ?B" using mem_s2 mem_c1 mem_s1 b by simp
  then have exec_s2_1: "?I4_1 \<turnstile> (0,t\<^sub>1(''0'':=0),mem\<^sub>s\<^sub>2) \<rightarrow>* (3,t\<^sub>1(''0'':=?B,''1'':=0),mem\<^sub>s\<^sub>2)"
    by (simp add: step_consume)
  let ?I = "?I @ ?I4_1"
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,t\<^sub>1(''0'':=?B,''1'':=0),mem\<^sub>s\<^sub>2)"
    by (rule exec_append_trans_1[OF exec]) (auto simp: exec_s2_1)

  (* load the vars depending on b *)
  have "(t\<^sub>1(''0'':=?B,''1'':=0)) ''0'' = ?B" by simp
  with load_correct[of ?VS "t\<^sub>1(''0'':=?B,''1'':=0)" "i+1" mem\<^sub>s\<^sub>2] If.prems obtain tl\<^sub>1 where
    exec_l1: "?I5 \<turnstile> (0,t\<^sub>1(''0'':=?B,''1'':=0),mem\<^sub>s\<^sub>2) \<rightarrow>* (size ?I5,tl\<^sub>1,mem\<^sub>s\<^sub>2)" and 
    pres_l1: "(\<forall>v. v\<notin>set ?VS \<longrightarrow> (t\<^sub>1(''0'':=?B,''1'':=0)) v = tl\<^sub>1 v)" and (* preserved *)
    load_l1: "(\<forall>j. 0\<le>j \<and> j<size ?VS \<longrightarrow> tl\<^sub>1 (?VS !! j) = mem\<^sub>s\<^sub>2 (i+1+2*j+?B))" by auto
  let ?I = "?I @ ?I5"
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,tl\<^sub>1,mem\<^sub>s\<^sub>2)"
    by (rule exec_append_trans_1[OF exec exec_l1])

  (* cleanup *)
  have exec_l1_1: "?I5_1 \<turnstile> (0,tl\<^sub>1,mem\<^sub>s\<^sub>2) \<rightarrow>* (size ?I5_1,tl\<^sub>1(''0'':=0,''1'':=0),mem\<^sub>s\<^sub>2)"
    by (simp add: step_consume)
  let ?I = "?I @ ?I5_1"
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,tl\<^sub>1(''0'':=0,''1'':=0),mem\<^sub>s\<^sub>2)"
    by (rule exec_append_trans_1[OF exec exec_l1_1])

  (* IH 2 *)
  obtain tl\<^sub>1' where "tl\<^sub>1' = tl\<^sub>1(''0'':=0,''1'':=0)" by simp
  (* for some reason, we must trick the auto-solver
    here not to simplify t *)
  from If.prems(1,2) loop_free_terminates obtain t\<^sub>2 where
    [simp]: "(c\<^sub>2,tl\<^sub>1') \<Rightarrow> t\<^sub>2" by blast
  have "tl\<^sub>1' ''0'' = 0" "tl\<^sub>1' ''1'' = 0" using \<open>tl\<^sub>1' = tl\<^sub>1(''0'':=0,''1'':=0)\<close> by simp+
  with If.IH(2)[of tl\<^sub>1' t\<^sub>2 ?J mem\<^sub>s\<^sub>2] If.prems \<open>(c\<^sub>2,tl\<^sub>1') \<Rightarrow> t\<^sub>2\<close> obtain mem\<^sub>c\<^sub>2 where
    exec_c2: "?I6 \<turnstile> (0,tl\<^sub>1',mem\<^sub>s\<^sub>2) \<rightarrow>* (size ?I6,t\<^sub>2,mem\<^sub>c\<^sub>2)" and
    mem_c2: "(\<forall>j<(i+1+size ?VS+size ?VS). mem\<^sub>s\<^sub>2 j = mem\<^sub>c\<^sub>2 j)" by auto

  from exec_c2 \<open>tl\<^sub>1' = tl\<^sub>1(''0'':=0,''1'':=0)\<close> have exec_c2':
    "?I6 \<turnstile> (0,tl\<^sub>1(''0'':=0,''1'':=0),mem\<^sub>s\<^sub>2) \<rightarrow>* (size ?I6,t\<^sub>2,mem\<^sub>c\<^sub>2)" by blast
  let ?I = "?I @ ?I6"
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,t\<^sub>2,mem\<^sub>c\<^sub>2)"
    by (rule exec_append_trans_1[OF exec exec_c2'])

  have mem: "\<forall>j<i. mem j = mem\<^sub>c\<^sub>2 j" using mem mem_c2 by fastforce

  (* cleanup *)
  have exec_c2_1: "?I6_1 \<turnstile> (0,t\<^sub>2,mem\<^sub>c\<^sub>2) \<rightarrow>* (1,t\<^sub>2(''0'':=0),mem\<^sub>c\<^sub>2)"
    by (simp add: step_consume)
  let ?I = "?I @ ?I6_1"
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,t\<^sub>2(''0'':=0),mem\<^sub>c\<^sub>2)"
    by (rule exec_append_trans_1[OF exec]) (auto simp: exec_c2_1)

  (* store vars of c\<^sub>2 *)
  from store_correct[of ?VS "t\<^sub>2(''0'':=0)" "i+1" mem\<^sub>c\<^sub>2] If.prems obtain mem\<^sub>s\<^sub>3 where
    exec_s3: "?I7 \<turnstile> (0,t\<^sub>2(''0'':=0),mem\<^sub>c\<^sub>2) \<rightarrow>* (size ?I7,t\<^sub>2(''0'':=0),mem\<^sub>s\<^sub>3)" and
    mem_s3: "\<forall>j<i+1. mem\<^sub>c\<^sub>2 j = mem\<^sub>s\<^sub>3 j" and
    store_s3: "\<forall>j. 0\<le>j \<and> j<size ?VS \<longrightarrow> mem\<^sub>c\<^sub>2 (i+1+2*j+1) = mem\<^sub>s\<^sub>3 (i+1+2*j+1) \<and> (t\<^sub>2(''0'':=0)) (?VS !! j) = mem\<^sub>s\<^sub>3 (i+1+2*j)" by auto
  let ?I = "?I @ ?I7"
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,t\<^sub>2(''0'':=0),mem\<^sub>s\<^sub>3)"
    by (rule exec_append_trans_1[OF exec exec_s3])
  have mem: "\<forall>j<i. mem j = mem\<^sub>s\<^sub>3 j" using mem mem_s3 by fastforce

  (* load the boolean result *)
  have "mem\<^sub>s\<^sub>3 i = ?B" using mem_s3 mem_c2 \<open>mem\<^sub>s\<^sub>2 i = ?B\<close> by simp
  then have exec_s3_1: "?I7_1 \<turnstile> (0,t\<^sub>2(''0'':=0),mem\<^sub>s\<^sub>3) \<rightarrow>* (3,t\<^sub>2(''0'':=?B,''1'':=0),mem\<^sub>s\<^sub>3)"
    by (simp add: step_consume)
  let ?I = "?I @ ?I7_1"
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,t\<^sub>2(''0'':=?B,''1'':=0),mem\<^sub>s\<^sub>3)"
    by (rule exec_append_trans_1[OF exec]) (auto simp: exec_s3_1)

  (* load the vars depending on b *)
  have "(t\<^sub>2(''0'':=?B,''1'':=0)) ''0'' = ?B" by simp
  with load_correct[of ?VS "t\<^sub>2(''0'':=?B,''1'':=0)" "i+1" mem\<^sub>s\<^sub>3] If.prems obtain tl\<^sub>2 where
    exec_l2: "?I8 \<turnstile> (0,t\<^sub>2(''0'':=?B,''1'':=0),mem\<^sub>s\<^sub>3) \<rightarrow>* (size ?I8,tl\<^sub>2,mem\<^sub>s\<^sub>3)" and 
    pres_l2: "(\<forall>v. v\<notin>set ?VS \<longrightarrow> (t\<^sub>2(''0'':=?B,''1'':=0)) v = tl\<^sub>2 v)" and (* preserved *)
    load_l2: "(\<forall>j. 0\<le>j \<and> j<size ?VS \<longrightarrow> tl\<^sub>2 (?VS !! j) = mem\<^sub>s\<^sub>3 (i+1+2*j+?B))" by auto
  let ?I = "?I @ ?I8"
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,tl\<^sub>2,mem\<^sub>s\<^sub>3)"
    by (rule exec_append_trans_1[OF exec exec_l2])

  (* cleanup *)
  let ?T = "tl\<^sub>2(''0'':=0,''1'':=0)" (* This is our final state *)

  have exec_l2_1: "?I8_1 \<turnstile> (0,tl\<^sub>2,mem\<^sub>s\<^sub>3) \<rightarrow>* (size ?I8_1,?T,mem\<^sub>s\<^sub>3)"
    by (simp add: step_consume)
  let ?I = "?I @ ?I8_1"
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,?T,mem\<^sub>s\<^sub>3)"
    by (rule exec_append_trans_1[OF exec exec_l2_1])

  (* bringing it together *)
  let ?C = "IF b THEN c\<^sub>1 ELSE c\<^sub>2"

  (* show the state change fits *)
  have "t ''0'' = 0" using If.prems(3) not_in_vars_unchanged[OF \<open>(?C,s) \<Rightarrow> t\<close> If.prems(5)]
    by simp
  have "t ''1'' = 0" using If.prems(4) not_in_vars_unchanged[OF \<open>(?C,s) \<Rightarrow> t\<close> If.prems(6)]
    by simp

  (* Show the state is as in big-step *)
  have "t = ?T"
    text \<open>This is the point, where the actual big-step-logic is applied. Before, we only required
the assumption, that a program terminates.\<close>
  proof (cases "bval b s")
    case True
    (* first branch executed *)
    then have \<open>(c\<^sub>1,s) \<Rightarrow> t\<close> using If.prems(1) by blast
    then have "t = t\<^sub>1" using \<open>(c\<^sub>1,s) \<Rightarrow> t\<^sub>1\<close> using big_step_determ by blast
    then have "t\<^sub>1(''0'':=0) = t" using \<open>t ''0'' = 0\<close> by auto

    (* fist store/load does not change vars due to execution of c\<^sub>1 *)
    have pres: "\<forall>v. v \<notin> set ?VS \<longrightarrow> (t\<^sub>1(''0'' := 1, ''1'' := 0)) v = tl\<^sub>1 v"
      using pres_l1 True by simp
    have load: "\<forall>v. v \<in> set ?VS \<longrightarrow> t v = tl\<^sub>1 v"
    proof (rule allI, rule impI)
      fix v assume "v \<in> set ?VS"
      then obtain j where j_bounds: "?VS !! j = v" "0 \<le> j \<and> j < size ?VS"
        using inth_exists by metis
      then have "t v = mem\<^sub>s\<^sub>2 (i + 2 + 2 * j)" 
        using store_s2 \<open>t\<^sub>1(''0'':=0) = t\<close> by auto
      then have "t v = mem\<^sub>s\<^sub>2 (i + 1 + 2 * j + 1)"
        by (smt (verit))
      then show "t v = tl\<^sub>1 v"
        using load_l1 j_bounds True by auto
    qed

    have "\<forall>v. v \<noteq> ''0'' \<and> v \<noteq> ''1'' \<longrightarrow> t v = tl\<^sub>1 v"
    proof (rule allI, rule impI)
      fix v assume assm: "v \<noteq> ''0'' \<and> v \<noteq> ''1''"
      show "t v = tl\<^sub>1 v"
      proof (cases "v \<in> set ?VS")
        case True
        then show ?thesis using load by blast
      next
        case False
        then have "t v = (t\<^sub>1(''0'' := 1, ''1'' := 0)) v"
          using \<open>t\<^sub>1(''0'':=0) = t\<close> assm by auto
        then show ?thesis using pres False by auto
      qed
    qed
    have "\<forall>v. t v = (tl\<^sub>1(''0'':=0,''1'':=0)) v"
    proof (rule allI)
      fix v
      show "t v = (tl\<^sub>1(''0'' := 0, ''1'' := 0)) v"
        by (cases "v \<noteq> ''0'' \<and> v \<noteq> ''1''") (simp add: \<open>\<forall>v. v \<noteq> ''0'' \<and> v \<noteq> ''1'' \<longrightarrow> t v = tl\<^sub>1 v\<close> \<open>t ''0'' = 0\<close> \<open>t ''1'' = 0\<close>)+
    qed
    then have "t = tl\<^sub>1'" using \<open>tl\<^sub>1' = tl\<^sub>1(''0'':=0,''1'':=0)\<close> by blast

    (* second store/load does not change vars due to store/load *)
    thm mem_c2
    thm pres_l2

    have pres: "\<forall>v. v \<notin> set ?VS \<longrightarrow> (t v = ?T v)"
    proof (rule allI, rule impI)
      fix v assume assm: "v \<notin> set ?VS"
      then have "v \<notin> set (vars c\<^sub>1 @ vars c\<^sub>2)" by simp
      then have "v \<notin> set (vars c\<^sub>2)" by simp
      then have "t v = t\<^sub>2 v" using \<open>t = tl\<^sub>1'\<close> not_in_vars_unchanged[OF \<open>(c\<^sub>2,tl\<^sub>1') \<Rightarrow> t\<^sub>2\<close>] by simp
      
      have pres: "\<forall>v. v \<notin> set ?VS \<longrightarrow> (t\<^sub>2(''0'' := 1, ''1'' := 0)) v = tl\<^sub>2 v"
        using pres_l2 True by simp
      
      show "t v = (tl\<^sub>2(''0'':=0,''1'':=0)) v"
      proof (cases "v \<noteq> ''0'' \<and> v \<noteq> ''1''")
        case True
        then show ?thesis using \<open>t v = t\<^sub>2 v\<close> pres assm by auto
      next
        case False
        then show ?thesis using \<open>t ''0'' = 0\<close> \<open>t ''1'' = 0\<close> by auto
      qed
    qed
    have load: "\<forall>v. v \<in> set ?VS \<longrightarrow> (t v = ?T v)"
    proof (rule allI, rule impI)
      fix v assume assm: "v \<in> set ?VS"
      then obtain j where j_bounds: "?VS !! j = v" "0 \<le> j \<and> j < size ?VS"
        using inth_exists by metis
      have "(i+1+2*j+1)<i+1+size ?VS+size ?VS" using j_bounds(2) by simp

      from j_bounds have "t v = mem\<^sub>s\<^sub>2 (i + 2 + 2 * j)" 
        using store_s2 \<open>t\<^sub>1(''0'':=0) = t\<close> by auto
      then have "t v = mem\<^sub>s\<^sub>2 (i + 1 + 2 * j + 1)"
        by (smt (verit))
      then have "t v = mem\<^sub>c\<^sub>2 (i + 1 + 2 * j + 1)"
        using mem_c2 \<open>(i+1+2*j+1)<i+1+size ?VS+size ?VS\<close> by metis
      then have "t v = mem\<^sub>s\<^sub>3 (i + 1 + 2 * j + 1)"
        using store_s3 j_bounds(2) by simp
      then have "t v = tl\<^sub>2 v"
        using load_l2 j_bounds True by auto
      then show "t v = ?T v"
        using \<open>t ''0'' = 0\<close> \<open>t ''1'' = 0\<close> by auto
    qed
    
    have "\<forall>v. t v = ?T v"
    proof (rule allI)
      fix v
      show "t v = ?T v"
        by (cases "v \<in> set ?VS") (simp add: pres load)+
    qed
    then show "t = ?T" by blast
  next
    case False
    text \<open>This is almost the same prove as in the True-case in inverse, but with some adjustments
due to different arithmetics\<close>

    (* fist store/load does not change vars due to store/load *)
    have pres: "\<forall>v. v \<notin> set ?VS \<longrightarrow> s v = (tl\<^sub>1(''0'':=0,''1'':=0)) v"
    proof (rule allI, rule impI)
      fix v assume assm: "v \<notin> set ?VS"
      then have "v \<notin> set (vars c\<^sub>1 @ vars c\<^sub>2)" by simp
      then have "v \<notin> set (vars c\<^sub>1)" by simp
      then have "s v = t\<^sub>1 v" using not_in_vars_unchanged[OF \<open>(c\<^sub>1,s) \<Rightarrow> t\<^sub>1\<close>] by simp
      then have "(t\<^sub>1(''0'' := 0, ''1'' := 0)) v = s v" using If.prems by auto
      
      have pres: "\<forall>v. v \<notin> set ?VS \<longrightarrow> (t\<^sub>1(''0'' := 0, ''1'' := 0)) v = tl\<^sub>1 v"
        using pres_l1 False by simp
      then show "s v = (tl\<^sub>1(''0'':=0,''1'':=0)) v"
        using \<open>(t\<^sub>1(''0'' := 0, ''1'' := 0)) v = s v\<close> assm by auto
    qed
    have load: "\<forall>v. v \<in> set ?VS \<longrightarrow> s v = (tl\<^sub>1(''0'':=0,''1'':=0)) v"
    proof (rule allI, rule impI)
      fix v assume assm: "v \<in> set ?VS"
      then obtain j where j_bounds: "?VS !! j = v" "0 \<le> j \<and> j < size ?VS"
        using inth_exists by metis
      have "(i+2*j+1)<i+1+size ?VS+size ?VS" using j_bounds(2) by simp
      have "i+1+2*j = i+2+2*(j-1)+1" by simp
      have "i+2*j+1 = i+2+2*(j-1)+1" by simp
      then have "j-1 < size ?VS" using j_bounds(2) by simp

      from j_bounds have "s v = mem\<^sub>s\<^sub>1 (i + 1 + 2 * j)" 
        using store_s1 by blast
      then have "s v = mem\<^sub>s\<^sub>1 (i + 2 * j + 1)"
        by (smt (verit))
      then have "s v = mem\<^sub>c\<^sub>1 (i + 2 * j + 1)"
        using mem_c1 using \<open>(i+2*j+1)<i+1+size ?VS+size ?VS\<close> by simp
      then have c1: "s v = mem\<^sub>c\<^sub>1 (i + 2 + 2 * (j-1) + 1)"
        using \<open>i+2*j+1 = i+2+2*(j-1)+1\<close> by metis

      text \<open>in the case of "j=0" we must use the other memory preservation hypothesis\<close>
      have "s v = mem\<^sub>s\<^sub>2 (i + 2 + 2 * (j-1) + 1)"
      proof (cases "j = 0")
        case True
        then have "i+2+2*(j-1)+1 < i+2" using j_bounds by simp
        then show ?thesis
          using mem_s2 c1 by auto
      next
        case False
        then have "0 \<le> j-1" using j_bounds by simp
        then have "mem\<^sub>c\<^sub>1 (i + 2 + 2 * (j-1) + 1) = mem\<^sub>s\<^sub>2 (i + 2 + 2 * (j-1) + 1)"
          using  \<open>j-1 < size ?VS\<close> store_s2 by blast
        then show ?thesis using c1 by auto
      qed
      then have "s v = mem\<^sub>s\<^sub>2 (i + 1 + 2 * j)"
        using \<open>i+1+2*j = i+2+2*(j-1)+1\<close> by metis
      then have "s v = tl\<^sub>1 v"
        using load_l1 j_bounds False by auto
      then show "s v = (tl\<^sub>1(''0'':=0,''1'':=0)) v"
        using \<open>s ''0'' = 0\<close> \<open>s ''1'' = 0\<close> by auto
    qed

    have "\<forall>v. s v = (tl\<^sub>1(''0'':=0,''1'':=0)) v"
    proof (rule allI)
      fix v
      show "s v = (tl\<^sub>1(''0'':=0,''1'':=0)) v"
        by (cases "v \<in> set ?VS") (simp add: pres load)+
    qed
    then have "s = tl\<^sub>1'" using \<open>tl\<^sub>1' = tl\<^sub>1(''0'':=0,''1'':=0)\<close> by blast

    (* second branch executed *)
    from False have \<open>(c\<^sub>2,s) \<Rightarrow> t\<close> using If.prems(1) by blast
    then have "t = t\<^sub>2" using \<open>s = tl\<^sub>1'\<close> \<open>(c\<^sub>2,tl\<^sub>1') \<Rightarrow> t\<^sub>2\<close> using big_step_determ by blast
    then have "t\<^sub>2(''0'':=0) = t" using \<open>t ''0'' = 0\<close> by auto

    (* second store/load does not change vars due to execution of c\<^sub>2 *)
    have pres: "\<forall>v. v \<notin> set ?VS \<longrightarrow> (t\<^sub>2(''0'' := 0, ''1'' := 0)) v = tl\<^sub>2 v"
      using pres_l2 False by simp
    have load: "\<forall>v. v \<in> set ?VS \<longrightarrow> t v = tl\<^sub>2 v"
    proof (rule allI, rule impI)
      fix v assume "v \<in> set ?VS"
      then obtain j where j_bounds: "?VS !! j = v" "0 \<le> j \<and> j < size ?VS"
        using inth_exists by metis
      then have "t v = mem\<^sub>s\<^sub>3 (i + 1 + 2 * j)" 
        using store_s3 \<open>t\<^sub>2(''0'':=0) = t\<close> by auto
      then show "t v = tl\<^sub>2 v"
        using load_l2 j_bounds False by auto
    qed

    have "\<forall>v. v \<noteq> ''0'' \<and> v \<noteq> ''1'' \<longrightarrow> t v = tl\<^sub>2 v"
    proof (rule allI, rule impI)
      fix v assume assm: "v \<noteq> ''0'' \<and> v \<noteq> ''1''"
      show "t v = tl\<^sub>2 v"
      proof (cases "v \<in> set ?VS")
        case True
        then show ?thesis using load by blast
      next
        case False
        then have "t v = (t\<^sub>2(''0'' := 0, ''1'' := 0)) v"
          using \<open>t\<^sub>2(''0'':=0) = t\<close> assm by auto
        then show ?thesis using pres False by auto
      qed
    qed
    have "\<forall>v. t v = (tl\<^sub>2(''0'':=0,''1'':=0)) v"
    proof (rule allI)
      fix v
      show "t v = (tl\<^sub>2(''0'' := 0, ''1'' := 0)) v"
        by (cases "v \<noteq> ''0'' \<and> v \<noteq> ''1''") (simp add: \<open>\<forall>v. v \<noteq> ''0'' \<and> v \<noteq> ''1'' \<longrightarrow> t v = tl\<^sub>2 v\<close> \<open>t ''0'' = 0\<close> \<open>t ''1'' = 0\<close>)+
    qed
    then show ?thesis by blast
  qed

  (* program is correct *)
  have "ccomp_if ?C i = ?I" by simp
  then have prog: "ccomp_if ?C i \<turnstile> (0,s,mem) \<rightarrow>* (size (ccomp_if ?C i),t,mem\<^sub>s\<^sub>3)"
    using exec \<open>t = ?T\<close> by simp

  (* mem preserved *)
  thm mem

  show ?case using prog mem by blast
qed auto

text \<open>The full correctness proof of ccomp\<close>
lemma ccomp_bigstep:
  assumes "(c,s) \<Rightarrow> t"
  assumes "outer_loop c"
  assumes "s ''0'' = 0" "s ''1'' = 0" "''0'' \<notin> set (vars c)" "''1'' \<notin> set (vars c)" (* registers excluded *)
  shows "\<exists>mem'. (ccomp c i \<turnstile> (0,s,mem) \<rightarrow>* (size(ccomp c i),t,mem'))
    \<and> (\<forall>j<i. mem j = mem' j)"
  using assms ccomp_if_bigstep[OF \<open>(c,s) \<Rightarrow> t\<close>]
proof (induction arbitrary: mem rule: big_step_induct)
  case (WhileFalse b s c)
  let ?B = "0"
  let ?NB = "1"
  let ?C = "IF b THEN c ELSE SKIP"
  let ?W = "WHILE b DO c"
  let ?F = "(\<lambda>x. if x = 0 then 1 else 0)"

  let ?I1 = "(bcomp b i)"
  let ?I2 = "ccomp_if ?C (i+1)"
  let ?I2_1 = "[MOVI ''0'' 0, MOVL ''0'' ''0'' i, MOVT ''0'' ?F ''0'']"
  let ?I3 = "[JMPZ ''0'' (-(size (?I1 @ ?I2 @ ?I2_1) + 1))]"
  let ?I3_1 = "[MOVI ''0'' 0]"

  have vars_c: "''0'' \<notin> set (vars ?C)" "''1'' \<notin> set (vars ?C)" using WhileFalse.prems(4,5) by simp+

  from \<open>outer_loop (WHILE b DO c)\<close> have "loop_free ?C" by blast
  then obtain t where "(?C,s) \<Rightarrow> t" using loop_free_terminates by blast

  (* b *)
  from bcomp_correct[of s b i] WhileFalse.prems(2,3) WhileFalse.hyps obtain mem\<^sub>b where
    exec_cb: "?I1 \<turnstile> (0,s,mem) \<rightarrow>* (size ?I1,s,mem\<^sub>b)" and
    b: "mem\<^sub>b i = ?B" and mem_cb: "\<forall>j<i. mem j = mem\<^sub>b j" by auto

  (* c *)
  from ccomp_if_bigstep[OF \<open>(?C,s) \<Rightarrow> t\<close> \<open>loop_free ?C\<close> WhileFalse.prems(2,3) vars_c] obtain mem' where
    exec_c: "?I2 \<turnstile> (0, s, mem\<^sub>b) \<rightarrow>* (size ?I2, t, mem')" and
    mem_c: "(\<forall>j<(i+1). mem\<^sub>b j = mem' j)" by blast
  let ?I = "?I1 @ ?I2"
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,t,mem')"
    by (rule exec_append_trans_1[OF exec_cb exec_c])
  have "mem' i = ?B" using mem_c b by simp
  have mem: "\<forall>j<i. mem j = mem' j" using mem_cb mem_c by fastforce

  (* load bval *)
  let ?T = "t(''0'':=?NB)"
  have exec_c_1: "?I2_1 \<turnstile> (0,t,mem') \<rightarrow>* (size ?I2_1,?T,mem')"
    using \<open>mem' i = ?B\<close> by (simp add: step_consume)
  let ?I = "?I @ ?I2_1"
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,?T,mem')"
    by (rule exec_append_trans_1[OF exec exec_c_1])

  (* jump *)
  have jump: "?I3 \<turnstile> (0,?T,mem') \<rightarrow> (1,?T,mem')"
    by (simp add: exec1_def)
  hence exec_j: "?I3 \<turnstile> (0,?T,mem') \<rightarrow>* (size ?I3,?T,mem')"
    by auto
  let ?I = "?I @ ?I3"
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,?T,mem')"
    by (rule exec_append_trans_1[OF exec exec_j])

  (* While logic *)
  from \<open>(?C,s) \<Rightarrow> t\<close> \<open>\<not>bval b s\<close> have "s = t" by blast
  hence "t(''0'':=0) = t" using \<open>s ''0'' = 0\<close> by fastforce

  (* cleanup *)
  have exec_c_1: "?I3_1 \<turnstile> (0,?T,mem') \<rightarrow>* (size ?I3_1,t,mem')"
    by (simp add: step_consume \<open>t(''0'':=0) = t\<close>)
  let ?I = "?I @ ?I3_1"
  have exec: "?I \<turnstile> (0,s,mem) \<rightarrow>* (size ?I,t,mem')"
    by (rule exec_append_trans_1[OF exec exec_c_1])

  (* program is correct *)
  have "ccomp ?W i = ?I"
    by (simp del: ccomp_if.simps)
  then have prog: "ccomp ?W i \<turnstile> (0,s,mem) \<rightarrow>* (size (ccomp ?W i),s,mem')"
    using exec \<open>s = t\<close> by (simp del: ccomp_if.simps)

  show ?case using prog mem by blast
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  let ?B = "1"
  let ?NB = "0"
  let ?C = "IF b THEN c ELSE SKIP"
  let ?W = "WHILE b DO c"
  let ?F = "(\<lambda>x. if x = 0 then 1 else 0)"

  let ?I1 = "(bcomp b i)"
  let ?I2 = "ccomp_if ?C (i+1)"
  let ?I2_1 = "[MOVI ''0'' 0, MOVL ''0'' ''0'' i, MOVT ''0'' ?F ''0'']"
  let ?I3 = "[JMPZ ''0'' (-(size (?I1 @ ?I2 @ ?I2_1) + 1))]"
  let ?I3_1 = "[MOVI ''0'' 0]"

  have vars_c: "''0'' \<notin> set (vars ?C)" "''1'' \<notin> set (vars ?C)" using WhileTrue.prems(4,5) by simp+

  from \<open>outer_loop (WHILE b DO c)\<close> have "loop_free ?C" by blast
  then obtain t where "(?C,s\<^sub>1) \<Rightarrow> t" using loop_free_terminates by blast

  (* b *)
  from bcomp_correct[of s\<^sub>1 b i] WhileTrue.prems(2,3) WhileTrue.hyps obtain mem\<^sub>b where
    exec_cb: "?I1 \<turnstile> (0,s\<^sub>1,mem) \<rightarrow>* (size ?I1,s\<^sub>1,mem\<^sub>b)" and
    b: "mem\<^sub>b i = ?B" and mem_cb: "\<forall>j<i. mem j = mem\<^sub>b j" by auto

  (* c *)
  from ccomp_if_bigstep[OF \<open>(?C,s\<^sub>1) \<Rightarrow> t\<close> \<open>loop_free ?C\<close> WhileTrue.prems(2,3) vars_c] obtain mem' where
    exec_c: "?I2 \<turnstile> (0,s\<^sub>1,mem\<^sub>b) \<rightarrow>* (size ?I2,t,mem')" and
    mem_c: "(\<forall>j<(i+1). mem\<^sub>b j = mem' j)" by blast
  let ?I = "?I1 @ ?I2"
  have exec: "?I \<turnstile> (0,s\<^sub>1,mem) \<rightarrow>* (size ?I,t,mem')"
    by (rule exec_append_trans_1[OF exec_cb exec_c])
  have "mem' i = ?B" using mem_c b by simp
  have mem: "\<forall>j<i. mem j = mem' j" using mem_cb mem_c by fastforce

  (* load bval *)
  let ?T = "t(''0'':=?NB)"
  have exec_c_1: "?I2_1 \<turnstile> (0,t,mem') \<rightarrow>* (size ?I2_1,?T,mem')"
    using \<open>mem' i = ?B\<close> by (simp add: step_consume)
  let ?I = "?I @ ?I2_1"
  have exec: "?I \<turnstile> (0,s\<^sub>1,mem) \<rightarrow>* (size ?I,?T,mem')"
    by (rule exec_append_trans_1[OF exec exec_c_1])

  (* jump *)
  have jump: "?I3 \<turnstile> (0,?T,mem') \<rightarrow> (-size (?I1 @ ?I2 @ ?I2_1),?T,mem')"
    by (simp add: exec1_def)
  hence jump: "?I3 \<turnstile> (0,?T,mem') \<rightarrow>* (-size (?I1 @ ?I2 @ ?I2_1),?T,mem')" by blast

  obtain I where "?I = I" by blast
  hence execI: "I \<turnstile> (0,s\<^sub>1,mem) \<rightarrow>* (size I,?T,mem')" using exec by blast

  have "size ?I - size (?I1 @ ?I2 @ ?I2_1) = 0" by simp
  hence "size I - size (?I1 @ ?I2 @ ?I2_1) = 0" using \<open>?I = I\<close> by simp 

  have exec_j: "I @ ?I3 \<turnstile> (0,s\<^sub>1,mem) \<rightarrow>* (size I + - size (?I1 @ ?I2 @ ?I2_1),?T,mem')"
    apply (rule exec_append_trans[OF execI])
      apply (auto simp: jump)
    apply fastforce
    done
  hence exec: "?I @ ?I3 \<turnstile> (0,s\<^sub>1,mem) \<rightarrow>* (0,?T,mem')"
    using \<open>size I - size (?I1 @ ?I2 @ ?I2_1) = 0\<close> \<open>?I = I\<close> by simp
  hence exec: "?I @ ?I3 @ ?I3_1 \<turnstile> (0,s\<^sub>1,mem) \<rightarrow>* (0,?T,mem')"
    using exec_appendR[OF exec] by simp
  let ?I = "?I @ ?I3 @ ?I3_1"

  (* While logic *)
  thm WhileTrue.hyps
  from \<open>(?C,s\<^sub>1) \<Rightarrow> t\<close> \<open>bval b s\<^sub>1\<close> have "(c,s\<^sub>1) \<Rightarrow> t" by blast
  hence "t = s\<^sub>2" using WhileTrue.hyps big_step_determ by simp
  hence "(?C,s\<^sub>1) \<Rightarrow> s\<^sub>2" using \<open>(?C,s\<^sub>1) \<Rightarrow> t\<close> by blast
  hence "s\<^sub>2 ''0'' = 0" "s\<^sub>2 ''1'' = 0"
    using WhileTrue.prems(2,3) vars_c not_in_vars_unchanged[OF \<open>(?C,s\<^sub>1) \<Rightarrow> s\<^sub>2\<close>]
    by simp+
  then have "?T = s\<^sub>2" using \<open>t = s\<^sub>2\<close> by auto

  (* IH *)
  from WhileTrue.IH(2)[OF WhileTrue.prems(1) \<open>s\<^sub>2 ''0'' = 0\<close> \<open>s\<^sub>2 ''1'' = 0\<close> WhileTrue.prems(4,5)]
  obtain mem'' where
    exec_IH: "ccomp ?W i \<turnstile> (0, s\<^sub>2, mem') \<rightarrow>* (size (ccomp (WHILE b DO c) i), s\<^sub>3, mem'')" and
    mem_IH: "(\<forall>j<i. mem' j = mem'' j)"
      by blast
  
  (* program is correct *)
  have "ccomp ?W i = ?I"
    by (simp del: ccomp_if.simps)
  (* simplify exec lemma *)
  then have exec: "ccomp ?W i \<turnstile> (0,s\<^sub>1,mem) \<rightarrow>* (0,s\<^sub>2,mem')"
    using exec \<open>?T = s\<^sub>2\<close> by argo
  have prog: "ccomp ?W i \<turnstile> (0,s\<^sub>1,mem) \<rightarrow>* (size (ccomp ?W i),s\<^sub>3,mem'')"
    by (rule star_trans[OF exec exec_IH])

  (* memory is preserved *)
  have mem: "\<forall>j<i. mem j = mem'' j" using mem mem_IH by fastforce

  show ?case using prog mem by blast
qed auto

section \<open>One Loop\<close>

text \<open>Ideally, we want to compile all programs, not just loop-free ones.
Since this would exceed the scope of this project, we just provide some intuition about how to
achieve this.\<close>

text \<open>To simplify things, we would want an equality bexp, but since we would not like to redefine
the entire com, we introduce it as a definition.

Ideally, we would implement equality using MOV-instructions (and not lookup tables). Calculating x = y
is possible by first moving 0 into the memory at x and then moving 1 into the memory at y. Iff x = y,
then the second move would have overwritten the value 0 at x, so moving from memory at x yields 1.\<close>
definition eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "eq a1 a2 = (And (Not (Less a1 a2)) (Not (Less a1 a2)))"

subsection \<open>Definitions\<close>


fun flatten :: "com \<Rightarrow> nat \<Rightarrow> (com \<times> nat)" where
"flatten SKIP i = (SKIP,i)" |
"flatten (x ::= a) i = (IF (eq (V ''l'') (N (int i))) THEN x ::= a ELSE SKIP, i)" |
"flatten (c1 ;; c2) i = (let (fc1,j) = flatten c1 i; (fc2,k) = flatten c2 j
  in (Seq fc1 fc2,k))" |
"flatten (IF b THEN c1 ELSE c2) i = (let (fc1,j) = flatten c1 i; (fc2,k) = flatten c2 j
  in (IF b THEN fc1 ELSE fc2,k))" |
"flatten (WHILE b DO c) i = (let (fc,j) = flatten c (i+1) in
  (IF (Not (And (Not (eq (V ''l'') (N (int i)))) (Not (eq (V ''l'') (N (int i+1))))))
    THEN (IF b THEN ''l'' ::= (N (int i+1)) ELSE ''l'' ::= (N (int i)))
    ELSE SKIP) ;;
  fc ,i)"

definition one_loop :: "com \<Rightarrow> com" where
  (* old variant with one repetition before WHILE *)
  (* "one_loop c = (let (fc,i) = flatten c 0 in fc ;; WHILE (Less (N 0) (V ''l'')) DO fc)" *)
  (* new variant with WHILE on the outer-most level *)
  "one_loop c = (let (fc,i) = flatten c 0 in
    WHILE (Not (And (Not (Less (V ''s'') (N 1))) (Not (Less (N 0) (V ''l''))))) DO (
      ''s'' ::= (N 1);;
      fc))"

(* Examples *)
values "{map t [''x''] |t. (WHILE Less (V ''x'') (N 10) DO ''x'' ::= (Plus (V ''x'') (N 1)), <>) \<Rightarrow> t}"
values "{map t [''x''] |t. (one_loop (WHILE Less (V ''x'') (N 10) DO ''x'' ::= (Plus (V ''x'') (N 1))), <>) \<Rightarrow> t}"

values "{map t [''x''] |t. (
  WHILE Less (V ''x'') (N 10) DO (
    ''y'' ::= N 0 ;;
    WHILE Less (V ''y'') (N 3) DO (
      ''y'' ::= (Plus (V ''y'') (N 1)) ;;
      ''x'' ::= (Plus (V ''x'') (N 1))
    )
  ), <>) \<Rightarrow> t}"
values "{map t [''x'', ''l''] |t. (one_loop (
  WHILE Less (V ''x'') (N 10) DO (
    ''y'' ::= N 0 ;;
    WHILE Less (V ''y'') (N 3) DO (
      ''y'' ::= (Plus (V ''y'') (N 1)) ;;
      ''x'' ::= (Plus (V ''x'') (N 1))
    )
  )), <>) \<Rightarrow> t}"

subsection "Correctness"

definition eq_l :: "(vname \<Rightarrow> int) \<Rightarrow> (vname \<Rightarrow> int) \<Rightarrow> bool"  ("_ =\<^sub>l _") where
  "eq_l s t = (\<forall>v. v \<noteq> ''l'' \<longrightarrow> s v = t v)"

text \<open>We skip these proves due to time constraints\<close>
lemma one_loop_small_step:
  assumes "(c,s) \<rightarrow>* (c',t)"
  assumes "s ''l'' = 0"
  shows "\<exists>c'' t''. (one_loop c,s) \<rightarrow>* (c'',t'') \<and> (t =\<^sub>l t'')"
  using assms
  sorry

theorem one_loop_eq:
  assumes "s ''l'' = 0"
  assumes "t =\<^sub>l t'"
  shows "(c,s) \<Rightarrow> t = (one_loop c,s) \<Rightarrow> t'"
proof
  assume "(c,s) \<Rightarrow> t"
  then have "(c,s) \<rightarrow>* (SKIP, t)" using big_to_small by simp
  then have "(one_loop c,s) \<rightarrow>* (SKIP,t')" sorry
  then show "(one_loop c,s) \<Rightarrow> t'" using small_to_big by simp
next
  assume "(one_loop c,s) \<Rightarrow> t'"
  then have "(one_loop c,s) \<rightarrow>* (SKIP, t')" using big_to_small by simp
  then have "(c,s) \<rightarrow>* (SKIP,t)" sorry
  then show "(c,s) \<Rightarrow> t" using small_to_big by simp
qed

subsection \<open>Derived Properties\<close>

thm flatten.induct

text \<open>The fact, that programs obtained through the functions above are free of inner loops is easy
to see, but not trivial to prove. Due to time constraints, we simply lay out the properties here:\<close>

text \<open>This guarantees a flattened program is loop_free\<close>
lemma flatten_loop_free_exists:
  shows"\<exists>fc j. flatten c i = (fc,j) \<longrightarrow> loop_free fc"
proof (induction c arbitrary: i)
  case (Seq c1 c2)
  then obtain fc1 j where "flatten c1 i = (fc1, j) \<longrightarrow> loop_free fc1" by fastforce
  then obtain fc2 k where "flatten c2 j = (fc1, k) \<longrightarrow> loop_free fc2" by fastforce
  then show ?case by auto
qed auto


text \<open>Ideally, we would want the stronger lemma\<close>
lemma flatten_loop_free: "flatten c i = (fc,j) \<Longrightarrow> loop_free fc"
  sorry

text \<open>What remains to be shown, is, that a program obtained through one_loop can be compiled into
MOV instructions\<close>
theorem one_loop_outer_loop: "outer_loop (one_loop c)"
  sorry

end