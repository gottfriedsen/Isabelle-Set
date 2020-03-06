chapter \<open>Natural numbers\<close>

theory Nat
imports Ordinal Function Monoid

begin

text \<open>The basic results have already been shown for \<nat> = \<omega>.\<close>

definition nat ("\<nat>") where "\<nat> = \<omega>"

definition "nat_zero \<equiv> {}"
definition "nat_one \<equiv> succ nat_zero"

bundle notation_nat_zero begin notation nat_zero ("0") end
bundle no_notation_nat_zero begin no_notation nat_zero ("0") end

bundle notation_nat_one begin notation nat_one ("1") end
bundle no_notation_nat_one begin no_notation nat_one ("1") end

unbundle
  no_notation_zero_implicit
  no_notation_one_implicit

  notation_nat_zero
  notation_nat_one

lemmas
  nat_unfold = omega_unfold[folded nat_def nat_zero_def] and
  zero_nat [simp] = empty_in_omega[folded nat_def nat_zero_def] and
  succ_nat [simp] = succ_omega[folded nat_def] and
  nat_cases = omega_cases[folded nat_def nat_zero_def] and
  nat_induct [case_names 0 induct, induct set: nat] =
    omega_induct[folded nat_def nat_zero_def] and
  nat_elems = omega_elems[folded nat_def nat_zero_def] and
  succ_not_empty [simp] = Ordinal.succ_not_empty[folded nat_zero_def] and
  empty_not_succ [simp] = Ordinal.empty_not_succ[folded nat_zero_def]

section \<open>\<nat> as a type\<close>

abbreviation "Nat \<equiv> element \<nat>"

lemmas Nat_induct = nat_induct
  [ simplified element_type_iff,
    case_names base induct,
    induct pred: Nat ]

lemmas Nat_cases = nat_cases[simplified element_type_iff]

lemma Nat_Ord [derive]: "x : Nat \<Longrightarrow> x : Ord"
  by (induct x rule: Nat_induct) (auto intro: succ_Ord simp: nat_zero_def)

lemma
  zero_type [type]: "0 : Nat" and
  succ_type [type]: "succ : Nat \<Rightarrow> Nat"
  by unfold_types auto

lemma one_type [type]: "1 : Nat"
  unfolding nat_one_def by auto

section \<open>Truncated predecessor function\<close>

definition "pred n = (if n = 0 then 0 else (THE m \<in> \<nat>. n = succ m))"

lemma pred_type [type]: "pred : Nat \<Rightarrow> Nat"
  unfolding pred_def by unfold_types (auto intro: btheI1 nat_elems)

lemma pred_nonzero: "\<lbrakk>n : Nat; n \<noteq> 0\<rbrakk> \<Longrightarrow> pred n = (THE m \<in> \<nat>. n = succ m)"
  unfolding pred_def by auto

lemma pred_zero [simp]: "pred 0 = 0"
  unfolding pred_def by auto

lemma pred_succ [simp]: "n : Nat \<Longrightarrow> pred (succ n) = n"
  unfolding pred_def by auto

\<comment> \<open>Note Kevin: TODO: change to typed version\<close>
lemma succ_pred: "\<lbrakk>n \<in> \<nat>; n \<noteq> 0\<rbrakk> \<Longrightarrow> succ (pred n) = n"
  unfolding pred_def by (simp, rule sym, rule btheI2) (fact nat_elems)

section \<open>The \<open><\<close> and \<open>\<le>\<close> orders on Nat\<close>

definition lt (infix "<" 60) where "m < n = (m \<in> n)"

lemmas
  lt_succ [simp] = succ_mem[folded lt_def] and
  lt_succ_cases = succ_cases[folded lt_def]

lemma succ_lt_monotone [intro]:
  "n : Nat \<Longrightarrow> m < n \<Longrightarrow> succ m < succ n"
  unfolding lt_def nat_def by auto

lemma nat_lt_of_succ_lt: "n : Nat \<Longrightarrow> succ m < succ n \<Longrightarrow> m < n"
  unfolding lt_def nat_def by (auto intro: omega_succ_mem_monotoneE)

lemma nat_lt_succ: "n : Nat \<Longrightarrow> m < n \<Longrightarrow> m < succ n"
  unfolding lt_def by simp

lemma succ_lt_monotoneE:
  "\<lbrakk>n: Nat; succ m < succ n\<rbrakk> \<Longrightarrow> m < n"
  unfolding lt_def
  by unfold_types (auto intro: omega_succ_mem_monotoneE simp: nat_def)

lemma lt_trichotomy:
  "\<lbrakk>m: Nat; n: Nat\<rbrakk> \<Longrightarrow> m < n \<or> m = n \<or> n < m"
  unfolding lt_def using Ord_trichotomy by auto
  \<comment>\<open>Good *EXAMPLE* of type derivation helpfulness!\<close>

lemma lt_trichotomyE:
  assumes major: "m: Nat" "n: Nat"
      and case1: "m < n \<Longrightarrow> P"
      and case2: "m = n \<Longrightarrow> P"
      and case3: "n < m \<Longrightarrow> P"
  shows P
  using assms lt_trichotomy unfolding lt_def by auto

definition le (infix "\<le>" 60) where "m \<le> n = (m < n \<or> m = n)"

lemma le_self [simp]: "n \<le> n"
  unfolding le_def by simp

lemma le_of_lt: "m < n \<Longrightarrow> m \<le> n"
  unfolding le_def ..

lemma le_succ [simp]: "n \<le> succ n"
  unfolding le_def by auto

lemma succ_le_monotone:
  "\<lbrakk>n: Nat; m \<le> n\<rbrakk> \<Longrightarrow> succ m \<le> succ n"
  unfolding le_def using succ_lt_monotone by auto

lemma succ_le_monotoneE:
  "\<lbrakk>n: Nat; succ m \<le> succ n\<rbrakk> \<Longrightarrow> m \<le> n"
  unfolding le_def using succ_lt_monotoneE by auto

lemma succ_lt_le_monotone:
  "\<lbrakk>n: Nat; m < n\<rbrakk> \<Longrightarrow> succ m \<le> succ n"
  unfolding le_def using succ_lt_monotone by auto

lemma lt_0 [simp]: "n : Nat \<Longrightarrow> 0 < succ n"
  unfolding lt_def nat_def nat_zero_def
  by unfold_types (fact omega_empty_in_succ)

lemma zero_ltE [elim]: "n < 0 \<Longrightarrow> P"
  unfolding lt_def nat_zero_def by auto

corollary [simp]: "\<not> n < 0" by auto

lemma ne_zero_of_gt_zero: "0 < n \<Longrightarrow> n \<noteq> 0"
  by auto

lemma gt_zero_of_ne_zero: assumes "n : Nat" and "n \<noteq> 0" shows "0 < n"
  by (rule lt_trichotomyE[of 0 n]) (auto simp: assms)

lemma
  not_succ_lt [simp]: "\<not> succ n < n" and
  not_lt_self [simp]: "\<not> n < n"
  unfolding lt_def by auto

lemma nat_zero_lt_of_ne_zero:
  "n: Nat \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> 0 < n"
  using nat_elems by unfold_types force

lemma le_0 [simp]: "n \<le> 0 \<Longrightarrow> n = 0"
  unfolding le_def by auto

lemma Nat_of_lt [elim]: "n: Nat \<Longrightarrow> m < n \<Longrightarrow> m: Nat"
  unfolding nat_def lt_def by unfold_types (fact omega_mem_transitive)

(*Case splits*)
lemma le_cases: assumes "n: Nat" and "m \<le> n"
  obtains (eq) "m = n" | (lt) "m < n"
  using assms unfolding le_def by auto

lemma lt_asym: "\<lbrakk>m < n; n < m\<rbrakk> \<Longrightarrow> P"
  unfolding lt_def using mem_asym by blast

lemma lt_transitive:
  "n : Nat \<Longrightarrow> k < m \<Longrightarrow> m < n \<Longrightarrow> k < n"
  unfolding lt_def nat_def
  by unfold_types (auto intro: omega_elem_mem_transitive')

lemma
  le_trans: "n: Nat \<Longrightarrow> k \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> k \<le> n" and
  le_lt_lt: "n: Nat \<Longrightarrow> k \<le> m \<Longrightarrow> m < n \<Longrightarrow> k < n" and
  lt_le_lt: "n: Nat \<Longrightarrow> k < m \<Longrightarrow> m \<le> n \<Longrightarrow> k < n" and
  lt_le_le: "n: Nat \<Longrightarrow> k < m \<Longrightarrow> m \<le> n \<Longrightarrow> k \<le> n" and
  le_lt_le: "n: Nat \<Longrightarrow> k \<le> m \<Longrightarrow> m < n \<Longrightarrow> k \<le> n" and
  lt_lt_le: "n: Nat \<Longrightarrow> k < m \<Longrightarrow> m < n \<Longrightarrow> k \<le> n" and
  lt_trans: "n: Nat \<Longrightarrow> k < m \<Longrightarrow> m < n \<Longrightarrow> k < n"
  unfolding le_def by (auto intro: lt_transitive)

lemma succ_lt: "\<lbrakk>m: Nat; n: Nat; succ m < n\<rbrakk> \<Longrightarrow> m < n"
  unfolding succ_def lt_def nat_def
  by unfold_types (auto dest: omega_elem_Ord Ord_mem_transitive')

lemma succ_zero_lt:
  "\<lbrakk>m: Nat; n: Nat\<rbrakk> \<Longrightarrow> succ m < n \<Longrightarrow> 0 < n"
  by (rule lt_transitive) auto

lemma pred_lt_monotone [intro]:
  assumes "m: Nat" "n: Nat"
      and "0 < m" "m < n"
  shows "pred m < pred n"
proof -
  have "m \<in> \<nat>" "n \<in> \<nat>" "m \<noteq> 0" "n \<noteq> 0"
    using assms by auto
  then obtain k k' where "k \<in> \<nat>" "k'\<in> \<nat>" and
    *: "m = succ k" "n = succ k'"
    using nat_elems by blast
  then have "succ k < succ k'"
    using assms by simp
  thus ?thesis
    using succ_lt_monotoneE by (auto simp only: * pred_succ)
qed

lemma lt_pred_of_succ_lt:
  assumes "m: Nat" "n: Nat" "succ n < m"
  shows "n < pred m"
proof (rule succ_lt_monotoneE)
  have "m \<noteq> 0" using assms by auto
  with succ_pred show "succ n < succ (pred m)" by auto
qed discharge_types


section \<open>Ranges\<close>

definition upto ("{0, ..., _}") where "{0, ..., n} = {i \<in> \<nat> | i \<le> n}"

lemma succ_eq_upto: "n: Nat \<Longrightarrow> succ n = {0, ..., n}"
  unfolding succ_def upto_def le_def lt_def
  by unfold_types (auto intro: equalityI omega_mem_transitive simp: nat_def)

lemmas upto_eq_succ = succ_eq_upto[symmetric]

lemma uptoI: "n: Nat \<Longrightarrow> m \<le> n \<Longrightarrow> m \<in> {0, ..., n}"
  by unfold_types (auto simp: upto_eq_succ le_def lt_def)

lemma uptoE1: "m \<in> {0, ..., n} \<Longrightarrow> m: Nat"
  unfolding upto_def by auto

lemmas [derive] = uptoE1[simplified element_type_iff]

lemma uptoE2: "m \<in> {0, ..., n} \<Longrightarrow> m \<le> n"
  unfolding upto_def by auto

lemma le_iff_upto: "n: Nat \<Longrightarrow> m \<le> n = (m \<in> {0, ..., n})"
  by (auto intro: uptoI elim: uptoE2)

lemmas upto_iff_le = le_iff_upto[symmetric]

lemma [derive]: "n: Nat \<Longrightarrow> 0: element {0, ..., n}"
  by
    (simp add: upto_eq_succ nat_def nat_zero_def, unfold_types)
    (auto intro: omega_empty_in_succ)

lemma
  [derive]: "n: Nat \<Longrightarrow> n: element {0, ..., n}" and
  [derive]: "n: Nat \<Longrightarrow> m: element n \<Longrightarrow> m: element {0, ..., n}"
  by unfold_types (auto simp: upto_eq_succ)

lemma upto_subset_upto [intro!]: "n: Nat \<Longrightarrow> m < n \<Longrightarrow> {0, ..., m} \<subseteq> {0, ..., n}"
  unfolding upto_def le_def by (auto intro: lt_transitive)

lemma le_induct:
  assumes "m: Nat"
      and "n: Nat"
      and "m \<le> n"
      and "P 0"
      and "\<And>m. m < n \<Longrightarrow> P m \<Longrightarrow> P (succ m)"
  shows "P m"
proof (cases n rule: Nat_cases, fact)
  assume "n = 0"
  hence "m = 0" using \<open>m \<le> n\<close> by auto
  thus "P m" using assms by simp

  next {
  fix m
  have "m: Nat \<Longrightarrow> (\<And>k. \<lbrakk>k: Nat; n = succ k; m \<le> n\<rbrakk> \<Longrightarrow> P m)"
  proof (induction m rule: Nat_induct)
    show "P 0" by fact
    next
    fix k l assume
      "succ l \<le> n" and
      hyp: "\<And>k. k : Nat \<Longrightarrow> n = succ k \<Longrightarrow> l \<le> n \<Longrightarrow> P l" and
      conds: "k: Nat" "n = succ k"
    then have "l < n" by (auto intro: lt_succ lt_le_lt)
    then moreover have "l \<le> n" by (rule le_of_lt)
    ultimately show "P (succ l)" using conds hyp assms(5) by auto
  qed
  }
  thus "\<And>k. k : Nat \<Longrightarrow> n = succ k \<Longrightarrow> P m" using assms by blast
qed

lemma cons_upto_FunctionI [intro]:
  assumes "n: Nat"
      and "f \<in> {0, ..., n} \<rightarrow> X"
      and "x \<in> X"
  shows "cons \<langle>succ n, x\<rangle> f \<in> {0, ..., succ n} \<rightarrow> X"
  by
    (simp only: upto_eq_succ, subst (2) succ_def)
    (auto intro: assms cons_FunctionI' simp: succ_eq_upto)


section \<open>Recursion\<close>

text \<open>Recursion on Nat. Axiomatized, for now.\<close>

axiomatization natrec :: \<open>set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set\<close> where
  natrec_0 [simp]: "natrec x\<^sub>0 f 0 = x\<^sub>0" and
  natrec_succ [simp]: "natrec x\<^sub>0 f (succ n) = f (natrec x\<^sub>0 f n)"

lemma natrec_type [type]:
  "natrec : X \<Rightarrow> (X \<Rightarrow> X) \<Rightarrow> Nat \<Rightarrow> X"
proof (intro typeI)
  fix x f n
  show "n: Nat \<Longrightarrow> x: X \<Longrightarrow> f: X \<Rightarrow> X \<Longrightarrow> natrec x f n: X"
  by (induct n rule: Nat_induct) auto
qed


section \<open>Arithmetic\<close>

named_theorems arith

subsection \<open>Addition\<close>

\<comment> \<open>Note Kevin: TODO: recursion should be on the first parameter, not the second\<close>
definition [arith]: "nat_add m n = natrec m succ n"

lemma nat_add_type [type]: "nat_add : Nat \<Rightarrow> Nat \<Rightarrow> Nat"
  unfolding nat_add_def by auto

bundle notation_nat_add begin notation nat_add (infixl "+" 65) end
bundle no_notation_nat_add begin no_notation nat_add (infixl "+" 65) end

unbundle
  no_notation_add_implicit
  notation_nat_add

lemma nat_zero_add [simp]: "m: Nat \<Longrightarrow> 0 + m = m"
  unfolding nat_add_def by (induction m rule: Nat_induct) auto

lemma nat_add_zero [simp]: "m: Nat \<Longrightarrow> m + 0 = m"
  unfolding nat_add_def by simp

lemma nat_add_assoc: "k: Nat \<Longrightarrow> n: Nat \<Longrightarrow> m: Nat \<Longrightarrow> m + n + k = m + (n + k)"
  unfolding nat_add_def by (induction k rule: Nat_induct) auto

lemma nat_add_succ_eq_succ_add [simp]: "m + succ n = succ (m + n)"
  unfolding nat_add_def by simp

lemma nat_succ_add: assumes "m : Nat" "n : Nat"
  shows "succ n + m = succ (n + m)"
  using assms by (induction m rule: Nat_induct) auto

lemma nat_add_comm: "n: Nat \<Longrightarrow> m: Nat \<Longrightarrow> m + n = n + m"
  by (induction n arbitrary: m rule: Nat_induct) (auto simp: nat_succ_add)

lemma nat_add_nonzero_left:
  assumes
    "m: Nat" "n: Nat" "m \<noteq> 0"
  shows "m + n \<noteq> 0"
  unfolding nat_add_def
  by (insert assms(2), induction n rule: Nat_induct) auto

lemma nat_add_nonzero_right:
  assumes
    "m: Nat" "n: Nat" "n \<noteq> 0"
  shows "m + n \<noteq> 0"
  using nat_add_nonzero_left assms by (subst nat_add_comm)

lemma nat_lt_add: assumes "l : Nat" "m : Nat" "n : Nat" and "n < m"
  shows "n < m + l"
using assms
proof (induction l rule: Nat_induct)
  case (induct l)
  then have "n < m + l" by simp
  then have "n < succ (m + l)" using lt_trans by simp
  then show "n < m + succ l" using nat_add_succ_eq_succ_add by simp
\<comment> \<open>  TODO: Transitivity rules have typing assumptions. Proof should more
  look like this:
  then have "n < m + l" by simp
  also have "... < succ (m + l)" by simp
  also have "... = m + succ l" using nat_add_succ_eq_succ_add by auto
  finally show ?case by auto\<close>
qed simp

lemma nat_add_nonzero: assumes "m: Nat" "n: Nat" and "m \<noteq> 0" "n \<noteq> 0"
  shows "m + n \<noteq> 0"
proof -
  \<comment> \<open>Note Kevin: why are these steps working without passing "assms"?
Implicitly taking assumptions from the context is bad practice.\<close>
  from gt_zero_of_ne_zero have "0 < m" and "0 < n" by auto
  then have "0 < m + n" using nat_lt_add by simp
  then show ?thesis by auto
qed
  
subsection \<open>Subtraction (truncated)\<close>

definition [arith]: "nat_sub m n = natrec m pred n"

lemma nat_sub_type [type]: "nat_sub : Nat \<Rightarrow> Nat \<Rightarrow> Nat"
  unfolding nat_sub_def by auto

bundle notation_nat_sub begin notation nat_sub (infixl "-" 65) end
bundle no_notation_nat_sub begin no_notation nat_sub (infixl "-" 65) end

unbundle notation_nat_sub

lemma nat_sub_zero [simp]: "m - 0 = m"
  unfolding nat_sub_def by auto

lemma nat_sub_succ_eq_pred_sub: "m - succ n = pred (m - n)"
  unfolding nat_sub_def by simp

lemma nat_pred_sub: assumes "m : Nat" "n : Nat"
  shows "pred n - m = pred (n - m)"
  using assms
  by (induction m rule: Nat_induct) (auto simp: nat_sub_succ_eq_pred_sub)

lemma nat_succ_sub [simp]:
  "n: Nat \<Longrightarrow> m: Nat \<Longrightarrow> succ m - succ n = m - n"
  by (induction n rule: Nat_induct) (simp_all add: arith)

lemma nat_zero_lt_sub: assumes "m : Nat" "n : Nat" and "m < n" shows "0 < n - m"
using assms
proof (induction m arbitrary: n rule: Nat_induct)
  case (induct m)
  with lt_pred_of_succ_lt have "m < pred n" by simp
  then have "0 < pred n - m" using induct.IH by simp
  then show ?case using nat_pred_sub nat_sub_succ_eq_pred_sub by simp
qed simp

subsection \<open>Multiplication\<close>

definition [arith]: "nat_mul m n = natrec 0 (nat_add n) m"

lemma nat_mul_type [type]: "nat_mul : Nat \<Rightarrow> Nat \<Rightarrow> Nat"
  unfolding nat_mul_def by auto

bundle notation_nat_mul begin notation nat_mul (infixl "\<cdot>" 65) end
bundle no_notation_nat_mul begin no_notation nat_mul (infixl "\<cdot>" 65) end

unbundle no_notation_mul_implicit
unbundle notation_nat_mul

lemma nat_succ_mul: "succ m \<cdot> n = n + (m \<cdot> n)"
  unfolding nat_mul_def by simp

lemma nat_zero_mul [simp]: "0 \<cdot> n = 0"
  unfolding nat_mul_def by simp

lemma nat_mul_zero [simp]: assumes "n : Nat" shows "n \<cdot> 0 = 0"
  using assms unfolding nat_mul_def by (induction n rule: Nat_induct) auto

lemma nat_zero_lt_mul [intro]: assumes "m : Nat" "n : Nat" and "0 < m" "0 < n"
  shows "0 < m \<cdot> n"
using assms
proof (induction m rule: Nat_induct)
  case (induct m)
  with nat_lt_add have "0 < n + (m \<cdot> n)" by simp
  with nat_succ_mul show ?case by simp
qed simp

lemma "nat_mul_eq_zero": assumes "m : Nat" "n : Nat" and "m \<cdot> n = 0"
  shows "m = 0 \<or> n = 0"
proof (rule ccontr)
  presume "m \<noteq> 0" and "n \<noteq> 0"
  with gt_zero_of_ne_zero have "0 < m" and "0 < n" using assms by simp_all
  with nat_zero_lt_mul have "0 < m \<cdot> n" using assms by blast
  with \<open>m \<cdot> n = 0\<close> have "0 < 0" by simp
  then show "False" by simp
qed auto

lemma nat_mul_eq_zeroE: assumes "m : Nat" "n : Nat" "m \<cdot> n = 0"
  obtains (left_zero) "m = 0" | (right_zero) "n = 0"
  using assms nat_mul_eq_zero by blast

lemma nat_mul_ne_zero: assumes "m: Nat" "n: Nat" and "m \<noteq> 0" "n \<noteq> 0"
  shows "m \<cdot> n \<noteq> 0"
  using gt_zero_of_ne_zero nat_mul_eq_zeroE[of m n] assms by simp


section \<open>Monoid structure of (\<nat>, +)\<close>

definition Nat_monoid ("'(\<nat>, +')")
  where "(\<nat>, +) \<equiv> object {\<langle>@zero, 0\<rangle>, \<langle>@add, \<lambda>m n\<in> \<nat>. nat_add m n\<rangle>}"

lemma "(\<nat>, +): Monoid \<nat>"
proof unfold_types
  show "(\<nat>, +) @@ zero \<in> \<nat>"
   and "(\<nat>, +) @@ add \<in> \<nat> \<rightarrow> \<nat> \<rightarrow> \<nat>"
  unfolding Nat_monoid_def by auto

  fix x assume "x \<in> \<nat>"
  show "add (\<nat>, +) (zero (\<nat>, +)) x = x"
   and "add (\<nat>, +) x (zero (\<nat>, +)) = x"
  \<comment> \<open>Very low-level; lots of unfolding.\<close>
  unfolding Nat_monoid_def add_def zero_def by auto

  fix y z assume "y \<in> \<nat>" "z \<in> \<nat>"
  show
    "add (\<nat>, +) (add (\<nat>, +) x y) z =
      add (\<nat>, +) x (add (\<nat>, +) y z)"
  unfolding Nat_monoid_def add_def zero_def
  using nat_add_assoc by auto
qed


end
