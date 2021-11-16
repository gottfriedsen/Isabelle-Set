chapter \<open>Integers\<close>

theory Integer
  imports Nat_Set HOTG.Sum Set_Extension
begin

section \<open>Carrier of \<int>\<close>

text \<open>
  We construct the integers as a pair of a non-negative and a negative part.
  By using the set extension principle, we ensure that \<open>\<nat> \<subseteq> \<int>\<close>.
\<close>

definition "int_rep = sum nat (nat \<setminus> {0})"

\<comment> \<open>Some type derivation rule setup\<close>
lemma
  [type]: "succ: Element nat \<Rightarrow> Element (nat \<setminus> {0})" and
  [type]: "inl : Element nat \<Rightarrow> Element int_rep" and
  [type]: "inr : Element (nat \<setminus> {0}) \<Rightarrow> Element int_rep"
  unfolding int_rep_def by unfold_types auto

interpretation Int: set_extension nat int_rep inl
  proof (* FIX: What is the method called by `proof` here? *) qed auto

abbreviation int ("\<int>") where "\<int> \<equiv> Int.def"
abbreviation "pos n \<equiv> Int.Abs (inl n)"
abbreviation "neg n \<equiv> Int.Abs (inr n)"

lemmas nat_subset_int [simp] = Int.extension_subset

abbreviation "Int' \<equiv> Element \<int>"

corollary [derive]: "n : Nat \<Longrightarrow> n : Int'"
  by (unfold_types, rule subsetE) auto


section \<open>Basic arithmetic\<close>

subsection \<open>Raw definitions on the underlying representation\<close>

definition "int_rep_add x y \<equiv> sum_case
  (\<lambda>m. sum_case
    (\<lambda>n. inl (m + n))
    (\<lambda>n. if m < n then inr (n - m) else inl (m - n))
    y)
  (\<lambda>m. sum_case
    (\<lambda>n. if n < m then inr (m - n) else inl (n - m))
    (\<lambda>n. inr (m + n))
    y)
  x"

definition "int_rep_neg =
  sum_case (\<lambda>n. if n = 0 then inl n else inr n) (\<lambda>n. inl n)"

definition "int_rep_sub x y = int_rep_add x (int_rep_neg y)"

definition "int_rep_mul x y \<equiv> sum_case
  (\<lambda>m. sum_case
    (\<lambda>n. inl (m \<cdot> n))
    (\<lambda>n. if m = 0 then inl 0 else inr (m \<cdot> n))
    y)
  (\<lambda>m. sum_case
    (\<lambda>n. if n = 0 then inl 0 else inr (m \<cdot> n))
    (\<lambda>n. inl (m \<cdot> n))
    y)
  x"

lemma int_rep_zero_add:
  "n \<in> int_rep \<Longrightarrow> int_rep_add (inl 0) n = n"
  unfolding int_rep_def int_rep_add_def
  by (elim sumE) (auto intro: zero_lt_if_ne_zero)

lemma int_rep_add_zero:
  "n \<in> int_rep \<Longrightarrow> int_rep_add n (inl 0) = n"
  unfolding int_rep_def int_rep_add_def
  by (elim sumE) (auto intro: zero_lt_if_ne_zero)

lemma int_rep_add_assoc:
  assumes "x \<in> int_rep" "y \<in> int_rep" "z \<in> int_rep"
  shows "int_rep_add (int_rep_add x y) z = int_rep_add x (int_rep_add y z)"
  apply (
    rule sumE[OF assms(1)[unfolded int_rep_def]];
    rule sumE[OF assms(2)[unfolded int_rep_def]];
    rule sumE[OF assms(3)[unfolded int_rep_def]])
  unfolding int_rep_add_def
  apply (auto simp:
    nat_sub_dist_add nat_sub_twice_comm)
oops

lemma int_rep_one_mul:
  "x \<in> int_rep \<Longrightarrow> int_rep_mul (inl 1) x = x"
  unfolding int_rep_def int_rep_mul_def by (elim sumE) auto

lemma int_rep_mul_one:
  "x \<in> int_rep \<Longrightarrow> int_rep_mul x (inl 1) = x"
  unfolding int_rep_def int_rep_mul_def
  by (rule sumE) auto

lemma int_rep_mul_assoc:
  assumes "x \<in> int_rep" "y \<in> int_rep" "z \<in> int_rep"
  shows "int_rep_mul (int_rep_mul x y) z = int_rep_mul x (int_rep_mul y z)"
  unfolding int_rep_def int_rep_mul_def by (
    rule sumE[OF assms(1)[unfolded int_rep_def]];
    rule sumE[OF assms(2)[unfolded int_rep_def]];
    rule sumE[OF assms(3)[unfolded int_rep_def]])
    (auto simp: nat_mul_assoc nat_mul_ne_zero)

lemma int_rep_add_type [type]:
  "int_rep_add: Element int_rep \<Rightarrow> Element int_rep \<Rightarrow> Element int_rep"
  unfolding int_rep_def int_rep_add_def
  by (unfold_types, erule sumE; erule sumE) auto
  \<comment> \<open>
  Note Kevin: I do not think unfolding everything for the above functions is a
  good idea. I think we want to get the type system up to a point where this is
  handled by said system.
  
  Reply Josh: Is this not what we'd want to do here? Conceptually int_rep *is*
  the low-level representation, so it seems alright to me that we unfold...
  \<close>

lemma [type]:
  "int_rep_neg: Element int_rep \<Rightarrow> Element int_rep"
  unfolding int_rep_def int_rep_neg_def
  by unfold_types auto

lemma int_rep_sub_type [type]:
  "int_rep_sub: Element int_rep \<Rightarrow> Element int_rep \<Rightarrow> Element int_rep"
  unfolding int_rep_sub_def by auto

lemma int_rep_mul_type [type]:
  "int_rep_mul: Element int_rep \<Rightarrow> Element int_rep \<Rightarrow> Element int_rep"
  unfolding int_rep_def int_rep_mul_def
  by (unfold_types, erule sumE; erule sumE) (auto simp: nat_mul_ne_zero)

subsection \<open>Arithmetic operations lifted to Int\<close>

text \<open>
  We lift constants/functions from \<open>int_rep\<close> to \<open>\<int>\<close> manually.
  This should be automated in the future using some technique similar to
  transfer in Isabelle/HOL.
\<close>

definition "int_add x y = Int.Abs (int_rep_add (Int.Rep x) (Int.Rep y))"
definition "int_neg x = Int.Abs (int_rep_neg (Int.Rep x))"
definition "int_sub x y = Int.Abs (int_rep_sub (Int.Rep x) (Int.Rep y))"
definition "int_mul x y \<equiv> Int.Abs (int_rep_mul (Int.Rep x) (Int.Rep y))"

lemma
  int_add_type [type]: "int_add: Int' \<Rightarrow> Int' \<Rightarrow> Int'" and
  int_neg_type [type]: "int_neg: Int' \<Rightarrow> Int'" and
  int_sub_type [type]: "int_sub: Int' \<Rightarrow> Int' \<Rightarrow> Int'" and
  int_mul_type [type]: "int_mul: Int' \<Rightarrow> Int' \<Rightarrow> Int'"
  unfolding int_add_def int_neg_def int_sub_def int_mul_def
  using  [[type_derivation_depth=3]] \<comment> \<open>Need increased depth *EXAMPLE*\<close>
  by auto


text \<open>
  Need a notation package that also does inference to determine if a number is a
  Nat, Int, etc. Typeclass integration here already?...
\<close>

bundle notation_int_add begin notation int_add (infixl "+" 65) end
bundle no_notation_int_add begin no_notation int_add (infixl "+" 65) end

bundle notation_int_sub begin notation int_sub (infixl "-" 65) end
bundle no_notation_int_sub begin no_notation int_sub (infixl "-" 65) end

bundle notation_int_mul begin notation int_mul (infixl "\<cdot>" 65) end
bundle no_notation_int_mul begin no_notation int_mul (infixl "\<cdot>" 65) end

unbundle
  no_notation_nat_add
  no_notation_nat_sub
  no_notation_nat_mul

  notation_int_add
  notation_int_sub
  notation_int_mul

lemma int_one_mul [simp]:
  assumes "x: Int'" shows "1 \<cdot> x = x"
proof -
  have "Int.Rep 1 = inl 1" unfolding Int.Rep_def by simp
  with int_rep_one_mul show ?thesis unfolding int_mul_def by simp
qed

lemma int_mul_one [simp]:
  assumes "x: Int'" shows "x \<cdot> 1 = x"
proof -
  have "Int.Rep 1 = inl 1" unfolding Int.Rep_def by simp
  with int_rep_mul_one show ?thesis unfolding int_mul_def by simp
qed

lemma int_mul_assoc:
  assumes "x: Int'" "y: Int'" "z: Int'"
  shows "x \<cdot> y \<cdot> z = x \<cdot> (y \<cdot> z)"
  using assms int_rep_mul_assoc unfolding int_mul_def by simp

subsection \<open>Examples\<close>

experiment begin

named_theorems arith
lemmas [arith] =
  int_rep_add_def int_rep_neg_def int_rep_sub_def int_rep_mul_def
  int_add_def int_sub_def int_mul_def

text \<open>
  At some point we want to just be able to write \<open>succ n\<close> below, and
  automatically infer that it has to have soft type \<open>Int\<close>.
\<close>

schematic_goal
  "pos (succ 0) + pos (succ 0) + neg (succ 0) = ?a"
  by (simp add: arith)

schematic_goal
  "pos 0 - neg (succ 0) + pos (succ 0) - neg (succ 0) = ?a"
  by (simp add: arith)

end

end
