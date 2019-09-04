section \<open>Monoids\<close>

text \<open>
  We define monoids as a soft type class (though without tool support) and experiment with
  how it can interact with implicit arguments and type inference.
  
  Structures are modeled as sets that contain the operations, but are parametrized over
  the carrier sets.
\<close>

theory Monoid
imports Structures

begin

setup \<open>soft_type_simp_solver\<close>

definition Monoid :: "set \<Rightarrow> set type"
  where Monoid_typedef:
  "Monoid A =
    Zero A
  \<bar> Plus A
  \<bar> \<lparr> (@plus plus) (@zero zero).
    (\<forall>x: element A. plus `zero `x = x) \<and>
    (\<forall>x: element A. plus `x `zero = x) \<and>
    (\<forall>x: element A. \<forall>y: element A. \<forall>z: element A.
      plus `(plus `x `y) `z = plus `x `(plus `y `z)) \<rparr>"

lemma Monoid_is_Zero [derive]: "Monoid A \<prec> Zero A"
  unfolding Monoid_typedef by (intro subtypeI) squash_types

lemma Monoid_is_Plus [derive]: "Monoid A \<prec> Plus A"
  unfolding Monoid_typedef by (intro subtypeI) squash_types

lemma Monoid_typeI:
  "\<lbrakk>str : Zero A; str : Plus A;
    \<forall>x: element A. str[@plus] `str[@zero] `x = x;
    \<forall>x: element A. str[@plus] `x `str[@zero] = x;
    \<forall>x: element A. \<forall>y: element A. \<forall>z: element A.
       str[@plus] `(str[@plus] `x `y) `z = str[@plus] `x `(str[@plus] `y `z)
    \<rbrakk> \<Longrightarrow> str : Monoid A"
  unfolding Monoid_typedef by squash_types

text \<open>
  Now we define the global operations as projections. Here, we also convert the set
  functions to meta functions. The axioms can then be derived.
\<close>

lemma
  assumes "M : Monoid A"
  shows 
  monoid_left_neut [simp]: "x : element A \<Longrightarrow> plus M (zero M) x = x" and
  monoid_right_neut [simp]: "x : element A \<Longrightarrow> plus M x (zero M) = x" and
  monoid_assoc [simp]: "\<lbrakk>x : element A; y : element A; z : element A\<rbrakk>
     \<Longrightarrow> plus M (plus M x y) z = plus M x (plus M y z)"
  
  using assms
  unfolding Monoid_typedef Zero_typedef plus_def zero_def
  by (squash_types, blast+)


subsection \<open>Instance for pairs\<close>

definition
  "pair_plus A B p1 p2 \<equiv>
    \<lparr> @plus = \<lambda>\<langle>a1,b1\<rangle>\<in>A\<times>B. \<lambda>\<langle>a2,b2\<rangle>\<in>A\<times>B. \<langle>plus p1 a1 a2, plus p2 b1 b2\<rangle> \<rparr>"

definition
  "pair_zero A B z1 z2 \<equiv>
    \<lparr> @zero = \<langle>zero z1, zero z2\<rangle> \<rparr>"

(* TODO: Need some form of structure composition: pair_monoid = pair_zero [+] pair_plus *)
definition
  "pair_monoid A B m1 m2 \<equiv>
    \<lparr> @zero = (pair_zero A B m1 m2)[@zero], @plus = (pair_plus A B m1 m2)[@plus] \<rparr>"

lemma pair_monoid_ZERO [simp]: "(pair_monoid A B m1 m2)[@zero] = (pair_zero A B m1 m2)[@zero]"
  unfolding pair_monoid_def by simp

lemma pair_monoid_PLUS [simp]: "(pair_monoid A B m1 m2)[@plus] = (pair_plus A B m1 m2)[@plus]"
  unfolding pair_monoid_def by simp

text \<open>
  The following proofs illustrate that reasoning with types is still very much pedestrian
  and needs better automated support.
\<close>

lemma pair_plus_PLUS:
  "(pair_plus A B p1 p2)[@plus] = \<lambda>\<langle>a1,b1\<rangle>\<in>A\<times>B. \<lambda>\<langle>a2,b2\<rangle>\<in>A\<times>B. \<langle>plus p1 a1 a2, plus p2 b1 b2\<rangle>"
  unfolding pair_plus_def by simp

lemma pair_plus_type [type]:
  "pair_plus : (A : set) \<Rightarrow> (B : set) \<Rightarrow> Plus A \<Rightarrow> Plus B \<Rightarrow> Plus (A \<times> B)"
  apply (intro Pi_typeI Plus_typeI)
  apply (unfold pair_plus_PLUS split_def)
  by discharge_types (* TODO: takes very long *)

lemma pair_zero_type [type]:
  "pair_zero : (A : set) \<Rightarrow> (B : set) \<Rightarrow> Zero A \<Rightarrow> Zero B \<Rightarrow> Zero (A \<times> B)"
  unfolding Zero_typedef pair_zero_def zero_def
  by squash_types auto

lemma pair_monoid_type [type]:
  "pair_monoid : (A : set) \<Rightarrow> (B : set) \<Rightarrow> Monoid A \<Rightarrow> Monoid B \<Rightarrow> Monoid (A \<times> B)"
proof (intro Pi_typeI)

  fix A B p1 p2 assume [type]: "A : set" "B : set" "p1 : Monoid A" "p2 : Monoid B"
  let ?plus = "(pair_monoid A B p1 p2)[@plus]"
  let ?zero = "(pair_monoid A B p1 p2)[@zero]"

  show "pair_monoid A B p1 p2 : Monoid (A \<times> B)" 
  proof (rule Monoid_typeI)

    show "pair_monoid A B p1 p2 : Zero (A \<times> B)"
      by (rule Zero_typeI) auto
    show "pair_monoid A B p1 p2 : Plus (A \<times> B)"
      by (rule Plus_typeI) auto

    show "\<forall>x: element (A \<times> B). ?plus `?zero `x = x"
      unfolding split_paired_Ball
      by (auto simp: pair_plus_def pair_zero_def)

    show "\<forall>x: element (A \<times> B). ?plus `x `?zero = x"
      unfolding split_paired_Ball
        by (auto simp: pair_plus_def pair_zero_def)

      show "\<forall>x: element (A\<times>B). \<forall>y: element (A\<times>B). \<forall>z: element (A\<times>B). 
          ?plus `(?plus `x `y) `z = ?plus `x `(?plus `y `z)"
      unfolding split_paired_Ball
      by (auto simp: pair_plus_def pair_zero_def)
  qed
qed


lemma [type_instance]:
  "m1 : Plus A \<Longrightarrow> m2 : Plus B \<Longrightarrow> pair_plus A B m1 m2 : Plus (A \<times> B)"
  "m1 : Zero A \<Longrightarrow> m2 : Zero B \<Longrightarrow> pair_zero A B m1 m2 : Zero (A \<times> B)"
  "m1 : Monoid A \<Longrightarrow> m2 : Monoid B \<Longrightarrow> pair_monoid A B m1 m2 : Monoid (A \<times> B)"
  by discharge_types

declare [[auto_elaborate, trace_soft_types]]

lemma "x + 0 = x"
  print_types
  oops

lemma "\<langle>x, y\<rangle> + 0 = \<langle>x, y\<rangle>"
  print_types
  oops

lemma "x + (y + z) = x + y + z"
  print_types
  oops

lemma "x + y = z + w \<and> u + v = 0"
  print_types
  oops


subsection \<open>Extension to groups\<close>

declare [[auto_elaborate = false]]

object Group "A :: set" is
  "Monoid A
  \<bar> \<lparr> (@plus plus) (@zero zero) (@inv inv).
    inv : element (A \<rightarrow> A) \<and>
    (\<forall>x\<in>A. plus `(inv `x) `x = zero) \<and>
    (\<forall>x\<in>A. plus `x `(inv `x) = zero) \<rparr>"

lemma group_is_monoid:  "G : Group A \<Longrightarrow> G : Monoid A"
  unfolding Group_typedef by squash_types


end
