theory Poly_Rat
  imports Rational
begin

hide_type set
unbundle
  no_notation_rat_div

definition "function' a b = {s \<in> powerset (prodset a b) | function_like a s}"

lemma h1: "(\<And>x. x : s \<Longrightarrow> x : t) \<Longrightarrow> (\<And>x. x : t \<Longrightarrow> x : s) \<Longrightarrow> s = t"
  using meaning_of_type
  sorry

lemma function'_type: "Element (function' a b) = Function a b"
proof -
  { fix z
    assume assm: "z : type (\<lambda>x. x \<in> {S \<in> powerset (a \<times> b) | \<forall>a \<in> a. \<exists>!y. \<langle>a, y\<rangle> \<in> S})"
    have "z : (\<lambda>S. \<forall>a \<in> a. \<exists>!y. \<langle>a, y\<rangle> \<in> S) \<sqdot> type (\<lambda>x. x \<in> powerset (a \<times> b))"
      using meaning_of_type meaning_of_adj assm by (metis (no_types, lifting) collect_iff)
  }
  note 1 = this
  { fix z
    assume assm: "z : (\<lambda>S. \<forall>a \<in> a. \<exists>!y. \<langle>a, y\<rangle> \<in> S) \<sqdot> type (\<lambda>x. x \<in> powerset (a \<times> b))"
    have "z : type (\<lambda>x. x \<in> {S \<in> powerset (a \<times> b) | \<forall>a \<in> a. \<exists>!y. \<langle>a, y\<rangle> \<in> S})"
      using meaning_of_type meaning_of_adj assm by (metis (no_types, lifting) collectI)
  }
  note 2 = this
  show ?thesis
    unfolding Element_def function'_def DepFunction_def function_like_def Subset_def
    apply (rule h1) using 1 2 by blast+
qed

definition "poly_rat_rep = function' \<nat> \<rat>"

definition rat_in_poly_rat :: \<open>set \<Rightarrow> set\<close>
  where "rat_in_poly_rat x = (\<lambda>n\<in>\<nat>. if n = 0 then x else 0)"


lemma [type]: "rat_in_poly_rat: Element \<rat> \<Rightarrow> Element poly_rat_rep"
  unfolding poly_rat_rep_def rat_in_poly_rat_def
  apply unfold_types
  sorry


interpretation Poly_Rat: set_extension \<rat> poly_rat_rep rat_in_poly_rat
proof
  show "rat_in_poly_rat : Rat \<Rightarrow> Element poly_rat_rep"
    by simp
  { fix x y
    assume assms: "x \<in> \<rat>" "y \<in> \<rat>"
      "(\<lambda>n \<in> \<nat>. if n = 0 then x else 0) = (\<lambda>n \<in> \<nat>. if n = 0 then y else 0)"
    have "x = y" sorry
  }
  note 1 = this
  show " \<forall>x \<in> \<rat>.
      \<forall>y \<in> \<rat>. rat_in_poly_rat x = rat_in_poly_rat y \<longrightarrow> x = y"
    unfolding rat_in_poly_rat_def
    using 1 by blast
qed

abbreviation "poly_rat \<equiv> Poly_Rat.def"
abbreviation "Poly_Rat \<equiv> Element poly_rat"

lemmas rat_subset_poly_rat [simp] = Poly_Rat.extension_subset

corollary [derive]: "x : Rat \<Longrightarrow> x : Poly_Rat"
  apply unfold_types
  apply (rule subsetE)
  using rat_subset_poly_rat by blast

definition "poly_rat_rep_add p q = (\<lambda>n\<in>\<nat>. p`n + q`n)"

definition "poly_rat_rep_coeffs p = rng p"

lemma "p \<in> poly_rat_rep \<Longrightarrow> q \<in> poly_rat_rep \<Longrightarrow> poly_rat_rep_add p q \<in> poly_rat_rep"
  unfolding poly_rat_rep_def poly_rat_rep_add_def
  using lambda_function_typeI' rat_add_type eval_type function'_type
  sorry

definition "poly_rat_rep_zero = (\<lambda>n\<in>\<nat>. 0)"

lemma poly_rat_zero_add_rep: "p \<in> poly_rat_rep \<Longrightarrow> poly_rat_rep_add poly_rat_rep_zero p = p"
  unfolding poly_rat_rep_zero_def poly_rat_rep_add_def poly_rat_rep_def
  sorry

definition "poly_rat_add p q = Poly_Rat.Abs (poly_rat_rep_add (Poly_Rat.Rep p) (Poly_Rat.Rep q))"

definition "poly_rat_coeffs p = poly_rat_rep_coeffs (Poly_Rat.Rep p)"

lemma poly_rat_add_type [type]: "poly_rat_add: Poly_Rat \<Rightarrow> Poly_Rat \<Rightarrow> Poly_Rat"
  sorry

bundle notation_poly_rat_add begin notation poly_rat_add (infixl "+" 65) end
bundle no_notation_poly_rat_add begin no_notation poly_rat_add (infixl "+" 65) end

unbundle
  no_notation_rat_add
  notation_poly_rat_add

definition "Poly_Rat_Rel p_rep p \<equiv> p \<in> Poly_Rat.def \<and> Poly_Rat.Rep p = p_rep"

lemma zero_in_rat: "0 \<in> \<rat>"
  using Rat_Rel_0 Rat_Rel_def by blast

lemma Poly_Rat_Rel_0 [transfer_rule]: "Poly_Rat_Rel poly_rat_rep_zero 0"
proof -
  have "Poly_Rat.Rep 0 = poly_rat_rep_zero"
    unfolding Poly_Rat.Rep_def poly_rat_rep_zero_def rat_in_poly_rat_def
    by (simp add: zero_in_rat)
  moreover have "0 \<in> poly_rat"
    unfolding Poly_Rat.def_def
    by (simp add: zero_in_rat)
  ultimately show ?thesis
    unfolding Poly_Rat_Rel_def
    by blast
qed

lemma Poly_Rel_eq [transfer_rule]: "(Poly_Rat_Rel ===> Poly_Rat_Rel ===> (=)) (=) (=)"
  unfolding rel_fun_def Poly_Rat_Rel_def Poly_Rat.Rep_def Poly_Rat.def_def
  by (metis Poly_Rat.Rep_def Poly_Rat.Rep_inverse Poly_Rat.def_def)

lemma Poly_Rel_add [transfer_rule]: "(Poly_Rat_Rel ===> Poly_Rat_Rel ===> Poly_Rat_Rel) poly_rat_rep_add poly_rat_add"
  unfolding  rel_fun_def Poly_Rat_Rel_def
  using poly_rat_add_def Poly_Rat.Abs_inverse poly_rat_add_type
  sorry

lemma Poly_Rel_All [transfer_rule]:
  "((Poly_Rat_Rel ===> (=)) ===> (=)) (ball poly_rat_rep) (ball poly_rat)"
  unfolding rel_fun_def Poly_Rat_Rel_def
  sorry

lemma "\<forall>p\<in>poly_rat. 0 + p = p"
  apply transfer
  by (simp add: poly_rat_zero_add_rep)

definition "Poly_Int = (\<lambda>p. poly_rat_coeffs p \<subseteq> \<int>) \<sqdot> Poly_Rat"

lemma rng_lambdaI: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> rng (lambda A f) \<subseteq> B"
  by blast

lemma Int_is_Poly_Int:
  assumes "i : Int'"
  shows "i : Poly_Int"
proof -
  let ?poly_int = "{p \<in> poly_rat | poly_rat_coeffs p \<subseteq> \<int>}"
  let ?p = "\<lambda>n \<in> \<nat>. if n = 0 then i else 0"
  have zero_in_int: "0 \<in> \<int>" by simp
  have i_in_int: "i \<in> \<int>" by simp
  have i_in_poly_rat: "i \<in> poly_rat"
    using i_in_int rat_subset_poly_rat int_subset_rat by blast
  have "i \<in> \<rat>" by simp
  hence "Poly_Rat.Rep i = rat_in_poly_rat i"
    using Poly_Rat.Rep_def by simp
  moreover have "rat_in_poly_rat i = ?p"
    using rat_in_poly_rat_def by simp
  ultimately have "poly_rat_coeffs i \<subseteq> \<int>"
    using zero_in_int i_in_int poly_rat_coeffs_def poly_rat_rep_coeffs_def rng_lambdaI by simp
  with i_in_poly_rat have "i \<in> ?poly_int" by simp
  thus ?thesis
    using Poly_Int_def Element_iff meaning_of_adj collect_iff by metis
qed

lemma "(\<And>p. p : Poly_Int \<Longrightarrow> P p) \<Longrightarrow> i : Int' \<Longrightarrow> P i"
  using Int_is_Poly_Int by blast

end