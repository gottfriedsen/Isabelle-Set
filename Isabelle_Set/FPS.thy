theory FPS
  imports Lifting_Set Nat_Set Ring
begin

term "(\<And>x. x : Element A \<Longrightarrow> x : Element B) \<Longrightarrow> f : B \<rightarrow> C \<Longrightarrow> f : A \<rightarrow> C"

lemma "f : A \<rightarrow> B \<Longrightarrow> C \<subseteq> A \<Longrightarrow> f : C \<rightarrow> B"
  apply unfold_types

definition "function A B \<equiv> {f \<in> A \<times> B | f : A \<rightarrow> B}"

lemma elem_function: "f \<in> (function A B) \<equiv> f : A \<rightarrow> B"
  apply (rule eq_reflection, rule iffI)
  unfolding function_def
  using DepFunction_def meaning_of_adj
   apply fastforce
  apply (rule collectI)
   defer apply assumption
  unfolding DepFunction_def meaning_of_adj function_like_def
  apply (erule conjE)
  sorry

lemma Elem_function: "Element (function A B) = Function A B"
  using elem_function
  by (metis DepFunctionI collect_iff function_def not_mem_emptyset pairsetE)

no_notation zero_implicit ("0")

lemma Ring_zero_type: "\<And>R A. R : Ring A \<Longrightarrow> zero R : Element A"
  by (simp add: Group_Monoid Monoid_Zero Zero_zero_type zero_def)


locale formal_power_series =
  fixes A R :: set
  assumes Ring_R: "R : Ring A"
begin

definition "fps_rep = function \<nat> A"
abbreviation "FPS_rep \<equiv> Element fps_rep"

no_notation comp  (infixl "\<circ>" 55)

definition fps_map :: "(set \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set"
  where "fps_map f s \<equiv> (\<lambda>n\<in>\<nat>. f (s`n))"

definition fps_rel :: "(set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
  where "fps_rel S s1 s2 \<equiv> (\<forall>n\<in>\<nat>. S (s1`n) (s2`n))"

definition "fps_rep_zero = (\<lambda>n\<in>\<nat>. zero R)"

lemma fps_rep_zero_type: "fps_rep_zero : FPS_rep"
  unfolding fps_rep_zero_def fps_rep_def
  unfolding Elem_function
  apply (rule DepFunctionI, rule ElementD)
  apply (rule Ring_zero_type[OF Ring_R])
  done

lemma fps_app_elem: "s \<in> fps_rep \<Longrightarrow> n \<in> \<nat> \<Longrightarrow> s`n \<in> A"
  unfolding fps_rep_def elem_function
  by (rule DepFunctionE, assumption+)

definition "fps_rep_add = (\<lambda>s1\<in>fps_rep. \<lambda>s2\<in>fps_rep. \<lambda>n\<in>\<nat>. add R (s1`n) (s2`n))"

lemma FunctionI: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> (\<lambda>x\<in>A. f x) : A \<rightarrow> B"
  by (fact DepFunctionI)

lemma fps_rep_add_type: "fps_rep_add : fps_rep \<rightarrow> fps_rep \<rightarrow> fps_rep"
  unfolding fps_rep_add_def
  by (metis collect_iff elem_function empty_function function_def not_mem_emptyset pairset_empty_index)
  by (metis collectD1 elem_function empty_function function_def not_mem_emptyset pairset_empty_index)
  apply (rule DepFunctionI)
  using fps_app_elem
  unfolding Elem_function
  apply (rule DepFunctionI, rule ElementD)
  apply (rule Ring_zero_type[OF Ring_R])
  sorry

definition fps_inj :: "set \<Rightarrow> set"
  where "fps_inj x = (\<lambda>n\<in>\<nat>. if n = 0 then x else zero R)"

lemma [type]: "fps_inj: Element A \<Rightarrow> Element fps_rep"
  unfolding fps_rep_def fps_inj_def Elem_function
  apply unfold_types
  sorry

interpretation FPS: set_extension A fps_rep fps_inj
proof
  show "fps_inj : Element A \<Rightarrow> Element fps_rep"
    by simp
  show "\<forall>x \<in> A. \<forall>y \<in> A. fps_inj x = fps_inj y \<longrightarrow> x = y"
  proof ((rule Bounded_Quantifiers.ballI)+, rule impI)
    fix x y
    assume assms: "x \<in> A" "y \<in> A" "fps_inj x = fps_inj y"
    show "x = y"
      using lambda_eqE[OF assms(3)[unfolded fps_inj_def] nat_zero_nat]
      by simp
  qed
qed

abbreviation "fps \<equiv> FPS.def"
abbreviation "FPS \<equiv> Element fps"

lemmas subset_fps = FPS.extension_subset

lemma subtype_FPS: "x : Element A \<Longrightarrow> x : FPS"
  apply unfold_types
  apply (rule subsetE)
  apply (simp add: subset_fps)+
  done

abbreviation "FPS_Rel \<equiv> Ext_Rel fps FPS.Rep" (* not parametrized *)

lemmas FPS_lifting = set_extension_lifting(1)[OF FPS.set_extension_axioms]

abbreviation "eq_FPS_abs \<equiv> eq FPS.def"
abbreviation "eq_FPS_rep \<equiv> eq fps_rep"

lemma lifting_start: "lifting Eq_rep Eq_abs T abs rep \<Longrightarrow> Eq_rep x x \<Longrightarrow> const True (T x (abs x)) \<Longrightarrow> T x (abs x)"
  using lifting_Eq_rep(1)
  by metis

lemma FPS_Rel_zero: "\<exists>T t. T fps_rep_zero t"
  apply (rule exI, rule exI)
  apply (rule lifting_start[where x=fps_rep_zero])
    apply (rule FPS_lifting)
  sorry

end


term "formal_power_series.fps_rep_zero"

end