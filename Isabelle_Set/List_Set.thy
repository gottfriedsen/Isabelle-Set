theory List_Set
  imports Option_Set
begin

definition Nil_rep where "Nil_rep = inl {}"
definition Cons_rep where "Cons_rep x xs = inr \<langle>x, xs\<rangle>"

lemma nil_neq_cons: "Nil_rep \<noteq> Cons_rep x xs"
  unfolding Nil_rep_def Cons_rep_def
  by simp

lemma cons_inject [iff]: "Cons_rep x xs = Cons_rep y ys \<longleftrightarrow> x = y \<and> xs = ys"
  unfolding Cons_rep_def
  by simp

hide_const lfp

definition List_rep where
  "List_rep A = lfp (univ A) (\<lambda>L. {Nil_rep} \<union> {Cons_rep x xs | \<langle>x, xs\<rangle> \<in> A \<times> L})"

lemma List_rep_distinct[simp]: "Nil_rep \<noteq> Cons_rep x xs"
  unfolding Nil_rep_def Cons_rep_def by simp

hide_fact def_lfp_unfold
hide_fact monotoneI

lemma Nil_rep_in_univ: "Nil_rep \<in> univ A"
  by (simp add: Nil_rep_def empty_in_univ univ_closed_inl)

lemma Cons_rep_in_univ: "x \<in> A \<Longrightarrow> xs \<in> univ A \<Longrightarrow> Cons_rep x xs \<in> univ A"
  using Cons_rep_def univ_closed_inr univ_opair_closed univ_transitive3 by presburger

lemma List_rep_mono: "(\<lambda>L. {Nil_rep} \<union> {Cons_rep x xs | \<langle>x, xs\<rangle> \<in> A \<times> L}) : Monop (univ A)"
  apply unfold_types
  apply (rule conjI, rule monotoneI)
  by (blast, auto simp add: Nil_rep_in_univ Cons_rep_in_univ)

lemmas List_rep_unfold = def_lfp_unfold[OF List_rep_mono List_rep_def]

lemma Nil_rep_type [type]: "Nil_rep: Element (List_rep A)"
  by (subst List_rep_unfold) (unfold_types, auto)

lemma Cons_rep_type [type]: "Cons_rep: Element A \<Rightarrow> Element (List_rep A) \<Rightarrow> Element (List_rep A)"
  by (subst (2) List_rep_unfold) (unfold_types, auto)

lemma Cons_rep_type': "x \<in> A \<Longrightarrow> xs \<in> List_rep A \<Longrightarrow> Cons_rep x xs \<in> List_rep A"
  by simp

lemma opairD2: "\<langle>a, b\<rangle> \<in> A \<times> B \<Longrightarrow> b \<in> B"
  by simp

hide_fact def_lfp_induct
hide_const collect
thm def_lfp_induct
lemma List_rep_induct:
  assumes xs_type: "xs: Element (List_rep A)"
  assumes Nil: "P Nil_rep"
  assumes Cons: "\<And>x xs. x: Element A \<Longrightarrow> xs: Element (List_rep A) \<Longrightarrow> P xs \<Longrightarrow> P (Cons_rep x xs)"
  shows "P xs"
proof (rule def_lfp_induct[OF List_rep_mono List_rep_def, where ?P=P and ?a=xs and ?A1=A])
  from xs_type show "xs \<in> List_rep A" by unfold_types
next
  fix x assume assm: "x \<in> {Nil_rep} \<union> {Cons_rep x xs | \<langle>x, xs\<rangle> \<in> A \<times> collect (List_rep A) P}"
  show "P x"
  proof (cases "x=Nil_rep")
    case True
    then show ?thesis
      using Nil Element_iff by simp
  next
    case False
    obtain y ys where x: "x = Cons_rep y ys"
      using False assm by auto
    have y_type: "y : Element A" using x assm sorry
    have ys_type: "ys : Element (List_rep A)" sorry
    have "x \<in> {Cons_rep x xs | \<langle>x, xs\<rangle> \<in> A \<times> collect (List_rep A) P}"
      using assm False List_rep_distinct by blast
    then have "ys \<in> collect (List_rep A) P"
      using x collectD2[of _ "List_rep A" P] opairD2[of y ys A "collect (List_rep A) P"]
      sorry
    hence "P ys" using x assm collectD2 pairsetD2 by blast
    thus ?thesis
      using x Cons[OF y_type ys_type] by simp
  qed
qed

definition "singleton_rep x = Cons_rep x Nil_rep"

lemma singleton_rep_type: "singleton_rep : Element A \<Rightarrow> Element (List_rep A)"
  apply unfold_types
  unfolding singleton_rep_def
  using Cons_rep_type Nil_rep_type
  by simp

lemma singleton_rep_inject [iff]: "singleton_rep x = singleton_rep y \<longleftrightarrow> x = y"
  unfolding singleton_rep_def by simp

definition "option_in_list = option_case singleton_rep Nil_rep"

lemma option_in_list_type: "option_in_list : Option A \<Rightarrow> Element (List_rep A)"
  apply unfold_types
  unfolding option_in_list_def
  using option_case_type[OF singleton_rep_type Nil_rep_type] by simp

interpretation List: set_extension "option A" "List_rep A" option_in_list
proof
  show "option_in_list : Option A \<Rightarrow> Element (List_rep A)"
    using option_in_list_type .
  show "\<forall>x \<in> option A. \<forall>y \<in> option A. option_in_list x = option_in_list y \<longrightarrow> x = y"
    unfolding option_in_list_def
    using cons_inject singleton_rep_inject
    case_some singleton_rep_def
    by (smt (z3) Bounded_Quantifiers.ballI Bounded_Quantifiers.bexE nil_neq_cons option_case_def option_iff)
qed

abbreviation "list \<equiv> List.def"
abbreviation "List A \<equiv> Element (list A)"

lemmas option_subset_list [simp] = List.extension_subset

corollary [derive]: "x : Option A \<Longrightarrow> x : List A"
  apply unfold_types
  apply (rule subsetE)
  using option_subset_list by auto

definition "Nil A = List.Abs A Nil_rep"

definition "Cons A x xs = List.Abs A (Cons_rep x (List.Rep A xs))"

lemma Nil_type [type]: "Nil A : List A"
  apply unfold_types
  unfolding Nil_def by simp

lemma Cons_type [type]: "Cons A : (Element A \<Rightarrow> List A \<Rightarrow> List A)"
proof (unfold_types)
  fix x xs
  assume assms: "x \<in> A" "xs \<in> list A"
  have "List.Rep A xs \<in> List_rep A" by simp
  thus "Cons A x xs \<in> list A"
    unfolding Cons_def
    using  Cons_rep_type' by simp
qed

definition "List_Rel A xs xs' \<equiv> xs' \<in> List.def A \<and> List.Rep A xs' = xs"

definition "Eq A x y \<equiv> x \<in> A \<and> x = y"

lemma Eq_refl [transfer_rule]: "x \<in> A \<Longrightarrow> Eq A x x"
  unfolding Eq_def by simp

lemma List_Rel_Nil [transfer_rule]: "List_Rel A Nil_rep (Nil A)"
  unfolding List_Rel_def Nil_def by simp

lemma List_Rel_Cons [transfer_rule]: "((Eq A) ===> List_Rel A ===> List_Rel A) Cons_rep (Cons A)"
  unfolding rel_fun_def List_Rel_def Cons_def
proof auto
  fix x x' xs
  assume assms: "Eq A x' x" "xs \<in> list A"
  have "x : Element A"
    using assms(1) Eq_def by auto
  moreover have "List.Rep A xs : Element (List_rep A)"
    using assms(1) by simp
  ultimately have "Cons_rep x (List.Rep A xs) : Element (List_rep A)"
    using Cons_rep_type by simp
  thus "List.Abs A (Cons_rep x (List.Rep A xs)) \<in> list A"
    using List.Abs_type Element_iff by simp
  show "x = x'" using assms(1) Eq_def by simp
qed

lemma List_Rel_eq [transfer_rule]: "(List_Rel A ===> List_Rel A ===> (=)) (=) (=)"
  unfolding rel_fun_def List_Rel_def
  using List.Rep_inverse by fastforce

lemma List_Rel_All [transfer_rule]: "((List_Rel A ===> (=)) ===> (=)) All All"
  unfolding rel_fun_def List_Rel_def
  sorry

lemma Nil_neq_Cons: "Nil A \<noteq> Cons A x xs"
  apply transfer_start
  oops

end