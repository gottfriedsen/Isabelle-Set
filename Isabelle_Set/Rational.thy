theory Rational
  imports Transfer_Test
begin

definition "rat_univ \<equiv> \<int> \<times> (\<int> \<setminus> {0})"

definition "rat_rep = {{q \<in> rat_univ | fst p \<cdot> snd q = snd p \<cdot> fst q}. p \<in> rat_univ}"

definition "int_in_rat i = {p \<in> rat_univ | fst p  = i \<cdot> snd p}"

lemma h1: "\<exists>x. x \<in> A \<and> y = g x \<Longrightarrow> y \<in> {g z | z \<in> A}" by simp

lemma
  [type]: "int_in_rat : Element \<int> \<Rightarrow> Element rat_rep"
proof -
  { fix i
    assume assm: "i \<in> \<int>"
    have "\<exists>x. x \<in> rat_univ \<and>
      {p \<in> rat_univ | fst p = i \<cdot> snd p} =
      {q \<in> rat_univ | fst x \<cdot> snd q = snd x \<cdot> fst q}"
    proof -
      let ?x = "\<langle>i, 1\<rangle>"
      have exists_conj_intro: "\<And>P Q x. \<lbrakk>P x; Q x\<rbrakk> \<Longrightarrow> \<exists>x. P x \<and> Q x" by blast
      have "?x \<in> rat_univ" by (auto simp add: rat_univ_def)               
      moreover have "{p \<in> rat_univ | fst p = i \<cdot> snd p} =
        {q \<in> rat_univ | fst ?x \<cdot> snd q = snd ?x \<cdot> fst q}"
        unfolding rat_univ_def 
        by (smt (verit, best) ElementI collect_cong fst_opair_eq int_one_mul pairset_fst snd_opair_eq)
      ultimately show ?thesis unfolding rat_univ_def
        by (rule exists_conj_intro[of "\<lambda>x. x \<in> \<int> \<times> (\<int> \<setminus> {0})" "\<langle>i, 1\<rangle>"])
    qed
  }
  note 1 = this                           
  show "int_in_rat : Element \<int> \<Rightarrow> Element rat_rep"
  unfolding rat_rep_def int_in_rat_def apply unfold_types
    using 1 by auto
qed

interpretation Rat: set_extension \<int> rat_rep int_in_rat
proof
  show "int_in_rat : Int' \<Rightarrow> Element rat_rep" by auto
  show "ball \<int> (\<lambda>x. ball \<int> (\<lambda>y. int_in_rat x = int_in_rat y \<longrightarrow> x = y))"
  proof ((rule Bounded_Quantifiers.ballI)+, rule impI)
    fix x y
    assume assms: "x \<in> \<int>" "y \<in> \<int>" "int_in_rat x = int_in_rat y"
    have "\<not>(x \<noteq> y)"
    proof
      assume prem: "x \<noteq>  y"
      let ?A = "{p \<in> rat_univ | fst p = x \<cdot> snd p}"
      let ?B = "{p \<in> rat_univ | fst p = y \<cdot> snd p}"
      have "\<langle>x, 1\<rangle> \<in> ?A" by (auto simp add: rat_univ_def)
      moreover have "\<langle>x, 1\<rangle> \<notin> ?B" using prem by auto
      ultimately show False using assms prem unfolding int_in_rat_def by simp
    qed
    thus "x = y" by simp
  qed
qed

definition "rat_rep_zero = {\<langle>0, i\<rangle> | i \<in> \<int> \<setminus> {0}}"
definition "rat_rep_one = {\<langle>i, i\<rangle> | i \<in> \<int> \<setminus> {0}}"

abbreviation rat ("\<rat>") where "\<rat> \<equiv> Rat.def"
definition "over_rep i j \<equiv> {p \<in> rat_univ | j \<cdot> fst p = i \<cdot> snd p}"
abbreviation "over i j \<equiv> Rat.Abs (over_rep i j)"

lemmas int_subset_rat [simp] = Rat.extension_subset

abbreviation "Rat \<equiv> Element \<rat>"

corollary [derive]: "n: Int' \<Longrightarrow> n: Rat"
  by (unfold_types, rule subsetE) auto

definition "rat_rep_add x y \<equiv>
  {r \<in> rat_univ | \<exists>p\<in>x. \<exists>q\<in>y. snd p \<cdot> snd q \<cdot> fst r = (snd q \<cdot> fst p + snd p \<cdot> fst q) \<cdot> snd r}"

definition "rat_rep_mul x y \<equiv>
  {r \<in> rat_univ | \<exists>p\<in>x. \<exists>q\<in>y. snd p \<cdot> snd q \<cdot> fst r = fst p \<cdot> fst q \<cdot> snd r}"

definition "rat_rep_neg x \<equiv> {\<langle>0 - j, i\<rangle> | \<langle>j, i\<rangle> \<in> x}"

definition "rat_rep_inv x \<equiv> {\<langle>j, i\<rangle> | \<langle>j, i\<rangle> \<in> x}"

definition "rat_rep_sub x y \<equiv> rat_rep_add x (rat_rep_neg y)"

definition "rat_rep_div x y \<equiv> rat_rep_mul x (rat_rep_inv y)"

lemma rat_rep_one_mul:
  "x \<in> rat_rep \<Longrightarrow> rat_rep_mul rat_rep_one x = x"
  unfolding rat_rep_def rat_rep_mul_def over_rep_def
  using int_one_mul
  sorry

lemma rat_rep_mul_inv:
  "x \<in> rat_rep \<Longrightarrow> y \<in> rat_rep \<Longrightarrow> y \<noteq> rat_rep_zero \<Longrightarrow> rat_rep_div (rat_rep_mul x y) y = x"
  sorry

lemma rat_rep_add_comm: "x \<in> rat_rep \<Longrightarrow> y \<in> rat_rep \<Longrightarrow> rat_rep_add x y = rat_rep_add y x"
  sorry

definition "rat_add x y = Rat.Abs (rat_rep_add (Rat.Rep x) (Rat.Rep y))"
definition "rat_sub x y = Rat.Abs (rat_rep_sub (Rat.Rep x) (Rat.Rep y))"
definition "rat_mul x y = Rat.Abs (rat_rep_mul (Rat.Rep x) (Rat.Rep y))"
definition "rat_div x y = Rat.Abs (rat_rep_div (Rat.Rep x) (Rat.Rep y))"

lemma rat_add_type [type]: "rat_add: Rat \<Rightarrow> Rat \<Rightarrow> Rat"
  unfolding rat_add_def
  sorry

lemma rat_mul_type [type]: "rat_mul: Rat \<Rightarrow> Rat \<Rightarrow> Rat"
  unfolding rat_mul_def
  sorry

lemma rat_div_type [type]: "rat_div: Rat \<Rightarrow> Rat \<Rightarrow> Rat"
  unfolding rat_div_def
  sorry

bundle notation_rat_add begin notation rat_add (infixl "+" 65) end
bundle no_notation_rat_add begin no_notation rat_add (infixl "+" 65) end

bundle notation_rat_sub begin notation rat_sub (infixl "-" 65) end
bundle no_notation_rat_sub begin no_notation rat_sub (infixl "-" 65) end

bundle notation_rat_mul begin notation rat_mul (infixl "\<cdot>" 65) end
bundle no_notation_rat_div begin no_notation rat_div (infixl "'/" 65) end

bundle notation_rat_div begin notation rat_div (infixl "'/" 65) end
bundle no_notation_rat_mul begin no_notation rat_mul (infixl "\<cdot>" 65) end

unbundle
  no_notation_int_add
  no_notation_int_sub
  no_notation_int_mul

  notation_rat_add
  notation_rat_sub
  notation_rat_mul
  notation_rat_div

definition "Rat_Rel p_rep p \<equiv> p \<in> Rat.def \<and> Rat.Rep p = p_rep"

(* This should be automated by lifting *)

method_setup unfold =
  \<open>Attrib.thms >> (fn thms => fn ctxt =>
    SIMPLE_METHOD (FIRSTGOAL (rewrite_goal_tac ctxt thms)))\<close>

method prove_rel_rep uses rel_def rep_def =
  (unfold rel_def rep_def, rule conjI, assumption, rule refl)

method prove_rel_inj uses rel_def =
  (unfold rel_def, unfold_types)

method prove_rel_abs uses rel_def rep_inv =
  (unfold rel_def, erule conjE, erule HOL.subst, erule rep_inv)

lemma Rat_Rel_Rep: "a \<in> Rat.def \<Longrightarrow> Rat_Rel (Rat.Rep a) a"
  by (prove_rel_rep rel_def: Rat_Rel_def rep_def: Rat.Rep_def)

lemma Rat_Rel_inj: "Rat_Rel a b \<Longrightarrow> Rat_Rel a' b \<Longrightarrow> a = a'"
  by (prove_rel_inj rel_def: Rat_Rel_def)

lemma Rat_Rel_Abs: "Rat_Rel a b \<Longrightarrow> Rat.Abs a = b"
  by (prove_rel_abs rel_def: Rat_Rel_def rep_inv: Rat.Rep_inverse)


lemma Rat_Rel_0 [transfer_rule]: "Rat_Rel rat_rep_zero 0"
  unfolding Rat.Rep_def Rat_Rel_def Rat.def_def rat_rep_zero_def
  sorry

lemma Rat_Rel_1 [transfer_rule]: "Rat_Rel rat_rep_one 1"
  unfolding Rat.Rep_def Rat_Rel_def Rat.def_def rat_rep_one_def
  sorry

lemma Rat_Rel_eq [transfer_rule]: "(Rat_Rel ===> Rat_Rel ===> (=)) (=) (=)"
  unfolding rel_fun_def Rat_Rel_def Rat.Rep_def Rat.def_def
  by (metis Rat.Rep_def Rat.Rep_inverse Rat.def_def)

lemma Rat_Rel_neq [transfer_rule]: "(Rat_Rel ===> Rat_Rel ===> (=)) (\<noteq>) (\<noteq>)"
  unfolding rel_fun_def Rat_Rel_def Rat.Rep_def Rat.def_def
  by (metis Rat.Rep_def Rat.Rep_inverse Rat.def_def)

lemma Rat_Rel_add [transfer_rule]: "(Rat_Rel ===> Rat_Rel ===> Rat_Rel) rat_rep_add rat_add"
  unfolding  rel_fun_def Rat_Rel_def
  using rat_add_def Rat.Abs_inverse rat_add_type
  using ElementD ElementI Pi_typeE
  by (metis (no_types, lifting) ElementD ElementI Pi_typeE)

lemma Rat_Rel_mul [transfer_rule]: "(Rat_Rel ===> Rat_Rel ===> Rat_Rel) rat_rep_mul rat_mul"
  unfolding  rel_fun_def Rat_Rel_def
  using rat_mul_def Rat.Abs_inverse rat_mul_type
  by (metis (no_types, lifting) ElementD ElementI Pi_typeE)

lemma Rat_Rel_div [transfer_rule]: "(Rat_Rel ===> Rat_Rel ===> Rat_Rel) rat_rep_div rat_div"
  unfolding  rel_fun_def Rat_Rel_def
  using rat_div_def Rat.Abs_inverse rat_div_type
  by (metis (no_types, lifting) ElementD ElementI Pi_typeE)

lemma Rat_Rel_All [transfer_rule]:
  "((Rat_Rel ===> (=)) ===> (=)) All All"
  unfolding rel_fun_def
  sorry

lemma Rat_Rel_Ball [transfer_rule]:
  "((Rat_Rel ===> (=)) ===> (=)) (ball rat_rep) (ball rat)"
  unfolding rel_fun_def Rat_Rel_def
  by (smt (verit, ccfv_threshold) ElementD ElementI Pi_typeE Rat.Abs_inverse Rat.Abs_type Rat.Rep_type ball_def)

definition "Type_Rel B B' \<equiv> (\<exists>A f. set_extension A B f \<and> B' = Element (set_extension.def A B f))"

definition "Rat_Type_Rel B B' \<equiv> B = rat_rep \<and> B' = Rat"

lemma "Rat_Type_Rel A B \<Longrightarrow> Type_Rel A B"
  using Rat.set_extension_axioms Rat_Type_Rel_def Type_Rel_def
  by auto

lemma "Type_Rel rat_rep Rat"
  unfolding Type_Rel_def
  using Rat.set_extension_axioms by blast

lemma [transfer_rule]: "Rat_Type_Rel rat_rep Rat"
  unfolding Type_Rel_def Rat_Type_Rel_def by blast

lemma [transfer_rule]: "(Rat_Rel ===> Rat_Type_Rel ===> (=)) (\<in>) (has_type)"
  unfolding rel_fun_def Rat_Rel_def Rat_Type_Rel_def
  by (metis Element_iff Pi_typeE Rat.Rep_type)

lemma "(Rat_Rel ===> Type_Rel ===> (=)) (\<in>) (has_type)"
  unfolding rel_fun_def Rat_Rel_def
  using Type_Rel_def Rat.Rep_def Rat.set_extension_axioms
  oops

lemma rat_one_mul: "ball rat (\<lambda>x. 1 \<cdot> x = x)"
  apply transfer
  using rat_rep_one_mul by simp

lemma "\<forall>x. x : Rat \<longrightarrow> 1 \<cdot> x = x"
  apply transfer
  using rat_rep_one_mul by simp

lemma rat_mul_inv:
  assumes "x: Rat" "y: Rat" "y \<noteq> 0"
  shows "rat_div (x \<cdot> y) y = x"
proof -
  have "All (\<lambda>x. All (\<lambda>y. x: Rat \<longrightarrow> y: Rat \<longrightarrow> y \<noteq> 0 \<longrightarrow> rat_div (x \<cdot> y) y = x))"
    apply transfer_start
    apply transfer_step+
    using rat_rep_mul_inv by simp

  have "ball rat (\<lambda>x. ball rat (\<lambda>y. y \<noteq> 0 \<longrightarrow> rat_div (x \<cdot> y) y = x))"
    apply transfer
    using rat_rep_mul_inv by simp
  thus ?thesis using assms ElementD by blast
qed

lemma atomize_all: "(\<And>x. P x) \<equiv> Trueprop (\<forall>x. P x)"
  by presburger

lemma atomize_all_sym: "Trueprop (\<forall>x. P x) \<equiv> (\<And>x. P x)"
  by presburger

lemma atomize_imp: "(A \<Longrightarrow> B) \<equiv> Trueprop (A \<longrightarrow> B)"
  by presburger

lemma atomize_imp_sym: "Trueprop (A \<longrightarrow> B) \<equiv> (A \<Longrightarrow> B)"
  by presburger

lemma atomize_not: "(A \<Longrightarrow> False) \<equiv> Trueprop (\<not> A)"
  by presburger

lemma atomize_eq: "(x \<equiv> y) \<equiv> Trueprop (x = y)"
  by presburger

lemma atomize_eq_sym: "Trueprop (x = y) \<equiv> (x \<equiv> y)"
  by presburger

lemma atomize_conj: "(A &&& B) \<equiv> Trueprop (A \<and> B)"
  by presburger

method_setup atomize' =
  \<open>Attrib.thms >> (fn thms => fn ctxt =>
    SIMPLE_METHOD
      (FIRSTGOAL (rewrite_goal_tac
        (put_simpset HOL_basic_ss ctxt addsimps thms) @{thms atomize_imp atomize_all atomize_eq})))\<close>
  "rewirte subgoal by given rules"

method_setup atomize_rev' =
  \<open>Attrib.thms >> (fn thms => fn ctxt =>
    SIMPLE_METHOD
      (FIRSTGOAL (rewrite_goal_tac
        (put_simpset HOL_basic_ss ctxt addsimps thms) @{thms atomize_eq_sym atomize_all_sym atomize_imp_sym})))\<close>
  "rewirte subgoal by given rules"

method atomize_transfer =
  (atomize', transfer, atomize_rev')

lemma conjE1: "(A \<and> B \<Longrightarrow> A)"
  by blast

lemma conjE2: "A \<and> B \<Longrightarrow> (B \<Longrightarrow> P) \<Longrightarrow> P"
  by blast

lemma Fun_typeE: "x \<in> A \<Longrightarrow> f : Element A \<Rightarrow> Element B \<Longrightarrow> f x \<in> B"
  by unfold_types

definition "surj' A B f \<equiv> ({f x | x \<in> A} = B)"

lemma Rep_surj:
  assumes set_ext: "set_extension A B f"
  shows "surj' (set_extension.def A B f) B (set_extension.Rep A f)"
proof -
  define def where "def = set_extension.def A B f"
  define Rep where "Rep = set_extension.Rep A f"
  define Abs where "Abs = set_extension.Abs A f"
  note 1 = this
  have 2: "{Rep y | y \<in> def} \<subseteq> B"
  proof
    fix y
    assume y: "y \<in> {Rep x | x \<in> def}"
    obtain x where x: "x \<in> def \<and> y = Rep x" using y by blast
    show "y \<in> B" using set_extension.Rep_type[OF set_ext] x Rep_def def_def
      by unfold_types
  qed
  have 3: "B \<subseteq> {Rep x | x \<in> def}"
  proof
    fix y
    assume y: "y \<in> B"
    have "Abs y \<in> def"
      using set_extension.Abs_type[OF set_ext] def_def Abs_def
      by unfold_types
    then obtain x where x: "x \<in> def \<and> y = Rep x"
      using set_extension.Abs_inverse[OF set_ext] Abs_def Rep_def
      by fastforce
    show "y \<in> {Rep x | x \<in> def}" using x 
      by blast
  qed
  show ?thesis
    using 2 3 unfolding def_def Rep_def surj'_def
    by (simp add: Basic.extensionality)
  qed

lemma l1: "x \<in> A \<Longrightarrow> surj' A B f \<Longrightarrow> (\<And>y. y \<in> B \<Longrightarrow> P y) \<Longrightarrow> P (f x)"
  using replI surj'_def by auto

lemma subst': "x = y \<Longrightarrow> P x \<Longrightarrow> P y" by (erule subst, assumption)

thm Rep_surj[OF Rat.set_extension_axioms]


lemma Rat_Rel_add': "(Rat_Rel ===> Rat_Rel ===> Rat_Rel) rat_rep_add rat_add"
  unfolding  rel_fun_def Rat_Rel_def
  apply atomize_rev'
  apply (rule conjI)
    (* drop non-relevant part of premises *)
   apply (drule conjE1)+
  unfolding rat_add_def
    (* make goal more readable *)
   apply(rule Fun_typeE[OF _ Rat.Abs_type])
   apply (rule l1[OF _ Rep_surj[OF Rat.set_extension_axioms]], assumption)
   apply (rule l1[OF _ Rep_surj[OF Rat.set_extension_axioms]], assumption)
    (* clean up premises *)
   apply (erule HOL.cnf.weakening_thm)
   apply (erule HOL.cnf.weakening_thm)
   defer
    (* prove second goal *)
  unfolding Rat.Abs_inverse
   apply (erule conjE2)+
   apply (erule subst')+
   apply (rule refl)
  sorry

lemma "\<And>x y. x: Rat \<Longrightarrow> y: Rat \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> rat_div (x \<cdot> y) y \<equiv> x"
  apply atomize_transfer
  sorry


lemma rat_add_comm:
  assumes "x: Rat" "y: Rat"
  shows "rat_add x y = rat_add y x"
proof-
  have "ball rat (\<lambda>x. ball rat (\<lambda> y. rat_add x y = rat_add y x))"
    apply transfer
    by (simp add: rat_rep_add_comm)
  thus ?thesis using assms
    using ElementD by blast
qed

end