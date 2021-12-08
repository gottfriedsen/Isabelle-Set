theory Rational_T
  imports Transfer_Test
begin

no_syntax Ints :: "'a set"  ("\<int>")

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

lemma rat_sub_type [type]: "rat_sub: Rat \<Rightarrow> Rat \<Rightarrow> Rat"
  unfolding rat_sub_def
  sorry

lemma rat_mul_type [type]: "rat_mul: Rat \<Rightarrow> Rat \<Rightarrow> Rat"
  unfolding rat_mul_def
  sorry

lemma rat_div_type [type]: "rat_div: Rat \<Rightarrow> Rat \<Rightarrow> Rat"
  unfolding rat_div_def
  sorry

no_syntax inverse_divide :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "'/" 70)

bundle notation_rat_add begin notation rat_add (infixl "+" 65) end
bundle no_notation_rat_add begin no_notation rat_add (infixl "+" 65) end

bundle notation_rat_sub begin notation rat_sub (infixl "-" 65) end
bundle no_notation_rat_sub begin no_notation rat_sub (infixl "-" 65) end

bundle notation_rat_mul begin notation rat_mul (infixl "\<cdot>" 65) end
bundle no_notation_rat_mul begin no_notation rat_mul (infixl "\<cdot>" 65) end

bundle notation_rat_div begin notation rat_div (infixl "'/" 65) end
bundle no_notation_rat_div begin no_notation rat_div (infixl "'/" 65) end

unbundle
  no_notation_int_add
  no_notation_int_sub
  no_notation_int_mul

  notation_rat_add
  notation_rat_sub
  notation_rat_mul
  notation_rat_div

definition "Rat_Rel p_rep p \<equiv> p \<in> Rat.def \<and> Rat.Rep p = p_rep"

lemma Rat_Rel_0 [trans_rule]: "Rat_Rel rat_rep_zero 0"
  unfolding Rat.Rep_def Rat_Rel_def Rat.def_def rat_rep_zero_def
  sorry

lemma Rat_Rel_1 [trans_rule]: "Rat_Rel rat_rep_one 1"
  unfolding Rat.Rep_def Rat_Rel_def Rat.def_def rat_rep_one_def
  sorry

lemma Rat_Rel_eq [trans_rule]: "(Rat_Rel \<rightarrow> Rat_Rel \<rightarrow> (=)) (=) (=)"
  unfolding rel_fun_def Rat_Rel_def Rat.Rep_def Rat.def_def
  by (metis Rat.Rep_def Rat.Rep_inverse Rat.def_def)

lemma Rat_Rel_neq [trans_rule]: "(Rat_Rel \<rightarrow> Rat_Rel\<rightarrow> (=)) (\<noteq>) (\<noteq>)"
  unfolding rel_fun_def Rat_Rel_def Rat.Rep_def Rat.def_def
  by (metis Rat.Rep_def Rat.Rep_inverse Rat.def_def)

lemma Rat_Rel_add [trans_rule]: "(Rat_Rel \<rightarrow> Rat_Rel\<rightarrow> Rat_Rel) rat_rep_add rat_add"
  unfolding  rel_fun_def Rat_Rel_def
  using rat_add_def Rat.Abs_inverse rat_add_type
  by (metis (no_types, lifting) ElementD ElementI Pi_typeE)

lemma Rat_Rel_sub [trans_rule]: "(Rat_Rel \<rightarrow> Rat_Rel\<rightarrow> Rat_Rel) rat_rep_sub rat_sub"
  unfolding  rel_fun_def Rat_Rel_def
  using rat_sub_def Rat.Abs_inverse rat_sub_type
  by (metis (no_types, lifting) ElementD ElementI Pi_typeE)

lemma Rat_Rel_mul [trans_rule]: "(Rat_Rel \<rightarrow> Rat_Rel \<rightarrow> Rat_Rel) rat_rep_mul rat_mul"
  unfolding  rel_fun_def Rat_Rel_def
  using rat_mul_def Rat.Abs_inverse rat_mul_type
  by (metis (no_types, lifting) ElementD ElementI Pi_typeE)

lemma Rat_Rel_div [trans_rule]: "(Rat_Rel\<rightarrow> Rat_Rel \<rightarrow> Rat_Rel) rat_rep_div rat_div"
  unfolding  rel_fun_def Rat_Rel_def
  using rat_div_def Rat.Abs_inverse rat_div_type
  by (metis (no_types, lifting) ElementD ElementI Pi_typeE)

lemma Rat_Rel_All [trans_rule]:
  "((Rat_Rel \<rightarrow> (=)) \<rightarrow> (=)) All All"
  unfolding rel_fun_def
  sorry

lemma Rat_Rel_Ball [trans_rule]:
  "((Rat_Rel \<rightarrow> (=)) \<rightarrow> (=)) (ball rat_rep) (ball rat)"
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

lemma [trans_rule]: "Rat_Type_Rel rat_rep Rat"
  unfolding Type_Rel_def Rat_Type_Rel_def by blast

lemma [trans_rule]: "(Rat_Rel \<rightarrow> Rat_Type_Rel \<rightarrow> (=)) (\<in>) (has_type)"
  unfolding rel_fun_def Rat_Rel_def Rat_Type_Rel_def
  by (metis Element_iff Pi_typeE Rat.Rep_type)

lemma "(Rat_Rel ===> Type_Rel ===> (=)) (\<in>) (has_type)"
  unfolding rel_fun_def Rat_Rel_def
  using Type_Rel_def Rat.Rep_def Rat.set_extension_axioms
  oops

lemma [trans_rule]: "((=) \<rightarrow> (=)) (\<longrightarrow>) (\<longrightarrow>)" by blast

lemma []: "(=) x x" by blast

lemma rat_one_mul: "ball rat (\<lambda>x. 1 \<cdot> x = x)"
  apply trans
  using rat_rep_one_mul by simp

lemma "\<forall>x. x : Rat \<longrightarrow> 1 \<cdot> x = x"
  apply trans
  using rat_rep_one_mul by simp

no_syntax inverse_divide :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "'/" 70)
no_syntax inverse_divide :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "'/" 70)
term Fields.inverse_class.inverse_divide
term "rat_add x (f y a) = g x b"
term "g x"
term Rational.rat_div

lemma "snd \<langle>x, a\<rangle> + b = a + b"
  apply (trans_start fixing: x)
   apply trans_step
   apply trans_step
   apply trans_step
   apply trans_step
  sorry

lemma
  assumes "x = y"
  shows "rat_sub x y = 0"
  apply trans_start
  apply trans_step
  apply trans_step
  apply trans_step
  apply trans_step
  apply trans_step
  apply trans_step
  apply trans_step
  apply (rule HOL.allI)+
  sorry

lemma
  shows "x = y \<Longrightarrow> rat_sub x y = 0"
  apply trans_start
  apply trans_step
  apply trans_step
   apply trans_step
  defer
   apply trans_step
   apply trans_step
   apply trans_step
   apply trans_step
  apply (rule HOL.allI)+
  apply (rule HOL.impI)
  sorry

lemma "\<forall>x. x = x"
proof(rule HOL.allI)
  fix x
  show "x = x" by simp
qed

lemma rat_mul_inv:
  assumes "x: Rat" "y: Rat" "y \<noteq> 0"
  shows "rat_div (x \<cdot> y) y = x"
proof -
  have "All (\<lambda>x. All (\<lambda>y. x: Rat \<longrightarrow> y: Rat \<longrightarrow> y \<noteq> 0 \<longrightarrow> rat_div (x \<cdot> y) y = x))"
    apply trans_start
    apply trans_step+
    using rat_rep_mul_inv by simp

  have "ball rat (\<lambda>x. ball rat (\<lambda>y. y \<noteq> 0 \<longrightarrow> rat_div (x \<cdot> y) y = x))"
    apply transfer
    using rat_rep_mul_inv by simp
  thus ?thesis using assms ElementD by blast
qed

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