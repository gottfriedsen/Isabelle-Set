theory Transfer_Test
imports Integer HOL.Transfer HOL.Sledgehammer
begin

(* resolve name clashes *)
no_syntax "_Bex" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool" ("(3\<exists>(_/\<in>_)./ _)" [0, 0, 10] 10)
no_notation Set.member ("(_/ : _)" [51, 51] 50)
no_notation Set.member  ("'(\<in>')")
no_notation Set.member ("(_/ \<in> _)" [51, 51] 50)
no_notation Set.empty ("{}")
no_syntax "_Finset" :: "args \<Rightarrow> 'a set" ("{(_)}")
no_syntax "_UNION" :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>_\<in>_./ _)" [0, 0, 10] 10)
no_notation BNF_Def.convol ("\<langle>(_,/ _)\<rangle>")
no_notation Product_Type.Times (infixr "\<times>" 80)
no_notation Nat.Nats ("\<nat>")
no_notation Int.ring_1_class.Ints ("\<int>")
no_notation Groups.plus_class.plus (infixl "+" 65)
no_notation Groups.zero_class.zero ("0")
hide_fact sumE
hide_const fst snd
hide_const Nat nat
notation rel_fun  (infixr "===>" 55)

lemma int_rep_mul_inj_1:
  assumes assms: "i \<in> int_rep" "i' \<in> int_rep" "j \<in> int_rep \<setminus> {inl 0}"
    "int_rep_mul i j = int_rep_mul i' j"
  shows "i = i'"
  sorry

lemma int_rep_mul_inj_2:
  assumes assms: "i \<in> int_rep" "i' \<in> int_rep" "j \<in> int_rep \<setminus> {inl 0}"
    "int_rep_mul j i = int_rep_mul j i'"
  shows "i = i'"
  sorry

definition "int_rep_div i j \<equiv> (THE k. k \<in> int_rep \<and> int_rep_mul j k = i)"

lemma
  assumes i: "i \<in> int_rep"
    and j: "j \<in> (int_rep \<setminus> {inl 0})"
    and exists_k: "\<exists>k\<in>int_rep. i = int_rep_mul j k"
  shows "int_rep_div i j \<in> int_rep"
proof -
  let ?k = "(THE k. k \<in> int_rep \<and> int_rep_mul j k = i)"
  obtain k where k: "k \<in> int_rep \<and> int_rep_mul j k = i"
    using exists_k by blast
  have k_in_int_rep: "?k \<in> int_rep"
    using k int_rep_mul_inj_2[of k _ j] theI[of _ k]
    by (smt (verit, ccfv_threshold) j)
  show ?thesis
    unfolding int_rep_div_def
    using k_in_int_rep .
qed

definition "int_div i j \<equiv> Int.Abs (int_rep_div (Int.Rep i) (Int.Rep j))"

lemma int_div_type: "int_div: Int' \<Rightarrow> Int' \<Rightarrow> Int'"
  unfolding int_div_def
  using  [[type_derivation_depth=3]] \<comment> \<open>Need increased depth *EXAMPLE*\<close>
  oops

(* transfer relation *)
definition "Int_Rel i_rep i \<equiv> i \<in> Int.def \<and> Int.Rep i = i_rep"

(* transfer rules *)
lemma bi_unique_Int_Rel [transfer_rule]: "bi_unique Int_Rel"
  unfolding Int_Rel_def bi_unique_def
  using Int.Rep_inverse by fastforce

lemma Int_Rel_0 [transfer_rule]: "Int_Rel (inl 0) 0"
  unfolding Int.Rep_def Int_Rel_def Int.def_def
  by (simp add: int_rep_def)

lemma Int_Rel_eq [transfer_rule]: "(Int_Rel ===> Int_Rel ===> (=)) (=) (=)"
  unfolding rel_fun_def Int_Rel_def Int.Rep_def Int.def_def
  by auto

lemma Int_Rel_add [transfer_rule]: "(Int_Rel ===> Int_Rel ===> Int_Rel) int_rep_add int_add"
  unfolding  rel_fun_def Int_Rel_def
  using int_add_def Int.Abs_inverse int_add_type
  by (metis (no_types, lifting) ElementD ElementI Pi_typeE)

lemma Int_Rel_sub [transfer_rule]: "(Int_Rel ===> Int_Rel ===> Int_Rel) int_rep_sub int_sub"
  unfolding  rel_fun_def Int_Rel_def
  using int_sub_def Int.Abs_inverse int_sub_type
  by (metis (no_types, lifting) ElementD ElementI Pi_typeE)

lemma Int_Rel_mul [transfer_rule]: "(Int_Rel ===> Int_Rel ===> Int_Rel) int_rep_mul int_mul"
  unfolding  rel_fun_def Int_Rel_def
  using int_mul_def Int.Abs_inverse int_mul_type
  by (metis (no_types, lifting) ElementD ElementI Pi_typeE)

lemma Int_Rel_div [transfer_rule]: "(Int_Rel ===> Int_Rel ===> Int_Rel) int_rep_div int_div"
  unfolding  rel_fun_def Int_Rel_def
  using int_div_def Int.Abs_inverse
  oops

lemma Int_Rel_All [transfer_rule]:
  "((Int_Rel ===> (=)) ===> (=)) (ball int_rep) (ball \<int>)"
  unfolding rel_fun_def Int_Rel_def
  by (smt (verit, ccfv_threshold) ElementD ElementI Int.Abs_inverse Int.Abs_type Int.Rep_type Pi_typeE ball_def)

(* proving theorems by transfer *)
lemma
  assumes "int_rep_add (inl 0) (inl 0) = (inl 0)"
  shows "0 + 0 = 0"
  apply transfer
  using assms .

lemma
  "ball \<int> (\<lambda>i. ball \<int> (\<lambda>j. int_div (int_mul i j) j = i))"
  apply transfer
  oops

(* Can't hide notation for bounded universal quantifier from HOL.Set *)
lemma
  assumes "ball int_rep (\<lambda>i. ball int_rep (\<lambda>j. ball int_rep (\<lambda>k .
    int_rep_mul i (int_rep_sub j k) = int_rep_sub (int_rep_mul k i) (int_rep_mul j i))))"
  shows "ball \<int> (\<lambda>i. ball \<int> (\<lambda>j. ball \<int> (\<lambda>k. i \<cdot> (j - k) = (k \<cdot> i) - (j \<cdot> i))))"
  apply transfer
  using assms .

end