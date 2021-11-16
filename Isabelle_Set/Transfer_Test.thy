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

(* Can't hide notation for bounded universal quantifier from HOL.Set *)
lemma
  assumes "ball int_rep (\<lambda>i. ball int_rep (\<lambda>j. ball int_rep (\<lambda>k .
    int_rep_mul i (int_rep_sub j k) = int_rep_sub (int_rep_mul k i) (int_rep_mul j i))))"
  shows "ball \<int> (\<lambda>i. ball \<int> (\<lambda>j. ball \<int> (\<lambda>k. i \<cdot> (j - k) = (k \<cdot> i) - (j \<cdot> i))))"
  apply transfer
  using assms .

end