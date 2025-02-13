section \<open>Axioms of Tarski-Grothendieck Set Theory embedded in HOL.\<close>

theory Axioms
imports Setup
begin
paragraph \<open>Summary\<close>
text \<open>We follow the axiomatisation as described in @{cite "brown_et_al:LIPIcs:2019:11064"}, who also
describe the existence of a model if a 2-inaccessible cardinal exists.\<close>


text \<open>The primitive set type.\<close>
typedecl set

text \<open>The first four axioms.\<close>
axiomatization
  mem      :: \<open>set \<Rightarrow> set \<Rightarrow> bool\<close> and
  emptyset :: \<open>set\<close> and
  union       :: \<open>set \<Rightarrow> set\<close> and
  repl     :: \<open>set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set\<close>
where
  mem_induction: "(\<forall>X. (\<forall>x. mem x X \<longrightarrow> P x) \<longrightarrow> P X) \<longrightarrow> (\<forall>X. P X)" and
  emptyset: "\<not>(\<exists>x. mem x emptyset)" and
  union: "\<forall>X x. mem x (union X) \<longleftrightarrow> (\<exists>Y. mem Y X \<and> mem x Y)" and
  replacement: "\<forall>X y. mem y (repl X F) \<longleftrightarrow> (\<exists>x. mem x X \<and> y = F x)"

text \<open>Note: axioms @{thm mem_induction} and @{thm replacement} are axiom schemas in first-order
logic. Moreover, @{thm replacement} takes a meta-level function \<open>F\<close>.}\<close>

text \<open>Let us define some expected notation.\<close>

bundle hotg_mem_syntax begin notation mem (infixl "\<in>" 50) end
bundle no_hotg_mem_syntax begin no_notation mem (infixl "\<in>" 50) end

bundle hotg_emptyset_zero_syntax begin notation emptyset ("\<emptyset>") end
bundle no_hotg_emptyset_zero_syntax begin no_notation emptyset ("\<emptyset>") end

bundle hotg_emptyset_braces_syntax begin notation emptyset ("{}") end
bundle no_hotg_emptyset_braces_syntax begin no_notation emptyset ("{}") end

bundle hotg_emptyset_syntax
begin 
  unbundle hotg_emptyset_zero_syntax hotg_emptyset_braces_syntax
end
bundle no_hotg_emptyset_syntax
begin
  unbundle no_hotg_emptyset_zero_syntax no_hotg_emptyset_braces_syntax
end

bundle hotg_union_syntax begin notation union ("\<Union>_" [90] 90) end
bundle no_hotg_union_syntax begin no_notation union ("\<Union>_" [90] 90) end

unbundle hotg_mem_syntax hotg_emptyset_syntax hotg_union_syntax

text \<open>Based on the membership relation, we can define the subset relation.\<close>
definition subset :: \<open>set \<Rightarrow> set \<Rightarrow> bool\<close>
  where "subset A B \<equiv> (\<forall>x. x \<in> A \<longrightarrow> x \<in> B)"

text \<open>Again, we define some notation.\<close>
bundle hotg_subset_syntax begin notation subset (infixl "\<subseteq>" 50) end
bundle no_hotg_subset_syntax begin no_notation subset (infixl "\<subseteq>" 50) end
(* Note Kevin: I do not think we want to hide it, especially if one decides to use this theory along
another theory dealing with sets. *)
(*hide_const (open) subset \<comment> \<open>We hide the subset constant as it Will usually be referred to via infix.\<close>*)

unbundle hotg_subset_syntax

text \<open>The axiom of extensionality and powerset.\<close>
axiomatization
  powerset :: \<open>set \<Rightarrow> set\<close>
where
  extensionality: "\<forall>X Y. X \<subseteq> Y \<longrightarrow> Y \<subseteq> X \<longrightarrow> X = Y" and
  powerset: "\<forall>A x. x \<in> powerset A \<longleftrightarrow> x \<subseteq> A"

text \<open>Lastly, we want to axiomatise the existence of Grothendieck universes. This can be done in
different ways. Here, we again, we follow the approach from @{cite "brown_et_al:LIPIcs:2019:11064"}.\<close>

definition mem_transitive :: \<open>set \<Rightarrow> bool\<close>
  where "mem_transitive X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> x \<subseteq> X)"

definition ZF_closed :: \<open>set \<Rightarrow> bool\<close>
  where "ZF_closed U \<equiv> (
      (\<forall>X. X \<in> U \<longrightarrow> \<Union>X \<in> U) \<and>
      (\<forall>X. X \<in> U \<longrightarrow> powerset X \<in> U) \<and>
      (\<forall>X F. X \<in> U \<longrightarrow> (\<forall>x. x \<in> X \<longrightarrow> F x \<in> U) \<longrightarrow> repl X F \<in> U))"

text \<open>Remark: @{const ZF_closed} is a second-order statement.\<close>

text \<open>\<open>univ X\<close> is the smallest Grothendieck universe containing X.\<close>
axiomatization
  univ :: \<open>set \<Rightarrow> set\<close>
where
  univ_elem: "X \<in> univ X" and
  univ_trans: "mem_transitive (univ X)" and
  univ_ZF_closed: "ZF_closed (univ X)" and
  univ_min: "\<lbrakk>X \<in> U; mem_transitive U; ZF_closed U\<rbrakk> \<Longrightarrow> univ X \<subseteq> U"

(* Bundles to switch basic hotg notations on and off *)
bundle hotg_syntax
begin
  unbundle hotg_mem_syntax hotg_emptyset_syntax hotg_union_syntax hotg_subset_syntax
end
bundle no_hotg_syntax
begin 
  unbundle no_hotg_mem_syntax no_hotg_emptyset_syntax no_hotg_union_syntax no_hotg_subset_syntax
end

end