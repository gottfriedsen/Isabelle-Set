theory Rewrite
imports HOL.HOL
begin

consts rewrite_HOLE :: "'a::{}"  ("\<hole>")

lemma eta_expand:
  fixes f :: "'a::{} \<Rightarrow> 'b::{}"
  shows "f \<equiv> \<lambda>x. f x" .

lemma rewr_imp:
  assumes "PROP A \<equiv> PROP B"
  shows "(PROP A \<Longrightarrow> PROP C) \<equiv> (PROP B \<Longrightarrow> PROP C)"
  apply (rule Pure.equal_intr_rule)
  apply (drule equal_elim_rule2[OF assms]; assumption)
  apply (drule equal_elim_rule1[OF assms]; assumption)
  done

lemma imp_cong_eq:
  "(PROP A \<Longrightarrow> (PROP B \<Longrightarrow> PROP C) \<equiv> (PROP B' \<Longrightarrow> PROP C')) \<equiv>
    ((PROP B \<Longrightarrow> PROP A \<Longrightarrow> PROP C) \<equiv> (PROP B' \<Longrightarrow> PROP A \<Longrightarrow> PROP C'))"
  apply (intro Pure.equal_intr_rule)
     apply (drule (1) cut_rl; drule Pure.equal_elim_rule1 Pure.equal_elim_rule2; assumption)+
   apply (drule Pure.equal_elim_rule1 Pure.equal_elim_rule2; assumption)+
  done

ML_file \<open>~~/src/HOL/Library/cconv.ML\<close>
ML_file \<open>~~/src/HOL/Library/rewrite.ML\<close>

end
