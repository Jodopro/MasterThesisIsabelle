theory IEEE_Properties_Examples
imports IEEE_Properties_Float_Operations 
begin

definition "pre_fadd a' b' \<longleftrightarrow>  \<not>(a' = PInfty \<and> b' = MInfty \<or> a'=MInfty \<and>b'=PInfty)"
definition "pre_fadd_c a b \<longleftrightarrow> \<not>(is_infinity a \<and> is_infinity b \<and> sign a \<noteq> sign b)"

lemma pre_fadd_relation:
  assumes "pre_fadd a' b'"
    and "extended_valof (a::('e, 'f) float) \<le> a'" and "extended_valof b \<le> b'"
      and nnana: "\<not>(is_nan a)" and nnanb: "\<not>(is_nan b)"
    shows "pre_fadd_c a b"
  sorry
  
lemma add_two_numbers_infinite':
  assumes illegal_cases: "\<not>(a' = PInfty \<and> b' = MInfty \<or> a'=MInfty \<and>b'=PInfty)"
      and bound_a: "extended_valof (a::('e, 'f) float) \<le> a'" and bound_b: "extended_valof b \<le> b'"
      and nnana: "\<not>(is_nan a)" and nnanb: "\<not>(is_nan b)"
      and len_e: "LENGTH('e) > 1"
    shows "(extended_valof (fadd To_ninfinity a b) \<le> a' + b') \<and> \<not> is_nan (fadd To_ninfinity a b)"
  apply rule
  apply (rule order_trans)
    apply (rule add_two_numbers_infinite(1)[where c="0"]) 
        apply fact
  apply fact
      apply (simp add:not_is_nan_zero)
     apply fact
  subgoal 
    using assms pre_fadd_relation unfolding pre_fadd_def pre_fadd_c_def apply simp by blast
  using bound_a bound_b
   apply (simp add: add_mono)
  apply (rule add_two_numbers_infinite(3)[where c="0"])
      apply fact
     apply fact
    apply (simp add:not_is_nan_zero)
   apply fact
  using assms pre_fadd_relation unfolding pre_fadd_def pre_fadd_c_def apply simp by blast
  
lemma float_list_sum: 
  assumes eval_rel: "list_all2 (\<lambda>f r. \<not>is_nan f \<and> extended_valof f \<le> r) (xs::('e, 'f) float list) xs'"
  assumes "\<forall>r\<in>set xs'. r\<noteq>PInfty \<and> r\<noteq>MInfty"
    and len_e: "LENGTH('e) > 1" 
  shows "extended_valof (foldr (fadd To_ninfinity) xs 0) \<le> foldr (+) xs' 0 \<and> \<not> is_nan (foldr (fadd To_ninfinity) xs 0)"
  using assms apply (induction xs xs' rule: list_all2_induct)
   apply (simp add:extended_valof_zero not_is_nan_zero)
  apply clarsimp
  apply (rule add_two_numbers_infinite')
  apply simp_all
  done


end