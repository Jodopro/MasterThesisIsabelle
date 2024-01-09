theory IEEE_Properties_Relations
  imports IEEE_Properties_Rounding "HOL-Eisbach.Eisbach"
begin

definition "float_rel_smaller a c \<equiv> \<not>(is_nan c) \<and> extended_valof c \<le> a" (*and the sign is correct*)
definition "float_rel_bigger a c \<equiv> \<not>(is_nan c) \<and> extended_valof c \<ge> a"

context 
  fixes ca::"('e, 'f)float"
  fixes aa1::ereal
  assumes len_e: "1 < LENGTH('e)"
begin

lemma float_rel_minus_1: 
  assumes rel_a1: "float_rel_smaller aa1 ca" 
  shows "float_rel_bigger (-aa1) (-ca)"
  using rel_a1 float_rel_bigger_def float_rel_smaller_def extended_valof_minus by fastforce

lemma float_rel_minus_2:
  assumes rel_a1: "float_rel_bigger aa1 ca" 
  shows "float_rel_smaller (-aa1) (-ca)"
  using rel_a1 float_rel_bigger_def float_rel_smaller_def extended_valof_minus by fastforce

lemmas float_rel_minus=
  float_rel_minus_1
  float_rel_minus_2

lemma float_rel_smaller_infinity: 
  assumes rel_a1: "float_rel_smaller aa1 ca"
  shows "ca = plus_infinity \<longrightarrow> aa1 = PInfty"
  using float_rel_smaller_def rel_a1
  by (metis ereal_infty_less_eq(1) infinity_ereal_def pinfty_eq_plus_inifity)

lemma float_rel_bigger_infinity: 
  assumes rel_a1: "float_rel_bigger aa1 ca"
  shows "ca = minus_infinity \<longrightarrow> aa1 = MInfty"
  using float_rel_bigger_def rel_a1
  by (metis minfty_eq_minus_inifity minus_infinity_smaller verit_la_disequality)

lemma infinity_add_smaller:
  assumes "is_infinity ca" and rel_a1: "float_rel_smaller aa1 ca"
  shows "float_rel_smaller (aa1+x) ca"
    and "float_rel_smaller (x+aa1) ca"
  unfolding float_rel_smaller_def
  apply rule
  using rel_a1 float_rel_smaller_def apply blast
  apply(cases "ca=minus_infinity")
  using minus_infinity_smaller apply blast
  using rel_a1 float_rel_smaller_def 
  apply (metis assms ereal_infty_less_eq(1) ereal_less_eq(1) infinity_ereal_def not_infinite pinfty_eq_plus_inifity plus_ereal.simps(2))
  apply rule
  using rel_a1 float_rel_smaller_def apply blast
  apply(cases "ca=minus_infinity")
  using minus_infinity_smaller apply blast
  using rel_a1 float_rel_smaller_def 
  by (metis assms ereal_plus_eq_PInfty extended_valof_def infinity_ereal_def is_infinity_cases order_antisym_conv plus_infinity_bigger)

(*lemma infinity_add_bigger:
  assumes "is_infinity ca"
    and x_not_pinfty: "x \<noteq> PInfty"
  shows "float_rel_bigger (aa2+x) ca"
    and "float_rel_bigger (x+aa2) ca"
  unfolding float_rel_bigger_def
  apply rule
  using rel_a2 float_rel_bigger_def apply blast
  apply(cases "ca=plus_infinity")
  using plus_infinity_bigger apply blast
  using rel_a2 float_rel_bigger_def x_not_pinfty
  subgoal 
    by (metis assms(1) ereal_MInfty_eq_plus ereal_less_eq(1) ereal_less_eq(2) extended_valof_not_infinity infinity_ereal_def uminus_ereal.simps(2) verit_la_disequality)
  apply rule
  using rel_a2 float_rel_bigger_def apply blast
  apply(cases "ca=plus_infinity")
  using plus_infinity_bigger apply blast
  using rel_a2 float_rel_bigger_def x_not_pinfty
  by (simp add: \<open>ca \<noteq> plus_infinity \<Longrightarrow> aa2 + x \<le> extended_valof ca\<close> add.commute)*)

end




context 
  fixes ca cb::"('e, 'f)float"
    and aa ab::ereal
  assumes len_e: "1 < LENGTH('e)"
    and rel_a: "float_rel_smaller aa ca"
    and rel_b: "float_rel_smaller ab cb"
begin

lemma float_add_smaller_infinite:
  assumes illegal_cases: "\<not>(is_infinity ca \<and> is_infinity cb \<and> sign ca \<noteq> sign cb)"
  shows "float_rel_smaller (aa + ab) (fadd To_ninfinity ca cb)"
  unfolding float_rel_smaller_def
  apply rule
  subgoal
    unfolding fadd_def
    using rel_a rel_b apply(simp add: float_rel_smaller_def illegal_cases if_not_P del: round.simps split del: if_split)
    apply (cases "\<not>is_infinity ca")
    apply (cases "\<not>is_infinity cb")
    apply (simp_all add:if_not_P if_P del: round.simps split del: if_split)
    using round_to_ninfinity_infinite len_e by blast
  subgoal
    unfolding fadd_def
    using rel_a rel_b apply(simp add: float_rel_smaller_def illegal_cases if_not_P del: round.simps split del: if_split)
    apply (cases "\<not>is_infinity ca")
    apply (cases "\<not>is_infinity cb")
    apply (simp_all add:if_not_P if_P extended_valof_zerosign del: round.simps split del: if_split)
    using round_to_ninfinity_infinite(1) len_e extended_valof_finite
      apply (metis add_mono_thms_linordered_semiring(1) dual_order.trans plus_ereal.simps(1))
    using float_rel_smaller_def len_e apply (metis infinity_add_smaller(2))
    using len_e float_rel_smaller_def infinity_add_smaller(1) rel_a by blast
  done

(*lemma float_mul_smaller_infinite:
  assumes illegal_cases1: "\<not>(is_infinity a \<and> is_zero b)" and illegal_cases2: " \<not>(is_zero a \<and> is_infinity b)"
  shows "float_rel_smaller (aa * ab) (fmul To_ninfinity ca cb)"
  unfolding float_rel_smaller_def
  apply rule
  subgoal
    unfolding fmul_def
    using rel_a rel_b apply(simp add: float_rel_smaller_def illegal_cases1 illegal_cases2 if_not_P del: round.simps split del: if_split)
    apply (cases "\<not>is_infinity ca")
    apply (cases "\<not>is_infinity cb")
    apply (simp_all add:if_not_P if_P del: round.simps split del: if_split)
    using round_to_ninfinity_infinite len_e apply blast
  subgoal
    unfolding fadd_def
    using rel_a rel_b apply(simp add: float_rel_smaller_def illegal_cases if_not_P del: round.simps split del: if_split)
    apply (cases "\<not>is_infinity ca")
    apply (cases "\<not>is_infinity cb")
    apply (simp_all add:if_not_P if_P extended_valof_zerosign del: round.simps split del: if_split)
    using round_to_ninfinity_infinite(1) len_e extended_valof_finite
      apply (metis add_mono_thms_linordered_semiring(1) dual_order.trans plus_ereal.simps(1))
    using float_rel_smaller_def len_e apply (metis infinity_add_smaller(2))
    using float_rel_bigger_def len_e float_rel_smaller_def infinity_add_smaller(1) rel_a by blast
  done*)

end

context 
  fixes ca cb::"('e, 'f)float"
    and aa ab::ereal
  assumes len_e: "1 < LENGTH('e)"
    and rel_a: "float_rel_smaller aa ca"
    and rel_b: "float_rel_bigger ab cb"
begin

lemma float_sub_smaller_infinite:
  assumes illegal_cases: "\<not>(is_infinity ca \<and> is_infinity cb \<and> sign ca = sign cb)"
  shows "float_rel_smaller (aa - ab) (fsub To_ninfinity ca cb)"
  apply(simp add: fsub_eq_fadd_minus)
  using float_add_smaller_infinite[OF len_e rel_a float_rel_minus(2)[OF len_e rel_b]] float_neg_sign1 illegal_cases minus_ereal_def
    by auto
end

lemma float_list_sum: 
  assumes eval_rel: "list_all2 (\<lambda>a c. float_rel_smaller a c) as (cs::('e, 'f) float list)"
  assumes "\<forall>c\<in>set as. c\<noteq>PInfty \<and> c\<noteq>MInfty"
    and len_e: "LENGTH('e) > 1" 
  shows "float_rel_smaller (foldr (+) as 0) (foldr (fadd To_ninfinity) cs 0)"
  using assms apply (induction as cs rule: list_all2_induct)
   apply (simp add:extended_valof_zero float_rel_smaller_def not_is_nan_zero)
  thm float_add_smaller_infinite
  apply simp
  apply (rule float_add_smaller_infinite)
     apply simp_all
  using float_rel_smaller_infinity float_rel_bigger_infinity oops (*both can only be minus_infinity but not proven yet*)

end