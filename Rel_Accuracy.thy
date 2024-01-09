theory Rel_Accuracy
  imports ULP_Accuracy
begin
(*
definition ulp_accuracy_expanded :: "real \<Rightarrow> ('e, 'f) float \<Rightarrow> real \<Rightarrow> bool" 
  where "ulp_accuracy_expanded a c u \<equiv> (is_finite c) \<and> \<bar>(valof c - a)\<bar> \<le> u * 2^(max (exponent c) 1) / 2^(2^(LENGTH('e) - 1) - 1 + LENGTH('f)) "
*)
definition rel_accuracy :: "real \<Rightarrow> ('e, 'f) float \<Rightarrow> real \<Rightarrow> bool"
  where "rel_accuracy a c u \<equiv> (is_finite c) \<and> \<bar>(valof c - a)\<bar> \<le> \<bar>valof c\<bar>*u/ 2^LENGTH('f)"

lemma rel_accuracy_non_negative:
  assumes "rel_accuracy a (c::('e,'f) float) u"
  shows "valof c \<noteq> 0 \<Longrightarrow> u \<ge> (0::real)"
proof -
  from rel_accuracy_def assms have "(0::real) \<le> \<bar>valof c\<bar>*u/ 2^LENGTH('f)" by force
  moreover have "valof c \<noteq> 0 \<Longrightarrow> (0::real) < \<bar>valof c\<bar>" by linarith
  ultimately have "valof c \<noteq> 0 \<Longrightarrow> u/ 2^LENGTH('f) \<ge> (0::real)"
    by (metis divide_divide_eq_right divide_le_0_abs_iff mult.commute zero_le_divide_iff zero_le_numeral zero_le_power)
  moreover have "2^LENGTH('f) > (0::real)" by fastforce
  ultimately show "valof c \<noteq> 0 \<Longrightarrow> u \<ge> (0::real)"
    by (simp add: zero_le_divide_iff)
qed

lemma ulp_accuracy_to_rel_accuracy:
  assumes "ulp_accuracy a (c::('e, 'f) float) u"
    and "exponent c \<noteq> 0"
  shows "rel_accuracy a c u"
  using assms apply(simp add:ulp_accuracy_def rel_accuracy_def ulp_equivelance abs_valof_eq2 bias_def ulp_divisor_rewrite)
 subgoal proof -
  {
    assume first_assm: "\<bar>valof c - a\<bar>
    \<le> u * (2::real) ^ IEEE.exponent c /
       (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))"
    have ge_1: "((2::real) ^ LENGTH('f) + real (fraction c)) / (2::real) ^ LENGTH('f) \<ge> 1" by auto
    from first_assm have ge_0: "0
    \<le> u * (2::real) ^ IEEE.exponent c /
       (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))" by argo
    have "u * (2::real) ^ IEEE.exponent c /
       (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) = 0 \<Longrightarrow>
        (u * (2::real) ^ IEEE.exponent c /
       (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) \<le> u * (2::real) ^ IEEE.exponent c /
       (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) * ((2::real) ^ LENGTH('f) + real (fraction c)) / (2::real) ^ LENGTH('f))" by force
    from ge_0 have g_0: "u * (2::real) ^ IEEE.exponent c /
       (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) \<noteq> 0 \<Longrightarrow>
        u * (2::real) ^ IEEE.exponent c /
       (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) > 0" by argo
    with ge_1 have "u * (2::real) ^ IEEE.exponent c /
       (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) \<noteq> 0 \<Longrightarrow> (u * (2::real) ^ IEEE.exponent c /
       (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) \<le> u * (2::real) ^ IEEE.exponent c /
       (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) * ((2::real) ^ LENGTH('f) + real (fraction c)) / (2::real) ^ LENGTH('f))" 
      using mult_le_cancel_left1[where c="u * (2::real) ^ IEEE.exponent c /
       (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))" and b="((2::real) ^ LENGTH('f) + real (fraction c)) / (2::real) ^ LENGTH('f)"] by simp
    with first_assm have "\<bar>valof c - a\<bar>
    \<le>  u * (2::real) ^ IEEE.exponent c /
       (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) * ((2::real) ^ LENGTH('f) + real (fraction c)) / (2::real) ^ LENGTH('f)" by fastforce
  } note implies_goal = this 
  then show "is_finite c \<and>
    \<bar>valof c - a\<bar>
    \<le> u * (2::real) ^ IEEE.exponent c /
       (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) \<Longrightarrow>
    (0::nat) < IEEE.exponent c \<Longrightarrow>
    \<bar>valof c - a\<bar>
    \<le> (2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c)) * u /
       ((2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) *
        (2::real) ^ LENGTH('f))" by argo
qed
  done

lemma rel_accuracy_to_ulp_accuracy1:
  assumes "rel_accuracy a (c::('e, 'f) float) u"
    and "exponent c \<noteq> 0"
  shows "ulp_accuracy a c (2*u)"
  using assms apply(simp add:ulp_accuracy_def rel_accuracy_def ulp_equivelance abs_valof_eq2 bias_def ulp_divisor_rewrite)
  subgoal proof -
  {
    have p1: "(2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) > 0" by fastforce
    have "(2::real) ^ IEEE.exponent c > 0" by auto
    moreover have "((2::real) ^ LENGTH('f) + real (fraction c)) > 0" using float_frac_ge
      by (simp add: add.commute add_strict_increasing2)
    ultimately have big_part_g0: "((2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) /
    ((2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c)))) > 0" using p1 by simp
    assume first_assm: "\<bar>valof c - a\<bar>
    \<le> (2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c)) * u /
       ((2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) *
        (2::real) ^ LENGTH('f))"
    then have tmp:"\<bar>valof c - a\<bar>
    \<le> u * (2::real) ^ IEEE.exponent c * (((2::real) ^ LENGTH('f) + real (fraction c))/ (2::real) ^ LENGTH('f))/((2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)))"
      by argo
    from float_frac_l  have  "real (fraction c) \<le> (2::real) ^ LENGTH('f)" using power_2_simp
      using less_or_eq_imp_le by auto
    then have "((2::real) ^ LENGTH('f) + real (fraction c)) \<le> 2*(2::real) ^ LENGTH('f)" by argo
    then have "(2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c)) \<le> (2::real) ^ IEEE.exponent c * 2*(2::real) ^ LENGTH('f)" by simp
    moreover from assms zero_val_exponent rel_accuracy_non_negative have "(0::real) \<le> u" by meson
    ultimately have "u * (2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c)) \<le> u* (2::real) ^ IEEE.exponent c * 2*(2::real) ^ LENGTH('f)"
      using mult_left_mono[where a="(2::real) ^ IEEE.exponent (c::('e, 'f) IEEE.float) * ((2::real) ^ LENGTH('f) + real (fraction c))" and b="(2::real) ^ IEEE.exponent c * 2*(2::real) ^ LENGTH('f)" and c=u] by linarith
    then have "u * (2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c))/ (2::real) ^ LENGTH('f) \<le> u* (2::real) ^ IEEE.exponent c * 2"
      by (simp add: pos_divide_le_eq)
    then have "u * (2::real) ^ IEEE.exponent c * (((2::real) ^ LENGTH('f) + real (fraction c))/ (2::real) ^ LENGTH('f))/((2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))) \<le>
          u * (2::real) ^ IEEE.exponent c * 2/((2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)))"
      by (simp add: pos_divide_le_eq)
    with tmp have "\<bar>valof c - a\<bar>
    \<le> (2::real) * u * (2::real) ^ IEEE.exponent c /
       (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))"
      by argo
  } note implies_goal = this 
  then show ?thesis
    using assms by(simp add:ulp_accuracy_def rel_accuracy_def ulp_equivelance abs_valof_eq2 bias_def ulp_divisor_rewrite)
qed
  done

lemma rel_accuracy_to_ulp_accuracy2:
  assumes "rel_accuracy a (c::('e, 'f) float) u"
    and "exponent c = 0"
    and "u \<ge> 0"
  shows "ulp_accuracy a c (2*u)"
  using assms apply(simp add:ulp_accuracy_def rel_accuracy_def ulp_equivelance abs_valof_eq2 bias_def ulp_divisor_rewrite)
  subgoal proof -
  {
    have p1: "(2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) > 0" by fastforce
    have p2: "((2::real) * real (fraction c)) \<ge> 0" using float_frac_ge by auto
    assume first_assm: "\<bar>valof c - a\<bar>
    \<le> (2::real) * real (fraction c) * u /
       ((2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) *
        (2::real) ^ LENGTH('f))"

    have "(2::real) * real (fraction c) \<le> (2::real) * (2::real) ^ LENGTH('f)" using float_frac_l less_eq_real_def by auto
    with p2 have "(2::real) * real (fraction c) / (2::real) ^ LENGTH('f) \<le> (2::real)"
      by (simp add: mult_imp_div_pos_le)
    then have "(2::real) * real (fraction c) / (2::real) ^ LENGTH('f) \<le> (4::real)"
      by (simp add: mult_imp_div_pos_le)
    then have "(2::real) * real (fraction c) / (2::real) ^ LENGTH('f) /((2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))) \<le> (4::real)/ (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))"
      using p1 div_less by blast
    then have "(2::real) * real (fraction c)  /
       ((2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) *
        (2::real) ^ LENGTH('f)) \<le> (4::real)/ (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))" by argo
    with assms have "(2::real) * real (fraction c) * u /
       ((2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)) *
        (2::real) ^ LENGTH('f)) \<le> (4::real) * u / (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))"
      using mult_right_mono by fastforce
    with first_assm have "(\<bar>valof c - a\<bar>
    \<le> (4::real) * u / (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)))" by argo
  } note implies_goal = this 
  then show ?thesis using assms by(simp add:ulp_accuracy_def rel_accuracy_def ulp_equivelance abs_valof_eq2 bias_def ulp_divisor_rewrite)
qed
  done

lemma rel_accuracy_to_ulp_accuracy:
  assumes "rel_accuracy a (c::('e, 'f) float) u"
    and "u \<ge> 0"
  shows "ulp_accuracy a c (2*u)"
  apply(cases "exponent c = 0")
  using assms rel_accuracy_to_ulp_accuracy2 apply blast
  using assms rel_accuracy_to_ulp_accuracy1 by blast

lemma rel_accuracy_to_factor_helper:
  assumes "\<bar>(b::real) - (a::real)\<bar> \<le> \<bar>b\<bar> * f"
    and "0 \<le> f"
  shows "\<exists>(d::real). (a = (1+d)*b \<and> \<bar>d\<bar>\<le> f)"
proof -
  {
    assume "b=0"
    moreover with assms have "a = 0" by simp
    ultimately have "\<exists>(d::real). (a = (1+d)*b \<and> \<bar>d\<bar>\<le> f)" using assms
      by (metis abs_le_self_iff mult_not_zero)
  } note b_0 = this
  obtain actual_d where "actual_d = (a/b) - 1" by simp
  then have actual_d_def: "b\<noteq>0 \<Longrightarrow> a = (1+actual_d)*b" by simp
  then have "b\<noteq>0 \<Longrightarrow> a-b=b*actual_d" by algebra
  then have "b\<noteq>0 \<Longrightarrow> \<bar>a-b\<bar>=\<bar>b*actual_d\<bar>" by presburger
  then have "b\<noteq>0 \<Longrightarrow> \<bar>a-b\<bar>=\<bar>b\<bar>*\<bar>actual_d\<bar>"
    by (metis abs_mult)
  with assms have "\<bar>b\<bar>*\<bar>actual_d\<bar> \<le> \<bar>b\<bar>*f" by fastforce
  then have "b\<noteq>0 \<Longrightarrow> \<bar>actual_d\<bar> \<le> f" by force
  then have "b\<noteq>0 \<Longrightarrow> \<exists>(d::real). (a = (1+d)*b \<and> \<bar>d\<bar>\<le> f)" using actual_d_def by blast
  with b_0 show ?thesis by blast
qed

lemma rel_accuracy_to_factor:
  assumes "rel_accuracy a (c::('e, 'f) float) u"
  and "u \<ge> 0"
shows "\<exists>(d::real). (a = (1+d)*valof c \<and> \<bar>d\<bar>\<le> u / (2::real) ^ LENGTH('f))"
  using assms unfolding rel_accuracy_def
proof -
  from assms have "0 \<le>  u / (2::real) ^ LENGTH('f)" by force
  with rel_accuracy_to_factor_helper have 
"(\<bar>valof c - a\<bar> \<le> \<bar>valof c\<bar> * (u / (2::real) ^ LENGTH('f))) \<Longrightarrow>
    \<exists>d. (a = ((1::real) + d) * valof c \<and> \<bar>d\<bar> \<le> u / (2::real) ^ LENGTH('f))" by simp
  moreover from  rel_accuracy_def assms have "\<bar>valof c - a\<bar> \<le> \<bar>valof c\<bar> * (u / (2::real) ^ LENGTH('f))" by auto
  ultimately show ?thesis by blast
qed

lemma factor_to_rel_accuracy:
  assumes "\<exists>(d::real). (a = (1+d)*valof c \<and> \<bar>d\<bar>\<le> u / (2::real) ^ LENGTH('f))"
  shows " is_finite c \<Longrightarrow> rel_accuracy a (c::('e, 'f) float) u"
proof - 
  from assms obtain d where d_def: "(a = (1+d)*valof c \<and> \<bar>d\<bar>\<le> u / (2::real) ^ LENGTH('f))" by blast
  then have "a-valof c = d*valof c" by argo
  then have "\<bar>valof c - a\<bar> = \<bar>valof c\<bar> * \<bar>d\<bar>"
    by (simp add: abs_minus_commute abs_mult)
  with d_def mult_left_mono have "\<bar>valof c - a\<bar> \<le> \<bar>valof c\<bar> * u / (2::real) ^ LENGTH('f)" by fastforce
  with rel_accuracy_def show "is_finite c \<Longrightarrow> rel_accuracy a (c::('e, 'f) float) u" by blast
qed

lemma rel_accuracy_increase:
  assumes "rel_accuracy a (c::('e,'f) float) u"
   and "u \<ge> 0"
  shows "rel_accuracy ((1+d)*a) c (u+\<bar>u*d\<bar>+\<bar>d\<bar>*(2::real) ^ LENGTH('f))"
  using assms unfolding rel_accuracy_def apply simp
proof -
  from assms rel_accuracy_to_factor obtain d2 where "(a = (1+d2)*valof c \<and> \<bar>d2\<bar>\<le> u / (2::real) ^ LENGTH('f))" by blast
  then have "(1+d)*a - valof c = (d+d2 + d*d2)*valof c" by algebra
  then have "\<bar>valof c - ((1+d)*a)\<bar> = \<bar>(d+d2 + d*d2)*valof c\<bar>" by simp
  oops

end