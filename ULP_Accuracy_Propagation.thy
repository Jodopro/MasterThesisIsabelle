theory ULP_Accuracy_Propagation
imports Rel_Accuracy
begin

lemma eq_implies_valof_eq:
  assumes "a = b"
  shows "valof a = valof b"
  using assms by simp

lemma valof_same_ulp_accuracy_same:
  assumes "valof (a::('e,'f) float) = valof (b::('e,'f) float)"
  shows "ulp_accuracy r a e = ulp_accuracy r b e"
  unfolding ulp_accuracy_def
proof -
  from abs_valof_e_exp_e ulp_equivelance assms have "ulp a = ulp b" by metis
  with assms have "(\<bar>valof a - r\<bar> \<le> e * ulp a) = (\<bar>valof b - r\<bar> \<le> e * ulp b)" by presburger
  moreover from assms abs_valof_e_exp_e eq_exp_eq_finite have "is_finite a = is_finite b" by metis
  ultimately show " (is_finite a \<and> \<bar>valof a - r\<bar> \<le> e * ulp a) = (is_finite b \<and> \<bar>valof b - r\<bar> \<le> e * ulp b)" by presburger
qed

context 
  fixes a_float b_float c_float::"('e, 'f)float"
    and a_real b_real c_real::"real"
    and a_accuracy b_accuracy c_accuracy::"real"
  assumes a_rel:"ulp_accuracy a_real a_float a_accuracy"
      and b_rel:"ulp_accuracy b_real b_float b_accuracy"
      and c_rel:"ulp_accuracy c_real c_float c_accuracy"
      and len_e: "1 < LENGTH('e)"
      and len_f: "1 < LENGTH('f)"
      and sign_a: "sign a_float = 0"
      and sign_b: "sign b_float = 0"
      and sign_c: "sign c_float = 0"
begin

lemmas context_assumptions = a_rel b_rel c_rel len_e len_f sign_a sign_b sign_c

lemma addition_error_propagation_distance:
  assumes "\<bar>valof a_float + valof b_float\<bar> < threshold TYPE(('e, 'f) float)"
  shows "\<bar>(valof a_float + valof b_float) - (a_real+b_real)\<bar> \<le> (a_accuracy+b_accuracy) * ulp (fadd To_nearest a_float b_float)"
proof -
  have step_1: "valof (fadd To_nearest a_float b_float) = valof (
                 round To_nearest (valof a_float + valof b_float)::('e,'f) float)" 
    apply(simp add:fadd_def valof_zerosign del:round.simps)
    using assms context_assumptions ulp_accuracy_def float_distinct_finite by blast
  moreover obtain rounded_sum where rounded_sum_def: "rounded_sum = (round To_nearest (valof a_float + valof b_float)::('e,'f) float)" by blast 
  ultimately have ulp_same: "ulp (fadd To_nearest a_float b_float) = ulp rounded_sum" using abs_valof_e_exp_e ulp_equivelance by metis 
  from assms context_assumptions ulp_accuracy_def have finite_a_b: "is_finite a_float \<and> is_finite b_float" by blast
  with addition_rounding_increases valof_nonneg assms context_assumptions rounded_sum_def have "valof a_float \<le> valof rounded_sum \<and> valof b_float \<le> valof rounded_sum"
    by (metis add.commute)
  with valof_nonneg assms context_assumptions abs_of_nonneg have "\<bar>valof a_float\<bar> \<le> \<bar>valof rounded_sum\<bar> \<and> \<bar>valof b_float\<bar> \<le> \<bar>valof rounded_sum\<bar>"
    by (smt (verit, del_insts))
  with abs_valof_ge_exp_ge exp_ge_ulp_ge assms context_assumptions ulp_accuracy_non_negative have 
    "a_accuracy * ulp a_float \<le> a_accuracy * ulp rounded_sum \<and> b_accuracy * ulp b_float \<le> b_accuracy * ulp rounded_sum"
    using mult_left_mono by metis
  moreover from assms context_assumptions ulp_accuracy_def have "\<bar>valof a_float - a_real\<bar> \<le> a_accuracy * ulp a_float \<and> \<bar>valof b_float - b_real\<bar> \<le> b_accuracy * ulp b_float" by fast
  ultimately have rounded_sum_dist: "\<bar>(valof a_float + valof b_float) - (a_real+b_real)\<bar> \<le> (a_accuracy+b_accuracy) * ulp rounded_sum" by argo
  with ulp_same show ?thesis by presburger
qed


lemma addition_error_propagation_ulp_accuracy:
  assumes "\<bar>valof a_float + valof b_float\<bar> < threshold TYPE(('e, 'f) float)"
  shows "ulp_accuracy (a_real + b_real) (fadd To_nearest a_float b_float) (a_accuracy + b_accuracy + 0.5)"
proof -
  have step_1: "valof (fadd To_nearest a_float b_float) = valof (
                 round To_nearest (valof a_float + valof b_float)::('e,'f) float)" 
    apply(simp add:fadd_def valof_zerosign del:round.simps)
    using assms context_assumptions ulp_accuracy_def float_distinct_finite by blast
  moreover obtain rounded_sum where rounded_sum_def: "rounded_sum = (round To_nearest (valof a_float + valof b_float)::('e,'f) float)" by blast 
  ultimately have ulp_accuracy_same: "ulp_accuracy (a_real + b_real) (fadd To_nearest a_float b_float) (a_accuracy + b_accuracy + 0.5) =
    ulp_accuracy (a_real + b_real) rounded_sum (a_accuracy + b_accuracy + 0.5)" using valof_same_ulp_accuracy_same by blast 
  from step_1 rounded_sum_def have ulp_same: "ulp (fadd To_nearest a_float b_float) = ulp rounded_sum" using abs_valof_e_exp_e exp_e_ulp_e by metis
  
  with assms addition_error_propagation_distance have "\<bar>(valof a_float + valof b_float) - (a_real+b_real)\<bar> \<le> (a_accuracy+b_accuracy) * ulp rounded_sum" by metis
  moreover from rounding_0_5_ulp ulp_accuracy_def assms context_assumptions rounded_sum_def have "\<bar>valof rounded_sum - (valof a_float + valof b_float)\<bar> \<le> 0.5 * ulp rounded_sum" by fast
  ultimately have rounded_sum_dist: "\<bar>valof rounded_sum - (a_real+b_real)\<bar> \<le> (0.5+a_accuracy+b_accuracy) * ulp rounded_sum" by argo

  from is_finite_closest have "is_finite (closest valof (\<lambda>a::('e, 'f) float. even (fraction a)) (Collect is_finite) (valof a_float + valof b_float))" by blast
  with rounded_sum_def assms have "is_finite rounded_sum" by fastforce
  with rounded_sum_dist have "ulp_accuracy (a_real + b_real) rounded_sum (a_accuracy + b_accuracy + 0.5)"
    apply(simp add:ulp_accuracy_def) by argo
  with ulp_accuracy_same show ?thesis by fast
qed

lemma exp_0_valof_le_1:
  assumes "exponent (a::('e,'f) float) = 0"
shows "\<bar>valof a\<bar> \<le> 1"
  using abs_valof_max[where x="a"] apply(simp add:bias_def assms)
  subgoal proof -
    have "\<forall>e. (2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) - Suc (0::nat)) \<le> (2::real) ^ ((2::nat) ^ (Suc e - Suc (0::nat)) - Suc (0::nat))" 
      using diff_le_mono by auto
    then have e_ge: "\<forall>e. (2::real) /(2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) - Suc (0::nat)) \<ge> (2::real) /(2::real) ^ ((2::nat) ^ (Suc e - Suc (0::nat)) - Suc (0::nat))"
      by (simp add: frac_le)
    show "\<bar>valof a\<bar> < (2::real) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) - Suc (0::nat)) \<Longrightarrow>
    \<bar>valof a\<bar> \<le> (1::real)" apply(induction "LENGTH('e)") apply auto using e_ge 
      by (smt (verit) One_nat_def context_assumptions(4) divide_le_eq_1_pos less_2_cases_iff one_less_power self_le_power zero_less_diff)
  qed done

lemma multiplication_error_propagation1_distance_general:
  assumes "ulp_accuracy a_r (a_f::('e,'f) float) a_a"
  and "ulp_accuracy b_r (b_f::('e,'f) float) b_a"
  and "exponent a_f \<noteq> 0"
  and "exponent b_f = 0"
  and "a_r \<le> 1"
  and "a_r \<ge> 0"
  and "sign a_f = 0" and "sign b_f = 0"
  and "\<bar>valof a_f * valof b_f\<bar> < threshold TYPE(('e, 'f) float)"
shows "\<bar>(valof a_f * valof b_f) - (a_r*b_r)\<bar> \<le> (2*a_a+b_a) * ulp (fmul To_nearest a_f b_f)"
proof -
  from assms context_assumptions ulp_accuracy_to_rel_accuracy have "rel_accuracy a_r a_f a_a" by blast
  then have "\<exists>(d::real). (a_r = (1+d)*valof a_f \<and> \<bar>d\<bar>\<le> a_a / (2::real) ^ LENGTH('f))" using rel_accuracy_to_factor assms context_assumptions ulp_accuracy_non_negative by blast
  then obtain d1 where d1_def: "a_r = (1+d1)*valof a_f \<and> \<bar>d1\<bar>\<le> a_a / (2::real) ^ LENGTH('f)" by presburger
  from assms context_assumptions ulp_accuracy_def have "\<bar>valof b_f - b_r\<bar> \<le> b_a * ulp b_f" by blast
  then have "\<exists>d. (b_r = valof b_f + d \<and> \<bar>d\<bar> \<le> b_a * ulp b_f)"
    by (metis abs_minus_commute add_diff_cancel_left' add_diff_eq)
  then obtain d2 where d2_def: "b_r = valof b_f + d2 \<and> \<bar>d2\<bar> \<le> b_a * ulp b_f" by blast
  then have "a_r*b_r=a_r*valof b_f + a_r*d2" by algebra
  then have "a_r*b_r \<le> a_r*valof b_f + \<bar>a_r*d2\<bar> \<and> a_r*valof b_f - \<bar>a_r*d2\<bar> \<le> a_r*b_r" by argo
  moreover from assms have "\<bar>a_r*d2\<bar> \<le> \<bar>d2\<bar>"
    by (metis abs_mult_pos' abs_not_less_zero mult_le_cancel_right2)
  ultimately have "a_r*b_r \<le> a_r*valof b_f + \<bar>d2\<bar> \<and> a_r*valof b_f - \<bar>d2\<bar> \<le> a_r*b_r" by argo
  with d1_def have "a_r*b_r - \<bar>d2\<bar> \<le> (1+d1)*valof a_f*valof b_f \<and> (1+d1)*valof a_f*valof b_f \<le> a_r*b_r + \<bar>d2\<bar>" by simp
  then have ge_le: "a_r*b_r - \<bar>d2\<bar> - \<bar>d1*valof a_f*valof b_f\<bar> \<le> valof a_f*valof b_f \<and> valof a_f*valof b_f \<le> a_r*b_r + \<bar>d2\<bar> + \<bar>d1*valof a_f*valof b_f\<bar>" by argo

  obtain rounded_mul where rounded_mul_def: "rounded_mul = (round To_nearest (valof a_f * valof b_f)::('e,'f) float)" by blast 
  with rounding_0_5_ulp ulp_accuracy_def assms context_assumptions have rounded_mul_d: "\<bar>valof rounded_mul - (valof a_f * valof b_f)\<bar> \<le> 0.5 * ulp rounded_mul" by fast  
  moreover from is_finite_closest rounded_mul_def assms have fin_rounded_mul: "is_finite rounded_mul" by auto
  ultimately have "ulp_accuracy (valof a_f * valof b_f) rounded_mul 0.5" using ulp_accuracy_def by blast
   have step_1: "valof (fmul To_nearest a_f b_f) = valof (
                 round To_nearest (valof a_f * valof b_f)::('e,'f) float)" 
    apply(simp add:fmul_def valof_zerosign del:round.simps)
    using assms context_assumptions ulp_accuracy_def float_distinct_finite by blast
  with rounded_mul_def have ulp_same: "ulp (fmul To_nearest a_f b_f) = ulp rounded_mul" using abs_valof_e_exp_e exp_e_ulp_e by metis
  
  from rounding_bounds rounded_mul_def fin_rounded_mul have "\<bar>valof a_f*valof b_f\<bar>
    \<le> (2::real) * (2::real) ^ exponent rounded_mul /
      (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat))"
    by fastforce
  moreover have "(2::real) * (2::real) ^ exponent rounded_mul \<le> (2::real) * (2::real) ^ (max (exponent rounded_mul) 1)" by force
  ultimately have  "\<bar>valof a_f*valof b_f\<bar>
    \<le> (2::real) * (2::real) ^ (max (exponent rounded_mul) 1) /
      (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat))"
    by (smt (verit) divide_right_mono zero_le_power)
  moreover from assms context_assumptions ulp_accuracy_non_negative have "a_a / (2::real) ^ LENGTH('f) \<ge> 0" by fastforce
  ultimately have "(a_a / (2::real) ^ LENGTH('f)) * \<bar>valof a_f*valof b_f\<bar>
    \<le> (a_a / (2::real) ^ LENGTH('f)) * (2::real) * (2::real) ^ (max (exponent rounded_mul) 1) /
      (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat))" 
    using mult_left_mono[where a="\<bar>valof a_f*valof b_f\<bar>" and b="(2::real) * (2::real) ^ (max (exponent rounded_mul) 1) /
      (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat))" and c="a_a / (2::real) ^ LENGTH('f)"] by auto
  with d1_def have "\<bar>d1\<bar> * \<bar>valof a_f*valof b_f\<bar>
    \<le> (a_a / (2::real) ^ LENGTH('f)) * (2::real) * (2::real) ^ (max (exponent rounded_mul) 1) /
      (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat))" using mult_left_mono[where a="\<bar>d1\<bar>" and b="a_a / (2::real) ^ LENGTH('f)" and  c="\<bar>valof a_f*valof b_f\<bar>"] by argo
  then have "\<bar>d1\<bar> * \<bar>valof a_f*valof b_f\<bar>
    \<le> a_a  * (2::real) * (2::real) ^ (max (exponent rounded_mul) 1) /
      ((2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat)) * (2::real) ^ LENGTH('f))" by argo
  then have "\<bar>d1\<bar> * \<bar>valof a_f*valof b_f\<bar>
    \<le> a_a  * (2::real) * (2::real) ^ (max (exponent rounded_mul) 1) /
      (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) +  LENGTH('f))" by(simp add:  ulp_divisor_rewrite)
  then have a_acc_to_ulp: "\<bar>d1 * valof a_f*valof b_f\<bar>
    \<le> a_a  * (2::real) * ulp rounded_mul" by(simp add:ulp_equivelance abs_mult )

  from assms have "exponent b_f \<le> exponent rounded_mul" by linarith
  then have "ulp b_f \<le> ulp rounded_mul" by(simp add:exp_ge_ulp_ge) 
  with assms context_assumptions ulp_accuracy_non_negative d2_def have  b_acc_to_ulp:  "\<bar>d2\<bar> \<le> b_a * ulp rounded_mul"
    by (metis dual_order.trans ordered_comm_semiring_class.comm_mult_left_mono)

  from  a_acc_to_ulp  b_acc_to_ulp ge_le have "a_r*b_r - ((2::real)*a_a+b_a) * ulp rounded_mul \<le> valof a_f*valof b_f \<and> valof a_f*valof b_f \<le> a_r*b_r + (2*a_a+b_a) * ulp rounded_mul" by argo
  then have rounded_mul_dist: "\<bar>valof a_f*valof b_f - a_r*b_r\<bar> \<le> ((2::real)*a_a+b_a) * ulp rounded_mul" by force
  from is_finite_closest have "is_finite (closest valof (\<lambda>a::('e, 'f) float. even (fraction a)) (Collect is_finite) (valof a_f + valof b_f))" by blast
  with ulp_same fin_rounded_mul rounded_mul_dist show ?thesis by presburger
qed

lemma multiplication_error_propagation1_distance_1:
  assumes "exponent a_float \<noteq> 0"
  and "exponent b_float = 0"
  and "a_real \<le> 1"
  and "a_real \<ge> 0"
  and "\<bar>valof a_float * valof b_float\<bar> < threshold TYPE(('e, 'f) float)"
shows "\<bar>(valof a_float * valof b_float) - (a_real*b_real)\<bar> \<le> (2*a_accuracy+b_accuracy) * ulp (fmul To_nearest a_float b_float)"
  using multiplication_error_propagation1_distance_general assms context_assumptions by blast

lemma multiplication_error_propagation1_distance_2:
  assumes "exponent b_float \<noteq> 0"
  and "exponent a_float = 0"
  and "b_real \<le> 1"
  and "b_real \<ge> 0"
  and "\<bar>valof a_float * valof b_float\<bar> < threshold TYPE(('e, 'f) float)"
shows "\<bar>(valof a_float * valof b_float) - (a_real*b_real)\<bar> \<le> (a_accuracy+2*b_accuracy) * ulp (fmul To_nearest a_float b_float)"
proof -
  from assms(5) have a_5: "\<bar>valof b_float * valof a_float\<bar> < threshold TYPE(('e, 'f) float)" by argo
  have "fmul To_nearest a_float b_float = fmul To_nearest b_float a_float" apply(simp add:fmul_def) by argo
  with multiplication_error_propagation1_distance_general[where a_f=b_float and b_f=a_float and a_r=b_real and b_r=a_real and a_a=b_accuracy and b_a=a_accuracy, OF b_rel a_rel assms(1) assms(2) assms(3) assms(4) sign_b sign_a a_5]
  show ?thesis apply simp by argo
qed

lemma multiplication_error_propagation2_distance_general:
  assumes "exponent a_f = 0"
  and "exponent b_f = 0"
  and "a_r \<le> 1"
  and "a_r \<ge> 0"
  and a_rel: "ulp_accuracy a_r (a_f::('e, 'f) float) a_a"
  and b_rel: "ulp_accuracy b_r (b_f::('e, 'f) float) b_a"
  and "sign a_f = 0"
  and "sign b_f = 0"
  and "\<bar>valof a_f * valof b_f\<bar> < threshold TYPE(('e, 'f) float)"
shows "\<bar>(valof a_f * valof b_f) - (a_r*b_r)\<bar> \<le> (a_a+b_a) * ulp (fmul To_nearest a_f b_f)"
proof -
  from a_rel ulp_accuracy_def have "\<exists>d. (a_r = valof a_f + d \<and> \<bar>d\<bar> \<le> a_a * ulp a_f)"
    by (metis abs_minus_commute add.commute diff_add_cancel)
  then obtain d1 where d1_def: "a_r = valof a_f + d1 \<and> \<bar>d1\<bar> \<le> a_a * ulp a_f" by blast
  from b_rel ulp_accuracy_def have "\<exists>d. (b_r = valof b_f + d \<and> \<bar>d\<bar> \<le> b_a * ulp b_f)"
    by (metis abs_minus_commute add.commute diff_add_cancel)
  then obtain d2 where d2_def: "b_r = valof b_f + d2 \<and> \<bar>d2\<bar> \<le> b_a * ulp b_f" by blast
  then have "a_r*b_r = a_r*valof b_f + a_r*d2" by algebra
  with assms have "a_r*b_r - \<bar>d2\<bar> \<le> a_r*valof b_f \<and> a_r*valof b_f \<le> a_r*b_r + \<bar>d2\<bar>"
    by (smt (verit) d2_def mult_cancel_right1 mult_le_cancel_right2 mult_left_less_imp_less mult_nonneg_nonpos)
  with d1_def have "a_r*b_r - \<bar>d2\<bar> \<le>valof a_f*valof b_f + d1*valof b_f \<and> valof a_f*valof b_f + d1*valof b_f\<le> a_r*b_r + \<bar>d2\<bar>" by (metis (no_types, opaque_lifting) distrib_right)
  moreover from assms exp_0_valof_le_1 have "\<bar>d1\<bar>*valof b_f \<le>\<bar>d1\<bar>"
    by (smt (verit, ccfv_SIG) mult_less_cancel_left mult_less_cancel_left1)
  moreover with valof_nonneg assms context_assumptions have "\<bar>d1*valof b_f\<bar> \<le>\<bar>d1\<bar>" by (metis abs_mult_pos)
  ultimately have p1: "a_r*b_r - \<bar>d2\<bar> - \<bar>d1\<bar> \<le>valof a_f*valof b_f \<and> valof a_f*valof b_f\<le> a_r*b_r + \<bar>d2\<bar> + \<bar>d1\<bar>" by argo


  obtain rounded_mul where rounded_mul_def: "rounded_mul = (round To_nearest (valof a_f * valof b_f)::('e,'f) float)" by blast 
  with rounding_0_5_ulp ulp_accuracy_def assms context_assumptions have rounded_mul_d: "\<bar>valof rounded_mul - (valof a_f * valof b_f)\<bar> \<le> 0.5 * ulp rounded_mul" by fast  
  moreover from is_finite_closest rounded_mul_def assms have fin_rounded_mul: "is_finite rounded_mul" by auto
  ultimately have "ulp_accuracy (valof a_f * valof b_f) rounded_mul 0.5" using ulp_accuracy_def by blast
  have step_1: "valof (fmul To_nearest a_f b_f) = valof (
                 round To_nearest (valof a_f * valof b_f)::('e,'f) float)" 
    apply(simp add:fmul_def valof_zerosign del:round.simps)
    using assms ulp_accuracy_def float_distinct_finite len_e len_f by blast
  with rounded_mul_def have ulp_same: "ulp (fmul To_nearest a_f b_f) = ulp rounded_mul" using abs_valof_e_exp_e exp_e_ulp_e by metis
  
  
  from assms have "ulp b_f \<le> ulp rounded_mul" by(simp add:exp_ge_ulp_ge)
  with assms context_assumptions ulp_accuracy_non_negative d2_def have  b_acc_to_ulp:  "\<bar>d2\<bar> \<le> b_a * ulp rounded_mul"
    by (metis dual_order.trans ordered_comm_semiring_class.comm_mult_left_mono)
  from assms have "ulp a_f \<le> ulp rounded_mul" by(simp add:exp_ge_ulp_ge)
  with assms context_assumptions ulp_accuracy_non_negative d1_def have a_acc_to_ulp:  "\<bar>d1\<bar> \<le> a_a * ulp rounded_mul"
    by (metis dual_order.trans ordered_comm_semiring_class.comm_mult_left_mono)
  from p1 a_acc_to_ulp b_acc_to_ulp have "a_r*b_r - (a_a+b_a) * ulp rounded_mul  \<le>valof a_f*valof b_f \<and> valof a_f*valof b_f\<le> a_r*b_r + (a_a+b_a) * ulp rounded_mul" by argo
  then have rounded_mul_dist:"\<bar>valof a_f*valof b_f - a_r*b_r\<bar> \<le> (a_a+b_a) * ulp rounded_mul" by force
  from is_finite_closest have "is_finite (closest valof (\<lambda>a::('e, 'f) float. even (fraction a)) (Collect is_finite) (valof a_f + valof b_f))" by blast
  with ulp_same fin_rounded_mul rounded_mul_dist show ?thesis by presburger
qed

lemma multiplication_error_propagation2_distance_1:
  assumes "exponent a_float = 0"
  and "exponent b_float = 0"
  and "a_real \<le> 1"
  and "a_real \<ge> 0"
  and "\<bar>valof a_float * valof b_float\<bar> < threshold TYPE(('e, 'f) float)"
shows "\<bar>(valof a_float * valof b_float) - (a_real*b_real)\<bar> \<le> (a_accuracy+b_accuracy) * ulp (fmul To_nearest a_float b_float)"
  using assms context_assumptions multiplication_error_propagation2_distance_general by blast

lemma multiplication_error_propagation2_distance_2:
  assumes "exponent a_float = 0"
  and "exponent b_float = 0"
  and "b_real \<le> 1"
  and "b_real \<ge> 0"
  and "\<bar>valof a_float * valof b_float\<bar> < threshold TYPE(('e, 'f) float)"
shows "\<bar>(valof a_float * valof b_float) - (a_real*b_real)\<bar> \<le> (a_accuracy+b_accuracy) * ulp (fmul To_nearest a_float b_float)"
proof -
  from assms(5) have a_5: "\<bar>valof b_float * valof a_float\<bar> < threshold TYPE(('e, 'f) float)" by argo
  have "fmul To_nearest a_float b_float = fmul To_nearest b_float a_float" apply(simp add:fmul_def) by argo
  with multiplication_error_propagation2_distance_general[where a_f=b_float and b_f=a_float and a_r=b_real and b_r=a_real and a_a=b_accuracy and b_a=a_accuracy, OF assms(2) assms(1) assms(3) assms(4) b_rel a_rel sign_b sign_a a_5]
  show ?thesis apply simp by argo
qed

lemma multiplication_exp_rounded_mul:
  assumes "exponent (a::('e,'f) float) \<noteq> 0"
      and "exponent (b::('e,'f) float) \<noteq> 0"
      and rounded_mul_def: "rounded_mul = (round To_nearest (valof a * valof b)::('e,'f) float)"
      and threshold_assm: "\<bar>valof a * valof b\<bar> < threshold TYPE(('e, 'f) float)"
    shows "(2::real)^(max (exponent rounded_mul) 1) \<ge> (2::real) ^ (exponent a + exponent b) / (2::real) ^ bias TYPE(('e, 'f) float)"
proof -
  have step1: "\<bar>valof a * valof b\<bar> = \<bar>valof a\<bar> * \<bar>valof b\<bar>" using abs_mult by blast
  from assms abs_valof_min have a_l: "(2::real) ^ exponent a / (2::real) ^ bias TYPE(('e, 'f) float) \<le> \<bar>valof a\<bar>" by (smt (verit, best))
  then have step2: "\<bar>valof a\<bar> * \<bar>valof b\<bar> \<ge> (2::real) ^ exponent a / (2::real) ^ bias TYPE(('e, 'f) float) * \<bar>valof b\<bar>" using mult_right_mono by fastforce 
  from assms abs_valof_min have "\<bar>valof b\<bar> \<ge> (2::real) ^ exponent b / (2::real) ^ bias TYPE(('e, 'f) float)" by (smt (verit, best))
  moreover have "0<(2::real) ^ exponent a / (2::real) ^ bias TYPE(('e, 'f) float)" using a_l zero_val_exponent assms by force
  ultimately have "(2::real) ^ exponent a / (2::real) ^ bias TYPE(('e, 'f) float) * \<bar>valof b\<bar> \<ge>
      (2::real) ^ exponent a / (2::real) ^ bias TYPE(('e, 'f) float) *
      (2::real) ^ exponent b / (2::real) ^ bias TYPE(('e, 'f) float)" 
    using mult_le_cancel_left_pos[where 
         a="\<bar>valof b\<bar>" and
         b="(2::real) ^ exponent b / (2::real) ^ bias TYPE(('e, 'f) float)" and
         c="(2::real) ^ exponent a / (2::real) ^ bias TYPE(('e, 'f) float)"
      ] by auto
  with step1 step2 have lower_bound: "\<bar>valof a * valof b\<bar>\<ge> (2::real) ^ exponent a / (2::real) ^ bias TYPE(('e, 'f) float) *
      (2::real) ^ exponent b / (2::real) ^ bias TYPE(('e, 'f) float)"
    by argo
  moreover from rounding_bounds rounded_mul_def rounded_threshold_is_finite[OF threshold_assm] have "\<bar>valof a * valof b\<bar> < 2*2^exponent rounded_mul / 2^(2 ^ (LENGTH('e) - 1) - 1)" by blast
  ultimately have "(2::real) ^ exponent a / (2::real) ^ bias TYPE(('e, 'f) float) *
      (2::real) ^ exponent b / (2::real) ^ bias TYPE(('e, 'f) float) < 2*2^exponent rounded_mul / 2^(2 ^ (LENGTH('e) - 1) - 1)" by argo
  with bias_def have "(2::real) ^ exponent a / (2::real) ^ bias TYPE(('e, 'f) float) *
      (2::real) ^ exponent b < 2*2^exponent rounded_mul"
    by (smt (verit) divide_less_cancel zero_less_power)
  then have something_div_2: "(2::real) ^ (exponent a + exponent b) / (2::real) ^ bias TYPE(('e, 'f) float) / 2 
    < 2^exponent rounded_mul"
    by (simp add: power_add)
  from assms have "exponent a + exponent b > 1" by simp
  then have "(2::real) ^ (exponent a + exponent b) / (2::nat) ^ 1 = (2::real) ^ (exponent a + exponent b - 1)" 
    using power_diff[where n="1" and m="exponent a + exponent b" and a="(2::real)"] by auto
  with something_div_2 have "(2::real) ^ (exponent a + exponent b - 1) / (2::real) ^ bias TYPE(('e, 'f) float) 
    < (2::real)^exponent rounded_mul" by simp
  moreover have "(2::real)^exponent rounded_mul \<le> (2::real)^(max (exponent rounded_mul) 1)" by fastforce
  ultimately have "(2::real)^(max (exponent rounded_mul) 1) > (2::real) ^ (exponent a + exponent b - 1) / (2::real) ^ bias TYPE(('e, 'f) float)" by argo
  then have "(2::real)^((max (exponent rounded_mul) 1) + (bias TYPE(('e, 'f) float))) > (2::real) ^ (exponent a + exponent b - 1)"
    by (simp add:power_add pos_divide_less_eq)
  then have "(2::real)^((max (exponent rounded_mul) 1) + (bias TYPE(('e, 'f) float))) \<ge> (2::real) ^ (exponent a + exponent b)" 
    by simp
  then show ?thesis  by(simp add:power_add divide_le_eq)
qed


lemma multiplication_error_propagation3_case1_helper_general:
  assumes case1: "exponent (rounded_mul::('e, 'f) float) + bias TYPE(('e, 'f) float) \<ge> exponent (a::('e, 'f) float) + exponent (b::('e, 'f) float) + (n::nat)"
  and "exponent a \<noteq> 0"
  and "exponent b \<noteq> 0"
  and d1_def: "\<bar>d1\<bar> \<le> a_a * ulp a"
shows "\<bar>valof b * d1\<bar> \<le> 
          ((1::real) + real (fraction b) / (2::real) ^ LENGTH('f)) * a_a * ulp rounded_mul / (2::real)^n"
proof -
  from d1_def have "\<bar>valof b * d1\<bar> \<le> \<bar>valof b\<bar> * a_a * ulp a" apply(simp add:abs_mult ) using mult_le_cancel_left[where c="\<bar>valof b\<bar>"] by force
  with assms have"\<bar>valof b * d1\<bar> \<le> (2::real) ^ exponent b / (2::real) ^ bias TYPE(('e, 'f) float) *
          ((1::real) + real (fraction b) / (2::real) ^ LENGTH('f)) * a_a * (2::real) ^ exponent a /
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" by(simp add:abs_valof_eq ulp_equivelance)
  then have step1:  "\<bar>valof b * d1\<bar> \<le> (2::real) ^ exponent b * (2::real) ^ exponent a / (2::real) ^ bias TYPE(('e, 'f) float) *
          ((1::real) + real (fraction b) / (2::real) ^ LENGTH('f)) * a_a /
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" by argo

  from case1 have "(2::real) ^ exponent rounded_mul * (2::real) ^ bias TYPE(('e, 'f) float) \<ge> (2::real) ^ exponent a * (2::real) ^ exponent b * (2::real)^n" using power_add
    by (metis exp_less)
  then have "(2::real) ^ exponent rounded_mul * (2::real) ^ bias TYPE(('e, 'f) float) / (2::real)^n \<ge> (2::real) ^ exponent a * (2::real) ^ exponent b"
    using mult_imp_div_pos_le[where y="(2::real)^n" and z="(2::real) ^ exponent rounded_mul * (2::real) ^ bias TYPE(('e, 'f) float)" and x="(2::real) ^ exponent a * (2::real) ^ exponent b"]
    by (simp add: le_divide_eq)
  then have "(2::real) ^ exponent rounded_mul / (2::real)^n * (2::real) ^ bias TYPE(('e, 'f) float) \<ge> (2::real) ^ exponent a * (2::real) ^ exponent b" by argo
  then have step1_5: "(2::real) ^ exponent rounded_mul / (2::real)^n \<ge> (2::real) ^ exponent b * (2::real) ^ exponent a / (2::real) ^ bias TYPE(('e, 'f) float)" 
    using mult_imp_div_pos_le[where z="(2::real) ^ exponent rounded_mul / (2::real)^n" and y="(2::real) ^ bias TYPE(('e, 'f) float)" and x="(2::real) ^ exponent b * (2::real) ^ exponent a"]
    by (simp add: mult.commute)
  have "0 \<le> (1::real) + real (fraction b) / (2::real) ^ LENGTH('f)" by simp
  moreover from ulp_positive assms have "0 \<le> a_a"
    by (metis abs_not_less_zero linorder_le_less_linear mult_pos_neg2 order_le_less_trans)
  ultimately have step1_75: "0 \<le> ((1::real) + real (fraction b) / (2::real) ^ LENGTH('f)) * a_a  / 
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" by simp

  with step1 have step2: "\<bar>valof b * d1\<bar> \<le> (2::real) ^ exponent rounded_mul / (2::real)^n*
          (((1::real) + real (fraction b) / (2::real) ^ LENGTH('f)) * a_a /
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f)))"
    using mult_right_mono[where c="((1::real) + real (fraction b) / (2::real) ^ LENGTH('f)) * a_a  / 
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" and b="(2::real) ^ exponent rounded_mul / (2::real)^n" and a="(2::real) ^ exponent a * (2::real) ^ exponent b/
    (2::real) ^ bias TYPE(('e, 'f) float)"] step1_5 by argo

  have "(2::real) ^ exponent rounded_mul > 0" by simp
  then have "1 / (2::real)^n* ((1::real) + real (fraction b) / (2::real) ^ LENGTH('f)) * a_a /
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f)) < 0 \<Longrightarrow> 
    0 > (2::real) ^ exponent rounded_mul / (2::real)^n*
          ((1::real) + real (fraction b) / (2::real) ^ LENGTH('f)) * a_a /
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" using mult_pos_neg[where a="(2::real) ^ exponent rounded_mul" and b="1/(2::real)^n* ((1::real) + real (fraction b) / (2::real) ^ LENGTH('f)) * a_a /
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))"] by argo
    with step2 have "0 \<le> 1/(2::real)^n*((1::real) + real (fraction b) / (2::real) ^ LENGTH('f)) * a_a /
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" by argo
    moreover have "(2::real) ^ exponent rounded_mul \<le> (2::real) ^ (max (exponent rounded_mul) (1::nat))" by simp
    ultimately have "(2::real) ^ exponent rounded_mul / 
          (2::real)^n*((1::real) + real (fraction b) / (2::real) ^ LENGTH('f)) * a_a /
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f)) \<le> (2::real) ^ (max (exponent rounded_mul) (1::nat)) /
          (2::real)^n*((1::real) + real (fraction b) / (2::real) ^ LENGTH('f)) * a_a /
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" 
      using mult_right_mono[where a="(2::real) ^ exponent rounded_mul" and b="(2::real) ^ (max (exponent rounded_mul) (1::nat))"
            and c="1/(2::real)^n*((1::real) + real (fraction b) / (2::real) ^ LENGTH('f)) * a_a /
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))"] by simp
    with step2 have "\<bar>valof b * d1\<bar> \<le> 
          1/(2::real)^n*((1::real) + real (fraction b) / (2::real) ^ LENGTH('f)) * a_a * (2::real) ^ (max (exponent rounded_mul) (1::nat)) /
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" by argo
    then have "\<bar>valof b * d1\<bar> \<le> 
          1/(2::real)^n*((1::real) + real (fraction b) / (2::real) ^ LENGTH('f)) * a_a * ulp rounded_mul" by(simp add: ulp_equivelance)
    then show ?thesis by argo
  qed

lemma multiplication_error_propagation3_case1_helper2_general:
  assumes case1: "exponent (rounded_mul::('e, 'f) float) + bias TYPE(('e, 'f) float) \<ge> exponent (a_float::('e, 'f) float) + exponent (b_float::('e, 'f) float)  + (n::nat)"
  and "exponent a_float \<noteq> 0"
  and "exponent b_float \<noteq> 0"
  and d1_def: "\<bar>d1\<bar> \<le> a_accuracy * ulp a_float"
  and d2_def: "\<bar>d2\<bar> \<le> b_accuracy * ulp b_float"
shows "\<bar>d1*d2\<bar> \<le> 
          (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy / (2::real)^n * ulp rounded_mul"
proof -
  from d2_def have "\<bar>d1 * d2\<bar> \<le> \<bar>d1\<bar> * b_accuracy * ulp b_float" apply(simp add:abs_mult) using mult_le_cancel_left[where c="\<bar>d1\<bar>"] by force
  moreover from d2_def have "b_accuracy * ulp b_float \<ge> 0" by linarith
  ultimately have "\<bar>d1 * d2\<bar> \<le> a_accuracy * ulp a_float * b_accuracy * ulp b_float" using d1_def  mult_le_cancel_left[where c="b_accuracy * ulp b_float"]
    by (smt (verit) mult_pos_neg2 mult_right_less_imp_less ulp_positive)
  with assms have"\<bar>d1*d2\<bar> \<le> a_accuracy * (2::real) ^ exponent a_float /
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f)) * b_accuracy * (2::real) ^ exponent b_float /
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" by(simp add: ulp_equivelance)
  then have step1:  "\<bar>d1*d2\<bar> \<le> (2::real) ^ exponent b_float * (2::real) ^ exponent a_float / (2::real) ^ bias TYPE(('e, 'f) float) *
          b_accuracy * a_accuracy / (2::real) ^ LENGTH('f) / 
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" apply(simp add:bias_def ulp_divisor_rewrite) by argo

  from case1 have "(2::real) ^ exponent rounded_mul * (2::real) ^ bias TYPE(('e, 'f) float) \<ge> (2::real) ^ exponent a_float * (2::real) ^ exponent b_float * (2::real)^n" using power_add
    by (metis exp_less)
  then have "(2::real) ^ exponent rounded_mul * (2::real) ^ bias TYPE(('e, 'f) float) / (2::real)^n \<ge> (2::real) ^ exponent a_float * (2::real) ^ exponent b_float"
    using mult_imp_div_pos_le[where y="(2::real)^n" and z="(2::real) ^ exponent rounded_mul * (2::real) ^ bias TYPE(('e, 'f) float)" and x="(2::real) ^ exponent a_float * (2::real) ^ exponent b_float"]
    by (simp add: le_divide_eq)
  then have "(2::real) ^ exponent rounded_mul / (2::real)^n * (2::real) ^ bias TYPE(('e, 'f) float) \<ge> (2::real) ^ exponent a_float * (2::real) ^ exponent b_float" by argo
  then have step1_5: "(2::real) ^ exponent rounded_mul / (2::real)^n \<ge> (2::real) ^ exponent b_float * (2::real) ^ exponent a_float / (2::real) ^ bias TYPE(('e, 'f) float)" 
    using mult_imp_div_pos_le[where z="(2::real) ^ exponent rounded_mul / (2::real)^n" and y="(2::real) ^ bias TYPE(('e, 'f) float)" and x="(2::real) ^ exponent b_float * (2::real) ^ exponent a_float"]
    by (simp add: mult.commute)
  from ulp_positive assms have "0 \<le>  b_accuracy * a_accuracy "
    by (smt (verit) mult_nonneg_nonneg mult_pos_neg2)
  then have "0 \<le> b_accuracy * a_accuracy / (2::real) ^ LENGTH('f) / 
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" by simp
  with step1_5 step1 have step2: "\<bar>d1*d2\<bar> \<le> (2::real) ^ exponent rounded_mul / (2::real)^n *
           b_accuracy * a_accuracy / (2::real) ^ LENGTH('f) / 
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" using mult_right_mono[where c="b_accuracy * a_accuracy / (2::real) ^ LENGTH('f) / 
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))"] by fastforce

  from step2 have "0 \<le> (2::real) ^ exponent rounded_mul / (2::real)^n *
           b_accuracy * a_accuracy / (2::real) ^ LENGTH('f) / 
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" by argo
  have "(2::real) ^ exponent rounded_mul / (2::real)^n > 0" by simp
  then have "b_accuracy * a_accuracy / (2::real) ^ LENGTH('f) / 
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f)) < 0 \<Longrightarrow> 
    0 > (2::real) ^ exponent rounded_mul / (2::real)^n *
         b_accuracy * a_accuracy / (2::real) ^ LENGTH('f) / 
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" using mult_pos_neg[where a="(2::real) ^ exponent rounded_mul / (2::real)^n" and b="b_accuracy * a_accuracy / (2::real) ^ LENGTH('f) / 
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))"] by argo
  with step2 have "0 \<le> b_accuracy * a_accuracy / (2::real) ^ LENGTH('f) / 
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" by argo
  moreover have "(2::real) ^ exponent rounded_mul / (2::real)^n \<le> (2::real) ^ (max (exponent rounded_mul) (1::nat)) / (2::real)^n "
    by (simp add: IEEE_Properties.div_less)
  ultimately have "(2::real) ^ exponent rounded_mul / (2::real)^n * 
          b_accuracy * a_accuracy / (2::real) ^ LENGTH('f) / 
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f)) \<le> (2::real) ^ (max (exponent rounded_mul) (1::nat)) / (2::real)^n *
          b_accuracy * a_accuracy / (2::real) ^ LENGTH('f) / 
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" 
      using mult_right_mono[where a="(2::real) ^ exponent rounded_mul/(2::real)^n " and b="(2::real) ^ (max (exponent rounded_mul) (1::nat))/ (2::real)^n "
            and c="b_accuracy * a_accuracy / (2::real) ^ LENGTH('f) / 
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))"] by simp
    with step2 have "\<bar>d1*d2\<bar> \<le> 
          1/(2::real)^n *b_accuracy * a_accuracy / (2::real) ^ LENGTH('f) * (2::real) ^ (max (exponent rounded_mul) (1::nat)) /
(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" by argo
    then have "\<bar>d1*d2\<bar> \<le> 
          1/(2::real)^n * b_accuracy / (2::real) ^ LENGTH('f) * a_accuracy * ulp rounded_mul" by(simp add: ulp_equivelance)
    then show ?thesis by argo
  qed


lemma multiplication_error_propagation3_distance:
  assumes "exponent a_float \<noteq> 0"
  and "exponent b_float \<noteq> 0"
  and "a_accuracy \<le> (2::real) ^ LENGTH('f)"
  and "b_accuracy \<le> (2::real) ^ LENGTH('f)"
  and "\<bar>valof a_float * valof b_float\<bar> < threshold TYPE(('e, 'f) float)"
shows "\<bar>(valof a_float * valof b_float) - (a_real*b_real)\<bar> \<le> (2*a_accuracy+2*b_accuracy) * ulp (fmul To_nearest a_float b_float)"
proof -
  thm rounding_multiplication_exponent
  from assms ulp_accuracy_def context_assumptions have "\<exists>d. (a_real = valof a_float + d \<and> \<bar>d\<bar> \<le> a_accuracy * ulp a_float)"
    by (metis abs_minus_commute add_diff_cancel_left' add_diff_eq)
  then obtain d1 where d1_def: "a_real = valof a_float + d1 \<and> \<bar>d1\<bar> \<le> a_accuracy * ulp a_float" by blast
  from assms ulp_accuracy_def context_assumptions have "\<exists>d. (b_real = valof b_float + d \<and> \<bar>d\<bar> \<le> b_accuracy * ulp b_float)"
    by (metis abs_minus_commute add_diff_cancel_left' add_diff_eq)
  then obtain d2 where d2_def: "b_real = valof b_float + d2 \<and> \<bar>d2\<bar> \<le> b_accuracy * ulp b_float" by blast
  with d1_def have real_float_diff: "a_real * b_real = (valof a_float * valof b_float) + (valof a_float * d2) + (valof b_float * d1) + (d1 * d2)" by algebra

  obtain rounded_mul where rounded_mul_def: "rounded_mul = (round To_nearest (valof a_float * valof b_float)::('e,'f) float)" by blast 
  with rounding_0_5_ulp ulp_accuracy_def assms context_assumptions have rounded_mul_d: "\<bar>valof rounded_mul - (valof a_float * valof b_float)\<bar> \<le> 0.5 * ulp rounded_mul" by fast  
  moreover from is_finite_closest rounded_mul_def assms have fin_rounded_mul: "is_finite rounded_mul" by auto
  ultimately have "ulp_accuracy (valof a_float * valof b_float) rounded_mul 0.5" using ulp_accuracy_def by blast
  have step_1: "valof (fmul To_nearest a_float b_float) = valof (
                 round To_nearest (valof a_float * valof b_float)::('e,'f) float)" 
    using assms apply(simp add:fmul_def valof_zerosign del:round.simps)
    using assms ulp_accuracy_def float_distinct_finite context_assumptions by blast
  with rounded_mul_def have ulp_same: "ulp (fmul To_nearest a_float b_float) = ulp rounded_mul" using abs_valof_e_exp_e exp_e_ulp_e by metis
  

  {
    assume case1: "exponent rounded_mul + bias TYPE(('e, 'f) float) = exponent a_float + exponent b_float"
    with rounded_mul_def fin_rounded_mul assms rounding_multiplication_exponent have fracs_added: "fraction a_float + fraction b_float < (2::nat) ^ LENGTH('f)" by blast

    from case1 have case1_ge: "exponent rounded_mul + bias TYPE(('e, 'f) float) \<ge> exponent a_float + exponent b_float+ 0 " by auto
    

    from d1_def multiplication_error_propagation3_case1_helper_general[OF case1_ge assms(1) assms(2)] have b_d1: "\<bar>valof b_float * d1\<bar> \<le> 
          ((1::real) + real (fraction b_float) / (2::real) ^ LENGTH('f)) * a_accuracy * ulp rounded_mul" by simp
    from case1_ge have case1_ge':"exponent rounded_mul + bias TYPE(('e, 'f) float)\<ge> exponent b_float + exponent a_float + 0 " by simp
    from d2_def multiplication_error_propagation3_case1_helper_general[ OF case1_ge' assms(2) assms(1)] have a_d2: "\<bar>valof a_float * d2\<bar> \<le> 
          ((1::real) + real (fraction a_float) / (2::real) ^ LENGTH('f)) * b_accuracy * ulp rounded_mul" by simp

    from d1_def d2_def multiplication_error_propagation3_case1_helper2_general[OF case1_ge  assms(1) assms(2)] have d1_d2: "\<bar>d1*d2\<bar> \<le> 
          (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy * ulp rounded_mul" by simp

    from b_d1 a_d2 d1_d2 have combined: "\<bar>valof b_float * d1 + valof a_float * d2 + d1 * d2\<bar> \<le>
      (
        (fraction b_float / (2::real) ^ LENGTH('f) * a_accuracy +
        fraction a_float / (2::real) ^ LENGTH('f) * b_accuracy +
        (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy) 
      + a_accuracy + b_accuracy
      ) * ulp rounded_mul" by argo

    from ulp_accuracy_non_negative assms frac_def context_assumptions have all_pos: 
      "0 \<le> a_accuracy \<and> 0 \<le> b_accuracy \<and> 0 \<le> fraction a_float \<and> 0 < (2::real) ^ LENGTH('f)" by fastforce
    from fracs_added have "fraction b_float \<le> (2::real) ^ LENGTH('f) - fraction a_float"
      using power_2_simp[where x="LENGTH('f)"] by linarith
    with all_pos have "fraction b_float / (2::real) ^ LENGTH('f) * a_accuracy +
           fraction a_float / (2::real) ^ LENGTH('f) * b_accuracy +
           (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy \<le> 
           ((2::real) ^ LENGTH('f) - fraction a_float) / (2::real) ^ LENGTH('f) * a_accuracy +
           fraction a_float / (2::real) ^ LENGTH('f) * b_accuracy +
           (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy" 
      by(simp add:mult_le_cancel_right divide_le_cancel)
    with all_pos have "fraction b_float / (2::real) ^ LENGTH('f) * a_accuracy +
           fraction a_float / (2::real) ^ LENGTH('f) * b_accuracy +
           (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy \<le>  
           (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float +
           (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy + (2::real) ^ LENGTH('f)/ (2::real) ^ LENGTH('f) * a_accuracy"
      by argo
    with all_pos have before_split: "fraction b_float / (2::real) ^ LENGTH('f) * a_accuracy +
           fraction a_float / (2::real) ^ LENGTH('f) * b_accuracy +
           (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy \<le>  
           (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float +
           b_accuracy* a_accuracy / (2::real) ^ LENGTH('f) + a_accuracy" by simp

    
    from float_frac_l have "fraction a_float < (2::real) ^ LENGTH('f)" using power_2_simp[where x="LENGTH('f)"] by auto
    then have "fraction a_float \<le> (2::real) ^ LENGTH('f)" by fastforce
    moreover have "b_accuracy \<ge> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) \<ge> 0" by simp
    ultimately have "b_accuracy \<ge> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float \<le> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * (2::real) ^ LENGTH('f)"
      using mult_left_mono by blast
    with all_pos have "b_accuracy \<ge> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float \<le> (b_accuracy - a_accuracy)" by auto
    then have "b_accuracy \<ge> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float +
           b_accuracy* a_accuracy / (2::real) ^ LENGTH('f) + a_accuracy \<le> b_accuracy* a_accuracy / (2::real) ^ LENGTH('f) + b_accuracy" by argo
    with all_pos assms have b_ge_a: "b_accuracy \<ge> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float +
           b_accuracy* a_accuracy / (2::real) ^ LENGTH('f) + a_accuracy \<le> a_accuracy + b_accuracy" using mult_right_mono[where c="a_accuracy / (2::real) ^ LENGTH('f)"] by fastforce

    from float_frac_l have "fraction a_float < (2::real) ^ LENGTH('f)" using power_2_simp[where x="LENGTH('f)"] by auto
    then have "fraction a_float \<le> (2::real) ^ LENGTH('f)" by fastforce
    moreover have "b_accuracy \<le> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) \<le> 0" by (simp add: divide_nonpos_nonneg)
    ultimately have "b_accuracy \<le> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float \<le> 0"
      by (metis mult_nonneg_nonpos2 of_nat_0_le_iff)
    then have "b_accuracy \<le> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float +
           b_accuracy* a_accuracy / (2::real) ^ LENGTH('f) + a_accuracy \<le> b_accuracy* a_accuracy / (2::real) ^ LENGTH('f) + a_accuracy" by argo
    moreover from all_pos assms have "a_accuracy* b_accuracy / (2::real) ^ LENGTH('f) \<le> b_accuracy" using mult_right_mono[where c="b_accuracy / (2::real) ^ LENGTH('f)"] by fastforce
    ultimately have "b_accuracy \<le> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float +
           b_accuracy* a_accuracy / (2::real) ^ LENGTH('f) + a_accuracy \<le> a_accuracy + b_accuracy" by argo
    with b_ge_a have "(b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float +
           b_accuracy* a_accuracy / (2::real) ^ LENGTH('f) + a_accuracy \<le> a_accuracy + b_accuracy" by linarith

    with before_split all_pos have "fraction b_float / (2::real) ^ LENGTH('f) * a_accuracy +
           fraction a_float / (2::real) ^ LENGTH('f) * b_accuracy +
           (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy \<le> a_accuracy + b_accuracy" by argo
    then have "(
        (fraction b_float / (2::real) ^ LENGTH('f) * a_accuracy +
        fraction a_float / (2::real) ^ LENGTH('f) * b_accuracy +
        (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy) 
      + a_accuracy + b_accuracy
      ) \<le> 2*a_accuracy + 2*b_accuracy" by argo
    with ulp_positive combined have "(
        (fraction b_float / (2::real) ^ LENGTH('f) * a_accuracy +
        fraction a_float / (2::real) ^ LENGTH('f) * b_accuracy +
        (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy) 
      + a_accuracy + b_accuracy
      ) * ulp rounded_mul \<le> (
        2*a_accuracy + 2*b_accuracy
      ) * ulp rounded_mul" using mult_right_mono[where c="ulp rounded_mul"]
      using less_eq_real_def by blast
    with combined have "\<bar>valof b_float * d1 + valof a_float * d2 + d1 * d2\<bar> \<le> (
        2*a_accuracy + 2*b_accuracy
      ) * ulp rounded_mul"
      by auto
  } note case1 = this

  {
    assume case2: "exponent rounded_mul + bias TYPE(('e, 'f) float) \<noteq> exponent a_float + exponent b_float"
    with  rounding_multiplication_exponent_ge assms have "exponent rounded_mul + bias TYPE(('e, 'f) float) > exponent a_float + exponent b_float"
      using fin_rounded_mul rounded_mul_def by fastforce
    then have case2_ge: "exponent rounded_mul + bias TYPE(('e, 'f) float) \<ge> exponent a_float + exponent b_float + 1" by fastforce
    from float_frac_l have fracs_added: "fraction a_float + fraction b_float < 2*(2::nat) ^ LENGTH('f)"
      by (metis add_less_mono mult_2)

    from d1_def multiplication_error_propagation3_case1_helper_general[OF case2_ge assms(1) assms(2)] have b_d1: "\<bar>valof b_float * d1\<bar> \<le> 
          ((1::real) + real (fraction b_float) / (2::real) ^ LENGTH('f)) * a_accuracy / 2 * ulp rounded_mul" by simp
    from case2_ge have case2_ge':"exponent rounded_mul + bias TYPE(('e, 'f) float)\<ge> exponent b_float + exponent a_float + 1 " by simp
    from d2_def multiplication_error_propagation3_case1_helper_general[OF case2_ge' assms(2) assms(1)] have a_d2: "\<bar>valof a_float * d2\<bar> \<le> 
          ((1::real) + real (fraction a_float) / (2::real) ^ LENGTH('f)) * b_accuracy / 2 * ulp rounded_mul" by simp

    from d1_def d2_def multiplication_error_propagation3_case1_helper2_general[OF case2_ge  assms(1) assms(2)] have d1_d2: "\<bar>d1*d2\<bar> \<le> 
          (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy / 2 * ulp rounded_mul" by simp

    from b_d1 a_d2 d1_d2 have combined: "\<bar>valof b_float * d1 + valof a_float * d2 + d1 * d2\<bar> \<le>
      (
        (fraction b_float / (2::real) ^ LENGTH('f) * a_accuracy +
        fraction a_float / (2::real) ^ LENGTH('f) * b_accuracy +
        (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy) 
      + a_accuracy + b_accuracy
      ) / 2 * ulp rounded_mul" by argo

    from ulp_accuracy_non_negative assms frac_def context_assumptions have all_pos: 
      "0 \<le> a_accuracy \<and> 0 \<le> b_accuracy \<and> 0 \<le> fraction a_float \<and> 0 < (2::real) ^ LENGTH('f)" by fastforce
    from fracs_added have "fraction b_float \<le> 2*(2::real) ^ LENGTH('f) - fraction a_float"
      using power_2_simp[where x="LENGTH('f)"] by linarith
    with all_pos have "fraction b_float / (2::real) ^ LENGTH('f) * a_accuracy +
           fraction a_float / (2::real) ^ LENGTH('f) * b_accuracy +
           (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy \<le> 
           (2*(2::real) ^ LENGTH('f) - fraction a_float) / (2::real) ^ LENGTH('f) * a_accuracy +
           fraction a_float / (2::real) ^ LENGTH('f) * b_accuracy +
           (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy" 
      by(simp add:mult_le_cancel_right divide_le_cancel)
    with all_pos have "fraction b_float / (2::real) ^ LENGTH('f) * a_accuracy +
           fraction a_float / (2::real) ^ LENGTH('f) * b_accuracy +
           (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy \<le>  
           (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float +
           (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy + 2*(2::real) ^ LENGTH('f)/ (2::real) ^ LENGTH('f) * a_accuracy"
      by argo
    with all_pos have before_split: "fraction b_float / (2::real) ^ LENGTH('f) * a_accuracy +
           fraction a_float / (2::real) ^ LENGTH('f) * b_accuracy +
           (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy \<le>  
           (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float +
           b_accuracy* a_accuracy / (2::real) ^ LENGTH('f) + 2*a_accuracy" by simp

    
    from float_frac_l have "fraction a_float < (2::real) ^ LENGTH('f)" using power_2_simp[where x="LENGTH('f)"] by auto
    then have "fraction a_float \<le> (2::real) ^ LENGTH('f)" by fastforce
    moreover have "b_accuracy \<ge> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) \<ge> 0" by simp
    ultimately have "b_accuracy \<ge> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float \<le> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * (2::real) ^ LENGTH('f)"
      using mult_left_mono by blast
    with all_pos have "b_accuracy \<ge> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float \<le> (b_accuracy - a_accuracy)" by auto
    then have "b_accuracy \<ge> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float +
           b_accuracy* a_accuracy / (2::real) ^ LENGTH('f) + a_accuracy \<le> b_accuracy* a_accuracy / (2::real) ^ LENGTH('f) + b_accuracy" by argo
    with all_pos assms have b_ge_a: "b_accuracy \<ge> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float +
           b_accuracy* a_accuracy / (2::real) ^ LENGTH('f) + a_accuracy \<le> a_accuracy + b_accuracy" using mult_right_mono[where c="a_accuracy / (2::real) ^ LENGTH('f)"] by fastforce

    from float_frac_l have "fraction a_float < (2::real) ^ LENGTH('f)" using power_2_simp[where x="LENGTH('f)"] by auto
    then have "fraction a_float \<le> (2::real) ^ LENGTH('f)" by fastforce
    moreover have "b_accuracy \<le> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) \<le> 0" by (simp add: divide_nonpos_nonneg)
    ultimately have "b_accuracy \<le> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float \<le> 0"
      by (metis mult_nonneg_nonpos2 of_nat_0_le_iff)
    then have "b_accuracy \<le> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float +
           b_accuracy* a_accuracy / (2::real) ^ LENGTH('f) + a_accuracy \<le> b_accuracy* a_accuracy / (2::real) ^ LENGTH('f) + a_accuracy" by argo
    moreover from all_pos assms have "a_accuracy* b_accuracy / (2::real) ^ LENGTH('f) \<le> b_accuracy" using mult_right_mono[where c="b_accuracy / (2::real) ^ LENGTH('f)"] by fastforce
    ultimately have "b_accuracy \<le> a_accuracy \<Longrightarrow> (b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float +
           b_accuracy* a_accuracy / (2::real) ^ LENGTH('f) + a_accuracy \<le> a_accuracy + b_accuracy" by argo
    with b_ge_a have "(b_accuracy - a_accuracy) / (2::real) ^ LENGTH('f) * fraction a_float +
           b_accuracy* a_accuracy / (2::real) ^ LENGTH('f) + a_accuracy \<le> a_accuracy + b_accuracy" by linarith

    with before_split all_pos have "fraction b_float / (2::real) ^ LENGTH('f) * a_accuracy +
           fraction a_float / (2::real) ^ LENGTH('f) * b_accuracy +
           (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy \<le> 2*a_accuracy + b_accuracy" by argo
    then have "(
        (fraction b_float / (2::real) ^ LENGTH('f) * a_accuracy +
        fraction a_float / (2::real) ^ LENGTH('f) * b_accuracy +
        (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy) 
      + a_accuracy + b_accuracy
      ) \<le> 3*a_accuracy + 2*b_accuracy" by argo
    with ulp_positive combined have "(
        (fraction b_float / (2::real) ^ LENGTH('f) * a_accuracy +
        fraction a_float / (2::real) ^ LENGTH('f) * b_accuracy +
        (b_accuracy / (2::real) ^ LENGTH('f)) * a_accuracy) 
      + a_accuracy + b_accuracy
      ) * ulp rounded_mul \<le> (
        3*a_accuracy + 2*b_accuracy
      ) * ulp rounded_mul" using mult_right_mono[where c="ulp rounded_mul"]
      using less_eq_real_def by blast
    with combined have step3: "\<bar>valof b_float * d1 + valof a_float * d2 + d1 * d2\<bar> \<le> (
        3*a_accuracy + 2*b_accuracy
      ) / 2 * ulp rounded_mul"
      by auto

    from ulp_accuracy_non_negative a_rel b_rel have "3*a_accuracy \<le> 4*a_accuracy" by fastforce
    moreover from ulp_accuracy_non_negative a_rel b_rel have "2*b_accuracy \<le> 4*b_accuracy" by fastforce
    ultimately have "3*a_accuracy + 2*b_accuracy \<le> 4*a_accuracy + 4*b_accuracy" by force
    moreover from ulp_positive have "0 < 1/ 2 * ulp rounded_mul" by auto
    ultimately have "(
        3*a_accuracy + 2*b_accuracy
      ) / 2 * ulp rounded_mul \<le> (
        4*a_accuracy + 4*b_accuracy
      ) / 2 * ulp rounded_mul"
      using mult_right_mono[where c="1/ 2 * ulp rounded_mul"] by fastforce
    with step3 have "\<bar>valof b_float * d1 + valof a_float * d2 + d1 * d2\<bar> \<le> (
        2*a_accuracy + 2*b_accuracy
      ) * ulp rounded_mul"
      by argo
  } note case2 = this
  from case1 case2 have cases_combined: "\<bar>valof b_float * d1 + valof a_float * d2 + d1 * d2\<bar> \<le> (
        2*a_accuracy + 2*b_accuracy
      ) * ulp rounded_mul" by blast
  with real_float_diff have rounded_mul_dist:"\<bar>(valof a_float * valof b_float) - a_real * b_real\<bar> \<le> (
        2*a_accuracy + 2*b_accuracy
      ) * ulp rounded_mul" by simp
  from is_finite_closest have "is_finite (closest valof (\<lambda>a::('e, 'f) float. even (fraction a)) (Collect is_finite) (valof a_float + valof b_float))" by blast
  with ulp_same fin_rounded_mul rounded_mul_dist show ?thesis by presburger
qed


lemma multiplication_error_propagation_combined_distance:
  assumes "\<bar>valof a_float * valof b_float\<bar> < threshold TYPE(('e, 'f) float)"
  and "a_accuracy \<le> (2::real) ^ LENGTH('f)"
  and "b_accuracy \<le> (2::real) ^ LENGTH('f)"
  and "0 \<le> a_real" and "a_real \<le> 1"
  and "0 \<le> b_real" and "b_real \<le> 1"
shows "\<bar>(valof a_float * valof b_float) - (a_real*b_real)\<bar> \<le> (2*a_accuracy+2*b_accuracy) * ulp (fmul To_nearest a_float b_float)"
  apply(cases "exponent a_float \<noteq> 0")
  apply(cases "exponent b_float \<noteq> 0")
  using assms multiplication_error_propagation3_distance apply blast
  subgoal proof -
    from ulp_accuracy_non_negative a_rel b_rel have "(2*a_accuracy+b_accuracy) \<le> (2*a_accuracy+2*b_accuracy)"
      by fastforce
    with ulp_positive have dist_bigger: "(2*a_accuracy+b_accuracy) * ulp (fmul To_nearest a_float b_float) \<le> (2*a_accuracy+2*b_accuracy) * ulp (fmul To_nearest a_float b_float)"
      using mult_right_mono[where c="ulp (fmul To_nearest a_float b_float)" and a="(2*a_accuracy+b_accuracy)" and b="(2*a_accuracy+2*b_accuracy)"]
      using less_eq_real_def by blast
    from multiplication_error_propagation1_distance_1 dist_bigger assms(1) assms(4) assms(5)
    show " exponent a_float \<noteq> (0::nat) \<Longrightarrow>
    \<not> exponent b_float \<noteq> (0::nat) \<Longrightarrow>
    \<bar>valof a_float * valof b_float - a_real * b_real\<bar>
    \<le> (2*a_accuracy + 2*b_accuracy) * ulp (fmul To_nearest a_float b_float)" by argo
  qed
  apply(cases "exponent b_float \<noteq> 0")
  subgoal proof -
    from ulp_accuracy_non_negative a_rel b_rel have "(a_accuracy+2*b_accuracy) \<le> (2*a_accuracy+2*b_accuracy)"
      by fastforce
    with ulp_positive have dist_bigger: "(a_accuracy+2*b_accuracy) * ulp (fmul To_nearest a_float b_float) \<le> (2*a_accuracy+2*b_accuracy) * ulp (fmul To_nearest a_float b_float)"
      using mult_right_mono[where c="ulp (fmul To_nearest a_float b_float)" and a="(a_accuracy+2*b_accuracy)" and b="(2*a_accuracy+2*b_accuracy)"]
      using less_eq_real_def by blast
    have mul_same: "fmul To_nearest a_float b_float = fmul To_nearest b_float a_float" by(simp add: fmul_def mult.commute)
    from multiplication_error_propagation1_distance_2
    have reorederd: "b_real \<le> (1::real) \<Longrightarrow>
      (0::real) \<le> b_real \<Longrightarrow>
      \<bar>valof a_float * valof b_float\<bar> < threshold TYPE(('e, 'f) float) \<Longrightarrow>
      exponent b_float \<noteq> (0::nat) \<Longrightarrow>
      exponent a_float = (0::nat) \<Longrightarrow>
      \<bar>valof a_float * valof b_float - a_real * b_real\<bar>
       \<le> (a_accuracy + (2::real) * b_accuracy) * ulp (fmul To_nearest a_float b_float)" by argo
    from reorederd[OF assms(7) assms(6) assms(1)] dist_bigger mul_same
    show "\<not>  exponent a_float \<noteq> (0::nat) \<Longrightarrow>
    exponent b_float \<noteq> (0::nat) \<Longrightarrow>
    \<bar>valof a_float * valof b_float - a_real * b_real\<bar>
    \<le> (2*a_accuracy + 2*b_accuracy) * ulp (fmul To_nearest a_float b_float)" by fastforce
  qed
  subgoal proof -
    from multiplication_error_propagation2_distance_1
    have reordered: "a_real \<le> (1::real) \<Longrightarrow>
      (0::real) \<le> a_real \<Longrightarrow>
      \<bar>valof a_float * valof b_float\<bar> < threshold TYPE(('e, 'f) float) \<Longrightarrow>
      exponent a_float = (0::nat) \<Longrightarrow>
      exponent b_float = (0::nat) \<Longrightarrow>
      \<bar>valof a_float * valof b_float - a_real * b_real\<bar> \<le> (a_accuracy + b_accuracy) * ulp (fmul To_nearest a_float b_float)"
      by blast
    from reordered[OF assms(5) assms(4) assms(1)]
    show "\<not> exponent a_float \<noteq> (0::nat) \<Longrightarrow>
    \<not> exponent b_float \<noteq> (0::nat) \<Longrightarrow>
    \<bar>valof a_float * valof b_float - a_real * b_real\<bar>
    \<le> ((2::real) * a_accuracy + (2::real) * b_accuracy) * ulp (fmul To_nearest a_float b_float)" by argo
  qed
  done

lemma multiplication_error_propagation_ulp_accuracy:
  assumes "\<bar>valof a_float * valof b_float\<bar> < threshold TYPE(('e, 'f) float)"
  and "a_accuracy \<le> (2::real) ^ LENGTH('f)"
  and "b_accuracy \<le> (2::real) ^ LENGTH('f)"
  and "0 \<le> a_real" and "a_real \<le> 1"
  and "0 \<le> b_real" and "b_real \<le> 1"
shows "ulp_accuracy (a_real * b_real) (fmul To_nearest a_float b_float) (2*a_accuracy + 2*b_accuracy + 0.5)"
proof -
  have step_1: "valof (fmul To_nearest a_float b_float) = valof (
                 round To_nearest (valof a_float * valof b_float)::('e,'f) float)" 
    apply(simp add:fmul_def valof_zerosign del:round.simps)
    using assms context_assumptions ulp_accuracy_def float_distinct_finite by blast
  moreover obtain rounded_mul where rounded_mul_def: "rounded_mul = (round To_nearest (valof a_float * valof b_float)::('e,'f) float)" by blast 
  ultimately have ulp_accuracy_same: "ulp_accuracy (a_real * b_real) (fmul To_nearest a_float b_float) (2*a_accuracy + 2*b_accuracy + 0.5) =
    ulp_accuracy (a_real * b_real) rounded_mul (2*a_accuracy + 2*b_accuracy + 0.5)" using valof_same_ulp_accuracy_same by blast 
  from step_1 rounded_mul_def have ulp_same: "ulp (fmul To_nearest a_float b_float) = ulp rounded_mul" using abs_valof_e_exp_e exp_e_ulp_e by metis
  
  with assms multiplication_error_propagation_combined_distance have "\<bar>(valof a_float * valof b_float) - (a_real*b_real)\<bar> \<le> (2*a_accuracy+2*b_accuracy) * ulp rounded_mul" by metis
  moreover from rounding_0_5_ulp ulp_accuracy_def assms context_assumptions rounded_mul_def have "\<bar>valof rounded_mul - (valof a_float * valof b_float)\<bar> \<le> 0.5 * ulp rounded_mul" by fast
  ultimately have rounded_mul_dist: "\<bar>valof rounded_mul - (a_real*b_real)\<bar> \<le> (0.5+2*a_accuracy+2*b_accuracy) * ulp rounded_mul" by argo

  from is_finite_closest have "is_finite (closest valof (\<lambda>a::('e, 'f) float. even (fraction a)) (Collect is_finite) (valof a_float * valof b_float))" by blast
  with rounded_mul_def assms have "is_finite rounded_mul" by fastforce
  with rounded_mul_dist have "ulp_accuracy (a_real * b_real) rounded_mul (2*a_accuracy + 2*b_accuracy + 0.5)"
    apply(simp add:ulp_accuracy_def) by argo
  with ulp_accuracy_same show ?thesis by fast
qed

lemma multiplication_addition_error_propagation_ulp_accuracy:
  assumes  "\<bar>valof a_float * valof b_float + valof c_float\<bar> < threshold TYPE(('e, 'f) float)"
   and "a_accuracy \<le> (2::real) ^ LENGTH('f)"
   and "b_accuracy \<le> (2::real) ^ LENGTH('f)"
   and "0 \<le> a_real" and "a_real \<le> 1"
   and "0 \<le> b_real" and "b_real \<le> 1"
shows "ulp_accuracy (a_real * b_real + c_real) (fmul_add To_nearest a_float b_float c_float) (2*a_accuracy + 2*b_accuracy + c_accuracy + 0.5)"
proof -
  from mult_nonneg_nonneg valof_nonneg sign_a sign_b abs_of_nonneg have mult_eq_abs: "\<bar>valof a_float * valof b_float\<bar> = valof a_float * valof b_float" by meson
  moreover from valof_nonneg sign_c abs_of_nonneg have c_eq_abs: "\<bar>valof c_float\<bar> = valof c_float" by blast
  ultimately have multiplication_le: "\<bar>valof a_float * valof b_float\<bar> \<le> \<bar>valof a_float * valof b_float + valof c_float\<bar>" by force
  with assms(1) have mult_l_threshold: "\<bar>valof a_float * valof b_float\<bar> < threshold TYPE(('e, 'f) float)" by argo
  with assms multiplication_error_propagation_combined_distance have mult_dist:
    "\<bar>(valof a_float * valof b_float) - (a_real*b_real)\<bar> \<le> (2*a_accuracy+2*b_accuracy) * ulp (fmul To_nearest a_float b_float)" by blast
  from c_eq_abs mult_eq_abs have mult_add_eq_abs: "\<bar>valof a_float * valof b_float + valof c_float\<bar> = valof a_float * valof b_float + valof c_float" by argo

  obtain rounded_sum where rounded_sum_def: "rounded_sum = (round To_nearest (valof a_float * valof b_float + valof c_float)::('e,'f) float)" by blast 
  then have fmul_add_to_round: "valof (fmul_add To_nearest a_float b_float c_float) = valof (
                 rounded_sum)" 
    using sign_a sign_b sign_c apply(simp add:fmul_add_def Let_def valof_zerosign valof_round_nearest_zero del:round.simps)
    using ulp_accuracy_def float_distinct_finite a_rel b_rel c_rel by blast
  with fmul_add_to_round have ulp_same: "ulp (fmul_add To_nearest a_float b_float c_float) = ulp rounded_sum" using abs_valof_e_exp_e ulp_equivelance by metis 
  from fmul_add_to_round ge_zero_rounding_ge_zero mult_eq_abs assms(1) rounded_sum_def have abs_fmul_add_to_round:"\<bar>valof (fmul_add To_nearest a_float b_float c_float)\<bar> = valof (
                 rounded_sum)"
    by (metis abs_le_self_iff abs_le_zero_iff abs_of_nonneg add.right_neutral add_le_same_cancel1 mult_add_eq_abs)
  have fmul_to_round: "valof (fmul To_nearest a_float b_float) = valof (
                 round To_nearest (valof a_float * valof b_float)::('e,'f) float)" 
    using sign_a sign_b sign_c apply(simp add:fmul_def Let_def valof_zerosign valof_round_nearest_zero del:round.simps)
    using ulp_accuracy_def float_distinct_finite a_rel b_rel c_rel float_distinct_finite by blast
  with ge_zero_rounding_ge_zero mult_eq_abs mult_l_threshold have abs_fmul_to_round: "\<bar>valof (fmul To_nearest a_float b_float)\<bar> = valof (
                 round To_nearest (valof a_float * valof b_float)::('e,'f) float)" by force
 
  from abs_fmul_add_to_round abs_fmul_to_round ge_rounding_ge multiplication_le assms(2) rounded_sum_def have 
    "\<bar>valof (fmul To_nearest a_float b_float)\<bar> \<le> \<bar>valof (fmul_add To_nearest a_float b_float c_float)\<bar>"
    by (smt (verit, ccfv_SIG) c_eq_abs assms(1))
  with exp_ge_ulp_ge abs_valof_ge_exp_ge ulp_same have "ulp (fmul To_nearest a_float b_float) \<le> ulp rounded_sum" by metis
  with a_rel b_rel ulp_accuracy_non_negative mult_dist have mult_dist2: 
    "\<bar>(valof a_float * valof b_float) - (a_real*b_real)\<bar> \<le> (2*a_accuracy+2*b_accuracy) * ulp rounded_sum"
    by (smt (verit, ccfv_SIG) ordered_comm_semiring_class.comm_mult_left_mono)
  
  { 
    from assms context_assumptions ulp_accuracy_def have finite_a_b_c: "is_finite c_float" by blast
    with addition_rounding_increases[where a="valof a_float * valof b_float" and b="c_float"]
      assms context_assumptions rounded_sum_def mult_eq_abs zero_le_power_abs have "valof c_float \<le> valof rounded_sum"
      by (metis power_one_right)
    with valof_nonneg assms abs_of_nonneg context_assumptions have "\<bar>valof c_float\<bar> \<le> \<bar>valof rounded_sum\<bar>"
      by (smt (verit, del_insts))
    with abs_valof_ge_exp_ge exp_ge_ulp_ge assms ulp_accuracy_non_negative context_assumptions have 
      "c_accuracy * ulp c_float \<le> c_accuracy * ulp rounded_sum"
      using mult_left_mono by metis
    moreover from assms ulp_accuracy_def context_assumptions have "\<bar>valof c_float - c_real\<bar> \<le> c_accuracy * ulp c_float" by fast
    ultimately have "\<bar>valof c_float - c_real\<bar> \<le> c_accuracy * ulp rounded_sum" by argo
  }
  with mult_dist2 have "\<bar>(valof a_float * valof b_float+valof c_float) - (a_real*b_real+c_real)\<bar> \<le> (2*a_accuracy+2*b_accuracy+c_accuracy) * ulp rounded_sum"
    by argo
  
  moreover from rounding_0_5_ulp ulp_accuracy_def assms context_assumptions rounded_sum_def have "\<bar>valof rounded_sum - (valof a_float * valof b_float + valof c_float)\<bar> \<le> 0.5 * ulp rounded_sum" by fast
  ultimately have rounded_mul_dist: "\<bar>valof rounded_sum - (a_real*b_real+c_real)\<bar> \<le> (0.5+2*a_accuracy+2*b_accuracy+c_accuracy) * ulp rounded_sum" by argo

  from is_finite_closest have "is_finite (closest valof (\<lambda>a::('e, 'f) float. even (fraction a)) (Collect is_finite) (valof a_float * valof b_float+valof c_float))" by blast
  with rounded_sum_def assms have "is_finite rounded_sum" by fastforce
  with rounded_mul_dist have "ulp_accuracy (a_real * b_real+c_real) rounded_sum (2*a_accuracy + 2*b_accuracy + c_accuracy + 0.5)"
    apply(simp add:ulp_accuracy_def) by argo
  moreover have ulp_accuracy_same: "ulp_accuracy (a_real * b_real + c_real) (fmul_add To_nearest a_float b_float c_float) (2*a_accuracy + 2*b_accuracy + c_accuracy + 0.5) =
    ulp_accuracy (a_real * b_real + c_real) rounded_sum (2*a_accuracy + 2*b_accuracy + c_accuracy + 0.5)" using valof_same_ulp_accuracy_same fmul_add_to_round by blast
  ultimately show ?thesis by fast
qed

thm three_mul_added_numbers
lemma multiplication_addition_error_propagation_ulp_accuracy2:
  assumes "is_finite (fmul_add To_nearest a_float b_float c_float)"
  and "a_accuracy \<le> (2::real) ^ LENGTH('f)"
  and "b_accuracy \<le> (2::real) ^ LENGTH('f)"
  and "0 \<le> a_real" and "a_real \<le> 1"
  and "0 \<le> b_real" and "b_real \<le> 1"
shows "ulp_accuracy (a_real * b_real + c_real) (fmul_add To_nearest a_float b_float c_float) (2*a_accuracy + 2*b_accuracy + c_accuracy + 0.5)"
  using three_mul_added_numbers(1) assms multiplication_addition_error_propagation_ulp_accuracy
  by metis
end
end