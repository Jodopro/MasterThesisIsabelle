theory IEEE_Properties_Rounding
imports IEEE_Properties_Basic_Extension "HOL-Library.Extended_Real"
begin

lemma round_to_ninfinity_not_empty:
  assumes threshold: "\<bar>a\<bar> \<le> largest TYPE(('e, 'f)float)" and len_e: "1 < LENGTH('e)"
  shows "{c::('e, 'f) float. is_finite c \<and> valof c \<le> a} \<noteq> {}"
proof -
  have fin_bot: "is_finite (bottomfloat::('e, 'f) float)" using finite_bottomfloat by auto
  from threshold valof_topfloat len_e have "(valof (bottomfloat::('e, 'f) float)) \<le> a"
    by (simp add: bottomfloat_eq_m_largest valof_topfloat)
  with fin_bot show ?thesis by blast
qed

lemma round_to_infinity_not_empty:
  assumes threshold: "\<bar>a\<bar> \<le> largest TYPE(('e, 'f)float)" and len_e: "1 < LENGTH('e)"
  shows "{c::('e, 'f) float. is_finite c \<and> valof c \<ge> a} \<noteq> {}"
proof -
  have fin_top: "is_finite (topfloat::('e, 'f) float)" using finite_topfloat by auto
  from threshold valof_topfloat have "(valof (topfloat::('e, 'f) float)) \<ge> a"
    by (metis abs_le_D1 len_e)
  with fin_top show ?thesis by blast
qed

lemma extract_set_properties_closest:
  assumes not_empty: "{c. P c} \<noteq> {}"
  shows "P ((closest valof (\<lambda>c. Q c) {c. P c} a)::('e, 'f) float)"
proof -
  from not_empty Hilbert_Choice.someI_ex have "is_closest (valof) {c::('e, 'f) float. P c} a (SOME output. is_closest (valof) {c::('e, 'f) float. P c} a output)"
    by (metis (no_types, lifting) closest_is_closest) 
  from is_closest_def have  "\<forall>output. ((is_closest (valof) {c::('e, 'f) float. P c} a output) \<longrightarrow> (P output))"
    by (metis mem_Collect_eq)
  then show ?thesis 
    by (metis closest_is_closest not_empty)
qed

lemma extract_set_properties_closest_to_ninfinity: 
  assumes len_e: "1 < LENGTH('e)"
    and threshold: "\<bar>a\<bar> \<le> largest TYPE(('e, 'f)float)"
  shows "is_finite ((closest valof (\<lambda>c. True) {c::('e, 'f) float. is_finite c \<and> valof c \<le> a} a)::('e, 'f) float)"
    and "valof ((closest valof (\<lambda>c. True) {c::('e, 'f) float. is_finite c \<and> valof c \<le> a} a)::('e, 'f) float) \<le> a"
  subgoal
  proof -
    from len_e threshold round_to_ninfinity_not_empty have "{c::('e, 'f) float. is_finite c \<and> valof c \<le> a} \<noteq> {}" by fast
    with extract_set_properties_closest show ?thesis by (smt (verit, del_insts))
  qed
  subgoal
  proof -
    from len_e threshold round_to_ninfinity_not_empty have "{c::('e, 'f) float. is_finite c \<and> valof c \<le> a} \<noteq> {}" by fast
    with extract_set_properties_closest show ?thesis by (smt (verit, del_insts))
  qed
  done

lemma extract_set_properties_closest_to_infinity: 
  assumes len_e: "1 < LENGTH('e)"
    and threshold: "\<bar>a\<bar> \<le> largest TYPE(('e, 'f)float)"
  shows "is_finite ((closest valof (\<lambda>c. True) {c::('e, 'f) float. is_finite c \<and> valof c \<ge> a} a)::('e, 'f) float)" 
    and "valof ((closest valof (\<lambda>c. True) {c::('e, 'f) float. is_finite c \<and> valof c \<ge> a} a)::('e, 'f) float) \<ge> a"
  subgoal
  proof -
    from len_e threshold round_to_infinity_not_empty have "{c::('e, 'f) float. is_finite c \<and> valof c \<ge> a} \<noteq> {}" by fast
    with extract_set_properties_closest show ?thesis by (smt (verit, del_insts))
  qed
  subgoal
  proof -
    from len_e threshold round_to_infinity_not_empty have "{c::('e, 'f) float. is_finite c \<and> valof c \<ge> a} \<noteq> {}" by fast
    with extract_set_properties_closest show ?thesis by (smt (verit, del_insts))
  qed
  done

lemma round_to_ninfinity:
  assumes threshold: "\<bar>a\<bar> \<le> largest TYPE(('e, 'f)float)"
    and len_e: "1 < LENGTH('e)"
  shows "valof ((IEEE.round To_ninfinity a)::('e, 'f) float) \<le> a"
    and "is_finite ((IEEE.round To_ninfinity a)::('e, 'f) float)"
  using round.simps round_to_ninfinity_not_empty assms extract_set_properties_closest_to_ninfinity apply auto
  done

lemma round_to_ninfinity_infinite:
  assumes len_e: "1 < LENGTH('e)"
  shows "extended_valof ((IEEE.round To_ninfinity a)::('e, 'f) float) \<le> a"
    and "\<not> is_nan ((IEEE.round To_ninfinity a)::('e, 'f) float)"
    subgoal
    proof (cases "\<bar>a\<bar> \<le> largest TYPE(('e, 'f)float)")
      case True
      with len_e round_to_ninfinity extended_valof_def show ?thesis
        by (metis ereal_less_eq(3) infinite_infinity(2) is_finite_uminus)
    next
      case False
      then consider "a > largest TYPE(('e, 'f)float)" | "a < - largest TYPE(('e, 'f)float)"
        by linarith
      then show ?thesis proof cases
        case 1
        with round.simps False have is_topfloat: "((round To_ninfinity a)::('e, 'f) float) = (topfloat::('e, 'f) float)"  
          by (smt (verit, ccfv_SIG) finite_topfloat float_val_ge_largest len_e valof_topfloat)
        then have  largest: "valof ((round To_ninfinity a)::('e, 'f) float) = largest TYPE(('e, 'f)float)"
          using len_e valof_topfloat by auto
        with 1 have comparison: "valof ((IEEE.round To_ninfinity a)::('e, 'f) float) \<le> a" 
          by fastforce
        from 1 False is_topfloat have "((IEEE.round To_ninfinity a)::('e, 'f) float) \<noteq> plus_infinity \<and> ((IEEE.round To_ninfinity a)::('e, 'f) float) \<noteq> minus_infinity"
          by (metis finite_topfloat infinite_infinity(1) infinite_infinity(2)) 
        with extended_valof_def comparison show ?thesis
          by (metis ereal_less_eq(3))
      next
        case 2
        with round.simps False have is_minfinity: "((round To_ninfinity a)::('e, 'f) float) = (minus_infinity::('e, 'f) float)" by simp
        with extended_valof_def have "extended_valof ((IEEE.round To_ninfinity a)::('e, 'f) float) = MInfty"
          by (metis float_neg_sign)
        then show ?thesis
          by (metis MInfty_eq_minfinity less_ereal.simps(5) order_less_imp_le) 
      qed
    qed
    unfolding round.simps
    subgoal
    proof (cases "\<bar>a\<bar> \<le> largest TYPE(('e, 'f)float)")
      case True
      with len_e round_to_ninfinity show ?thesis by fastforce
    next
      case False
      then consider "a > largest TYPE(('e, 'f)float)" | "a < - largest TYPE(('e, 'f)float)"
        by linarith
      then show ?thesis proof cases
        case 1
        with False round.simps have "((IEEE.round To_ninfinity a)::('e, 'f) float) = (topfloat::('e, 'f) float)"  
          by (smt (verit, ccfv_SIG) finite_topfloat float_val_ge_largest len_e valof_topfloat)
        then show ?thesis
          using finite_topfloat float_distinct_finite(1) by auto
      next
        case 2
        with round.simps False have "((round To_ninfinity a)::('e, 'f) float) = (minus_infinity::('e, 'f) float)" by simp
        then show ?thesis
          using float_distinct(1) infinity_is_infinity by auto
      qed
    qed
    done

lemma round_to_infinity:
  assumes threshold: "\<bar>a\<bar> \<le> largest TYPE(('e, 'f)float)"
    and len_e: "1 < LENGTH('e)"
  shows "valof ((IEEE.round To_pinfinity a)::('e, 'f) float) \<ge> a"
    and "is_finite ((IEEE.round To_pinfinity a)::('e, 'f) float)"
  using round.simps round_to_infinity_not_empty assms extract_set_properties_closest_to_infinity apply auto
  done

lemma round_to_infinity_infinite:
  assumes len_e: "1 < LENGTH('e)"
  shows "extended_valof ((IEEE.round To_pinfinity a)::('e, 'f) float) \<ge> a"
    and "\<not> is_nan ((IEEE.round To_pinfinity a)::('e, 'f) float)"
  subgoal
    proof (cases "\<bar>a\<bar> \<le> largest TYPE(('e, 'f)float)")
      case True
      with len_e round_to_infinity extended_valof_def show ?thesis
        by (metis ereal_less_eq(3) infinite_infinity(2) is_finite_uminus)
    next
      case False
      then consider "a > largest TYPE(('e, 'f)float)" | "a < - largest TYPE(('e, 'f)float)"
        by linarith
      then show ?thesis proof cases
        case 1
        with round.simps False have is_pinfinity: "((round To_pinfinity a)::('e, 'f) float) = (plus_infinity::('e, 'f) float)" 
          by (smt (verit, ccfv_SIG) finite_topfloat float_val_ge_largest len_e valof_topfloat)
        with extended_valof_def have "extended_valof ((IEEE.round To_pinfinity a)::('e, 'f) float) = PInfty"
          by metis
        then show ?thesis
          by (metis ereal_less_eq(1) infinity_ereal_def) 
      next
        case 2
        with round.simps False have is_bottomfloat: "((round To_pinfinity a)::('e, 'f) float) = - (topfloat::('e, 'f) float)"  
          by (smt (verit, ccfv_SIG) finite_topfloat float_val_ge_largest len_e valof_topfloat)
        then have  largest: "valof ((round To_pinfinity a)::('e, 'f) float) = - largest TYPE(('e, 'f)float)"
          using len_e bottomfloat_eq_m_largest by auto
        with 2 have comparison: "valof ((IEEE.round To_pinfinity a)::('e, 'f) float) \<ge> a" 
          by (metis linorder_not_less nle_le)
        from 2 False have "((IEEE.round To_pinfinity a)::('e, 'f) float) \<noteq> plus_infinity \<and> ((IEEE.round To_pinfinity a)::('e, 'f) float) \<noteq> minus_infinity"
          by (metis finite_bottomfloat infinite_infinity(1) infinite_infinity(2) is_bottomfloat)
        with extended_valof_def comparison show ?thesis
          by (metis ereal_le_le ereal_le_real)
      qed
    qed
    unfolding round.simps
    subgoal
    proof (cases "\<bar>a\<bar> \<le> largest TYPE(('e, 'f)float)")
      case True
      with len_e round_to_infinity show ?thesis by fastforce
    next
      case False
      then consider "a > largest TYPE(('e, 'f)float)" | "a < - largest TYPE(('e, 'f)float)"
        by linarith
      then show ?thesis proof cases
        case 1
        with round.simps False have is_pinfinity: "((round To_pinfinity a)::('e, 'f) float) = (plus_infinity::('e, 'f) float)" 
          by (smt (verit, ccfv_SIG) finite_topfloat float_val_ge_largest len_e valof_topfloat)
        with infinity_is_infinity have "is_infinity ((round To_pinfinity a)::('e, 'f) float)" by simp
        then show ?thesis
          using float_distinct(1) by force
      next
        case 2
        with round.simps False have is_bottomfloat: "((round To_pinfinity a)::('e, 'f) float) = - (topfloat::('e, 'f) float)"  
          by (smt (verit, ccfv_SIG) finite_topfloat float_val_ge_largest len_e valof_topfloat)
        then show ?thesis
          using float_distinct_finite(1) finite_bottomfloat by auto
      qed
    qed
    done

lemma ge_rounding_ge:
  assumes threshold_a: "\<bar>a\<bar> < threshold TYPE(('e, 'f)float)"
  and threshold_b: "\<bar>b\<bar> < threshold TYPE(('e, 'f)float)"
  and "a \<le> b"
shows "valof ((round To_nearest a)::('e, 'f) float) \<le> valof ((round To_nearest b)::('e, 'f) float)"
proof - 
  from threshold_b defloat_float_zerosign_round_finite is_finite_zerosign have fin_rounded_b: "is_finite ((round To_nearest b)::('e, 'f) float)" by blast
  from threshold_a have "((round To_nearest a)::('e, 'f) float) = (closest valof (\<lambda>a::('e, 'f) IEEE.float. even (fraction a)) (Collect is_finite) (a))" by auto
  with closest_is_closest is_finite_nonempty have "is_closest valof (Collect is_finite) (a) ((round To_nearest (a))::('e, 'f) float)" by metis 
  with assms fin_rounded_b bound_at_worst_lemma have dis_a_smaller: "\<bar>valof ((round To_nearest (a))::('e, 'f) float) - (a)\<bar> \<le> \<bar>(valof ((round To_nearest b)::('e, 'f) float)) - (a)\<bar>" by blast

  from threshold_a defloat_float_zerosign_round_finite is_finite_zerosign have fin_rounded_a: "is_finite ((round To_nearest a)::('e, 'f) float)" by blast
  from threshold_b have "((round To_nearest b)::('e, 'f) float) = (closest valof (\<lambda>a::('e, 'f) IEEE.float. even (fraction a)) (Collect is_finite) (b))" by auto
  with closest_is_closest is_finite_nonempty have "is_closest valof (Collect is_finite) (b) ((round To_nearest (b))::('e, 'f) float)" by metis 
  with assms fin_rounded_a bound_at_worst_lemma have dis_b_smaller: "\<bar>valof ((round To_nearest (b))::('e, 'f) float) - (b)\<bar> \<le> \<bar>(valof ((round To_nearest a)::('e, 'f) float)) - (b)\<bar>" by blast

  from dis_a_smaller dis_b_smaller assms(3) show ?thesis
    by (smt (verit, best))
qed

lemma ge_zero_rounding_ge_zero:
  assumes "(0::real) \<le> a"
  and "\<bar>a\<bar> < threshold TYPE(('e, 'f)float)"
shows "(0::real) \<le> valof ((round To_nearest a)::('e, 'f) float)"
  using zero_l_threshold valof_round_nearest_zero ge_rounding_ge assms abs_0 by metis 

lemma le_zero_rounding_le_zero:
  assumes "(0::real) \<ge> a"
  and "\<bar>a\<bar> < threshold TYPE(('e, 'f)float)"
shows "(0::real) \<ge> valof ((round To_nearest a)::('e, 'f) float)"
  using zero_l_threshold valof_round_nearest_zero ge_rounding_ge assms abs_0 by metis 

lemma addition_rounding_increases:
  assumes "a \<ge> 0"
  and len_e: "1 < LENGTH('e)"
    and threshold: "\<bar>(a + valof b)\<bar> < threshold TYPE(('e, 'f)float)"
    and "is_finite b"
  shows "valof ((round To_nearest (a + valof b))::('e, 'f) float) \<ge> valof (b::('e, 'f) float)"
proof-
  from threshold round.simps have "((round To_nearest (a + valof b))::('e, 'f) float) = (closest valof (\<lambda>a::('e, 'f) IEEE.float. even (fraction a)) (Collect is_finite) (a + valof b))"
    apply simp by linarith
  with closest_is_closest is_finite_nonempty have "is_closest valof (Collect is_finite) (a + valof b) ((round To_nearest (a + valof b))::('e, 'f) float)" by metis 
  with is_closest_def assms have "\<bar>valof ((round To_nearest (a + valof b))::('e, 'f) float) - (a + valof b)\<bar> \<le> \<bar>valof b - (a + valof b)\<bar>"
    by (meson bound_at_worst_lemma)
  with assms show "valof ((round To_nearest (a + valof b))::('e, 'f) float) \<ge> valof (b::('e, 'f) float)" by fastforce
qed

context 
begin
lift_definition exp_increase::"('e ,'f) float \<Rightarrow> ('e ,'f) float" is "\<lambda>(s, e, f). 
  (s, e+1::'e word, 0)" .

lemma rounding_bounds:
  assumes "round To_nearest a = (c::('e, 'f) float)"
  and "is_finite c"
shows "\<bar>a\<bar> < 2*2^exponent c / 2^(2 ^ (LENGTH('e) - 1) - 1)"
proof -
  from assms round.simps have threshold_bound: "\<bar>a\<bar> < threshold TYPE(('e, 'f) IEEE.float)"
    by (smt (verit, ccfv_threshold) infinite_infinity(1) infinite_infinity(2))
  {
    assume assm_a: "\<bar>a\<bar> \<ge> 2*2^exponent c / 2^(2 ^ (LENGTH('e) - 1) - 1)"
    then have "a \<noteq> 0" using two_realpow_ge_one
      using divide_le_0_iff by force
    assume assm_b: "exponent c < emax TYPE(('e, 'f) IEEE.float) - 1"
    then have "exponent c < 2^ LENGTH('e) - 1"
      by (simp add: emax_eq)
    then have ei_c_def: "sign c = sign (exp_increase c) \<and> fraction (exp_increase c) = 0 \<and> exponent (exp_increase c) = exponent c + 1" 
      apply (simp add: exp_increase.rep_eq sign.rep_eq fraction.rep_eq exponent.rep_eq Abs_float_inverse sign_def fraction_def exponent_def split: prod.splits)
      by (metis One_nat_def Suc_eq_plus1 less_diff_conv unat_add_lem' unsigned_1)
    with abs_valof_eq2 have "\<bar>valof (exp_increase c)\<bar> =
     2 ^ IEEE.exponent (exp_increase c) / 2 ^ bias TYPE(('e, 'f) IEEE.float)" by(simp add:abs_valof_eq2)
    with ei_c_def bias_def have valof_eic: "\<bar>valof (exp_increase c)\<bar> =
     2 * (2::real) ^ IEEE.exponent c / 2 ^ (2 ^ (LENGTH('e) - 1) - 1 )" by auto
    moreover from abs_valof_max bias_def have "\<bar>valof c\<bar> < 2 * (2::real) ^ IEEE.exponent c / 2 ^ (2 ^ (LENGTH('e) - 1) - 1 )" by metis
    ultimately have "\<bar>valof c\<bar> <  \<bar>valof (exp_increase c)\<bar>" by presburger

    then have p1: "\<bar>a - valof c\<bar> > \<bar>a - valof (exp_increase c)\<bar> \<or> \<bar>a - valof c\<bar> > \<bar>a - valof (-exp_increase c)\<bar> "
      using assm_a valof_eic
      apply(cases "a\<ge>0")
      by auto
    moreover from assm_b ei_c_def float_exp_le2 have "is_finite (exp_increase c) \<and> is_finite (-exp_increase c)" by force
    ultimately have "(is_finite (exp_increase c) \<and> \<bar>a - valof c\<bar> > \<bar>a - valof (exp_increase c)\<bar>) \<or> (is_finite (-exp_increase c) \<and> \<bar>a - valof c\<bar> > \<bar>a - valof (-exp_increase c)\<bar>)" by fast
    then have "\<exists>(b::('e, 'f) float).(is_finite b \<and> \<bar>a - valof c\<bar> > \<bar>a - valof b\<bar>)" by blast
    then have "\<not>(\<forall>(b::('e, 'f) float). b \<in> (Collect is_finite) \<longrightarrow> \<bar>valof c - a\<bar> \<le> \<bar>valof b - a\<bar>)" by fastforce
    with assms closest_def round.simps have "False" 
      using threshold_bound bound_at_worst_lemma by blast
  }
  moreover {
    assume assm_a: "\<bar>a\<bar> \<ge> 2*2^exponent c / 2^(2 ^ (LENGTH('e) - 1) - 1)"
    then have "a \<noteq> 0" using two_realpow_ge_one
      using divide_le_0_iff by force
    assume assm_b: "exponent c \<ge> emax TYPE(('e, 'f) IEEE.float) - 1"
    with assms float_exp_le2 float_exp_le have "exponent c = emax TYPE(('e, 'f) IEEE.float) - 1" by force
    with threshold_def bias_def have threshold_expanded: "threshold TYPE(('e, 'f) IEEE.float) = 
      (2::real) ^ (exponent c) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat)) *
    ((2::real) - (1::real) / (2::real) ^ Suc LENGTH('f))" by metis
    
    have "((2::real) - (1::real) / (2::real) ^ Suc LENGTH('f)) < 2" by simp
    moreover have "(2::real) ^ (exponent c) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat)) > 0" by force
    ultimately have "(2::real) ^ (exponent c) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat)) *
    ((2::real) - (1::real) / (2::real) ^ Suc LENGTH('f)) < (2::real) ^ (exponent c) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat)) *
    2" using mult_strict_right_mono 
      by (metis mult.commute)
    with threshold_expanded have "threshold TYPE(('e, 'f) IEEE.float) < 2*2^exponent c / 2^(2 ^ (LENGTH('e) - 1) - 1)" by simp
    with assm_a have "threshold TYPE(('e, 'f) IEEE.float) < \<bar>a\<bar>" by argo
    with threshold_bound have "False" by argo
  }
  ultimately show ?thesis by fastforce
qed
end

lemma rounding_multiplication_exponent:
  assumes "round To_nearest (valof (a::('e, 'f) float) * valof (b::('e, 'f) float)) = (c::('e, 'f) float)"
  and "is_finite c"  
  and "exponent a \<noteq> 0" and "exponent b \<noteq> 0"
  and "exponent c + bias TYPE(('e, 'f) IEEE.float) = exponent a + exponent b"
shows "fraction a + fraction b < 2^LENGTH('f)"
proof -
  from assms have "\<bar>valof a * valof b\<bar> = (2 ^ (exponent a) / 2 ^ bias TYPE(('e, 'f) IEEE.float)) * (1 + (fraction a) / 2 ^ LENGTH('f)) * (2 ^ (exponent b) / 2 ^ bias TYPE(('e, 'f) IEEE.float)) * (1 + (fraction b) / 2 ^ LENGTH('f))" by(simp add:abs_valof_eq abs_mult)
  with assms rounding_bounds bias_def have "(2 ^ (exponent a) / 2 ^ bias TYPE(('e, 'f) IEEE.float)) * (1 + (fraction a) / 2 ^ LENGTH('f)) * 
      (2 ^ (exponent b) / 2 ^ bias TYPE(('e, 'f) IEEE.float)) * (1 + (fraction b) / 2 ^ LENGTH('f)) <
      2*2^exponent c / 2^bias TYPE(('e, 'f) IEEE.float)" by metis
  then have "(2 ^ (exponent a) / 2 ^ bias TYPE(('e, 'f) IEEE.float)) * (1 + (fraction a) / 2 ^ LENGTH('f)) * 
      (2 ^ (exponent b)) * (1 + (fraction b) / 2 ^ LENGTH('f)) / 2^bias TYPE(('e, 'f) IEEE.float) <
      2*2^exponent c / 2^bias TYPE(('e, 'f) IEEE.float)" by simp
  then have step1: "(2 ^ (exponent a) / 2 ^ bias TYPE(('e, 'f) IEEE.float)) * (1 + (fraction a) / 2 ^ LENGTH('f)) *
      (2 ^ (exponent b)) * (1 + (fraction b) / 2 ^ LENGTH('f)) <
      2*2^exponent c" using zero_less_power divide_less_cancel[where c="2^bias TYPE(('e, 'f) IEEE.float)"] by fastforce
  
  from assms have "(2::real)^(exponent c + bias TYPE(('e, 'f) IEEE.float)) = (2::real) ^ (exponent a) * (2::real)^(exponent b)" by(simp add:power_add)
  moreover have "(2::real)^(exponent c + bias TYPE(('e, 'f) IEEE.float)) = (2::real)^(exponent c)* (2::real)^( bias TYPE(('e, 'f) IEEE.float))" by(simp add:power_add)
  ultimately have "(2::real)^(exponent c) = (2::real) ^ (exponent a) * (2::real)^(exponent b) / (2::real)^( bias TYPE(('e, 'f) IEEE.float))" by (simp add: eq_divide_imp)
  with step1 have "(1 + (fraction a) / 2 ^ LENGTH('f)) * (1 + (fraction b) / 2 ^ LENGTH('f)) < 2" by(simp add:divide_less_cancel mult_less_cancel_right)
  then have "(fraction a) / 2 ^ LENGTH('f) + (fraction b) / 2 ^ LENGTH('f) + (fraction a) / 2 ^ LENGTH('f)*(fraction b) / 2 ^ LENGTH('f) < 1" by argo
  moreover have "1 \<le> 1+ (fraction a) / 2 ^ LENGTH('f)*(fraction b) / 2 ^ LENGTH('f)" by simp
  ultimately have "(fraction a) / 2 ^ LENGTH('f) + (fraction b) / 2 ^ LENGTH('f) + (fraction a) / 2 ^ LENGTH('f)*(fraction b) / 2 ^ LENGTH('f) < 1 + (fraction a) / 2 ^ LENGTH('f)*(fraction b) / 2 ^ LENGTH('f)" by argo
  then have "(fraction a) / 2 ^ LENGTH('f) + (fraction b) / 2 ^ LENGTH('f) < 1" by simp
  then have "(fraction a + fraction b) / 2 ^ LENGTH('f) < 1" by (simp add: add_divide_distrib)
  then have "(fraction a + fraction b) * 2 ^ LENGTH('f)/ 2 ^ LENGTH('f) < 2 ^ LENGTH('f)" by (simp add: mult_less_cancel_right)
  then show "(fraction a) + (fraction b) < 2 ^ LENGTH('f)" apply(simp add: divide_self[where a="2 ^ LENGTH('f)"])
    by (metis of_nat_add of_nat_less_imp_less power_2_simp)
qed

lemma rounding_multiplication_exponent_ge:
  assumes "round To_nearest (valof (a::('e, 'f) float) * valof (b::('e, 'f) float)) = (c::('e, 'f) float)"
  and "is_finite c"  
  and norm_a: "exponent a \<noteq> 0" and norm_b: "exponent b \<noteq> 0"
shows "exponent c + bias TYPE(('e, 'f) IEEE.float) \<ge> exponent a + exponent b"
   proof -
    from norm_a abs_valof_min[where x=a] have step1: "\<bar>valof a\<bar> * \<bar>valof b\<bar> \<ge> (2::real) ^ exponent a / 2 ^ bias TYPE(('e, 'f) float) * \<bar>valof b\<bar>"
      using mult_le_cancel_right[where a="\<bar>valof a\<bar>" and b="2 ^ exponent a / 2 ^ bias TYPE(('e, 'f) IEEE.float)" and c="\<bar>valof b\<bar>"] by auto
    have "0 < (2::real) ^ IEEE.exponent a / 2 ^ bias TYPE(('e, 'f) IEEE.float)" by simp
    with norm_b abs_valof_min[where x=b] have "(2::real) ^ exponent a / 2 ^ bias TYPE(('e, 'f) float) * \<bar>valof b\<bar> \<ge> 2 ^ exponent a / 2 ^ bias TYPE(('e, 'f) float) * 2 ^ exponent b / 2 ^ bias TYPE(('e, 'f) float)"
      using mult_le_cancel_left[where c="(2::real) ^ exponent a / 2 ^ bias TYPE(('e, 'f) float)" and b="\<bar>valof b\<bar>" and a="(2::real) ^ exponent b / 2 ^ bias TYPE(('e, 'f) float)"] by argo
    with step1 have "\<bar>valof a\<bar> * \<bar>valof b\<bar> \<ge> 2 ^ exponent a / 2 ^ bias TYPE(('e, 'f) float) * 2 ^ exponent b / 2 ^ bias TYPE(('e, 'f) float)" by argo

    moreover from rounding_bounds assms have "\<bar>valof a * valof b\<bar> < (2::real) * (2::real) ^ IEEE.exponent c /
      2 ^ bias TYPE(('e, 'f) float)" apply(simp add:bias_def) by blast
    ultimately have "2 ^ exponent a / 2 ^ bias TYPE(('e, 'f) float) * 2 ^ exponent b / 2 ^ bias TYPE(('e, 'f) float) < (2::real) * (2::real) ^ IEEE.exponent c / 2 ^ bias TYPE(('e, 'f) float)
      " by linarith
    then have "2 ^ exponent a / 2 ^ bias TYPE(('e, 'f) float) * 2 ^ exponent b < (2::real) * (2::real) ^ IEEE.exponent c" using divide_less_cancel[where c="2 ^ bias TYPE(('e, 'f) float)"] by fastforce
    then have "2 ^ exponent a * 2 ^ exponent b < (2::real) * (2::real) ^ exponent c * 2 ^ bias TYPE(('e, 'f) float)"
      by (simp add: divide_less_eq)
    then have "2 ^ (exponent a + exponent b) < (2::real) ^ (1 + exponent c + bias TYPE(('e, 'f) float))" by(simp add:power_add)
    then have "exponent a + exponent b < 1 + exponent c + bias TYPE(('e, 'f) float)" using power_strict_increasing_iff[where b="(2::real)"] by fastforce
    then show "exponent a + exponent b \<le> exponent c + bias TYPE(('e, 'f) float)" by auto
  qed

end