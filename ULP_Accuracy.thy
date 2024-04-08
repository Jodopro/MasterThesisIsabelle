theory ULP_Accuracy
imports ULP_Parts
begin

definition ulp_accuracy_expanded :: "real \<Rightarrow> ('e, 'f) float \<Rightarrow> real \<Rightarrow> bool" 
  where "ulp_accuracy_expanded a c u \<equiv> (is_finite c) \<and> \<bar>(valof c - a)\<bar> \<le> u * 2^(max (exponent c) 1) / 2^(2^(LENGTH('e) - 1) - 1 + LENGTH('f)) "

definition ulp_accuracy :: "real \<Rightarrow> ('e, 'f) float \<Rightarrow> real \<Rightarrow> bool" 
  where "ulp_accuracy a c u \<equiv> (is_finite c) \<and> \<bar>(valof c - a)\<bar> \<le> u * (ulp c)"

lemma rounding_threshold:
  assumes "\<bar>a\<bar> < threshold TYPE(('e, 'f)float)" 
  shows "((round To_nearest a)::('e, 'f) float) = closest (valof) (\<lambda>b. even (fraction b)) {b. is_finite b} a"
  unfolding round.simps
  using assms by auto
  
lemma rounded_threshold_is_finite: 
  assumes "\<bar>a\<bar> < threshold TYPE(('e, 'f)float)"
  shows "is_finite ((round To_nearest a)::('e, 'f) float)"
  using assms apply (simp add:rounding_threshold)
  using is_finite_nonempty extract_set_properties_closest rounding_threshold by auto

lemma rounded_threshold_is_closest: 
  assumes "\<bar>a\<bar> < threshold TYPE(('e, 'f)float)"
  shows "is_closest (\<lambda>b. valof b) {b. is_finite b} a ((round To_nearest a)::('e, 'f) float)"
  using assms apply (simp add:rounding_threshold  del: round.simps)
  using is_finite_nonempty closest_is_closest[where v=valof and s="{b. is_finite b}" and x=a and p="(\<lambda>b. even (fraction b))"] by fast

lemma power_exponent_div:
  shows "(2::real) ^ (a + b) /
         (2::real) ^ (c + b) =
         (2::real) ^ (a) /
         (2::real) ^ (c) 
        "
  by(simp add: power_add)

lemma ulp_equivelance:
  shows "ulp (c::('e, 'f) float) = 2^(max (exponent c) 1) / 2^(2^(LENGTH('e) - 1) - 1 + LENGTH('f))"
  unfolding ulp_def
  apply (simp add: valof_eq2 one_lp_parts zero_lp_parts del:round.simps)
  apply (auto simp add: bias_def)
  using power_exponent_div One_nat_def apply(simp_all add: ulp_divisor_rewrite power_add add_divide_distrib factor_minus distrib_left )
  using Nat.diff_add_assoc2 less_eq_Suc_le nat_one_le_power pos2
  by (metis power_add power_exponent_div)

lemma ulp_uminus[simp]:
  shows "ulp (-x) = ulp x"
  by(simp add:ulp_equivelance)

lemma exp_e_ulp_e:
  assumes "exponent (a::('e, 'f) float) = exponent (b::('e, 'f) float)"
  shows "ulp a = ulp b"
  using assms by(simp add:ulp_equivelance )

lemma exp_ge_ulp_ge:
  assumes "exponent (a::('e, 'f) float) \<ge> exponent (b::('e, 'f) float)"
  shows "ulp a \<ge> ulp b"
  using assms apply(simp add:ulp_equivelance )
  apply(rule divide_right_mono)
  by simp_all

lemma ulp_increase_bigger_ulp:
  assumes "is_finite c"
  shows "ulp (c::('e,'f) float) \<le>  ulp (ulp_increase c)"
  apply(cases "fraction c \<noteq> 2^LENGTH('f) - 1")
  using assms  by (auto simp add:ulp_increase_exp exp_ge_ulp_ge)

lemma ulp_accuracy_equivelance:
  shows "ulp_accuracy a c u = ulp_accuracy_expanded a c u"
  unfolding ulp_accuracy_def ulp_accuracy_expanded_def 
  by (simp add: ulp_equivelance)

lemma distrib_left_real_reverse:
  "(a::real) * b - a * c = a * (b - c)"
  by argo

lemma diff_1_ulp_helper1:
  assumes "d>0"
  shows "(\<bar>(a::real)/d - b/d\<bar> \<le> c/d) \<longleftrightarrow> \<bar>a-b\<bar>\<le>c" 
  using assms
  by (metis abs_div_pos diff_divide_distrib divide_le_cancel divide_less_cancel verit_comp_simplify1(3))

lemma diff_1_ulp:
  assumes "is_finite (a::('e, 'f) float)" "is_finite (b::('e, 'f) float)" "exponent a = exponent b" "sign a = sign b" and "fraction a = fraction b + 1"
  shows "ulp_accuracy (valof a) b 1"
  apply (simp add: ulp_accuracy_equivelance)
  unfolding ulp_accuracy_expanded_def fraction_def
  using assms apply (simp add:valof_eq2)
  apply(cases "exponent b = 0")
  apply(simp_all add: bias_def)
   apply(simp_all add:ulp_divisor_rewrite diff_1_ulp_helper1)
  by(simp_all add:distrib_left_real_reverse abs_pow_min_1)


lemma ulp_increase_helper1: "1 + (x::real) / 2 ^ (f::nat) = (2 ^ f + x) / 2 ^ f" 
  by (simp add: add_divide_distrib)

lemma ulp_increase_helper3: "(f1::real) * f3 / d -
      f2 * f4 / d = 
      (f1*f3 - f2*f4) / d"
  by argo

lemma ulp_increase_helper4: "x * (f1::real) * f3 -
      x * f2 * f4 = 
      x * (f1*f3 - f2*f4)"
  by argo

lemma ulp_increase_helper2: "x * ((f1::real) + f2) = 
      x * f1 + x * f2"
  by argo

lemma ulp_increase_helper5: "x * ((f1::real) - f2) = 
      x * f1 - x * f2"
  by argo


lemma ulp_increase_diff:
  assumes "is_finite (x::('e, 'f) float)"
  shows "\<bar>valof (ulp_increase (x::('e, 'f) float)) - valof x\<bar> = ulp x"
  apply(cases "fraction x = 2^LENGTH('f) - 1")
  using assms  apply (simp_all add: valof_eq ulp_increase_exp ulp_increase_sign ulp_equivelance)
   apply(simp_all add: bias_def ulp_increase_helper1)
   apply(simp_all add:ulp_divisor_rewrite ulp_divisor_rewrite')
   apply(simp_all add:ulp_increase_helper3 ulp_increase_helper4 abs_pow_min_1)
  apply(simp_all add:ulp_increase_frac)
   apply(simp_all add:ulp_increase_helper2)
proof -
  have "2 ^ LENGTH('f) \<ge> (1::nat)" by simp
  then have all_x: "\<forall>x. x * real (2 ^ LENGTH('f) - Suc 0) = x*2 ^ LENGTH('f) - x"
    by (simp add: factor_minus of_nat_diff)
  from all_x have x_2: "2 * 2 ^ LENGTH('f) - 2 * real (2 ^ LENGTH('f) - Suc 0) = 2" by simp
  from all_x have x_exp: "2 ^ IEEE.exponent x * 2 ^ LENGTH('f) - 2 ^ IEEE.exponent x * real (2 ^ LENGTH('f) - Suc 0) = 2 ^ IEEE.exponent x" by simp
  from x_2 x_exp show "(IEEE.exponent x = 0 \<longrightarrow> 2 * 2 ^ LENGTH('f) - 2 * real (2 ^ LENGTH('f) - Suc 0) = 2) \<and>
    (0 < IEEE.exponent x \<longrightarrow> 2 ^ IEEE.exponent x * 2 ^ LENGTH('f) - 2 ^ IEEE.exponent x * real (2 ^ LENGTH('f) - Suc 0) = 2 ^ IEEE.exponent x)" by fastforce
qed

lemma ulp_increase_abs_diff:
  assumes "is_finite (x::('e, 'f) float)"
  shows "\<bar>valof (ulp_increase (x::('e, 'f) float))\<bar> - \<bar>valof x\<bar> = ulp x"
  apply(cases "fraction x = 2^LENGTH('f) - 1")
  using assms  apply (simp_all add: abs_valof_eq2 ulp_increase_exp ulp_increase_sign ulp_equivelance)
   apply(simp_all add: bias_def ulp_increase_helper1)
   apply(simp_all add:ulp_divisor_rewrite ulp_divisor_rewrite')
   apply(simp_all add:ulp_increase_helper3 ulp_increase_helper4 abs_pow_min_1)
  apply(simp_all add:ulp_increase_frac)
   apply(simp_all add:ulp_increase_helper2)
  apply(simp_all add:ulp_increase_helper3)
proof -
  have "2 ^ LENGTH('f) \<ge> (1::nat)" by simp
  then have all_x: "\<forall>x. x * real (2 ^ LENGTH('f) - Suc 0) = x*2 ^ LENGTH('f) - x"
    by (simp add: factor_minus of_nat_diff)
  from all_x have x_2: "2 * 2 ^ LENGTH('f) - 2 * real (2 ^ LENGTH('f) - Suc 0) = 2" by simp
  from all_x have x_exp: "2 ^ IEEE.exponent x * 2 ^ LENGTH('f) - 2 ^ IEEE.exponent x * real (2 ^ LENGTH('f) - Suc 0) = 2 ^ IEEE.exponent x" by simp
  from x_2 x_exp show "(IEEE.exponent x = (0::nat) \<longrightarrow> (2::real) * (2::real) ^ LENGTH('f) - (2::real) * real ((2::nat) ^ LENGTH('f) - Suc (0::nat)) = (2::real)) \<and>
    ((0::nat) < IEEE.exponent x \<longrightarrow>
     (2::real) ^ IEEE.exponent x * (2::real) ^ LENGTH('f) - (2::real) ^ IEEE.exponent x * real ((2::nat) ^ LENGTH('f) - Suc (0::nat)) =
     (2::real) ^ IEEE.exponent x)" by fastforce
qed

lemma real_mult:
  shows "real (x*y) = x*real y"
  by auto

lemma f_min_1:
  assumes "f \<ge> 1"
  shows "x*real ((f::nat) - Suc (0::nat)) = x*f - x"
  using assms apply auto
  by (simp add: factor_minus of_nat_diff)

lemma pow_f_min_1:
  assumes "f \<ge> 1"
  shows "2*2^ ((f::nat) - Suc (0::nat)) = 2^f"
  using assms apply auto
  apply (induction f)
  by auto

lemma sign_increase_ulp_bigger:
  assumes "sign (x::('e, 'f) float) = 0"
  and "is_finite x"
  shows "valof x < valof (ulp_increase x)"
  apply(cases "fraction x = 2^LENGTH('f) - 1")
  using assms  apply (simp_all add: valof_eq ulp_increase_exp ulp_increase_sign ulp_equivelance)
  apply(simp_all add: bias_def ulp_increase_helper1)
   apply(simp_all add:ulp_divisor_rewrite ulp_divisor_rewrite')
  apply(simp_all add:ulp_increase_frac)
   apply(simp_all add:ulp_increase_helper2)
   apply(simp_all add:divide_strict_right_mono divide_less_cancel)
subgoal proof -
  have "(2::real) * real ((2::nat) ^ LENGTH('f) - Suc (0::nat)) < (2::real) * (2::nat) ^ LENGTH('f)" by simp
  then have "(2::real) * real ((2::nat) ^ LENGTH('f) - Suc (0::nat)) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))
    < (2::real) * (2::nat) ^ LENGTH('f) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))"
    by (simp add: divide_strict_right_mono) 
  then have "(2::real) * real ((2::nat) ^ LENGTH('f) - Suc (0::nat)) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))
    < (2::real) * (2::nat) ^ LENGTH('f) / ((2::nat) ^ LENGTH('f) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) - Suc (0::nat))) " using ulp_divisor_rewrite'
    by fastforce
  then show ?thesis by force
qed
  done

lemma ulp_0_5_exists0:
  assumes "(a::real) \<ge> 0" 
    and "\<bar>a\<bar> < largest TYPE(('e, 'f)float)" 
  and "ulp_accuracy a (c::('e, 'f) float) \<bar>x\<bar>"
  and "valof c \<le> a"
  and "sign c = 0"
  and "1 < LENGTH('e)"
shows "(valof (ulp_increase c) \<le> a \<and> ulp_accuracy a (ulp_increase c) \<bar>x-1\<bar>) \<or> (valof (ulp_increase c) > a \<and> (\<exists>f::('e, 'f) float. ulp_accuracy a f 0.5))"
  apply(cases "valof (ulp_increase c) \<le> a")
  subgoal
  proof -
    from ulp_increase_diff assms ulp_accuracy_def have diff_is_ulp: "\<bar>valof (ulp_increase c) - valof c\<bar> = ulp c" by blast
    with sign_increase_ulp_bigger assms have tmp1: "valof (ulp_increase c) - valof c = ulp c"
      by (metis abs_of_pos diff_gt_0_iff_gt ulp_accuracy_def)
    from assms ulp_accuracy_def have c_a_diff: "\<bar> valof c - a\<bar> \<le> \<bar>x\<bar> * ulp c" by fast
    with assms have "a - valof c \<le> \<bar>x\<bar> * ulp c" by force
    then have v_c: "valof c \<ge> a- \<bar>x\<bar> * ulp c" by argo
    from tmp1 assms c_a_diff have "valof (ulp_increase c) \<le> a \<Longrightarrow> \<bar>valof (ulp_increase c) - a\<bar> \<le> \<bar>x\<bar> * ulp c - ulp c" by fastforce
    then have ulp_distance: "valof (ulp_increase c) \<le> a \<Longrightarrow> \<bar>valof (ulp_increase c) - a\<bar> \<le> \<bar>(x-1)\<bar> * ulp c"
      by (smt (verit, ccfv_SIG) diff_is_ulp left_diff_distrib' mult_le_cancel_right2)
    from ulp_increase_bigger_ulp assms ulp_accuracy_def have "ulp c \<le>  ulp (ulp_increase c)" by blast
    with ulp_distance have ulp_increase_distance: "valof (ulp_increase c) \<le> a \<Longrightarrow> \<bar>valof (ulp_increase c) - a\<bar> \<le> \<bar>x-1\<bar> * ulp (ulp_increase c)" 
      by (smt (verit) diff_gt_0_iff_gt mult_le_cancel_left)
    from assms ulp_increase_sign valof_nonneg have "valof (ulp_increase c) \<le> a \<Longrightarrow> \<bar>valof (ulp_increase c) \<bar> < largest TYPE(('e, 'f)float)"
      by (metis abs_of_nonneg dual_order.strict_trans2)
    then have  "valof (ulp_increase c) \<le> a \<Longrightarrow> \<bar>valof (ulp_increase c) \<bar> < threshold TYPE(('e, 'f)float)" using largets_l_threshold
      using order_less_trans by blast
    with threshold_finite have "valof (ulp_increase c) \<le> a \<Longrightarrow> is_finite (ulp_increase c) " by blast
    with ulp_accuracy_def ulp_increase_distance have "valof (ulp_increase c) \<le> a \<Longrightarrow> ulp_accuracy a (ulp_increase c) \<bar>x - (1::real)\<bar>" by fast
    then show "valof (ulp_increase c) \<le> a \<Longrightarrow>
    valof (ulp_increase c) \<le> a \<and> ulp_accuracy a (ulp_increase c) \<bar>x - (1::real)\<bar> \<or>
    a < valof (ulp_increase c) \<and> (\<exists>f::('e, 'f) IEEE.float. ulp_accuracy a f ((5::real) / (10::real)))" by blast 
  qed
  subgoal
  proof -
    from assms ulp_accuracy_def have fin_c: "is_finite c" by blast

    from ulp_increase_diff assms ulp_accuracy_def have "\<bar>valof (ulp_increase c) - valof c\<bar> = ulp c" by blast
    with sign_increase_ulp_bigger assms have tmp1: "valof (ulp_increase c) - valof c = ulp c"
      by (metis abs_of_pos diff_gt_0_iff_gt ulp_accuracy_def)
    then have ulp_distance_a_bigger: "a-valof c > 0.5 * ulp c \<Longrightarrow> \<not> valof (ulp_increase c) \<le> a \<Longrightarrow> \<bar>valof (ulp_increase c) - a\<bar> \<le> 0.5 * ulp c" by argo
    from ulp_increase_bigger_ulp assms ulp_accuracy_def have "ulp c \<le>  ulp (ulp_increase c)" by blast
    with ulp_distance_a_bigger have ulp_increase_diff: "a-valof c > 0.5 * ulp c \<Longrightarrow> \<not> valof (ulp_increase c) \<le> a \<Longrightarrow> \<bar>valof (ulp_increase c) - a\<bar> \<le> 0.5 * ulp (ulp_increase c)" by fastforce

    from assms threshold_finite have l_is_finite: "valof (ulp_increase c) < threshold TYPE(('e, 'f)float) \<Longrightarrow> is_finite (ulp_increase c)"
      by (metis abs_of_nonneg ulp_increase_sign valof_nonneg)
    from largets_l_threshold have "valof (ulp_increase c) \<ge> threshold TYPE(('e, 'f)float) \<Longrightarrow> valof (ulp_increase c) > largest TYPE(('e, 'f)float) " apply(rule order_less_le_trans) by blast
    with assms have g_topfloat: "valof (ulp_increase c) \<ge> threshold TYPE(('e, 'f)float) \<Longrightarrow> valof (ulp_increase c) > valof (topfloat::('e, 'f)float)" by(simp add:valof_topfloat)
    from assms valof_nonneg have "valof c < largest TYPE(('e, 'f)float)" by linarith
    with assms have "valof c < valof (topfloat::('e, 'f)float)" by(simp add:valof_topfloat)
    with g_topfloat nothing_between_ulp_increase fin_c have "valof (ulp_increase c) \<ge> threshold TYPE(('e, 'f)float) \<Longrightarrow>False"
      using assms(5) linorder_not_less by auto
    with l_is_finite have "is_finite (ulp_increase c)" by fastforce
    with ulp_increase_diff ulp_accuracy_def have ulp_accuracy_increase: "a-valof c > 0.5 * ulp c \<Longrightarrow> \<not> valof (ulp_increase c) \<le> a \<Longrightarrow> ulp_accuracy a (ulp_increase c) 0.5" by blast

    from assms have "a-valof c \<le> 0.5 * ulp c \<Longrightarrow> ulp_accuracy a c 0.5" by(simp add: ulp_accuracy_def)
    with ulp_accuracy_increase have "\<not> valof (ulp_increase c) \<le> a \<Longrightarrow> (\<exists>f::('e, 'f) float. ulp_accuracy a f (5 / 10))" by force
    then show "\<not> valof (ulp_increase c) \<le> a \<Longrightarrow>
    valof (ulp_increase c) \<le> a \<and> ulp_accuracy a (ulp_increase c) \<bar>x - (1::real)\<bar> \<or>
    a < valof (ulp_increase c) \<and> (\<exists>f::('e, 'f) IEEE.float. ulp_accuracy a f ((5::real) / (10::real)))" by argo
   qed
  done

lemma ulp_positive: "ulp x > 0" 
  unfolding ulp_def one_lp_parts zero_lp_parts valof_eq
  apply(cases "exponent x = 0")
   apply simp_all
  by (simp add: pos_divide_less_eq)

lemma ulp_accuracy_non_negative: "ulp_accuracy a b x \<longrightarrow> x \<ge> 0" 
  unfolding ulp_accuracy_def
  using ulp_positive
  by (metis abs_ge_zero dual_order.trans verit_comp_simplify1(3) zero_le_mult_iff)

lemma ulp_accuracy_zero:
  assumes "x \<ge> 0"
  shows "ulp_accuracy 0 0 x"
  apply(simp add:ulp_accuracy_def finite_zero )
  using ulp_positive assms mult_nonneg_nonneg
  by (metis less_eq_real_def)

lemma ulp_accuracy_widen:
  assumes "ulp_accuracy a (b::('e, 'f) float) x" "y > x"
  shows "ulp_accuracy a b y"
  using assms ulp_positive unfolding ulp_accuracy_def apply simp
  by (smt (verit) mult_right_less_imp_less ulp_positive)


lemma ulp_0_5_exists1:
  assumes a1: "(a::real) \<ge> 0" 
    and a2: "\<bar>a\<bar> < largest TYPE(('e, 'f)float)" 
  and a3: "ulp_accuracy a (c::('e, 'f) float) \<bar>x\<bar>"
  and a4: "valof c \<le> a"
  and a5: "sign c = 0"
  and a6: "1 < LENGTH('e)"
  shows "((y::nat) - 0.5 \<le> x \<and> (y+0.5) > x \<and> ulp_accuracy a (b::('e, 'f) float) \<bar>x\<bar> \<and> valof b \<le> a \<and> sign b = 0 \<longrightarrow> (\<exists>(b::('e, 'f) float). ulp_accuracy a b 0.5))"
proof(induction y arbitrary: x b)
  case 0
  then show ?case using ulp_accuracy_widen
    by (smt (verit) semiring_1_class.of_nat_0)
next
  case (Suc y)
  have implied_from_idk_helper: "real (Suc (y::nat)) - (5::real) / (10::real) \<le> (x::real) \<and>
  x < real (Suc y) + (5::real) / (10::real) \<and> ulp_accuracy (a::real) (b::('e, 'f) IEEE.float) \<bar>x\<bar> \<and> valof b \<le> a \<and> sign b = (0::nat) \<longrightarrow> (valof (ulp_increase b) \<le> a \<and> ulp_accuracy a (ulp_increase b) \<bar>x-1\<bar>) \<or> (valof (ulp_increase b) > a \<and> (\<exists>f::('e, 'f) float. ulp_accuracy a f 0.5))" 
    using ulp_0_5_exists0 assms by blast
  
  from implied_from_idk_helper have ulp_increase_exists: "real (Suc y) - (5::real) / (10::real) \<le> x \<and> x < real (Suc y) + (5::real) / (10::real) \<and> ulp_accuracy (a::real) (b::('e, 'f) IEEE.float) \<bar>x\<bar> \<and> valof b \<le> a \<and> sign b = (0::nat) \<longrightarrow> valof (ulp_increase b) \<le> a \<longrightarrow> ulp_accuracy a (ulp_increase b) \<bar>x-1\<bar>" by linarith
  then obtain b2 where b2_exists: "b2 = (ulp_increase b)" by blast
  from Suc have "real (y::nat) - (5::real) / (10::real) \<le> ((x-1)::real) \<and>
  (x-1) < real y + (5::real) / (10::real) \<and> ulp_accuracy (a::real) b2 \<bar>(x-1)\<bar> \<and> valof b2 \<le> a \<and> sign b2 = (0::nat) \<longrightarrow>
  (\<exists>b::('e, 'f) IEEE.float. ulp_accuracy a b ((5::real) / (10::real)))" by blast
  with b2_exists ulp_increase_sign have "real (y::nat) - (5::real) / (10::real) \<le> ((x-1)::real) \<and>
  (x-1) < real y + (5::real) / (10::real) \<and> ulp_accuracy (a::real) b2 \<bar>(x-1)\<bar> \<and> valof b \<le> a \<and> sign b = (0::nat) \<longrightarrow> valof (ulp_increase b) \<le> a \<longrightarrow>
  (\<exists>b::('e, 'f) IEEE.float. ulp_accuracy a b ((5::real) / (10::real)))" by metis
    
  then have with_Suc: "real (Suc y::nat) - (5::real) / (10::real) \<le> (x::real) \<and>
  x < real (Suc y) + (5::real) / (10::real) \<and> ulp_accuracy (a::real) b2 \<bar>(x-1)\<bar> \<and> valof b \<le> a \<and> sign b = (0::nat) \<longrightarrow> valof (ulp_increase b) \<le> a \<longrightarrow>
  (\<exists>b::('e, 'f) IEEE.float. ulp_accuracy a b ((5::real) / (10::real)))" by fastforce
  then have "real (Suc y) - (5::real) / (10::real) \<le> x \<and> x < real (Suc y) + (5::real) / (10::real) \<and> ulp_accuracy a b \<bar>x\<bar> \<and> valof b \<le> a \<and> sign b = (0::nat) \<longrightarrow> (\<exists>b::('e, 'f) IEEE.float. ulp_accuracy a b ((5::real) / (10::real)))"
    using b2_exists ulp_increase_exists
    using implied_from_idk_helper by blast

  then show ?case by blast
qed

lemma distance_threshold_largets:
  assumes "1 < LENGTH('e)"
  shows "threshold TYPE(('e, 'f)float) - largest TYPE(('e, 'f)float) = 0.5 * ulp (topfloat::('e, 'f) float)"
  apply(simp add: threshold_def largest_def right_diff_distrib ulp_equivelance float_defs(29))
  apply(simp add: bias_def ulp_divisor_rewrite)
  apply(simp add: emax_def unat_minus_one_word) 
proof -
  from assms have "(2::nat) < (2::nat) ^ LENGTH('e)"
    by (metis n_less_equal_power_2 power_one_right power_strict_increasing_iff)
  then show "(2::nat) ^ LENGTH('e) - Suc (Suc (0::nat)) = max ((2::nat) ^ LENGTH('e) - Suc (Suc (0::nat))) (Suc (0::nat))" by fastforce
qed

lemma ulp_0_5_exists_threshold:
  assumes a1: "(a::real) \<ge> 0" 
    and a2: "\<bar>a\<bar> \<ge> largest TYPE(('e, 'f)float)" 
    and a3: "\<bar>a\<bar> < threshold TYPE(('e, 'f)float)"
    and a4: "1 < LENGTH('e)"
  shows "(\<exists>(b::('e, 'f) float). ulp_accuracy a b 0.5)"
proof -
  from assms have "\<bar>largest TYPE(('e, 'f)float) - a\<bar> \<le> threshold TYPE(('e, 'f)float) - largest TYPE(('e, 'f)float)" by simp
  with assms distance_threshold_largets have "\<bar>largest TYPE(('e, 'f)float) - a\<bar> \<le> 0.5 * ulp (topfloat::('e, 'f) float)" by metis
  then have "ulp_accuracy a (topfloat::('e, 'f) float) 0.5" 
    using assms by (simp add:ulp_accuracy_def finite_topfloat valof_topfloat)
  then show ?thesis by blast
qed

lemma ulp_0_5_exists1_threshold:
  assumes a1: "(a::real) \<ge> 0" 
    and a2: "\<bar>a\<bar> < threshold TYPE(('e, 'f)float)" 
  and a3: "ulp_accuracy a (c::('e, 'f) float) \<bar>x\<bar>"
  and a4: "valof c \<le> a"
  and a5: "sign c = 0"
  and a6: "1 < LENGTH('e)"
  shows "((y::nat) - 0.5 \<le> x \<and> (y+0.5) > x \<and> ulp_accuracy a (b::('e, 'f) float) \<bar>x\<bar> \<and> valof b \<le> a \<and> sign b = 0 \<longrightarrow> (\<exists>(b::('e, 'f) float). ulp_accuracy a b 0.5))"
  using assms ulp_0_5_exists1 ulp_0_5_exists_threshold
  by (smt (verit, ccfv_SIG) of_nat_0_eq_iff of_nat_le_0_iff)

lemma ulp_0_5_exists2:
  assumes "(x::real)\<ge>0" "y=\<lceil>\<lfloor>x*2\<rfloor>/2\<rceil>"
  shows "y-0.5 \<le> x \<and> (y+0.5) > x"
proof -
  from assms have "y\<ge>\<lfloor>x*2\<rfloor>/2 \<and> (y-1)<\<lfloor>x*2\<rfloor>/2" by linarith
  then have "2*y\<ge>\<lfloor>x*2\<rfloor> \<and> 2*y-2<\<lfloor>x*2\<rfloor>" by simp
  then have "2*y+1>x*2 \<and> 2*y-1\<le>x*2" by linarith
  then have "y+0.5>x \<and> y-0.5\<le>x" by linarith 
  then show ?thesis by blast
qed

lemma ulp_0_5_exists3:
  assumes "(x::real)\<ge>0"
  shows "\<exists>y::nat. (y::nat) - 0.5 \<le> x \<and> (y+0.5) > x"
proof -
  obtain y where y_def: "(y::int)=\<lceil>\<lfloor>x*2\<rfloor>/2\<rceil>" by blast
  with assms ulp_0_5_exists2 have math_rewrite: "y-0.5 \<le> x \<and> (y+0.5) > x" by blast
  from assms y_def have "y\<ge>0" by linarith
  then have is_nat: "\<exists>y2::nat. y2=y" by presburger
  with math_rewrite show ?thesis by fastforce
qed

lemma distance_has_ulp_distance:
  assumes "is_finite b"
  shows "\<exists>x. ulp_accuracy a (b::('e,'f) float) x"
  unfolding ulp_accuracy_def
proof -
  have "\<forall>y::real.(\<exists>x::real. y\<le>x*ulp b)"
    by (metis mult_not_zero nle_le real_archimedian_rdiv_eq_0 ulp_positive verit_comp_simplify1(3))
  then have "\<exists>x. \<bar>valof b - a\<bar> \<le> x * ulp b" by presburger
  with assms show "\<exists>x::real. is_finite b \<and> \<bar>valof b - a\<bar> \<le> x * ulp b" by blast
qed
  
  

lemma ulp_0_5_exists_positive:
  assumes  "\<bar>a\<bar> < threshold TYPE(('e, 'f)float)"
    and "(a::real) \<ge> 0" 
    and "1 < LENGTH('e)"
  shows "\<exists>(b::('e, 'f) float). ulp_accuracy a b 0.5"
proof -
  obtain x where obt_x: "ulp_accuracy a (0::('e,'f) float) x"
    using distance_has_ulp_distance finite_zero by auto
  with assms ulp_accuracy_non_negative have abs_x: "x = \<bar>x\<bar>" by fastforce
  moreover from assms have "valof (0::('e,'f) float) \<le> a" 
    by force
  moreover have "sign (0::('e,'f) float) = 0"
    by (simp add: zero_simps(1))
  moreover obtain y where "(y::nat) - 0.5 \<le> x \<and> (y+0.5) > x" using obt_x ulp_0_5_exists3 assms ulp_accuracy_non_negative by blast
  with ulp_0_5_exists1_threshold show ?thesis
    by (metis assms obt_x calculation)
qed

lemma ulp_0_5_exists_negative:
  assumes  "\<bar>a\<bar> < threshold TYPE(('e, 'f)float)"
    and "(a::real) \<le> 0" 
    and "1 < LENGTH('e)"
  shows "\<exists>(b::('e, 'f) float). ulp_accuracy a b 0.5"
proof -
  from assms ulp_0_5_exists_positive have "\<exists>(b::('e, 'f) float). ulp_accuracy (-a) b 0.5"
    by force
  then obtain b where "ulp_accuracy (-a) (b::('e, 'f) float) 0.5" by blast
  with ulp_accuracy_def have "is_finite (-b) \<and> \<bar>valof b - (-a)\<bar> \<le> 0.5 * ulp b" by auto
  with valof_uminus have "is_finite (-b) \<and> \<bar>valof (-b) - a\<bar> \<le> 0.5 * ulp (-b)" apply(simp add:valof_uminus) by argo
  with ulp_accuracy_def show ?thesis by blast 
qed

lemma ulp_0_5_exists:
  assumes  "\<bar>a\<bar> < threshold TYPE(('e, 'f)float)"
    and "1 < LENGTH('e)"
  shows "\<exists>(b::('e, 'f) float). ulp_accuracy a b 0.5"
  using ulp_0_5_exists_positive ulp_0_5_exists_negative assms by fastforce

lemma ulp_decrease_underflow:
  assumes "fraction (x::('e, 'f) float) = 0" and "exponent x = 0"
  shows "\<not>is_finite (ulp_decrease x)"
  unfolding ulp_decrease_def
  using assms apply (simp_all add: ulp_decrease.rep_eq assms Abs_float_inverse exponent_def split: prod.splits)
  using assms by (auto simp add:word_minus_1 fraction_def unat_eq_zero ulp_decrease_exp_helper split: prod.splits)

lemma ulp_decrease_underflow':
  assumes "fraction (x::('e, 'f) float) = 0" and "is_finite (ulp_decrease x)"
  shows "exponent x \<noteq> 0"
  using ulp_decrease_underflow assms by blast

lemma ulp_decrease_case_x_1: 
  assumes "(0::nat) < exponent x" and "exponent x \<le> Suc (0::nat)"
  shows "exponent x = 1"
  using assms by simp


lemma ulp_is_smaller:
  shows "exponent (b::('e, 'f) float) \<noteq> 0 \<Longrightarrow> \<bar>valof b\<bar> > ulp b" 
  apply(simp add:abs_valof_eq2 ulp_equivelance bias_def diff_1_ulp_helper1 ulp_divisor_rewrite divide_less_cancel)
  by (smt (verit) len_gt_0 of_nat_less_0_iff one_less_power)

(*lemma mul_less: 
  assumes "(z::real) > 0" and "(x::real) \<ge> (y::real)"
  shows "x*z \<ge> y*z"
  using assms by auto*)

lemma closest_means_ulp_0_5_helper: "(a::real) \<le> (b::real) \<Longrightarrow> ((2::real) ^ (c::nat) / 2 ^ bias TYPE(('e, 'f) float)) *
            (2 ^ LENGTH('f) + a) / 2 ^ LENGTH('f) \<le> (2 ^ c / 2 ^ bias TYPE(('e, 'f) float)) *
            real ((2::nat) ^ LENGTH('f) + b) / 2 ^ LENGTH('f)"
proof -
  have g0: "(2::real) ^ LENGTH('f) > (0::real)" by simp
  have g0_2: "((2::real) ^ c / 2 ^ bias TYPE(('e, 'f) float)) > 0" by simp
  then have "a \<le> b \<Longrightarrow> (2 ^ LENGTH('f) + a) \<le> (2 ^ LENGTH('f) + b)" by simp
  with g0 have "a \<le> b \<Longrightarrow> (2 ^ LENGTH('f) + a)  / 2 ^ LENGTH('f)\<le> (2 ^ LENGTH('f) + b) / 2 ^ LENGTH('f)"
    by (simp add: IEEE_Properties.div_less)
  with g0_2 show "a \<le> b \<Longrightarrow> ((2::real) ^ c / 2 ^ bias TYPE(('e, 'f) float))* (2 ^ LENGTH('f) + a)  / 2 ^ LENGTH('f)\<le> ((2::real) ^ c / 2 ^ bias TYPE(('e, 'f) float))*(2 ^ LENGTH('f) + b) / 2 ^ LENGTH('f)"by (simp add:div_less) 
qed


lemma half_times_power: "x > 0 \<longrightarrow> (0.5::real)*2^x = 2^(x-1)"
  apply(induction x)
  by auto

lemma power_2_at_least_4: "(x::nat)>1 \<longrightarrow> (2::real)^x \<ge> 4"
  apply(induction x)
   apply auto
  using Suc_lessI by fastforce

(*lemma both_positive_abs:
  assumes "(a::real) \<ge> 0" and "(b::real) \<ge> 0"
    and "\<bar>a\<bar> > \<bar>b\<bar> "
  shows "\<bar>a\<bar> - \<bar>b\<bar> = \<bar>a - b\<bar>"*)
lemma closest_mean_ulp_0_5_helper_rewrite_to_ulp:
  assumes "\<bar>valof b - valof c\<bar> = (2 ^ (exponent b) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f)) / 2 ^ LENGTH('f) - (2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f) + (2::nat) ^ LENGTH('f) - (1::nat)) / 2 ^ LENGTH('f)"
     and "exponent c = exponent b - (1::nat)"
     and a:"\<not> IEEE.exponent b \<le> IEEE.exponent c" and b:"IEEE.exponent b \<noteq> (1::nat)"
   shows "\<bar>valof b - valof c\<bar> = (2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) / 2 ^ LENGTH('f)"
proof -
  from assms have "\<bar>valof b - valof c\<bar> = (2 ^ (exponent c + 1) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f)) / 2 ^ LENGTH('f) - (2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f) + (2::nat) ^ LENGTH('f) - (1::nat)) / 2 ^ LENGTH('f)" by fastforce
  then have "\<bar>valof b - valof c\<bar> = (2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f) + 2 ^ LENGTH('f)) / 2 ^ LENGTH('f) - (2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f) + (2::nat) ^ LENGTH('f) - (1::nat)) / 2 ^ LENGTH('f)" by fastforce
  then have "\<bar>valof b - valof c\<bar> = (2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) * (
              (2 ^ LENGTH('f) + 2 ^ LENGTH('f)) / 2 ^ LENGTH('f) -
              (2 ^ LENGTH('f) + (2::nat) ^ LENGTH('f) - (1::nat)) / 2 ^ LENGTH('f))" by argo
  then have "\<bar>valof b - valof c\<bar> = (2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) * (
              (2 ^ LENGTH('f) + 2 ^ LENGTH('f)) -
              (2 ^ LENGTH('f) + (2::nat) ^ LENGTH('f) - (1::nat)))/ 2 ^ LENGTH('f)"
    by (simp add: diff_divide_distrib nat_1_add_1 of_nat_diff right_diff_distrib)
  then show "\<bar>valof b - valof c\<bar> = (2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float))/ 2 ^ LENGTH('f)"
    by (simp add: trans_le_add2) qed

lemma closest_means_ulp_0_5:
  assumes "ulp_accuracy a (b::('e,'f) float) 0.5" and "LENGTH('f)> 1"
  and "(\<forall>(b::('e,'f) float). b \<in> {a. is_finite a} \<longrightarrow> \<bar>valof (c::('e,'f) float) - a\<bar> \<le> \<bar>valof b - a\<bar>)"
  and "is_finite c"
  shows "ulp_accuracy a c 0.5"
  apply (cases "exponent b \<le> exponent c \<or> exponent b = 1")
  subgoal proof -
    from ulp_equivelance have ulp_same: "\<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow> IEEE.exponent b = (1::nat) \<Longrightarrow> ulp b = ulp c"
      by (metis max.absorb1 max.commute nat_le_linear)
    moreover have "exponent b \<le> exponent c \<longrightarrow> ulp b \<le> ulp c" by (auto simp add:ulp_equivelance divide_right_mono)
    ultimately have "IEEE.exponent b \<le> IEEE.exponent c \<or> IEEE.exponent b = (1::nat) \<Longrightarrow> ulp b \<le> ulp c " by argo
    then show "IEEE.exponent b \<le> IEEE.exponent c \<or> IEEE.exponent b = (1::nat) \<Longrightarrow> ulp_accuracy a c ((5::real) / (10::real))" using assms apply(simp add:ulp_accuracy_def) by force 
  qed
  subgoal proof -
    {
      assume a:"\<not> IEEE.exponent b \<le> IEEE.exponent c" and b:"IEEE.exponent b \<noteq> (1::nat)"
      from a b have exp_not_0: "exponent b \<noteq> 0" by simp
      from sign_valof_diff have "sign b \<noteq> sign c \<Longrightarrow> \<bar>valof c - a\<bar> \<ge> \<bar>valof b\<bar> + \<bar>valof c\<bar> - \<bar>valof b - a\<bar>"
        by (smt (verit))
      with assms exp_not_0 ulp_accuracy_def have "sign b \<noteq> sign c \<Longrightarrow> \<bar>valof c - a\<bar> > \<bar>valof b - a\<bar>" apply(simp add: assms ulp_accuracy_def ulp_is_smaller)
        by (smt (verit, ccfv_SIG) not_gr_zero ulp_is_smaller)
      with assms ulp_accuracy_def have "sign b = sign c"
        by (smt (verit, ccfv_threshold) mem_Collect_eq)
    } note sign_equality = this

    {
      assume a:"\<not> IEEE.exponent b \<le> IEEE.exponent c" and b:"IEEE.exponent b \<noteq> (1::nat)"
      assume to_disprove: "exponent c < exponent b - 1"

      {
        from a b have b_at_least_2: "(exponent b)-(2::nat)+(1::nat) = (exponent b)-(1::nat)" by auto
        from abs_valof_max have "\<bar>valof c\<bar> < (2* 2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float))" by blast
        moreover from to_disprove have "exponent c \<le> exponent b - 2" by linarith
        ultimately have "\<bar>valof c\<bar> \<le> (2* 2 ^ (exponent b - 2) / 2 ^ bias TYPE(('e, 'f) float))"
          by (smt (verit) exp_less less_divide_eq nat_less_le zero_less_power)
        with b_at_least_2 have "\<bar>valof c\<bar> \<le> ( 2 ^ ((exponent b)-(1::nat)) / 2 ^ bias TYPE(('e, 'f) float))"
          by (metis power_add power_commutes power_one_right)
      } note val_c_simplified = this

      {
        from a have "\<bar>valof b\<bar> = (2 ^ (exponent b) / 2 ^ bias TYPE(('e, 'f) float)) * 
          (2 ^ LENGTH('f) + real (fraction b)) / 2 ^ LENGTH('f)"  by (simp add:abs_valof_eq2)
        with float_frac_ge have "\<bar>valof b\<bar> \<ge> (2 ^ (exponent b) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f)) / 2 ^ LENGTH('f)"
          by (smt (verit, del_insts) divide_nonneg_nonneg divide_right_mono mult_left_mono of_nat_0_le_iff zero_le_power)
        with a have "\<bar>valof b\<bar> \<ge> (2 ^ (exponent b - 1 + 1) / 2 ^ bias TYPE(('e, 'f) float))" by fastforce
        then have val_b_simplified: "\<bar>valof b\<bar> \<ge> (2*2 ^ (exponent b-1) / 2 ^ bias TYPE(('e, 'f) float))"
          by (metis power_add power_commutes power_one_right)
      } note val_b_simplified = this
      
      { 
        have step_1: "((2^LENGTH('f))-1)*(2 ^ (exponent b-1) / 2 ^ (bias TYPE(('e, 'f) float)+LENGTH('f))) > ((2::real) ^ (exponent b - 1) / (2::real) ^ (bias TYPE(('e, 'f) float) + LENGTH('f)))" 
          apply(simp add:div_less divide_less_eq frac_less) 
          using assms power_2_at_least_4 by fastforce
        from assms ulp_accuracy_def bias_def ulp_equivelance a half_times_power have "\<bar>valof b - a\<bar> \<le> 0.5*((2::real) ^ max (IEEE.exponent b) (1::nat) / (2::real) ^ (bias TYPE(('e, 'f) float) + LENGTH('f)))" by metis
        with a half_times_power have val_b_min_a: "\<bar>valof b - a\<bar> \<le> ((2::real) ^ (exponent b - 1) / (2::real) ^ (bias TYPE(('e, 'f) float) + LENGTH('f)))" by auto
        with to_disprove a b val_b_simplified val_c_simplified have "\<bar>valof c - a\<bar> \<ge> (2^LENGTH('f)) * (2 ^ (exponent b-1) / 2 ^ (bias TYPE(('e, 'f) float)+LENGTH('f))) - ((2::real) ^ (exponent b - 1) / (2::real) ^ (bias TYPE(('e, 'f) float) + LENGTH('f)))"
          apply (simp add: power_add) by argo
        with val_b_min_a step_1 have "\<bar>valof c - a\<bar> > \<bar>valof b - a\<bar>" by argo
      } note c_min_a_bigger = this
      with assms have "exponent c = exponent b - (1::nat)" by(auto simp add:ulp_accuracy_def)
    } note exp_c_exp_b_min_1 = this
    with assms have exp_c_exp_b_min_1: "\<not> exponent b \<le> exponent c \<Longrightarrow> exponent c = exponent b - (1::nat)" by fastforce
    with ulp_equivelance have ulp_b_2_ulp_c: "\<not> exponent b \<le> exponent c \<Longrightarrow> exponent b \<noteq> (1::nat) \<Longrightarrow> ulp b = 2*ulp c" by(simp add:ulp_equivelance pow_f_min_1)
    from exp_c_exp_b_min_1 have exp_c_not_0: "\<not> exponent b \<le> exponent c \<Longrightarrow> exponent b \<noteq> (1::nat) \<Longrightarrow>exponent c \<noteq> 0" by linarith
    then have exp_c_bigger_equal_1: "\<not> exponent b \<le> exponent c \<Longrightarrow> exponent b \<noteq> (1::nat) \<Longrightarrow> max (exponent c) 1 = exponent c" by fastforce
    

    {
      assume a:"\<not> IEEE.exponent b \<le> IEEE.exponent c" and b:"IEEE.exponent b \<noteq> (1::nat)"
      
      from a b have "\<bar>\<bar>valof b\<bar> - \<bar>valof c\<bar>\<bar> = \<bar>valof b - valof c\<bar>" apply(cases "sign b = 0") by (simp_all add: sign_pos sign_equality sign_cases valof_nonpos valof_nonneg)
      moreover from a b exp_c_exp_b_min_1 abs_valof_ge_exp_ge have val_b_g_val_c: "\<bar>valof b\<bar> > \<bar>valof c\<bar>"
        using linorder_not_less by blast
      ultimately have val_b_min_val_c: "\<bar>valof b - valof c\<bar> = \<bar>valof b\<bar> - \<bar>valof c\<bar>" 
        by argo
      
      {
        assume to_disprove: "fraction c \<le>  (2::real) ^ LENGTH('f) - 2"
        then have "(2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f) + real (fraction c)) / 2 ^ LENGTH('f) \<le>
            (2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f)  + 2 ^ LENGTH('f) - 2) / 2 ^ LENGTH('f)" 
          using mult_le_cancel_left_pos[where c="(2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float))"]
          by (smt (verit) divide_le_cancel divide_pos_pos zero_less_power)
        then have bad_val_c_expanded: "\<bar>valof c\<bar> \<le> (2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f) + 2 ^ LENGTH('f) - 2) / 2 ^ LENGTH('f)"
          using a b exp_c_exp_b_min_1 by(simp add:abs_valof_eq2)
        moreover from a b exp_c_exp_b_min_1 have "\<bar>valof b\<bar> \<ge> (2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f) + 2 ^ LENGTH('f)) / 2 ^ LENGTH('f)"
          using mult_left_mono[where a="(2 ^ LENGTH('f)) / 2 ^ LENGTH('f)" and b="(2 ^ LENGTH('f) + real (fraction b)) / 2 ^ LENGTH('f)" and c = "(2::nat)* (2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float))"]
          by (simp add:abs_valof_eq2 pow_f_min_1 power_commutes)
        ultimately  have "\<bar>valof b - valof c\<bar> \<ge> (2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) * 2 / 2 ^ LENGTH('f)"
          using val_b_min_val_c by argo
        then have b_min_c: "\<bar>valof b - valof c\<bar> \<ge> ulp c * 2" using a b exp_c_bigger_equal_1 by (simp add: bias_def ulp_equivelance ulp_divisor_rewrite)
        from a b assms ulp_b_2_ulp_c exp_c_exp_b_min_1 have "\<bar>valof b - a\<bar> \<le> ulp c" by(simp add:ulp_accuracy_def)
        moreover with assms have "\<bar>valof c - a\<bar> \<le> ulp c"
          using ulp_accuracy_def dual_order.trans by blast
        ultimately have dists: "\<bar>valof b - a\<bar> = ulp c \<and> \<bar>valof c - a\<bar> = ulp c" using b_min_c by argo
        moreover from a b exp_c_not_0 ulp_is_smaller have "\<bar>valof c\<bar> > ulp c" by force
        ultimately have "\<bar>a\<bar> = \<bar>valof c\<bar> + ulp c" using val_b_g_val_c by argo
        with ulp_increase_abs_diff assms have "\<bar>a\<bar> = \<bar>valof (ulp_increase c)\<bar>"
          by fastforce
        with valof_minus have "\<bar>a - valof (ulp_increase c)\<bar> = 0 \<or> \<bar>a - valof (- ulp_increase c)\<bar> = 0" by auto
        moreover have "is_finite (ulp_increase c)"
          using ulp_increase_exp assms exp_c_exp_b_min_1 ulp_accuracy_def eq_exp_eq_finite
          by (smt (verit, best) Nat.diff_diff_eq a add_diff_inverse_nat b diff_is_0_eq exp_c_not_0 nat_diff_split nat_le_linear)
        moreover then have "is_finite (- ulp_increase c)" by fastforce
        ultimately have "\<exists>(x::('e,'f) float). \<bar>a - valof x\<bar> = 0 \<and> is_finite x" by blast
        then have "\<exists>(x::('e,'f) float). \<bar>a - valof x\<bar> < \<bar>a - valof c\<bar> \<and> is_finite x"
          using dists ulp_positive
          by (metis eq_iff_diff_eq_0 zero_less_abs_iff)
        with assms(3) have "False" by fastforce
      } note to_disprove_false2 = this
      then have "fraction c \<ge> (2::nat) ^ LENGTH('f) - (1::nat)"
        apply (simp add: nat_le_real_less of_nat_diff) by argo
      with float_frac_le have "real (fraction c) = (2::nat) ^ LENGTH('f) - (1::nat)"
        by (metis le_antisym)
      then have "(2::real) ^ LENGTH('f) + real (fraction c) = (2::nat) ^ LENGTH('f) + (2::nat) ^ LENGTH('f) - Suc (0::nat)"
        apply simp
        by (metis Abs_fnat_hom_add Nat.diff_add_assoc nat_one_le_power not_less_eq_eq not_numeral_le_zero power_2_simp)
      then have val_c_eq: "\<bar>valof c\<bar> = (2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f) + (2::nat) ^ LENGTH('f) - (1::nat)) / 2 ^ LENGTH('f)" 
              using a b exp_c_exp_b_min_1 by(simp add:abs_valof_eq2)
      from assms have "\<bar>valof c - a\<bar> \<le> 0.5*ulp b"
        by (smt (verit) mem_Collect_eq ulp_accuracy_def)
      with ulp_b_2_ulp_c a b have "\<bar>a\<bar> \<le> \<bar>valof c\<bar> + ulp c" by linarith
      with val_c_eq ulp_equivelance have "\<bar>a\<bar> \<le> (2 ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f) + (2::nat) ^ LENGTH('f) - (1::nat)) / 2 ^ LENGTH('f) + 
              (2::real) ^ max (IEEE.exponent c) (1::nat) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))" by metis
      with a b exp_c_exp_b_min_1 have "\<bar>a\<bar> \<le> ((2::real) ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f) + (2::nat) ^ LENGTH('f) - (1::nat)) / 2 ^ LENGTH('f) + 
              (2::real) ^ exponent c / (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))"
        by force
      with a b exp_c_exp_b_min_1 ulp_divisor_rewrite bias_def have "\<bar>a\<bar> \<le> ((2::real) ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f) + (2::nat) ^ LENGTH('f) - (1::nat)) / 2 ^ LENGTH('f) + 
              (2::real) ^ exponent c  / 2 ^ bias TYPE(('e, 'f) float) / 2 ^ LENGTH('f)"
        by (metis (no_types, lifting) divide_divide_eq_left power_add)

      
      then have "\<bar>a\<bar> \<le> (((2::real) ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f) + (2::nat) ^ LENGTH('f) - (1::nat)) + 
              (2::real) ^ exponent c  / 2 ^ bias TYPE(('e, 'f) float)) / 2 ^ LENGTH('f)" by argo
      then have "\<bar>a\<bar> \<le> ((2::real) ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) *
              ((2 ^ LENGTH('f) + (2::nat) ^ LENGTH('f) - (1::nat)) + (1::nat)) / 2 ^ LENGTH('f)"
        by (smt (z3) Nat.add_0_right One_nat_def Suc_pred add_Suc_right add_gr_0 f_min_1 le_Suc_eq le_add2 len_of_finite_1_def length_not_greater_eq_2_iff numeral_le_real_of_nat_iff real_of_nat_less_numeral_iff zero_less_power)
      then have "\<bar>a\<bar> \<le> ((2::real) ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float)) *
              2*2 ^ LENGTH('f) / 2 ^ LENGTH('f)" by fastforce
      then have "\<bar>a\<bar> \<le> (2::real)* (2::real) ^ (exponent c) / 2 ^ bias TYPE(('e, 'f) float) *
              2 ^ LENGTH('f) / 2 ^ LENGTH('f)" by argo
      then have abs_a_le: "\<bar>a\<bar> \<le> (2::real) ^ (exponent c + (1::nat)) / 2 ^ bias TYPE(('e, 'f) float) *
              2 ^ LENGTH('f) / 2 ^ LENGTH('f)" by force
      {
        assume to_disprove: "fraction b \<ge> (1::nat)"
        then have "(2 ^ LENGTH('f) + real (fraction b)) / 2 ^ LENGTH('f) \<ge> (2 ^ LENGTH('f)  + (1::real)) / 2 ^ LENGTH('f)" by (simp add:divide_right_mono)
        then have "(2 ^ (exponent b) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f) + real (fraction b)) / 2 ^ LENGTH('f) \<ge>
            (2 ^ (exponent b) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f)  + 1) / 2 ^ LENGTH('f)" 
        using mult_le_cancel_left_pos[where c="(2 ^ (exponent b) / 2 ^ bias TYPE(('e, 'f) float))"]
        by (smt (verit) divide_le_cancel divide_pos_pos zero_less_power)
        then have bad_val_b_expanded: "\<bar>valof b\<bar> \<ge> (2 ^ (exponent b) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f) + 1) / 2 ^ LENGTH('f)"
          using a b exp_c_exp_b_min_1 by(simp add:abs_valof_eq2)
        with a b exp_c_exp_b_min_1 abs_a_le have "\<bar>valof b - a\<bar> \<ge> (2 ^ (exponent b) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f) + 1) / 2 ^ LENGTH('f) - (2::real) ^ (exponent b) / 2 ^ bias TYPE(('e, 'f) float) *
              2 ^ LENGTH('f) / 2 ^ LENGTH('f)" by force
        with a b have "\<bar>valof b - a\<bar> \<ge> ulp b" apply(simp add:ulp_equivelance ulp_divisor_rewrite bias_def) by argo
        moreover from ulp_positive have "0.5*ulp b < ulp b" by auto
        ultimately have "False" using assms ulp_accuracy_def ulp_positive by force
      } note to_disprove_false3 = this
      then have frac_b: "fraction b = 0" by fastforce
      from a b have val_b_eq: "\<bar>valof b\<bar> = (2 ^ (exponent b) / 2 ^ bias TYPE(('e, 'f) float)) *
              (2 ^ LENGTH('f)) / 2 ^ LENGTH('f)" by(simp add:abs_valof_eq2 frac_b)
      with val_b_min_val_c val_c_eq a b assms have 
        "\<bar>valof b - valof c\<bar> = (2::real) ^ exponent c / (2::real) ^ bias TYPE(('e,'f) IEEE.float) / (2::real) ^ LENGTH('f)" using closest_mean_ulp_0_5_helper_rewrite_to_ulp
        using exp_c_exp_b_min_1 by metis
      with a b exp_c_exp_b_min_1 have diff_is_ulp_c: "\<bar>valof b - valof c\<bar> = ulp c" by(simp add:ulp_equivelance ulp_divisor_rewrite bias_def)
      

      from abs_a_le a b exp_c_exp_b_min_1 val_b_eq have upper_bound: "\<bar>a\<bar> \<le> \<bar>valof b\<bar>" by fastforce
      from assms ulp_accuracy_def have "\<bar>valof b - a\<bar> \<le> 0.5*ulp b" by blast
      with a b ulp_b_2_ulp_c have "\<bar>valof b\<bar> - ulp c \<le> \<bar>a\<bar>" by auto
      with val_b_min_val_c diff_is_ulp_c have lower_bound: "\<bar>valof c\<bar> \<le> \<bar>a\<bar>" by argo
      have c_positive_a_positive: "valof c \<ge> 0 \<longrightarrow> a \<ge> 0"
        using a b exp_c_exp_b_min_1 assms(3) diff_0_right finite_zero nle_le zero_val_exponent by fastforce
      with lower_bound upper_bound sign_equality a b valof_nonneg have sign_0: "sign c = 0 \<longrightarrow> \<bar>valof b - valof c\<bar> = \<bar>valof c - a\<bar> + \<bar>valof b - a\<bar>" by auto 
      have c_positive_a_positive: "valof c \<le> 0 \<longrightarrow> a \<le> 0"
        using a b exp_c_exp_b_min_1 assms(3) diff_0_right finite_zero nle_le zero_val_exponent by fastforce
      with lower_bound upper_bound sign_equality a b valof_nonpos have "sign c = 1 \<longrightarrow> \<bar>valof b - valof c\<bar> = \<bar>valof c - a\<bar> + \<bar>valof b - a\<bar>" by auto
      with sign_0 sign_cases have "\<bar>valof b - valof c\<bar> = \<bar>valof c - a\<bar> + \<bar>valof b - a\<bar>" by metis
      moreover from assms ulp_accuracy_def have "\<bar>valof b - a\<bar> \<ge> \<bar>valof c - a\<bar>" by blast
      ultimately have "\<bar>valof c - a\<bar> \<le> 0.5*ulp c" using ulp_positive diff_is_ulp_c by argo
    }
    with assms ulp_accuracy_def show "\<not> (IEEE.exponent b \<le> IEEE.exponent c \<or> IEEE.exponent b = (1::nat)) \<Longrightarrow> ulp_accuracy a c 0.5" by blast
    (*526-856*)
    (*new start 501*)
  qed
  done

lemma rounding_0_5_ulp: 
  assumes "\<bar>a\<bar> < threshold TYPE(('e, 'f)float)" 
          "a_r = ((round To_nearest a)::('e, 'f) float)"
          "1 < LENGTH('e)"
          "1 < LENGTH('f)"
        shows "ulp_accuracy a a_r 0.5"
  proof -
  from is_finite_nonempty rounded_threshold_is_finite have fin_a_r: "is_finite a_r"
    using assms(1) assms(2) by blast 
  from ulp_0_5_exists obtain b where b_def: "ulp_accuracy a (b::('e,'f) float) 0.5"
    using assms by blast
  from assms rounded_threshold_is_closest have "is_closest (valof) (Collect is_finite) a a_r" 
    by metis
  with closest_means_ulp_0_5 is_closest_def assms b_def have "is_finite a_r \<Longrightarrow> ulp_accuracy a a_r ((5::real) / (10::real))"
    by metis
  with fin_a_r show ?thesis by blast
qed
  
end