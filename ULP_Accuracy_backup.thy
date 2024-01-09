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

lemma diff_1_ulp_helper1:
  shows "((2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) - Suc (0::nat)) * (2::real) ^ (f::nat)) = (2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) - Suc (0::nat) + f)"
  by (metis power_add)

lemma diff_1_ulp_helper1':
  shows "((2::real) ^ (f::nat) * (2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) - Suc (0::nat))) = (2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) - Suc (0::nat) + f)"
  using diff_1_ulp_helper1
  by (simp add: mult.commute)

lemma diff_1_ulp_helper1_div:
  shows "(2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) - Suc (0::nat)) = (2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) - Suc (0::nat) + f) / (2::real) ^ (f::nat)"
  by (metis divide_eq_eq power_add semiring_1_no_zero_divisors_class.power_not_zero zero_neq_numeral)

lemma diff_1_ulp_helper2:
  shows "(\<bar>a/(2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) + f - Suc (0::nat)) - b/(2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) + f - Suc (0::nat))\<bar> \<le> c/(2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) + f - Suc (0::nat))) \<longleftrightarrow> \<bar>a-b\<bar>\<le>c"
proof - 
  have "(2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) - Suc (0::nat) + f) > 0" by simp
  then have "\<bar>a/(2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) + f - Suc (0::nat)) - b/(2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) + f - Suc (0::nat))\<bar> = \<bar>a-b\<bar>/(2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) + f - Suc (0::nat))"
    by (simp add: abs_div_pos diff_divide_distrib)
  then show ?thesis
    by (simp add: divide_le_cancel)
qed

lemma diff_1_ulp_helper3:
  shows "\<bar>(- (1::real))^(sign b)*x*x2 - (- (1::real))^(sign b)*y*y2\<bar> = \<bar>x*x2-y*y2\<bar>"
proof -
  have "\<bar>(- (1::real))^(sign b)*x*x2 - (- (1::real))^(sign b)*y*y2\<bar> = \<bar>(- (1::real))^(sign b)*(x*x2 -y*y2)\<bar>" by argo
  then show ?thesis by (simp add:abs_pow_min_1) 
qed

lemma diff_1_ulp_helper4:
  shows "(2::real) ^ IEEE.exponent c * ((2::real) ^b + (1::real)) /
         (2::real) ^ ((2::nat) ^ (a - Suc (0::nat)) + b - Suc (0::nat)) =
         (2::real) ^ (IEEE.exponent c + b) /
         (2::real) ^ ((2::nat) ^ (a - Suc (0::nat)) + b - Suc (0::nat)) +
         (2::real) ^ IEEE.exponent c /
         (2::real) ^ ((2::nat) ^ (a - Suc (0::nat)) + b - Suc (0::nat))
        "
  by (smt (verit, best) diff_divide_distrib factor_minus power_add)

lemma diff_1_ulp_helper5:
  shows "(2::real) ^ (IEEE.exponent c + b) /
         (2::real) ^ ((2::nat) ^ (a - Suc (0::nat)) + b - Suc (0::nat)) =
         (2::real) ^ (IEEE.exponent c) /
         (2::real) ^ ((2::nat) ^ (a - Suc (0::nat)) - Suc (0::nat)) 
        "
  by (smt (z3) Nat.add_diff_assoc2 bot_nat_0.extremum_uniqueI frac_eq_eq mult.commute mult.left_commute not_less_eq_eq power_add semiring_1_no_zero_divisors_class.power_not_zero zero_neq_numeral)


lemma ulp_equivelance:
  shows "ulp (c::('e, 'f) float) = 2^(max (exponent c) 1) / 2^(2^(LENGTH('e) - 1) - 1 + LENGTH('f))"
  unfolding ulp_def
  apply (simp add: valof_eq2 one_lp_parts zero_lp_parts del:round.simps)
  apply (simp_all add: bias_def)
  by(simp_all add: diff_1_ulp_helper1 diff_1_ulp_helper4 diff_1_ulp_helper5)

lemma ulp_uminus[simp]:
  shows "ulp (-x) = ulp x"
  by(simp add:ulp_equivelance)

lemma ulp_increase_bigger_ulp:
  assumes "is_finite c"
  shows "ulp (c::('e,'f) float) \<le>  ulp (ulp_increase c)"
  apply(simp add:ulp_equivelance )
  apply(rule divide_right_mono)
  apply(cases "fraction c \<noteq> 2^LENGTH('f) - 1")
  using assms  apply (auto simp add:ulp_increase_exp)
  by (metis Suc_n_not_le_n diff_Suc_1 exp_less le_Suc_eq le_max_iff_disj max_0R mult.commute nat_le_linear power_Suc2)

lemma ulp_accuracy_equivelance:
  shows "ulp_accuracy a c u = ulp_accuracy_expanded a c u"
  unfolding ulp_accuracy_def ulp_accuracy_expanded_def 
  by (simp add: ulp_equivelance)

lemma diff_1_ulp:
  assumes "is_finite (a::('e, 'f) float)" "is_finite (b::('e, 'f) float)" "exponent a = exponent b" "sign a = sign b" and "fraction a = fraction b + 1"
  shows "ulp_accuracy (valof a) b 1"
  apply (simp add: ulp_accuracy_equivelance)
  unfolding ulp_accuracy_expanded_def fraction_def
  using assms apply (simp add:valof_eq2)
  apply(cases "exponent b = 0")
  apply(simp_all add: bias_def)
  apply(simp_all add:diff_1_ulp_helper1 diff_1_ulp_helper2 diff_1_ulp_helper3)
  subgoal
  proof - 
    have "((2::real) ^ IEEE.exponent b) \<noteq> 0" by force
    then have "(2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f) + ((1::real) + real (fraction b))) -
    (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f) + real (fraction b))
    \<le> (2::real) ^ IEEE.exponent b \<longleftrightarrow> ((2::real) ^ LENGTH('f) + ((1::real) + real (fraction b))) -
    ((2::real) ^ LENGTH('f) + real (fraction b))
    \<le> 1" by argo
    then show ?thesis by auto qed
  done

(*lemma ulp_increase_helper2:
  shows "\<bar>(- 1) ^ sign x * (y::real) * (z::real) / 2 ^ (f::nat) / 2 ^ (2 ^ (e - Suc 0) - Suc 0)\<bar> = \<bar>y*z\<bar> / (2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) - Suc (0::nat) + f)"
proof -
  have "\<bar>(- 1) ^ sign x * y * z / 2 ^ (f::nat) / 2 ^ (2 ^ (e - Suc 0) - Suc 0)\<bar> = \<bar>(- 1) ^ sign x * y * z / 2 ^ (2 ^ (e - Suc 0) - Suc 0 + f)\<bar>"
    by (simp add: diff_1_ulp_helper1 power_commuting_commutes)
  then show ?thesis by (simp add:abs_pow_min_1 mult.assoc)
qed*)

lemma power_add_div:
  "(x::real)/ 2 ^ (f::nat) / 2 ^ (2 ^ ((e::nat) - Suc 0) - Suc 0) =  x / 2 ^ (2 ^ (e - Suc 0) + f - Suc 0)"
proof -
  have "x/ 2 ^ f / 2 ^ (2 ^ (e - Suc 0) - Suc 0) = x/ (2 ^ (2 ^ (e - Suc 0) - Suc 0) * 2 ^ f)" by simp
  with diff_1_ulp_helper1 show ?thesis by fastforce 
qed

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

lemma ulp_increase_helper2': "x * ((f1::real) - f2) = 
      x * f1 - x * f2"
  by argo

lemma ulp_increase_diff:
  assumes "is_finite (x::('e, 'f) float)"
  shows "\<bar>valof (ulp_increase (x::('e, 'f) float)) - valof x\<bar> = ulp x"
  apply(cases "fraction x = 2^LENGTH('f) - 1")
  using assms  apply (simp_all add: valof_eq ulp_increase_exp ulp_increase_sign ulp_equivelance)
   apply(simp_all add: bias_def ulp_increase_helper1 power_add_div)
   apply(simp_all add:diff_1_ulp_helper1 diff_1_ulp_helper1')
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
  apply(simp_all add: bias_def ulp_increase_helper1 power_add_div)
   apply(simp_all add:diff_1_ulp_helper1 diff_1_ulp_helper1')
  apply(simp_all add:ulp_increase_frac)
   apply(simp_all add:ulp_increase_helper2)
   apply(simp_all add:divide_strict_right_mono divide_less_cancel)
subgoal proof -
  have "(2::real) * real ((2::nat) ^ LENGTH('f) - Suc (0::nat)) < (2::real) * (2::nat) ^ LENGTH('f)" by simp
  then have "(2::real) * real ((2::nat) ^ LENGTH('f) - Suc (0::nat)) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))
    < (2::real) * (2::nat) ^ LENGTH('f) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))"
    by (simp add: divide_strict_right_mono) 
  then have "(2::real) * real ((2::nat) ^ LENGTH('f) - Suc (0::nat)) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))
    < (2::real) * (2::nat) ^ LENGTH('f) / (2::nat) ^ LENGTH('f) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) - Suc (0::nat)) " using power_add_div
    by (metis (no_types, opaque_lifting) real_of_nat_eq_numeral_power_cancel_iff)
  then show ?thesis by force
qed
  done

lemma idk_helper:
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
    with g_topfloat nothing_between_ulp_increase have "valof (ulp_increase c) \<ge> threshold TYPE(('e, 'f)float) \<Longrightarrow>False"
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

lemma ulp_accuracy_widen:
  assumes "ulp_accuracy a (b::('e, 'f) float) x" "y > x"
  shows "ulp_accuracy a b y"
  using assms ulp_positive unfolding ulp_accuracy_def apply simp
  by (smt (verit) mult_right_less_imp_less ulp_positive)


lemma idk2:
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
    using idk_helper assms by blast
  
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
  assumes  "\<bar>a\<bar> < largest TYPE(('e, 'f)float)"
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
  with idk2 show ?thesis
    by (metis assms obt_x calculation)
qed

lemma ulp_0_5_exists_negative:
  assumes  "\<bar>a\<bar> < largest TYPE(('e, 'f)float)"
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
  assumes  "\<bar>a\<bar> < largest TYPE(('e, 'f)float)"
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

(*lemma ulp_decrease_diff:
  assumes "is_finite (x::('e, 'f) float) \<and> is_finite (ulp_decrease x)"
  shows "\<bar>valof x - valof (ulp_decrease x)\<bar> = ulp x"
  apply(cases "fraction x = 0")
  using assms  apply (simp_all add: valof_eq ulp_equivelance)
  apply(simp_all add: ulp_decrease_underflow')
  apply(simp_all add:  bias_def diff_1_ulp_helper1_div[where e="LENGTH('e)" and f="LENGTH('f)"])
  apply(simp_all add:ulp_decrease_exp ulp_decrease_sign )
   apply(simp_all add: bias_def ulp_increase_helper1 power_add_div)
   (*apply(simp_all add:diff_1_ulp_helper1 diff_1_ulp_helper1')
  apply(simp_all add:)*)
   apply(simp_all add:ulp_increase_helper3 ulp_increase_helper4 abs_pow_min_1)
  apply(simp_all add:ulp_decrease_frac)
   apply(simp_all add:ulp_increase_helper2 ulp_increase_helper2' )
   apply (auto simp add:f_min_1[where f="(2::nat) ^ LENGTH('f)"])
  subgoal proof -
    have "(0::nat) < exponent x \<Longrightarrow> exponent x \<le> Suc (0::nat) \<Longrightarrow> exponent x = 1" by linarith
    then have "(0::nat) < exponent x \<Longrightarrow> exponent x \<le> Suc (0::nat) \<Longrightarrow> (2::real) ^ IEEE.exponent x = 2" by fastforce
    then show "(0::nat) < exponent x \<Longrightarrow> exponent x \<le> Suc (0::nat) \<Longrightarrow> \<bar>(2::real) ^ IEEE.exponent x * (2::real) ^ LENGTH('f) - ((2::real) * (2::real) ^ LENGTH('f) - (2::real))\<bar> = (2::real) ^ IEEE.exponent x" by force
  qed
  apply(simp add:field_simps)
  subgoal proof -
    have "Suc (0::nat) < exponent x \<Longrightarrow> (2::real) * ((2::real) ^ LENGTH('f) * (2::real) ^ (IEEE.exponent x - Suc (0::nat))) = (2::real) ^ LENGTH('f) * (2::real) ^ exponent x" by (simp add: pow_f_min_1)
    then have "Suc (0::nat) < exponent x \<Longrightarrow> ((2::real) * ((2::real) ^ LENGTH('f) * (2::real) ^ (IEEE.exponent x - Suc (0::nat))) - (2::real) ^ (IEEE.exponent x - Suc (0::nat))) = (2::real) ^ LENGTH('f) * (2::real) ^ exponent x - (2::real) ^ exponent x" apply (simp add: pow_f_min_1)

  
  (*apply(simp add: ulp_decrease_case_x_1[where x=x])*)
  
      sorry
    then show ?thesis sorry
  qed sorry*)

lemma 
  assumes "is_finite (b::('e, 'f) float)" "x\<le>x'"
  assumes "ulp_accuracy a b x"
  shows "ulp_accuracy a b x'"
  using assms
  apply (simp add:ulp_accuracy_equivelance ulp_accuracy_expanded_def)
  by (smt (verit, ccfv_SIG) divide_right_mono mult_right_mono zero_le_power)

lemma 
  assumes "is_finite (b::('e, 'f) float) \<and> is_finite (c::('e, 'f) float)"
  assumes "\<bar>(valof b - a)\<bar> \<le> \<bar>(valof c - a)\<bar>" "ulp_accuracy a c x"
  shows "ulp_accuracy a b x"
  using assms apply (simp add:ulp_accuracy_equivelance ulp_accuracy_expanded_def)
  apply (cases "IEEE.exponent c = IEEE.exponent b")
  subgoal by simp
  apply (cases "IEEE.exponent c > IEEE.exponent b")
  subgoal
    apply (subgoal_tac "\<bar>valof c\<bar> > \<bar>valof b\<bar>") defer
    

    find_theorems IEEE.exponent "(<)"
    oops

(*lemma valof_smaller_exponent:
  assumes "exponent a < exponent b" and "exponent b > 1"
  shows "\<bar>valof a  - valof b \<bar> \<ge> ulp b"
  using assms apply (simp add: ulp_equivelance)
proof -
  from valof_eq have "exponent a = (0::nat) \<Longrightarrow> valof a = (- (1::real)) ^ sign a * (2::real) * (real (fraction a) / (2::real) ^ LENGTH('b)) /
     (2::real) ^ bias TYPE(('a, 'b) IEEE.float)"
    by (metis (no_types, opaque_lifting) times_divide_eq_left times_divide_eq_right)
  then have "exponent a = (0::nat) \<Longrightarrow> valof a = (- (1::real)) ^ sign a * (2::real) ^ (1+IEEE.exponent a) * (real (fraction a) / (2::real) ^ LENGTH('b)) /
     (2::real) ^ bias TYPE(('a, 'b) IEEE.float)" by fastforce
  then have "(2::real) ^ bias TYPE(('a, 'b) IEEE.float) > 0 \<Longrightarrow> (2::real) ^ LENGTH('b) > 0  \<Longrightarrow> exponent a = (0::nat) \<Longrightarrow> valof a \<le> (- (1::real)) ^ sign a * (2::real) ^ (1+IEEE.exponent a) * ((1::real) + real (fraction a) / (2::real) ^ LENGTH('b)) /
     (2::real) ^ bias TYPE(('a, 'b) IEEE.float)" sorry
    oops*)

lemma diff_ulp:
  assumes "valof (a::('e,'f) float) \<noteq> valof (b::('e,'f) float)"
  shows "\<bar>valof a - valof b\<bar> \<ge> ulp a"  
  
  oops

lemma smaller_ulp_is_closer:
  assumes "is_finite (b::('e, 'f) float) \<and> is_finite (c::('e, 'f) float)" and "ulp_accuracy a b 0.5" and "\<not>ulp_accuracy a c 0.5"
  shows "\<bar>(valof b - a)\<bar> \<le> \<bar>(valof c - a)\<bar>"
  using assms apply (simp add:ulp_accuracy_equivelance ulp_accuracy_expanded_def)
  apply (cases "exponent b = exponent c")
   apply simp_all
  apply (cases "exponent b < exponent c")
   apply simp_all
  subgoal proof -
    from exponent_def have exp_0: "\<forall>x. exponent x \<ge> 0" by simp
    from max_def have max_diff: "exponent b < exponent c \<Longrightarrow> max (IEEE.exponent b) (Suc (0::nat)) \<le> 
          IEEE.exponent c" by force
    have "((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))) > 0" by simp
      with max_diff have "exponent b < exponent c \<Longrightarrow> (2::real) ^ max (IEEE.exponent b) (Suc (0::nat)) /
       ((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))) \<le> 
          (2::real) ^ IEEE.exponent c /
       ((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)))"
      by (simp add: divide_right_mono)
    then show "is_finite b \<and> is_finite c \<Longrightarrow>
    \<bar>valof b - a\<bar>
    \<le> (2::real) ^ max (IEEE.exponent b) (Suc (0::nat)) /
       ((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))) \<Longrightarrow>
    \<not> \<bar>valof c - a\<bar>
       \<le> (2::real) ^ IEEE.exponent c /
          ((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))) \<Longrightarrow>
    IEEE.exponent b < IEEE.exponent c \<Longrightarrow> \<bar>valof b - a\<bar> \<le> \<bar>valof c - a\<bar>" by argo
  qed
  apply (cases "exponent b = 1")
  subgoal proof -
    have "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>
    \<not> IEEE.exponent b < IEEE.exponent c \<Longrightarrow> IEEE.exponent b = (1::nat) \<Longrightarrow> exponent b = max (IEEE.exponent c) (Suc (0::nat))" by fastforce
    then have "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>
    \<not> IEEE.exponent b < IEEE.exponent c \<Longrightarrow> IEEE.exponent b = (1::nat) \<Longrightarrow> 
    (2::real) ^ IEEE.exponent b /
       ((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))) =
    (2::real) ^ max (IEEE.exponent c) (Suc (0::nat)) /
          ((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)))
    " by auto
    then show "is_finite b \<and> is_finite c \<Longrightarrow>
    \<bar>valof b - a\<bar>
    \<le> (2::real) ^ IEEE.exponent b /
       ((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))) \<Longrightarrow>
    \<not> \<bar>valof c - a\<bar>
       \<le> (2::real) ^ max (IEEE.exponent c) (Suc (0::nat)) /
          ((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))) \<Longrightarrow>
    IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>
    \<not> IEEE.exponent b < IEEE.exponent c \<Longrightarrow> IEEE.exponent b = (1::nat) \<Longrightarrow> \<bar>valof b - a\<bar> \<le> \<bar>valof c - a\<bar>" by argo
  qed
  subgoal proof -
    have "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>
    \<not> IEEE.exponent b < IEEE.exponent c \<Longrightarrow> IEEE.exponent b \<noteq> (1::nat) \<Longrightarrow> max (IEEE.exponent b) (1::nat) \<noteq> max (IEEE.exponent c) (1::nat)" by linarith
    with ulp_equivelance have "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>
    \<not> IEEE.exponent b < IEEE.exponent c \<Longrightarrow> IEEE.exponent b \<noteq> (1::nat) \<Longrightarrow> ulp b \<noteq> ulp c"
      by (smt (verit, ccfv_SIG) divide_cancel_right power_inject_exp semiring_1_no_zero_divisors_class.power_not_zero)
    from assms ulp_accuracy_def have "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>
    \<not> IEEE.exponent b < IEEE.exponent c \<Longrightarrow> IEEE.exponent b \<noteq> (1::nat) \<Longrightarrow> valof b = valof c \<Longrightarrow> ulp_accuracy a b 0.5 = ulp_accuracy a c 0.5" sorry
    then have bc_rel: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow> \<bar>valof b - valof c\<bar> \<ge> ulp b" sorry
    from assms ulp_accuracy_def have b_diff: "\<bar>valof b - a\<bar> \<le> 0.5*ulp b" by fast
    from bc_rel b_diff have 1: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>valof b \<ge> valof c \<Longrightarrow> valof b \<ge> a \<Longrightarrow> \<bar>valof c - a\<bar> \<ge> 0.5*ulp b" by fastforce
    from bc_rel b_diff have 2: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>valof b < valof c \<Longrightarrow> valof b \<ge> a \<Longrightarrow> \<bar>valof c - a\<bar> \<ge> 0.5*ulp b" by fastforce
    from bc_rel b_diff have 3: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>valof b \<ge> valof c \<Longrightarrow> valof b < a \<Longrightarrow> \<bar>valof c - a\<bar> \<ge> 0.5*ulp b" by fastforce
    from bc_rel b_diff have 4: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>valof b < valof c \<Longrightarrow> valof b < a \<Longrightarrow> \<bar>valof c - a\<bar> \<ge> 0.5*ulp b" by fastforce
    from 1 2 3 4 have "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>\<bar>valof c - a\<bar> \<ge> 0.5*ulp b" by argo
    with b_diff show "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow> \<bar>valof b - a\<bar> \<le> \<bar>valof c - a\<bar>" by force
  qed
  oops

lemma smaller_ulp_is_closer2:
  assumes "is_finite (b::('e, 'f) float) \<and> is_finite (c::('e, 'f) float)" and "ulp_accuracy a b 0.5" and "\<not>ulp_accuracy a c 0.5"
  shows "\<bar>(valof b - a)\<bar> < \<bar>(valof c - a)\<bar> \<or> (\<bar>(valof b - a)\<bar> = \<bar>(valof c - a)\<bar> \<and> \<not>even (fraction c))"
  using assms apply (simp add:ulp_accuracy_equivelance ulp_accuracy_expanded_def)
  apply (cases "exponent b = exponent c")
   apply simp_all
  apply (cases "exponent b < exponent c")
   apply simp_all
  subgoal proof -
    from exponent_def have exp_0: "\<forall>x. exponent x \<ge> 0" by simp
    from max_def have max_diff: "exponent b < exponent c \<Longrightarrow> max (IEEE.exponent b) (Suc (0::nat)) \<le> 
          IEEE.exponent c" by force
    have "((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))) > 0" by simp
      with max_diff have "exponent b < exponent c \<Longrightarrow> (2::real) ^ max (IEEE.exponent b) (Suc (0::nat)) /
       ((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))) \<le> 
          (2::real) ^ IEEE.exponent c /
       ((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)))"
      by (simp add: divide_right_mono)
    then show "is_finite b \<and> is_finite c \<Longrightarrow>
    \<bar>valof b - a\<bar>
    \<le> (2::real) ^ max (IEEE.exponent b) (Suc (0::nat)) /
       ((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))) \<Longrightarrow>
    \<not> \<bar>valof c - a\<bar>
       \<le> (2::real) ^ IEEE.exponent c /
          ((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))) \<Longrightarrow>
    IEEE.exponent b < IEEE.exponent c \<Longrightarrow> \<bar>valof b - a\<bar> < \<bar>valof c - a\<bar> \<or> \<bar>valof b - a\<bar> = \<bar>valof c - a\<bar> \<and> odd (fraction c)" by argo
  qed
  apply (cases "exponent b = 1")
  subgoal proof -
    have "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>
    \<not> IEEE.exponent b < IEEE.exponent c \<Longrightarrow> IEEE.exponent b = (1::nat) \<Longrightarrow> exponent b = max (IEEE.exponent c) (Suc (0::nat))" by fastforce
    then have "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>
    \<not> IEEE.exponent b < IEEE.exponent c \<Longrightarrow> IEEE.exponent b = (1::nat) \<Longrightarrow> 
    (2::real) ^ IEEE.exponent b /
       ((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))) =
    (2::real) ^ max (IEEE.exponent c) (Suc (0::nat)) /
          ((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat)))
    " by auto
    then show "is_finite b \<and> is_finite c \<Longrightarrow>
    \<bar>valof b - a\<bar>
    \<le> (2::real) ^ IEEE.exponent b /
       ((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))) \<Longrightarrow>
    \<not> \<bar>valof c - a\<bar>
       \<le> (2::real) ^ max (IEEE.exponent c) (Suc (0::nat)) /
          ((2::real) * (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) + LENGTH('f) - Suc (0::nat))) \<Longrightarrow>
    IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>
    \<not> IEEE.exponent b < IEEE.exponent c \<Longrightarrow>
    IEEE.exponent b = (1::nat) \<Longrightarrow> \<bar>valof b - a\<bar> < \<bar>valof c - a\<bar> \<or> \<bar>valof b - a\<bar> = \<bar>valof c - a\<bar> \<and> odd (fraction c)" by argo
  qed
  subgoal proof -
    have "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>
    \<not> IEEE.exponent b < IEEE.exponent c \<Longrightarrow> IEEE.exponent b \<noteq> (1::nat) \<Longrightarrow> max (IEEE.exponent b) (1::nat) \<noteq> max (IEEE.exponent c) (1::nat)" by linarith
    with ulp_equivelance have "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>
    \<not> IEEE.exponent b < IEEE.exponent c \<Longrightarrow> IEEE.exponent b \<noteq> (1::nat) \<Longrightarrow> ulp b \<noteq> ulp c"
      by (smt (verit, ccfv_SIG) divide_cancel_right power_inject_exp semiring_1_no_zero_divisors_class.power_not_zero)
    from assms ulp_accuracy_def have "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>
    \<not> IEEE.exponent b < IEEE.exponent c \<Longrightarrow> IEEE.exponent b \<noteq> (1::nat) \<Longrightarrow> valof b = valof c \<Longrightarrow> ulp_accuracy a b 0.5 = ulp_accuracy a c 0.5" sorry
    then have bc_rel: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow> \<bar>valof b - valof c\<bar> \<ge> ulp b" sorry
    from assms ulp_accuracy_def have b_diff: "\<bar>valof b - a\<bar> \<le> 0.5*ulp b" by fast
    from b_diff have l_1: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow> \<bar>valof b - valof c\<bar> > ulp b \<Longrightarrow> valof b \<ge> valof c \<Longrightarrow> valof b \<ge> a \<Longrightarrow> \<bar>valof c - a\<bar> > 0.5*ulp b" by fastforce
    from b_diff have l_2: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow> \<bar>valof b - valof c\<bar> > ulp b \<Longrightarrow>valof b < valof c \<Longrightarrow> valof b \<ge> a \<Longrightarrow> \<bar>valof c - a\<bar> > 0.5*ulp b" by fastforce
    from b_diff have l_3: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow> \<bar>valof b - valof c\<bar> > ulp b \<Longrightarrow>valof b \<ge> valof c \<Longrightarrow> valof b < a \<Longrightarrow> \<bar>valof c - a\<bar> > 0.5*ulp b" by fastforce
    from b_diff have l_4: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow> \<bar>valof b - valof c\<bar> > ulp b \<Longrightarrow>valof b < valof c \<Longrightarrow> valof b < a \<Longrightarrow> \<bar>valof c - a\<bar> > 0.5*ulp b" by fastforce
    from l_1 l_2 l_3 l_4 have "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow> \<bar>valof b - valof c\<bar> > ulp b \<Longrightarrow>\<bar>valof c - a\<bar> > 0.5*ulp b" by argo
    with b_diff have smaller_case: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow> \<bar>valof b - valof c\<bar> > ulp b \<Longrightarrow> \<bar>valof b - a\<bar> < \<bar>valof c - a\<bar>" by force

    from b_diff bc_rel have e_1: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow> valof b \<ge> valof c \<Longrightarrow> valof b \<ge> a \<Longrightarrow> \<bar>valof c - a\<bar> = 0.5*ulp b \<Longrightarrow> \<bar>valof b - valof c\<bar> = ulp b" by argo
    from b_diff bc_rel have e_2: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>valof b < valof c \<Longrightarrow> valof b \<ge> a \<Longrightarrow> \<bar>valof c - a\<bar> = 0.5*ulp b \<Longrightarrow> \<bar>valof b - valof c\<bar> = ulp b" by argo
    from b_diff bc_rel have e_3: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>valof b \<ge> valof c \<Longrightarrow> valof b < a \<Longrightarrow> \<bar>valof c - a\<bar> = 0.5*ulp b \<Longrightarrow> \<bar>valof b - valof c\<bar> = ulp b" by argo
    from b_diff bc_rel have e_4: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>valof b < valof c \<Longrightarrow> valof b < a \<Longrightarrow> \<bar>valof c - a\<bar> = 0.5*ulp b \<Longrightarrow> \<bar>valof b - valof c\<bar> = ulp b" by argo
    from e_1 e_2 e_3 e_4 have "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>\<bar>valof c - a\<bar> = 0.5*ulp b \<Longrightarrow> \<bar>valof b - valof c\<bar> = ulp b" by argo
    with b_diff have smaller_case: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow> \<bar>valof b - valof c\<bar> > ulp b \<Longrightarrow> \<bar>valof b - a\<bar> < \<bar>valof c - a\<bar>" sorry

    from assms ulp_accuracy_def have b_diff: "\<bar>valof b - a\<bar> \<le> 0.5*ulp b" by fast
    from bc_rel b_diff have 1: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow> valof b \<ge> valof c \<Longrightarrow> valof b \<ge> a \<Longrightarrow> \<bar>valof c - a\<bar> \<ge> 0.5*ulp b" by fastforce
    from bc_rel b_diff have 2: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>valof b < valof c \<Longrightarrow> valof b \<ge> a \<Longrightarrow> \<bar>valof c - a\<bar> \<ge> 0.5*ulp b" by fastforce
    from bc_rel b_diff have 3: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>valof b \<ge> valof c \<Longrightarrow> valof b < a \<Longrightarrow> \<bar>valof c - a\<bar> \<ge> 0.5*ulp b" by fastforce
    from bc_rel b_diff have 4: "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>valof b < valof c \<Longrightarrow> valof b < a \<Longrightarrow> \<bar>valof c - a\<bar> \<ge> 0.5*ulp b" by fastforce
    from 1 2 3 4 have "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow>\<bar>valof c - a\<bar> \<ge> 0.5*ulp b" by argo
    with b_diff have "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow> \<bar>valof b - a\<bar> \<le> \<bar>valof c - a\<bar>" by force
    with b_diff show "IEEE.exponent b \<noteq> IEEE.exponent c \<Longrightarrow> \<bar>valof b - a\<bar> < \<bar>valof c - a\<bar> \<or> \<bar>valof b - a\<bar> = \<bar>valof c - a\<bar> \<and> odd (fraction c)" sorry
  qed
  oops

thm unat_lt2p
lemma float_fraction_limit1:
  assumes "\<forall>xa::nat. (xa < f)"
  shows "(case a of b \<Rightarrow> (xa::nat)) < f"
  using assms 
  by simp

lemma float_fraction_limit2:
  assumes "\<forall>xa. (unat xa < f)"
  shows "(case a of b \<Rightarrow> (unat xa)) < f"
  thm float_fraction_limit1[where xa="unat xa"] oops


(*lemma float_fraction_limit:
  shows "fraction (a::('e,'f) float) < (2::nat)^LENGTH('f)"
  find_theorems "fraction _"
  find_theorems "Rep_float _"
  find_theorems "(case _ of _ \<Rightarrow> _)"
  using float_frac_le sledgehammer
  thm float_fraction_limit1[where f="(2::nat)^LENGTH('f)"]
  using unat_lt2p[where 'a='f] float_fraction_limit1 sorry*)
  
  


(*lemma diff_exponent:
  assumes "exponent (a::('e, 'f) float) \<noteq> exponent (b::('e, 'f) float)"
  shows "valof a \<noteq> valof b"
  apply(cases "sign a = sign b")
  apply(cases "exponent a = 0 \<or> exponent b = 0")
  subgoal proof -
    from zero_val_exponent assms have not_zero: "\<not>(valof a = 0 \<and> valof b = 0)" by metis
    then show "sign a = sign b \<Longrightarrow> valof a \<noteq> valof b" sorry
  qed
  subgoal
    apply(simp add:valof_eq2)
    subgoal proof -
      have f_a: "real (fraction a) < (2::real) ^ LENGTH('f)" sorry
      have f_b: "real (fraction b) < (2::real) ^ LENGTH('f)" sorry
    show "(0::nat) < IEEE.exponent a \<and> (0::nat) < IEEE.exponent b \<Longrightarrow>
    (2::real) ^ IEEE.exponent a * ((2::real) ^ LENGTH('f) + real (fraction a)) \<noteq>
    (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f) + real (fraction b))" sorry
  qed done
  subgoal proof -
    from zero_val_exponent assms have not_zero: "\<not>(valof a = 0 \<and> valof b = 0)" by metis
    from valof_nonneg valof_nonpos have "sign a \<noteq> sign b \<Longrightarrow> (valof a \<ge> 0 \<and> valof b \<le> 0) \<or> (valof a \<le> 0 \<and> valof b \<ge> 0)"
      by (metis sign_cases)
    with not_zero show "sign a \<noteq> sign b \<Longrightarrow> valof a \<noteq> valof b" by argo
  qed
  done*)

lemma rounding_0_5_ulp: 
  assumes "\<bar>a\<bar> < threshold TYPE(('e, 'f)float)" 
          "a_r = ((round To_nearest a)::('e, 'f) float)"
  shows "ulp_accuracy a a_r 0.5"
  unfolding ulp_accuracy_def 
  using assms apply (simp add: rounded_threshold_is_finite del:round.simps)
  apply(simp add: is_finite_nonempty closest_is_closest rounded_threshold_is_closest)
  find_theorems "is_closest"
  (*
  closest (valof) (\<lambda>a. even (fraction a)) {a. is_finite a} y)
  is_closest v s x a \<longleftrightarrow> a \<in> s \<and> (\<forall>b. b \<in> s \<longrightarrow> \<bar>v a - x\<bar> \<le> \<bar>v b - x\<bar>)
  closest v p s x = (SOME a. is_closest v s x a \<and> ((\<exists>b. is_closest v s x b \<and> p b) \<longrightarrow> p a))
*)
  subgoal proof -
  from is_finite_nonempty rounded_threshold_is_finite have fin_a_r: "is_finite a_r"
    using assms(1) assms(2) by blast 
  with ulp_accuracy_def have "\<not>ulp_accuracy a a_r 0.5 \<longrightarrow> \<bar>(valof a_r - a)\<bar> > 0.5 * (ulp a_r)" by fastforce
  from ulp_0_5_exists obtain b where "ulp_accuracy a (b::('e,'f) float) 0.5"
    using assms(1) by blast
  (*with smaller_ulp_is_closer fin_a_r ulp_accuracy_def have "\<not>ulp_accuracy a a_r 0.5 \<longrightarrow> \<bar>(valof a_r - a)\<bar> \<ge> \<bar>(valof b - a)\<bar>" by blast
  from is_closest_def smaller_ulp_is_closer ulp_0_5_exists have "\<not>ulp_accuracy a a_r 0.5 \<longrightarrow> \<not>is_closest (valof) (Collect is_finite) a a_r" sorry
  with ulp_0_5_exists smaller_ulp_is_closer show ?thesis oops
  with ulp_0_5_exists1 ulp_accuracy_def have "\<bar>(valof a_r) - a + (valof (one_lp a_r))\<bar> < \<bar>(valof a_r) - a\<bar> \<or> \<bar>(valof a_r) - a - (valof (one_lp a_r))\<bar> < \<bar>(valof a_r) - a\<bar>"
    sledgehammer
    oops*)
  oops


(*lemma closer_means_ulp_0_5:
  assumes "ulp_accuracy a b 0.5"
  shows "\<bar>(valof (b::('e,'f) float) - a)\<bar> \<ge> \<bar>(valof (c::('e,'f) float) - a)\<bar> \<and> is_finite c \<longrightarrow> ulp_accuracy a c 0.5"
  apply (cases "exponent b \<le> exponent c")
  subgoal proof -
    have num_ge: "exponent b \<le> exponent c \<longrightarrow> (2::real) ^ max (IEEE.exponent b) (1::nat) \<le> (2::real) ^ max (IEEE.exponent c) (1::nat)" by fastforce 
    have div_g0: "(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f)) > 0" by auto
    from num_ge div_g0 have "exponent b \<le> exponent c \<longrightarrow> ((2::real) ^ max (IEEE.exponent b) (1::nat) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))) \<le> ((2::real) ^ max (IEEE.exponent c) (1::nat) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f)))" sledgehammer
      by (simp add: divide_right_mono)
    with ulp_equivelance have ulp_bigger: "exponent b \<le> exponent c \<longrightarrow> ulp b \<le> ulp c" by metis
    from assms ulp_accuracy_def have "\<bar>(valof (b::('e,'f) float) - a)\<bar> \<le> 0.5*ulp b" by blast
    with ulp_bigger have "exponent b \<le> exponent c \<longrightarrow> \<bar>(valof (b::('e,'f) float) - a)\<bar> \<le> 0.5*ulp c" by fastforce
    with ulp_accuracy_def show "IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow> \<bar>valof c - a\<bar> \<le> \<bar>valof b - a\<bar> \<and> is_finite c \<longrightarrow> ulp_accuracy a c ((5::real) / (10::real))" by fastforce
  qed
  subgoal proof -
  
    show ?thesis sorry
  qed
  oops*)

lemma float_frac_ge:
  shows "fraction x \<ge> 0"
  by simp

lemma div_less2: "a < b \<and> c > 0 \<Longrightarrow> a/c < b/c" for a b c :: "'a::linordered_field"
  by (simp add: divide_less_cancel)

lemma valof_divider_g0: 
  shows "((2::real) ^ x * (2::real) ^y) > 0"
  using bias_def by simp

lemma ulp_is_smaller:
  shows "exponent (b::('e, 'f) float) \<noteq> 0 \<Longrightarrow> \<bar>valof b\<bar> > ulp b" 
  apply(simp add:abs_valof_eq2 ulp_equivelance bias_def diff_1_ulp_helper1)
  apply(rule div_less2)
  apply(simp)
  by (smt (verit) len_gt_0 of_nat_less_0_iff one_less_power)

lemma mul_less: 
  assumes "(z::real) > 0" and "(x::real) \<ge> (y::real)"
  shows "x/z \<ge> y/z"
  using assms
  by (simp add: IEEE_Properties.div_less)

lemma closest_means_ulp_0_5_helper: "(a::real) \<le> (b::real) \<Longrightarrow> ((2::real) ^ (c::nat) / 2 ^ bias TYPE(('e, 'f) float)) *
            (2 ^ LENGTH('f) + a) / 2 ^ LENGTH('f) \<le> (2 ^ c / 2 ^ bias TYPE(('e, 'f) float)) *
            real ((2::nat) ^ LENGTH('f) + b) / 2 ^ LENGTH('f)"
proof -
  have g0: "(2::real) ^ LENGTH('f) > (0::real)" by simp
  have g0_2: "((2::real) ^ c / 2 ^ bias TYPE(('e, 'f) float)) > 0" by simp
  then have "a \<le> b \<Longrightarrow> (2 ^ LENGTH('f) + a) \<le> (2 ^ LENGTH('f) + b)" by simp
  with g0 have "a \<le> b \<Longrightarrow> (2 ^ LENGTH('f) + a)  / 2 ^ LENGTH('f)\<le> (2 ^ LENGTH('f) + b) / 2 ^ LENGTH('f)"
    by (simp add: IEEE_Properties.div_less)
  with g0_2 show "a \<le> b \<Longrightarrow> ((2::real) ^ c / 2 ^ bias TYPE(('e, 'f) float))* (2 ^ LENGTH('f) + a)  / 2 ^ LENGTH('f)\<le> ((2::real) ^ c / 2 ^ bias TYPE(('e, 'f) float))*(2 ^ LENGTH('f) + b) / 2 ^ LENGTH('f)"by (simp add:mul_less) 
qed


(*lemma assumes "\<forall>y. \<exists>x. P x y" shows "\<exists>x. \<forall>y. P x y"
  apply (rule exI)
proof 
  fix y
  from assms obtain x where "P x y" by blast
  show "P x y"
  
    oops

lemma "\<exists>xs::nat list. xs=[]"
proof -
  obtain xs::"nat list" where "xs=[]" by simp

  show ?thesis
    apply (rule exI[where x=xs])
    by fact
*)

lemma half_times_power: "x > 0 \<longrightarrow> (0.5::real)*2^x = 2^(x-1)"
  apply(induction x)
  by auto

lemma power_2_at_least_4: "(x::nat)>1 \<longrightarrow> (2::real)^x \<ge> 4"
  apply(induction x)
   apply auto
  using Suc_lessI by fastforce

lemma closest_means_ulp_0_5:
  assumes "ulp_accuracy a (b::('e,'f) float) 0.5" and "LENGTH('f)> 1"
  and "(\<forall>(b::('e,'f) float). b \<in> {a. is_finite a} \<longrightarrow> \<bar>valof (c::('e,'f) float) - a\<bar> \<le> \<bar>valof b - a\<bar>)"
  shows "is_finite c \<longrightarrow> ulp_accuracy a c 0.5"
  apply (cases "exponent b \<le> exponent c")
subgoal proof -
  

    have num_ge: "exponent b \<le> exponent c \<longrightarrow> (2::real) ^ max (IEEE.exponent b) (1::nat) \<le> (2::real) ^ max (IEEE.exponent c) (1::nat)" by fastforce 
    have div_g0: "(2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f)) > 0" by auto
    from num_ge div_g0 have "exponent b \<le> exponent c \<longrightarrow> ((2::real) ^ max (IEEE.exponent b) (1::nat) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f))) \<le> ((2::real) ^ max (IEEE.exponent c) (1::nat) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f)))" sledgehammer
      by (simp add: divide_right_mono)
    with ulp_equivelance have ulp_bigger: "exponent b \<le> exponent c \<longrightarrow> ulp b \<le> ulp c" by metis
    from assms ulp_accuracy_def have "\<bar>(valof (b::('e,'f) float) - a)\<bar> \<le> 0.5*ulp b" by blast
    with ulp_bigger have "exponent b \<le> exponent c \<longrightarrow> \<bar>(valof (b::('e,'f) float) - a)\<bar> \<le> 0.5*ulp c" by fastforce
    with ulp_accuracy_def show "exponent b \<le> exponent c \<Longrightarrow> is_finite c \<longrightarrow> ulp_accuracy a c ((5::real) / (10::real))"
      by (metis assms(1) assms(3) dual_order.trans mem_Collect_eq mult.commute)
  qed
  apply (cases "exponent b = 1")
  subgoal proof -
    have " \<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow>
    IEEE.exponent b = (1::nat) \<Longrightarrow> exponent b = max (IEEE.exponent c) (Suc (0::nat))" by fastforce
    with ulp_equivelance have ulp_same: "\<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow>
    IEEE.exponent b = (1::nat) \<Longrightarrow> ulp b = ulp c"
      by (metis max.absorb1 max.commute nat_le_linear)
    from assms ulp_accuracy_def have distance_smaller: "\<bar>valof c - a\<bar> \<le> \<bar>valof b - a\<bar>" by blast
    from assms ulp_accuracy_def have "\<bar>valof b - a\<bar> \<le> 0.5*ulp b" by blast
    with ulp_same distance_smaller ulp_accuracy_def show "\<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow>
    IEEE.exponent b = (1::nat) \<Longrightarrow> is_finite c \<longrightarrow> ulp_accuracy a c ((5::real) / (10::real))" by force
  qed
  subgoal proof -

    (*float_frac_le
    from  float_frac_le valof_def  have "\<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow> IEEE.exponent b \<noteq> (1::nat) \<Longrightarrow> \<bar>valof c\<bar> < \<bar>valof b\<bar>" sorry
    *)have exp_not_0: "\<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow> IEEE.exponent b \<noteq> (1::nat) \<Longrightarrow> exponent b \<noteq> 0" by simp
    from assms ulp_accuracy_def have "\<bar>a\<bar> \<ge> \<bar>valof b\<bar> - 0.5*ulp b"
      by (smt (verit, ccfv_threshold))
    with abs_valof_eq2 exp_not_0 have "\<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow> IEEE.exponent b \<noteq> (1::nat) \<Longrightarrow> \<bar>a\<bar> \<ge> (2::real) ^ exponent b / (2::real) ^ bias TYPE(('e, 'f) float) *
          ((2::real) ^ LENGTH('f) + real (fraction b)) /
          (2::real) ^ LENGTH('f) - 0.5*ulp b" by metis
    then have "\<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow> IEEE.exponent b \<noteq> (1::nat) \<Longrightarrow> \<bar>a\<bar> \<ge> (2::real) ^ exponent b / (2::real) ^ bias TYPE(('e, 'f) float) *
          ((2::real) ^ LENGTH('f) + real (fraction b)) /
          (2::real) ^ LENGTH('f) - 0.5*(2::real) ^exponent b / (2::real) ^ (bias TYPE(('e, 'f) float) + LENGTH('f))" by (simp add:ulp_equivelance bias_def)
    then have "\<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow> IEEE.exponent b \<noteq> (1::nat) \<Longrightarrow> \<bar>a\<bar> \<ge> (2::real) ^ exponent b / (2::real) ^ bias TYPE(('e, 'f) float) *
          ((2::real) ^ LENGTH('f) + real (fraction b)) /
          (2::real) ^ LENGTH('f) - 0.5*(2::real) ^ exponent b / (2::real) ^ (bias TYPE(('e, 'f) float) + LENGTH('f))" by (simp add:bias_def)
    from sign_valof_diff have "sign b \<noteq> sign c \<Longrightarrow> \<bar>valof c - a\<bar> \<ge> \<bar>valof b\<bar> + \<bar>valof c\<bar> - \<bar>valof b - a\<bar>"
      by (smt (verit))
    with assms ulp_accuracy_def have "exponent b \<noteq> 0 \<Longrightarrow> sign b \<noteq> sign c \<Longrightarrow> \<bar>valof c - a\<bar> > \<bar>valof b - a\<bar>" apply(simp add: assms ulp_accuracy_def ulp_is_smaller)
      by (smt (verit, ccfv_SIG) not_gr_zero ulp_is_smaller)
    with assms have "exponent b \<noteq> 0 \<Longrightarrow> sign b = sign c" using assms apply(simp add:assms)
      using assms ulp_accuracy_def mem_Collect_eq by fastforce

    from assms ulp_accuracy_def have diff_smaller: "\<bar>valof c - a\<bar> \<le> \<bar>valof b - a\<bar>" by blast

   
    from abs_valof_eq2 have "exponent c < exponent b - 1 \<Longrightarrow> \<bar>valof c\<bar> \<le> (if exponent c = 0
       then (2 / 2 ^ bias TYPE(('e, 'f) float)) *
            (real (fraction c) / 2 ^ LENGTH('f))
       else (2 ^ (exponent b-2) / 2 ^ bias TYPE(('e, 'f) float)) *
            (2 ^ LENGTH('f) + real (fraction c)) / 2 ^ LENGTH('f))" 
      apply (auto simp add:abs_valof_eq2)
      apply(rule div_less)
      apply simp 
      apply(rule mult_right_mono)
      by (simp_all)
    then have val_c: "exponent c < exponent b - 1 \<Longrightarrow> \<bar>valof c\<bar> \<le> (2 ^ (exponent b-2) / 2 ^ bias TYPE(('e, 'f) float)) *
            (2 ^ LENGTH('f) + real (fraction c)) / 2 ^ LENGTH('f)" 
      apply (cases "exponent c = 0") 
       apply (simp_all)
      apply(rule Orderings.preorder_class.dual_order.trans)
       apply simp_all
      apply(rule div_less)
      apply (simp add:power_add)
      subgoal proof -
        have "Suc (0::nat) < IEEE.exponent b \<Longrightarrow> (IEEE.exponent b - Suc (Suc (0::nat))) \<ge> 0" by linarith
        then have "(1::real) \<le> 2^(IEEE.exponent b - (2::nat))" by(simp add:self_le_power)
        then have a: "(1::real) * real (fraction c) \<le> (2^(IEEE.exponent b -  Suc (Suc (0::nat)))) * real (fraction c)" using mult_right_mono[where a="1" and b="2^(IEEE.exponent b - Suc (Suc (0::nat)))" and c="real (fraction c)"] by simp
        have b: "2* real (fraction c) \<le> (2::real) ^ LENGTH('f) + real (fraction c)" using float_frac_le[where a=c] by simp
        then have "(2^(IEEE.exponent b - Suc (Suc (0::nat))))* (2::real)* real (fraction c) \<le> (2::real) ^ (IEEE.exponent b - Suc (Suc (0::nat))) * ((2::real) ^ LENGTH('f) + real (fraction c))" by simp thm mult_right_mono
        with a show "(2::real) * real (fraction c) \<le> (2::real) ^ (IEEE.exponent b - (2::nat)) * ((2::real) ^ LENGTH('f) + real (fraction c))"
          by (smt (verit, best) One_nat_def Suc_1 distrib_right mult_2_right) qed
      done
    with float_frac_le have "exponent c < exponent b - 1 \<Longrightarrow> \<bar>valof c\<bar> \<le> (2 ^ (exponent b-2) / 2 ^ bias TYPE(('e, 'f) float)) *
            (2 ^ LENGTH('f) + (2::nat) ^ LENGTH('f)) / 2 ^ LENGTH('f)" proof -
      from float_frac_le have real_frac_le: "real (fraction c) \<le> (2::nat) ^ LENGTH('f)"
        by (smt (verit, best) of_nat_1 of_nat_diff of_nat_mono one_le_numeral one_le_power)
      from closest_means_ulp_0_5_helper[where a="real (fraction c)" and b="(2::nat) ^ LENGTH('f)" and c="(exponent b-2)"] real_frac_le
      have "(2 ^ (exponent b-2) / 2 ^ bias TYPE(('e, 'f) float)) *
            (2 ^ LENGTH('f) + real (fraction c)) / 2 ^ LENGTH('f) \<le> (2 ^ (exponent b-2) / 2 ^ bias TYPE(('e, 'f) float)) *
            (2 ^ LENGTH('f) + (2::nat) ^ LENGTH('f)) / 2 ^ LENGTH('f)" using closest_means_ulp_0_5_helper[where a="real (fraction c)" and b="(2::nat) ^ LENGTH('f)" and c="(exponent b-2)"] real_frac_le by blast
      then show "exponent c < exponent b - 1 \<Longrightarrow> \<bar>valof c\<bar> \<le> (2 ^ (exponent b-2) / 2 ^ bias TYPE(('e, 'f) float)) *
            (2 ^ LENGTH('f) + (2::nat) ^ LENGTH('f)) / 2 ^ LENGTH('f)" 
        using val_c by linarith
    qed
    then have "exponent c < exponent b - 1 \<Longrightarrow> \<bar>valof c\<bar> \<le> (2 ^ (exponent b-2) / 2 ^ bias TYPE(('e, 'f) float)) *2" by simp
    then have "exponent c < exponent b - 1 \<Longrightarrow> \<bar>valof c\<bar> \<le> (2 * 2 ^ (exponent b-2) / 2 ^ bias TYPE(('e, 'f) float))" by argo
    
    then have "exponent c < exponent b - 1 \<Longrightarrow> \<bar>valof c\<bar> \<le> ( 2 ^ (exponent b-2+(1::nat)) / 2 ^ bias TYPE(('e, 'f) float))" by auto
    then have "exponent c < exponent b - 1 \<Longrightarrow> \<bar>valof c\<bar> \<le> ( 2 ^ ((exponent b)-(2::nat)+(1::nat)) / 2 ^ bias TYPE(('e, 'f) float))" by blast
    then have val_c_simplified: "exponent c < exponent b - 1 \<Longrightarrow> \<bar>valof c\<bar> \<le> ( 2 ^ ((exponent b)-(1::nat)) / 2 ^ bias TYPE(('e, 'f) float))"
      by (smt (verit) add_is_0 diff_add_inverse2 diff_diff_left gr_implies_not0 nat_1_add_1 power_eq_if)
    have "\<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow>  \<bar>valof b\<bar> = (2 ^ (exponent b) / 2 ^ bias TYPE(('e, 'f) float)) *
            (2 ^ LENGTH('f) + real (fraction b)) / 2 ^ LENGTH('f)"  by (simp add:abs_valof_eq2)
    with float_frac_ge have "\<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow>  \<bar>valof b\<bar> \<ge> (2 ^ (exponent b) / 2 ^ bias TYPE(('e, 'f) float)) *
            (2 ^ LENGTH('f)) / 2 ^ LENGTH('f)"
      by (smt (verit, del_insts) divide_nonneg_nonneg divide_right_mono mult_left_mono of_nat_0_le_iff zero_le_power)
    then have "\<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow>  \<bar>valof b\<bar> \<ge> (2 ^ (exponent b) / 2 ^ bias TYPE(('e, 'f) float))" by fastforce
    then have "\<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow>  \<bar>valof b\<bar> \<ge> (2 ^ (exponent b-1+1) / 2 ^ bias TYPE(('e, 'f) float))" by force
    then have val_b_simplified: "\<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow>  \<bar>valof b\<bar> \<ge> (2*2 ^ (exponent b-1) / 2 ^ bias TYPE(('e, 'f) float))"
      by (metis power_add power_commutes power_one_right)
    have "\<bar>valof b - valof c\<bar> \<ge> \<bar>valof b\<bar> - \<bar>valof c\<bar>" by auto
    with val_b_simplified val_c_simplified have b_c_diff: "exponent c < exponent b - 1 \<Longrightarrow> \<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow>  \<bar>valof b - valof c\<bar> \<ge> (2 ^ (exponent b-1) / 2 ^ bias TYPE(('e, 'f) float))" by argo
    from assms ulp_accuracy_def have "\<bar>valof b - a\<bar> \<le> 0.5*ulp b" by blast
    with ulp_equivelance have "\<bar>valof b - a\<bar> \<le> 0.5*((2::real) ^ max (IEEE.exponent b) (1::nat) / (2::real) ^ ((2::nat) ^ (LENGTH('e) - (1::nat)) - (1::nat) + LENGTH('f)))" by metis
    with bias_def have "\<bar>valof b - a\<bar> \<le> 0.5*((2::real) ^ max (IEEE.exponent b) (1::nat) / (2::real) ^ (bias TYPE(('e, 'f) float) + LENGTH('f)))" by metis
    then have "\<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow> \<bar>valof b - a\<bar> \<le> 0.5*((2::real) ^ exponent b / (2::real) ^ (bias TYPE(('e, 'f) float) + LENGTH('f)))" by simp
    with half_times_power have val_b_min_a: "\<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow> \<bar>valof b - a\<bar> \<le> ((2::real) ^ (exponent b - 1) / (2::real) ^ (bias TYPE(('e, 'f) float) + LENGTH('f)))" by auto
    with b_c_diff have "exponent c < exponent b - 1 \<Longrightarrow> \<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow>  \<bar>valof c - a\<bar> \<ge> (2 ^ (exponent b-1) / 2 ^ bias TYPE(('e, 'f) float)) - ((2::real) ^ (exponent b - 1) / (2::real) ^ (bias TYPE(('e, 'f) float) + LENGTH('f)))" by argo
    then have "exponent c < exponent b - 1 \<Longrightarrow> \<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow>  \<bar>valof c - a\<bar> \<ge> (2^LENGTH('f)) * (2 ^ (exponent b-1) / 2 ^ bias TYPE(('e, 'f) float))/(2^LENGTH('f)) - ((2::real) ^ (exponent b - 1) / (2::real) ^ (bias TYPE(('e, 'f) float) + LENGTH('f)))" by simp
    then have "exponent c < exponent b - 1 \<Longrightarrow> \<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow>  \<bar>valof c - a\<bar> \<ge> (2^LENGTH('f)) * (2 ^ (exponent b-1) / 2 ^ (bias TYPE(('e, 'f) float)+LENGTH('f))) - ((2::real) ^ (exponent b - 1) / (2::real) ^ (bias TYPE(('e, 'f) float) + LENGTH('f)))"
      by (simp add: power_add)
    with b_c_diff have val_c_min_a: "exponent c < exponent b - 1 \<Longrightarrow> \<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow>  \<bar>valof c - a\<bar> \<ge> ((2^LENGTH('f))-1)*(2 ^ (exponent b-1) / 2 ^ (bias TYPE(('e, 'f) float)+LENGTH('f)))" by argo
    have "LENGTH('f)> 1 \<Longrightarrow> (((2::real)^LENGTH('f))-1)*(2 ^ (exponent b-1)) \<ge> (4-1)*(2 ^ (exponent b-1))" by(simp add:power_2_at_least_4[where x="LENGTH('f)"])
    then have "exponent c < exponent b - 1 \<Longrightarrow> \<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow> LENGTH('f)> 1 \<Longrightarrow> (((2::real)^LENGTH('f))-1)*(2 ^ (exponent b-1)/ 2 ^ (bias TYPE(('e, 'f) float)+LENGTH('f))) \<ge> (4-1)*(2 ^ (exponent b-1)/ 2 ^ (bias TYPE(('e, 'f) float)+LENGTH('f)))" by (simp add:mul_less)
    with val_c_min_a have "exponent c < exponent b - 1 \<Longrightarrow> \<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow> LENGTH('f)> 1 \<Longrightarrow> \<bar>valof c - a\<bar> \<ge> (4-1)*(2 ^ (exponent b-1)/ 2 ^ (bias TYPE(('e, 'f) float)+LENGTH('f)))" by argo
    with val_b_min_a have "exponent c < exponent b - 1 \<Longrightarrow> \<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow> LENGTH('f)> 1 \<Longrightarrow> \<bar>valof c - a\<bar> -\<bar>valof b - a\<bar> \<ge> 2*(2 ^ (exponent b-1)/ 2 ^ (bias TYPE(('e, 'f) float)+LENGTH('f)))" by argo
    then have "exponent c < exponent b - 1 \<Longrightarrow> \<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow> LENGTH('f)> 1 \<Longrightarrow> \<bar>valof c - a\<bar> -\<bar>valof b - a\<bar> > 0"
      by (smt (verit) divide_eq_0_iff power_eq_0_iff val_b_min_a)
    then have "exponent c < exponent b - 1 \<Longrightarrow> \<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow> LENGTH('f)> 1 \<Longrightarrow> \<bar>valof c - a\<bar> > \<bar>valof b - a\<bar>" by argo
    with assms have "exponent c < exponent b - 1 \<Longrightarrow> \<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow> LENGTH('f)> 1 \<Longrightarrow> False"
      using diff_smaller by linarith 
    with assms have "\<not> IEEE.exponent b \<le> IEEE.exponent c \<Longrightarrow> exponent c = exponent b - 1" by fastforce
    oops

find_theorems "ulp_accuracy"
end