theory IEEE_Properties_Basic_Extension
imports "IEEE_Floating_Point.Conversion_IEEE_Float" "HOL-Library.Extended_Real"
begin

(*definition for valof using extended reals*)
definition extended_valof :: "('e, 'f) float \<Rightarrow> ereal"
  where "extended_valof x = (if x = (plus_infinity::('e, 'f) float) 
    then PInfty else (if x = (minus_infinity::('e, 'f) float) 
    then MInfty else ereal (valof x)))"

(*generic lemmas*)
lemma abs_less_conv: "\<bar>a+b\<bar> \<le> m \<longleftrightarrow> a+b\<in>{-m..m}" for m :: real
  by auto

lemma power_2_simp: "(2::real)^x = (2::nat)^x"
  by simp

lemma float_frac_ge:
  shows "fraction x \<ge> 0"
  by simp

lemma sign_rewrite_tmp: "(- (1::real)) ^ (Suc (0::nat) - sign x) = (- (1::real)) * (- (1::real)) ^ (sign x)"
proof -
  from sign_cases consider "sign x = 0" | "sign x = 1" by metis
  then show ?thesis proof cases
    case 1
    then show ?thesis by force
  next
    case 2
    then show ?thesis by fastforce
  qed qed

lemma valof_minus[simp]: "valof (-a) = - valof a" 
  by (simp add:valof_eq sign_minus_float sign_rewrite_tmp)

lemma fsub_eq_fadd_minus: "fsub m a b = fadd m a (-b)"
  unfolding fsub_def fadd_def
  apply (simp add:float_neg_sign1) done

lemma abs_pow_min_1:
  shows "\<bar>(- 1) ^ x * (y::real)\<bar> = \<bar>y\<bar>"
  apply(induction x)
  by auto

lemma bias_nonneg:
  shows "bias x \<ge> 0"
  unfolding bias_def
  by blast

lemma bias_pos:
  assumes "LENGTH('e) > 1"
  shows "bias  TYPE(('e, 'f) float) > 0"
  unfolding bias_def
  using assms
  by (meson one_less_numeral_iff one_less_power semiring_norm(76) zero_less_diff)

lemma float_frac_l: "fraction (a::('e,'f) float) < 2^LENGTH('f)"
  by(auto simp: fraction_def Abs_float_inverse split: prod.splits)

lemma valof_eq2:
  "valof x =
    (if exponent x = 0
       then (- 1) ^ sign x * (2 / 2 ^ bias TYPE(('a, 'b) float)) *
            (real (fraction x) / 2 ^ LENGTH('b))
       else (- 1) ^ sign x * (2 ^ exponent x / 2 ^ bias TYPE(('a, 'b) float)) *
            (2 ^ LENGTH('b) + real (fraction x)) / 2 ^ LENGTH('b))"
  for x::"('a, 'b) float"
  by (simp add:valof_eq bias_def divide_simps unat_eq_0)

lemma abs_valof_eq2:
  "\<bar>valof x\<bar> =
    (if exponent x = 0
       then (2 / 2 ^ bias TYPE(('a, 'b) float)) *
            (real (fraction x) / 2 ^ LENGTH('b))
       else (2 ^ exponent x / 2 ^ bias TYPE(('a, 'b) float)) *
            (2 ^ LENGTH('b) + real (fraction x)) / 2 ^ LENGTH('b))"
  for x::"('a, 'b) float"
  apply(cases "exponent x= 0")
  by(simp_all add:valof_eq2 abs_mult)

lemma abs_valof_eq:
  "\<bar>valof x\<bar> =
    (if exponent x = 0
       then (2 / 2 ^ bias TYPE(('a, 'b) float)) *
            (real (fraction x) / 2 ^ LENGTH('b))
       else (2 ^ exponent x / 2 ^ bias TYPE(('a, 'b) float)) *
            (1 + real (fraction x) / 2 ^ LENGTH('b)))"
  for x::"('a, 'b) float"
  apply(cases "exponent x= 0")
  by(simp_all add:valof_eq abs_mult)

lemma abs_valof_min:
  "\<bar>valof x\<bar> \<ge>
    (if exponent x = 0
       then 0
       else 2 ^ exponent x / 2 ^ bias TYPE(('a, 'b) float))"
  for x::"('a, 'b) float"
  apply(cases "exponent x= 0")
   apply(simp_all add:abs_valof_eq2 float_frac_ge)
proof -
  have exp_bigger: "(0::nat) < 2 ^ IEEE.exponent x" by auto
  have "(1::nat)\<le> (2 ^ LENGTH('b) + real (fraction x))/ 2 ^ LENGTH('b)" by(simp add:float_frac_ge)
  then have "(1::nat)/ 2 ^ bias TYPE(('a, 'b) IEEE.float)\<le> (2 ^ LENGTH('b) + real (fraction x))/ 2 ^ LENGTH('b)/ 2 ^ bias TYPE(('a, 'b) IEEE.float)" 
    apply(rule divide_right_mono) by simp
  then have "(1::nat)/ 2 ^ bias TYPE(('a, 'b) IEEE.float)\<le> (2 ^ LENGTH('b) + real (fraction x))/ (2 ^ bias TYPE(('a, 'b) IEEE.float) * 2 ^ LENGTH('b))" by argo
  then have "2 ^ IEEE.exponent x * 1/ 2 ^ bias TYPE(('a, 'b) IEEE.float)
    \<le> 2 ^ IEEE.exponent x * (2 ^ LENGTH('b) + real (fraction x)) / (2 ^ bias TYPE(('a, 'b) IEEE.float) * 2 ^ LENGTH('b))"
    using mult_le_cancel_left_pos[where c="2 ^ IEEE.exponent x" and a="1/ 2 ^ bias TYPE(('a, 'b) IEEE.float)" and b="(2 ^ LENGTH('b) + real (fraction x)) / (2 ^ bias TYPE(('a, 'b) IEEE.float) * 2 ^ LENGTH('b))"] by auto
  then show "2 ^ IEEE.exponent x / 2 ^ bias TYPE(('a, 'b) IEEE.float)
    \<le> 2 ^ IEEE.exponent x * (2 ^ LENGTH('b) + real (fraction x)) / (2 ^ bias TYPE(('a, 'b) IEEE.float) * 2 ^ LENGTH('b))" by fastforce
qed

lemma abs_valof_max':
  shows
  "\<bar>valof (x::('a, 'b) float)\<bar> <
    (if exponent x = 0
       then (2 / 2 ^ bias TYPE(('a, 'b) float))
       else 2*2 ^ exponent x / 2 ^ bias TYPE(('a, 'b) float))"
  apply(cases "exponent x= 0")
   apply(simp_all add:abs_valof_eq2)
  subgoal proof -
    from float_frac_l have " real (fraction x) / 2 ^ LENGTH('b) < 1" by auto
    with bias_pos have " real (fraction x) / 2 ^ LENGTH('b) / 2 ^ bias TYPE(('a, 'b) IEEE.float) < 1/ 2 ^ bias TYPE(('a, 'b) float)" using divide_strict_right_mono
      by (smt (verit) zero_less_power)
    with bias_nonneg show " 2 * real (fraction x) / (2 ^ bias TYPE(('a, 'b) IEEE.float) * 2 ^ LENGTH('b)) < 2 / 2 ^ bias TYPE(('a, 'b) IEEE.float)" by argo
  qed
  subgoal proof -
    from float_frac_l have " real (fraction x) / 2 ^ LENGTH('b) < 1" by auto
    then have "(2 ^ LENGTH('b) + real (fraction x)) / 2 ^ LENGTH('b) < 1 + 2 ^ LENGTH('b)/2 ^ LENGTH('b)" by argo
    then have "(2 ^ LENGTH('b) + real (fraction x)) / 2 ^ LENGTH('b) < 2" by auto
    with bias_pos have "(2 ^ LENGTH('b) + real (fraction x)) / 2 ^ LENGTH('b) / 2 ^ bias TYPE(('a, 'b) IEEE.float) < 2/ 2 ^ bias TYPE(('a, 'b) float)" using divide_strict_right_mono
      by (smt (verit) zero_less_power)
    then have "2 ^ IEEE.exponent x * (2 ^ LENGTH('b) + real (fraction x)) / 2 ^ LENGTH('b) / 2 ^ bias TYPE(('a, 'b) IEEE.float) < 2 ^ IEEE.exponent x * 2/ 2 ^ bias TYPE(('a, 'b) float)" using divide_strict_right_mono
      using divide_divide_eq_left linordered_comm_semiring_strict_class.comm_mult_strict_left_mono of_nat_numeral one_add_one power_add times_divide_eq_right by fastforce
    with bias_nonneg show "2 ^ IEEE.exponent x * (2 ^ LENGTH('b) + real (fraction x)) / (2 ^ bias TYPE(('a, 'b) IEEE.float) * 2 ^ LENGTH('b))
    < 2 * 2 ^ IEEE.exponent x / 2 ^ bias TYPE(('a, 'b) IEEE.float)" by argo
  qed
  done

lemma abs_valof_max:
  shows
  "\<bar>valof (x::('a, 'b) float)\<bar> <
    2*2 ^ exponent x / 2 ^ bias TYPE(('a, 'b) float)"
  apply(cases "exponent x = 0")
  using abs_valof_max' power_0
  apply (smt (verit, del_insts) numeral_One)
  using abs_valof_max'
  by (smt (verit, ccfv_SIG))

lemma valof_divider_g0: 
  shows "((2::real) ^ x * (2::real) ^y) > 0"
  using bias_def by simp

lemma abs_valof_ge_exp_ge:
  assumes "\<bar>valof (a::('e, 'f) float)\<bar> \<ge> \<bar>valof (b::('e, 'f) float)\<bar>"
  shows "exponent a \<ge> exponent b"
proof -
  from abs_valof_min have "(if IEEE.exponent b = 0 then 0 else 2 ^ IEEE.exponent b / 2 ^ bias TYPE(('e, 'f) IEEE.float))
  \<le> \<bar>valof b\<bar>" by blast
  with assms have "(if IEEE.exponent b = 0 then 0 else 2 ^ IEEE.exponent b / 2 ^ bias TYPE(('e, 'f) IEEE.float))
  \<le> \<bar>valof a\<bar>" by argo
  moreover from abs_valof_max have "\<bar>valof a\<bar> < 2 * 2 ^ IEEE.exponent a / 2 ^ bias TYPE(('e, 'f) IEEE.float)" by fast
  ultimately have "(if IEEE.exponent b = 0 then (0::real) else 2 ^ IEEE.exponent b / 2 ^ bias TYPE(('e, 'f) IEEE.float)) < 2 * 2 ^ IEEE.exponent a / 2 ^ bias TYPE(('e, 'f) IEEE.float)"
    by argo
  with bias_nonneg have "exponent b \<noteq> 0 \<Longrightarrow> 2 ^ IEEE.exponent b < (2::real) * 2 ^ IEEE.exponent a"
    by (simp add: divide_less_cancel)
  then have "exponent b \<noteq> 0 \<Longrightarrow> 2 ^ IEEE.exponent b < (2::real) ^ (1+ IEEE.exponent a)" by fastforce
  then have "exponent b \<noteq> 0 \<Longrightarrow> exponent b < 1 + exponent a"
    by (meson one_less_numeral_iff power_less_imp_less_exp semiring_norm(76))
  then show "exponent b \<le> exponent a" by linarith
qed

lemma abs_valof_order_exp:
  assumes "exponent (a::('e, 'f) float) > exponent (b::('e, 'f) float)"
  shows "\<bar>valof a\<bar> > \<bar>valof b\<bar>"
  apply(cases "exponent b=0")
  using assms apply(simp_all add:abs_valof_eq2 divide_less_cancel mult_less_0_iff)
  subgoal proof-
    from assms have exp_a: "exponent a \<ge> 1" by linarith
    have "2 ^ IEEE.exponent a * (2 ^ LENGTH('f)) \<le> 2 ^ IEEE.exponent a * (2 ^ LENGTH('f) + real (fraction a))" by(simp add:float_frac_ge)
    moreover with exp_a have "(2::real) * (2 ^ LENGTH('f)) \<le> 2 ^ IEEE.exponent a * (2 ^ LENGTH('f))" by (simp add: self_le_power)
    ultimately have "(2::real) * (2 ^ LENGTH('f)) \<le> 2 ^ IEEE.exponent a * (2 ^ LENGTH('f) + real (fraction a))" by linarith
    moreover from float_frac_le have "2 * real (fraction b) \<le> 2 * real (2 ^ LENGTH('f) - 1)" by force
    moreover have "2 * real (2 ^ LENGTH('f) - 1) < (2::real) * (2 ^ LENGTH('f))" by simp
    ultimately show "2 * real (fraction b) < 2 ^ IEEE.exponent a * (2 ^ LENGTH('f) + real (fraction a))" by argo qed
proof -
  from assms have exp_a: "exponent a \<ge> exponent b + 1" by linarith
  have "2 ^ IEEE.exponent a * (2 ^ LENGTH('f)) \<le> 2 ^ IEEE.exponent a * (2 ^ LENGTH('f) + real (fraction a))" by(simp add:float_frac_ge)
  moreover with exp_a exp_less have "(2::real) ^ (exponent b) * (2::real) * (2 ^ LENGTH('f)) \<le> 2 ^ IEEE.exponent a * (2 ^ LENGTH('f))" by fastforce
  ultimately have "(2::real) ^ (exponent b) * (2::real) * (2 ^ LENGTH('f)) \<le> 2 ^ IEEE.exponent a * (2 ^ LENGTH('f) + real (fraction a))" by linarith
  moreover from float_frac_le have "(2 ^ LENGTH('f) + real (fraction b)) \<le> 2 ^ LENGTH('f) + real (2 ^ LENGTH('f) - 1)" by force
  moreover then have "(2 ^ LENGTH('f) + real (fraction b)) < (2::real) * (2 ^ LENGTH('f))" apply (simp add: real_le_power_numeral_diff) by (metis Suc_pred le_imp_less_Suc pos2 zero_less_power)
  moreover then have "2 ^ IEEE.exponent b * (2 ^ LENGTH('f) + real (fraction b)) < 2 ^ IEEE.exponent b * (2::real) * (2 ^ LENGTH('f))" by force
  ultimately show "2 ^ IEEE.exponent b * (2 ^ LENGTH('f) + real (fraction b)) < 2 ^ IEEE.exponent a * (2 ^ LENGTH('f) + real (fraction a))" by linarith qed

lemma largets_l_threshold:
  "largest x < threshold x"
  unfolding largest_def threshold_def
proof -
  have "(2::real) ^ bias x * ((2::real) - (1::real) / (2::real) ^ LENGTH('b)) < (2::real) ^ bias x * ((2::real) - (1::real) / (2::real) ^ Suc LENGTH('b))" by(auto simp add:divide_strict_left_mono)
  then show "(2::real) ^ (emax x - (1::nat)) / (2::real) ^ bias x * ((2::real) - (1::real) / (2::real) ^ LENGTH('b))
    < (2::real) ^ (emax x - (1::nat)) / (2::real) ^ bias x * ((2::real) - (1::real) / (2::real) ^ Suc LENGTH('b))"
    by (smt (verit) divide_eq_0_iff divide_nonneg_nonneg mult_left_le_imp_le power_eq_0_iff zero_le_power)
qed

lift_definition example_nan::"('e ,'f) float" is "(0, -1, 1)" .
lemma example_nan_exp_frac:
  shows "exponent (example_nan::('e ,'f) float) = unat (- (1::'e word))" and "fraction example_nan = 1"
  unfolding example_nan_def
  by(auto simp: example_nan.rep_eq exponent_def fraction_def Abs_float_inverse split: prod.splits)

lemma some_nan_is_nan[simp]:
  "is_nan (some_nan::('e, 'f)float)"
  apply(simp add:some_nan_def some_eq_ex)
  unfolding example_nan_def
  apply (simp add: is_nan_def example_nan.rep_eq Abs_float_inverse emax_def  split: prod.splits)
  using example_nan_exp_frac
  by (metis less_numeral_extra(1))

(*lemmas about infinity*)
lemma float_exp_le2: "exponent a \<le> emax TYPE(('e, 'f)float) - 1 \<Longrightarrow> is_finite a"
  for a::"('e, 'f)float"
  unfolding float_defs
  by auto

lemma eq_exp_eq_finite: 
  assumes "exponent (a::('e,'f) float) = exponent (b::('e,'f) float)"
  shows "is_finite a = is_finite b"
  unfolding is_finite_def is_normal_def is_denormal_def is_zero_def
  using assms apply simp by fast

lemma infinity_is_infinity: "is_infinity (plus_infinity)"
  unfolding is_infinity_def
  unfolding plus_infinity_def
  by (metis infinity_simps(3) infinity_simps(5) plus_infinity_def)

lemma pinfinity_unfold[code_unfold]: "x = plus_infinity \<longleftrightarrow> is_infinity x \<and> sign x = 0"
  by (metis float_neg_sign infinity_is_infinity infinity_simps(1) is_infinity_cases)

lemma ninfinity_unfold[code_unfold]:  "x = minus_infinity \<longleftrightarrow> is_infinity x \<and> sign x = 1"
  by (metis infinity_is_infinity infinity_simps(1) infinity_simps(2) is_infinity_cases is_infinity_uminus zero_neq_one)

lemma extended_valof_finite: "\<not> is_infinity a \<Longrightarrow> extended_valof a = valof a"
  unfolding extended_valof_def
  using infinity_is_infinity by auto

lemma inf_not_zero: 
    "is_infinity x \<longrightarrow> \<not> is_zero x"
  using float_distinct(7) by auto

lemma pinfty_eq_plus_inifity: "extended_valof plus_infinity = PInfty" using extended_valof_def by metis
lemma minfty_eq_minus_inifity: "extended_valof minus_infinity = MInfty" unfolding extended_valof_def 
    using pinfty_eq_plus_inifity pinfinity_unfold ninfinity_unfold
    by force

lemma plus_infinity_bigger: "y \<le> extended_valof plus_infinity"
  unfolding extended_valof_def 
  by simp_all

lemma minus_infinity_smaller: "extended_valof minus_infinity \<le> y"
  unfolding extended_valof_def 
  apply simp_all
  using pinfinity_unfold ninfinity_unfold by force

lemma extended_valof_not_infinity: 
  assumes "\<not>is_nan x"
    and "extended_valof x \<noteq> PInfty"
and "extended_valof x \<noteq> MInfty"
shows "\<not>is_infinity x"
  using assms unfolding extended_valof_def
  by (meson is_infinity_cases)

lemma not_infinite: "\<not> x=plus_infinity \<and> \<not>x=minus_infinity \<Longrightarrow> \<not>is_infinity x"
  using is_infinity_cases by blast

lemma extended_valof_minus[simp]: "extended_valof (-a) = - extended_valof a" 
  apply (cases "a\<noteq>plus_infinity")
  apply (cases "a\<noteq>minus_infinity")
  apply (simp_all add:pinfty_eq_plus_inifity minfty_eq_minus_inifity split del: if_split)
  by (simp add:extended_valof_finite not_infinite)

lemma threshold_finite:
  assumes "\<bar>valof (c::('e, 'f) float)\<bar> < threshold TYPE(('e, 'f)float)"
  shows "is_finite c"
  using assms unfolding is_finite_def is_normal_def is_denormal_def is_zero_def threshold_def emax_def 
  apply(cases "exponent c=0")
   apply (simp_all add: abs_valof_eq2 bias_def)
   apply (auto)
  subgoal proof -
    assume a: "(2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c)) /
    ((2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) - Suc (0::nat)) * (2::real) ^ LENGTH('f))
    < (2::real) ^ (unat (- (1::'e word)) - Suc (0::nat)) *
      ((2::real) - (1::real) / ((2::real) * (2::real) ^ LENGTH('f))) /
      (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) - Suc (0::nat))"
    have  b: "(2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c)) /
    ((2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) - Suc (0::nat)) * (2::real) ^ LENGTH('f)) = (2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c)) / (2::real) ^ LENGTH('f) /
    (2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) - Suc (0::nat)) " by simp
    have "(2::real) ^ ((2::nat) ^ (LENGTH('e) - Suc (0::nat)) - Suc (0::nat)) > 0" by  auto
    with a b divide_less_cancel have "(2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c)) / (2::real) ^ LENGTH('f)
    < (2::real) ^ (unat (- (1::'e word)) - Suc (0::nat)) *
      ((2::real) - (1::real) / ((2::real) * (2::real) ^ LENGTH('f)))" by metis
    then have "(2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c)) / (2::real) ^ LENGTH('f)
    < (2::real) ^ (unat (- (1::'e word)) - Suc (0::nat)) *
      ((2::real) - (1::real) / (2::real) / (2::real) ^ LENGTH('f))" by argo
    then have "(2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c)) / (2::real) ^ LENGTH('f)
    < (2::real) ^ (unat (- (1::'e word)) - Suc (0::nat)) *
      ((2::real)* (2::real) ^ LENGTH('f)/ (2::real) ^ LENGTH('f) - (1::real) / (2::real)/ (2::real) ^ LENGTH('f))" by fastforce
    then have c: "(2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c)) / (2::real) ^ LENGTH('f)
    < (2::real) ^ (unat (- (1::'e word)) - Suc (0::nat)) *
      ((2::real)* (2::real) ^ LENGTH('f) - (1::real) / (2::real))/ (2::real) ^ LENGTH('f)" by argo
    have "(2::real) ^ LENGTH('f) > 0" by fastforce
    with divide_less_cancel c have c_smaller: "(2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c))
    < (2::real) ^ (unat (- (1::'e word)) - Suc (0::nat)) *
      ((2::real)*(2::real) ^ LENGTH('f) - (1::real) / (2::real))" by blast

    have min_one_word: "unat (- (1::'e word)) \<ge> 1"
      by (meson less_one linorder_le_less_linear max_word_not_0 unsigned_eq_0_iff)
    have e_part: "(2::real) ^ IEEE.exponent c > 0" by fastforce
    have less_tmp: "IEEE.exponent c \<ge> unat (- (1::'e word)) \<Longrightarrow> (2::real) ^ IEEE.exponent c * (2::real) ^ LENGTH('f)
    \<ge> (2::real) ^ (unat (- (1::'e word))) * (2::real) ^ LENGTH('f)" by simp
    with e_part have "(2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c)) \<ge> (2::real) ^ IEEE.exponent c * (2::real) ^ LENGTH('f)" by simp
    with e_part less_tmp have "IEEE.exponent c \<ge> unat (- (1::'e word)) \<Longrightarrow> (2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c))
    \<ge> (2::real) ^ (unat (- (1::'e word))) * (2::real) ^ LENGTH('f)"
      by linarith
    with min_one_word have less_tmp2: "IEEE.exponent c \<ge> unat (- (1::'e word)) \<Longrightarrow> (2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c))
    \<ge> (2::real) ^ (unat (- (1::'e word)) - Suc(0::nat)) * (2::real) * (2::real) ^ LENGTH('f)" apply auto
      by (metis (no_types, opaque_lifting) diff_Suc_1 diff_Suc_eq_diff_pred diff_le_self minus_nat.diff_0 not0_implies_Suc not_less_eq_eq power_Suc2)
    
    have "(2::real) ^ (unat (- (1::'e word)) - Suc(0::nat)) * (2::real)*(2::real) ^ LENGTH('f)
    \<ge> (2::real) ^ (unat (- (1::'e word)) - Suc(0::nat)) * ((2::real)*(2::real) ^ LENGTH('f) - (1::real) / (2::real))" by auto
    with less_tmp2 have "IEEE.exponent c \<ge> unat (- (1::'e word)) \<Longrightarrow> (2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c))
    \<ge> (2::real) ^ (unat (- (1::'e word)) - Suc(0::nat)) * ((2::real)*(2::real) ^ LENGTH('f) - (1::real) / (2::real))" by argo

    with c_smaller have "IEEE.exponent c \<ge> unat (- (1::'e word)) \<Longrightarrow> False" by argo
    with a show ?thesis by fastforce
  qed
  done
    
(*lemmas for zerosign*)
lemma valof_zerosign: "valof (zerosign s f) = valof f"
  unfolding zerosign_def by (auto simp: val_zero)

lemma extended_valof_zerosign: "extended_valof (zerosign s f) = extended_valof f"
  unfolding zerosign_def extended_valof_def 
  by (smt (verit) float_zero1 float_zero2 infinite_infinity(2) is_finite_def val_zero)

lemma is_nan_zerosign[simp]: "is_nan (zerosign s a) \<longleftrightarrow> is_nan a"
  by (metis float_distinct_finite(1) is_finite_def is_finite_zerosign zerosign_def)
(*declare [[show_types]]
lemma sign_of_zerosign: "is_zero a \<Longrightarrow> sign (zerosign s a) = s"
  apply(simp add:zerosign_def float_defs(22) float_defs(23)) find_theorems "(0::('e,'f) float)" try0*)

(*lemmas about zero*)
lemma zero_val_exponent: "valof (x::('e, 'f) float) = 0 \<Longrightarrow> exponent x = 0" 
proof -
  assume asm: "valof x = 0"
  from valof_def have rewrite: "IEEE.exponent x \<noteq> 0 \<Longrightarrow> valof x = (- 1::real) ^ (sign x) * (2 ^ (exponent x) / 2 ^ bias TYPE(('e, 'f) float)) * (1 + real (fraction x) / 2 ^ LENGTH('f))" 
    by (simp add: valof_eq)
  have a: "(- 1::real) ^ (sign x) \<noteq> 0" by simp
  have b: "(2 ^ (exponent x) / 2 ^ bias TYPE(('e, 'f) float)) \<noteq> (0::real)" by fastforce
  have c: "(1 + real (fraction x) / 2 ^ LENGTH('f)) \<noteq> (0::real)"
    by (metis add_less_same_cancel1 add_less_same_cancel2 divide_less_0_iff not_one_less_zero of_nat_less_0_iff one_add_one zero_less_divide_iff zero_less_one zero_less_power zero_less_two)
  from a b c rewrite have "IEEE.exponent x \<noteq> 0 \<Longrightarrow> valof x \<noteq> 0" by force
  with asm have "exponent x \<noteq> 0 \<Longrightarrow> False" by blast
  then have "valof x = 0 \<Longrightarrow> exponent x = 0" by blast
  with asm show ?thesis by blast
qed

lemma zero_val: "valof x = 0 \<longrightarrow> is_zero x"
  unfolding is_zero_def
  using zero_val_exponent valof_def 
  by (smt (verit) divide_eq_0_iff divisors_zero of_nat_eq_0_iff power_eq_0_iff valof_eq) 

lemma zero_eq_zero: "is_zero x \<longleftrightarrow> valof x = 0"
  using val_zero zero_val by blast

lemma finite_zero: "is_finite 0"
  by (simp add: is_finite_def)

lemma valof_zero_eq_evalof_zero: "extended_valof x = 0 \<longleftrightarrow> valof x = 0"
  unfolding extended_valof_def
  using finite_zero float_cases
  using float_distinct(7) infinity_is_infinity zero_eq_zero by auto

lemma not_is_nan_zero: "\<not>is_nan 0"
  using float_distinct(4) float_zero1 by blast 

lemma minus_infinity_not_zero[simp]: "minus_infinity \<noteq> 0"
  by (metis float_neg_sign infinity_simps(1) zero_simps(1))

lemma plus_infinity_not_zero[simp]: "plus_infinity \<noteq> 0"
  using finite_zero infinite_infinity(1) by metis

lemma extended_valof_zero: "extended_valof 0 = 0" 
  unfolding extended_valof_def 
  by auto

lemma extended_valof_neg_zero: "extended_valof (-0) = 0" 
  unfolding extended_valof_def 
  apply auto
  apply (metis finite_zero infinite_infinity(2) is_finite_uminus)
  by (metis finite_zero infinite_infinity(2) is_finite_uminus)

lemma zero_l_threshold:
  shows "0 < threshold TYPE(('e, 'f)float)"
proof - 
  have "1 < (2::real) * 2 ^ Suc LENGTH('f)"
    by (metis mult.commute one_less_numeral_iff power_Suc2 power_gt1 semiring_norm(76))
  then have "0 < ((2::real) - 1 / 2 ^ Suc LENGTH('f))"
    by (simp add: mult_imp_div_pos_less)
  moreover have "0<(2::real) ^ bias TYPE(('e, 'f)float)" by simp
  ultimately have "0 <  (2::real) ^ bias TYPE(('e, 'f)float) * (2 - 1 / 2 ^ Suc LENGTH('f))" by simp
  moreover have "0 < (2::real) ^ (emax TYPE(('e, 'f)float) - 1)" by force
  ultimately show ?thesis apply(simp add:threshold_def)
    by (simp add: zero_less_mult_iff)
qed


lemma valof_round_nearest_zero: "valof ((round To_nearest 0)::('e, 'f) float) = 0"
proof -
  from zero_l_threshold have "\<bar>0\<bar> < threshold TYPE(('e, 'f)float)" by fastforce
  then have "((round To_nearest 0)::('e, 'f) float) = closest valof (\<lambda>a::('e, 'f) IEEE.float. even (fraction a)) (Collect is_finite) 0" by fastforce
  with closest_is_closest is_finite_nonempty have "is_closest (valof) (Collect is_finite) 0 ((round To_nearest 0)::('e, 'f) float)" by metis
  with is_closest_def have "(\<forall>b::('e, 'f) float. b \<in> (Collect is_finite) \<longrightarrow> \<bar>valof ((round To_nearest 0)::('e, 'f) float) - 0\<bar> \<le> \<bar>valof b - 0\<bar>)" by metis
  moreover from finite_zero have "is_finite (0::('e, 'f) float)" by auto
  moreover from zero_eq_zero have "\<bar>valof (0::('e, 'f) float) - 0\<bar> = 0" by fastforce
  ultimately have "\<bar>valof ((round To_nearest 0)::('e, 'f) float) - 0\<bar> \<le> 0"
    by (metis mem_Collect_eq)
  then show ?thesis by linarith
qed

(*lemmas about the sign bit*)
lemma sign_pos: "sign x > 0 \<equiv> sign x = 1"
  by (smt (verit) less_nat_zero_code less_one sign_cases)

lemma sign_pos_ereal: "sign (x::('e, 'f) float) = 0 \<longrightarrow> extended_valof x \<ge> 0"
  unfolding extended_valof_def
  proof (cases "is_infinity x")
    case True
    then have "is_infinity x \<Longrightarrow> sign x = 0 \<longrightarrow> x = (plus_infinity::('e, 'f) float)"
      by (simp add: pinfinity_unfold)
    then show "is_infinity x \<Longrightarrow> sign x = 0 \<longrightarrow> 0 \<le> (if x = plus_infinity then PInfty else if x = minus_infinity then MInfty else ereal (valof x))" by simp
  next
    case False
    then show "\<not> is_infinity x \<Longrightarrow> sign x = 0 \<longrightarrow> 0 \<le> (if x = plus_infinity then PInfty else if x = minus_infinity then MInfty else ereal (valof x))"
      by (simp add: ninfinity_unfold valof_nonneg)
  qed

lemma sign_neg_ereal: "sign (x::('e, 'f) float) = 1 \<longrightarrow> extended_valof x \<le> 0"
  unfolding extended_valof_def
  proof (cases "is_infinity x")
    case True
    then have "is_infinity x \<Longrightarrow> sign x = 1 \<longrightarrow> x = (minus_infinity::('e, 'f) float)"
      by (simp add: ninfinity_unfold)
    then show "is_infinity x \<Longrightarrow> sign x = 1 \<longrightarrow> (if x = plus_infinity then PInfty else if x = minus_infinity then MInfty else ereal (valof x)) \<le> 0" 
      by (simp add: infinity_simps(1))
  next
    case False
    then show "\<not> is_infinity x \<Longrightarrow> sign x = 1 \<longrightarrow> (if x = plus_infinity then PInfty else if x = minus_infinity then MInfty else ereal (valof x)) \<le> 0"
      by (simp add: pinfinity_unfold valof_nonpos)
  qed

lemma valof_nonpos_zero: "\<not>is_zero x \<longrightarrow> sign (x::('e, 'f) float) = 1 \<longrightarrow> valof x < 0"
  by (meson order_le_less valof_nonpos zero_val)

lemma valof_nonneg_zero: "\<not>is_zero x \<longrightarrow> sign (x::('e, 'f) float) = 0 \<longrightarrow> valof x > 0"
  by (metis nless_le valof_nonneg zero_val)

lemma nonneg_valof: "valof (x::('e, 'f) float) > 0 \<longrightarrow> sign x = 0"
proof -
  from valof_nonpos have "valof (x::('e, 'f) float) > 0 \<longrightarrow> sign x \<noteq> 1"
    by force
  with sign_cases show ?thesis by metis
qed

lemma nonpos_valof: "valof (x::('e, 'f) float) < 0 \<longrightarrow> sign x = 1"
proof -
  from valof_nonneg have "valof (x::('e, 'f) float) < 0 \<longrightarrow> sign x \<noteq> 0"
    by force
  with sign_cases show ?thesis by metis
qed

lemmas valof_signs=
  sign_pos_ereal
  sign_neg_ereal
  valof_nonpos_zero
  valof_nonneg_zero
  nonneg_valof
  nonpos_valof

lemma sign_valof_diff: "sign a \<noteq> sign b \<Longrightarrow> \<bar>valof a - valof b\<bar> = \<bar>valof a\<bar> + \<bar>valof b\<bar>"
  apply(cases "sign a = 0")
  apply(simp_all add: sign_cases valof_nonpos valof_nonneg)
  using sign_cases
  apply (smt (verit, del_insts) nat_less_le nonneg_valof nonpos_valof)
  using sign_cases
  by (smt (verit, best) nonneg_valof nonpos_valof)

(*lemmas about ereal operations*)
lemma mul_infinity:
  assumes
      nnana: "\<not>is_nan a" and nnanb: "\<not>is_nan b" and 
      illegal_cases1: "\<not>(is_infinity a \<and> is_zero b)" and illegal_cases2: " \<not>(is_zero a \<and> is_infinity b)" 
  shows "is_infinity a \<or> is_infinity b \<Longrightarrow> extended_valof a * extended_valof b = (if sign a = sign b then PInfty else MInfty)"
  apply (cases "is_infinity a")
  subgoal
    apply(cases "sign a = 0")
    unfolding extended_valof_def
    apply(simp_all add: ninfinity_unfold pinfinity_unfold valof_nonneg_zero del: round.simps split del: if_split)
    using assms pinfinity_unfold times_ereal.simps ninfinity_unfold valof_nonneg_zero valof_nonpos_zero
    apply (smt (verit, ccfv_threshold) Infty_neq_0(1) MInfty_eq_minfinity diff_0 ereal_eq_0(2) ereal_less(1) ereal_less(2) ereal_less(5) ereal_less(6) ereal_mult_m1 infinity_ereal_def less_eq_ereal_def less_ereal.simps(3) sign_cases uminus_ereal.simps(2) valof_nonpos verit_comp_simplify1(1) verit_comp_simplify1(3) zero_eq_zero)
    using assms pinfinity_unfold times_ereal.simps ninfinity_unfold valof_nonneg_zero valof_nonpos_zero
    by (smt (verit, ccfv_threshold) MInfty_eq_minfinity One_nat_def float_neg_sign1 infinity_ereal_def less_numeral_extra(3))
  subgoal
    apply(cases "sign a = 0")
    unfolding extended_valof_def
    apply(simp_all add: ninfinity_unfold pinfinity_unfold valof_nonneg_zero del: round.simps split del: if_split)
    subgoal using assms pinfinity_unfold times_ereal.simps ninfinity_unfold valof_nonneg_zero valof_nonpos_zero
      by (smt (verit) MInfty_eq_minfinity infinity_ereal_def not_infinite zero_eq_zero)
    using assms pinfinity_unfold times_ereal.simps ninfinity_unfold valof_nonneg_zero valof_nonpos_zero
    by (smt (verit) MInfty_eq_minfinity infinity_ereal_def sign_cases)
  done

lemma extended_valof_multiply_positive:
  assumes nnana: "\<not>is_nan a" and nnanb: "\<not>is_nan b"
  shows"extended_valof a * extended_valof b > 0 \<longrightarrow> sign a = sign b"
  thm times_ereal.simps
proof -
  from nnana float_cases_finite is_infinity_cases have a_cases: "a = plus_infinity \<or> a = minus_infinity \<or> is_finite a" by blast
  from nnanb float_cases_finite is_infinity_cases have b_cases: "b = plus_infinity \<or> b = minus_infinity \<or> is_finite b" by blast
  consider "a = plus_infinity \<and> b=plus_infinity" | "a = plus_infinity \<and> b=minus_infinity" | "a = plus_infinity \<and> is_finite b" |  
           "a = minus_infinity \<and> b=plus_infinity" | "a = minus_infinity \<and> b=minus_infinity" | "a = minus_infinity \<and> is_finite b" | 
           "is_finite a \<and> b=plus_infinity" | "is_finite a \<and> b=minus_infinity" | "is_finite a \<and> is_finite b" 
    using a_cases b_cases by argo
  then show ?thesis proof cases
    case 1
    with pinfinity_unfold show ?thesis by metis
  next
    case 2
    with pinfinity_unfold ninfinity_unfold extended_valof_def times_ereal.simps show ?thesis
      by (metis MInfty_eq_minfinity infinity_ereal_def less_eq_ereal_def not_MInfty_nonneg)
  next
    case 3
    with pinfinity_unfold extended_valof_def times_ereal.simps valof_signs(1) valof_signs(2) show ?thesis
      by (metis ereal_zero_less_0_iff less_eq_ereal_def order_antisym_conv order_less_irrefl sign_cases)
  next
    case 4
    with pinfinity_unfold ninfinity_unfold extended_valof_def times_ereal.simps show ?thesis
      by (metis MInfty_eq_minfinity infinity_ereal_def less_eq_ereal_def not_MInfty_nonneg)
  next
    case 5
    with ninfinity_unfold show ?thesis by metis
  next
    case 6
    with pinfinity_unfold extended_valof_def times_ereal.simps valof_signs(1) valof_signs(2) show ?thesis
      by (metis ereal_zero_less_0_iff less_eq_ereal_def order_antisym_conv order_less_irrefl sign_cases)
  next
    case 7
    with pinfinity_unfold extended_valof_def times_ereal.simps valof_signs(1) valof_signs(2) show ?thesis
      by (metis ereal_zero_less_0_iff less_eq_ereal_def order_antisym_conv order_less_irrefl sign_cases)
  next
    case 8
    with pinfinity_unfold extended_valof_def times_ereal.simps valof_signs(1) valof_signs(2) show ?thesis
      by (metis ereal_zero_less_0_iff less_eq_ereal_def order_antisym_conv order_less_irrefl sign_cases)
  next
    case 9
    with times_ereal.simps valof_signs(1) valof_signs(2) show ?thesis
      by (metis ereal_zero_less_0_iff less_eq_ereal_def order_antisym_conv order_less_irrefl sign_cases)
  qed
qed

lemma extended_valof_multiply_negative:
  assumes nnana: "\<not>is_nan a" and nnanb: "\<not>is_nan b"
  shows "extended_valof a * extended_valof b < 0 \<longrightarrow> sign a \<noteq> sign b"
  thm times_ereal.simps
proof -
  from nnana float_cases_finite is_infinity_cases have a_cases: "a = plus_infinity \<or> a = minus_infinity \<or> is_finite a" by blast
  from nnanb float_cases_finite is_infinity_cases have b_cases: "b = plus_infinity \<or> b = minus_infinity \<or> is_finite b" by blast
  consider "a = plus_infinity \<and> b=plus_infinity" | "a = plus_infinity \<and> b=minus_infinity" | "a = plus_infinity \<and> is_finite b" |  
           "a = minus_infinity \<and> b=plus_infinity" | "a = minus_infinity \<and> b=minus_infinity" | "a = minus_infinity \<and> is_finite b" | 
           "is_finite a \<and> b=plus_infinity" | "is_finite a \<and> b=minus_infinity" | "is_finite a \<and> is_finite b" 
    using a_cases b_cases by argo
  then show ?thesis proof cases
    case 1
    with extended_valof_def times_ereal.simps show ?thesis
      by (metis MInfty_eq_minfinity ereal.distinct(5) ereal_mult_eq_MInfty infinity_ereal_def)
  next
    case 2
    with pinfinity_unfold ninfinity_unfold show ?thesis by force
  next
    case 3
    with pinfinity_unfold extended_valof_def times_ereal.simps show ?thesis
      by (metis ereal_mult_less_0_iff sign_pos_ereal verit_comp_simplify1(3))
  next
    case 4
    with pinfinity_unfold ninfinity_unfold show ?thesis by force
  next
    case 5
    with pinfinity_unfold ninfinity_unfold extended_valof_def times_ereal.simps show ?thesis
      by (metis MInfty_eq_minfinity ereal.distinct(5) ereal_mult_eq_MInfty infinity_ereal_def)
  next
    case 6
    with ninfinity_unfold times_ereal.simps show ?thesis
      by (metis ereal_mult_less_0_iff sign_neg_ereal verit_comp_simplify1(3))
  next
    case 7
    with pinfinity_unfold extended_valof_def times_ereal.simps show ?thesis
      by (metis ereal_mult_less_0_iff sign_pos_ereal verit_comp_simplify1(3))
  next
    case 8
    with ninfinity_unfold times_ereal.simps show ?thesis
      by (metis ereal_mult_less_0_iff sign_neg_ereal verit_comp_simplify1(3))
  next
    case 9
    with times_ereal.simps show ?thesis
      by (metis ereal_mult_less_0_iff sign_cases sign_neg_ereal sign_pos_ereal verit_comp_simplify1(3))
  qed
qed
end