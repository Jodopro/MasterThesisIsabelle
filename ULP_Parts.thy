theory ULP_Parts
imports "IEEE_Floating_Point.Conversion_IEEE_Float" "HOL-Library.Extended_Real" "HOL-Library.Extended_Real" IEEE_Properties_Float_Operations
begin

lemma zero_lp_sign:
  shows "sign (zero_lp c) = 0"
  apply(simp add: zero_lp.rep_eq sign_def)
  by (metis (no_types, lifting) case_prod_conv surj_pair unsigned_0)

lemma zero_lp_exponent:
  shows "exponent (zero_lp c) = exponent c"
  apply(simp add: zero_lp.rep_eq exponent_def)
  by (smt (verit, best) case_prod_conv prod_cases3)

lemma zero_lp_fraction:
  shows "fraction (zero_lp c) = 0"
  apply(simp add: zero_lp.rep_eq fraction_def)
  by (metis (no_types, lifting) case_prod_conv surj_pair unsigned_0)

lemma one_lp_sign:
  shows "sign (one_lp c) = 0"
  apply(simp add: one_lp.rep_eq sign_def)
  by (metis (no_types, lifting) case_prod_conv surj_pair unsigned_0)

lemma one_lp_exponent:
  shows "exponent (one_lp c) = exponent c"
  apply(simp add: one_lp.rep_eq exponent_def)
  by (smt (verit, best) case_prod_conv prod_cases3)

lemma one_lp_fraction:
  shows "fraction (one_lp c) = 1"
  apply(simp add: one_lp.rep_eq fraction_def)
  by (metis (mono_tags, lifting) case_prod_conv surj_pair unat_eq_1)

lemmas one_lp_parts=
  one_lp_sign
  one_lp_fraction
  one_lp_exponent

lemmas zero_lp_parts=
  zero_lp_sign
  zero_lp_fraction
  zero_lp_exponent

lift_definition ulp_increase::"('e ,'f) float \<Rightarrow> ('e ,'f) float" is "\<lambda>(s, e, f). 
  if f+1\<noteq>0 then (s, e::'e word, f+1) else (s, e+1::'e word, f+1)" .
lift_definition ulp_decrease::"('e ,'f) float \<Rightarrow> ('e ,'f) float" is "\<lambda>(s, e, f). 
  if f\<noteq>0 then (s, e::'e word, f-1) else (s, e-1::'e word, f-1)" .

lift_definition last_frac::"('e ,'f) float \<Rightarrow> ('e ,'f) float" is "\<lambda>(s, e, f). 
  (s, e, -1)" .

lemma ulp_increase_sign:
  shows "sign (ulp_increase x) = sign x"
  unfolding ulp_increase_def
  by(auto simp: ulp_increase.rep_eq sign_def fraction_def Abs_float_inverse split: prod.splits)

lemma word_minus_1:
  shows "x+1 = 0 \<longleftrightarrow> unat (x::'f::len word) = 2^LENGTH('f) - 1"
  apply auto
  apply (metis add_diff_cancel_right' add_eq_0_iff_both_eq_0 len_not_eq_0 less_numeral_extra(3) linorder_neqE_nat numeral_1_eq_Suc_0 numeral_One p2_eq_1 unat_1 unat_plus_if' unsigned_eq_0_iff word_exp_length_eq_0 zero_less_diff)
  by (metis Suc_pred nat_less_le pos2 unatSuc2 unat_1 unat_add_lem word_overflow_unat zero_less_power)

lemma ulp_increase_exp_helper:
  assumes "is_finite (x::('e, 'f) float)"
  shows "\<forall>x1 a b. Rep_float x = (x1, a, b) \<longrightarrow> unat (a + 1) = Suc (unat a)"
proof -
  have "\<forall>x1 a b. Rep_float x = (x1, a, b) \<longrightarrow> exponent x = unat a" by(simp add:exponent_def)
  with assms have "\<forall>x1 a b. Rep_float x = (x1, a, b) \<longrightarrow> unat a < unat (- 1::'e word)" unfolding is_finite_def is_normal_def is_zero_def is_denormal_def emax_def by auto
  then show ?thesis using unat_Suc2 by force
qed

lemma ulp_increase_exp1:
  assumes "fraction (x::('e, 'f) float) \<noteq> 2^LENGTH('f) - 1"
  shows "exponent (ulp_increase x) = exponent x"
  unfolding ulp_increase_def
  using assms apply(simp add: ulp_increase.rep_eq assms Abs_float_inverse exponent_def split: prod.splits)
  using assms by (auto simp add:word_minus_1 fraction_def split: prod.splits)

lemma ulp_increase_exp2:
  assumes "fraction (x::('e, 'f) float) = 2^LENGTH('f) - 1"
  shows "is_finite x \<Longrightarrow> exponent (ulp_increase x) = 1+exponent x"
  unfolding ulp_increase_def
  using assms apply (simp add: ulp_increase.rep_eq assms Abs_float_inverse exponent_def ulp_increase_exp_helper split: prod.splits)
  using assms by (auto simp add:word_minus_1 fraction_def split: prod.splits)

lemmas ulp_increase_exp=
  ulp_increase_exp1
  ulp_increase_exp2

lemma ulp_increase_frac_helper: "unat (ba::'f::len word) \<noteq> 2 ^ LENGTH('f) - Suc 0 \<Longrightarrow> unat (ba + 1) = Suc (unat ba)"
proof -
  from word_minus_1 have "unat (ba::'f::len word) \<noteq> 2 ^ LENGTH('f) - Suc 0 \<Longrightarrow> ba+1 \<noteq> 0" by auto
  then have a: "unat (ba::'f::len word) \<noteq> 2 ^ LENGTH('f) - Suc 0 \<Longrightarrow> unat ba < unat (- 1::'f word)"
    by (metis diff_minus_eq_add eq_iff_diff_eq_0 word_less_nat_alt word_order.not_eq_extremum)
  from unat_Suc2 have b: "unat ba < unat (- 1::'f word) \<Longrightarrow> unat (ba + 1) = Suc (unat ba)" by force
  from a b show "unat (ba::'f::len word) \<noteq> 2 ^ LENGTH('f) - Suc 0 \<Longrightarrow> unat (ba + 1) = Suc (unat ba)" by blast
qed

lemma ulp_increase_frac1:
  assumes "fraction (x::('e, 'f) float) \<noteq> 2^LENGTH('f) - 1"
  shows "fraction (ulp_increase x) = 1 + fraction x"
  unfolding ulp_increase_def
  using assms apply(simp add: ulp_increase.rep_eq assms Abs_float_inverse fraction_def split: prod.splits)
  using assms word_minus_1 by (auto simp add:word_minus_1 fraction_def ulp_increase_frac_helper split: prod.splits)

lemma ulp_increase_frac2:
  assumes "fraction (x::('e, 'f) float) = 2^LENGTH('f) - 1"
  shows "fraction (ulp_increase x) = 0"
  unfolding ulp_increase_def
  using assms apply (simp add: ulp_increase.rep_eq assms Abs_float_inverse fraction_def ulp_increase_exp_helper split: prod.splits)
  using assms by (auto simp add:word_minus_1 fraction_def split: prod.splits)

lemmas ulp_increase_frac=
  ulp_increase_frac1
  ulp_increase_frac2

lemma ulp_decrease_sign:
  shows "sign (ulp_decrease x) = sign x"
  unfolding ulp_decrease_def
  by(auto simp: ulp_decrease.rep_eq sign_def fraction_def Abs_float_inverse split: prod.splits)

lemma ulp_decrease_exp1:
  assumes "fraction (x::('e, 'f) float) \<noteq> 0"
  shows "exponent (ulp_decrease x) = exponent x"
  unfolding ulp_decrease_def
  using assms apply(simp add: ulp_decrease.rep_eq assms Abs_float_inverse exponent_def split: prod.splits)
  using assms by (auto simp add:word_minus_1 fraction_def split: prod.splits)

lemma ulp_decrease_frac_helper: "unat (ba::'f::len word) = 0 \<Longrightarrow> unat (ba-1) = 2^LENGTH('f) - 1"
  apply auto
  by (simp add: unat_eq_zero unat_minus_one_word)

lemma ulp_decrease_exp_helper:
  "\<not>is_finite (Abs_float (x1, - 1, x2)::('e, 'f) float)"
proof-
  have a: "exponent (Abs_float (x1, - 1, x2)::('e, 'f) float) = unat (-1::'e word)" by (simp add:exponent_def Abs_float_inverse split: prod.splits)
  have b: "exponent (Abs_float (x1, - 1, x2)::('e, 'f) float) = emax TYPE(('e, 'f)float) \<longrightarrow> \<not>is_finite (Abs_float (x1, - 1, x2)::('e, 'f) float)" by (simp add:is_finite_def is_normal_def is_denormal_def is_zero_def)
  have c: "emax TYPE(('e, 'f)float) = unat (-1::'e word)" by(simp add:emax_def) 
  from a b c show ?thesis by presburger
qed

lemma ulp_decrease_exp2:
  assumes "fraction (x::('e, 'f) float) = 0"
  shows "is_finite (ulp_decrease x) \<Longrightarrow> exponent (ulp_decrease x) = exponent x-1"
  unfolding ulp_decrease_def
  apply(cases "exponent x = 0")
  using assms apply (simp_all add: ulp_decrease.rep_eq assms Abs_float_inverse exponent_def split: prod.splits)
  using assms apply (auto simp add:word_minus_1 fraction_def unat_eq_zero ulp_decrease_exp_helper split: prod.splits)
  by (metis One_nat_def less_numeral_extra(3) unat_0 unat_minus_one)

lemmas ulp_decrease_exp=
  ulp_decrease_exp1
  ulp_decrease_exp2

lemma ulp_decrease_frac1:
  assumes "fraction (x::('e, 'f) float) \<noteq> 0"
  shows "fraction (ulp_decrease x) = fraction x - 1"
  unfolding ulp_decrease_def
  using assms apply(simp add: ulp_decrease.rep_eq assms Abs_float_inverse fraction_def split: prod.splits)
  using assms word_minus_1 apply (auto simp add:word_minus_1 fraction_def ulp_decrease_frac_helper split: prod.splits)
  by (simp add: unat_minus_one)

lemma ulp_decrease_frac2:
  assumes "fraction (x::('e, 'f) float) = 0"
  shows "fraction (ulp_decrease x) = 2^LENGTH('f) - 1"
  unfolding ulp_decrease_def
  using assms apply (simp add: ulp_decrease.rep_eq assms Abs_float_inverse fraction_def ulp_decrease_frac_helper split: prod.splits)
  using assms by (auto simp add:word_minus_1 fraction_def unsigned_eq_0_iff unat_minus_one_word split: prod.splits)

lemmas ulp_decrease_frac=
  ulp_decrease_frac1
  ulp_decrease_frac2

lemma helper_div_g0:
  "((2::real) ^ x * 2 ^ y) > 0" by simp 

lemma ulp_divisor_rewrite:
  shows "((2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) - Suc (0::nat)) * (2::real) ^ (f::nat)) = (2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) - Suc (0::nat) + f)"
  by (metis power_add)

lemma ulp_divisor_rewrite':
  shows "((2::real) ^ (f::nat) * (2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) - Suc (0::nat))) = (2::real) ^ ((2::nat) ^ (e - Suc (0::nat)) - Suc (0::nat) + f)"
  using ulp_divisor_rewrite
  by (simp add: mult.commute)

declare [[show_types]]
lemma exp_l_abs_valof_l:
  assumes "exponent (a::('e, 'f) float) < exponent (b::('e, 'f) float)"
  shows "\<bar>valof a\<bar> < \<bar>valof b\<bar>"
  using assms apply(simp add:abs_valof_eq2)
  apply(cases "exponent a = 0")
   apply(simp_all add:divide_less_cancel )
   apply(simp_all add:bias_def ulp_divisor_rewrite)
  subgoal 
  proof -
    from float_frac_le have "real (fraction a) \<le> (2::nat) ^ LENGTH('f) - 1" by auto
    with div_eq_0_iff have "real (fraction a) < (2::nat) ^ LENGTH('f)"
      by fastforce
    then have 1: "(2::real) * real (fraction a) < (2::real) * (2::nat) ^ LENGTH('f)" by linarith
    have "(1::nat) \<le> IEEE.exponent b \<Longrightarrow> (2::real) \<le> (2::real) ^ IEEE.exponent b "
      by (metis exp_less power_one_right)
    then have "(0::nat) < IEEE.exponent b \<Longrightarrow> (2::real) \<le> (2::real) ^ IEEE.exponent b " by auto
    then have 2: "(0::nat) < IEEE.exponent b \<Longrightarrow> (2::real) * ((2::real) ^ LENGTH('f)) \<le> (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f))"
      by auto
    have "(0::nat) < IEEE.exponent b \<Longrightarrow> (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f)) \<le> (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f) + real (fraction b))"
      by force
    with 2 have 3: "(0::nat) < IEEE.exponent b \<Longrightarrow> (2::real) * ((2::real) ^ LENGTH('f)) \<le> (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f) + real (fraction b))" by linarith
    with 1 show "(0::nat) < IEEE.exponent b \<Longrightarrow> (2::real) * real (fraction a) < (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f) + real (fraction b))"
      by (smt (verit, best) nat_1_add_1 of_nat_1 of_nat_add semiring_1_class.of_nat_power) 
  qed
  subgoal proof -
    have "((2::real) ^ LENGTH('f) + real (fraction a)) \<le> ((2::real) ^ LENGTH('f) + (2::nat) ^ LENGTH('f) - 1)" apply(simp) using float_frac_le
      using real_le_power_numeral_diff by blast
    then have "((2::real) ^ LENGTH('f) + real (fraction a)) < (2::real) * (2::real) ^ LENGTH('f)"
      by (simp add: nat_less_real_le)
    then have "(2::real) ^ IEEE.exponent a * ((2::real) ^ LENGTH('f) + real (fraction a)) < (2::real) ^ IEEE.exponent a * (2::real) * (2::real) ^ LENGTH('f)" by simp
    then have 1: "(2::real) ^ IEEE.exponent a * ((2::real) ^ LENGTH('f) + real (fraction a)) < (2::real) ^ (IEEE.exponent a + 1) * (2::real) ^ LENGTH('f)" by simp
    have 2: "(2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f)) \<le> (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f) + real (fraction b))" by simp
    then have "IEEE.exponent a < IEEE.exponent b \<Longrightarrow> (IEEE.exponent a + 1) \<le> IEEE.exponent b" 
      by linarith
    then have "IEEE.exponent a < IEEE.exponent b \<Longrightarrow> (2::real) ^ (exponent a + 1) \<le> (2::real) ^ exponent b"
      using exp_less by blast
    then have "IEEE.exponent a < IEEE.exponent b \<Longrightarrow> (2::real) ^ (exponent a + 1) * ((2::real) ^ LENGTH('f)) \<le> (2::real) ^ exponent b * ((2::real) ^ LENGTH('f))" by auto
    with 2 have "IEEE.exponent a < IEEE.exponent b \<Longrightarrow> (2::real) ^ (exponent a + 1) * ((2::real) ^ LENGTH('f)) \<le> (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f) + real (fraction b))" by linarith
    with 1 show "IEEE.exponent a < IEEE.exponent b \<Longrightarrow>
    (2::real) ^ IEEE.exponent a * ((2::real) ^ LENGTH('f) + real (fraction a))
    < (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f) + real (fraction b))" by linarith
  qed
  done

lemma exp_e_abs_valof_l:
  assumes "exponent (a::('e, 'f) float) = exponent (b::('e, 'f) float)"
  and "fraction a < fraction b"
  shows "\<bar>valof a\<bar> < \<bar>valof b\<bar>"
  using assms by(simp add:abs_valof_eq2 divide_less_cancel bias_def ulp_divisor_rewrite)

lemma exp_e_abs_valof_e:
  assumes "exponent (a::('e, 'f) float) = exponent (b::('e, 'f) float)"
  and "fraction a = fraction b"
  shows "\<bar>valof a\<bar> = \<bar>valof b\<bar>"
  using assms by(simp add:abs_valof_eq2 divide_less_cancel bias_def ulp_divisor_rewrite)

lemma abs_valof_e_exp_e:
  assumes "\<bar>valof a\<bar> = \<bar>valof b\<bar>"
  shows "exponent (a::('e, 'f) float) = exponent (b::('e, 'f) float)"
  apply(cases "exponent a = 0")
  apply(cases "exponent b = 0")
  using assms apply(simp_all add:abs_valof_eq2 divide_less_cancel bias_def ulp_divisor_rewrite)
  subgoal proof-
    from float_frac_le have step_1: "(2::real) * real (fraction a) \<le> (2::real) * ((2::nat) ^ LENGTH('f) - (1::nat))" by auto
    have "(0::nat) < IEEE.exponent b \<Longrightarrow> (2::real) \<le> (2::real) ^ IEEE.exponent b"
      by (simp add: self_le_power)
    then have "(0::nat) < IEEE.exponent b \<Longrightarrow> (2::real) * ((2::real) ^ LENGTH('f)) \<le> (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f) + real (fraction b)) "
      by (metis (no_types, opaque_lifting) add.commute add_increasing less_eq_real_def mult_mono' of_nat_0_le_iff of_nat_eq_of_nat_power_cancel_iff of_nat_numeral)
    with step_1 show "(0::nat) < IEEE.exponent b \<Longrightarrow>
    (2::real) * real (fraction a) =
    (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f) + real (fraction b)) \<Longrightarrow>
    False" 
      by (simp add: of_nat_diff)
  qed
  apply(cases "exponent b = 0")
  using assms apply(simp_all add:abs_valof_eq2 divide_less_cancel bias_def ulp_divisor_rewrite)
  subgoal proof-
    from float_frac_le have step_1: "(2::real) * real (fraction b) \<le> (2::real) * ((2::nat) ^ LENGTH('f) - (1::nat))" by auto
    have "(0::nat) < IEEE.exponent a \<Longrightarrow> (2::real) \<le> (2::real) ^ IEEE.exponent a"
      by (simp add: self_le_power)
    then have "(0::nat) < IEEE.exponent a \<Longrightarrow> (2::real) * ((2::real) ^ LENGTH('f)) \<le> (2::real) ^ IEEE.exponent a * ((2::real) ^ LENGTH('f) + real (fraction a)) "
      by (metis (no_types, opaque_lifting) add.commute add_increasing less_eq_real_def mult_mono' of_nat_0_le_iff of_nat_eq_of_nat_power_cancel_iff of_nat_numeral)
    moreover have "(2::real) * ((2::nat) ^ LENGTH('f) - (1::nat)) < (2::real) * ((2::real) ^ LENGTH('f))" by auto
    ultimately show "(0::nat) < IEEE.exponent a \<Longrightarrow>
    (2::real) ^ IEEE.exponent a * ((2::real) ^ LENGTH('f) + real (fraction a)) =
    (2::real) * real (fraction b) \<Longrightarrow> False" 
     using step_1 by argo
 qed
  subgoal proof-
    have bigger: "\<forall>(c::('e, 'f) float). (2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c)) \<ge> (2::real) ^ IEEE.exponent c * (2::real) ^ LENGTH('f)" by simp
    have smaller: "\<forall>(c::('e, 'f) float). (2::real) ^ IEEE.exponent c * ((2::real) ^ LENGTH('f) + real (fraction c)) < (2::real) ^ (IEEE.exponent c + 1) * (2::real) ^ LENGTH('f)"
      using float_frac_l real_le_power_numeral_diff by auto
    from bigger have "exponent a < exponent b \<Longrightarrow> (2::real) ^ (exponent b) * (2::real) ^ LENGTH('f) \<le> (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f) + real (fraction b))"
      by presburger
    have "exponent a < exponent b \<Longrightarrow> (2::real) ^ (exponent a + 1) \<le> (2::real) ^ (exponent b)"
      by (metis exp_less nat_less_real_le of_nat_1 of_nat_add of_nat_le_iff)
    then have "exponent a < exponent b \<Longrightarrow> (2::real) ^ (exponent a + 1) * (2::real) ^ LENGTH('f) \<le> (2::real) ^ (exponent b) * (2::real) ^ LENGTH('f)"
      by fastforce
    with bigger smaller have a_bigger: "exponent a < exponent b \<Longrightarrow>
      (2::real) ^ IEEE.exponent a * ((2::real) ^ LENGTH('f) + real (fraction a)) < (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f) + real (fraction b))"
      by (smt (verit))
    have "exponent b < exponent a \<Longrightarrow> (2::real) ^ (exponent b + 1) \<le> (2::real) ^ (exponent a)"
      by (metis exp_less nat_less_real_le of_nat_1 of_nat_add of_nat_le_iff)
    then have "exponent b < exponent a \<Longrightarrow> (2::real) ^ (exponent b + 1) * (2::real) ^ LENGTH('f) \<le> (2::real) ^ (exponent a) * (2::real) ^ LENGTH('f)"
      by fastforce
    with bigger smaller have "exponent b < exponent a \<Longrightarrow>
      (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f) + real (fraction b)) < (2::real) ^ IEEE.exponent a * ((2::real) ^ LENGTH('f) + real (fraction a))"
      by (smt (verit))
    with a_bigger have "exponent a \<noteq> exponent b \<Longrightarrow>
      (2::real) ^ IEEE.exponent a * ((2::real) ^ LENGTH('f) + real (fraction a)) \<noteq> (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f) + real (fraction b))"
      by force
    then show "(2::real) ^ IEEE.exponent a * ((2::real) ^ LENGTH('f) + real (fraction a)) =
    (2::real) ^ IEEE.exponent b * ((2::real) ^ LENGTH('f) + real (fraction b)) \<Longrightarrow>
    (0::nat) < IEEE.exponent b \<Longrightarrow> IEEE.exponent a = IEEE.exponent b" by blast
  qed
  done

lemma g_float_exp_frac:
  assumes "\<bar>valof (a::('e, 'f) float)\<bar> < \<bar>valof (b::('e, 'f) float)\<bar>"
  shows "exponent a < exponent b \<or> (exponent a = exponent b \<and> fraction a < fraction b)"
  apply(cases "exponent a < exponent b")
  using assms apply(simp add:exp_l_abs_valof_l)
  using assms
  subgoal proof-
    from exp_l_abs_valof_l have "IEEE.exponent a > IEEE.exponent b \<longrightarrow> \<bar>valof a\<bar> > \<bar>valof b\<bar>" by blast
    then have 1: "\<not> IEEE.exponent a < IEEE.exponent b \<Longrightarrow> \<bar>valof a\<bar> < \<bar>valof b\<bar> \<Longrightarrow> IEEE.exponent a = IEEE.exponent b" by simp
    from exp_e_abs_valof_l exp_e_abs_valof_e have "IEEE.exponent a = IEEE.exponent b \<Longrightarrow> fraction b \<le> fraction a \<Longrightarrow> \<bar>valof a\<bar> < \<bar>valof b\<bar> \<Longrightarrow> False"
      by (metis order.asym order_le_imp_less_or_eq)
    with 1 show "\<not> IEEE.exponent a < IEEE.exponent b \<Longrightarrow>
    \<bar>valof a\<bar> < \<bar>valof b\<bar> \<Longrightarrow> IEEE.exponent a < IEEE.exponent b \<or> IEEE.exponent a = IEEE.exponent b \<and> fraction a < fraction b"  by fastforce
  qed
  done

lemma g_exp_ulp_bigger:
  assumes "exponent (c::('e, 'f) float) < exponent (x::('e, 'f) float)"
  and "is_finite c"
  shows "\<bar>valof x\<bar> \<ge> \<bar>valof (ulp_increase c)\<bar>"
  apply(cases "fraction (c::('e, 'f) float) = 2^LENGTH('f) - 1")
  subgoal proof -
    from ulp_increase_exp assms have exp_part: "fraction c = (2::nat) ^ LENGTH('f) - (1::nat) \<Longrightarrow> exponent (ulp_increase c) = exponent c + 1" by auto
    from ulp_increase_frac assms have frac_part: "fraction c = (2::nat) ^ LENGTH('f) - (1::nat) \<Longrightarrow> fraction (ulp_increase c) = 0" by auto
    from exp_l_abs_valof_l have exp_smaller: "exponent x > exponent (ulp_increase c) \<Longrightarrow> \<bar>valof x\<bar> \<ge> \<bar>valof (ulp_increase c)\<bar>" by fastforce
    from assms exp_part have "fraction c = (2::nat) ^ LENGTH('f) - (1::nat) \<Longrightarrow> exponent x \<le> exponent (ulp_increase c) \<Longrightarrow> exponent x = exponent c + 1" by fastforce
    with exp_e_abs_valof_l exp_e_abs_valof_e have "fraction c = (2::nat) ^ LENGTH('f) - (1::nat) \<Longrightarrow> exponent x \<le> exponent (ulp_increase c) \<Longrightarrow> \<bar>valof x\<bar> \<ge> \<bar>valof (ulp_increase c)\<bar>" sledgehammer
      by (smt (verit, ccfv_threshold) frac_part bot_nat_0.not_eq_extremum exp_part)
    with exp_smaller show "fraction c = (2::nat) ^ LENGTH('f) - (1::nat) \<Longrightarrow> \<bar>valof (ulp_increase c)\<bar> \<le> \<bar>valof x\<bar>"
      by fastforce 
  qed
  subgoal proof -
    from ulp_increase_exp have "fraction c \<noteq> (2::nat) ^ LENGTH('f) - (1::nat) \<Longrightarrow> exponent (ulp_increase c) = exponent c" by blast
    with assms have "fraction c \<noteq> (2::nat) ^ LENGTH('f) - (1::nat) \<Longrightarrow> exponent (ulp_increase c) < exponent x" by presburger
    with exp_l_abs_valof_l show "fraction c \<noteq> (2::nat) ^ LENGTH('f) - (1::nat) \<Longrightarrow> \<bar>valof (ulp_increase c)\<bar> \<le> \<bar>valof x\<bar>"
      by force
  qed
  done

lemma e_exp_g_frac_ulp_bigger:
  assumes "exponent (c::('e, 'f) float) = exponent (x::('e, 'f) float)"
  and "fraction c < fraction x"
  and "is_finite c"
shows "\<bar>valof x\<bar> \<ge> \<bar>valof (ulp_increase c)\<bar>"
proof -
  from float_frac_le have not_max: "fraction c \<noteq> (2::nat) ^ LENGTH('f) - (1::nat)"
    by (metis assms(2) le_antisym less_or_eq_imp_le nat_neq_iff)
  with ulp_increase_frac assms have frac_part: "fraction (ulp_increase c) \<le> fraction x" by fastforce
  with ulp_increase_exp(1) assms not_max have exp_part: "exponent (ulp_increase c) = exponent x" by metis
  with frac_part exp_e_abs_valof_e exp_e_abs_valof_l show ?thesis by fastforce
qed

lemma g_ulp_increase_ge: 
  assumes "\<bar>valof (x::('e, 'f) float)\<bar> > \<bar>valof (c::('e, 'f) float)\<bar>"
    and "is_finite c"
  shows "\<bar>valof x\<bar> \<ge> \<bar>valof (ulp_increase c)\<bar>"
  using assms g_float_exp_frac e_exp_g_frac_ulp_bigger g_exp_ulp_bigger by blast
  

lemma nothing_between_ulp_increase:
  assumes "sign c = 0"
    and "is_finite c"
  shows "valof (c::('e, 'f) float) \<ge> valof (x::('e, 'f) float) \<or> valof x \<ge> valof (ulp_increase c)"
  apply(cases "valof c \<ge> valof x")
   apply simp
  using g_ulp_increase_ge assms valof_nonneg
  by (smt (verit, ccfv_threshold) dual_order.trans leI linorder_linear)
end