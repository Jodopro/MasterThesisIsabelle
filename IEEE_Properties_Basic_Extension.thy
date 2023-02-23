theory IEEE_Properties_Basic_Extension
imports "IEEE_Floating_Point.Conversion_IEEE_Float" "HOL-Library.Extended_Real"
begin

lemma infinity_is_infinity: "is_infinity (plus_infinity)"
  unfolding is_infinity_def
  unfolding plus_infinity_def
  by (metis infinity_simps(3) infinity_simps(5) plus_infinity_def)

lemma pinfinity_unfold[code_unfold]: "x = plus_infinity \<longleftrightarrow> is_infinity x \<and> sign x = 0"
  by (metis float_neg_sign infinity_is_infinity infinity_simps(1) is_infinity_cases)

lemma ninfinity_unfold[code_unfold]:  "x = minus_infinity \<longleftrightarrow> is_infinity x \<and> sign x = 1"
  by (metis infinity_is_infinity infinity_simps(1) infinity_simps(2) is_infinity_cases is_infinity_uminus zero_neq_one)

definition extended_valof :: "('e, 'f) float \<Rightarrow> ereal"
  where "extended_valof x = (if x = (plus_infinity::('e, 'f) float) 
    then PInfty else (if x = (minus_infinity::('e, 'f) float) 
    then MInfty else ereal (valof x)))"


lemma valof_zerosign: "valof (zerosign s f) = valof f"
  unfolding zerosign_def by (auto simp: val_zero)

lemma extended_valof_zerosign: "extended_valof (zerosign s f) = extended_valof f"
  unfolding zerosign_def extended_valof_def 
  by (smt (verit) float_zero1 float_zero2 infinite_infinity(2) is_finite_def val_zero)

lemma extended_valof_finite: "\<not> is_infinity a \<Longrightarrow> extended_valof a = valof a"
  unfolding extended_valof_def
  using infinity_is_infinity by auto

lemma inf_not_zero: 
    "is_infinity x \<longrightarrow> \<not> is_zero x"
  using float_distinct(7) by auto

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

lemma real_of_word_bigger_zero: "real_of_word x \<ge> 0"
  by linarith

lemma zero_val_helper1: 
  fixes x::"('e, 'f) float" 
  shows"(-1::real)^x1 * ((2^(x2::nat)) / (2^(x3::nat))) * (1 + (real_of_word x4)/2^LENGTH('f)) \<noteq> 0"
proof -
  have a: "(-1::real)^x1 \<noteq> 0" by auto
  have b: "((2^x2) / (2^x3)) \<noteq> (0::real)" by simp
  have "\<forall>y. (real_of_word x4)\<ge>0 \<longrightarrow> y>0 \<longrightarrow> (1 + (real_of_word x4)/y) \<noteq> 0"
    using divide_nonneg_pos by fastforce
  with real_of_word_bigger_zero have c: "(1 + (real_of_word x4)/2^LENGTH('f)) \<noteq> 0" by auto
  from a b c show ?thesis by simp
qed

lemma zero_val_helper2: "valof (x::('e, 'f) float) = 0 \<Longrightarrow> exponent x = 0" 
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
  using zero_val_helper2 valof_def 
  by (smt (verit) divide_eq_0_iff divisors_zero of_nat_eq_0_iff power_eq_0_iff valof_eq) 

lemma zero_eq_zero: "is_zero x \<longleftrightarrow> valof x = 0"
  using val_zero zero_val by blast

lemma valof_nonpos_zero: "\<not>is_zero x \<longrightarrow> sign (x::('e, 'f) float) = 1 \<longrightarrow> valof x < 0"
  by (meson order_le_less valof_nonpos zero_val)

lemma valof_nonneg_zero: "\<not>is_zero x \<longrightarrow> sign (x::('e, 'f) float) = 0 \<longrightarrow> valof x > 0"
  by (metis nless_le valof_nonneg zero_val)

lemma is_nan_zerosign[simp]: "is_nan (zerosign s a) \<longleftrightarrow> is_nan a"
  by (metis float_distinct_finite(1) is_finite_def is_finite_zerosign zerosign_def)

lemma abs_less_conv: "\<bar>a+b\<bar> \<le> m \<longleftrightarrow> a+b\<in>{-m..m}" for m :: real
  by auto

lemma finite_zero: "is_finite 0"
  by (simp add: is_finite_def)

end