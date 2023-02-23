theory IEEE_Properties_Float_Operations
  imports IEEE_Properties_Rounding "HOL-Eisbach.Eisbach"
begin

context 
  fixes a b c::"('e, 'f)float"
  assumes fina: "is_finite a"
    and finb: "is_finite b"
    and finc: "is_finite c"
    and len_e: "1 < LENGTH('e)"
begin

private method prove_bound=(simp add: fina finb finc finite_infinity finite_nan valof_zerosign Let_def del: round.simps split del: if_split), 
  insert round_to_ninfinity round_to_infinity len_e, blast


lemma add_two_numbers_finite:
  assumes 
     threshold: "\<bar>valof a + valof b\<bar> \<le> largest TYPE(('e, 'f)float)"
   shows "(valof (fadd To_ninfinity a b) \<le> valof a + valof b)" 
     and "(valof (fadd To_pinfinity a b) \<ge> valof a + valof b)" 
     and "is_finite (fadd To_ninfinity a b)"
     and "is_finite (fadd To_pinfinity a b)"
  unfolding fadd_def
  using assms apply prove_bound
  using assms apply prove_bound
  using assms apply prove_bound
  using assms apply prove_bound
  done

lemma sub_two_numbers_finite:
  assumes 
     threshold: "\<bar>valof a - valof b\<bar> \<le> largest TYPE(('e, 'f)float)"
   shows "(valof (fsub To_ninfinity a b) \<le> valof a - valof b)" 
     and "(valof (fsub To_pinfinity a b) \<ge> valof a - valof b)" 
     and "is_finite (fsub To_ninfinity a b)"
     and "is_finite (fsub To_pinfinity a b)"
  unfolding fsub_def
  using assms apply prove_bound
  using assms apply prove_bound
  using assms apply prove_bound
  using assms apply prove_bound
  done
  
lemma mul_two_numbers_finite:
  assumes 
     threshold: "\<bar>valof a * valof b\<bar> \<le> largest TYPE(('e, 'f)float)"
   shows "(valof (fmul To_ninfinity a b) \<le> valof a * valof b)" 
     and "(valof (fmul To_pinfinity a b) \<ge> valof a * valof b)" 
     and "is_finite (fmul To_ninfinity a b)"
     and "is_finite (fmul To_pinfinity a b)"
  unfolding fmul_def
  using assms apply prove_bound
  using assms apply prove_bound
  using assms apply prove_bound
  using assms apply prove_bound
  done

lemma div_two_numbers_finite:
  assumes 
     threshold: "\<bar>valof a / valof b\<bar> \<le> largest TYPE(('e, 'f)float)"
    and non_zero_b: "\<not> is_zero b"(*transform to abstract instead of concrete*)
   shows "(valof (fdiv To_ninfinity a b) \<le> valof a / valof b)" 
     and "(valof (fdiv To_pinfinity a b) \<ge> valof a / valof b)" 
     and "is_finite (fdiv To_ninfinity a b)"
     and "is_finite (fdiv To_pinfinity a b)"
  unfolding fdiv_def
  using assms apply prove_bound
  using assms apply prove_bound
  using assms apply prove_bound
  using assms apply prove_bound
  done

lemma sqrt_one_number_finite:
  assumes 
     threshold: "\<bar>sqrt (valof a)\<bar> \<le> largest TYPE(('e, 'f)float)"
    and pos_a: "sign a = 0"(*transform to abstract instead of concrete*)
   shows "(valof (fsqrt To_ninfinity a) \<le> sqrt (valof a))" 
     and "(valof (fsqrt To_pinfinity a) \<ge> sqrt (valof a))" 
     and "is_finite (fsqrt To_ninfinity a)"
     and "is_finite (fsqrt To_pinfinity a)"
  unfolding fsqrt_def
  apply(cases "is_zero a")
  using float_distinct(4) val_zero apply force
  using assms apply prove_bound
  apply(cases "is_zero a")
  using float_distinct(4) val_zero apply force
  using assms apply prove_bound
  apply(cases "is_zero a")
  apply (smt (verit) fina nan_not_finite)
  using assms apply prove_bound
  apply(cases "is_zero a")
  apply (smt (verit) fina nan_not_finite)
  using assms apply prove_bound
  done

lemma mul_add_two_numbers_finite:
  assumes 
     threshold: "\<bar>valof a * valof b + valof c\<bar> \<le> largest TYPE(('e, 'f)float)"
   shows "(valof (fmul_add To_ninfinity a b c) \<le> valof a * valof b + valof c)" 
     and "(valof (fmul_add To_pinfinity a b c) \<ge> valof a * valof b + valof c)" 
     and "is_finite (fmul_add To_ninfinity a b c)"
     and "is_finite (fmul_add To_pinfinity a b c)"
  unfolding fmul_add_def
  apply (simp add: fina finb finc finite_infinity finite_nan valof_zerosign del: round.simps split del: if_split)
  apply (cases "valof a * valof b + valof c = 0")
  apply (simp add: valof_zerosign)
  using assms apply prove_bound
  apply (simp add: fina finb finc finite_infinity finite_nan valof_zerosign del: round.simps split del: if_split)
  apply (cases "valof a * valof b + valof c = 0")
  apply (simp add: valof_zerosign)
  using assms apply prove_bound
  apply (simp add: fina finb finc finite_infinity finite_nan valof_zerosign del: round.simps split del: if_split)
  apply (cases "valof a * valof b + valof c = 0")
  apply (simp add: finite_zero)
  using assms apply prove_bound
  apply (simp add: fina finb finc finite_infinity finite_nan valof_zerosign del: round.simps split del: if_split)
  apply (cases "valof a * valof b + valof c = 0")
  apply (simp add: finite_zero)
  using assms apply prove_bound
  done
end

lemmas fop_finite = 
  add_two_numbers_finite
  sub_two_numbers_finite
  div_two_numbers_finite
  mul_two_numbers_finite
  sqrt_one_number_finite
  mul_add_two_numbers_finite

context 
  fixes a b c::"('e, 'f)float"
  assumes nnana: "\<not> is_nan a"
    and nnanb: "\<not> is_nan b"
    and nnanc: "\<not> is_nan c"
    and len_e: "1 < LENGTH('e)"
begin

private method prove_is_infinite_setup=(simp add: nnana nnanb nnanc del: round.simps split del: if_split)
private method prove_is_infinite_finite_cases=(simp add: extended_valof_zerosign extended_valof_finite del: round.simps split del: if_split), insert len_e round_to_ninfinity_infinite round_to_infinity_infinite extended_valof_finite, blast
private method prove_is_infinite_something_infinite=simp, (smt (verit) infinity_simps(1) infinity_simps(2) is_infinity_cases is_infinity_uminus zero_neq_one)

private method prove_is_infinite_keep_not_nan=
  prove_is_infinite_setup, 
  cases "is_infinity a", 
  insert nnana, fastforce, 
  cases "is_infinity b",
  (simp add: nnanb), 
  prove_is_infinite_finite_cases

private method prove_is_infinite_smaller=
  prove_is_infinite_setup ,
  (cases "is_infinity a"),
  (simp add: extended_valof_def),
  prove_is_infinite_something_infinite,
  (cases "is_infinity b"),
  (simp add: extended_valof_def infinity_simps),
  (metis infinity_is_infinity is_infinity_cases),
  prove_is_infinite_finite_cases

lemma add_two_numbers_infinite:
  assumes illegal_cases: "\<not>(is_infinity a \<and> is_infinity b \<and> sign a \<noteq> sign b)"
   shows "(extended_valof (fadd To_ninfinity a b) \<le> extended_valof a + extended_valof b)" 
     and "(extended_valof (fadd To_pinfinity a b) \<ge> extended_valof a + extended_valof b)" 
     and "\<not> is_nan (fadd To_ninfinity a b)"
     and "\<not> is_nan (fadd To_pinfinity a b)"
  unfolding fadd_def
  subgoal 
    apply prove_is_infinite_setup 
    apply (cases "is_infinity a")
     apply (simp add: extended_valof_def)
    using illegal_cases is_infinity_cases apply blast
    apply (cases "is_infinity b")
     apply (simp add: extended_valof_def infinity_simps)
    apply (metis is_infinity_cases)
    apply prove_is_infinite_finite_cases
    done
  subgoal using assms by prove_is_infinite_smaller
  using assms apply prove_is_infinite_keep_not_nan
  using assms apply prove_is_infinite_keep_not_nan
  done

lemma sub_two_numbers_infinite:
  assumes illegal_cases: "\<not>(is_infinity a \<and> is_infinity b \<and> sign a = sign b)"
   shows "(extended_valof (fsub To_ninfinity a b) \<le> extended_valof a - extended_valof b)" 
     and "(extended_valof (fsub To_pinfinity a b) \<ge> extended_valof a - extended_valof b)" 
     and "\<not> is_nan (fsub To_ninfinity a b)"
     and "\<not> is_nan (fsub To_pinfinity a b)"
  unfolding fsub_def
  subgoal 
    apply prove_is_infinite_setup 
    apply (cases "is_infinity a")
     apply (simp add: extended_valof_def)
    using illegal_cases is_infinity_cases apply blast
    apply (cases "is_infinity b")
     apply (simp add: extended_valof_def infinity_simps)
    apply (metis float_neg_sign is_infinity_cases)
    apply prove_is_infinite_finite_cases
    done
  subgoal using assms by prove_is_infinite_smaller
  using assms apply prove_is_infinite_keep_not_nan
  using assms apply prove_is_infinite_keep_not_nan
  done

lemma not_infinite: "\<not> x=plus_infinity \<and> \<not>x=minus_infinity \<Longrightarrow> \<not>is_infinity x"
  using is_infinity_cases by blast

private method prove_is_infinite_mul = 
  simp

lemma mul_two_numbers_infinite:
  assumes illegal_cases1: "\<not>(is_infinity a \<and> is_zero b)" and illegal_cases2: " \<not>(is_zero a \<and> is_infinity b)"
   shows "(extended_valof (fmul To_ninfinity a b) \<le> extended_valof a * extended_valof b)" 
     and "(extended_valof (fmul To_pinfinity a b) \<ge> extended_valof a * extended_valof b)" 
     and "\<not> is_nan (fmul To_ninfinity a b)"
     and "\<not> is_nan (fmul To_pinfinity a b)"
  subgoal 
    unfolding fmul_def 
    apply(cases "is_infinity a \<or> is_infinity b")
    apply(simp_all add: nnana nnanb illegal_cases1 illegal_cases2 extended_valof_zerosign del: round.simps split del: if_split)
    subgoal
      apply(cases "sign a = sign b")
      apply (simp_all add: extended_valof_def infinity_is_infinity ninfinity_unfold pinfinity_unfold infinity_simps(2))
      apply (metis One_nat_def less_numeral_extra(3) sign_cases illegal_cases1 illegal_cases2 valof_nonneg_zero valof_nonpos_zero)  
      done
    using assms apply prove_is_infinite_keep_not_nan
    done
  subgoal 
    unfolding fmul_def 
    apply(cases "is_infinity a \<or> is_infinity b")
    apply(simp_all add: nnana nnanb illegal_cases1 illegal_cases2 extended_valof_zerosign del: round.simps split del: if_split)
    subgoal
      apply(cases "sign a = sign b")
      apply (simp_all add: extended_valof_def infinity_is_infinity ninfinity_unfold pinfinity_unfold)
      apply (metis One_nat_def less_numeral_extra(3) sign_cases illegal_cases1 illegal_cases2 valof_nonneg_zero valof_nonpos_zero)  
      done
    using assms apply prove_is_infinite_keep_not_nan
    done
  subgoal 
    unfolding fmul_def 
    apply(cases "is_infinity a \<or> is_infinity b")
    apply(simp_all add: nnana nnanb illegal_cases1 illegal_cases2 extended_valof_zerosign del: round.simps split del: if_split)
    subgoal
      apply (simp_all add: extended_valof_def infinity_is_infinity ninfinity_unfold pinfinity_unfold infinity_simps(2))
      using float_distinct(1) infinity_is_infinity by blast
    using assms apply prove_is_infinite_keep_not_nan
    done
  subgoal 
    unfolding fmul_def 
    apply(cases "is_infinity a \<or> is_infinity b")
    apply(simp_all add: nnana nnanb illegal_cases1 illegal_cases2 extended_valof_zerosign del: round.simps split del: if_split)
    subgoal
      apply (simp_all add: extended_valof_def infinity_is_infinity ninfinity_unfold pinfinity_unfold infinity_simps(2))
      using float_distinct(1) infinity_is_infinity by blast
    using assms apply prove_is_infinite_keep_not_nan
    done
  done
end

end