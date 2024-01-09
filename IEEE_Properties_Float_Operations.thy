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

private method prove_bound=(simp add: zero_eq_zero nonneg_valof fina finb finc finite_infinity finite_nan valof_zerosign Let_def del: round.simps split del: if_split), 
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
    and non_zero_b: "valof b \<noteq> 0"
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
    and pos_a: "valof a \<ge> 0"
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

lemma mul_add_three_numbers_finite:
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

context 
  fixes a b c::"('e, 'f)float"
begin
lemma three_mul_added_numbers_finite:
  assumes 
      "is_finite(fmul_add mode a b c)"
    shows "fmul_add mode a b c = (
    if (valof a * valof b + valof c)=0 then ( \<comment> \<open>Exact Zero Case. Same sign rules as for add apply. \<close>
        if (valof a * valof b)=0 \<and> (valof c)=0 \<and> (if sign a = sign b then 0 else 1)=sign c then zerosign (if sign a = sign b then 0 else 1) 0
        else if mode = To_ninfinity then -0
        else 0
      ) else ( \<comment> \<open>Not exactly zero: Rounding has sign of exact value, even if rounded val is zero\<close>
        zerosign (if (valof a * valof b + valof c)<0 then 1 else 0) (round mode (valof a * valof b + valof c))
      )
  )"
  
  using assms apply (simp_all add: fmul_add_def Let_def del: round.simps split del: if_split) 
  apply (simp_all add: if_split[where Q="is_nan a \<or> is_nan b \<or> is_nan c"]  float_distinct_finite Let_def verit_bool_simplify(7)  del: round.simps split del: if_split)
  apply (cases "is_infinity a \<and> is_zero b \<or>
         is_zero a \<and> is_infinity b \<or>
         is_infinity c \<and> (is_infinity a \<or> is_infinity b) \<and> (if sign a = sign b then 0 else 1) \<noteq> sign c")
  apply (simp_all add: if_not_P[where P="is_infinity a \<and> is_zero b \<or>
         is_zero a \<and> is_infinity b \<or>
         is_infinity c \<and> (is_infinity a \<or> is_infinity b) \<and> (if sign a = sign b then 0 else 1) \<noteq> sign c"]  float_distinct_finite Let_def verit_bool_simplify(7)  del: round.simps split del: if_split)
  
  apply (simp_all add: if_split[where P="is_finite"]  float_distinct_finite Let_def verit_bool_simplify(7)  del: round.simps split del: if_split)
  apply (simp_all add: if_not_P[where P="is_infinity c \<and> sign c = 0 \<or> (is_infinity a \<or> is_infinity b) \<and> (if sign a = sign b then 0 else 1) = 0"]  float_distinct_finite Let_def verit_bool_simplify(7)  del: round.simps split del: if_split)
  
  by (simp_all add: if_not_P[where P="is_infinity c \<and> sign c = Suc 0 \<or> (is_infinity a \<or> is_infinity b) \<and> (if sign a = sign b then 0 else 1) = Suc 0"]  float_distinct_finite Let_def verit_bool_simplify(7)  del: round.simps split del: if_split)


  lemma three_mul_added_numbers:
    assumes 
      "is_finite(fmul_add To_nearest a b c)"
   shows "\<bar>valof a * valof b + valof c\<bar> < threshold TYPE(('e, 'f)float)" 
     and "is_finite a" 
     and "is_finite b"
     and "is_finite c"
    using assms apply (simp_all add: fmul_add_def Let_def del: round.simps) 
    apply (simp_all add: if_split[where P="is_finite"]  float_distinct_finite Let_def verit_bool_simplify(7) )
    apply(cases "valof a * valof b + valof c = 0") using zero_l_threshold apply auto[1] apply argo
    apply (metis (full_types) One_nat_def float_cases_finite less_zeroE)
    apply (metis (full_types) One_nat_def float_cases_finite less_zeroE)
    by (metis float_cases_finite less_numeral_extra(3) numeral_1_eq_Suc_0 numerals(1) sign_cases)

  lemma three_mul_added_numbers_positive:
    assumes "is_finite(fmul_add To_nearest a b c)" 
        and "sign a = 0" and "sign b = 0" and "sign c = 0"
      shows "sign (fmul_add To_nearest a b c) = 0"
    using assms(1) three_mul_added_numbers_finite[where mode="To_nearest"]  apply(simp del: round.simps split del: if_split)
    apply (cases "valof a * valof b + valof c = 0")
    using assms apply (simp_all add:  if_split[where P="\<lambda>x. sign x=0"] if_split[where P="is_finite"] zerosign_def float_defs(22) float_defs(23) del: round.simps split del: if_split)
    by (metis add_less_zeroD ge_zero_rounding_ge_zero mult_less_0_iff nonpos_valof sign_cases three_mul_added_numbers(1) valof_nonpos_zero verit_comp_simplify1(3))

end

lemmas fop_finite = 
  add_two_numbers_finite
  sub_two_numbers_finite
  div_two_numbers_finite
  mul_two_numbers_finite
  sqrt_one_number_finite
  mul_add_three_numbers_finite

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

lemma mul_two_numbers_infinite:
  assumes illegal_cases1: "\<not>(is_infinity a \<and> is_zero b)" and illegal_cases2: " \<not>(is_zero a \<and> is_infinity b)"
   shows "(extended_valof (fmul To_ninfinity a b) \<le> extended_valof a * extended_valof b)" 
     and "(extended_valof (fmul To_pinfinity a b) \<ge> extended_valof a * extended_valof b)" 
     and "\<not> is_nan (fmul To_ninfinity a b)"
     and "\<not> is_nan (fmul To_pinfinity a b)"
  subgoal 
    unfolding fmul_def
    apply(cases "\<not> (is_infinity a \<or> is_infinity b)")
    apply(simp_all add: nnana nnanb extended_valof_zerosign assms del: round.simps split del: if_split)
    using assms apply prove_is_infinite_finite_cases
    apply(cases "sign a = sign b")
    using assms apply (simp_all add: assms extended_valof_def infinity_is_infinity ninfinity_unfold pinfinity_unfold infinity_simps(2))
    by (smt (verit) One_nat_def illegal_cases1 illegal_cases2 less_numeral_extra(3) sign_cases valof_nonneg_zero valof_nonpos_zero)
  subgoal 
    unfolding fmul_def
    apply(cases "\<not> (is_infinity a \<or> is_infinity b)")
    apply(simp_all add: nnana nnanb extended_valof_zerosign assms del: round.simps split del: if_split)
    using assms apply prove_is_infinite_finite_cases
    apply(cases "sign a = sign b")
    using assms apply (simp_all add: assms extended_valof_def infinity_is_infinity ninfinity_unfold pinfinity_unfold infinity_simps(2))
    by (smt (verit) One_nat_def illegal_cases1 illegal_cases2 less_numeral_extra(3) sign_cases valof_nonneg_zero valof_nonpos_zero)
  subgoal 
    unfolding fmul_def 
    apply(cases "is_infinity a \<or> is_infinity b")
    apply(simp_all add: nnana nnanb illegal_cases1 illegal_cases2 extended_valof_zerosign del: round.simps split del: if_split)
    apply (simp add: extended_valof_def infinity_is_infinity ninfinity_unfold pinfinity_unfold infinity_simps(2))
    using float_distinct(1) pinfinity_unfold apply auto[1]
    using assms apply prove_is_infinite_finite_cases
    done
  subgoal 
    unfolding fmul_def 
    apply(cases "is_infinity a \<or> is_infinity b")
    apply(simp_all add: nnana nnanb illegal_cases1 illegal_cases2 extended_valof_zerosign del: round.simps split del: if_split)
    apply (simp add: extended_valof_def infinity_is_infinity ninfinity_unfold pinfinity_unfold infinity_simps(2))
    using float_distinct(1) pinfinity_unfold apply auto[1]
    using assms apply prove_is_infinite_finite_cases
    done
  done



lemma div_two_numbers_infinite:
  assumes illegal_cases1: "valof b \<noteq> 0" and illegal_cases2: " \<not>(is_infinity a \<and> is_infinity b)"
   shows "(extended_valof (fdiv To_ninfinity a b) \<le> extended_valof a / extended_valof b)" 
     and "(extended_valof (fdiv To_pinfinity a b) \<ge> extended_valof a / extended_valof b)" 
     and "\<not> is_nan (fdiv To_ninfinity a b)"
     and "\<not> is_nan (fdiv To_pinfinity a b)"
  unfolding fdiv_def
  subgoal 
    apply (cases "is_infinity a")                                                                                            
    using  illegal_cases2 illegal_cases1 apply (simp_all add: if_split[where Q="is_zero a \<and> is_zero b"] zero_eq_zero nnana nnanb nnanc assms del: round.simps split del: if_split)
    subgoal 
      apply auto
      apply (cases "sign a = 0")
      using illegal_cases1
        apply (metis ereal_divide_ereal ereal_infty_less_eq2(1) extended_valof_finite pinfinity_unfold plus_infinity_bigger valof_nonneg)
      subgoal proof-
        assume assms2: "is_infinity a  "" \<not> is_infinity b " " sign a = sign b " " sign a \<noteq> 0"
        with sign_cases sign_neg_ereal have "extended_valof b \<le> 0" by metis
        with illegal_cases1 zero_eq_zero valof_zero_eq_evalof_zero have b_smaller: "extended_valof b < 0" by fastforce
        from assms2 ninfinity_unfold sign_cases extended_valof_def have "extended_valof a = MInfty"
          by (metis pinfinity_unfold)
        with b_smaller assms2 ereal_divide_ereal show ?thesis
          using extended_valof_finite plus_infinity_bigger by fastforce qed 
      using minus_infinity_smaller by auto
    apply (cases "is_infinity b")
    subgoal
      using assms
      apply (simp add: extended_valof_def del: round.simps split del: if_split)
      by (smt (z3) MInfty_eq_minfinity dual_order.eq_iff ereal_divide_Infty(1) ereal_divide_Infty(2) float_zero1 inf_not_zero infinity_ereal_def is_infinity_cases is_infinity_uminus valof_zero(2) zero_eq_zero zero_ereal_def)
    apply (simp add: assms zero_eq_zero extended_valof_zerosign del: round.simps split del: if_split)
    subgoal
      using illegal_cases1 apply(simp add: extended_valof_finite zero_eq_zero del: round.simps split del: if_split)
      using len_e round_to_ninfinity_infinite(1) by blast
    done
  subgoal 
    apply (cases "is_infinity a")
    using  illegal_cases2 illegal_cases1 apply (simp add: if_split[where Q="is_zero a \<and> is_zero b"] nnana nnanb nnanc assms extended_valof_def zero_eq_zero del: round.simps split del: if_split) 
    apply simp
    apply (smt (verit) illegal_cases1 infinity_simps(1) infinity_simps(2) is_infinity_uminus nonneg_valof nonpos_valof not_infinite val_zero)
    apply (simp add: nnana nnanb nnanc assms del: round.simps split del: if_split) 
    apply (cases "is_infinity b")
    subgoal
      using assms
      apply (simp add: extended_valof_def del: round.simps split del: if_split)
      by (smt (z3) MInfty_eq_minfinity dual_order.eq_iff ereal_divide_Infty(1) ereal_divide_Infty(2) float_zero1 inf_not_zero infinity_ereal_def is_infinity_cases is_infinity_uminus valof_zero(2) zero_eq_zero zero_ereal_def)
    apply (simp add: assms zero_eq_zero extended_valof_zerosign del: round.simps split del: if_split)
    subgoal
      using illegal_cases1 apply(simp add: extended_valof_finite zero_eq_zero del: round.simps split del: if_split)
      using len_e round_to_infinity_infinite(1) by blast
    done
  subgoal
    unfolding fdiv_def 
    apply(cases "is_infinity a")
    apply(simp_all add: nnana nnanb illegal_cases1 illegal_cases2 extended_valof_zerosign del: round.simps split del: if_split)
    apply (simp add: extended_valof_def infinity_is_infinity ninfinity_unfold pinfinity_unfold infinity_simps(2))
    using float_distinct(1) illegal_cases2 inf_not_zero pinfinity_unfold apply auto[1]
    apply (cases "is_infinity b")
    using float_distinct(4) illegal_cases1 zero_eq_zero apply fastforce
    apply(simp add: nnana nnanb illegal_cases1 illegal_cases2 extended_valof_zerosign zero_eq_zero del: round.simps split del: if_split)
    using assms by prove_is_infinite_keep_not_nan
  subgoal
    unfolding fdiv_def 
    apply(cases "is_infinity a")
    apply(simp_all add: nnana nnanb illegal_cases1 illegal_cases2 extended_valof_zerosign del: round.simps split del: if_split)
    apply (simp add: extended_valof_def infinity_is_infinity ninfinity_unfold pinfinity_unfold infinity_simps(2))
    using float_distinct(1) illegal_cases2 inf_not_zero pinfinity_unfold apply auto[1]
    apply (cases "is_infinity b")
    using float_distinct(4) illegal_cases1 zero_eq_zero apply fastforce
    apply(simp add: nnana nnanb illegal_cases1 illegal_cases2 extended_valof_zerosign zero_eq_zero del: round.simps split del: if_split)
    using assms by prove_is_infinite_keep_not_nan
  done

lemma muladd_illegal_simp:
  assumes illegal_cases1: "\<not>(is_infinity a \<and> is_zero b)" and illegal_cases2: " \<not>(is_zero a \<and> is_infinity b)"
      and illegal_cases3: "\<not>(is_infinity c \<and> (is_infinity a \<or> is_infinity b) \<and> ((sign a = sign b \<and> sign c = 1) \<or> (sign a \<noteq> sign b \<and> sign c = 0)))"
    shows "\<not>(is_infinity a \<and> valof b = 0 \<or>
            valof a = 0 \<and> is_infinity b \<or> is_infinity c \<and> (is_infinity a \<or> is_infinity b) \<and> (if sign a = sign b then 0 else 1) \<noteq> sign c)"
  apply(simp add:illegal_cases1 illegal_cases2 illegal_cases3 sign_cases zero_val)
  by (metis One_nat_def illegal_cases1 illegal_cases2 illegal_cases3 sign_cases zero_val)

lemma infinity_sign_cases:
  assumes "(is_infinity x \<longrightarrow> (0::nat) < sign x)"
    and "(is_infinity x \<longrightarrow> sign x \<noteq> Suc (0::nat))"
  shows "extended_valof x = valof x"
  using sign_cases assms extended_valof_finite
  by (metis One_nat_def less_numeral_extra(3))

lemma infinity_sign_cases2:
  assumes "(is_infinity z \<longrightarrow> (0::nat) < sign z) \<and> (\<not> is_infinity x \<and> \<not> is_infinity y \<or> (0::nat) < (if sign x = sign y then 0::nat else (1::nat)))"
    and "(is_infinity z \<longrightarrow> sign z \<noteq> Suc (0::nat)) \<and> (\<not> is_infinity x \<and> \<not> is_infinity y \<or> (if sign x = sign y then 0::nat else (1::nat)) \<noteq> Suc (0::nat))"
  shows "extended_valof x = valof x" and "extended_valof y = valof y"
  subgoal
  proof - 
    from assms have a1: "(\<not> is_infinity x \<and> \<not> is_infinity y \<or> (0::nat) < (if sign x = sign y then 0::nat else (1::nat)))" by presburger
    from assms have a2: "(\<not> is_infinity x \<and> \<not> is_infinity y \<or> (if sign x = sign y then 0::nat else (1::nat)) \<noteq> Suc (0::nat))" by fast
    from a1 a2 have "\<not> is_infinity x \<and> \<not> is_infinity y"
      using One_nat_def by presburger
    with extended_valof_finite show ?thesis by fastforce
  qed
  subgoal
  proof - 
    from assms have a1: "(\<not> is_infinity x \<and> \<not> is_infinity y \<or> (0::nat) < (if sign x = sign y then 0::nat else (1::nat)))" by presburger
    from assms have a2: "(\<not> is_infinity x \<and> \<not> is_infinity y \<or> (if sign x = sign y then 0::nat else (1::nat)) \<noteq> Suc (0::nat))" by fast
    from a1 a2 have "\<not> is_infinity x \<and> \<not> is_infinity y"
      using One_nat_def by presburger
    with extended_valof_finite show ?thesis by fastforce
  qed
  done


lemma mul_add_first_case_simped: "(is_infinity c \<longrightarrow> (0::nat) < sign c) \<and>
    (\<not> is_infinity a \<and> \<not> is_infinity b \<or> (0::nat) < (if sign a = sign b then 0::nat else (1::nat))) \<longrightarrow> 
    (if (is_infinity c \<and> sign c = (0::nat) \<or> (is_infinity a \<or> is_infinity b) \<and> (if sign a = sign b then 0::nat else (1::nat)) = (0::nat)) then x else y = y)"
  by simp


lemma mul_add_three_numbers_infinite:
  assumes illegal_cases1: "\<not>(is_infinity a \<and> is_zero b)" and illegal_cases2: " \<not>(is_zero a \<and> is_infinity b)"
      and illegal_cases3: "\<not>(is_infinity c \<and> (is_infinity a \<or> is_infinity b) \<and> ((sign a = sign b \<and> sign c = 1) \<or> (sign a \<noteq> sign b \<and> sign c = 0)))"
   shows "(extended_valof (fmul_add To_ninfinity a b c) \<le> (extended_valof a * extended_valof b) + extended_valof c)" 
     and "(extended_valof (fmul_add To_pinfinity a b c) \<ge> (extended_valof a * extended_valof b) + extended_valof c)" 
     and "\<not> is_nan (fmul_add To_ninfinity a b c)"
     and "\<not> is_nan (fmul_add To_pinfinity a b c)"
  
  supply [[show_types]]
  subgoal
    unfolding fmul_add_def
    using assms apply(simp_all add: Let_def muladd_illegal_simp nnana nnanb nnanc inf_not_zero zero_eq_zero del: round.simps split del: if_split)
    apply (cases "is_infinity c \<and> sign c = 0 \<or> (is_infinity a \<or> is_infinity b) \<and> (if sign a = sign b then (0::nat) else 1) = 0")
    apply(simp_all add: if_P if_not_P del: round.simps split del: if_split)
    subgoal
      apply (cases " is_infinity c \<and> sign c = (0::nat)")
      subgoal proof -
        assume assms2: "is_infinity c \<and> sign c = (0::nat)"
        have not_min: "\<not> is_infinity a \<and> \<not> is_infinity b \<longrightarrow> extended_valof a * extended_valof b \<noteq> MInfty"
          by (simp add: extended_valof_finite)
        from assms2 extended_valof_def pinfinity_unfold have "extended_valof c = PInfty" by metis
        with not_min plus_ereal.simps show ?thesis
          by (metis ereal_less_eq(1) infinity_ereal_def) qed
      subgoal proof -
        assume assms2: "
    is_infinity c \<and> sign c = (0::nat) \<or> (is_infinity a \<or> is_infinity b) \<and> (if sign a = sign b then 0::nat else (1::nat)) = (0::nat) ""
    \<not> (is_infinity c \<and> sign c = (0::nat))"
        then have "(is_infinity a \<or> is_infinity b) \<and> (if sign a = sign b then 0::nat else (1::nat)) = (0::nat)" by fast
        with zero_neq_one have options: "(is_infinity a \<or> is_infinity b) \<and> sign a = sign b" by metis
        with nnana nnanb assms mul_infinity have "extended_valof a * extended_valof b = PInfty" by metis
        with plus_ereal.simps(2) have "extended_valof a * extended_valof b + extended_valof c = PInfty" by force
        then show ?thesis by fastforce qed 
      done
    apply (cases "is_infinity c \<and> sign c = Suc (0::nat) \<or>
            (is_infinity a \<or> is_infinity b) \<and> (if sign a = sign b then 0::nat else (1::nat)) = Suc (0::nat)")
    apply(simp_all add: if_P if_not_P Let_def del: round.simps split del: if_split)
    using minus_infinity_smaller
    apply (metis extended_valof_minus)
    apply (cases "valof a * valof b + valof c = (0::real)")
      apply(simp_all add: if_P if_not_P Let_def del: round.simps split del: if_split) 
    apply (simp add: infinity_sign_cases infinity_sign_cases2 round_to_ninfinity_infinite round_to_infinity_infinite extended_valof_zerosign valof_zerosign Let_def del: round.simps split del: if_split)
    apply (simp add: extended_valof_zerosign extended_valof_zero extended_valof_neg_zero)
    apply(simp add: extended_valof_zerosign infinity_sign_cases infinity_sign_cases2 del: round.simps split del: if_split)
    apply (rule round_to_ninfinity_infinite(1))
    using len_e by blast
  subgoal
    unfolding fmul_add_def
    apply(simp add: Let_def nnana nnanb nnanc assms del: round.simps split del: if_split)
    apply (cases "is_infinity c \<and> (is_infinity a \<or> is_infinity b) \<and> (if sign a = sign b then 0::nat else (1::nat)) \<noteq> sign c")
    apply (simp_all add: if_P if_not_P len_e del: round.simps split del: if_split)
    apply (metis One_nat_def illegal_cases3 sign_cases)
    apply (cases "is_infinity c \<and> sign c = 0 \<or> (is_infinity a \<or> is_infinity b) \<and> (if sign a = sign b then (0::nat) else 1) = 0")
    using assms apply (simp_all add: if_P if_not_P len_e Let_def assms zero_eq_zero del: round.simps split del: if_split)
    using plus_infinity_bigger apply blast
    apply (cases "is_infinity c \<and> sign c = Suc (0::nat) \<or>
            (is_infinity a \<or> is_infinity b) \<and> (if sign a = sign b then 0::nat else (1::nat)) = Suc (0::nat)")
    using assms apply (simp_all add: if_P if_not_P len_e del: round.simps split del: if_split)
    subgoal 
      apply (cases "is_infinity c \<and> sign c = Suc (0::nat)")
      subgoal proof -
        assume assms2: "is_infinity c \<and> sign c = Suc (0::nat)" "is_infinity c \<longrightarrow> \<not> is_infinity a \<and> \<not> is_infinity b \<or> (if sign a = sign b then 0::nat else (1::nat)) = sign c"
        have not_pin2: "\<not> is_infinity a \<and> \<not> is_infinity b \<longrightarrow> extended_valof a * extended_valof b \<noteq> PInfty" by (simp add: extended_valof_finite)
        from extended_valof_multiply_positive nnana nnanb have "sign a \<noteq> sign b \<longrightarrow> extended_valof a * extended_valof b \<noteq> PInfty" by (metis ereal_less(5) infinity_ereal_def)
        with assms2 not_pin2 have not_pin: "extended_valof a * extended_valof b \<noteq> PInfty" by presburger
        from assms2 ninfinity_unfold minfty_eq_minus_inifity have "extended_valof c = MInfty" by (metis One_nat_def)
        with not_pin plus_ereal.simps minus_infinity_smaller minfty_eq_minus_inifity show ?thesis
          by (metis ereal_MInfty_eq_plus infinity_ereal_def uminus_ereal.simps(2)) qed
      subgoal proof -
        assume assms2: "(is_infinity c \<longrightarrow> (0::nat) < sign c) \<and>
    (\<not> is_infinity a \<and> \<not> is_infinity b \<or> (0::nat) < (if sign a = sign b then 0::nat else (1::nat)))" "
    is_infinity c \<and> sign c = Suc (0::nat) \<or>
    (is_infinity a \<or> is_infinity b) \<and> (if sign a = sign b then 0::nat else (1::nat)) = Suc (0::nat) ""
    \<not> (is_infinity c \<and> sign c = Suc (0::nat))"
        then have "(is_infinity c \<longrightarrow> (0::nat) < sign c)" by auto
        with assms(3) have not_pin: "extended_valof c \<noteq> PInfty"
          by (metis assms2(3) ereal.distinct(1) infinity_sign_cases)
        from assms2 have "(is_infinity a \<or> is_infinity b) \<and> (if sign a = sign b then 0::nat else (1::nat)) = Suc (0::nat)" by fast
        with zero_neq_one have options: "(is_infinity a \<or> is_infinity b) \<and> sign a \<noteq> sign b" by auto
        with nnana nnanb assms mul_infinity have is_min: "extended_valof a * extended_valof b = MInfty" by metis
        with not_pin plus_ereal.simps(2) have "extended_valof a * extended_valof b + extended_valof c = MInfty" by force
        then show ?thesis
          by (metis dual_order.refl extended_valof_minus minfty_eq_minus_inifity) qed
      done
    apply (cases "valof a * valof b + valof c = (0::real)")
    apply (simp_all add: infinity_sign_cases infinity_sign_cases2 round_to_ninfinity_infinite round_to_infinity_infinite extended_valof_zerosign valof_zerosign Let_def del: round.simps split del: if_split)
    apply (simp add: extended_valof_zerosign extended_valof_zero extended_valof_neg_zero)
    using len_e round_to_infinity_infinite by blast
 oops
end

(*
preconditions for fold:
all need to be finite
then outcome \<le> or \<ge>
and outcome not is_nan

mul_add maybe also no zeros
*)
end