theory IEEE_Properties_Rounding
imports IEEE_Properties_Basic_Extension "HOL-Library.Extended_Real"
begin

lemma round_to_ninfinity_not_empty:
  assumes threshold: "\<bar>a\<bar> \<le> largest TYPE(('e, 'f)float)" and len_e: "1 < LENGTH('e)"
  shows "{c::('e, 'f) float. is_finite c \<and> valof c \<le> a} \<noteq> {}"
proof -
  have fin_bot: "is_finite (bottomfloat::('e, 'f) float)" using finite_bottomfloat by auto
  from threshold valof_topfloat len_e have "(valof (bottomfloat::('e, 'f) float)) \<le> a"
    by (simp add: bottomfloat_eq_m_largest)
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
  shows "P ((closest valof (\<lambda>c. True) {c. P c} a)::('e, 'f) float)"
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

end