theory ULP_Accuracy_Matrix
  imports ULP_Accuracy_Propagation Matrix_Extension
begin

fun float_list_mul :: "('e, 'f) float list \<Rightarrow> ('e, 'f) float list \<Rightarrow> ('e, 'f) float"
  where "float_list_mul [] _ = 0"
  | "float_list_mul _ []  = 0"
  | "float_list_mul (a#as) (b#bs) = fmul_add To_nearest a b (float_list_mul as bs)"

lemma list_float_multiplication:
  assumes a_rel: "list_all2 (\<lambda>f r. ulp_accuracy r (f::('e,'f) float) a_accuracy) (afs::('e, 'f) float list) ars"
      and b_rel: "list_all2 (\<lambda>f r. ulp_accuracy r (f::('e,'f) float) b_accuracy) (bfs::('e, 'f) float list) brs"
      and signs: "(\<forall>f\<in>set (afs). IEEE.sign f = 0) \<and> (\<forall>f\<in>set (bfs). IEEE.sign f = 0)"
      and probs: "(\<forall>r\<in>set (ars). 0 \<le> r \<and> r \<le> 1) \<and> (\<forall>r\<in>set (brs). 0 \<le> r \<and> r \<le> 1)"
      and "1 < LENGTH('e)"
      and "a_accuracy \<le> (2::real) ^ LENGTH('f)"
      and "b_accuracy \<le> (2::real) ^ LENGTH('f)"
      and "1 < LENGTH('f)"
      and "is_finite (float_list_mul afs bfs)"
      and "length afs = length bfs"
    shows "ulp_accuracy (foldr (+) (map2 (*) ars brs) 0) (float_list_mul afs bfs) ((2*a_accuracy + 2*b_accuracy + 0.5)*length afs) \<and> IEEE.sign (float_list_mul afs bfs) = 0"
using assms proof (induction afs arbitrary: bfs ars brs)
  case Nil
  hence [simp]: "bfs=[]" "ars=[]" "brs=[]" by auto
  show ?case by (simp add:  ulp_accuracy_def Nil.prems(9) float_defs(22) finite_zero)
next
  case (Cons a afs)

  then have "length bfs \<ge> 1" by fastforce
  then obtain b bfs' where bfs_def[simp]: "bfs=b#bfs'" 
    by (metis Cons.prems(10) length_Suc_conv)
  from Cons.prems obtain ar ars' where ars_def[simp]: "ars = ar#ars'"
    by (metis list_all2_Cons1) 
  from Cons.prems bfs_def obtain br brs' where brs_def[simp]: "brs=br#brs'"
    by (metis list_all2_Cons1)

  from Cons.prems bfs_def float_list_mul.simps have expanded_float_list_mul:
    "(float_list_mul (a#afs) bfs) = fmul_add To_nearest a b (float_list_mul afs bfs')" by fast
  {
    have 
    "ulp_accuracy (foldr (+) (map2 (*) ars' brs') 0) (float_list_mul afs bfs') ((2*a_accuracy + 2*b_accuracy + 0.5)*length afs)  \<and> IEEE.sign (float_list_mul afs bfs') = 0"
      using Cons apply simp using expanded_float_list_mul three_mul_added_numbers(4) by blast
  } note step1 = this

  
  have "ulp_accuracy (ar::real) (a) (a_accuracy::real)" using Cons.prems(1) by simp
  moreover have "ulp_accuracy (br::real) (b) (b_accuracy::real)" using Cons.prems(2) by simp
  moreover have "(1::nat) < LENGTH('e)" using Cons.prems(5) by blast
  moreover have "(1::nat) < LENGTH('f)" using Cons.prems(8) by blast
  moreover have "IEEE.sign a = (0::nat)" using Cons.prems(3) by fastforce
  moreover have "IEEE.sign b = (0::nat)" using bfs_def Cons.prems(3) by fastforce
  
  moreover have "a_accuracy \<le> (2::real) ^ LENGTH('f)" using Cons.prems(6) by fast
  moreover have "b_accuracy \<le> (2::real) ^ LENGTH('f)" using Cons.prems(7) by fast
  moreover have "(0::real) \<le> ar" using Cons.prems(4) by force
  moreover have "ar \<le> (1::real)" using Cons.prems(4) by force
  moreover have "(0::real) \<le> br" using Cons.prems(4) by force
  moreover have "br \<le> (1::real)" using Cons.prems(4) by force
  moreover from step1 have "ulp_accuracy (foldr (+) (map2 (*) ars' brs') 0) (float_list_mul afs bfs') ((2*a_accuracy + 2*b_accuracy + 0.5)*length afs)" by blast
  moreover have "is_finite (fmul_add To_nearest a b (float_list_mul afs bfs'))" using Cons.prems(9) expanded_float_list_mul by argo
  moreover have "IEEE.sign (float_list_mul afs bfs') = (0::nat)" using step1 by fast
  ultimately have "ulp_accuracy (ar * br + (foldr (+) (map2 (*) ars' brs') 0)) (fmul_add To_nearest a b (float_list_mul afs bfs')) (2*a_accuracy + 2*b_accuracy + ((2*a_accuracy + 2*b_accuracy + 0.5)*length afs) + 0.5)"

    using multiplication_addition_error_propagation_ulp_accuracy2 Cons.IH by blast
  with expanded_float_list_mul ars_def brs_def have "ulp_accuracy (foldr (+) (map2 (*) ars brs) (0::real)) (float_list_mul (a # afs) bfs)
        (2*a_accuracy + 2*b_accuracy + ((2*a_accuracy + 2*b_accuracy + 0.5)*length afs) + 0.5)" by force
  moreover have "(2*a_accuracy + 2*b_accuracy + ((2*a_accuracy + 2*b_accuracy + 0.5)*length afs) + 0.5) = ((2*a_accuracy + 2*b_accuracy + 0.5)*(1 + length afs))" 
    using distrib_left[where a="(2*a_accuracy + 2*b_accuracy + 0.5)" and b="1" and c="length afs"] by force
  ultimately have step2: "ulp_accuracy (foldr (+) (map2 (*) ars brs) (0::real)) (float_list_mul (a # afs) bfs)
        (((2::real) * a_accuracy + (2::real) * b_accuracy + (5::real) / (10::real)) * real (length (a # afs)))" by fastforce

  have "IEEE.sign a = (0::nat)" using Cons.prems(3) by fastforce
  moreover have "IEEE.sign b = (0::nat)" using bfs_def Cons.prems(3) by fastforce
  moreover have "IEEE.sign (float_list_mul afs bfs') = (0::nat)" using step1 by fast
  moreover have "is_finite (fmul_add To_nearest a b (float_list_mul afs bfs'))" using Cons.prems(9) expanded_float_list_mul by argo
  ultimately have "IEEE.sign (float_list_mul (a # afs) bfs) = (0::nat)" using expanded_float_list_mul three_mul_added_numbers_positive by auto
  with step2 show ?case by blast
qed  

definition float_vec_to_list_mul :: "('e, 'f) float vec \<Rightarrow> ('e, 'f) float vec \<Rightarrow> ('e, 'f) float"
  where "float_vec_to_list_mul a b = float_list_mul (list_of_vec a) (list_of_vec b)"
definition float_vec_mul :: "('e, 'f) float vec \<Rightarrow> ('e, 'f) float vec \<Rightarrow> ('e, 'f) float"
  where "float_vec_mul as bs = fold (\<lambda> i s. fmul_add To_nearest (as $ nat i) (bs $ nat i) s) [0..int (dim_vec as)-1] 0"
definition real_vec_mul :: "real vec \<Rightarrow> real vec \<Rightarrow> real"
  where "real_vec_mul as bs = fold (\<lambda> i s.  (as $ nat i) * (bs $ nat i) + s) [0..int (dim_vec as) - 1] 0"
(*
fold (lambda i s. s + ai*bi) [0..n] 0)
*)
value "\<Sum>i \<in> {0 ..< 2}. [(1::real),1] ! i * [1,1] ! i"


lemma sum_fold_helper: "(\<lambda>i::int. (+) ((f i)::real)) = ((+) \<circ> (\<lambda>x::nat. f (int x)))" by auto

lemma sum_fold_helper_comp_fun_commute_on:
  shows "comp_fun_commute_on {n::int. True} (\<lambda>i::int. (+) ((f i)::real))"
  by(auto simp add:comp_fun_commute_on_def)

lemma sum_fold_helper_subset:
  shows "set (xs::int list) \<subseteq> {n::int. True}"
  by blast



lemma sum_fold_helper_set_to_list:
  shows "{0::int..<int n} = (set [0::int..int n-1])"
  by auto 

lemma sum_fold_helper_remdups:
  shows "(remdups [0::int..int n-1]) = [0::int..int n-1]"
  by simp

lemma sum_fold_helper_lambda:
  shows "((+) \<circ> f) = (\<lambda>i::int. (+) (f i))"
  by auto

lemma sum_fold':
  shows "fold (\<lambda>i::int. (+) ((f i)::real)) [0::int..int n-1] (0::real) =
    (\<Sum>i::int = 0::int..<n. f i)"
  apply(simp add:Groups_Big.comm_monoid_add_class.sum.eq_fold)
proof -
  from List.comp_fun_commute_on.fold_set_fold_remdups[OF sum_fold_helper_comp_fun_commute_on sum_fold_helper_subset] sum_fold_helper_set_to_list
  have "Finite_Set.fold (\<lambda>x::int. (+) (f x)) (0::real) {0::int..<int n} =
    fold (\<lambda>x::int. (+) (f x)) (remdups [0::int..int n-1]) (0::real)" by presburger
  then show "fold (\<lambda>i::int. (+) (f i)) [0::int..int n - (1::int)] (0::real) = Finite_Set.fold ((+) \<circ> f) (0::real) {0::int..<int n}" by(simp add:sum_fold_helper_remdups sum_fold_helper_lambda)
qed

lemma atLeastLessThanSucInt:
    "{m..<(n::int) + 1} = (if m \<le> n then insert n {m..<n} else {})"
by (auto simp add: atLeastLessThan_def)

lemma sum_int_nat_helper:
  assumes "n \<ge> 0"
  shows "sum f {0::int..<int n} + ((f (int n))::real) = sum f {0::int..<(1::int) + int n}"
  thm atLeastLessThanSucInt
proof -
  from assms Set_Interval.dense_linorder_class.infinite_Ico have fin: "finite {0..<int n}" by force
  from atLeastLessThanSucInt assms have "{0::int..<(1::int) + int n} =  insert (int n) {0..<int n}" by fastforce
  then have "sum f {0::int..<(1::int) + int n} =  sum f (insert (int n) {0..<int n})" by presburger
  then have "sum f {0::int..<(1::int) + int n} = f (int n) + sum f ({0::int..<int n})"
    using Groups_Big.comm_monoid_add_class.sum.insert_remove[OF fin] by simp
  then show ?thesis by linarith
qed

lemma sum_int_nat:
  shows "(\<Sum>i::nat = 0::nat..<n. f i) = (\<Sum>i::int = 0::int..<n. ((f i)::real))"
  apply(cases "n < 0")
  apply fastforce
  apply(induction n)
  by (auto simp add:sum_int_nat_helper)

lemma sum_fold:
  shows "fold (\<lambda>i::int. (+) ((f i)::real)) [0::int..int n-1] (0::real) =
    (\<Sum>i::nat = 0::nat..<n. f i)"
  using sum_int_nat sum_fold' by presburger

lemma real_vec_mul_scalar_product:
  assumes "dim_vec as = dim_vec bs"
  shows "real_vec_mul as bs = as \<bullet> bs"
  thm real_vec_mul_def
  using assms apply (simp add:real_vec_mul_def scalar_prod_def sum_int_nat)
  using sum_fold[where n="dim_vec bs" and f="\<lambda>i. (as $ nat i * bs $ nat i)"] 
  by simp
  
find_theorems "(fold ?f ?xs ?x) = foldl ?f ?x ?xs"
find_theorems "foldl"
thm foldl_conv_foldr
thm foldl_conv_fold

lemma vec_mul_fold_foldr_helper:
  "(\<lambda> i s.  ((ars::real vec) $ nat i) * (brs $ nat i) + s) y \<circ> (\<lambda> i s.  (ars $ nat i) * (brs $ nat i) + s) x = (\<lambda> i s.  (ars $ nat i) * (brs $ nat i) + s) x \<circ> (\<lambda> i s.  (ars $ nat i) * (brs $ nat i) + s) y"
  by auto
  

lemma vec_mul_fold_foldr:
  "fold (\<lambda> i s.  ((ars::real vec) $ nat i) * (brs $ nat i) + s) is = foldr (\<lambda> i s.  (ars $ nat i) * (brs $ nat i) + s) is"
  thm vec_mul_fold_foldr_helper[where ars=ars and brs=brs]
proof -
  from foldr_fold[OF vec_mul_fold_foldr_helper[where ars=ars and brs=brs]] have "foldr (\<lambda>y. (+) ((ars::real vec) $ nat (y) * (brs::real vec) $ nat (y))) is =
  fold (\<lambda>y. (+) (ars $ nat (y) * brs $ nat (y))) is " by fast
  then show ?thesis by presburger
qed
  

lemma vector_multiplication_helper:
  assumes a_rel: "vec_all2 (\<lambda>f r. ulp_accuracy r (f::('e,'f) float) a_accuracy) (afs::('e, 'f) float vec) ars"
      and b_rel: "vec_all2 (\<lambda>f r. ulp_accuracy r (f::('e,'f) float) b_accuracy) (bfs::('e, 'f) float vec) brs"
      and signs: "vec_all (\<lambda>f. IEEE.sign f = 0) afs \<and> vec_all (\<lambda>f. IEEE.sign f = 0) bfs"
      and probs: "vec_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) ars \<and> vec_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) brs"
      and "1 < LENGTH('e)"
      and "a_accuracy \<le> (2::real) ^ LENGTH('f)"
      and "b_accuracy \<le> (2::real) ^ LENGTH('f)"
      and "1 < LENGTH('f)"
      and "is_finite (fold (\<lambda> i s. fmul_add To_nearest (afs $ nat i) (bfs $ nat i) s) is 0)"
      and "dim_vec afs = dim_vec bfs"
      and "\<forall>i\<in>set (is::int list). (0 \<le> i \<and> i < dim_vec afs)"
shows "ulp_accuracy (fold (\<lambda> i s.  (ars $ nat i) * (brs $ nat i) + s) is 0) (fold (\<lambda> i s. fmul_add To_nearest (afs $ nat i) (bfs $ nat i) s) is 0) ((2*a_accuracy + 2*b_accuracy + 0.5)*(length is)) \<and> IEEE.sign (fold (\<lambda> i s. fmul_add To_nearest (afs $ nat i) (bfs $ nat i) s) is 0) = 0 "
  
  (*proof (induction "is" arbitrary:afs bfs ars brs)*)
  (*using assms proof (induction "is" rule: rev_induct)*)
  using assms proof (induction "rev is" arbitrary: "is")
    case Nil
    have reals_0: "(fold (\<lambda>i::int. (+) (ars $ nat i * brs $ nat i)) (map int []) (0::real)) = 0" by(simp add:)
    moreover from Nil have floats_0: "(fold (\<lambda>i::int. fmul_add To_nearest (afs $ nat i) (bfs $ nat i)) (map int []) (0::('e, 'f) IEEE.float)) = 0" by(simp add:)
    
    have "(((2::real) * a_accuracy + (2::real) * b_accuracy + (5::real) / (10::real)) * (length [])) = 0" by simp
    with ulp_accuracy_zero reals_0 floats_0 Nil have acc: "ulp_accuracy (fold (\<lambda>i::int. (+) (ars $ nat i * brs $ nat i)) (map int []) (0::real)) (fold (\<lambda>i::int. fmul_add To_nearest (afs $ nat i) (bfs $ nat i)) (map int []) (0::('e, 'f) IEEE.float))
     (((2::real) * a_accuracy + (2::real) * b_accuracy + (5::real) / (10::real)) * (length []))" by force
    with floats_0 zero_simps(1) Nil show ?case by fastforce
  next
    case (Cons a is')
    then have "set(is') \<subseteq> set(rev is)"
      by (metis set_subset_Cons)
    then have "set(rev (is')) \<subseteq> set(is)" by auto
    with Cons have subset_precondition: "\<forall>i\<in>set (rev (is')). (0) \<le> i \<and> i < dim_vec (afs::('e, 'f) IEEE.float vec)" by auto

    from Cons have "is = rev ((a) # (is'))" by force
    then have new_is_def: "is = (rev is') @ [a]" by auto

    from fold_append new_is_def have folded_floats: "(fold (\<lambda> i s. fmul_add To_nearest (afs $ nat i) (bfs $ nat i) s) (is) 0) = fmul_add To_nearest (afs $ nat a) (bfs $ nat a) (fold (\<lambda> i s. fmul_add To_nearest (afs $ nat i) (bfs $ nat i) s) (rev is') 0)" by simp
    with three_mul_added_numbers(4) Cons.prems(9) have fin_c: "is_finite (fold (\<lambda> i s. fmul_add To_nearest (afs $ nat i) (bfs $ nat i) s) (rev is') 0)" by auto
    from fold_append new_is_def have folded_reals: "(fold (\<lambda> i s.  (ars $ nat i) * (brs $ nat i) + s) is 0) =  (ars $ nat a) * (brs $ nat a) + (fold (\<lambda> i s.  (ars $ nat i) * (brs $ nat i) + s) (rev is') 0)" by simp

    from folded_floats Cons.prems(9) have fin_total: "is_finite
   (fmul_add To_nearest (afs $ nat a) (bfs $ nat a) (fold (\<lambda> i s. fmul_add To_nearest (afs $ nat i) (bfs $ nat i) s) (rev is') 0))" by presburger
      
    have rev_rev: "(is') = rev (rev (is'))" by simp
    then have precondition: "ulp_accuracy (fold (\<lambda>i. (+) ((ars::real vec) $ nat i * (brs::real vec) $ nat i)) (rev is') (0::real))
     (fold (\<lambda>i::int. fmul_add To_nearest ((afs::('e, 'f) IEEE.float vec) $ nat i) ((bfs::('e, 'f) IEEE.float vec) $ nat i))
       (rev is') (0::('e, 'f) IEEE.float))
     (((2::real) * (a_accuracy::real) + (2::real) * (b_accuracy::real) + (5::real) / (10::real)) * real (length (rev is'))) \<and>
    IEEE.sign (fold (\<lambda>i::int. fmul_add To_nearest (afs $ nat i) (bfs $ nat i)) (rev is') (0::('e, 'f) IEEE.float)) =
    (0::nat)" using Cons(1)[OF rev_rev Cons.prems(1) Cons.prems(2) Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) Cons.prems(7) Cons.prems(8) fin_c Cons.prems(10) subset_precondition] by blast
    

    from Cons(2) have "a\<in>set(rev is)"
      by (metis list.set_intros(1))
    with Cons.prems(11) have a_l: "nat a < dim_vec afs" by fastforce
    with vec_all2_dim Cons.prems(1) have a_l2: "nat a < dim_vec ars" by metis
    from a_l vec_all2_dim Cons.prems(2) Cons.prems(10) have b_l: "nat a < dim_vec brs" by metis
    
    have u_a1: "ulp_accuracy (ars $ nat a) (afs $ nat a) (a_accuracy::real)" using vec_all2_map[OF Cons.prems(1) a_l] by blast 
    have u_a2: "ulp_accuracy (brs $ nat a) (bfs $ nat a) (b_accuracy::real)" using vec_all2_map[OF Cons.prems(2)] a_l Cons.prems(10) by simp
    have u_a3: "ulp_accuracy (fold (\<lambda>i. (+) ((ars::real vec) $ nat i * (brs::real vec) $ nat i)) (rev is') (0::real)) (fold (\<lambda>i. fmul_add To_nearest ((afs::('e, 'f) IEEE.float vec) $ nat i) ((bfs::('e, 'f) IEEE.float vec) $ nat i))
     (rev is') (0::('e, 'f) IEEE.float)) (((2::real) * (a_accuracy::real) + (2::real) * (b_accuracy::real) + (5::real) / (10::real)) * real (length (rev is')))" using precondition by force
    have s1: "IEEE.sign ((afs::('e, 'f) IEEE.float vec) $ nat a) = (0)" using Cons.prems(3)
      by (simp add: a_l vec_all_def)
    have s2: "IEEE.sign ((bfs::('e, 'f) IEEE.float vec) $ nat a) = (0::nat)" using Cons.prems(3) Cons.prems(10) 
      apply (simp add: a_l vec_all_def)
      using a_l vec_setI by auto
    have s3: "IEEE.sign ((fold (\<lambda>i. fmul_add To_nearest ((afs::('e, 'f) IEEE.float vec) $ nat i) ((bfs::('e, 'f) IEEE.float vec) $ nat i))
     (rev is') (0::('e, 'f) IEEE.float))) = (0::nat)"  using precondition by force
    have r1: "(0::real) \<le> (ars::real vec) $ nat a" using Cons.prems(4) by (simp add: a_l2 vec_all_def)
    have r2: "ars $ nat a \<le> (1::real)" using Cons.prems(4) by (simp add: a_l2 vec_all_def)
    have r3: "(0::real) \<le> (brs::real vec) $ nat a" using Cons.prems(4) by (simp add: b_l vec_all_def)
    have r4: "brs $ nat a \<le> (1::real)" using Cons.prems(4) by (simp add: b_l vec_all_def)
    
    from  multiplication_addition_error_propagation_ulp_accuracy2[OF u_a1 u_a2 u_a3 Cons.prems(5) Cons.prems(8) s1 s2 s3 fin_total Cons.prems(6) Cons.prems(7) r1 r2 r3 r4] have
      "ulp_accuracy
 ((ars::real vec) $ nat (a) * (brs::real vec) $ nat a +
  fold (\<lambda>i::int. (+) (ars $ nat i * brs $ nat i)) (rev (is')) (0::real))
 (fmul_add To_nearest ((afs::('e, 'f) IEEE.float vec) $ nat a) ((bfs::('e, 'f) IEEE.float vec) $ nat a)
   (fold (\<lambda>i::int. fmul_add To_nearest (afs $ nat i) (bfs $ nat i)) (rev is') (0::('e, 'f) IEEE.float)))
 ((2::real) * (a_accuracy::real) + (2::real) * (b_accuracy::real) +
  ((2::real) * a_accuracy + (2::real) * b_accuracy + (5::real) / (10::real)) * real (length (rev is')) +
  (5::real) / (10::real))" by blast
    then have "ulp_accuracy
 (fold (\<lambda>i. (+) ((ars::real vec) $ nat i * (brs::real vec) $ nat i)) is (0::real))
 (fold (\<lambda>i. fmul_add To_nearest ((afs::('e, 'f) IEEE.float vec) $ nat i) ((bfs::('e, 'f) IEEE.float vec) $ nat i))
 is (0::('e, 'f) IEEE.float))
 (((2::real) * a_accuracy + (2::real) * b_accuracy + (5::real) / (10::real)) * real (1 + length (rev is')))" apply(simp add:folded_floats folded_reals) by argo
    with new_is_def have "ulp_accuracy (fold (\<lambda>i. (+) (ars $ nat i * brs $ nat i)) is (0::real))
   (fold (\<lambda>i::int. fmul_add To_nearest (afs $ nat i) (bfs $ nat i)) is (0::('e, 'f) IEEE.float))
   (((2::real) * a_accuracy + (2::real) * b_accuracy + (5::real) / (10::real)) * real (length is))" by auto
    with three_mul_added_numbers_positive[OF fin_total s1 s2 s3] show ?case by(simp add:folded_floats)
  qed


lemma vector_multiplication_real_vec_mul:
  assumes a_rel: "vec_all2 (\<lambda>f r. ulp_accuracy r (f::('e,'f) float) a_accuracy) (afs::('e, 'f) float vec) ars"
      and b_rel: "vec_all2 (\<lambda>f r. ulp_accuracy r (f::('e,'f) float) b_accuracy) (bfs::('e, 'f) float vec) brs"
      and signs: "vec_all (\<lambda>f. IEEE.sign f = 0) afs \<and> vec_all (\<lambda>f. IEEE.sign f = 0) bfs"
      and probs: "vec_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) ars \<and> vec_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) brs"
      and "1 < LENGTH('e)"
      and "a_accuracy \<le> (2::real) ^ LENGTH('f)"
      and "b_accuracy \<le> (2::real) ^ LENGTH('f)"
      and "1 < LENGTH('f)"
      and "is_finite (float_vec_mul afs bfs)"
      and "dim_vec afs = dim_vec bfs"
shows "ulp_accuracy (real_vec_mul ars brs) (float_vec_mul afs bfs) ((2*a_accuracy + 2*b_accuracy + 0.5)*dim_vec afs) \<and> IEEE.sign (float_vec_mul afs bfs) = 0 "
  apply(simp add:real_vec_mul_def float_vec_mul_def)
proof -
  have s1: "is_finite
 (fold (\<lambda>i::int. fmul_add To_nearest ((afs::('e, 'f) IEEE.float vec) $ nat i) ((bfs::('e, 'f) IEEE.float vec) $ nat i))
   [0::int..int (dim_vec afs) - (1::int)] (0::('e, 'f) IEEE.float))" using assms(9) by(simp add: float_vec_mul_def)
  have s2: "\<forall>i::int\<in>set [0::int..int (dim_vec (afs::('e, 'f) IEEE.float vec)) - (1::int)]. (0::int) \<le> i \<and> i < int (dim_vec afs)" by force
  from vector_multiplication_helper[where ?is="[0::int..int (dim_vec afs) - (1::int)]", OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) s1 assms(10) s2] show "ulp_accuracy (fold (\<lambda>i::int. (+) (ars $ nat i * brs $ nat i)) [0::int..int (dim_vec ars) - (1::int)] (0::real))
     (fold (\<lambda>i::int. fmul_add To_nearest (afs $ nat i) (bfs $ nat i)) [0::int..int (dim_vec afs) - (1::int)]
       (0::('e, 'f) IEEE.float))
     (((2::real) * a_accuracy + (2::real) * b_accuracy + (1::real) / (2::real)) * real (dim_vec afs)) \<and>
    IEEE.sign
     (fold (\<lambda>i::int. fmul_add To_nearest (afs $ nat i) (bfs $ nat i)) [0::int..int (dim_vec afs) - (1::int)]
       (0::('e, 'f) IEEE.float)) =
    (0::nat)"
    using a_rel vec_all2_dim by fastforce
qed

lemma vector_multiplication:
  assumes a_rel: "vec_all2 (\<lambda>f r. ulp_accuracy r (f::('e,'f) float) a_accuracy) (afs::('e, 'f) float vec) ars"
      and b_rel: "vec_all2 (\<lambda>f r. ulp_accuracy r (f::('e,'f) float) b_accuracy) (bfs::('e, 'f) float vec) brs"
      and signs: "vec_all (\<lambda>f. IEEE.sign f = 0) afs \<and> vec_all (\<lambda>f. IEEE.sign f = 0) bfs"
      and probs: "vec_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) ars \<and> vec_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) brs"
      and "1 < LENGTH('e)"
      and "a_accuracy \<le> (2::real) ^ LENGTH('f)"
      and "b_accuracy \<le> (2::real) ^ LENGTH('f)"
      and "1 < LENGTH('f)"
      and "is_finite (float_vec_mul afs bfs)"
      and "dim_vec afs = dim_vec bfs"
shows "ulp_accuracy (ars \<bullet> brs) (float_vec_mul afs bfs) ((2*a_accuracy + 2*b_accuracy + 0.5)*dim_vec afs) \<and> IEEE.sign (float_vec_mul afs bfs) = 0 "
proof-
  from assms(10) a_rel b_rel vec_all2_dim have "dim_vec ars = dim_vec brs" by metis
  then have "(ulp_accuracy (ars \<bullet> brs) (float_vec_mul afs bfs) ((2*a_accuracy + 2*b_accuracy + 0.5)*dim_vec afs) \<and> IEEE.sign (float_vec_mul afs bfs) = 0) =
             (ulp_accuracy (real_vec_mul ars brs) (float_vec_mul afs bfs) ((2*a_accuracy + 2*b_accuracy + 0.5)*dim_vec afs) \<and> IEEE.sign (float_vec_mul afs bfs) = 0 )" by(simp add:real_vec_mul_scalar_product)
  then show ?thesis using assms vector_multiplication_real_vec_mul by blast
qed

(*
definition mult_mat_vec :: "'a :: semiring_0 mat \<Rightarrow> 'a vec \<Rightarrow> 'a vec" (infixl "*\<^sub>v" 70)
  where "A *\<^sub>v v \<equiv> vec (dim_row A) (\<lambda> i. row A i \<bullet> v)"
*)
definition float_mult_mat_vec :: "('e, 'f) float mat \<Rightarrow> ('e, 'f) float vec \<Rightarrow> ('e, 'f) float vec"
  where "float_mult_mat_vec A v \<equiv> vec (dim_row A) (\<lambda> i. float_vec_mul (row A i) v)"
(*
definition vec_all2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a vec \<Rightarrow> 'b vec \<Rightarrow> bool"
  where "vec_all2 f a b = list_all2 f (list_of_vec a) (list_of_vec b)"
*)

lemma matrix_multiplication_helper:
  assumes a_rel: "mat_all2 (\<lambda>f r. ulp_accuracy r (f::('e,'f) float) a_accuracy) (afs::('e, 'f) float mat) ars"
      and b_rel: "vec_all2 (\<lambda>f r. ulp_accuracy r (f::('e,'f) float) b_accuracy) (bfs::('e, 'f) float vec) brs"
      and signs: "mat_all (\<lambda>f. IEEE.sign f = 0) afs \<and> vec_all (\<lambda>f. IEEE.sign f = 0) bfs"
      and probs: "mat_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) ars \<and> vec_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) brs"
      and "1 < LENGTH('e)"
      and "a_accuracy \<le> (2::real) ^ LENGTH('f)"
      and "b_accuracy \<le> (2::real) ^ LENGTH('f)"
      and "1 < LENGTH('f)"
      and "vec_all (is_finite) (float_mult_mat_vec afs bfs)"
      and "dim_col afs = dim_vec bfs"
      and "(i::nat) < dim_vec (float_mult_mat_vec afs bfs)"
    shows "dim_vec (float_mult_mat_vec afs bfs) = dim_row ars \<and>
        ulp_accuracy ((ars *\<^sub>v brs) $ i) (float_mult_mat_vec afs bfs $ i)
         (((2::real) * a_accuracy + (2::real) * b_accuracy + (1::real) / (2::real)) * real (dim_vec bfs)) \<and>
     IEEE.sign (float_mult_mat_vec afs bfs $ i) = (0::nat)"
proof -
  have dim_afs: "dim_vec (float_mult_mat_vec afs bfs) = dim_row afs" by(simp add:float_mult_mat_vec_def)
  with a_rel have dim_ars: "dim_vec (float_mult_mat_vec afs bfs) = dim_row ars" by (simp add: mat_all2_def) 
  from assms(11) have single_mult_float: "(float_mult_mat_vec afs bfs $ i) = float_vec_mul (row afs i) bfs" by(simp add: float_mult_mat_vec_def)
  from assms(11) have single_mult_real: "(ars *\<^sub>v brs) $ i = (row ars i) \<bullet> brs"
    by (simp add: dim_ars)
  have dim_vec_fac: "real (dim_col afs) = real (dim_vec bfs)" using assms(10) by fastforce

  have "vec_all2 (\<lambda>(f::('e, 'f) IEEE.float) r::real. ulp_accuracy r f (a_accuracy::real)) (row afs i)
    (row ars i)" using mat_all2_vec_all2_row[OF assms(1)] assms(11) 
    by (simp add: float_mult_mat_vec_def)
  moreover have "vec_all2 (\<lambda>(f::('e, 'f) IEEE.float) r::real. ulp_accuracy r f (b_accuracy::real)) (bfs::('e, 'f) IEEE.float vec)
    (brs::real vec)" using assms(2) by blast
  moreover have "vec_all (\<lambda>f::('e, 'f) IEEE.float. IEEE.sign f = (0::nat)) (row afs i) \<and>
    vec_all (\<lambda>f::('e, 'f) IEEE.float. IEEE.sign f = (0::nat)) bfs" using assms(3) mat_all_vec_all_row assms(11) dim_afs by auto
  moreover have "vec_all (\<lambda>r::real. (0::real) \<le> r \<and> r \<le> (1::real)) (row ars i) \<and> vec_all (\<lambda>r::real. (0::real) \<le> r \<and> r \<le> (1::real)) brs" using assms(4) mat_all_vec_all_row assms(11) dim_ars by auto
  moreover have "(1::nat) < LENGTH('e)" using assms(5) by blast
  moreover have "a_accuracy \<le> (2::real) ^ LENGTH('f)" using assms(6) by blast
  moreover have "b_accuracy \<le> (2::real) ^ LENGTH('f)" using assms(7) by blast
  moreover have "(1::nat) < LENGTH('f)" using assms(8) by blast
  moreover have "is_finite (float_vec_mul (row afs i) bfs)" using assms(9) single_mult_float vec_all_def assms(11) by metis
  moreover have "dim_vec (row afs i) = dim_vec bfs" using assms(10) by auto 
  ultimately have "ulp_accuracy ((row ars i) \<bullet> brs) (float_vec_mul (row afs i) bfs)
     (((2::real) * a_accuracy + (2::real) * b_accuracy + (5::real) / (10::real)) * real (dim_vec (row afs i))) \<and>
    IEEE.sign (float_vec_mul (row afs i) bfs) = (0::nat)" using vector_multiplication by blast
  then show ?thesis apply(simp add: single_mult_float single_mult_real dim_vec_fac) using dim_ars by blast
qed


lemma matrix_multiplication:
  assumes a_rel: "mat_all2 (\<lambda>f r. ulp_accuracy r (f::('e,'f) float) a_accuracy) (afs::('e, 'f) float mat) ars"
      and b_rel: "vec_all2 (\<lambda>f r. ulp_accuracy r (f::('e,'f) float) b_accuracy) (bfs::('e, 'f) float vec) brs"
      and signs: "mat_all (\<lambda>f. IEEE.sign f = 0) afs \<and> vec_all (\<lambda>f. IEEE.sign f = 0) bfs"
      and probs: "mat_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) ars \<and> vec_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) brs"
      and "1 < LENGTH('e)"
      and "a_accuracy \<le> (2::real) ^ LENGTH('f)"
      and "b_accuracy \<le> (2::real) ^ LENGTH('f)"
      and "1 < LENGTH('f)"
      and "vec_all (is_finite) (float_mult_mat_vec afs bfs)"
      and "dim_col afs = dim_vec bfs"
    shows "vec_all2 (\<lambda>f r. ulp_accuracy r f ((2*a_accuracy + 2*b_accuracy + 0.5)*dim_vec bfs)) (float_mult_mat_vec afs bfs) (mult_mat_vec ars brs) \<and> vec_all (\<lambda>f. IEEE.sign f = 0) (float_mult_mat_vec afs bfs)"
  apply(simp add: vec_all2_def vec_all_def)
proof -
  from a_rel have step1: "dim_vec (float_mult_mat_vec afs bfs) = dim_row ars" by(simp add:float_mult_mat_vec_def mat_all2_def)
  then show "dim_vec (float_mult_mat_vec afs bfs) = dim_row ars \<and>
    (\<forall>i<dim_vec (float_mult_mat_vec afs bfs).
        ulp_accuracy ((ars *\<^sub>v brs) $ i) (float_mult_mat_vec afs bfs $ i)
         (((2::real) * a_accuracy + (2::real) * b_accuracy + (1::real) / (2::real)) * real (dim_vec bfs))) \<and>
    (\<forall>i<dim_vec (float_mult_mat_vec afs bfs). IEEE.sign (float_mult_mat_vec afs bfs $ i) = (0::nat))" 
    using matrix_multiplication_helper[OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) assms(10)] by blast
qed

(*
and "is_finite (fold (\<lambda> i s. fmul_add To_nearest (afs $ nat i) (bfs $ nat i) s) is 0)"
      and "dim_vec afs = dim_vec bfs"
      and "\<forall>i\<in>set (is::int list). (0 \<le> i \<and> i < dim_vec afs)"
shows "ulp_accuracy (fold (\<lambda> i s.  (ars $ nat i) * (brs $ nat i) + s) is 0) (fold (\<lambda> i s. fmul_add To_nearest (afs $ nat i) (bfs $ nat i) s) is 0) ((2*a_accuracy + 2*b_accuracy + 0.5)*(length is))
*)

lemma vec_mul_added_numbers_helper:
    assumes 
      "is_finite (fold (\<lambda> i s. fmul_add To_nearest (afs $ nat i) (bfs $ nat i) s) is 0)"
      and "dim_vec afs = dim_vec bfs"
      and "\<forall>i\<in>set (is::int list). (0 \<le> i \<and> i < dim_vec afs)"
    shows "\<forall>i\<in>set (is).is_finite (afs $ nat i)" 
     and "\<forall>i\<in>set (is). is_finite (bfs $ nat i)"
using assms proof (induction "is" rule: rev_induct)
  case Nil
  {
    case 1
    then show ?case by force
  next
    case 2
    then show ?case by force
  }
next
  case (snoc x xs)
  {
    case 1
    from fold_append have folded_floats: "(fold (\<lambda> i s. fmul_add To_nearest (afs $ nat i) (bfs $ nat i) s) ((xs @ [x])) 0) = fmul_add To_nearest (afs $ nat x) (bfs $ nat x) (fold (\<lambda> i s. fmul_add To_nearest (afs $ nat i) (bfs $ nat i) s) (xs) 0)" by simp
    with 1 three_mul_added_numbers(2) have fin_a: "is_finite (afs $ nat x)" by auto
    from folded_floats 1(1) three_mul_added_numbers(4) have fin_c: "is_finite
 (fold (\<lambda>i. fmul_add To_nearest ((afs::('a, 'b) IEEE.float vec) $ nat i) ((bfs::('a, 'b) IEEE.float vec) $ nat i))
   (xs) (0::('a, 'b) IEEE.float))" by auto
    from 1(3) have dims: "\<forall>i\<in>set (xs). 0 \<le> i \<and> i < dim_vec (afs::('a, 'b) IEEE.float vec)" by simp
    moreover from snoc(1)[OF fin_c 1(2) dims] have "\<forall>i\<in>set xs. is_finite (afs $ nat i)" by linarith
    with fin_a show ?case by simp
  next
    case 2
    from fold_append have folded_floats: "(fold (\<lambda> i s. fmul_add To_nearest (afs $ nat i) (bfs $ nat i) s) ((xs @ [x])) 0) = fmul_add To_nearest (afs $ nat x) (bfs $ nat x) (fold (\<lambda> i s. fmul_add To_nearest (afs $ nat i) (bfs $ nat i) s) (xs) 0)" by simp
    with 2 three_mul_added_numbers(3) have fin_a: "is_finite (bfs $ nat x)" by auto
    from folded_floats 2(1) three_mul_added_numbers(4) have fin_c: "is_finite
 (fold (\<lambda>i::int. fmul_add To_nearest ((afs::('a, 'b) IEEE.float vec) $ nat i) ((bfs::('a, 'b) IEEE.float vec) $ nat i))
   ((xs)) (0::('a, 'b) IEEE.float))" by auto
    from 2(3) have dims: "\<forall>i\<in>set (xs). (0) \<le> i \<and> i < dim_vec (afs::('a, 'b) IEEE.float vec)" by simp
    moreover from snoc(2)[OF fin_c 2(2) dims] have "\<forall>i\<in>set xs. is_finite (bfs $ nat i)" by linarith
    with fin_a show ?case by simp
  }
qed

lemma vec_mul_added_numbers:
    assumes 
      "is_finite (float_vec_mul afs bfs)"
      and "dim_vec afs = dim_vec bfs"
    shows "vec_all (is_finite) afs" 
     and "vec_all (is_finite) bfs"
   using assms apply(simp_all add:vec_all_def float_vec_mul_def)
subgoal proof -
  have s1: "is_finite
 (fold (\<lambda>i::int. fmul_add To_nearest ((afs) $ nat i) ((bfs) $ nat i))
   [0::int..int (dim_vec afs) - (1::int)] 0)" using assms by(simp add: float_vec_mul_def)
  have s2: "\<forall>i::int\<in>set [0::int..int (dim_vec afs) - (1::int)]. (0::int) \<le> i \<and> i < int (dim_vec afs)" by force
  from vec_mul_added_numbers_helper(1)[OF s1 assms(2) s2] have s3: "\<forall>i::int\<in>set [0::int..int (dim_vec bfs) - (1::int)]. is_finite (afs $ nat i)" by(simp add:assms(2))
  then show "\<forall>i<dim_vec bfs. is_finite (afs $ i)" apply(simp add:all_nat_less_eq)
    by (metis s3 assms(2) atLeastLessThan_iff atLeastLessThan_upto int_eq_iff nat_int_comparison(2))
qed
subgoal proof -
  have s1: "is_finite
 (fold (\<lambda>i::int. fmul_add To_nearest ((afs) $ nat i) ((bfs) $ nat i))
   [0::int..int (dim_vec afs) - (1::int)] 0)" using assms by(simp add: float_vec_mul_def)
  have s2: "\<forall>i::int\<in>set [0::int..int (dim_vec afs) - (1::int)]. (0::int) \<le> i \<and> i < int (dim_vec afs)" by force
  from vec_mul_added_numbers_helper(2)[OF s1 assms(2) s2] have s3: "\<forall>i::int\<in>set [0::int..int (dim_vec bfs) - (1::int)]. is_finite (bfs $ nat i)" by(simp add:assms(2))
  then show "\<forall>i<dim_vec bfs. is_finite (bfs $ i)" apply(simp add:all_nat_less_eq)
    by (metis s3 assms(2) atLeastLessThan_iff atLeastLessThan_upto int_eq_iff nat_int_comparison(2))
qed
  done

lemma matrix_mul_added_numbers1:
    assumes 
      "vec_all (is_finite) (float_mult_mat_vec afs bfs)"
      and "dim_col afs = dim_vec bfs"
      and "1 \<le> dim_row afs"
    shows "mat_all (is_finite) afs" 
     and "vec_all (is_finite) bfs"
  using assms  apply(simp add:mat_all_def vec_all_def float_mult_mat_vec_def)
   apply (smt (z3) index_row(1) index_row(2) vec_all_def vec_mul_added_numbers(1))
  subgoal proof-
    from assms have "is_finite (float_vec_mul (row afs 0) bfs)"  by(simp add:vec_all_def float_mult_mat_vec_def) 
    with vec_mul_added_numbers assms(2) show ?thesis by force
  qed
  done

lemma matrix_mul_added_numbers2:
    assumes 
      "vec_all (is_finite) (float_mult_mat_vec afs bfs)"
      and "dim_col afs = dim_vec bfs"
      and "dim_col afs = dim_row afs"
    shows "mat_all (is_finite) afs" 
     and "vec_all (is_finite) bfs"
  using assms  apply(simp add:mat_all_def vec_all_def float_mult_mat_vec_def)
   apply (smt (z3) index_row(1) index_row(2) vec_all_def vec_mul_added_numbers(1))
  apply(cases "dim_vec bfs = 0")
  using vec_all_def apply fastforce
  using assms matrix_mul_added_numbers1 by fastforce

lemma matrix_pow_mul_added_numbers_b:
    assumes 
      "vec_all (is_finite) (f_mat_vec_pow (float_mult_mat_vec) afs bfs k)"
      and "dim_col afs = dim_vec bfs"
      and "dim_col afs = dim_row afs"
    shows "vec_all (is_finite) bfs"
  using assms proof(induction k arbitrary:bfs)
   case 0
   then show ?case by fastforce
 next
   case (Suc k)
   have "f_mat_vec_pow float_mult_mat_vec afs bfs (Suc k) = f_mat_vec_pow float_mult_mat_vec afs (float_mult_mat_vec afs bfs) k" by simp
   with Suc(1)[where bfs="float_mult_mat_vec afs bfs"] float_mult_mat_vec_def have "vec_all is_finite (float_mult_mat_vec afs bfs)"
     by (metis Suc.prems(1) assms(3) dim_vec)
   with matrix_mul_added_numbers2 show ?case
     using Suc.prems(2) assms(3) by blast
 qed

lemma matrix_pow_mul_added_numbers_a':
    assumes 
      "vec_all (is_finite) (f_mat_vec_pow (float_mult_mat_vec) afs bfs (k+1))"
      and "dim_col afs = dim_vec bfs"
      and "dim_col afs = dim_row afs"
    shows "mat_all (is_finite) afs" 
  using assms proof(induction k arbitrary:bfs)
  case 0
  then show ?case 
    apply simp
    using matrix_mul_added_numbers2(1) by metis
next
  case (Suc k)
  with float_mult_mat_vec_def show ?case
    by (metis Suc_eq_plus1 dim_vec f_mat_vec_pow.simps(2))
qed

lemma matrix_pow_mul_added_numbers_a:
    assumes 
      "vec_all (is_finite) (f_mat_vec_pow (float_mult_mat_vec) afs bfs k)"
      and "dim_col afs = dim_vec bfs"
      and "dim_col afs = dim_row afs"
      and "1 \<le> k"
    shows "mat_all (is_finite) afs" 
  using matrix_pow_mul_added_numbers_a' assms
  by (metis add.commute less_eqE)

lemmas matrix_pow_mul_added_numbers=
  matrix_pow_mul_added_numbers_a
  matrix_pow_mul_added_numbers_b

lemma matrix_multiplication_iteratively_dimension:
  assumes "dim_col afs = dim_vec bfs"
      and "dim_col afs = dim_row afs"
    shows "dim_vec (((float_mult_mat_vec afs)^^k) bfs) = dim_vec bfs"
  using assms apply(induction k)
  by (auto simp add: float_mult_mat_vec_def)

lemma sum_powers_0:
  assumes "1<x"
  shows "(\<Sum>i=0..k. (x::real)^i) = (x^(k+1) - 1)/(x-1)"
  proof(induction k)
    case 0
    with assms show ?case by simp
  next
    case (Suc k)
    from assms have "(x * x ^ k - (1::real)) / (x - (1::real)) + x * x ^ k = (x * x ^ k - (1::real)) / (x - (1::real)) + x * x ^ k* (x - (1::real))/ (x - (1::real))" by fastforce
    then have "(x * x ^ k - (1::real)) / (x - (1::real)) + x * x ^ k =  (x* x * x ^ k -(1::real))/ (x - (1::real))" by argo
    then show ?case
      by (auto simp add: Suc)
  qed

lemma sum_powers_1:
  assumes "1<x"
  shows "(\<Sum>i=1..k. (x::real)^i) = (x^(k+1) - 1)/(x-1) - 1"
proof (induction k)
  case 0
  with assms show ?case by simp
next
  case (Suc k)
  from assms have "(x * x ^ k - (1::real)) / (x - (1::real)) + x * x ^ k = (x * x ^ k - (1::real)) / (x - (1::real)) + x * x ^ k* (x - (1::real))/ (x - (1::real))" by fastforce
    then have "(x * x ^ k - (1::real)) / (x - (1::real)) + x * x ^ k =  (x* x * x ^ k -(1::real))/ (x - (1::real))" by argo
    then show ?case
      using Suc by auto
  qed

lemma sum_powers_matrix_multiplication_error':
  shows "(\<Sum>i=0..k. (2*(x::nat))^i) = ((2*x)^(k+1) - 1)/(2*x-1)"
  apply(cases "x=0")
  apply(induction k)
    apply auto
subgoal proof -
  have "(0::nat) < x \<Longrightarrow> 1 < 2*x" by linarith
  with sum_powers_0[where x="2*x"] show ?thesis by fastforce
qed done

lemma sum_powers_matrix_multiplication_error:
  shows "(\<Sum>i=1..k. (2*(x::nat))^i) = ((2*x)^(k+1) - 1)/(2*x-1) - 1"
  apply(cases "x=0")
  apply(induction k)
    apply auto
subgoal proof -
  have "(0::nat) < x \<Longrightarrow> 1 < 2*x" by linarith
  with sum_powers_1[where x="2*x"] show ?thesis by fastforce
qed done

lemma matrix_multiplication_iteratively:
  assumes a_rel: "mat_all2 (\<lambda>f r. ulp_accuracy r (f::('e,'f) float) 0) (afs::('e, 'f) float mat) ars"
      and b_rel: "vec_all2 (\<lambda>f r. ulp_accuracy r (f::('e,'f) float) 0) (bfs::('e, 'f) float vec) brs"
      and signs: "mat_all (\<lambda>f. IEEE.sign f = 0) afs \<and> vec_all (\<lambda>f. IEEE.sign f = 0) bfs"
      and probs: "mat_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) ars \<and> vec_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) brs"
      and "1 < LENGTH('e)"
      and "(\<Sum>i=1..k. (2*dim_vec bfs)^i)/2 \<le> (2::real) ^ LENGTH('f)"
      and "1 < LENGTH('f)"
      and "vec_all (is_finite) (((float_mult_mat_vec afs)^^k) bfs)"
      and "dim_col afs = dim_vec bfs"
      and "dim_col afs = dim_row afs"
      and "mat_all_col (\<lambda>v::real vec. sum (($) v) {0::nat..<dim_vec v} = (1::real)) (ars::real mat)" 
      and "sum (($) (brs::real vec)) {0::nat..<dim_vec brs} = (1::real)"
    shows "vec_all2 (\<lambda>f r. ulp_accuracy r f ((\<Sum>i=1..k. (2*dim_vec bfs)^i)/4)) (((float_mult_mat_vec afs)^^k) bfs)  (((mult_mat_vec ars)^^k) brs) \<and> vec_all (\<lambda>f. IEEE.sign f = 0)  (((float_mult_mat_vec afs)^^k) bfs)"
  using assms proof(induction k)
    case 0
    then show ?case by auto
  next
    case (Suc k)
    have "real (sum ((^) ((2::nat) * dim_vec bfs)) {1::nat..k::nat}) / (4::real) \<le> real (sum ((^) ((2::nat) * dim_vec bfs)) {1::nat..Suc k}) / (4::real)" by fastforce
    with Suc.prems(6) have new_6:"real (sum ((^) ((2::nat) * dim_vec (bfs::('e, 'f) IEEE.float vec))) {1::nat..(k::nat)}) / (2::real)
  \<le> (2::real) ^ LENGTH('f) " by linarith
    from Suc.prems(8) have tmp_8_1: "vec_all is_finite (float_mult_mat_vec afs ((float_mult_mat_vec afs ^^ k) bfs))" by auto
    from matrix_multiplication_iteratively_dimension Suc.prems(9) Suc.prems(10) have tmp_8_2: "dim_col (afs::('e, 'f) IEEE.float mat) = dim_vec ((float_mult_mat_vec afs ^^ (k::nat)) (bfs::('e, 'f) IEEE.float vec))" by metis
    from matrix_mul_added_numbers2(2)[OF tmp_8_1 tmp_8_2 Suc.prems(10)] have new_8: "vec_all is_finite ((float_mult_mat_vec (afs::('e, 'f) IEEE.float mat) ^^ (k::nat)) (bfs::('e, 'f) IEEE.float vec))" by simp
    thm Suc.IH[OF Suc.prems(1) Suc.prems(2) Suc.prems(3) Suc.prems(4) Suc.prems(5) new_6 Suc.prems(7) new_8 Suc.prems(9) Suc.prems(10)]
    have "real (sum ((^) ((2::nat) * dim_vec bfs)) {1::nat..k::nat}) / (4::real) \<le> real (sum ((^) ((2::nat) * dim_vec bfs)) {1::nat..Suc k}) / (4::real)" by fastforce
    with Suc.prems(6) have new_6_2:"real (sum ((^) ((2::nat) * dim_vec (bfs::('e, 'f) IEEE.float vec))) {1::nat..(k::nat)}) / (4::real)
  \<le> (2::real) ^ LENGTH('f) " by linarith
    from Suc.IH[OF Suc.prems(1) Suc.prems(2) Suc.prems(3) Suc.prems(4) Suc.prems(5) new_6 Suc.prems(7) new_8 Suc.prems(9) Suc.prems(10) Suc.prems(11) Suc.prems(12)] have actual_IH: "vec_all2
   (\<lambda>(f::('e, 'f) IEEE.float) r::real.
       ulp_accuracy r f (real (sum ((^) ((2::nat) * dim_vec (bfs::('e, 'f) IEEE.float vec))) {1::nat..k::nat}) / (4::real)))
   ((float_mult_mat_vec (afs::('e, 'f) IEEE.float mat) ^^ k) bfs) (((*\<^sub>v) (ars::real mat) ^^ k) (brs::real vec)) \<and>
  vec_all (\<lambda>f::('e, 'f) IEEE.float. IEEE.sign f = (0::nat)) (((float_mult_mat_vec afs)^^k) bfs)" by blast
    then have actual_IH_1: "vec_all2
   (\<lambda>(f::('e, 'f) IEEE.float) r::real.
       ulp_accuracy r f (real (sum ((^) ((2::nat) * dim_vec (bfs::('e, 'f) IEEE.float vec))) {1::nat..k::nat}) / (4::real)))
   ((float_mult_mat_vec (afs::('e, 'f) IEEE.float mat) ^^ k) bfs) (((*\<^sub>v) (ars::real mat) ^^ k) (brs::real vec))" by blast
    from  Suc.prems(3) actual_IH have signs_2: "mat_all (\<lambda>f::('e, 'f) IEEE.float. IEEE.sign f = (0::nat)) (afs::('e, 'f) IEEE.float mat) \<and>
  vec_all (\<lambda>f::('e, 'f) IEEE.float. IEEE.sign f = (0::nat))
   ((float_mult_mat_vec afs ^^ (k::nat)) (bfs::('e, 'f) IEEE.float vec))" by blast
    from Suc.prems(9) a_rel b_rel have dims1: "dim_col (ars::real mat) = dim_vec (brs::real vec)" by(simp add: mat_all2_def vec_all2_def)
    from Suc.prems(10) a_rel have dims2: "dim_col (ars) = dim_row (ars)" by(simp add: mat_all2_def)
    from  Suc.prems(4) iterative_matrix_multiplication_probabilities[OF Suc.prems(4) Suc.prems(11) Suc.prems(12) dims1 dims2] have probs_2: "mat_all (\<lambda>r::real. (0::real) \<le> r \<and> r \<le> (1::real)) (ars::real mat) \<and>
  vec_all (\<lambda>r::real. (0::real) \<le> r \<and> r \<le> (1::real)) (((*\<^sub>v) ars ^^ (k::nat)) (brs::real vec))" by blast
    have zero_le: "(0::real) \<le> (2::real) ^ LENGTH('f)" by auto

    have sum_rewrite':"(((\<Sum>x::nat = Suc (0::nat)..k. (2::real) ^ x * real (dim_vec bfs) ^ x) +
            (2::real) * (2::real) ^ k * (real (dim_vec bfs) * real (dim_vec bfs) ^ k)) /
           (2::real)) = (((\<Sum>x::nat = 1..Suc k. ((2::real) * real (dim_vec bfs)) ^ x)) /
           (2::real))" by fastforce
    thm Suc.prems
    thm Suc.prems(9)
    from sum_powers_matrix_multiplication_error
    have "((2::real) * (real (sum ((^) ((2::nat) * dim_vec bfs)) {1::nat..k::nat}) / (4::real)) +
          (5::real) / (10::real)) *
         real (dim_vec bfs) =
  ((2::real) * (((((2::real) * real (dim_vec bfs)) ^ (k + (1::nat)) - ( 1::real)) / ((2::real) * real (dim_vec bfs) - (1::real)) - (1::real))/ (4::real)) +
          (5::real) / (10::real))*
         real (dim_vec bfs)" by presburger
    then have "((2::real) * (real (sum ((^) ((2::nat) * dim_vec bfs)) {1::nat..k::nat}) / (4::real)) +
          (5::real) / (10::real)) *
         real (dim_vec bfs) =
  (((((2::real) * real (dim_vec bfs)) * ((2::real) * real (dim_vec bfs)) ^ (k + (1::nat)) - ((2::real) * real (dim_vec bfs))) / ((2::real) * real (dim_vec bfs) - (1::real)))/ (4::real))" by argo
    then have "((2::real) * (real (sum ((^) ((2::nat) * dim_vec bfs)) {1::nat..k::nat}) / (4::real)) +
          (5::real) / (10::real)) *
         real (dim_vec bfs) =
  (((((2::real) * real (dim_vec bfs)) ^ (k + (2::nat)) - ((2::real) * real (dim_vec bfs))) / ((2::real) * real (dim_vec bfs) - (1::real)))/ (4::real))" by force
    then have "((2::real) * (real (sum ((^) ((2::nat) * dim_vec bfs)) {1::nat..k::nat}) / (4::real)) +
          (5::real) / (10::real)) *
         real (dim_vec bfs) =
  (((((2::real) * real (dim_vec bfs)) ^ (k + (2::nat)) - ( 1::real)) / ((2::real) * real (dim_vec bfs) - (1::real)) - ((2::real) * real (dim_vec bfs) - (1::real))/ ((2::real) * real (dim_vec bfs) - (1::real)))/ (4::real))" by argo
    moreover have "((2::real) * real (dim_vec bfs) - (1::real))/ ((2::real) * real (dim_vec bfs) - (1::real)) = ( 1::real)" apply(induction "dim_vec bfs") by auto
    ultimately have "((2::real) * (real (sum ((^) ((2::nat) * dim_vec bfs)) {1::nat..k::nat}) / (4::real)) +
          (5::real) / (10::real)) *
         real (dim_vec bfs) =
  (((((2::real) * real (dim_vec bfs)) ^ (k + (2::nat)) - ( 1::real)) / ((2::real) * real (dim_vec bfs) - (1::real)) - ( 1::real))/ (4::real))" by presburger
    with sum_powers_matrix_multiplication_error have sum_rewrite: "((2::real) * (real (sum ((^) ((2::nat) * dim_vec bfs)) {1::nat..k::nat}) / (4::real)) +
          (5::real) / (10::real)) *
         real (dim_vec bfs) =
          real (sum ((^) ((2::nat) * dim_vec bfs)) {1::nat..Suc k}) / (4::real)"
      using Suc_eq_plus1 add_2_eq_Suc' by presburger
    moreover from matrix_multiplication[OF Suc.prems(1) actual_IH_1 signs_2 probs_2 Suc.prems(5) zero_le new_6_2 Suc.prems(7) tmp_8_1 tmp_8_2]
    have "vec_all2
   (\<lambda>(f::('e, 'f) IEEE.float) r::real.
       ulp_accuracy r f
        (((2::real) * (real (sum ((^) ((2::nat) * dim_vec bfs)) {1::nat..k::nat}) / (4::real)) +
          (5::real) / (10::real)) *
         real (dim_vec bfs)))
   ((float_mult_mat_vec afs ^^ Suc k) bfs) (((*\<^sub>v) ars ^^ Suc k) (brs::real vec)) \<and>
  vec_all (\<lambda>f::('e, 'f) IEEE.float. IEEE.sign f = (0::nat)) ((float_mult_mat_vec afs ^^ Suc k) bfs)" using tmp_8_2 Suc.prems(9) by auto
    ultimately show ?case by presburger
  qed

end