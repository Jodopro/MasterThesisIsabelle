theory Matrix_Extension
  imports "Jordan_Normal_Form.Matrix"
begin
definition vec_all2' :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a vec \<Rightarrow> 'b vec \<Rightarrow> bool"
  where "vec_all2' f a b = list_all2 f (list_of_vec a) (list_of_vec b)"

definition vec_all2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a vec \<Rightarrow> 'b vec \<Rightarrow> bool"
  where "vec_all2 f a b \<equiv> (dim_vec a = dim_vec b) \<and> (\<forall>(i::nat). i < dim_vec a \<longrightarrow> f (a $ i) (b $ i))"

lemma vec_all2'_dim:
  assumes "vec_all2' f a b"
  shows "dim_vec a = dim_vec b"
  using assms
  by (simp add: vec_all2'_def list_all2_conv_all_nth)

lemma vec_all2_dim:
  assumes "vec_all2 f a b"
  shows "dim_vec a = dim_vec b"
  using assms
  by (simp add: vec_all2_def)

lemma vec_all2'_map:
  assumes "vec_all2' f a b"
  and "i<dim_vec a"
  shows "f (a$i) (b$i)"
  using assms
  by (simp add: vec_all2'_def list_all2_conv_all_nth list_of_vec_index)

lemma vec_all2_map:
  assumes "vec_all2 f a b"
  and "i<dim_vec a"
  shows "f (a$i) (b$i)"
  using assms
  by (simp add: vec_all2_def)


definition mat_all2' :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> 'b mat \<Rightarrow> bool"
  where "mat_all2' f a b = list_all2 (\<lambda>la lb. list_all2 f la lb) (mat_to_list a) (mat_to_list b)"

definition mat_all2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> 'b mat \<Rightarrow> bool"
  where "mat_all2 f a b \<equiv> (dim_row a = dim_row b) \<and> (dim_col a = dim_col b) \<and> (\<forall>(i::nat) (j::nat). (i < dim_row a \<and> j < dim_col a) \<longrightarrow> f (a $$ (i, j)) (b $$ (i, j)))"

lemma mat_all2_ij:
  assumes "mat_all2 f a b"
  and "i < dim_row a"
  and "j < dim_col a"
shows "f (a $$ (i, j)) (b $$ (i, j))"
  using assms by(simp add:mat_all2_def)

lemma mat_all2_vec_all2_row:
  assumes "mat_all2 f a b"
  and "i < dim_row a"
shows "vec_all2 f (row a i) (row b i)"
  using assms by(simp add:vec_all2_def mat_all2_def)

lemma mat_all2_vec_all2_col:
  assumes "mat_all2 f a b"
  and "i < dim_col a"
shows "vec_all2 f (col a i) (col b i)"
  using assms by(simp add:vec_all2_def mat_all2_def)

definition mat_all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> bool"
  where "mat_all f a  \<equiv> (\<forall>(i::nat) (j::nat). (i < dim_row a \<and> j < dim_col a) \<longrightarrow> f (a $$ (i, j)))"

definition vec_all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a vec \<Rightarrow>  bool"
  where "vec_all f a \<equiv> (\<forall>(i::nat). i < dim_vec a \<longrightarrow> f (a $ i))"

definition mat_all_row :: "('a vec \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> bool"
  where "mat_all_row f a  \<equiv> (\<forall>(i::nat). (i < dim_row a) \<longrightarrow> f (row a i))"

definition mat_all_col :: "('a vec \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> bool"
  where "mat_all_col f a  \<equiv> (\<forall>(i::nat). (i < dim_col a) \<longrightarrow> f (col a i))"

lemma mat_all_vec_all_row:
  assumes "mat_all f a"
  and "i < dim_row a"
shows "vec_all f (row a i)"
  using assms by(auto simp add:mat_all_def vec_all_def)

lemma mat_all_vec_all_col:
  assumes "mat_all f a"
  and "i < dim_col a"
shows "vec_all f (col a i)"
  using assms by(auto simp add:mat_all_def vec_all_def)


lemma matrix_multiplication_distribution:
  assumes probs: "mat_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) (ars::real mat)"
      and sums: "mat_all_col (\<lambda>v. (\<Sum>i\<in>{0..<dim_vec v}. v $ i) = 1) ars"
      and "(\<lambda>v. (\<Sum>i\<in>{0..<dim_vec v}. v $ i) = b) brs"
      and "dim_col ars = dim_vec brs"
    shows "(\<lambda>v. (\<Sum>i\<in>{0..<dim_vec v}. v $ i) = b) (mult_mat_vec ars brs)"
  using assms apply(auto simp add:mult_mat_vec_def mat_all_def vec_all_def scalar_prod_def mat_all_col_def row_def)
proof -
  have "(\<Sum>i = 0..<dim_row ars. \<Sum>ia = 0..<dim_vec brs. ars $$ (i, ia) * brs $ ia) = (\<Sum>ia = 0..<dim_vec brs. \<Sum>i = 0..<dim_row ars. ars $$ (i, ia) * brs $ ia)"
    using sum.swap by force
  moreover have "\<forall>ia.(\<Sum>i = 0..<dim_row ars. ars $$ (i, ia) * brs $ ia) = (\<Sum>i = 0..<dim_row ars. ars $$ (i, ia)) * brs $ ia"
    by (simp add: sum_distrib_right)
  ultimately have "(\<Sum>i = 0..<dim_row ars. \<Sum>ia = 0..<dim_vec brs. ars $$ (i, ia) * brs $ ia) = (\<Sum>ia = 0..<dim_vec brs. (\<Sum>i = 0..<dim_row ars. ars $$ (i, ia)) * brs $ ia)"
    by presburger
  with assms have "(\<forall>i<dim_vec brs. (\<Sum>x = 0..<dim_row ars. ars $$ (x, i)) = 1) \<Longrightarrow> (\<Sum>i = 0..<dim_row ars. \<Sum>ia = 0..<dim_vec brs. ars $$ (i, ia) * brs $ ia) = (\<Sum>ia = 0..<dim_vec brs. brs $ ia)"
    by auto
  with assms show "\<forall>i<dim_vec brs. (\<Sum>x = 0..<dim_row ars. ars $$ (x, i)) = 1 \<Longrightarrow> (\<Sum>i = 0..<dim_row ars. \<Sum>ia = 0..<dim_vec brs. ars $$ (i, ia) * brs $ ia) = sum (($) brs) {0..<dim_vec brs}" by blast
qed

lemma sum_ge_0:
  assumes "\<forall>j<l. (0::real) \<le> f j"
  and "x \<le> l"
shows "0 \<le> (\<Sum>ia = 0..<(x::nat). f ia)"
  using assms apply(induction x)
  by auto

(*lemma sum_ge_0_helper:
  assumes "x \<le> dim_col ars"
  shows "ars $$ (i, x) * brs $ x = ars $$ (i, x) * brs $ x"*)
declare [[show_types]]
lemma sum_ge_0_matrix_vector:
  assumes "\<forall>j<dim_col ars. (0::real) \<le> ars $$ (i, j) * brs $ j"
  and "x \<le> dim_col ars"
shows "0 \<le> (\<Sum>ia = 0..<x. row ars i $ ia * brs $ ia)"
(*proof -
  have "ars $$ (i, x) = row ars i $ x" using assms apply(simp add:row_def) 
  using sum_ge_0[OF assms]
  using sum_ge_0[where l="dim_col ars" and f="\<lambda>j. ars $$ (i, j) * brs $ j" and x=x]*)
using assms proof (induction x)
  case 0
  then show ?case by auto
next
  case (Suc x)
  from assms have " 0 \<le>  ars $$ (i, x) * brs $ x"
    using Suc.prems(2) Suc_le_lessD by presburger
  moreover have "ars $$ (i, x) = row ars i $ x" using Suc by(simp add:row_def)
  ultimately have p1: "0 \<le>  row ars i $ x * brs $ x" by metis
  moreover from atLeast0_lessThan_Suc have comb: "(\<Sum>ia = 0..<Suc x. row ars i $ ia * brs $ ia) = (\<Sum>ia = 0..<x. row ars i $ ia * brs $ ia) + row ars i $ x * brs $ x" by simp
  with Suc have p2: "0 \<le> (\<Sum>ia = 0..<x. row ars i $ ia * brs $ ia)" by auto
  with comb p1 show "0 \<le> (\<Sum>ia = 0..<Suc x. row ars i $ ia * brs $ ia)" by linarith
qed 

lemma individual_parst_le_sum_helper:
  assumes "\<exists>i<li. v < f i"
  and "\<forall>i<(li::nat). 0 \<le> f i"
shows "(v::real) < (\<Sum>i = 0..<li. f i)"
using assms proof (induction li)
  case 0
  then show ?case by blast
next
  case (Suc li)
  {
    assume "\<exists>i<li. v < f i"
    with Suc have "v < sum f {0..<li}" by auto
    with Suc have "v < sum f {0..<Suc li}" by auto
  }
  moreover {
    assume "\<not>(\<exists>i<li. v < f i)"
    with Suc have "v < f li"
      by (metis not_less_less_Suc_eq)
    moreover have "sum f {0..<Suc li} = sum f {0..<li} + f li" by simp
    moreover from Suc sum_ge_0 have "0\<le>sum f {0..<li}" by auto
    ultimately have "v < sum f {0..<Suc li}" by linarith
    
  }
  ultimately show "v < sum f {0..<Suc li}" by blast
qed

lemma individual_parst_le_sum:
  assumes "(\<Sum>i = 0..<li. f i) = (s::real)"
  and "\<forall>i<(li::nat). 0 \<le> f i"
shows "\<forall>i<li. f i \<le> s"
proof (rule ccontr)
  have p1: "\<not> (\<forall>i<li. f i \<le> s) \<Longrightarrow> \<exists>i<li. s < f i" by auto
  from individual_parst_le_sum_helper[OF p1 assms(2)] assms(1) show "\<not> (\<forall>i<li. f i \<le> s) \<Longrightarrow> False" by blast
qed

lemma matrix_multiplication_probabilities:
  assumes probs: "mat_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) (ars::real mat) \<and> vec_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) (brs::real vec)"
      and sums: "mat_all_col (\<lambda>v. (\<Sum>i\<in>{0..<dim_vec v}. v $ i) = 1) ars"
      and "(\<lambda>v. (\<Sum>i\<in>{0..<dim_vec v}. v $ i) = 1) brs"
      and "dim_col ars = dim_vec brs"
    shows "vec_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) (mult_mat_vec ars brs) \<and> (\<lambda>v. (\<Sum>i\<in>{0..<dim_vec v}. v $ i) = 1) (mult_mat_vec ars brs)"
proof -
  from assms matrix_multiplication_distribution have p1: "sum (($) (ars *\<^sub>v brs)) {0..<dim_vec (ars *\<^sub>v brs)} = 1" by blast
  from mat_all_def vec_all_def assms have "\<forall>i j k. i < dim_row ars \<and> j < dim_col ars \<and> k<dim_vec brs \<longrightarrow> 0 \<le> ars $$ (i,j) \<and> 0\<le> brs $ k"
    by (metis (no_types, lifting))
  then have "\<forall>i j k. i < dim_row ars \<and> j < dim_col ars \<and> k<dim_vec brs \<longrightarrow> 0 \<le> ars $$ (i,j) * brs $ k" by force
  with assms(4) have "\<forall>i j. i < dim_row ars \<and> j < dim_vec brs \<longrightarrow> 0 \<le> ars $$ (i,j) * brs $ j" by presburger
  then have "\<forall>i<dim_row ars. (\<forall>j. j < dim_vec brs \<longrightarrow> 0 \<le> ars $$ (i,j) * brs $ j)" by blast
  then have "\<forall>i. i<dim_vec (ars *\<^sub>v brs) \<longrightarrow> 0 \<le> (ars *\<^sub>v brs) $ i" apply(simp add:scalar_prod_def mult_mat_vec_def ) using sum_ge_0_matrix_vector
    using assms(4) le_refl by presburger
  with p1 show ?thesis apply(simp add:mult_mat_vec_def mat_all_def vec_all_def scalar_prod_def mat_all_col_def )
    using individual_parst_le_sum by blast
qed

fun fm  where
    "fm f m v 0 = v"
  | "fm f m v (Suc k) = fm f m (f m v) k" (*f m (f_mat_vec_pow f m v k)*)

lemma "fm f m v k = ((f m)^^k) v"
  apply (induction k arbitrary: v)
  apply auto
  by (simp add: funpow_swap1)


fun f_mat_vec_pow :: "('b mat \<Rightarrow> 'a vec \<Rightarrow> 'a vec) \<Rightarrow> 'b mat \<Rightarrow> 'a vec \<Rightarrow>  nat \<Rightarrow> 'a vec" where
    "f_mat_vec_pow f m v 0 = v"
  | "f_mat_vec_pow f m v (Suc k) = f_mat_vec_pow f m (f m v) k" (*f m (f_mat_vec_pow f m v k)*)

(*

*)

term "(m::_ mat)^^k"

lemma iterative_matrix_multiplication_probabilities:
  assumes probs: "mat_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) (ars::real mat) \<and> vec_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) (brs::real vec)"
      and sums: "mat_all_col (\<lambda>v. (\<Sum>i\<in>{0..<dim_vec v}. v $ i) = 1) ars"
      and "(\<lambda>v. (\<Sum>i\<in>{0..<dim_vec v}. v $ i) = 1) brs"
      and "dim_col ars = dim_vec brs"
      and "dim_col ars = dim_row ars"
    shows "vec_all (\<lambda>r. 0 \<le> r \<and> r \<le> 1) (((mult_mat_vec ars)^^k) brs) \<and> (\<lambda>v. (\<Sum>i\<in>{0..<dim_vec v}. v $ i) = 1) (((mult_mat_vec ars)^^k) brs)"
using assms proof(induction k arbitrary: brs)
  case 0
  then show ?case by simp
next
  case (Suc k)
  moreover have "(((*\<^sub>v) ars ^^ Suc k) brs) = (((*\<^sub>v) ars ^^ k) ((*\<^sub>v) ars brs))" 
    by (simp add: funpow_swap1)
  ultimately show ?case using matrix_multiplication_probabilities 
    by (smt (verit) dim_mult_mat_vec)
qed




end