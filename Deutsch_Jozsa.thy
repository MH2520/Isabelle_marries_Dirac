(*
Authors: 

  Hanna Lachnitt, TU Wien, lachnitt@student.tuwien.ac.at
  Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk
*)

theory Deutsch_Jozsa
imports
  MoreTensor
  Binary_Nat
begin


(*There will probably be some lemmas going into Basic (maybe even Tensor) in here, 
I will transfer them when I am sure they are actually needed*)


(*TODO: Name IH everywhere the same*)
(*TODO: Clean up facts*)
(*TODO: Take smt out if possible*)
(*TODO: Suc n and n+1*)


section \<open>The Deutsch-Jozsa Algorithm\<close>

text \<open>
Given a constant or balanced function $f:{0,1}^n\mapsto {0,1}$, the Deutsch-Jozsa algorithm 
decides if this function is constant or balanced with a single $f(x)$ circuit to evaluate the 
function for multiple values of $x$ simultaneously. The algorithm makes use of quantum parallelism 
and quantum interference.
\<close>

section \<open>Input function\<close>

text \<open>
A constant function returns either always 0 or always 1. 
A balanced function is 0 for half of the inputs and 1 for the other half. 
\<close>

locale bob_fun =
  fixes f:: "nat \<Rightarrow> nat" and n:: "nat"
  assumes dom: "f \<in> ({(i::nat). i < 2^n} \<rightarrow>\<^sub>E {0,1})"
  assumes dim: "n \<ge> 1"

context bob_fun
begin

definition const:: "nat \<Rightarrow> bool" where 
"const c = (\<forall>x\<in>{i::nat. i < 2^n}. f x = c)"

definition is_const:: bool where 
"is_const \<equiv> const 0 \<or> const 1"

definition is_balanced:: bool where
"is_balanced \<equiv> \<exists>A B. A \<subseteq> {i::nat. i < 2^n} \<and> B \<subseteq> {i::nat. i < 2^n}
                   \<and> card A = (2^(n-1)) \<and> card B = (2^(n-1))  
                   \<and> (\<forall>x \<in> A. f(x) = 0)  \<and> (\<forall>x \<in> B. f(x) = 1)"

lemma is_balanced_inter: 
  fixes A B:: "nat set"
  assumes "\<forall>x \<in> A. f(x) = 0" and "\<forall>x \<in> B. f(x) = 1" 
  shows "A \<inter> B = {}" 
  using assms by auto

lemma is_balanced_union:
  fixes A B:: "nat set"
  assumes "A \<subseteq> {i::nat. i < 2^n}" and "B \<subseteq> {i::nat. i < 2^n}" 
      and "card A = (2^(n-1))" and "card B = (2^(n-1))" 
      and "A \<inter> B = {}"
  shows "A \<union> B = {i::nat. i < 2^n}"
proof-
  have "finite A" and "finite B" 
     apply (simp add: assms(3) card_ge_0_finite)
    apply (simp add: assms(4) card_ge_0_finite).
  then have "card(A \<union> B) = 2 * 2^(n-1)" 
    using assms(3-5) by (simp add: card_Un_disjoint)
  then have "card(A \<union> B) = 2^n"
    by (metis Nat.nat.simps(3) One_nat_def dim le_0_eq power_eq_if)
  moreover have "\<dots> = card({i::nat. i < 2^n})" by simp
  moreover have "A \<union> B \<subseteq> {i::nat. i < 2^n}" 
    using assms(1,2) by simp
  moreover have "finite ({i::nat. i < 2^n})" by simp
  ultimately show ?thesis 
    using card_subset_eq[of "{i::nat. i < 2^n}" "A \<union> B"] by simp
qed

lemma f_ge_0: "\<forall>x. (f x \<ge> 0)" by simp

lemma f_dom_not_zero: 
  shows "f \<in> ({i::nat. n \<ge> 1 \<and> i < 2^n} \<rightarrow>\<^sub>E {0,1})" 
  using dim dom by simp

lemma f_values: "\<forall>x \<in> {(i::nat). i < 2^n} .(f x = 0 \<or> f x = 1)" 
  using dom by auto


end (* bob_fun *)

text \<open>
The input function has to be constant or balanced. 
\<close>

locale jozsa = bob_fun +
  assumes const_or_balanced: "is_const \<or> is_balanced "


text \<open>
Introduce two customised rules: disjunctions with four disjuncts and induction starting from one instead of zero.
\<close>

(*To deal with Uf it is often necessary to do a case distinction with four different cases.*)
lemma disj_four_cases:
  assumes "A \<or> B \<or> C \<or> D"
  and "A \<Longrightarrow> P"
  and "B \<Longrightarrow> P"
  and "C \<Longrightarrow> P"
  and "D \<Longrightarrow> P"
  shows "P"
proof -
  from assms show ?thesis by blast
qed

(*As n has to be at least 1 we introduce a modified introduction rule *)
lemma ind_from_1 [case_names n_ge_1 1 step]:
  assumes "n \<ge> 1"
  assumes "P(1)" 
  assumes "\<And>n. n \<ge> 1 \<Longrightarrow>  P n \<Longrightarrow> P (Suc n)"
  shows " P n"
  using nat_induct_at_least assms by auto

text \<open>The unitary transform @{text U\<^sub>f}.\<close>

definition (in jozsa) jozsa_transform:: "complex Matrix.mat" ("U\<^sub>f") where 
"U\<^sub>f \<equiv> Matrix.mat (2^(n+1)) (2^(n+1)) (\<lambda>(i,j). if i = j then (1-f(i div 2)) else 
                                          if i = j + 1 \<and> odd i then f(i div 2) else
                                             if i = j - 1 \<and> even i \<and> j\<ge>1 then f(i div 2) else 0)"

lemma (in jozsa) jozsa_transform_dim [simp]:
  shows "dim_row U\<^sub>f = 2^(n+1)" and "dim_col U\<^sub>f = (2^(n+1))" 
  by (auto simp add: jozsa_transform_def)

lemma (in jozsa) jozsa_transform_coeff_is_zero [simp]:
  assumes "i < dim_row U\<^sub>f \<and> j < dim_col U\<^sub>f"
  shows "(i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1)) \<longrightarrow> U\<^sub>f $$ (i,j) = 0"
  using jozsa_transform_def assms by auto

lemma (in jozsa) jozsa_transform_coeff [simp]: 
  assumes "i < dim_row U\<^sub>f \<and> j < dim_col U\<^sub>f"
  shows "i = j \<longrightarrow> U\<^sub>f $$ (i,j) = 1 - f (i div 2)"
  and "i = j + 1 \<and> odd i \<longrightarrow> U\<^sub>f $$ (i,j) = f (i div 2)"
  and "j\<ge>1 \<and> i = j - 1 \<and> even i \<longrightarrow> U\<^sub>f $$ (i,j) = f (i div 2)" 
  using jozsa_transform_def assms by auto

(*Should this be a lemma on its own? could easily be integrated in main lemma (next one)*)
(*Is this version structured better than the next??? I am not sure*)
lemma (in jozsa) U\<^sub>f_mult_without_empty_summands_sum_even:  (*better name*)
  fixes i j A
  assumes "i < dim_row U\<^sub>f" and "j < dim_col A"
  and "even i" 
  and "dim_col U\<^sub>f = dim_row A"
  shows "(\<Sum>k\<in>{0..< dim_row A}. U\<^sub>f $$ (i, k) * A $$ (k, j)) =(\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i, k) * A $$ (k, j)) "
proof-
  have "(\<Sum>k\<in>{0..< 2 ^ (n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 
             (\<Sum>k \<in> {0..<i}. U\<^sub>f $$ (i, k) * A $$ (k, j))+
             (\<Sum>k \<in> {i,i+1}. U\<^sub>f $$ (i, k) * A $$ (k, j))+
             (\<Sum>k \<in> {(i+2)..< 2^(n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) " 
  proof - 
    have "{0..< 2^(n+1)} = {0..<i} \<union> {i..< 2^(n+1)} 
          \<and> {i..< 2^(n+1)} = {i,i+1} \<union> {(i+2)..<2^(n+1)}" using assms(1-3) by auto
    moreover have "{0..<i} \<inter> {i,i+1} = {} 
                  \<and> {i,i+1} \<inter> {(i+2)..< 2^(n+1)} = {} 
                  \<and> {0..<i} \<inter> {(i+2)..< 2^(n+1)} = {}" using assms by auto
    ultimately show ?thesis
      using assms sum.union_disjoint  
      by (metis (no_types, lifting) finite_Un finite_atLeastLessThan is_num_normalize(1) ivl_disj_int_two(3))
  qed
  moreover have "(\<Sum>k \<in> {0..<i}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 0 " 
  proof-
    have "k \<in> {0..<i} \<longrightarrow> (i\<noteq>k \<and> \<not>(i=k+1 \<and> odd i) \<and> \<not> (i=k-1 \<and> even i \<and> k\<ge>1))" for k 
      using assms by auto
    then have "k \<in> {0..<i} \<longrightarrow> U\<^sub>f $$ (i, k) =0" for k
      by (metis assms(1) atLeastLessThan_iff jozsa_transform_coeff_is_zero jozsa_transform_dim 
          less_imp_add_positive trans_less_add1)
    then show ?thesis 
      by simp
  qed
  moreover have "(\<Sum>k \<in> {(i+2)..< 2^(n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 0 " 
  proof- 
    have  "k \<in> {(i+2)..< 2^(n+1)} \<longrightarrow> (i\<noteq>k \<and> \<not>(i=k+1 \<and> odd i) \<and> \<not> (i=k-1 \<and> even i \<and> k\<ge>1))" for k
      using assms by auto
    then have "k \<in> {(i+2)..< 2^(n+1)}\<longrightarrow> U\<^sub>f $$ (i, k) = 0" for k
      using jozsa_transform_coeff_is_zero assms  by auto
    then show ?thesis
      by simp
  qed
  moreover have  "dim_row A =  2^(n+1)" using assms by simp
  ultimately show "(\<Sum>k\<in>{0..< dim_row A}. U\<^sub>f $$ (i, k) * A $$ (k, j)) =(\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i, k) * A $$ (k, j))"
    using assms 
    by (metis (no_types, lifting) add.left_neutral add.right_neutral)
qed

(*Second version with different structure*)
lemma (in jozsa) U\<^sub>f_mult_without_empty_summands_sum_even':  (*better name*)
  fixes i j A
  assumes "i < dim_row U\<^sub>f" and "j < dim_col A"
  and "even i" 
  and "dim_col U\<^sub>f = dim_row A"
  shows "(\<Sum>k\<in>{0..< dim_row A}. U\<^sub>f $$ (i, k) * A $$ (k, j)) =(\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i, k) * A $$ (k, j)) "
proof-
  have "{0..< 2^(n+1)} = {0..<i} \<union> {i..< 2^(n+1)} 
        \<and> {i..< 2^(n+1)} = {i,i+1} \<union> {(i+2)..<2^(n+1)}" using assms(1-3) by auto
  moreover have "{0..<i} \<inter> {i,i+1} = {} 
        \<and> {i,i+1} \<inter> {(i+2)..< 2^(n+1)} = {} 
        \<and> {0..<i} \<inter> {(i+2)..< 2^(n+1)} = {}" using assms by auto
  ultimately have f0: "(\<Sum>k\<in>{0..< 2 ^ (n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 
             (\<Sum>k \<in> {0..<i}. U\<^sub>f $$ (i, k) * A $$ (k, j))+
             (\<Sum>k \<in> {i,i+1}. U\<^sub>f $$ (i, k) * A $$ (k, j))+
             (\<Sum>k \<in> {(i+2)..< 2^(n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) " 
    using assms sum.union_disjoint  
    by (metis (no_types, lifting) finite_Un finite_atLeastLessThan is_num_normalize(1) ivl_disj_int_two(3))

  have "k \<in> {0..<i} \<longrightarrow> (i\<noteq>k \<and> \<not>(i=k+1 \<and> odd i) \<and> \<not> (i=k-1 \<and> even i \<and> k\<ge>1))" for k 
    using assms by auto
  then have "k \<in> {0..<i} \<longrightarrow> U\<^sub>f $$ (i, k) =0" for k
    by (metis assms(1) atLeastLessThan_iff jozsa_transform_coeff_is_zero jozsa_transform_dim 
        less_imp_add_positive trans_less_add1)
  then have f1:"(\<Sum>k \<in> {0..<i}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 0 " 
    by simp

  have "k \<in> {(i+2)..< 2^(n+1)} \<longrightarrow> (i\<noteq>k \<and> \<not>(i=k+1 \<and> odd i) \<and> \<not> (i=k-1 \<and> even i \<and> k\<ge>1))" for k
    using assms by auto
  then have "k \<in> {(i+2)..< 2^(n+1)}\<longrightarrow> U\<^sub>f $$ (i, k) = 0" for k
    using jozsa_transform_coeff_is_zero assms  by auto
  then have f2: "(\<Sum>k \<in> {(i+2)..< 2^(n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 0 " 
    by simp

  have "dim_row A =  2^(n+1)" using assms by simp
  then show "(\<Sum>k\<in>{0..< dim_row A}. U\<^sub>f $$ (i, k) * A $$ (k, j)) =(\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i, k) * A $$ (k, j))"
    using f0 f1 f2 assms 
    by (metis (no_types, lifting) add.left_neutral add.right_neutral)
qed

lemma (in jozsa) U\<^sub>f_mult_without_empty_summands_even: 
  fixes i j A
  assumes "i < dim_row U\<^sub>f" and "j < dim_col A"
  and "even i"
  and "dim_col U\<^sub>f = dim_row A"
  shows "(U\<^sub>f * A) $$ (i,j) = (\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i, k) * A $$ (k, j)) "
proof -
  have "(U\<^sub>f * A) $$ (i,j) = (\<Sum> k \<in> {0 ..< dim_row A}. (U\<^sub>f $$ (i,k)) * (A $$ (k,j)))"
    using assms index_matrix_prod 
    by (simp add: atLeast0LessThan)
  then show "(U\<^sub>f * A) $$ (i,j) = (\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i, k) * A $$ (k, j))" 
    using assms U\<^sub>f_mult_without_empty_summands_sum_even by auto
qed






lemma (in jozsa) U\<^sub>f_mult_without_empty_summands_sum_odd:  (*better name*)
  fixes i j A
  assumes "i < dim_row U\<^sub>f" and "j < dim_col A"
  and "odd i" 
  and "dim_col U\<^sub>f = dim_row A"
  shows "(\<Sum>k\<in>{0..< dim_row A}. U\<^sub>f $$ (i, k) * A $$ (k, j)) =(\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i, k) * A $$ (k, j)) "
proof-
  have "{0..< 2^(n+1)} = {0..<(i-1)} \<union> {(i-1)..< 2^(n+1)}" using assms by auto
  moreover have "{(i-1)..< 2^(n+1)} = {i-1,i} \<union> {(i+1)..<2^(n+1)}" using assms(1-3) by auto
  moreover have "{0..<(i-1)} \<inter> {i-1,i} = {} 
                \<and> {i-1,i} \<inter> {(i+1)..< 2^(n+1)} = {} 
                \<and> {0..<(i-1)} \<inter> {(i-1)..< 2^(n+1)} = {}" 
    using assms by auto
  ultimately have f0: "(\<Sum>k \<in> {0..< 2^(n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 
             (\<Sum>k \<in> {0..<(i-1)}. U\<^sub>f $$ (i, k) * A $$ (k, j))+
             (\<Sum>k \<in> {i-1,i}. U\<^sub>f $$ (i, k) * A $$ (k, j))+
             (\<Sum>k \<in> {(i+1)..<2^(n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) " 
    using assms sum.union_disjoint  
    by (metis (no_types, lifting) finite_Un finite_atLeastLessThan is_num_normalize(1) ivl_disj_int_two(3))

  have "k \<in> {0..<(i-1)} \<longrightarrow> (i\<noteq>k \<and> \<not>(i=k+1 \<and> odd i) \<and> \<not> (i=k-1 \<and> even i \<and> k\<ge>1))" for k 
    using assms by auto
  then have "k \<in> {0..<(i-1)} \<longrightarrow> U\<^sub>f $$ (i, k) =0" for k
    by (metis assms(1) atLeastLessThan_iff jozsa_transform_coeff_is_zero jozsa_transform_dim 
        less_imp_add_positive less_imp_diff_less trans_less_add1)
  then have f1:"(\<Sum>k \<in> {0..<(i-1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 0 " 
    by simp

  have "k \<in> {(i+1)..<2^(n+1)} \<longrightarrow> (i\<noteq>k \<and> \<not>(i=k+1 \<and> odd i) \<and> \<not> (i=k-1 \<and> even i \<and> k\<ge>1))" for k
    using assms by auto
  then have "k \<in> {(i+1)..<2^(n+1)} \<longrightarrow> U\<^sub>f $$ (i, k) = 0" for k
    using jozsa_transform_coeff_is_zero assms by auto
  then have f2: "(\<Sum>k \<in> {(i+1)..<2^(n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 0 " 
    by simp

  have "dim_row A =  2^(n+1)" using assms by simp
  then show "(\<Sum>k\<in>{0..< dim_row A}. U\<^sub>f $$ (i, k) * A $$ (k, j)) =(\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i, k) * A $$ (k, j))"
    using f0 f1 f2 assms 
    by (metis (no_types, lifting) add.left_neutral add.right_neutral)
qed

lemma (in jozsa) U\<^sub>f_mult_without_empty_summands_odd: 
  fixes i j A
  assumes "i < dim_row U\<^sub>f" and "j < dim_col A"
  and "odd i"
  and "dim_col U\<^sub>f = dim_row A"
  shows "(U\<^sub>f * A) $$ (i,j) = (\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i, k) * A $$ (k, j)) "
proof-
  have "(U\<^sub>f * A) $$ (i,j) = (\<Sum> k \<in> {0 ..< dim_row A}. (U\<^sub>f $$ (i,k)) * (A $$ (k,j)))"
    using assms index_matrix_prod 
    by (simp add: atLeast0LessThan)
  then show "(U\<^sub>f * A) $$ (i,j) = (\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i, k) * A $$ (k, j))" 
    using assms U\<^sub>f_mult_without_empty_summands_sum_odd by auto
qed



text \<open>@{text U\<^sub>f} is a gate.\<close>

lemma (in jozsa) transpose_of_jozsa_transform:
  shows "(U\<^sub>f)\<^sup>t = U\<^sub>f"
proof
  show "dim_row (U\<^sub>f\<^sup>t) = dim_row U\<^sub>f" by simp
next
  show "dim_col (U\<^sub>f\<^sup>t) = dim_col U\<^sub>f" by simp
next
  fix i j:: nat
  assume a0: "i < dim_row U\<^sub>f" and a1: "j < dim_col U\<^sub>f"
  thus "U\<^sub>f\<^sup>t $$ (i, j) = U\<^sub>f $$ (i, j)" 
  proof (induct rule: disj_four_cases)
    show "i=j \<or> (i=j+1 \<and> odd i) \<or> (i=j-1 \<and> even i \<and> j\<ge>1) \<or> (i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1))"
      by linarith
  next
    assume a2: "i=j"
    then show "U\<^sub>f\<^sup>t $$ (i, j) = U\<^sub>f $$ (i, j)" 
      using a0 by auto
  next
    assume a2: "(i=j+1 \<and> odd i)"
    then show "U\<^sub>f\<^sup>t $$ (i, j) = U\<^sub>f $$ (i, j)"
      using transpose_mat_def a0 a1 by auto
  next
    assume a2:"(i=j-1 \<and> even i \<and> j\<ge>1)"
    then have "U\<^sub>f $$ (i, j) = f (i div 2)" 
      using a0 a1 jozsa_transform_coeff by blast
    moreover have "U\<^sub>f $$ (j, i) = f (i div 2)" 
      using a0 a1 a2 jozsa_transform_coeff
      by (metis add_diff_assoc2 diff_add_inverse2 even_plus_one_iff even_succ_div_two jozsa_transform_dim)
    ultimately show "U\<^sub>f\<^sup>t $$ (i, j) = U\<^sub>f $$ (i, j)"
      using transpose_mat_def a0 a1 by auto
  next 
    assume a2: "(i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1))"
    then have "(j\<noteq>i \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))" 
      by (metis le_imp_diff_is_add diff_add_inverse even_plus_one_iff le_add1)
    then have "U\<^sub>f $$ (j, i) = 0" 
      using jozsa_transform_coeff_is_zero a0 a1 by auto
    moreover have "U\<^sub>f $$ (i, j) = 0" 
      using jozsa_transform_coeff_is_zero a0 a1 a2 by auto
    ultimately show "U\<^sub>f\<^sup>t $$ (i, j) = U\<^sub>f $$ (i, j)"
      using transpose_mat_def a0 a1 by auto
  qed 
qed

lemma (in jozsa) adjoint_of_jozsa_transform: 
  shows "(U\<^sub>f)\<^sup>\<dagger> = U\<^sub>f"
proof
  show "dim_row (U\<^sub>f\<^sup>\<dagger>) = dim_row U\<^sub>f" by simp
next
  show "dim_col (U\<^sub>f\<^sup>\<dagger>) = dim_col U\<^sub>f" by simp
next
  fix i j:: nat
  assume a0: "i < dim_row U\<^sub>f" and a1: "j < dim_col U\<^sub>f"
  thus "U\<^sub>f\<^sup>\<dagger> $$ (i, j) = U\<^sub>f $$ (i, j)"
  proof (induct rule: disj_four_cases )
 show "i=j \<or> (i=j+1 \<and> odd i) \<or> (i=j-1 \<and> even i \<and> j\<ge>1) \<or> (i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1))"
      by linarith
  next
    assume a2: "i=j"
    then show "U\<^sub>f\<^sup>\<dagger> $$ (i, j) = U\<^sub>f $$ (i, j)" 
      using a0 hermite_cnj_def by auto
  next
    assume a2: "(i=j+1 \<and> odd i)"
    then show "U\<^sub>f\<^sup>\<dagger> $$ (i, j) = U\<^sub>f $$ (i, j)" 
      using a0 hermite_cnj_def by auto
  next
    assume a2:"(i=j-1 \<and> even i \<and> j\<ge>1)"
    then have "U\<^sub>f $$ (i, j) = f (i div 2)" 
      using a0 a1 jozsa_transform_coeff by auto
    moreover have "U\<^sub>f\<^sup>\<dagger>  $$ (j, i) = f (i div 2)" 
      using a1 a2 jozsa_transform_coeff hermite_cnj_def by auto 
    ultimately show "U\<^sub>f\<^sup>\<dagger> $$ (i, j) = U\<^sub>f $$ (i, j)" 
      by (metis a0 a1 cnj_transpose hermite_cnj_dim_row index_transpose_mat
          transpose_hermite_cnj transpose_of_jozsa_transform)
  next 
    assume a2: "(i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1))"
    then have f0:"(i\<noteq>j \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))" 
      by (metis le_imp_diff_is_add diff_add_inverse even_plus_one_iff le_add1)
    then have "U\<^sub>f $$ (j,i) = 0" and "cnj 0 = 0"
      using jozsa_transform_coeff_is_zero a0 a1 a2 by auto
    then have "U\<^sub>f\<^sup>\<dagger> $$ (i,j) = 0" 
      using a0 a1 hermite_cnj_def by auto
    then show "U\<^sub>f\<^sup>\<dagger> $$ (i, j) = U\<^sub>f $$ (i, j)" 
      using a0 a1 a2 jozsa_transform_coeff_is_zero by auto
  qed 
qed

(*TODO: add line breaks if possible take out facts*)
lemma (in jozsa) jozsa_transform_is_unitary_index_even:
  fixes i j::nat
  assumes "i < dim_row U\<^sub>f" and "j < dim_col U\<^sub>f"
      and "even i"
  shows "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)"
proof-
  have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i, k) * U\<^sub>f $$ (k, j)) " 
    using U\<^sub>f_mult_without_empty_summands_even[of i j U\<^sub>f ] assms by auto
  moreover have "U\<^sub>f $$ (i, i) * U\<^sub>f $$ (i, j) = (1-f(i div 2))  * U\<^sub>f $$ (i, j)" 
    using assms by simp
  moreover have f0: "U\<^sub>f $$ (i, i+1) * U\<^sub>f $$ (i+1, j) = f(i div 2) * U\<^sub>f $$ (i+1, j)" 
    by (metis assms add.right_neutral One_nat_def Suc_leI add_Suc_right diff_add_inverse2 dvd_minus_add 
        even_add even_plus_one_iff even_succ_div_two index_transpose_mat(1) jozsa_transform_coeff(2) 
        jozsa_transform_dim nat_less_le power_add power_one_right transpose_of_jozsa_transform)
  ultimately have f1: "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (1-f(i div 2)) * U\<^sub>f $$ (i, j) +  f(i div 2) * U\<^sub>f $$ (i+1, j)" by auto
  thus "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)"
  proof (induct rule: disj_four_cases)
    show "j=i \<or> (j=i+1 \<and> odd j) \<or> (j=i-1 \<and> even j \<and> i\<ge>1) \<or> (j\<noteq>i \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))"
      by linarith
  next
    assume a0: "j=i"
    then have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (1-f(i div 2))  *(1-f(i div 2)) +  f(i div 2) * f(i div 2)" (*TODO: proof without smt*)
      using f1 assms
      by (smt Groups.monoid_add_class.add.right_neutral One_nat_def Suc_leI add_Suc_right even_add 
          even_mult_iff even_plus_one_iff even_succ_div_two jozsa_transform_coeff(1) jozsa_transform_coeff(2) 
          jozsa_transform_dim(1) nat_less_le of_nat_add of_nat_mult one_add_one power_add power_one_right)
    moreover have "(1-f(i div 2))  *(1-f(i div 2)) +  f(i div 2) * f(i div 2) = 1" 
      using f_values assms
      by (metis (no_types, lifting) Nat.minus_nat.diff_0 diff_add_0 diff_add_inverse jozsa_transform_dim(1) less_power_add_imp_div_less mem_Collect_eq mult_eq_if one_power2 power2_eq_square power_one_right) 
    ultimately show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
      by (metis assms(2) a0 index_one_mat(1) of_nat_1)
  next
    assume a0: "(j=i+1 \<and> odd j)"
    then have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (1-f(i div 2))  *f(i div 2) +  f(i div 2) *(1-f(i div 2))" (*TODO: proof without smt*)
      using f0 f1 assms
      by (smt jozsa_transform_coeff(1) Groups.ab_semigroup_mult_class.mult.commute even_succ_div_two 
          jozsa_transform_dim of_nat_add of_nat_mult)
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
      using assms a0 by auto
  next
    assume a0:"(j=i-1 \<and> even j \<and> i\<ge>1)"
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
      using a0 assms(3) dvd_diffD1 odd_one by blast
  next 
    assume a0: "(j\<noteq>i \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))"
    then have "U\<^sub>f $$ (i, j) = 0" 
      by (metis assms index_transpose_mat(1) jozsa_transform_coeff_is_zero jozsa_transform_dim transpose_of_jozsa_transform)
    moreover have "U\<^sub>f $$ (i+1, j) = 0" (*TODO: proof without smt*)
      using assms a0
      by (smt add.right_neutral One_nat_def Suc_leI add_Suc_right add_diff_cancel_left' add_right_cancel 
          dvd_minus_add even_plus_one_iff jozsa_transform_coeff_is_zero jozsa_transform_dim(1) 
          less_imp_le_nat nat_less_le odd_one power_add power_one_right)
    ultimately have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (1-f(i div 2))  *0 +  f(i div 2) *0" 
      by (simp add: f1)
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
      using a0 assms
      by (metis add.left_neutral index_one_mat(1) jozsa_transform_dim mult_0_right of_nat_0)
  qed
qed


lemma (in jozsa) jozsa_transform_is_unitary_index_odd:
  fixes i j::nat
  assumes "i < dim_row U\<^sub>f" and "j < dim_col U\<^sub>f"
      and "odd i"
  shows "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)"
proof-
  have f0: "i\<ge>1"  
    using linorder_not_less assms(3) by auto
  have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i, k) * U\<^sub>f $$ (k, j)) " 
    using U\<^sub>f_mult_without_empty_summands_odd[of i j U\<^sub>f ] assms by auto
  moreover have "(\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i, k) * U\<^sub>f $$ (k, j)) 
                 = U\<^sub>f $$ (i, i-1) * U\<^sub>f $$ (i-1, j) +  U\<^sub>f $$ (i, i) * U\<^sub>f $$ (i, j)" 
    using assms f0 by auto
  moreover have "U\<^sub>f $$ (i, i) * U\<^sub>f $$ (i, j) = (1-f(i div 2))  * U\<^sub>f $$ (i, j)" 
    using assms jozsa_transform_coeff by simp
  moreover have f1: "U\<^sub>f $$ (i, i-1) * U\<^sub>f $$ (i-1, j) = f(i div 2) * U\<^sub>f $$ (i-1, j)" 
    using assms(1) assms(3) by auto
  ultimately have f2: "(U\<^sub>f * U\<^sub>f) $$ (i,j) = f(i div 2) * U\<^sub>f $$ (i-1, j) + (1-f(i div 2))  * U\<^sub>f $$ (i, j)" 
    using assms by auto
  show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)"
  proof (induct rule: disj_four_cases)
    show "j=i \<or> (j=i+1 \<and> odd j) \<or> (j=i-1 \<and> even j \<and> i\<ge>1) \<or> (j\<noteq>i \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))"
      by linarith
  next
    assume a0: "j=i"
    then have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = f(i div 2) * f(i div 2) +  (1-f(i div 2)) *  (1-f(i div 2))" (*TODO: proof without smt*)
      using f2 assms 
      by (smt diff_less index_transpose_mat(1) jozsa_transform_coeff(1) jozsa_transform_coeff(2) 
          less_imp_add_positive less_numeral_extra(1) odd_pos odd_two_times_div_two_nat odd_two_times_div_two_succ 
          of_nat_add of_nat_mult trans_less_add1 transpose_of_jozsa_transform)
    moreover have "f(i div 2) * f(i div 2) +  (1-f(i div 2)) *  (1-f(i div 2)) = 1" 
      using f_values assms
      by (metis (no_types, lifting) Nat.minus_nat.diff_0 diff_add_0 diff_add_inverse jozsa_transform_dim(1) 
          less_power_add_imp_div_less mem_Collect_eq mult_eq_if one_power2 power2_eq_square power_one_right) 
    ultimately show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
      by (metis assms(2) a0 index_one_mat(1) of_nat_1)
  next
    assume a0: "(j=i+1 \<and> odd j)"
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
      using assms(3) dvd_diffD1 odd_one even_plus_one_iff by blast
  next
    assume a0:"(j=i-1 \<and> even j \<and> i\<ge>1)"
    then have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = f(i div 2) * (1-f(i div 2)) +  (1-f(i div 2)) *  f(i div 2)" 
      using f0 f1 f2 assms
      by (metis jozsa_transform_coeff(1) Groups.ab_semigroup_mult_class.mult.commute even_succ_div_two f2 
          jozsa_transform_dim odd_two_times_div_two_nat odd_two_times_div_two_succ of_nat_add of_nat_mult)
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
      using assms a0 by auto
  next 
    assume a0: "(j\<noteq>i \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))"
    then have "U\<^sub>f $$ (i, j) = 0" 
      by (metis assms index_transpose_mat(1) jozsa_transform_coeff_is_zero jozsa_transform_dim transpose_of_jozsa_transform)
    moreover have "U\<^sub>f $$ (i-1, j) = 0" (*TODO: proof without smt*)
      using assms a0 f0 
      by (smt Groups.ordered_cancel_comm_monoid_diff_class.add_diff_inverse diff_less even_diff_nat 
          even_plus_one_iff  jozsa_transform_coeff_is_zero less_imp_add_positive less_numeral_extra(1) trans_less_add1)
    ultimately have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (1-f(i div 2))  *0 +  f(i div 2) *0" 
      using f2 by simp
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
      using a0 assms
      by (metis add.left_neutral index_one_mat(1) jozsa_transform_dim mult_0_right of_nat_0)
  qed
qed

lemma (in jozsa) jozsa_transform_is_gate:
  shows "gate (n+1) U\<^sub>f"
proof
  show "dim_row U\<^sub>f = 2^(n+1)" by simp
next
  show "square_mat U\<^sub>f" by simp
next
  show "unitary U\<^sub>f"
  proof-
    have "U\<^sub>f * U\<^sub>f = 1\<^sub>m (dim_col U\<^sub>f)"
    proof
      show "dim_row (U\<^sub>f * U\<^sub>f) = dim_row (1\<^sub>m (dim_col U\<^sub>f))" by simp
    next
      show "dim_col (U\<^sub>f * U\<^sub>f) = dim_col (1\<^sub>m (dim_col U\<^sub>f))" by simp
    next
      fix i j:: nat
      assume "i < dim_row (1\<^sub>m (dim_col U\<^sub>f))" and "j < dim_col (1\<^sub>m (dim_col U\<^sub>f))"
      then have "i < dim_row U\<^sub>f" and "j < dim_col U\<^sub>f" by auto
      then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
        using jozsa_transform_is_unitary_index_odd jozsa_transform_is_unitary_index_even 
        by blast
    qed
  then show "unitary U\<^sub>f" 
    by (simp add: adjoint_of_jozsa_transform unitary_def)
  qed
qed


(*TODO: Better way then always assuming n\<ge>1?, for now just keep it a moment to try out what works*)

(*TODO: Think about binding of n and inductions. Should all lemmas be in jozsa? How to do induction then?
But first finish last step to see what requirements exist*)

text \<open>N-fold application of the tensor product\<close>

fun pow_tensor :: "complex Matrix.mat \<Rightarrow> nat \<Rightarrow>  complex Matrix.mat" (infixr "^\<^sub>\<otimes>" 75) where
  "A ^\<^sub>\<otimes> (Suc 0) = A"  
| "A ^\<^sub>\<otimes> (Suc k) =  A \<Otimes> (A ^\<^sub>\<otimes> k)"

lemma pow_tensor_1_is_id [simp]:
  fixes A
  shows "A ^\<^sub>\<otimes> 1 = A"
  using one_mat_def by auto

lemma pow_tensor_n: 
  fixes n
  assumes "n \<ge> 1"
  shows " A ^\<^sub>\<otimes> (Suc n) = A  \<Otimes>  ( A ^\<^sub>\<otimes> n)" using assms 
  by (metis Deutsch_Jozsa.pow_tensor.simps(2) One_nat_def Suc_le_D)

lemma pow_tensor_dim_row [simp]:
  fixes A n
  assumes "n \<ge> 1"
  shows "dim_row(A ^\<^sub>\<otimes> n) = (dim_row A)^n"
proof (induction n rule: ind_from_1)
  show "n\<ge>1" using assms by auto 
next
  show "dim_row(A ^\<^sub>\<otimes> 1) = (dim_row A)^1" by simp
next
  fix n
  assume "dim_row(A ^\<^sub>\<otimes> n) = (dim_row A)^n"
  then show "dim_row(A ^\<^sub>\<otimes> (Suc n)) = (dim_row A)^(Suc n)" 
    by (metis One_nat_def Suc_inject Zero_not_Suc dim_row_tensor_mat pow_tensor.elims power_Suc power_one_right)
qed

lemma pow_tensor_dim_col [simp]:
  fixes A n
  assumes "n \<ge> 1"
  shows "dim_col(A ^\<^sub>\<otimes> n) = (dim_col A)^n"
proof (induction n rule: ind_from_1)
  show "n\<ge>1" using assms by auto 
next
  show "dim_col(A ^\<^sub>\<otimes> 1) = (dim_col A)^1" by simp
next
  fix n
  assume "dim_col(A ^\<^sub>\<otimes> n) = (dim_col A)^n"
  then show "dim_col(A ^\<^sub>\<otimes> (Suc n)) = (dim_col A)^(Suc n)" 
    by (metis dim_col_tensor_mat One_nat_def Suc_inject Zero_not_Suc pow_tensor.elims power_Suc power_one_right )
qed

lemma pow_tensor_values:
  fixes A n i j
  assumes "n \<ge> 1"
  assumes "i < dim_row ( A \<Otimes> ( A ^\<^sub>\<otimes> n))"
  and "j < dim_col ( A \<Otimes> ( A ^\<^sub>\<otimes> n))"
  shows "( A ^\<^sub>\<otimes> (Suc n)) $$ (i, j) = ( A \<Otimes> ( A ^\<^sub>\<otimes> n)) $$ (i, j)"
  using assms
  by (metis One_nat_def le_0_eq not0_implies_Suc pow_tensor.simps(2))

lemma pow_tensor_mult_distr:
  assumes "n \<ge> 1"
  and "dim_col A = dim_row B" and "0 < dim_row B" and "0 < dim_col B"
  shows "(A ^\<^sub>\<otimes> (Suc n))*(B ^\<^sub>\<otimes> (Suc n)) = (A * B) \<Otimes> ((A ^\<^sub>\<otimes> n)*(B ^\<^sub>\<otimes> n))" 
proof -
  have "(A ^\<^sub>\<otimes> (Suc n))*(B ^\<^sub>\<otimes> (Suc n)) = (A \<Otimes> (A ^\<^sub>\<otimes> n)) * (B  \<Otimes> (B ^\<^sub>\<otimes> n))" 
    using Suc_le_D assms(1) by fastforce
  then show "(A ^\<^sub>\<otimes> (Suc n))*(B ^\<^sub>\<otimes> (Suc n)) =  (A * B) \<Otimes> ((A ^\<^sub>\<otimes> n)*(B ^\<^sub>\<otimes> n))" 
    using mult_distr_tensor [of A B "(pow_tensor A n)" "(pow_tensor B n)"] assms
    by auto
qed

lemma index_tensor_mat_vec2_i_smaller_row_B: (*Better name would be welcome. index_tensor_mat_vec2_1? *)
  fixes A B:: "complex Matrix.mat" and i:: "nat" 
assumes "i < dim_row B" 
    and "dim_row A = 2"
    and "dim_col A = 1"
    and "0 < dim_col B" 
  shows "(A \<Otimes> B) $$ (i, 0) = (A  $$ (0, 0)) * (B $$ (i,0))" 
using index_tensor_mat assms by auto

lemma index_tensor_mat_vec2_i_greater_row_B:
  fixes A B:: "complex Matrix.mat" 
  and     i:: "nat" 
  assumes "i < (dim_row A) * (dim_row B)" 
      and "0 < (dim_col A) * (dim_col B)" 
      and "i \<ge> dim_row B"
      and "dim_row A = 2"
      and "dim_col A = 1"
  shows "(A \<Otimes> B) $$ (i, 0) = (A  $$ (1, 0)) * (B $$ ( i -dim_row B,0))"
proof -
  have "(A \<Otimes> B) $$ (i,0) = A $$ (i div (dim_row B), 0) * B $$ (i mod (dim_row B),0)"
    using assms index_tensor_mat[of A "dim_row A" "dim_col A" B "dim_row B" "dim_col B" i 0]
    by auto
  moreover have "i div (dim_row B) = 1" 
    using assms(1) assms(3) assms(4) 
    by simp
  then  have "i mod (dim_row B) = i - (dim_row B)" 
    by (simp add: modulo_nat_def)
  ultimately show "(A \<Otimes> B) $$ (i, 0) = (A  $$ (1, 0)) * (B $$ ( i -dim_row B,0))" 
    by (simp add: \<open>i div dim_row B = 1\<close>)
qed


lemma pow_tensor_gate:
  fixes A :: "complex Matrix.mat" 
  and     n m:: "nat" 
  assumes "gate m A" 
      and "n\<ge>1" 
  shows "gate (m*n) (A ^\<^sub>\<otimes> n)"
proof (induction n rule: ind_from_1)
  show "n \<ge> 1" using assms by auto
next
  show "gate (m*1) (A ^\<^sub>\<otimes> 1)" using assms by auto
next
  fix n
  assume IH: "gate (m*n) (A ^\<^sub>\<otimes> n)"
      and a0: "n\<ge>1"
  then have "A ^\<^sub>\<otimes> (Suc n) = A \<Otimes> (A ^\<^sub>\<otimes> n)" 
    by (simp add: pow_tensor_n)
  moreover have "gate (m*n+m) (A ^\<^sub>\<otimes> (Suc n))"  
    using tensor_gate assms 
    by (simp add: IH add.commute calculation(1))
  then show "gate (m*(Suc n)) (A ^\<^sub>\<otimes> (Suc n))" 
    by (simp add: add.commute)
qed



text \<open>
n+1 qubits are prepared. 
The first n in the state $|0\rangle$, the last one in the state $|1\rangle$.
\<close>

abbreviation zero where "zero \<equiv> unit_vec 2 0"
abbreviation one where "one \<equiv> unit_vec 2 1"

lemma ket_zero_is_state: 
  shows "state 1 |zero\<rangle>"
  by (simp add: state_def ket_vec_def cpx_vec_length_def numerals(2))

lemma ket_one_is_state:
  shows "state 1 |one\<rangle>" 
  by (simp add: state_def ket_vec_def cpx_vec_length_def numerals(2))


abbreviation \<psi>\<^sub>1\<^sub>0:: "nat \<Rightarrow> complex Matrix.mat" where
"\<psi>\<^sub>1\<^sub>0 n \<equiv> Matrix.mat (2^n) 1 (\<lambda>(i,j). 1/(sqrt(2))^n)" (*start with 0 rather than 1? but then until 2^n-1*)

lemma \<psi>\<^sub>1\<^sub>0_values:
  fixes i j n
  assumes "i < dim_row (\<psi>\<^sub>1\<^sub>0 n)"
  and "j < dim_col (\<psi>\<^sub>1\<^sub>0 n)"
  and "n \<ge> 1"
  shows "(\<psi>\<^sub>1\<^sub>0 n) $$ (i,j) = 1/(sqrt(2)^n)" 
  using assms(1) assms(2) case_prod_conv by auto


text \<open>
$H^{\otimes n}$ is applied to $|0\rangle^{\otimes n}$. 
\<close>

lemma H_on_ket_zero: 
  shows "(H *  |zero\<rangle>) = (\<psi>\<^sub>1\<^sub>0 1)"
proof 
  fix i j:: nat
  assume a0: "i < dim_row (\<psi>\<^sub>1\<^sub>0 1)" 
     and a1: "j < dim_col (\<psi>\<^sub>1\<^sub>0 1)"
  then have f1: "i \<in> {0,1} \<and> j = 0" by (simp add: less_2_cases)
  then show "(H * |zero\<rangle>) $$ (i,j) = (\<psi>\<^sub>1\<^sub>0 1) $$ (i,j)"
    by (auto simp add: times_mat_def scalar_prod_def H_def ket_vec_def)
next
  show "dim_row (H * |zero\<rangle>) = dim_row (\<psi>\<^sub>1\<^sub>0 1)"  by (simp add: H_def)
next 
  show "dim_col (H * |zero\<rangle>) = dim_col (\<psi>\<^sub>1\<^sub>0 1)" using H_def  
    by (simp add: ket_vec_def)
qed

lemma H_on_ket_zero_is_state: 
  shows "state 1 (H * |zero\<rangle>)"
proof
  show "gate 1 H" 
    using H_is_gate by simp
next
  show "state 1 |zero\<rangle>" 
    using ket_zero_is_state by simp
qed

lemma \<psi>\<^sub>1\<^sub>0_tensor_n: 
  assumes "n \<ge> 1"
  shows "(\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n) = (\<psi>\<^sub>1\<^sub>0 (Suc n))"
proof
  have "dim_row (\<psi>\<^sub>1\<^sub>0 1) * dim_row (\<psi>\<^sub>1\<^sub>0 n)  =  2^(Suc n)" by simp 
  then show "dim_row ((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) = dim_row (\<psi>\<^sub>1\<^sub>0 (Suc n))" by auto
next
  have "dim_col (\<psi>\<^sub>1\<^sub>0 1) * dim_col (\<psi>\<^sub>1\<^sub>0 n)  =  1" by simp
  then show "dim_col ((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) = dim_col (\<psi>\<^sub>1\<^sub>0 (Suc n))" by auto
next
  fix i j:: nat
  assume a0: "i < dim_row (\<psi>\<^sub>1\<^sub>0 (Suc n))" and a1: "j < dim_col (\<psi>\<^sub>1\<^sub>0 (Suc n))"
  then have f0: "j = 0" and f1: "i< 2^(Suc n)" by auto
  then have f2: "(\<psi>\<^sub>1\<^sub>0 (Suc n)) $$ (i,j) = 1/(sqrt(2)^(Suc n))" 
    using  \<psi>\<^sub>1\<^sub>0_values[of i "(Suc n)" j] a0 a1 by auto
  show "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,j) = (\<psi>\<^sub>1\<^sub>0 (Suc n)) $$ (i,j)" 
  proof (rule disjE) (*case distinction*)
    show "i < dim_row (\<psi>\<^sub>1\<^sub>0 n) \<or> i \<ge> dim_row (\<psi>\<^sub>1\<^sub>0 n)" by linarith
  next (* case i < dim_row (\<psi>\<^sub>1\<^sub>0 n) *)
    assume a2: "i < dim_row (\<psi>\<^sub>1\<^sub>0 n)"
    then have "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,j) = (\<psi>\<^sub>1\<^sub>0 1) $$ (0,0) * (\<psi>\<^sub>1\<^sub>0 n) $$ (i,0)"
      using index_tensor_mat f0 assms by simp
    also have "... = 1/sqrt(2) * 1/(sqrt(2)^n)"
      using \<psi>\<^sub>1\<^sub>0_values a2 assms by auto
    finally show  "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,j) = (\<psi>\<^sub>1\<^sub>0 (Suc n)) $$ (i,j)" 
      using f2 divide_divide_eq_left power_Suc by simp
  next (* case i \<ge> dim_row (\<psi>\<^sub>1\<^sub>0 n) *)
    assume "i \<ge> dim_row (\<psi>\<^sub>1\<^sub>0 n)"
    then have "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,0) = ((\<psi>\<^sub>1\<^sub>0 1)  $$ (1, 0)) * ((\<psi>\<^sub>1\<^sub>0 n) $$ ( i -dim_row (\<psi>\<^sub>1\<^sub>0 n),0))"
      using index_tensor_mat_vec2_i_greater_row_B[of i "(\<psi>\<^sub>1\<^sub>0 1)" "(\<psi>\<^sub>1\<^sub>0 n)" ] a0 a1 f0  
      by auto
    then have "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,0) = 1/sqrt(2) * 1/(sqrt(2)^n)"
      using \<psi>\<^sub>1\<^sub>0_values[of "i -dim_row (\<psi>\<^sub>1\<^sub>0 n)" n j] a0 a1 by auto
    then show  "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,j) = (\<psi>\<^sub>1\<^sub>0 (Suc n)) $$ (i,j)" 
      using f0 f1 divide_divide_eq_left power_Suc 
      by auto
  qed
qed

lemma \<psi>\<^sub>1\<^sub>0_tensor_n_is_state:
  assumes "n \<ge> 1"
  shows "state n ( |zero\<rangle> ^\<^sub>\<otimes> n)"
proof (induction n rule: ind_from_1)
  show "n \<ge> 1" using assms by auto
next
  show "state 1 ( |zero\<rangle> ^\<^sub>\<otimes> 1)" using ket_zero_is_state by auto
next
  fix n
  assume a0: "state n ( |zero\<rangle> ^\<^sub>\<otimes> n)" and "n\<ge>1"
  then have "( |zero\<rangle>) ^\<^sub>\<otimes> (Suc n) = ( |zero\<rangle>)  \<Otimes>  ( |zero\<rangle> ^\<^sub>\<otimes> n)" 
    using assms pow_tensor_n[of n "|zero\<rangle>" ] by auto
  then show "state (Suc n) ( |zero\<rangle> ^\<^sub>\<otimes> (Suc n))" 
    using assms tensor_state a0 ket_zero_is_state by fastforce
qed


lemma H_tensor_n_is_gate:
  assumes "n \<ge> 1"
  shows "gate n (H ^\<^sub>\<otimes> n)" 
proof(induction n rule: ind_from_1)
  show "n \<ge> 1" using assms by auto
next
  show "gate 1 (H ^\<^sub>\<otimes> 1)" 
    using H_is_gate by auto
next
  fix n 
  assume a0: "gate n (H ^\<^sub>\<otimes> n)" and "n \<ge> 1"
  then have "(H ^\<^sub>\<otimes> (Suc n)) = H \<Otimes> (H ^\<^sub>\<otimes> n)" 
    using pow_tensor_n[of n H] by auto
  then show "gate (Suc n) (H ^\<^sub>\<otimes> (Suc n))" 
    using assms a0 tensor_gate H_is_gate by fastforce
qed



lemma H_tensor_n_on_zero_tensor_n: 
  assumes "n \<ge> 1"
  shows "(H ^\<^sub>\<otimes> n) * ( |zero\<rangle> ^\<^sub>\<otimes> n) = (\<psi>\<^sub>1\<^sub>0 n)"  
proof (induction n rule: ind_from_1)
  show "n\<ge>1" using assms by auto
next
  have "(H ^\<^sub>\<otimes> 1) * ( |zero\<rangle> ^\<^sub>\<otimes> 1) = H * |zero\<rangle>" by auto
  show "(H ^\<^sub>\<otimes> 1) * ( |zero\<rangle> ^\<^sub>\<otimes> 1) = (\<psi>\<^sub>1\<^sub>0 1)" using H_on_ket_zero by auto
next
  fix n
  assume a0: "1 \<le> n" and a1: "(H ^\<^sub>\<otimes> n) * ( |zero\<rangle> ^\<^sub>\<otimes> n) = (\<psi>\<^sub>1\<^sub>0 n)" 
  then have "(H ^\<^sub>\<otimes> (Suc n)) * ( |zero\<rangle> ^\<^sub>\<otimes> (Suc n)) = (H * |zero\<rangle>) \<Otimes> ((H ^\<^sub>\<otimes> n) * ( |zero\<rangle> ^\<^sub>\<otimes> n))" 
    using pow_tensor_mult_distr[of n "H" "|zero\<rangle>"] a0 ket_vec_def H_def
    by (simp add: H_def)
  also have  "... = (H * |zero\<rangle>) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)" using a1 by auto 
  also have "... = (\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)" using H_on_ket_zero by auto
  also have "... = (\<psi>\<^sub>1\<^sub>0 (Suc n))" using \<psi>\<^sub>1\<^sub>0_tensor_n a0 by auto
  finally show "(H ^\<^sub>\<otimes> (Suc n)) * ( |zero\<rangle> ^\<^sub>\<otimes> (Suc n)) = (\<psi>\<^sub>1\<^sub>0 (Suc n))" by auto
qed



lemma \<psi>\<^sub>1\<^sub>0_is_state:
  assumes "n \<ge> 1"
  shows "state n (\<psi>\<^sub>1\<^sub>0 n)"
  using H_tensor_n_is_gate \<psi>\<^sub>1\<^sub>0_tensor_n_is_state assms gate_on_state_is_state H_tensor_n_on_zero_tensor_n assms
  by metis


abbreviation \<psi>\<^sub>1\<^sub>1:: "complex Matrix.mat" where
"\<psi>\<^sub>1\<^sub>1 \<equiv> Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else -1/sqrt(2))"


lemma H_on_ket_one_is_\<psi>\<^sub>1\<^sub>1: 
  shows "(H * |one\<rangle>) = \<psi>\<^sub>1\<^sub>1"
proof 
  fix i j:: nat
  assume "i < dim_row \<psi>\<^sub>1\<^sub>1" and "j < dim_col \<psi>\<^sub>1\<^sub>1"
  then have "i \<in> {0,1} \<and> j = 0" by (simp add: less_2_cases)
  then show "(H * |one\<rangle>) $$ (i,j) = \<psi>\<^sub>1\<^sub>1 $$ (i,j)"
    by (auto simp add: times_mat_def scalar_prod_def H_def ket_vec_def)
next
  show "dim_row (H * |one\<rangle>) = dim_row \<psi>\<^sub>1\<^sub>1" by (simp add: H_def)
next 
  show "dim_col (H * |one\<rangle>) = dim_col \<psi>\<^sub>1\<^sub>1" by (simp add: H_def ket_vec_def)
qed

lemma \<psi>\<^sub>1\<^sub>1_is_state: 
  shows "state 1 (H * |one\<rangle>)"
  using H_is_gate ket_one_is_state by simp



abbreviation \<psi>\<^sub>1:: "nat \<Rightarrow> complex Matrix.mat" where
"\<psi>\<^sub>1 n \<equiv> Matrix.mat (2^(n+1))  1 (\<lambda>(i,j). if (even i) then 1/(sqrt(2)^(n+1)) else -1/(sqrt(2)^(n+1)))"

lemma \<psi>\<^sub>1_values_even[simp]:
  fixes i j n
  assumes "i < dim_row (\<psi>\<^sub>1 n)"
  and "j < dim_col (\<psi>\<^sub>1 n)"
  and "n \<ge> 1"
  and "even i"
  shows "(\<psi>\<^sub>1 n) $$ (i,j) = 1/(sqrt(2)^(n+1))" 
  using assms case_prod_conv by auto

lemma \<psi>\<^sub>1_values_odd [simp]:
  fixes i j n
  assumes "i < dim_row (\<psi>\<^sub>1 n)"
  and "j < dim_col (\<psi>\<^sub>1 n)"
  and "n \<ge> 1"
  and "odd i"
  shows "(\<psi>\<^sub>1 n) $$ (i,j) = -1/(sqrt(2)^(n+1))" 
  using assms case_prod_conv by auto


lemma "\<psi>\<^sub>1\<^sub>0_tensor_\<psi>\<^sub>1\<^sub>1_is_\<psi>\<^sub>1":
  assumes "n \<ge> 1"
  shows "(\<psi>\<^sub>1\<^sub>0 n) \<Otimes> \<psi>\<^sub>1\<^sub>1 = (\<psi>\<^sub>1 n)" 
proof 
 show "dim_col ((\<psi>\<^sub>1\<^sub>0 n) \<Otimes> \<psi>\<^sub>1\<^sub>1) = dim_col (\<psi>\<^sub>1 n)" by auto
next
  show "dim_row ((\<psi>\<^sub>1\<^sub>0 n) \<Otimes> \<psi>\<^sub>1\<^sub>1) = dim_row (\<psi>\<^sub>1 n)" by auto
next
  fix i j::nat
  assume a0: "i < dim_row (\<psi>\<^sub>1 n)" and a1: "j < dim_col (\<psi>\<^sub>1 n)"
  then have "i < 2^(n+1)" and "j = 0" by auto 
  then have f0: "((\<psi>\<^sub>1\<^sub>0 n) \<Otimes> \<psi>\<^sub>1\<^sub>1) $$ (i,j) = 1/(sqrt(2)^n) * \<psi>\<^sub>1\<^sub>1 $$ (i mod 2, j)" 
    using \<psi>\<^sub>1\<^sub>0_values[of "i div 2" n "j div 1"] a0 a1 by auto
  show "((\<psi>\<^sub>1\<^sub>0 n) \<Otimes> \<psi>\<^sub>1\<^sub>1) $$ (i,j) = (\<psi>\<^sub>1 n) $$ (i,j)" using f0 \<psi>\<^sub>1_values_even \<psi>\<^sub>1_values_odd a0 a1 by auto 
(*I have a longer proof with case distinction even i \<or> odd i for this which one is nicer?*)
qed

lemma \<psi>\<^sub>1_is_state:
  assumes "n \<ge> 1"
  shows "state (n+1) (\<psi>\<^sub>1 n)" 
  using \<psi>\<^sub>1\<^sub>0_tensor_\<psi>\<^sub>1\<^sub>1_is_\<psi>\<^sub>1  \<psi>\<^sub>1\<^sub>0_is_state assms  \<psi>\<^sub>1\<^sub>1_is_state assms H_on_ket_one_is_\<psi>\<^sub>1\<^sub>1 tensor_state by metis


abbreviation (in jozsa) \<psi>\<^sub>2:: "complex Matrix.mat" where
"\<psi>\<^sub>2 \<equiv> Matrix.mat (2^(n+1)) 1 (\<lambda>(i,j). if (even i) then ((1-f(i div 2))+-f(i div 2)) * 1/(sqrt(2)^(n+1)) 
                                      else (-(1-f(i div 2))+(f(i div 2)))* 1/(sqrt(2)^(n+1)))"

(* Would this be much better?
"\<psi>\<^sub>2 \<equiv> Matrix.mat (2^(n+1)) 1 (\<lambda>(i,j). if (even i) then (1-2*f(i div 2))/(sqrt(2)^(n+1)) 
                                      else (-1+2*f(i div 2))/(sqrt(2)^(n+1)))"*)

(*Edit: see below I showed that this is equivalent to (-1)^f(i div 2) resp. (-1)^(f(i div 2)+1)
This could also be used here and the proof below integrated in jozsa_transform_times_\<psi>\<^sub>1_is_\<psi>\<^sub>2*)

lemma (in jozsa) \<psi>\<^sub>2_values_even[simp]:
  fixes i j 
  assumes "i < dim_row \<psi>\<^sub>2 "
  and "j < dim_col \<psi>\<^sub>2 "
  and "even i"
  shows "\<psi>\<^sub>2  $$ (i,j) = ((1-f(i div 2))+-f(i div 2)) * 1/(sqrt(2)^(n+1))" 
  using assms case_prod_conv by simp

lemma (in jozsa) \<psi>\<^sub>2_values_odd[simp]:
  fixes i j 
  assumes "i < dim_row \<psi>\<^sub>2 "
  and "j < dim_col \<psi>\<^sub>2 "
  and "odd i"
  shows "\<psi>\<^sub>2  $$ (i,j) = (-(1-f(i div 2))+(f(i div 2)))* 1/(sqrt(2)^(n+1))" 
  using assms case_prod_conv by simp


lemma (in jozsa) jozsa_transform_times_\<psi>\<^sub>1_is_\<psi>\<^sub>2:
  shows "U\<^sub>f * (\<psi>\<^sub>1 n) = \<psi>\<^sub>2 " 
proof 
  show "dim_row (U\<^sub>f * (\<psi>\<^sub>1 n)) = dim_row \<psi>\<^sub>2 " by simp
next
  show "dim_col (U\<^sub>f * (\<psi>\<^sub>1 n)) = dim_col \<psi>\<^sub>2 " by simp
next
  fix i j ::nat
  assume a0: "i < dim_row \<psi>\<^sub>2" and a1: "j < dim_col \<psi>\<^sub>2"
  then have f0:"i \<in> {0..2^(n+1)} \<and> j=0" by auto
  then have f1: "i < dim_row U\<^sub>f \<and> j < dim_col U\<^sub>f " using a0 by auto
  have f2: "i < dim_row (\<psi>\<^sub>1 n) \<and> j < dim_col (\<psi>\<^sub>1 n)" using a0 a1 by auto
  show "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = \<psi>\<^sub>2 $$ (i,j)"
  proof (rule disjE)
    show "even i \<or> odd i" by auto
  next
    assume a2: "even i"
    then have "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = (\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i, k) * (\<psi>\<^sub>1 n)$$ (k, j))"
      using f1 f2 U\<^sub>f_mult_without_empty_summands_even[of i j "(\<psi>\<^sub>1 n)"] by auto 
    moreover have "U\<^sub>f $$ (i, i) * (\<psi>\<^sub>1 n)$$ (i, j) = (1-f(i div 2))* 1/(sqrt(2)^(n+1))" 
      using f0 f1 a2 by auto
    moreover have "U\<^sub>f $$ (i, i+1) * (\<psi>\<^sub>1 n)$$ (i+1, j) = (-f(i div 2))* 1/(sqrt(2)^(n+1))" 
      using f0 f1 a2 by auto
    ultimately have "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = (1-f(i div 2))* 1/(sqrt(2)^(n+1)) + (-f(i div 2))* 1/(sqrt(2)^(n+1))" 
      by auto
    also have "... = ((1-f(i div 2))+-f(i div 2)) * 1/(sqrt(2)^(n+1))" 
      using add_divide_distrib 
      by (metis (no_types, hide_lams) mult.right_neutral of_int_add of_int_of_nat_eq)
    also have "... =  \<psi>\<^sub>2 $$ (i,j)" 
      using a0 a1 a2 by auto
    finally show "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = \<psi>\<^sub>2 $$ (i,j)" by auto
  next 
    assume a2: "odd i"
    then have f6: "i\<ge>1"  
    using linorder_not_less by auto
    have "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = (\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i, k) * (\<psi>\<^sub>1 n)$$ (k, j))"
      using f1 f2 a2 U\<^sub>f_mult_without_empty_summands_odd[of i j "(\<psi>\<^sub>1 n)"]  
      by (metis dim_row_mat(1) jozsa_transform_dim(2)) 
    moreover have "(\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i, k) * (\<psi>\<^sub>1 n) $$ (k, j)) 
                 = U\<^sub>f $$ (i, i-1) * (\<psi>\<^sub>1 n) $$ (i-1, j) +  U\<^sub>f $$ (i, i) * (\<psi>\<^sub>1 n) $$ (i, j)" 
      using a2 f6 by auto
    moreover have  "U\<^sub>f $$ (i, i) * (\<psi>\<^sub>1 n)$$ (i, j) = (1-f(i div 2))* -1/(sqrt(2)^(n+1))" 
      using f1 f2 a2 by auto
    moreover have "U\<^sub>f $$ (i, i-1) * (\<psi>\<^sub>1 n)$$ (i-1, j) = f(i div 2)* 1/(sqrt(2)^(n+1))" 
      using a0 a1 a2 by auto
    ultimately have "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = (1-f(i div 2))* -1/(sqrt(2)^(n+1)) +(f(i div 2))* 1/(sqrt(2)^(n+1))" 
       using of_real_add by auto
     also have "... = ( -(1-f(i div 2)) + (f(i div 2)))* 1/(sqrt(2)^(n+1))" 
       by (metis (no_types, hide_lams) mult.right_neutral add_divide_distrib mult_minus1_right 
           of_int_add of_int_of_nat_eq)
     finally show "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = \<psi>\<^sub>2 $$ (i,j)" 
       using a0 a1 a2 by auto
  qed
qed

lemma (in jozsa) \<psi>\<^sub>2_is_state:
  shows "state (n+1) \<psi>\<^sub>2" 
  using jozsa_transform_times_\<psi>\<^sub>1_is_\<psi>\<^sub>2 jozsa_transform_is_gate \<psi>\<^sub>1_is_state dim gate_on_state_is_state by fastforce


(*TODO: Should this be integrated into the last proof and \<psi>\<^sub>2 replaced by \<psi>\<^sub>2'?*)
abbreviation (in jozsa) \<psi>\<^sub>2':: "complex Matrix.mat" where
"\<psi>\<^sub>2' \<equiv> Matrix.mat (2^(n+1)) 1 (\<lambda>(i,j). if (even i) then ((-1)^f(i div 2))/(sqrt(2)^(n+1)) 
                                      else ((-1)^(f(i div 2)+1))/(sqrt(2)^(n+1)))"

lemma  (in jozsa) \<psi>\<^sub>2'_values[simp]:
  assumes "2*k+1 < dim_row \<psi>\<^sub>2'" 
     and "j < dim_col \<psi>\<^sub>2'" 
   shows "(\<psi>\<^sub>2' $$ (2*k+1,j)) = ((-1)^(f((2*k+1) div 2)+1))/(sqrt(2)^(n+1))" using assms by auto



lemma (in jozsa) \<psi>\<^sub>2_is_\<psi>\<^sub>2':
  shows "\<psi>\<^sub>2 = \<psi>\<^sub>2'"
proof
  show "dim_row \<psi>\<^sub>2 = dim_row \<psi>\<^sub>2'" by simp
next
  show "dim_col \<psi>\<^sub>2 = dim_col \<psi>\<^sub>2'" by simp
next
  fix i j::nat
  assume a0:"i < dim_row \<psi>\<^sub>2'" and a1:"j < dim_col \<psi>\<^sub>2'"
  show "\<psi>\<^sub>2 $$ (i,j) = \<psi>\<^sub>2' $$ (i,j)" 
  proof (rule disjE)
    show "even i \<or> odd i" by auto
  next
    assume a2: "even i"
    then have f0: "\<psi>\<^sub>2 $$ (i,j) = ((1-f(i div 2))+-f(i div 2)) * 1/(sqrt(2)^(n+1))" 
      using a0 a1 by auto
    have "i div 2 \<in> {i. i < 2 ^ n}" 
      using a0 by auto
    then have " real (Suc 0 - f (i div 2)) - real (f (i div 2)) = (- 1) ^ f (i div 2)" 
      using a0 f_values by fastforce
    then have "((1-f(i div 2))+-f(i div 2)) * 1/(sqrt(2)^(n+1)) = (-1)^f(i div 2)/(sqrt(2)^(n+1))"
      using f_values a0 a1 by auto
    then show "\<psi>\<^sub>2 $$ (i,j) = \<psi>\<^sub>2' $$ (i,j)" using f0 a0 a1 a2 by auto
  next
    assume a2: "odd i"
    then have f0: "\<psi>\<^sub>2 $$ (i,j) = (-(1-f(i div 2))+f(i div 2)) * 1/(sqrt(2)^(n+1))" 
      using a0 a1 by auto
    have "i div 2 \<in> {i. i < 2 ^ n}" 
      using a0 by auto
    then have "(real (f (i div 2)) - real (Suc 0 - f (i div 2))) / (sqrt 2 ^ (n+1)) =
    - ((- 1) ^ f (i div 2) / (sqrt 2 ^ (n+1)))" 
      using a0 f_values by fastforce
    then have "(-(1-f(i div 2))+f(i div 2)) * 1/(sqrt(2)^(n+1)) = (-1)^(f(i div 2)+1)/(sqrt(2)^(n+1))"
      using f_values a0 a1 by auto
    then show "\<psi>\<^sub>2 $$ (i,j) = \<psi>\<^sub>2' $$ (i,j)" using f0 a0 a1 a2 by auto
  qed
qed


(*THIS SECTION STILL NEEDS SOME TIDYING UP*)
subsection "Bitwise inner product"


definition bitwise_inner_prod:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where 
"bitwise_inner_prod n i j = (\<Sum>k\<in>{0..<n}. (bin_rep n i)!k * (bin_rep n j)!k)"

abbreviation bip:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" ("_ \<cdot>\<^bsub>_\<^esub>  _") where
"bip i n j \<equiv> bitwise_inner_prod n i j"

lemma bin_rep_geq_0:  (*I had to restore this since bin_rep_coeff uses the assumption that i\<le>2^n*)
  assumes "i \<ge> 0"
  and "n\<ge>1"
  shows "k\<in>{0..<n} \<longrightarrow> bin_rep n i!k \<ge>0" 
proof (induction n rule: ind_from_1)
  show "n\<ge>1" using assms by auto
next
  have "(bin_rep 1 i)!0 \<ge> 0" using bin_rep_def assms by auto
  then show "k\<in>{0..<1}\<longrightarrow>bin_rep 1 i!k \<ge>0" using bin_rep_def bin_rep_aux_def assms 
    by (metis One_nat_def atLeastLessThan_iff less_Suc0)
next
  fix n
  assume a0: "n\<ge>1"
  and IH: "k\<in>{0..<n} \<longrightarrow> bin_rep n i!k \<ge>0" (*IH is not used if proof stays maybe restructure it*)
  moreover have "k \<in> {0..<Suc n} \<longrightarrow> k \<in> {0..<n} \<or> k \<in> {n}" by auto
  moreover have "k \<in> {n} \<longrightarrow> bin_rep (Suc n) i!k \<ge> 0" 
    by (smt pos_mod_bound pos_mod_sign One_nat_def a0 bin_rep_aux.simps(2) bin_rep_aux_neq_nil 
        bin_rep_coeff bin_rep_def butlast.simps(2) diff_diff_cancel diff_is_0_eq le_less_linear 
        less_Suc0 nth_Cons' one_neq_zero singleton_iff zero_less_power) 
  moreover have "k \<in> {0..<n} \<longrightarrow> bin_rep (Suc n) i!k \<ge> 0" 
  proof
    {assume a2: "k \<in> {0..<n}"
    have "bin_rep (Suc n) i!k = (butlast (i div 2^n # bin_rep_aux n (i mod 2^n)))!k" 
      using bin_rep_def bin_rep_aux_def by auto 
    also have "... = (i div 2^n # (butlast ( bin_rep_aux n (i mod 2^n))))!k" 
      by (simp add: bin_rep_aux_neq_nil)
    also have "... = (i div 2^n # bin_rep n (i mod 2^n))!k" 
      using bin_rep_def bin_rep_aux_def by auto
    moreover have "k \<in> {0} \<or> k \<in> {1..<n}" using a2 by auto
    moreover have "k=0 \<longrightarrow>(i div 2^n # bin_rep n (i mod 2^n))!k \<ge> 0"
      by (simp add: assms(1) pos_imp_zdiv_nonneg_iff)
    moreover have "k\<in>{1..<n} \<longrightarrow>(i div 2^n # bin_rep n (i mod 2^n))!k \<ge> 0"
      by (smt Euclidean_Division.pos_mod_bound Euclidean_Division.pos_mod_sign One_nat_def Suc_pred 
          atLeastLessThan_iff bin_rep_coeff le_trans lessI less_imp_le_nat not_less nth_Cons' zero_less_power)
    ultimately show "bin_rep (Suc n) i ! k \<ge> 0" 
      using bin_rep_def bin_rep_aux_def assms 
      by (metis singleton_iff)}
  qed
  ultimately show "k\<in>{0..<(Suc n)} \<longrightarrow> bin_rep (Suc n) i!k \<ge>0" by blast
qed

lemma bitwise_inner_prod_geq_0:
  assumes "i \<ge> 0 \<and> j\<ge>0"
  and "n\<ge>1"
  shows "bitwise_inner_prod n i j \<ge> 0" 
proof-
    have "k\<in>{0..<n} \<longrightarrow> (bin_rep n i)!k \<ge> 0" for k 
      using bin_rep_geq_0 by auto 
    moreover have "k\<in>{0..<n} \<longrightarrow> (bin_rep n j)!k \<ge> 0" for k 
      using bin_rep_geq_0 by auto 
    ultimately show "bitwise_inner_prod n i j \<ge> 0" 
      using bitwise_inner_prod_def 
      by (metis (no_types, lifting) mult_nonneg_nonneg sum_nonneg)
qed


abbreviation tensor_of_H:: "nat \<Rightarrow> complex Matrix.mat" ("H\<^sup>\<otimes>\<^bsup>_\<^esup>") where
"tensor_of_H n \<equiv> Matrix.mat (2^n) (2^n) (\<lambda>(i,j).(-1)^(nat(i \<cdot>\<^bsub>n\<^esub> j))/(sqrt(2)^n))"

lemma tensor_of_H_values [simp]:
  fixes n i j:: nat
  assumes "n \<ge> 1" and "i < dim_row (H\<^sup>\<otimes>\<^bsup>n\<^esup>)" and "j < dim_col (H\<^sup>\<otimes>\<^bsup>n\<^esup>)"
  shows "(H\<^sup>\<otimes>\<^bsup>n\<^esup>) $$ (i,j) = (-1)^(nat(i \<cdot>\<^bsub>n\<^esub> j))/(sqrt(2)^n)"
  using assms by simp

lemma bin_rep_index_0: (*This could go into Binary_Nat but it could also stay here? If its not already there*)
  fixes n:: nat and m:: int
  assumes "m < 2^n" and "m \<ge> 0"
  shows "(bin_rep (n+1) m) ! 0 = 0"
proof-
  have "butlast (0 # bin_rep_aux n m) = 0 # butlast(bin_rep_aux n m)"
    using assms length_of_bin_rep_aux by(metis Suc_eq_plus1 butlast.simps(2) list.size(3) nat.simps(3))
  then show "(bin_rep (n+1) m) ! 0 = 0"
    using bin_rep_def assms by simp
qed

lemma [simp]: (*Give name if stays*)
"(int i mod 2^n) = (int (i mod 2^n))" 
  by (simp add: of_nat_mod)

lemma bitwise_inner_prod_fst_el_0: 
  assumes "i < 2^n \<or> j < 2^n" and "i \<ge> 0 \<and> j \<ge> 0" and "i < 2^(n+1) \<and> j < 2^(n+1)" 
  shows "(i \<cdot>\<^bsub>n+1\<^esub> j) = (i mod 2^n) \<cdot>\<^bsub>n\<^esub> (j mod 2^n)" 
proof-
  have "(bip i (Suc n) j) = (\<Sum>k\<in>{0..<(Suc n)}. (bin_rep (Suc n) i)!k * (bin_rep (Suc n) j)!k)" 
    using bitwise_inner_prod_def by blast
  also have "... = (bin_rep (Suc n) i)!0 * (bin_rep (Suc n) j)!0 + 
             (\<Sum>k\<in>{1..<(Suc n)}. (bin_rep (Suc n) i)!k * (bin_rep (Suc n) j)!k)" 
    by (metis (no_types, lifting) One_nat_def sum.atLeast_Suc_lessThan zero_less_Suc)
  also have "... = (\<Sum>k\<in>{1..<(Suc n)}. (bin_rep (Suc n) i)!k * (bin_rep (Suc n) j)!k)"
    using bin_rep_index_0[of i n] bin_rep_index_0[of j n] assms by auto
  also have "... = (\<Sum>k\<in>{0..<n}. (bin_rep (Suc n) i)!(k+1) * (bin_rep (Suc n) j)!(k+1))" 
     using sum.shift_bounds_Suc_ivl[of "\<lambda>k. (bin_rep (Suc n) i)!k * (bin_rep (Suc n) j)!k" "0" "n"] 
     by (metis (no_types, lifting) One_nat_def add.commute plus_1_eq_Suc sum.cong)
  finally have "(bip i (Suc n) j) = (\<Sum>k\<in>{0..<n}. (bin_rep (Suc n) i)!(k+1) * (bin_rep (Suc n) j)!(k+1))" 
    by blast
  moreover have "k\<in>{0..n}\<longrightarrow>(bin_rep (Suc n) i)!(k+1) = (bin_rep n (i mod 2^n))!k" for k
    using assms bin_rep_def 
    by (metis (no_types, hide_lams) Suc_eq_plus1 of_nat_mod of_nat_numeral of_nat_power Suc_eq_plus1 
        bin_rep_aux.simps(2) bin_rep_aux_neq_nil butlast.simps(2) nth_Cons_Suc)
  moreover have "k\<in>{0..n}\<longrightarrow>(bin_rep (Suc n) j)!(k+1) = (bin_rep n (j mod 2^n))!k" for k 
  using assms bin_rep_def 
    by (metis (no_types, hide_lams) Suc_eq_plus1 of_nat_mod of_nat_numeral of_nat_power Suc_eq_plus1 
        bin_rep_aux.simps(2) bin_rep_aux_neq_nil butlast.simps(2) nth_Cons_Suc)
  ultimately show ?thesis
    using assms(1) bin_rep_index_0 bitwise_inner_prod_def by simp
qed

lemma [simp]: (*Give name if stays*)
  fixes i:: int  
  assumes "i \<ge> 2^n" and "i < 2^(n+1)" and "i \<ge> 0" 
  shows "(i div 2^n) = 1" 
proof-
  have "i = nat i" using assms by auto
  then have "((nat i) div 2^n) = 1" 
    by (metis Suc_1 Suc_eq_plus1 assms(1) assms(2) div_nat_eqI nat_less_numeral_power_cancel_iff 
        nat_mult_1_right of_nat_le_of_nat_power_cancel_iff of_nat_numeral power.simps(2) power_commutes)
  then show "(i div 2^n) = 1" 
    by (metis \<open>i = int (nat i)\<close> int_ops(2) int_ops(3) of_nat_power zdiv_int)
qed


lemma bin_rep_index_0_geq:  (*This could go into Binary_Nat but it could also stay here? If its not already there*)
  fixes n::nat and i:: int
  assumes "i \<ge> 2^n" and "i < 2^(n+1)"
  shows "(bin_rep (n+1) i) ! 0 = 1"
proof-
  have "(bin_rep (Suc n) i) =  butlast (bin_rep_aux (Suc n) i)" using bin_rep_def by auto
  then have "bin_rep_aux (Suc n) i = 1 # (bin_rep_aux n (i mod 2^n))" 
    using assms bin_rep_aux_def by simp
  moreover have "butlast (1# bin_rep_aux n i) = 1 # butlast(bin_rep_aux n i)"
    using assms length_of_bin_rep_aux Suc_eq_plus1 butlast.simps(2) nat.simps(3) by(metis bin_rep_aux_neq_nil)
  ultimately show ?thesis
    using bin_rep_def assms by (simp add: bin_rep_aux_neq_nil)
qed


(*TODO: There is some duplicate code with bitwise_inner_prod_fst_el_0. Might be nice 
to have an extra lemma for this. *)
lemma bitwise_inner_prod_fst_el_is_1:
  fixes n i j:: nat
  assumes "i \<ge> 2^n \<and> j \<ge> 2^n" and "i < 2^(n+1) \<and> j < 2^(n+1)" and "n \<ge> 1"
  shows "(i \<cdot>\<^bsub>(n+1)\<^esub> j) = 1 + ((i mod 2^n) \<cdot>\<^bsub>n\<^esub> (j mod 2^n))" 
proof-
  have "(bip i (Suc n) j) = (\<Sum>k\<in>{0..<(Suc n)}. (bin_rep (Suc n) i)!k * (bin_rep (Suc n) j)!k)" 
    using bitwise_inner_prod_def by blast
  also have "... = (bin_rep (Suc n) i)!0 * (bin_rep (Suc n) j)!0 + 
            (\<Sum>k\<in>{1..<(Suc n)}. (bin_rep (Suc n) i)!k * (bin_rep (Suc n) j)!k)" 
    by (metis (no_types, lifting) One_nat_def sum.atLeast_Suc_lessThan zero_less_Suc)
  also have "... = (1 + (\<Sum>k\<in>{1..<(Suc n)}. (bin_rep (Suc n) i)!k * (bin_rep (Suc n) j)!k))"
    using  bin_rep_index_0_geq[of n i] bin_rep_index_0_geq[of n j] assms
    by (metis (mono_tags, lifting) Suc_eq_plus1 add.right_neutral of_nat_Suc of_nat_le_iff of_nat_less_iff 
of_nat_power one_add_one power_0 power_add) 
  also have "... = 1 + (\<Sum>k\<in>{0..<n}. (bin_rep (Suc n) i)!(k+1) * (bin_rep (Suc n) j)!(k+1))" 
    using sum.shift_bounds_Suc_ivl[of "\<lambda>k. (bin_rep (Suc n) i)!k * (bin_rep (Suc n) j)!k" "0" "n"] 
    by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 sum.cong)
  finally have f0:"(bip i (Suc n) j) = 1 + (\<Sum>k\<in>{0..<n}. (bin_rep (Suc n) i)!(k+1) * (bin_rep (Suc n) j)!(k+1))"
    by blast
  have "k\<in>{0..<n} \<longrightarrow> 0 \<le> (bin_rep (Suc n) i)!(k+1) * (bin_rep (Suc n) j)!(k+1)" for k 
    using bin_rep_coeff[of "Suc n" "k+1" "i"] bin_rep_coeff[of "Suc n" "k+1" "j"] assms
     add.commute atLeastLessThan_iff bin_rep_coeff mult_eq_0_iff of_nat_0_le_iff of_nat_1 of_nat_Suc 
     of_nat_less_iff of_nat_power one_add_one plus_1_eq_Suc zero_less_Suc
    by (smt one_power2 power_Suc)
  have "(\<Sum>k\<in>{0..<n}. (bin_rep (Suc n) i) ! (k+1) * (bin_rep (Suc n) j) ! (k+1)) \<ge> 0" 
    by (meson \<open>\<And>k. k \<in> {0..<n} \<longrightarrow> 0 \<le> bin_rep (Suc n) (int i) ! (k + 1) * bin_rep (Suc n) (int j) ! (k + 1)\<close> sum_nonneg)
  then have "(bip i (Suc n) j) = 1 + (\<Sum>k\<in>{0..<n}. (bin_rep (Suc n) i)!(k+1) * (bin_rep (Suc n) j)!(k+1))"
    using f0 by linarith
  moreover have "k\<in>{0..n}\<longrightarrow>(bin_rep (Suc n) i)!(k+1) = (bin_rep n (i mod 2^n))!k" for k
    using assms bin_rep_def 
    by (metis (no_types, hide_lams) Suc_eq_plus1 of_nat_mod of_nat_numeral of_nat_power Suc_eq_plus1 
        bin_rep_aux.simps(2) bin_rep_aux_neq_nil butlast.simps(2) nth_Cons_Suc)
  moreover have "k\<in>{0..n}\<longrightarrow>(bin_rep (Suc n) j)!(k+1) = (bin_rep n (j mod 2^n))!k" for k 
  using assms bin_rep_def 
    by (metis (no_types, hide_lams) Suc_eq_plus1 of_nat_mod of_nat_numeral of_nat_power Suc_eq_plus1 
        bin_rep_aux.simps(2) bin_rep_aux_neq_nil butlast.simps(2) nth_Cons_Suc)
  ultimately show ?thesis
    using assms(1) bin_rep_index_0 bitwise_inner_prod_def by simp
qed


lemma tensor_of_H_next_dim:
  fixes n i j:: nat
  assumes "i < 2^n \<or> j < 2^n" and "n \<ge> 1" and "i < 2^(n+1) \<and>  j < 2^(n+1)"
  shows "(H\<^sup>\<otimes>\<^bsup>(n+1)\<^esup>) $$ (i,j) = 1/sqrt(2)* ((H\<^sup>\<otimes>\<^bsup>n\<^esup>) $$ (i mod 2^n, j mod 2^n))"
proof-
  have "(H\<^sup>\<otimes>\<^bsup>(n+1)\<^esup>) $$ (i,j) = (-1)^(nat(bip i (Suc n) j))/(sqrt(2)^(Suc n))" 
    using assms by simp
  moreover have "(bip i (Suc n) j) = (bip (i mod 2^n) n (j mod 2^n))" 
    using bitwise_inner_prod_fst_el_0 assms by simp
  moreover have "(H\<^sup>\<otimes>\<^bsup>n\<^esup>) $$ (i mod 2^n, j mod 2^n) = (-1)^(nat(bip (i mod 2^n) n (j mod 2^n)))/(sqrt(2)^n)" 
    by simp
  ultimately show ?thesis 
    using assms bitwise_inner_prod_def
    by (smt divide_divide_eq_left' left_minus_one_mult_self minus_one_mult_self mult.commute of_real_mult 
        power_Suc times_divide_eq_right)
qed

lemma Hn_first_factor_is_minus_sqrt_2:
  fixes n i j:: nat
  assumes "i \<ge> 2^n \<and> j \<ge> 2^n" and "n \<ge> 1" and "i < 2^(n+1) \<and>  j < 2^(n+1)" and "i \<ge> 0 \<and> j \<ge> 0"
  shows "(H\<^sup>\<otimes>\<^bsup>(n+1)\<^esup>) $$ (i,j) = -1/sqrt(2)* ((H\<^sup>\<otimes>\<^bsup>n\<^esup>) $$ (i mod 2^n, j mod 2^n)) "
proof-
  have "(H\<^sup>\<otimes>\<^bsup>(n+1)\<^esup>) $$ (i,j) = (-1)^(nat(bip i (n+1) j))/(sqrt(2)^(n+1))" 
    using assms by simp
  moreover have "(bip i (n+1) j) = 1 + (bip (i mod 2^n) n (j mod 2^n))" 
    using bitwise_inner_prod_fst_el_is_1 assms by simp
  moreover have "(-1)^(1 + (nat(bip (i mod 2^n) n (j mod 2^n))))/(sqrt(2)^(n+1)) 
                 = -1/sqrt(2) * (-1)^(nat(bip (i mod 2^n) n (j mod 2^n))) /(sqrt(2)^n)" 
    by simp
  moreover have "(H\<^sup>\<otimes>\<^bsup>n\<^esup>) $$ (i mod 2^n, j mod 2^n) = (-1)^(nat(bip (i mod 2^n) n (j mod 2^n)))/(sqrt(2)^n)" 
    by simp
  ultimately show ?thesis
    using assms bitwise_inner_prod_def Nat.Suc_eq_plus1 bitwise_inner_prod_geq_0 
    by (smt Suc_nat_eq_nat_zadd1 of_real_mult plus_1_eq_Suc times_divide_eq_right zero_order(1)) 
qed

lemma H_values: (*This should go in some other theory?*)
  fixes i j:: nat
  assumes "i < dim_row H" and "j < dim_col H" and "\<not>(i= 1 \<and> j=1)" 
  shows "H $$ (i,j) = 1/sqrt(2)" 
  using H_without_scalar_prod assms 
  by (smt One_nat_def case_prod_conv dim_col_mat(1) dim_row_mat(1) index_mat(1) less_2_cases)


lemma H_values_right_bottom: (*This should go in some other theory?*)
  fixes i j:: nat
  assumes "(i= 1 \<and> j=1)" 
  shows "H $$ (i,j) = -1/sqrt(2)" 
proof-
  have "i < dim_row H"  using assms 
    by (simp add: H_without_scalar_prod)
  moreover have "j < dim_col H" 
    by (simp add: H_without_scalar_prod assms)
  ultimately show ?thesis 
  using H_without_scalar_prod assms 
  by (smt case_prod_conv dim_row_mat(1) index_mat(1) minus_divide_left zero_neq_one)
qed

(*Todo: Clean up,delete unused facts*)
lemma H_tensor_tensor_of_H:   
  fixes n:: nat
  assumes "n \<ge> 1"
  shows  "H \<Otimes> H\<^sup>\<otimes>\<^bsup>n\<^esup> = H\<^sup>\<otimes>\<^bsup>n+1\<^esup>" 
proof
  fix i j:: nat
  assume a0: "i < dim_row (H\<^sup>\<otimes>\<^bsup>(n+1)\<^esup>)" and a1: "j < dim_col (H\<^sup>\<otimes>\<^bsup>n+1\<^esup>)"
  then have f0: "i\<in>{0..<2^(n+1)} \<and> j\<in>{0..<2^(n+1)}" by simp
  then have f1: "(H \<Otimes> H\<^sup>\<otimes>\<^bsup>n\<^esup>) $$ (i,j) = H $$ (i div (dim_row (H\<^sup>\<otimes>\<^bsup>n\<^esup>)), j div (dim_col (H\<^sup>\<otimes>\<^bsup>n\<^esup>))) 
                                 * (H\<^sup>\<otimes>\<^bsup>n\<^esup>) $$ (i mod (dim_row (H\<^sup>\<otimes>\<^bsup>n\<^esup>)), j mod (dim_col (H\<^sup>\<otimes>\<^bsup>n\<^esup>)))"
    by (simp add: H_without_scalar_prod)
  show "(H \<Otimes> H\<^sup>\<otimes>\<^bsup>n\<^esup>) $$ (i,j) = (H\<^sup>\<otimes>\<^bsup>(n+1)\<^esup>) $$ (i,j)"
  proof (rule disjE) 
    show "(i < 2^n \<or> j < 2^n) \<or> \<not>(i < 2^n \<or> j < 2^n)" by auto
  next
    assume a2: "(i < 2^n \<or> j < 2^n)"
    then have "(H\<^sup>\<otimes>\<^bsup>n+1\<^esup>) $$ (i,j) = 1/sqrt(2) * ((H\<^sup>\<otimes>\<^bsup>n\<^esup>) $$ (i mod 2^n, j mod 2^n))" 
      using assms a0 a1 f0 tensor_of_H_next_dim
      by (metis (mono_tags, lifting) atLeastLessThan_iff )
    moreover have "H $$ (i div (dim_row (H\<^sup>\<otimes>\<^bsup>n\<^esup>)), j div (dim_col (H\<^sup>\<otimes>\<^bsup>n\<^esup>))) = 1/sqrt(2)"
      using assms a0 a1 f0 H_without_scalar_prod H_values a2 
      by (metis (no_types, lifting) Suc_eq_plus1 dim_col_mat(1) dim_row_mat(1) div_less le_eq_less_or_eq 
le_numeral_extra(2) less_power_add_imp_div_less plus_1_eq_Suc power_one_right) 
    ultimately show "(H \<Otimes> H\<^sup>\<otimes>\<^bsup>n\<^esup>) $$ (i,j) = (H\<^sup>\<otimes>\<^bsup>(n+1)\<^esup>) $$(i,j)" 
      using f1 by simp
  next 
    assume a2: "\<not>(i < 2^n \<or> j < 2^n)"
    then have "i \<ge> 2^n \<and> j \<ge> 2^n" by simp
    then have f2:"(H\<^sup>\<otimes>\<^bsup>n+1\<^esup>) $$ (i,j) = -1/sqrt(2)* ((H\<^sup>\<otimes>\<^bsup>n\<^esup>) $$ (i mod 2^n, j mod 2^n))" 
      using assms a0 a1 f0 Hn_first_factor_is_minus_sqrt_2 by simp
    have "i div (dim_row (H\<^sup>\<otimes>\<^bsup>n\<^esup>)) =1" and "j div (dim_row (H\<^sup>\<otimes>\<^bsup>n\<^esup>)) =1"  
      using a2 assms a0 a1 by auto
    then have "H $$ (i div (dim_row (H\<^sup>\<otimes>\<^bsup>n\<^esup>)), j div (dim_col (H\<^sup>\<otimes>\<^bsup>n\<^esup>)))  = -1/sqrt(2)"
      using assms a0 a1 f0 H_values_right_bottom[of "i div (dim_row (H\<^sup>\<otimes>\<^bsup>n\<^esup>))" "j div (dim_col (H\<^sup>\<otimes>\<^bsup>n\<^esup>))"] a2 
      by fastforce
    then show "(H \<Otimes> H\<^sup>\<otimes>\<^bsup>n\<^esup>) $$ (i,j) = (H\<^sup>\<otimes>\<^bsup>n+1\<^esup>) $$(i,j)" 
      using f1 f2 by simp
  qed
next
  show "dim_row (H \<Otimes> H\<^sup>\<otimes>\<^bsup>n\<^esup>) = dim_row (H\<^sup>\<otimes>\<^bsup>n+1\<^esup>)" 
    by (simp add: H_without_scalar_prod) 
next
  show "dim_col (H \<Otimes> H\<^sup>\<otimes>\<^bsup>n\<^esup>) = dim_col (H\<^sup>\<otimes>\<^bsup>n+1\<^esup>)" 
    by (simp add: H_without_scalar_prod) 
qed

lemma H_tensor_n_is_tensor_of_H:
  fixes n:: nat
  assumes asm:"n \<ge> 1"
  shows "(H ^\<^sub>\<otimes> n) = H\<^sup>\<otimes>\<^bsup>n\<^esup>"
proof (induction n rule: ind_from_1)
  show "n \<ge> 1" using assms by simp
next
  show "(H ^\<^sub>\<otimes> 1) = H\<^sup>\<otimes>\<^bsup>1\<^esup>"
  proof 
    show f0: "dim_row (H ^\<^sub>\<otimes> 1) = dim_row (H\<^sup>\<otimes>\<^bsup>1\<^esup>)" 
      by (simp add:H_without_scalar_prod) 
    show f1: "dim_col (H ^\<^sub>\<otimes> 1) = dim_col (H\<^sup>\<otimes>\<^bsup>1\<^esup>)"
      by (simp add:H_without_scalar_prod) 
    fix i j:: nat
    assume a0:"i < dim_row (H\<^sup>\<otimes>\<^bsup>1\<^esup>)" and a1:"j < dim_col (H\<^sup>\<otimes>\<^bsup>1\<^esup>)"
    then have "H\<^sup>\<otimes>\<^bsup>1\<^esup> $$ (0, 0) = 1/sqrt(2)" 
       using bitwise_inner_prod_def bin_rep_def by simp 
    moreover have " H\<^sup>\<otimes>\<^bsup>1\<^esup> $$ (0,1) = 1/sqrt(2)" 
       using bitwise_inner_prod_def bin_rep_def by simp 
    moreover have " H\<^sup>\<otimes>\<^bsup>1\<^esup> $$ (1,0) = 1/sqrt(2)" 
       using bitwise_inner_prod_def bin_rep_def by simp 
    moreover have " H\<^sup>\<otimes>\<^bsup>1\<^esup> $$ (1,1) = -1/sqrt(2)" 
       using bitwise_inner_prod_def bin_rep_def by simp 
     ultimately show "(H ^\<^sub>\<otimes> 1) $$ (i,j) = H\<^sup>\<otimes>\<^bsup>1\<^esup> $$ (i, j)" 
       using a0 a1 assms f0 f1 H_values H_values_right_bottom
       by (metis (no_types, lifting) One_nat_def dim_col_mat(1) dim_row_mat(1) less_2_cases 
           pow_tensor_1_is_id power_one_right)
  qed
next
  fix n:: nat
  assume a0:"(H ^\<^sub>\<otimes> n) = H\<^sup>\<otimes>\<^bsup>n\<^esup>" and a1:"n \<ge> 1"
  then have "(H ^\<^sub>\<otimes> (n+1)) = H \<Otimes> (H ^\<^sub>\<otimes> n)" 
    using pow_tensor_n Nat.Suc_eq_plus1 by metis
  also have "... = H \<Otimes> H\<^sup>\<otimes>\<^bsup>n\<^esup>" using a0 by simp
  also have "... = H\<^sup>\<otimes>\<^bsup>n+1\<^esup>" using a1 H_tensor_tensor_of_H by simp
  finally show "(H ^\<^sub>\<otimes> (Suc n)) = H\<^sup>\<otimes>\<^bsup>Suc n\<^esup>" by simp
qed

(*Change name using new notation*)
abbreviation  HnId:: "nat \<Rightarrow> complex Matrix.mat" where
"HnId n \<equiv> Matrix.mat (2^(n+1)) (2^(n+1)) (\<lambda>(i,j).
  if (i mod 2 = j mod 2) then (-1)^(nat((i div 2) \<cdot>\<^bsub>n\<^esub> (j div 2)))/(sqrt(2)^n) else 0)"


abbreviation  HnId':: "nat \<Rightarrow> complex Matrix.mat" where
"HnId' n \<equiv> Matrix.mat (2^(n+1)) (2^(n+1)) (\<lambda>(i,j).
  if (even i \<and> even j) then (-1)^(nat((i div 2) \<cdot>\<^bsub>n\<^esub> (j div 2)))/(sqrt(2)^n) else
    (if (odd i \<and> odd j) then (-1)^(nat((i div 2) \<cdot>\<^bsub>n\<^esub> (j div 2)))/(sqrt(2)^n) else 0))"


lemma u1: (*Should this really be simp?*)
  shows "(even i \<and> even j)\<longrightarrow>(i mod 2 = j mod 2)"
  by simp


lemma u2:
  shows "(odd i \<and> odd j)\<longrightarrow>(i mod 2 = j mod 2)"
  by (simp add: mod2_eq_if)

lemma mod_2_is_both_even_or_odd: "((even i \<and> even j) \<or> (odd i \<and> odd j)) \<longleftrightarrow> (i mod 2 = j mod 2)" 
  by (metis dvd_eq_mod_eq_0 odd_iff_mod_2_eq_one)
  
lemma HnId_values [simp]:
  assumes "n \<ge> 1"
      and "i < dim_row (HnId n)" and "j < dim_col (HnId n)"
    shows "even i \<and> even j \<longrightarrow> (HnId n) $$ (i,j) = (-1)^(nat((i div 2) \<cdot>\<^bsub>n\<^esub> (j div 2)))/(sqrt(2)^n)"
      and "odd i \<and> odd j \<longrightarrow> (HnId n) $$ (i,j) = (-1)^(nat((i div 2) \<cdot>\<^bsub>n\<^esub> (j div 2)))/(sqrt(2)^n)"
      and "(i mod 2 = j mod 2) \<longrightarrow> (HnId n) $$ (i,j) = (-1)^(nat((i div 2) \<cdot>\<^bsub>n\<^esub> (j div 2)))/(sqrt(2)^n)"
      and "\<not>(i mod 2 = j mod 2) \<longrightarrow> (HnId n) $$ (i,j) = 0"
  using assms u1 u2 by auto



(*Tidy up*)
lemma tensor_of_H_tensor_Id_is_HnId:
  assumes "n \<ge> 1"
  shows "(H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<Otimes> Id 1 = HnId n"
proof
  show "dim_row ((H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<Otimes> Id 1) = dim_row (HnId n)" 
    by (simp add: Quantum.Id_def)
next
  show "dim_col ((H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<Otimes> Id 1) = dim_col (HnId n)" 
    by (simp add: Quantum.Id_def)
next
  fix i j 
  assume a0: "i< dim_row (HnId n)" and a1: "j< dim_col (HnId n)"
  then have f0: "i < (2^(n+1)) \<and> j < (2^(n+1))" by auto
  then have f1: "i < dim_row (H\<^sup>\<otimes>\<^bsup>n\<^esup>) * dim_row (Id 1) \<and> j < dim_col (H\<^sup>\<otimes>\<^bsup>n\<^esup>) * dim_col (Id 1)"   
    using Id_def f0 by simp
  moreover have f2: "dim_col (H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<ge> 0 \<and> dim_col (Id 1) \<ge> 0"  
    using Id_def by auto
  ultimately have f3: "((H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<Otimes> (Id 1)) $$ (i,j) 
    = (H\<^sup>\<otimes>\<^bsup>n\<^esup>) $$ (i div (dim_row (Id 1)), j div (dim_col (Id 1))) * (Id 1) $$ (i mod (dim_row (Id 1)), j mod (dim_col (Id 1)))"
    by (simp add: Quantum.Id_def)
  show "((H\<^sup>\<otimes>\<^bsup>n\<^esup>)\<Otimes>Id 1) $$ (i,j) = (HnId n) $$ (i,j)" 
  proof (rule disjE)
    show "(i mod 2 = j mod 2)\<or> \<not> (i mod 2 = j mod 2)" by simp
  next
    assume a2:"(i mod 2 = j mod 2)"
    then have "(Id 1) $$ (i mod (dim_row (Id 1)), j mod (dim_col (Id 1))) = 1" 
      by (simp add: Quantum.Id_def)
    moreover have "(H\<^sup>\<otimes>\<^bsup>n\<^esup>) $$ (i div (dim_row (Id 1)), j div (dim_col (Id 1))) 
                    = (-1)^(nat((i div (dim_row (Id 1))) \<cdot>\<^bsub>n\<^esub> (j div (dim_col (Id 1)))))/(sqrt(2)^n)" 
      using tensor_of_H_values assms f1 less_mult_imp_div_less by simp
    ultimately show "((H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<Otimes> Id 1) $$ (i,j) = (HnId n) $$ (i,j)" 
      using f3 a2 f0 Id_def 
      by (smt index_mat(1) index_one_mat(2) index_one_mat(3) mult.right_neutral power_one_right prod.simps(2))
  next
    assume a2: "\<not> (i mod 2 = j mod 2)" 
    then have "(Id 1) $$ (i mod (dim_row (Id 1)), j mod (dim_col (Id 1))) = 0" 
      by (simp add: Quantum.Id_def)
    then show "((H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<Otimes> Id 1) $$ (i,j) = (HnId n) $$ (i,j)" 
      using f3 a2 f0 by simp
  qed
qed



lemma HnId_is_gate:
  assumes "n\<ge>1"
  shows "gate (n+1) (HnId n)" 
proof- 
  have "HnId n = (H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<Otimes> Id 1 " 
    using tensor_of_H_tensor_Id_is_HnId assms by auto
  moreover have "gate 1 (Id 1)" using id_is_gate by auto
  moreover have "gate n (H\<^sup>\<otimes>\<^bsup>n\<^esup>)" using H_is_gate pow_tensor_gate[of 1 H n] assms 
    by (simp add: H_tensor_n_is_tensor_of_H)
  ultimately show "gate (n+1) (HnId n)" 
    using tensor_gate by presburger
qed




abbreviation (in jozsa) \<psi>\<^sub>3:: "complex Matrix.mat" where
"\<psi>\<^sub>3  \<equiv> Matrix.mat (2^(n+1)) 1 (\<lambda>(i,j). if even i
                                         then (\<Sum> k < 2^n. (-1)^(f(k) + nat ((i div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1))) 
                                          else  (\<Sum> k < (2::nat)^n.(-1)^(f(k) + 1 + nat ((i div 2) \<cdot>\<^bsub>n\<^esub>  k))
                                                 /(sqrt(2)^n * sqrt(2)^(n+1))))"

lemma (in jozsa) \<psi>\<^sub>3_values:
  fixes k
  assumes "i<dim_row \<psi>\<^sub>3"
  shows "odd i \<longrightarrow> \<psi>\<^sub>3 $$ (i,0) = (\<Sum> k < (2::nat) ^n. (-1)^(f(k) + 1 + nat ((i div 2) \<cdot>\<^bsub>n\<^esub> k))/(sqrt(2)^n * sqrt(2)^(n+1)))"
  using assms by auto


lemma sum_every_odd_summand_is_zero:
  fixes n 
  assumes "n\<ge>1"
  shows "\<forall>A::(nat \<Rightarrow> complex).(\<forall>i. i<(2^(n+1)) \<and> odd i \<longrightarrow> A i = 0) \<longrightarrow> 
            (\<Sum>k \<in>{(0::nat)..<(2^(n+1))}. A k) = (\<Sum>k\<in>{(0::nat)..< (2^n)}. A (2*k))" 
proof (induction n rule: ind_from_1)
  show "n\<ge>1" using assms by auto
next
  show "\<forall>A::(nat \<Rightarrow>complex).(\<forall>i. i<(2^(1+1)) \<and> odd i \<longrightarrow> A i = 0) \<longrightarrow>(\<Sum>k \<in>{(0::nat)..<(2^(1+1))}. A k) = (\<Sum>k\<in>{(0::nat)..< (2^1)}. A (2*k))"
  proof(rule allI,rule impI)
    fix A::"(nat \<Rightarrow>complex)"
    assume a0: "(\<forall>i. i<(2^(1+1)) \<and> odd i \<longrightarrow> A i = 0)" 
    moreover have "(\<Sum>k \<in>{(0::nat)..<4}. A k) = A 0 + A 1 + A 2 + A 3" 
      by (simp add: add.commute add.left_commute)
    moreover have "A 1 = 0" using a0 by auto 
    moreover have "A 3 = 0" using a0 by auto 
    moreover have "(\<Sum>k\<in>{0..< (2^1)}. A (2*k)) = A 0 + A 2" 
      using add.commute add.left_commute by simp
    ultimately show "(\<Sum>k \<in>{(0::nat)..<(2^(1+1))}. A k) = (\<Sum>k\<in>{(0::nat)..< (2^1)}. A (2*k))" 
      by simp
  qed
next
  fix n
  assume a0: "n\<ge>1"
  and IH: "\<forall>B::(nat \<Rightarrow>complex).(\<forall>i. i<(2^(n+1)) \<and> odd i \<longrightarrow> B i = 0) \<longrightarrow>(\<Sum>k \<in>{(0::nat)..<(2^(n+1))}. B k) 
              = (\<Sum>k\<in>{(0::nat)..< (2^n)}. B (2*k))" 
  show "\<forall>A::(nat \<Rightarrow>complex).(\<forall>i. i<(2^((Suc n)+1)) \<and> odd i \<longrightarrow> A i = 0) \<longrightarrow>(\<Sum>k \<in>{(0::nat)..<(2^((Suc n)+1))}. A k) 
              = (\<Sum>k\<in>{(0::nat)..< (2^(Suc n))}. A (2*k)) " 
  proof (rule allI,rule impI)
    fix A::"(nat \<Rightarrow>complex)"
    assume a1: "(\<forall>i. i<(2^((Suc n)+1)) \<and> odd i \<longrightarrow> A i = 0) "
    have IH_1: "(\<Sum>k \<in>{(0::nat)..<(2^(n+1))}. A k) = (\<Sum>k\<in>{(0::nat)..< (2^n)}. A (2*k))" 
      using a1 IH by auto
    have IH_2: "(\<Sum>k \<in>{(0::nat)..<(2^(n+1))}. (\<lambda>x. A (x+2^(n+1))) k) = (\<Sum>k\<in>{(0::nat)..< (2^n)}. (\<lambda>x. A (x+2^(n+1))) (2*k))" 
      using a1 IH by auto
    have "{(0::nat)..<(2^(n+2))} = {(0::nat)..<(2^(n+1))} \<union> {(2^(n+1))..<(2^(n+2))}" by auto
    then have "(\<Sum>k \<in>{(0::nat)..<(2^(n+2))}. A k) 
               = (\<Sum>k \<in>{(0::nat)..<(2^(n+1))}. A k) + (\<Sum>k \<in>{(2^(n+1))..<(2^(n+2))}. A k)" 
      by (simp add: sum.union_disjoint)
    also have "... = (\<Sum>k\<in>{(0::nat)..< (2^n)}. A (2*k)) + (\<Sum>k \<in>{(2^(n+1))..<(2^(n+2))}. A k)"  
      using IH_1 by auto
    also have "... = (\<Sum>k\<in>{(0::nat)..< (2^n)}. A (2*k)) + (\<Sum>k \<in>{0..<(2^(n+1))}. A (k+(2^(n+1))))"  
      using sum.shift_bounds_nat_ivl[of "A " "0" "(2^(n+1))" "(2^(n+1))"] by auto
    also have "... = (\<Sum>k\<in>{(0::nat)..< (2^n)}. A (2*k)) + (\<Sum>k\<in>{(0::nat)..< (2^n)}. (\<lambda>x. A (x+2^(n+1))) (2*k))"
      using IH_2 by auto
    also have "... = (\<Sum>k\<in>{(0::nat)..< (2^n)}. A (2*k)) + (\<Sum>k\<in>{(2^n)..< (2^(n+1))}. A (2 *k))"
      using sum.shift_bounds_nat_ivl[of "\<lambda>x. (A::nat\<Rightarrow>complex) (2*(x-2^n)+2^(n+1))" "0" "(2^n)" "(2^n)"] 
      by (simp add: mult_2)
    also have "... = (\<Sum>k\<in>{(0::nat)..< (2^(n+1))}. A (2*k))" 
      by (metis Suc_eq_plus1 lessI less_imp_le_nat one_le_numeral power_increasing sum.atLeastLessThan_concat zero_le)
    finally show "(\<Sum>k \<in>{(0::nat)..<(2^((Suc n)+1))}. A k) = (\<Sum>k\<in>{(0::nat)..< (2^(Suc n))}. A (2*k)) "
      by (metis Suc_eq_plus1 add_2_eq_Suc')
  qed
qed

lemma sum_every_even_summand_is_zero:
  fixes n 
  assumes "n\<ge>1"
  shows "\<forall>A::(nat \<Rightarrow> complex).(\<forall>i. i<(2^(n+1)) \<and> even i \<longrightarrow> A i = 0) \<longrightarrow> 
            (\<Sum>k \<in>{(0::nat)..<(2^(n+1))}. A k) = (\<Sum>k\<in>{(0::nat)..< (2^n)}. A (2*k+1))" 
proof (induction n rule: ind_from_1)
  show "n\<ge>1" using assms by auto
next
  show "\<forall>A::(nat \<Rightarrow>complex).(\<forall>i. i<(2^(1+1)) \<and> even i \<longrightarrow> A i = 0) \<longrightarrow>(\<Sum>k \<in>{(0::nat)..<(2^(1+1))}. A k) = (\<Sum>k\<in>{(0::nat)..< (2^1)}. A (2*k+1))"
  proof(rule allI,rule impI)
    fix A::"(nat \<Rightarrow>complex)"
    assume a0: "(\<forall>i. i<(2^(1+1)) \<and> even i \<longrightarrow> A i = 0)" 
    moreover have "(\<Sum>k \<in>{(0::nat)..<4}. A k) = A 0 + A 1 + A 2 + A 3" 
      by (simp add: add.commute add.left_commute)
    moreover have "A 0 = 0" using a0 by auto 
    moreover have "A 2 = 0" using a0 by auto 
    moreover have "(\<Sum>k\<in>{0..< (2^1)}. A (2*k+1)) = A 1 + A 3" 
      using add.commute add.left_commute by auto
    ultimately show "(\<Sum>k \<in>{(0::nat)..<(2^(1+1))}. A k) = (\<Sum>k\<in>{(0::nat)..< (2^1)}. A (2*k+1))" 
      by simp
  qed
next
  fix n
  assume a0: "n\<ge>1"
  and IH: "\<forall>B::(nat \<Rightarrow>complex).(\<forall>i. i<(2^(n+1)) \<and> even i \<longrightarrow> B i = 0) \<longrightarrow>(\<Sum>k \<in>{(0::nat)..<(2^(n+1))}. B k) 
              = (\<Sum>k\<in>{(0::nat)..< (2^n)}. B (2*k+1))" 
  show "\<forall>A::(nat \<Rightarrow>complex).(\<forall>i. i<(2^((Suc n)+1)) \<and> even i \<longrightarrow> A i = 0) \<longrightarrow>(\<Sum>k \<in>{(0::nat)..<(2^((Suc n)+1))}. A k) 
              = (\<Sum>k\<in>{(0::nat)..< (2^(Suc n))}. A (2*k+1)) " 
  proof (rule allI,rule impI)
    fix A::"(nat \<Rightarrow>complex)"
    assume a1: "(\<forall>i. i<(2^((Suc n)+1)) \<and> even i \<longrightarrow> A i = 0) "
    have IH_1: "(\<Sum>k \<in>{(0::nat)..<(2^(n+1))}. A k) = (\<Sum>k\<in>{(0::nat)..< (2^n)}. A (2*k+1))" 
      using a1 IH by auto
    have IH_2: "(\<Sum>k \<in>{(0::nat)..<(2^(n+1))}. (\<lambda>x. A (x+2^(n+1))) k) = (\<Sum>k\<in>{(0::nat)..< (2^n)}. (\<lambda>x. A (x+2^(n+1))) (2*k+1))" 
      using a1 IH by auto
    have "{(0::nat)..<(2^(n+2))} = {(0::nat)..<(2^(n+1))} \<union> {(2^(n+1))..<(2^(n+2))}" by auto
    then have "(\<Sum>k \<in>{(0::nat)..<(2^(n+2))}. A k) 
               = (\<Sum>k \<in>{(0::nat)..<(2^(n+1))}. A k) + (\<Sum>k \<in>{(2^(n+1))..<(2^(n+2))}. A k)" 
      by (simp add: sum.union_disjoint)
    also have "... = (\<Sum>k\<in>{(0::nat)..< (2^n)}. A (2*k+1)) + (\<Sum>k \<in>{(2^(n+1))..<(2^(n+2))}. A k)"  
      using IH_1 by auto
    also have "... = (\<Sum>k\<in>{(0::nat)..< (2^n)}. A (2*k+1)) + (\<Sum>k \<in>{0..<(2^(n+1))}. A (k+(2^(n+1))))"  
      using sum.shift_bounds_nat_ivl[of "A " "0" "(2^(n+1))" "(2^(n+1))"] by auto
    also have "... = (\<Sum>k\<in>{(0::nat)..< (2^n)}. A (2*k+1)) + (\<Sum>k\<in>{(0::nat)..< (2^n)}. (\<lambda>x. A (x+2^(n+1))) (2*k+1))"
      using IH_2 by auto
    also have "... = (\<Sum>k\<in>{(0::nat)..< (2^n)}. A (2*k+1)) + (\<Sum>k\<in>{(2^n)..< (2^(n+1))}. A (2 *k+1))"
      using sum.shift_bounds_nat_ivl[of "\<lambda>x. (A::nat\<Rightarrow>complex) (2*(x-2^n)+1+2^(n+1))" "0" "(2^n)" "(2^n)"] 
      by (simp add: mult_2)
    also have "... = (\<Sum>k\<in>{(0::nat)..< (2^(n+1))}. A (2*k+1))" 
      by (metis Suc_eq_plus1 lessI less_imp_le_nat one_le_numeral power_increasing sum.atLeastLessThan_concat zero_le)
    finally show "(\<Sum>k \<in>{(0::nat)..<(2^((Suc n)+1))}. A k) = (\<Sum>k\<in>{(0::nat)..< (2^(Suc n))}. A (2*k+1)) "
      by (metis Suc_eq_plus1 add_2_eq_Suc')
  qed
qed


(*Tidy up proof*)
lemma (in jozsa) hadamard_gate_tensor_n_times_\<psi>\<^sub>2_is_\<psi>\<^sub>3:
  shows "((H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<Otimes> Id 1) * \<psi>\<^sub>2' = \<psi>\<^sub>3"
proof
  fix i j
  assume a0:"i< dim_row \<psi>\<^sub>3" and a1:"j<dim_col \<psi>\<^sub>3" 
  then have f0: "i < (2^(n+1)) \<and> j = 0" by auto
  have f1: "((HnId n)* \<psi>\<^sub>2') $$ (i,j) 
                = (\<Sum>k<(2^(n+1)). ((HnId n) $$ (i,k)) * (\<psi>\<^sub>2' $$ (k,j)))" 
    using a1 f0 by (simp add: atLeast0LessThan)
  show "(((H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<Otimes> Id 1) * \<psi>\<^sub>2') $$ (i,j) = \<psi>\<^sub>3 $$ (i,j)"
  proof(rule disjE)
    show "even i \<or> odd i" by auto
  next
    assume a2: "even i"
    have "(\<not>(i mod 2 = k mod 2) \<and> k<dim_col (HnId n)) \<longrightarrow> ((HnId n) $$ (i,k)) * (\<psi>\<^sub>2' $$ (k,j)) = 0" 
      for k using f0 by auto
    then have "k<(2^(n+1)) \<and> odd k \<longrightarrow> ((HnId n) $$ (i,k)) * (\<psi>\<^sub>2' $$ (k,j)) = 0" 
      for k using a2 mod_2_is_both_even_or_odd f0
      by (metis (no_types, lifting) dim_col_mat(1))
    then have "(\<Sum>k \<in>{(0::nat)..<(2^(n+1))}. ((HnId n) $$ (i,k)) * (\<psi>\<^sub>2' $$ (k,j)))
              = (\<Sum>k\<in>{(0::nat)..< (2^n)}. ((HnId n) $$ (i,2*k)) * (\<psi>\<^sub>2' $$ (2*k,j)))" 
      using sum_every_odd_summand_is_zero dim by auto
    moreover have "(\<Sum>k<(2^n). ((HnId n) $$ (i,2*k)) * (\<psi>\<^sub>2' $$ (2*k,j))) 
                  =  (\<Sum> k < 2^n.(-1)^(nat ((i div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n) *((-1)^f(k))/(sqrt(2)^(n+1)))" 
    proof-{
      have "(even k \<and> k<dim_row \<psi>\<^sub>2') \<longrightarrow> (\<psi>\<^sub>2' $$ (k,j)) = ((-1)^f(k div 2))/(sqrt(2)^(n+1)) "
        for k using a2 a0 a1 f0  
        by (smt dim_row_mat(1) index_mat(1) less_numeral_extra(1) prod.simps(2))
      then have "(\<Sum>k<(2^n). ((HnId n) $$ (i,2*k)) * (\<psi>\<^sub>2' $$ (2*k,j))) 
               = (\<Sum> k < 2^n. ((HnId n) $$ (i,2*k)) *((-1)^f((2*k) div 2))/(sqrt(2)^(n+1)))" 
        by auto
      moreover have "(even k \<and> k<dim_col (HnId n))
                 \<longrightarrow> ((HnId n) $$ (i,k))  = (-1)^ (nat ((i div 2) \<cdot>\<^bsub>n\<^esub>  (k div 2)))/(sqrt(2)^n) " for k
        using a2 a0 a1 by auto
      ultimately have "(\<Sum>k<(2^n). ((HnId n) $$ (i,2*k)) * (\<psi>\<^sub>2' $$ (2*k,j))) 
                  =  (\<Sum> k < 2^n.(-1)^(nat ((i div 2) \<cdot>\<^bsub>n\<^esub>  ((2*k) div 2)))/(sqrt(2)^n) *((-1)^f((2*k) div 2))/(sqrt(2)^(n+1)))" 
      by auto
      then show "(\<Sum>k<(2^n). ((HnId n) $$ (i,2*k)) * (\<psi>\<^sub>2' $$ (2*k,j))) 
                  =  (\<Sum> k < 2^n.(-1)^(nat ((i div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n) *((-1)^f(k))/(sqrt(2)^(n+1)))" 
        by auto}
    qed
    ultimately have "((HnId n)* \<psi>\<^sub>2') $$ (i,j) = (\<Sum> k < 2^n.(-1)^(nat ((i div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n) *((-1)^f(k))/(sqrt(2)^(n+1)))" 
      using f1 by (metis atLeast0LessThan) 
    moreover have "(-1)^(nat ((i div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n) *((-1)^f(k))/(sqrt(2)^(n+1)) = 
                  (-1)^(f(k)+(nat ((i div 2) \<cdot>\<^bsub>n\<^esub>  k)))/((sqrt(2)^n)*(sqrt(2)^(n+1)))" for k 
      by (simp add: power_add)
    ultimately have "((HnId n)* \<psi>\<^sub>2') $$ (i,j) = (\<Sum> k < 2^n.(-1)^(f(k)+(nat ((i div 2) \<cdot>\<^bsub>n\<^esub>  k)))/((sqrt(2)^n)*(sqrt(2)^(n+1))))" 
      by (smt sum.cong)
    moreover have "\<psi>\<^sub>3 $$ (i,j) = (\<Sum> k < 2^n. (-1)^(f(k) +  nat ((i div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1)))" 
      using a0 a1 a2 by auto
    ultimately show "(((H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<Otimes> Id 1)* \<psi>\<^sub>2') $$ (i,j) = \<psi>\<^sub>3 $$ (i,j)" 
      using tensor_of_H_tensor_Id_is_HnId dim by auto
  next
    assume a2: "odd i"
    have "(\<not>(i mod 2 = k mod 2) \<and> k<dim_col (HnId n)) \<longrightarrow> ((HnId n) $$ (i,k)) * (\<psi>\<^sub>2' $$ (k,j)) = 0" 
      for k using f0 by auto
    then have "k<(2^(n+1)) \<and> even k \<longrightarrow> ((HnId n) $$ (i,k)) * (\<psi>\<^sub>2' $$ (k,j)) = 0" 
      for k using a2 mod_2_is_both_even_or_odd f0
      by (metis (no_types, lifting) dim_col_mat(1))
    then have "(\<Sum>k \<in>{(0::nat)..<(2^(n+1))}. ((HnId n) $$ (i,k)) * (\<psi>\<^sub>2' $$ (k,j)))
              = (\<Sum>k\<in>{(0::nat)..< (2^n)}. ((HnId n) $$ (i,2*k+1)) * (\<psi>\<^sub>2' $$ (2*k+1,j)))" 
      using sum_every_even_summand_is_zero dim by auto
    moreover have "(\<Sum>k<(2^n). ((HnId n) $$ (i,2*k+1)) * (\<psi>\<^sub>2' $$ (2*k+1,j))) 
                  =  (\<Sum> k < 2^n.(-1)^(nat ((i div 2) \<cdot>\<^bsub>n\<^esub> k))/(sqrt(2)^n) *((-1)^(f(k)+1))/(sqrt(2)^(n+1)))" 
    proof-{
      have "(odd k \<and> k<dim_row \<psi>\<^sub>2') \<longrightarrow> (\<psi>\<^sub>2' $$ (k,j)) = ((-1)^(f(k div 2)+1))/(sqrt(2)^(n+1)) "
        for k using a2 a0 a1 f0  
        by (smt dim_row_mat(1) index_mat(1) less_numeral_extra(1) prod.simps(2))
      then have f2:"(\<Sum>k<(2^n). ((HnId n) $$ (i,2*k+1)) * (\<psi>\<^sub>2' $$ (2*k+1,j))) 
               = (\<Sum> k < 2^n. ((HnId n) $$ (i,2*k+1)) * ((-1)^(f((2*k+1) div 2)+1))/(sqrt(2)^(n+1)))" 
        by auto
      have "i<dim_row (HnId n)" 
        using f0 a2 mod_2_is_both_even_or_odd by auto
      then have "((i mod 2 = k mod 2) \<and> k<dim_col (HnId n) )
                 \<longrightarrow> ((HnId n) $$ (i,k))  = (-1)^(nat((i div 2) \<cdot>\<^bsub>n\<^esub> (k div 2)))/(sqrt(2)^n) " for k
        using a2 a0 a1 f0 dim HnId_values 
        by auto
      moreover have "odd k \<longrightarrow> (i mod 2 = k mod 2)" for k using a2 u2 by auto
      ultimately have "(odd k \<and> k<dim_col (HnId n) )
                 \<longrightarrow> ((HnId n) $$ (i,k))  = (-1)^(nat((i div 2) \<cdot>\<^bsub>n\<^esub> (k div 2)))/(sqrt(2)^n) " for k
        by auto
      then have "(k<(2^n) ) \<longrightarrow> ((HnId n) $$ (i,2*k+1))  = (-1)^(nat((i div 2) \<cdot>\<^bsub>n\<^esub> ((2*k+1) div 2)))/(sqrt(2)^n) " for k
        by auto
      then have "(\<Sum>k<(2^n). ((HnId n) $$ (i,2*k+1)) * (\<psi>\<^sub>2' $$ (2*k+1,j))) 
                  = (\<Sum> k < 2^n.(-1)^(nat((i div 2) \<cdot>\<^bsub>n\<^esub> ((2*k+1) div 2)))/(sqrt(2)^n) *  ((-1)^(f((2*k+1) div 2)+1))/(sqrt(2)^(n+1)))" 
        using f2 by auto
      then show "(\<Sum>k<(2^n). ((HnId n) $$ (i,2*k+1)) * (\<psi>\<^sub>2' $$ (2*k+1,j))) 
                  =   (\<Sum> k < 2^n.(-1)^(nat ((i div 2) \<cdot>\<^bsub>n\<^esub> k))/(sqrt(2)^n) *((-1)^(f(k)+1))/(sqrt(2)^(n+1)))" by auto
        }
    qed
    ultimately have "((HnId n)* \<psi>\<^sub>2') $$ (i,j) = (\<Sum> k < 2^n.(-1)^(nat ((i div 2) \<cdot>\<^bsub>n\<^esub> k))/(sqrt(2)^n) 
                *((-1)^(f(k)+1))/(sqrt(2)^(n+1)))" 
      using f1 by (metis atLeast0LessThan) 
    moreover have "(-1)^(nat ((i div 2) \<cdot>\<^bsub>n\<^esub> k))/(sqrt(2)^n) *((-1)^(f(k)+1))/(sqrt(2)^(n+1)) = 
                  (-1)^(f(k)+1+(nat ((i div 2) \<cdot>\<^bsub>n\<^esub> k)))/((sqrt(2)^n)*(sqrt(2)^(n+1)))" for k 
      by (simp add: power_add)
    ultimately have "((HnId n)* \<psi>\<^sub>2') $$ (i,j) = (\<Sum> k < 2^n.(-1)^(f(k)+1+(nat ((i div 2) \<cdot>\<^bsub>n\<^esub> k)))/((sqrt(2)^n)*(sqrt(2)^(n+1))))" 
      by (smt sum.cong) 
    then show "(((H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<Otimes> Id 1)* \<psi>\<^sub>2') $$ (i,j) = \<psi>\<^sub>3 $$ (i,j)" 
      using tensor_of_H_tensor_Id_is_HnId dim a2 a0 a1 by auto
  qed
next
  show "dim_row (((H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<Otimes> Id 1)* \<psi>\<^sub>2') = dim_row \<psi>\<^sub>3"  
    using tensor_of_H_tensor_Id_is_HnId dim by auto
next
  show "dim_col (((H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<Otimes> Id 1)* \<psi>\<^sub>2') = dim_col \<psi>\<^sub>3" 
    using tensor_of_H_tensor_Id_is_HnId dim by auto
qed



lemma (in jozsa) \<psi>\<^sub>3_is_state:
  shows "state (n+1) \<psi>\<^sub>3"
proof-
  have "((H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<Otimes> Id 1) * \<psi>\<^sub>2' = \<psi>\<^sub>3" 
    using hadamard_gate_tensor_n_times_\<psi>\<^sub>2_is_\<psi>\<^sub>3 by auto
  moreover have "gate (n+1) ((H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<Otimes> Id 1)" 
    using tensor_of_H_tensor_Id_is_HnId HnId_is_gate dim by auto
  moreover have "state (n+1) \<psi>\<^sub>2'" using \<psi>\<^sub>2_is_state \<psi>\<^sub>2_is_\<psi>\<^sub>2' by auto
  ultimately show "state (n+1) \<psi>\<^sub>3"
    using gate_on_state_is_state dim 
    by (metis (no_types, lifting))
qed



definition (in jozsa) deutsch_jozsa_algo:: "complex Matrix.mat" where 
"deutsch_jozsa_algo \<equiv> ((H\<^sup>\<otimes>\<^bsup>n\<^esup>) \<Otimes> Id 1) * (U\<^sub>f * (((H ^\<^sub>\<otimes> n) * ( |zero\<rangle> ^\<^sub>\<otimes> n)) \<Otimes> (H * |one\<rangle>)))"


lemma (in jozsa) deutsch_jozsa_algo_result [simp]: 
  shows "deutsch_jozsa_algo = \<psi>\<^sub>3" 
  using deutsch_jozsa_algo_def H_on_ket_one_is_\<psi>\<^sub>1\<^sub>1 H_tensor_n_on_zero_tensor_n \<psi>\<^sub>1\<^sub>0_tensor_\<psi>\<^sub>1\<^sub>1_is_\<psi>\<^sub>1
  jozsa_transform_times_\<psi>\<^sub>1_is_\<psi>\<^sub>2 \<psi>\<^sub>2_is_\<psi>\<^sub>2' hadamard_gate_tensor_n_times_\<psi>\<^sub>2_is_\<psi>\<^sub>3 dim  by auto


lemma (in jozsa) deutsch_jozsa_algo_result_is_state: 
  shows "state (n+1) deutsch_jozsa_algo" 
  using \<psi>\<^sub>3_is_state by simp




text \<open>Measurement\<close>

(*HL to AB: I want to show that the probability that the first n qubits of deutsch_jozsa_algo are 0 
is 

(prob_first_m_qubits_0 (n+1) deutsch_jozsa_algo n) 
= (\<Sum>j\<in>{k| k i::nat. (k<2^(n+1)) \<and> i<n \<and> \<not> select_index (n+1) i k}. (cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2)
= (\<Sum>j\<in>{0,1}. (cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2)

Intuitively this makes sense to me. We search all indices where this n indices are 0. But the proof that
{k| k i::nat. (k<2^(n+1)) \<and> i<n \<and> \<not> select_index (n+1) i k} is the right set to choose from is hard.

First, I tried to give the probability for (prob0 (n+1) deutsch_jozsa_algo i) for each i<n (see below) but that 
was very hard. 
*)



(*Maybe try different approach. Do not show that measuring each qubit \<le>n yields 0 with prob 1 but that
measuring n qubits in state 0 yields one. but how?*)


(*Can be easily generalised to any list of qubits*)
(*SHOW SOMEHOW THAT THIS IS EQUIVALENT TO MEASURING THE FIRST N QUBITS AND MULT THE PROB*)
definition prob_first_m_qubits_0 ::"nat \<Rightarrow> complex Matrix.mat \<Rightarrow> nat \<Rightarrow> real" where
"prob_first_m_qubits_0 n v m \<equiv>
  if state n v then \<Sum>j\<in>{k| k i::nat. (k<2^n) \<and> i<m \<and> \<not> select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2 else undefined"

(*Rather take this one for now (if proven use it without definition just as a fact)*)
(*PUT IN deutsch_jozsa_algo INSTEAD OF V*)
definition prob_first_m_qubits_0' ::"nat \<Rightarrow> complex Matrix.mat \<Rightarrow> real" where
"prob_first_m_qubits_0' n v \<equiv>
  if state (n+1) v then \<Sum>j\<in>{k| k i::nat. (k<2^(n+1)) \<and> i\<le>n \<and> \<not> select_index (n+1) i k}. (cmod(v $$ (j,0)))\<^sup>2 else undefined"



(*How can I even proof this? I will first try a pen and paper proof somehow. It must also use properties of 
state vectors and seems so difficult...*)
lemma 
  shows "(\<Prod>i\<in>{0..n} . (\<Sum>j\<in>{k| k::nat. (k<2^(n+1)) \<and> (k mod 2^((Suc n)-i) < 2^(n-i))}. (cmod(v $$ (j,0)))\<^sup>2)) 
        = (\<Sum>j\<in>{k| k i::nat. (k<2^(n+1)) \<and> i\<le>n \<and> (k mod 2^((Suc n)-i) < 2^(n-i))}. (cmod(v $$ (j,0)))\<^sup>2)"
proof (induction n) (*can an induction even work?*)
  show "(\<Prod>i\<in>{0..0} . (\<Sum>j\<in>{k| k::nat. (k<2^(0+1)) \<and> (k mod 2^((Suc 0)-i) < 2^(0-i))}. (cmod(v $$ (j,0)))\<^sup>2)) 
        = (\<Sum>j\<in>{k| k i::nat. (k<2^(0+1)) \<and> i\<le>0 \<and> (k mod 2^((Suc 0)-i) < 2^(0-i))}. (cmod(v $$ (j,0)))\<^sup>2)"
    by auto
next
  fix n
  assume "(\<Prod>i\<in>{0..n} . (\<Sum>j\<in>{k| k::nat. (k<2^(n+1)) \<and> (k mod 2^((Suc n)-i) < 2^(n-i))}. (cmod(v $$ (j,0)))\<^sup>2)) 
        = (\<Sum>j\<in>{k| k i::nat. (k<2^(n+1)) \<and> i\<le>n \<and> (k mod 2^((Suc n)-i) < 2^(n-i))}. (cmod(v $$ (j,0)))\<^sup>2)"
  have "i< (Suc n) \<longrightarrow>  {k| k::nat. (k<2^((Suc n)+1)) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))}
        = {k| k::nat. (k<2^((Suc n)+1) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))) \<and> 
                       (k<2^(n+1)) \<and> (k mod 2^((Suc n)-i) < 2^(n-i))}
        \<union> {k| k::nat. (k<2^((Suc n)+1) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))) \<and>
              ((k\<ge>2^(n+1)) \<or> (k mod 2^((Suc n)-i) \<ge> 2^(n-i)))}" for i by auto
  then have "i< (Suc n) \<longrightarrow> (\<Prod>i\<in>{0..(Suc n)} . (\<Sum>j\<in>{k| k::nat. (k<2^((Suc n)+1)) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))}. (cmod(v $$ (j,0)))\<^sup>2)) 
        = (\<Prod>i\<in>{0..(Suc n)} . 
(\<Sum>j\<in>{k| k::nat. (k<2^((Suc n)+1) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))) \<and> 
                       (k<2^(n+1)) \<and> (k mod 2^((Suc n)-i) < 2^(n-i))}
        \<union> {k| k::nat. (k<2^((Suc n)+1) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))) \<and>
              ((k\<ge>2^(n+1)) \<or> (k mod 2^((Suc n)-i) \<ge> 2^(n-i)))}. (cmod(v $$ (j,0)))\<^sup>2)) " for i sorry

  then have "i< (Suc n) \<longrightarrow> (\<Prod>i\<in>{0..(Suc n)} . (\<Sum>j\<in>{k| k::nat. (k<2^((Suc n)+1)) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))}. (cmod(v $$ (j,0)))\<^sup>2)) 
        = (\<Prod>i\<in>{0..(Suc n)} .
          ((\<Sum>j\<in>{k| k::nat. (k<2^((Suc n)+1) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))) \<and> 
                       (k<2^(n+1)) \<and> (k mod 2^((Suc n)-i) < 2^(n-i))}. (cmod(v $$ (j,0)))\<^sup>2))  
          +(\<Sum>j\<in>{k| k::nat. (k<2^((Suc n)+1) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))) \<and>
              ((k\<ge>2^(n+1)) \<or> (k mod 2^((Suc n)-i) \<ge> 2^(n-i)))}. (cmod(v $$ (j,0)))\<^sup>2))" for i sledgehammer

  have "(\<Prod>i\<in>{0..(Suc n)} . (\<Sum>j\<in>{k| k::nat. (k<2^((Suc n)+1)) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))}. (cmod(v $$ (j,0)))\<^sup>2)) 
        = (\<Prod>i\<in>{0..n} . (\<Sum>j\<in>{k| k::nat. (k<2^(n+1)) \<and> (k mod 2^((Suc n)-i) < 2^(n-i))}. (cmod(v $$ (j,0)))\<^sup>2))
          * (\<Sum>j\<in>{k| k::nat. (k<2^(n+1)) \<and> (k mod 2^((Suc n)-(Suc n)) < 2^(n-(Suc n)))}. (cmod(v $$ (j,0)))\<^sup>2)
        + (\<Prod>i\<in>{0..(Suc n)} . (\<Sum>j\<in>{k| k::nat. (k<2^((Suc n)+1) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))) \<and>
              ((k\<ge>2^(n+1)) \<or> (k mod 2^((Suc n)-i) \<ge> 2^(n-i)))}. (cmod(v $$ (j,0)))\<^sup>2)) " sorry
  have "(\<Prod>i\<in>{0..n} . (\<Sum>j\<in>{k| k::nat. (k<2^((Suc n)+1)) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))}. (cmod(v $$ (j,0)))\<^sup>2)) 
        = (\<Sum>j\<in>{k| k i::nat. (k<2^(n+1)) \<and> i\<le>n \<and> (k mod 2^((Suc n)-i) < 2^(n-i))}. (cmod(v $$ (j,0)))\<^sup>2)
          * (\<Sum>j\<in>{k| k::nat. (k<2^(n+1)) \<and> (k mod 2^((Suc n)-(Suc n)) < 2^(n-(Suc n)))}. (cmod(v $$ (j,0)))\<^sup>2)
        + (\<Prod>i\<in>{0..n} . (\<Sum>j\<in>{k| k::nat. (k<2^((Suc n)+1) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))) \<and>
              ((k\<ge>2^(n+1)) \<or> (k mod 2^((Suc n)-i) \<ge> 2^(n-i)))}. (cmod(v $$ (j,0)))\<^sup>2)) " sorry
  have "(\<Prod>i\<in>{0..n} . (\<Sum>j\<in>{k| k::nat. (k<2^((Suc n)+1) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))) \<and>
              ((k\<ge>2^(n+1)) \<or> (k mod 2^((Suc n)-i) \<ge> 2^(n-i)))}. (cmod(v $$ (j,0)))\<^sup>2))
        = (\<Sum>j\<in>{k| k i::nat. (k<2^(n+1)) \<and> i\<le>n \<and> (k mod 2^((Suc n)-i) < 2^(n-i))}. (cmod(v $$ (j,0)))\<^sup>2)" sorry
  have "(\<Sum>j\<in>{k| k i::nat. (k<2^(n+1)) \<and> i\<le>n \<and> (k mod 2^((Suc n)-i) < 2^(n-i))}. (cmod(v $$ (j,0)))\<^sup>2)
          * (\<Sum>j\<in>{k| k::nat. (k<2^(n+1)) \<and> (k mod 2^((Suc n)-(Suc n)) < 2^(n-(Suc n)))}. (cmod(v $$ (j,0)))\<^sup>2)
        = (\<Sum>j\<in>{k| k i::nat. (k<2^(n+2)) \<and> i\<le>(n+1) \<and> (k mod 2^((Suc (n+1))-i) < 2^((n+1)-i))}. (cmod(v $$ (j,0)))\<^sup>2)" sorry
  have "(\<Sum>j\<in>{k| k i::nat. (k<2^(n+1)) \<and> i\<le>n \<and> (k mod 2^((Suc n)-i) < 2^(n-i))}. (cmod(v $$ (j,0)))\<^sup>2)
      + (\<Sum>j\<in>{k| k i::nat. (k<2^((Suc n)+1)) \<and> i\<le>(Suc n) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i)) \<and> 
                           (k\<ge>2^(n+1)) \<or> i>n \<or> (k mod 2^((Suc n)-i) \<ge> 2^(n-i))}. (cmod(v $$ (j,0)))\<^sup>2) 
      = (\<Sum>j\<in>{k| k i::nat. (k<2^((Suc n)+1)) \<and> i\<le>(Suc n) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))}. (cmod(v $$ (j,0)))\<^sup>2)"
    sorry
  show "(\<Prod>i\<in>{0..(Suc n)} . (\<Sum>j\<in>{k| k::nat. (k<2^((Suc n)+1)) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))}. (cmod(v $$ (j,0)))\<^sup>2))
        = (\<Sum>j\<in>{k| k i::nat. (k<2^((Suc n)+1)) \<and> i\<le>(Suc n) \<and> (k mod 2^((Suc (Suc n))-i) < 2^((Suc n)-i))}. (cmod(v $$ (j,0)))\<^sup>2)"






(*Show that the probability that the first n qubits of a n+1 qubit system are 0 is equal to the 
probability that the first qubit is zero times the prob that the second is zero and so on.*)
lemma
  fixes j n ::nat
  shows "\<forall>v. state (n+1) v \<longrightarrow> (\<Prod>i\<in>{0..n} . prob0 (n+1) v i) = prob_first_m_qubits_0' n v" 
proof (rule allI,rule impI)
  fix v
  assume "state (n+1) v "
  show "(\<Prod>i\<in>{0..n} . prob0 (n+1) v i) = prob_first_m_qubits_0' n v" 
    oops
qed
(*proof (rule allI,induction n,rule impI)
  fix v 
  assume a0: "state (0+1) v "
  have "prob_first_m_qubits_0' 0 v = (\<Sum>j\<in>{k| k i::nat. (k<2^(0+1)) \<and> i\<le>0 \<and> \<not> select_index (0+1) i k}. (cmod(v $$ (j,0)))\<^sup>2)"
    using a0 prob_first_m_qubits_0'_def by auto
  then have "prob_first_m_qubits_0' 0 v = (\<Sum>j\<in>{k| k ::nat. (k<2^(0+1))  \<and> \<not> select_index 1 0 k}. (cmod(v $$ (j,0)))\<^sup>2)"
    by auto
  moreover have " prob0 1 v 0 = (\<Sum>j\<in>{k| k::nat. (k<2^1) \<and> \<not>select_index 1 0 k }. (cmod(v $$ (j,0)))\<^sup>2)"
    using prob0_def a0 by auto
  ultimately show "prod (prob0 (0 + 1) v) {0..0} = prob_first_m_qubits_0' 0 v" by auto
next
  fix v n
  assume IH: "\<And>v. state (n + 1) v \<longrightarrow> prod (prob0 (n + 1) v) {0..n} = prob_first_m_qubits_0' n v"
  show "state (Suc n + 1) v \<longrightarrow> prod (prob0 (Suc n + 1) v) {0..Suc n} = prob_first_m_qubits_0' (Suc n) v" 
qed*)


(*
definition select_index ::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"select_index n i j \<equiv> (i\<le>n-1) \<and> (j\<le>2^n - 1) \<and> (j mod 2^(n-i) \<ge> 2^(n-1-i))"

definition prob0 ::"nat \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> real" where
"prob0 n v i \<equiv>
  if state n v then \<Sum>j\<in>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2 else undefined"


*)
value " (bin_rep 4 0)" 
value "(nat (0 \<cdot>\<^bsub>3\<^esub>  7))"

lemma bitwise_inner_prod_with_zero:
  assumes "k<2^n"
  shows "(nat (0 \<cdot>\<^bsub>n\<^esub>  k)) = 0" 
proof-
  have "(nat (0 \<cdot>\<^bsub>n\<^esub>  k)) = nat (\<Sum>j\<in>{0..<n}. (bin_rep n 0)!j * (bin_rep n k)!j)" 
    using bitwise_inner_prod_def by auto
  moreover have "nat (\<Sum>j\<in>{0..<n}. (bin_rep n 0)!j * (bin_rep n k)!j) 
                =  nat (\<Sum>j\<in>{0..<n}. 0 * (bin_rep n k)!j)" by (simp add: bin_rep_index)
  ultimately show "(nat (0 \<cdot>\<^bsub>n\<^esub>  k)) = 0" by auto
qed


value "\<not>(select_index 1 0 0)"


lemma u5:
  fixes j n::nat
  shows "j mod 2^(n+1) < 2^n \<longrightarrow> j \<notin> {2^n..<2^(n+1)}" 
  by force

lemma measure_if_first_n_qubits_zero_remaining_indices: (*Rename if stays*)
  fixes  k n::nat
  assumes "n\<ge>1"
  shows "(\<forall>i\<in>{0..n}.( k\<notin>{2^(n-i)+1..2^((n+1)-i)})) \<and> (k\<in>{0..<2^(n+1)}) \<longrightarrow> k\<in>{0,1}" 
proof (induction n rule: ind_from_1)
  show "n\<ge>1" using assms by auto
next
  have "(\<forall>i\<in>{0,1}.(k\<notin>{(2::nat)^(1-i)+1..2^((1+1)-i)})) \<longrightarrow> (k\<notin>{(2::nat)^(1-1)+1..2^((1+1)-0)})" 
    using set_2 assms by auto
  moreover have "k\<notin>{(2::nat)^(1-1)+1..2^((1+1)-0)}  \<and> k\<in>{0..<2^(1+1)} \<longrightarrow> k\<in>{0,1}" by auto
  ultimately show "((\<forall>i\<in>{0..1}.(k\<notin>{2^(1-i)+1..2^((1+1)-i)})) \<and> (k\<in>{0..<2^(1+1)})) \<longrightarrow> k\<in>{0,1}" 
    using atLeastAtMost_iff by blast
next
  fix n
  assume IH: "(\<forall>i\<in>{0..n}.( k\<notin>{2^(n-i)+1..2^((n+1)-i)})) \<and> (k\<in>{0..<2^(n+1)}) \<longrightarrow> k\<in>{0,1}" 
  and "n\<ge>1"
  show "(\<forall>i\<in>{0..Suc n}. k \<notin> {2 ^ (Suc n - i) + 1..2 ^ (Suc n + 1 - i)}) \<and> k \<in> {0..<2 ^ (Suc n + 1)} \<longrightarrow> k \<in> {0, 1}" 
  proof
    assume a0: "(\<forall>i\<in>{0..Suc n}. k \<notin> {2 ^ (Suc n - i) + 1..2 ^ (Suc n + 1 - i)}) \<and> k \<in> {0..<2 ^ (Suc n + 1)}"
    then have f0:"(\<forall>i\<in>{0..n}. k \<notin> {2 ^ (n - i) + 1..2 ^ (n + 1 - i)})" 
      using Suc_eq_plus1 Suc_leI atLeastAtMost_iff diff_Suc_Suc zero_le by force
    then have "(k\<in>{0..<2^(n+1)}) \<longrightarrow> k\<in>{0,1}" 
      using IH by auto
    moreover have "(k>2^(n+1)) \<longrightarrow> k\<in>{0,1}" 
      by (metis One_nat_def Suc_eq_plus1 Suc_leI a0 add_Suc_shift add_diff_cancel_right' atLeastAtMost_iff 
          atLeastLessThan_iff le_add2 le_add_same_cancel2 less_imp_le_nat)
    moreover have "(k=2^(n+1)) \<longrightarrow> k\<in>{0,1}" 
      using f0
      by (metis Suc_1 Suc_eq_plus1 Suc_leI atLeastLessThanSuc_atLeastAtMost atLeastLessThan_iff diff_zero le0 
          lessI power_strict_increasing_iff zero_less_Suc)
    ultimately show "k\<in>{0,1}" 
      using a0 
      by (meson atLeastLessThan_iff nat_neq_iff) 
  qed
qed


lemma k1 [simp]: (*Give name if stays*)
  shows "2^n/(sqrt(2)^n * sqrt(2)^(n+1)) = 1/sqrt(2)" 
proof(induction n)
  show "2^0/(sqrt(2)^0 * sqrt(2)^(0+1)) = 1/sqrt(2)" by auto
next
  fix n
  assume IH: "2^n/(sqrt(2)^n * sqrt(2)^(n+1)) = 1/sqrt(2)" 
  have "(sqrt 2 ^ Suc n * sqrt 2 ^ (Suc n + 1)) = (sqrt(2)^n * sqrt(2)^(n+1) * sqrt(2)^2)" 
    by auto 
  then have "2 ^ Suc n /(sqrt 2 ^ Suc n * sqrt 2 ^ (Suc n + 1)) = (2 ^ n * 2) /(sqrt(2)^n * sqrt(2)^(n+1) * sqrt(2)^2)"
    by (metis power_Suc semiring_normalization_rules(7))
  then show "2 ^ Suc n /(sqrt 2 ^ Suc n * sqrt 2 ^ (Suc n + 1)) = 1/sqrt(2)" 
    using IH by auto
qed

(*  declare [[show_types]]
  declare [[show_sorts]]
  declare [[show_consts]]*)

lemma (in jozsa)
  fixes i::nat 
  assumes "i\<in>{0..<n}"
    and "const 0"
  shows "prob_first_m_qubits_0' n deutsch_jozsa_algo = 1"
proof-
  have "(prob_first_m_qubits_0' n deutsch_jozsa_algo) = (\<Sum>j\<in>{0,1}. (cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2)"
  proof-
    have "(k<2^(n+1)) \<and> i\<le>n \<and> \<not> select_index (n+1) i k \<longrightarrow> (\<forall>i\<in>{0..n}.( k\<notin>{2^(n-i)+1..2^((n+1)-i)})) \<and> (k\<in>{0..<2^(n+1)})"
      for k i::nat sorry
    moreover have "(\<forall>i\<in>{0..n}.( k\<notin>{2^(n-i)+1..2^((n+1)-i)})) \<and> (k\<in>{0..<2^(n+1)}) \<longrightarrow> k\<in>{0,1}" for k::nat
      using measure_if_first_n_qubits_zero_remaining_indices dim by auto
    ultimately have "(k<2^(n+1)) \<and> i\<le>n \<and> \<not> select_index (n+1) i k \<longrightarrow> k\<in>{0,1}"
      for k i::nat by blast
    moreover have "Suc 0 < 2 * 2 ^ n" 
      using dim by (simp add: Suc_lessI)
    moreover have "\<not> select_index (Suc n) 0 0" 
      by (simp add: select_index_def)
    moreover have "\<not> select_index (Suc n) 0 1" 
      by (smt One_nat_def Suc_eq_plus1 add_diff_cancel_right' calculation(3) diff_is_0_eq' diff_zero dim eq_iff 
          mod_less nat_power_eq_Suc_0_iff not_less not_less_eq_eq select_index_def)
    ultimately have "({k| k i::nat. (k<2^(n+1)) \<and> i\<le>n \<and> \<not> select_index (n+1) i k}) = {0,1}" by auto
    moreover have  "prob_first_m_qubits_0' n deutsch_jozsa_algo 
        = (\<Sum>j\<in>{k| k i::nat. (k<2^(n+1)) \<and> i\<le>n \<and> \<not> select_index (n+1) i k}. (cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2)" 
    using deutsch_jozsa_algo_result_is_state prob_first_m_qubits_0'_def by auto 
    ultimately show "(prob_first_m_qubits_0' n deutsch_jozsa_algo) = (\<Sum>j\<in>{0,1}. (cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2)" 
      using prob_first_m_qubits_0'_def by auto
  qed

  moreover have "(cmod(deutsch_jozsa_algo $$ (0,0)))\<^sup>2 = 1/2"
  proof-
    have "k < 2^n\<longrightarrow>(nat (((0::nat) div 2) \<cdot>\<^bsub>n\<^esub>  k)) = 0" for k::nat
      using bin_rep_def bin_rep_aux_def bitwise_inner_prod_def bitwise_inner_prod_with_zero by auto
    moreover have " (2::nat) ^ n = card {..<(2::nat) ^ n}" by auto
    ultimately have "(\<Sum> k < (2::nat)^n. (-1)^(nat (((0::nat) div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1))) =  (\<Sum> k < (2::nat)^n.1/(sqrt(2)^n * sqrt(2)^(n+1)))" 
      by auto
    moreover have "(cmod(deutsch_jozsa_algo $$ (0,0)))\<^sup>2 = (cmod (\<Sum> k < (2::nat)^n. (-1)^(nat ((0 div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2"
      using deutsch_jozsa_algo_result const_def assms by auto
    ultimately have "(cmod(deutsch_jozsa_algo $$ (0,0)))\<^sup>2 = (cmod(\<Sum> k < (2::nat)^n.1/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2" 
      by metis
    also have "... = (cmod((2::nat)^n/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2" 
      by auto
    also have "... = (cmod(1/(sqrt(2))))\<^sup>2 " using k1 by simp
    also have "... = 1/2" 
      by (simp add: norm_divide power2_eq_square)
    finally show "(cmod(deutsch_jozsa_algo $$ (0,0)))\<^sup>2 = 1/2" by auto
  qed

  moreover have "(cmod(deutsch_jozsa_algo $$ (1,0)))\<^sup>2 = 1/2"
  proof-
    have "k < 2^n\<longrightarrow>(nat (((1::nat) div 2) \<cdot>\<^bsub>n\<^esub>  k)) = 0" for k::nat
      using bin_rep_def bin_rep_aux_def bitwise_inner_prod_def bitwise_inner_prod_with_zero by auto
    moreover have " (2::nat) ^ n = card {..<(2::nat) ^ n}" by auto
    ultimately have "(\<Sum> k < (2::nat)^n. (-1)^(f(k)+1 + nat (((1::nat) div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1))) 
                   = (\<Sum> k < (2::nat)^n.(-1)/(sqrt(2)^n * sqrt(2)^(n+1)))" 
      using const_def assms by auto
    (*have "deutsch_jozsa_algo $$ (1, 0)= (\<Sum> k < (2::nat) ^n. (-1)^(f(k) + 1 + nat ((1 div 2) \<cdot>\<^bsub>n\<^esub> k))/(sqrt(2)^n * sqrt(2)^(n+1)))"
       using deutsch_jozsa_algo_result \<psi>\<^sub>3_values sorry (*WHY IS THIS NOT WORKING?*)*)
    moreover have "(cmod(deutsch_jozsa_algo $$ (1,0)))\<^sup>2 = (cmod (\<Sum> k < (2::nat)^n. (-1)^(f(k)+ (1::nat) + nat ((1 div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2"
      using deutsch_jozsa_algo_result const_def assms sorry
    ultimately have "(cmod(deutsch_jozsa_algo $$ (1,0)))\<^sup>2 = (cmod(\<Sum> k < (2::nat)^n. (-1)/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2" 
       by metis
    also have "... = (cmod((2::nat)^n*(-1)/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2" 
      by auto
    also have "... = (cmod((-1)/(sqrt(2))))\<^sup>2 " using k1 by simp
    also have "... = 1/2" 
      by (simp add: norm_divide power2_eq_square)
    finally show "(cmod(deutsch_jozsa_algo $$ (1,0)))\<^sup>2 = 1/2" by auto
  qed

  ultimately have "prob_first_m_qubits_0' n deutsch_jozsa_algo = 1/2 + 1/2" by auto
  then show  "prob_first_m_qubits_0' n deutsch_jozsa_algo = 1" by auto
qed






(*
value "bin_rep 1 (0 div 2)"



(*See old/first version with prob1 below still mixed up*)
lemma (in jozsa)
  fixes i::nat 
  assumes "i\<in>{0..<n}"
    and "const 0"
  shows "(prob0 (n+1) deutsch_jozsa_algo i) = 1"
proof-
  have "\<not> select_index (n+1) i k = ((k>2^(n+1)-1) \<or> (k mod 2^((n+1)-i) < 2^((n+1)-i-1)))" for k
    using assms 
    by (simp add: not_less select_index_def)
  moreover have "(prob0 (n+1) deutsch_jozsa_algo i) = 
        (\<Sum>j\<in>{k| k::nat.(k<2^(n+1)) \<and> \<not> select_index (n+1) i k}. (cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2)"
    using deutsch_jozsa_algo_result_is_state prob0_def by auto 
  ultimately have "(prob0 (n+1) deutsch_jozsa_algo i) = 
        (\<Sum>j\<in>{k| k::nat.(k<2^(n+1)) \<and> ((k>2^(n+1)-1) \<or> (k mod 2^((n+1)-i) < 2^((n+1)-i-1)))}. (cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2)"
    by auto
  have "even j \<longrightarrow> j\<in>{k| k::nat. (k<2^(n+1)) \<and> (k mod 2^((n+1)-i) < 2^(n-i))} \<longrightarrow>(cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2 = 1/(2^(n+1))"
  proof(rule impI, rule impI)
    assume a0: "even j"
    assume a1: "j\<in>{k| k::nat. (k<2^(n+1)) \<and> (k mod 2^((n+1)-i) < 2^(n-i))}"
    then have "j < dim_row deutsch_jozsa_algo" 
      using deutsch_jozsa_algo_result by auto
    then have "(cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2
              =(cmod (\<Sum> k < 2^n. (-1)^(f(k) + nat ((j div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2"
      using a0 deutsch_jozsa_algo_result by auto
    then have "(cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2
              =(cmod(\<Sum> k < 2^n. (-1)^( nat ((j div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2" 
      using const_def assms by auto
    moreover have "(cmod(\<Sum> k < 2^n. (-1)^( nat ((j div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2
                  = (cmod(\<Sum> k < 2^n. 1/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2"  
      using bitwise_inner_prod_with_zero sorry
    moreover have "(\<Sum> k < 2^n. 1/(sqrt(2)^n * sqrt(2)^(n+1))) = 1/(sqrt(2)^n * sqrt(2)^(n+1))*2^n"
      
    ultimately have  "(cmod(\<Sum> k < 2^n. 1/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2 = (cmod ( 2^n*1/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2 " 
      sorry
    have "(cmod (2^n/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2 = (cmod (1/(sqrt(2))))\<^sup>2" sorry
    have "(cmod (1/(sqrt(2))))\<^sup>2 = 1/2" sorry
    show "(cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2 = 1/(2^(n+1))" sorry
  qed
  moreover have "odd j \<longrightarrow> j\<in>{k| k::nat. (i\<le>n) \<and> (k\<le>2^(n+1)-1) \<and> (k mod 2^((n+1)-i) \<ge> 2^(n-i))} \<longrightarrow>(cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2 = 1/(2^(n+1))" 
    sorry
  moreover have "card {k| k::nat. (i\<le>n) \<and> (k\<le>2^(n+1)-1) \<and> (k mod 2^((n+1)-i) \<ge> 2^(n-i))} = 2^(n+1) " sorry
  ultimately have 
       "(\<Sum>j\<in>{k| k::nat. (i\<le>n) \<and> (k\<le>2^(n+1)-1) \<and> (k mod 2^((n+1)-i) \<ge> 2^(n-i))}. (cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2)
        = 2^(n+1)*1/(2^(n+1))" sorry
  then have  "(\<Sum>j\<in>{k| k::nat. (i\<le>n) \<and> (k\<le>2^(n+1)-1) \<and> (k mod 2^((n+1)-i) \<ge> 2^(n-i))}. (cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2)
        = 1" sorry
  then show ?thesis sorry
qed



(*Might be better to use prob0. Proof outline below kind of does that?*)
(*lemma (in jozsa)
  fixes i::nat 
  assumes "i\<in>{0..<n}"
    and "const 0"
  shows "(prob1 (n+1) deutsch_jozsa_algo i) = 0"
proof-
  have "(prob1 (n+1) deutsch_jozsa_algo i) = 
        (\<Sum>j\<in>{k| k::nat. (k\<le>2^(n+1)-1) \<and> (k mod 2^((n+1)-i) \<ge> 2^(n-i))}. (cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2)"
    using deutsch_jozsa_algo_result_is_state prob1_def select_index_def assms by auto 
  have "even j \<longrightarrow> j\<in>{k| k::nat. (k\<le>2^(n+1)-1) \<and> (k mod 2^((n+1)-i) \<ge> 2^(n-i))} \<longrightarrow>(cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2 = 1/(2^(n+1))"
  proof(rule impI, rule impI)
    assume a0: "even j"
    assume a1: "j\<in>{k| k::nat. (k\<le>2^(n+1)-1) \<and> (k mod 2^((n+1)-i) \<ge> 2^(n-i))}"
    then have "j \<le> 2^(n+1)-1" by blast
    then have "j < dim_row deutsch_jozsa_algo" 
      using deutsch_jozsa_algo_result 
      by (metis (no_types, lifting) diff_diff_cancel dim_row_mat(1) le_antisym le_trans less_numeral_extra(1) 
          nat_less_le one_le_numeral one_le_power zero_less_diff)
    then have "(cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2
              =(cmod (\<Sum> k < 2^n. (-1)^(f(k) + nat ((j div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2"
      using a0 deutsch_jozsa_algo_result by auto
    have "(cmod(\<Sum> k < 2^n. (-1)^(f(k) + nat ((j div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2
        = (cmod(\<Sum> k < 2^n. (-1)^( nat ((j div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2" 
      using const_def assms by auto
    have "k < 2^n \<longrightarrow>nat ((j div 2) \<cdot>\<^bsub>n\<^esub>  k) = 0" 
      sorry
    have "(cmod(\<Sum> k < 2^n. 1/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2 = 2^n/(cmod ((sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2 " sorry
    have "2^n/(cmod ((sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2 = 2^n/(2^n * 2^(n+1))" sorry
    have "2^n/(2^n * 2^(n+1)) = 1/(2^(n+1))" sorry
    show "(cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2 = 1/(2^(n+1))" sorry
  qed
  moreover have "odd j \<longrightarrow> j\<in>{k| k::nat. (i\<le>n) \<and> (k\<le>2^(n+1)-1) \<and> (k mod 2^((n+1)-i) \<ge> 2^(n-i))} \<longrightarrow>(cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2 = 1/(2^(n+1))" 
    sorry
  moreover have "card {k| k::nat. (i\<le>n) \<and> (k\<le>2^(n+1)-1) \<and> (k mod 2^((n+1)-i) \<ge> 2^(n-i))} = 2^(n+1) " sorry
  ultimately have 
       "(\<Sum>j\<in>{k| k::nat. (i\<le>n) \<and> (k\<le>2^(n+1)-1) \<and> (k mod 2^((n+1)-i) \<ge> 2^(n-i))}. (cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2)
        = 2^(n+1)*1/(2^(n+1))" sorry
  then have  "(\<Sum>j\<in>{k| k::nat. (i\<le>n) \<and> (k\<le>2^(n+1)-1) \<and> (k mod 2^((n+1)-i) \<ge> 2^(n-i))}. (cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2)
        = 1" sorry
  then show ?thesis sorry
qed*)



(*
  have "\<not> select_index (n+1) i k = (i > n \<or> (k>2^(n+1)-1) \<or> (k mod 2^((n+1)-i) < 2^((n+1)-i-1)))"
    by (simp add: not_less select_index_def)
  moreover have "(prob0 (n+1) deutsch_jozsa_algo i) = 
        (\<Sum>j\<in>{k| k::nat.(k<2^(n+1)) \<and> \<not> select_index (n+1) i k}. (cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2)"
    using deutsch_jozsa_algo_result_is_state prob0_def by auto 
  ultimately have "(prob0 (n+1) deutsch_jozsa_algo i) = 
        (\<Sum>j\<in>{k| k::nat.(k<2^(n+1)) \<and> \<not> select_index (n+1) i k}. (cmod(deutsch_jozsa_algo $$ (j,0)))\<^sup>2)"*)


(*Why should only even elements be selected, seems like this in my slides but makes sense???
Do the same for odd ones and show that
  have "(i\<le>n) \<and> (k\<le>2^(n+1)-1) \<and> (k mod 2^((n+1)-i) \<ge> 2^(n-i)) \<longrightarrow> nat ((j div 2) \<cdot>\<^bsub>n\<^esub>  k) = 1" ?
If this holds it would be great! *)

(*
abbreviation (in jozsa) \<psi>\<^sub>3:: "complex Matrix.mat" where
"\<psi>\<^sub>3  \<equiv> Matrix.mat (2^(n+1)) 1 (\<lambda>(i,j). if even i
                                         then (\<Sum> k < 2^n. (-1)^(f(k) + nat ((i div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1))) 
                                          else (\<Sum> k < 2^n. (-1)^(f(k) + 1 + nat ((i div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1))) )"

*)
theorem (in jozsa) deutsch_jozsa_algo_is_correct:
  shows "\<forall>i\<in>{0..<n}.(prob1 (n+1) deutsch_jozsa_algo i) = 0 \<longrightarrow> is_const"
    and "\<exists>i\<in>{0..<n}.(prob1 (n+1) deutsch_jozsa_algo i) \<noteq> 0 \<longrightarrow> is_balanced"
  sorry
*)

end