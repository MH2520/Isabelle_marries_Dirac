theory Quantum_Fourier_Transform
imports
  Quantum
  Tensor
  MoreTensor
  FFT.FFT
begin

lemma root_unit_length [simp]:
  fixes "n":: nat
  shows "root n * cnj(root n) = 1"
  by (simp add: root_def complex_eq_iff)

definition R:: "nat \<Rightarrow> complex Matrix.mat" where (* AB: What is the name of this gate ? *)
"R n \<equiv> Matrix.mat 2 2 (\<lambda>(i,j). if i = j then (if i = 0 then 1 else root (2^n)) else 0)"

lemma R_is_gate [simp]:
  fixes "n":: nat
  shows "gate 1 (R n)"
proof
  show "dim_row (R n) = 2^1" by (simp add: R_def)
  show "square_mat (R n)" by (simp add: R_def)
  show "unitary (R n)"
    apply (auto simp add: one_mat_def R_def times_mat_def unitary_def)
    apply (rule cong_mat)
    by (auto simp: scalar_prod_def complex_eqI algebra_simps)
qed

definition fourier:: "nat \<Rightarrow> complex Matrix.mat" where
"fourier n \<equiv> Matrix.mat (2^n) (2^n) (\<lambda>(i,j). (root (2^n))^(i*j) / sqrt(2^n))"

lemma fourier_inv_0 [simp]: (* AB: this lemma is not true. Take n = 0, then the sum is 1 *)
  fixes "i" "j":: nat 
  assumes "i < 2^n" and "j < 2^n" and "i \<noteq> j"
  shows "(\<Sum>k = 0..<2^n. root (2^n) ^(i*k) * cnj (root (2^n)) ^(j*k) /
         (complex_of_real (sqrt (2^n)) * complex_of_real (sqrt (2^n)))) = 0"
  sorry

lemma fourier_inv_1 [simp]:
  fixes "j"::nat assumes "j < 2^n"
  shows "(\<Sum>i = 0..<2^n. root (2^n) ^ (j*i) * cnj (root (2^n)) ^ (j*i) /
         (complex_of_real (sqrt (2^n)) * complex_of_real (sqrt (2^n)))) = 1"
proof-
  have "\<And>i. root (2^n) ^ (j*i) * cnj (root (2^n)) ^ (j*i) = 1"
    by (metis power_mult_distrib power_one root_unit_length)
  then have "(\<Sum>i = 0..<2^n. root (2^n) ^ (j*i) * cnj (root (2^n)) ^ (j*i) /
             (complex_of_real (sqrt (2^n)) * complex_of_real (sqrt (2^n)))) = 2^n /
             (complex_of_real (sqrt (2^n)) * complex_of_real (sqrt (2^n)))"
    by simp
  then show ?thesis
    apply simp
    by (metis sqrt_power_of_2 of_real_mult of_real_numeral of_real_power)
qed

lemma fourier_is_gate [simp]:
  "gate n (fourier n)"
proof
  show "dim_row (fourier n) = 2^n" by (simp add: fourier_def)
  moreover show "square_mat (fourier n)" by (simp add: fourier_def)
  moreover have "(fourier n) * ((fourier n)\<^sup>\<dagger>) = 1\<^sub>m (2^n)"
    apply (auto simp add: one_mat_def fourier_def times_mat_def unitary_def)
    apply (rule cong_mat)
    by (auto simp: scalar_prod_def complex_eqI algebra_simps)
  moreover have "((fourier n)\<^sup>\<dagger>) * (fourier n)= 1\<^sub>m (2^n)"
    apply (auto simp add: one_mat_def fourier_def times_mat_def unitary_def)
    apply (rule cong_mat)
    by (auto simp: scalar_prod_def complex_eqI algebra_simps)
  ultimately show "unitary (fourier n)" by (simp add: unitary_def)
qed


end