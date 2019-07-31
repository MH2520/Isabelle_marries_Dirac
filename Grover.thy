(*
Authors: 
  Hanna Lachnitt, TU Wien, lachnitt@student.tuwien.ac.at
  Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk
*)

theory Grover
imports                           
  (*MoreTensor*)
  Binary_Nat
  Deutsch_Jozsa (*Just for now so that I don't have to copy everything*)
begin

abbreviation zero where "zero \<equiv> unit_vec 2 0"
abbreviation one where "one \<equiv> unit_vec 2 1" 

lemma ket_zero_is_state: 
  shows "state 1 |zero\<rangle>"
  by (simp add: state_def ket_vec_def cpx_vec_length_def numerals(2))

lemma ket_one_is_state:
  shows "state 1 |one\<rangle>" 
  by (simp add: state_def ket_vec_def cpx_vec_length_def numerals(2))

locale grover =
  fixes f:: "nat \<Rightarrow> nat" and n::nat and x:: "nat" 
  fixes q_oracle :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat"
  assumes fun_dom: "f \<in> ({(i::nat). i < 2^n} \<rightarrow>\<^sub>E {0,1})"
  assumes dim: "n\<ge>1"
  assumes searched_dom: "x \<in> {(i::nat). i < 2^n}"
  assumes searched: "\<forall>i < 2^n. f(i) = 1 \<longleftrightarrow> i=x" 
  assumes q_oracle_app: "\<forall>(A::complex Matrix.mat). dim_row A = 2^n \<and> dim_col A = 1 \<longrightarrow>   
                            q_oracle (A \<Otimes> (H * |one\<rangle>))
                         = (Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (A$$(i,j))))  \<Otimes> (H * |one\<rangle>)"

context grover
begin

definition iterations::nat where
"iterations = nat \<lceil>(pi/4 * sqrt(2^n))\<rceil>"

lemma iterations_nat [simp]:
  shows "nat \<lceil>(pi/4 * sqrt(2^n))\<rceil> = \<lceil>(pi/4 * sqrt(2^n))\<rceil>"
proof-
  have "sqrt(2^n) \<ge> 0" using dim by auto
  then have "(pi/4 * sqrt(2^n)) \<ge> 0" by auto
  then have "\<lceil>(pi/4 * sqrt(2^n))\<rceil> \<ge> 0" by linarith
  then show ?thesis by auto
qed

lemma f_ge_0: 
  shows "\<forall>x. (f x \<ge> 0)" by simp

lemma f_dom_not_zero: 
  shows "f \<in> ({i::nat. n \<ge> 1 \<and> i < 2^n} \<rightarrow>\<^sub>E {0,1})" 
  using fun_dom dim by simp

lemma f_values: "\<forall>x \<in> {(i::nat). i < 2^n} .(f x = 0 \<or> f x = 1)" 
  using fun_dom by auto

lemma search_function_zero [simp]:
  assumes "i < 2^n" and "i \<noteq> x"
  shows "f(i) = 0" 
  using fun_dom searched f_values assms
  by blast

lemma search_function_one [simp]:
  assumes "i < 2^n" and "i = x"
  shows "f(i) = 1" 
  using fun_dom searched f_values assms
  by blast

end (*context grover*)

definition(in grover) diffusion_operator::"complex Matrix.mat" where
"diffusion_operator = Matrix.mat (2^n) (2^n) (\<lambda>(i,j). if i=j then ((1-2^(n-1))/2^(n-1)) else 1/(2^(n-1)))"

notation(in grover) diffusion_operator ("D")

lemma (in grover) app_oracle:
  fixes \<alpha> \<beta>::nat
  assumes "v = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>))"
  assumes "w = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -\<alpha> else \<beta>))"
  shows "q_oracle (v \<Otimes> (H * |one\<rangle>)) = (w \<Otimes> (H * |one\<rangle>))"
proof-
  have "dim_row v = 2^n \<and> dim_col v = 1" using assms by auto
  then have "q_oracle (v \<Otimes> (H * |one\<rangle>)) = (Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (v$$(i,j)))) \<Otimes> (H * |one\<rangle>)"
    using q_oracle_app assms by blast
  moreover have "(Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (v$$(i,j)))) = w" 
  proof{
    fix i j::nat
    assume "i < dim_row w" 
    and    "j < dim_col w"
    then have f0: "i < 2^n \<and> j=0" using assms by auto
    moreover have "i=x \<longrightarrow> (-1)^f(i) = (-(1::real))" 
      using searched_dom grover_axioms by auto
    moreover have "i\<noteq>x \<and> i < 2^n  \<longrightarrow> (-1)^f(i) = 1" for i::nat
      using searched_dom grover_axioms search_function_zero by auto
    ultimately show "(Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (v$$(i,j)))) $$ (i,j) = w $$ (i,j)" 
      using assms f0 by auto
  next
    show "dim_row (Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (v$$(i,j)))) = dim_row w" 
      by (simp add: assms(2))
  next
    show "dim_col (Matrix.mat (2^n) 1 (\<lambda>(i,j). (-1)^f(i) * (v$$(i,j)))) = dim_col w" 
      by (simp add: assms(2))
  }qed
  ultimately show "q_oracle (v \<Otimes> (H * |one\<rangle>)) = (w \<Otimes> (H * |one\<rangle>))" by blast
qed

lemma sum_without_x:
  fixes n i::nat
      and a::real
  assumes "i<n" and "n\<ge>1"
  shows "(\<Sum> k \<in> ({0 ..< n}-{i}). a) = (n-1)*a "  using assms by auto

lemma sum_without_x_and_i: (*Put together with last lemma?*) 
  fixes n i x::nat
      and a ::real
  assumes "i<n" and "x<n" and "n\<ge>2" and "i\<noteq>x"
  shows "(\<Sum> k \<in> ({0 ..< n}-{i,x}). a) = (n-(2::real))*a" using assms by auto

lemma (in grover) pow_2_n_half[simp]: (*Give better name*)
  shows "2^n-2^(n-1) = (2::real)^(n-1)" 
proof (induction n rule: ind_from_1)
  show "n\<ge>1" using dim by auto
next
  show "2^1-2^(1-1) = (2::real)^(1-1)" by simp
next
  fix n
  assume a0: "n\<ge>1" and IH: "2^n-2^(n-1) = (2::real)^(n-1)"  
  then have "2^(n+1)-2^n = (2::real)*(2^n -2^(n-1))" by simp
  also have "... = (2::real)* 2^(n-1)" using IH by simp
  also have "... = (2::real)^n" 
    using IH le_add_diff_inverse2 by linarith
  finally show "2^(Suc n)-2^((Suc n)-1) = (2::real)^((Suc n)-1)" by simp
qed

lemma pow_2_minus_one: (*Find name for this*)
  assumes "n\<ge>2"
  shows "(2::real)^(n-1) - 2 + 1 = 2^(n-1) - 1"
proof -
  have "(2::nat) \<le> 2 ^ (n-1)" 
    by (metis (full_types) Suc_1 Suc_eq_plus1 add_le_imp_le_diff assms le_add2 power_increasing power_one_right)
  then show ?thesis
    by linarith
qed

lemma (in grover) simplify_\<beta>_term: (*Name needed*)
  fixes \<beta>::real
  shows "(2^n - (2::real)) /(2^(n-1)) * \<beta> + ((1-2^(n-1))/2^(n-1)) * \<beta> = (2^(n-1) - 1) /2^(n-1) * \<beta>" 
proof-
  have "(2^n - 2) /(2 ^ (n-1))+((1-2^(n-1))/2^(n-1)) = ((2^n - (2::real)) + (1 - 2^(n-1))) * 1/(2^(n-1))"
    using comm_semiring_class.distrib[of "(2^n - (2::real))" "(1-2^(n-1))" "1/(2^(n-1))"] by auto
  also have "... = (2^n -2^(n-1)- (2::real)+1) * 1/(2^(n-1))" 
    by (simp add: dim)
  also have "... =  (2^(n-1)- 1) * 1/(2^(n-1))" 
    using dim pow_2_n_half by auto
  moreover have "(2^n - 2) /(2^(n-1)) * \<beta> + ((1 - 2^(n-1))/2^(n-1)) * \<beta> 
               = ((2^n - 2) /(2^(n-1)) + ((1 - 2^(n-1))/2^(n-1))) * \<beta>"
    by (simp add: comm_semiring_class.distrib)
  ultimately show  "(2^n - (2::real)) /(2^(n-1)) * \<beta> + ((1-2^(n-1))/2^(n-1)) * \<beta> = (2^(n-1) - 1) /2^(n-1) * \<beta>" 
    by auto
qed

lemma (in grover) app_diffusion_op:
  fixes \<alpha> \<beta>::real (*Might have to change that into complex*)
  assumes "v = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then -\<alpha> else \<beta>))"
    and "w = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then ((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>
                                             else 1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta> ))"
    and "state n v" 
  shows "D * v = w"
proof
  fix i j::nat
  assume a0: "i < dim_row w" 
  and    a1: "j < dim_col w"
  then have f0: "i < 2^n \<and> j=0" using assms by auto
  then have "(D * v) $$ (i,j) = (\<Sum> k \<in> {0 ..< 2^n}. (Matrix.row D i) $ k * (Matrix.col v j) $ k)"
    using assms atLeast0LessThan diffusion_operator_def by auto
  then have f1: "(D * v) $$ (i,j) =
                (\<Sum> k \<in> ({0 ..< 2^n}-{i}). (Matrix.row D i) $ k * (Matrix.col v j) $ k)
              + (Matrix.row D i) $ i * (Matrix.col v j) $ i" 
    by (simp add: f0 sum_diff1)
  show "(D * v) $$ (i,j) = w  $$ (i,j)" 
  proof(rule disjE) 
    show "i=x \<or> i\<noteq>x" by auto
  next
    assume a2: "i=x" 
    moreover have "(\<Sum> k \<in> ({0 ..< 2^n}-{i}).  1/(2^(n-1)) * \<beta>) = (2^n - 1) * \<beta> / 2 ^ (n-1)" 
      using sum_without_x[of i "2^n" "(1/(2^(n-1)) * \<beta>)::real"] dim f0 
      by (simp add: of_nat_diff)
    ultimately have f2: "(D * v) $$ (i,j) = (2^n - 1) * \<beta> / 2 ^ (n-1) + ((1-2^(n-1))/2^(n-1)) * (-\<alpha>)" 
      using assms diffusion_operator_def a2 f0 f1
      by (simp add: of_nat_diff)
    moreover have f3: "((1-2^(n-1))/2^(n-1)) * (-\<alpha>) = ((2^(n-1)-1)/2^(n-1))*\<alpha>" 
      by (smt divide_minus_left mult_minus_left mult_minus_right of_int_minus of_int_of_nat_eq)
    ultimately have "(D * v) $$ (i,j) = (2^n - 1) * \<beta> / 2 ^ (n-1) + ((2^(n-1)-1)/2^(n-1))*\<alpha>" 
      by (simp add: f2 f3)
    then have "(D * v) $$ (i,j) = ((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta>"
      by (simp add: of_nat_diff)
    then show  "(D * v) $$ (i,j) = w $$ (i,j)" using assms a2 a0 a1 f1 by auto
  next
    assume a2: "i\<noteq>x "
    have "(\<Sum> k \<in> ({0 ..< 2^n}-{i}). (Matrix.row D i) $ k * (Matrix.col v j) $ k) =
                   (\<Sum> k \<in> ({0 ..< 2^n}-{i,x}). (Matrix.row D i) $ k * (Matrix.col v j) $ k)
                   + ((Matrix.row D i) $ x * (Matrix.col v j) $ x)" 
      using sum_diff1 a2 f0
      by (smt Diff_insert2 add.commute atLeast0LessThan finite_Diff finite_atLeastLessThan 
          insertE insert_Diff_single insert_absorb lessThan_iff mem_Collect_eq searched_dom sum.insert_remove)


    moreover have "(\<Sum> k \<in> ({0 ..< 2^n}-{i,x}). (Matrix.row D i) $ k * (Matrix.col v j) $ k) = (2^n - (2::real)) /(2 ^ (n-1)) * \<beta>" 
    proof-{
        have "i < 2^n \<and> x < 2^n \<and> 2 \<le> (2::nat)^n \<and> i \<noteq> x "
          using a2 f0 grover.searched_dom grover_axioms by fastforce
        then have "(\<Sum> k \<in> ({0 ..< 2^n}-{i,x}). 1/((2::real)^(n-1)) * \<beta>) = (real 2^n - 2) * (1/2^(n-1) * \<beta>)"
          using sum_without_x_and_i[of i "2^n" x "1/((2::real)^(n-1)) * \<beta>"] assms by auto
        moreover have "(\<Sum> k \<in> ({0 ..< 2^n}-{i,x}). (Matrix.row D i) $ k * (Matrix.col v j) $ k) =
              (\<Sum> k \<in> ({0 ..< 2^n}-{i,x}). 1/((2::real)^(n-1)) * \<beta>)" 
          using diffusion_operator_def a2 f0 assms by auto
        ultimately show  "(\<Sum> k \<in> ({0 ..< 2^n}-{i,x}). (Matrix.row D i) $ k * (Matrix.col v j) $ k) 
                        = (2^n - (2::real)) /((2::real) ^ (n-1)) * \<beta>" 
          by (metis (no_types, lifting) divide_cancel_left nonzero_divide_mult_cancel_left of_nat_numeral 
              times_divide_eq_left times_divide_eq_right)
    }qed

    moreover have "((Matrix.row D i) $ x * (Matrix.col v j) $ x) = 1/2^(n-1)*-\<alpha>" 
      using diffusion_operator_def a2 assms f0 searched_dom by auto
    moreover have "(Matrix.row D i) $ i * (Matrix.col v j) $ i = ((1-2^(n-1))/2^(n-1))*\<beta>" 
      using diffusion_operator_def a2 assms f0 searched_dom by auto
    ultimately have  "(D * v) $$ (i,j) = (2^n - (2::real)) /(2 ^ (n-1)) * \<beta> + 1/2^(n-1)*-\<alpha> +((1-2^(n-1))/2^(n-1))*\<beta>" 
      using f1 by auto 
    moreover have "(2^n - (2::real)) /(2 ^ (n-1)) * \<beta> +((1-2^(n-1))/2^(n-1))*\<beta> = (2^(n-1)-1)/2^(n-1)*\<beta>" 
      using simplify_\<beta>_term assms by auto
    ultimately have "(D * v) $$ (i,j) = 1/2^(n-1)*-\<alpha> + (-1+2^(n-1))/2^(n-1)*\<beta>"
      by (metis (mono_tags, hide_lams) add_divide_distrib combine_common_factor power_one_over ring_class.ring_distribs(1) 
          semiring_normalization_rules(24) semiring_normalization_rules(7) uminus_add_conv_diff)
    then show "(D * v) $$ (i,j) = w $$ (i,j)" using assms a2 f0 by auto
  qed
next
  show "dim_row (D * v) = dim_row w" using assms diffusion_operator_def by auto 
next 
  show "dim_col (D * v) = dim_col w" using assms diffusion_operator_def by auto 
qed

lemma (in grover) app_diffusion_op_index_x_recurence:
  fixes \<alpha> \<beta>::real
  shows "((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta> 
       = ((-\<alpha> + (2^n-1)*\<beta>)/2^(n-1)) + \<alpha>" 
proof-
  have "((2^(n-1)-1)/2^(n-1))*\<alpha> = ((2^(n-1)-1)*\<alpha>)/2^(n-1)" by simp
  moreover have "(2^(n-1)-1)*\<alpha> = (2^(n-1)*\<alpha>) + (-1*\<alpha>)" 
    by (metis add.inverse_inverse comm_semiring_class.distrib diff_minus_eq_add)
  ultimately have "((2^(n-1)-1)/2^(n-1))*\<alpha> = \<alpha> + (-\<alpha>)/2^(n-1)" 
    by (simp add: diff_divide_distrib)
  then have "((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta> = \<alpha> + (-\<alpha>)/2^(n-1) + (2^n-1)/(2^(n-1))*\<beta>" 
    by auto
  then show "((2^(n-1)-1)/2^(n-1))*\<alpha> + (2^n-1)/(2^(n-1))*\<beta> = ((-\<alpha> + (2^n-1)*\<beta>)/2^(n-1)) + \<alpha>" 
    by (metis (no_types, hide_lams) diff_divide_distrib divide_minus_left is_num_normalize(1) 
        mult.commute semiring_normalization_rules(24) times_divide_eq_right uminus_add_conv_diff)
qed

definition (in grover) amplitude_x ::"complex Matrix.mat \<Rightarrow> real"  where
"amplitude_x v \<equiv> (cmod(v $$ (x,0)))\<^sup>2"

notation(in grover) amplitude_x ("amp") (*Rather ampx or amp_x?*)

lemma divide_le:
  fixes a b c::real
  assumes "a \<le> b * c" 
  and "b \<ge> 1"
shows "a/b \<le> c" 
  using assms 
  by (metis (full_types) divide_right_mono linear nonzero_mult_div_cancel_left not_one_le_zero order_trans)
  
lemma (in grover) lower_bound_on_\<beta>: (*proposition 2.3*)
  fixes \<alpha> \<beta>::real 
  assumes "v = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>))"
      and "state n v" 
      and "amp v \<le> 1/4" and "n\<ge>2" and "\<beta>\<ge>0"
    shows "\<beta> \<ge> sqrt(3/(4*(2^n-1)))"
proof-
  have "1 = (\<Sum>i<2^n. (cmod (v $$ (i,0)))\<^sup>2)" 
    using assms cpx_vec_length_def state_def by auto
  also have "... = (\<Sum>i\<in>({0..<2^n}-{x}). (cmod (v $$ (i,0)))\<^sup>2) +  (cmod (v $$ (x,0)))\<^sup>2"
    by (smt atLeast0LessThan finite_atLeastLessThan insert_Diff insert_Diff_single lessThan_iff mem_Collect_eq 
        searched_dom sum.insert_remove)
  also have "... = real(2^n - 1)* \<beta>\<^sup>2 + (cmod (v $$ (x,0)))\<^sup>2" 
    using assms sum_without_x[of x "2^n" "\<beta>\<^sup>2"] fun_dom one_add_one searched_dom by auto
  also have "... = (2^n - 1) * \<beta>\<^sup>2 + (cmod (v $$ (x,0)))\<^sup>2"  by (simp add: of_nat_diff)
  also have "... \<le> (2^n - 1) * \<beta>\<^sup>2 + 1/4" using assms amplitude_x_def by auto
  finally have "1 \<le> (2^n - 1) * \<beta>\<^sup>2 + 1/4" by auto
  then have "3/4 \<le> (2^n - 1) * \<beta>\<^sup>2" by linarith
  moreover have "((2::real)^n - 1) \<ge> 1" using assms pow_2_n_half by auto
  ultimately have "3/(4 * (2^n - 1)) \<le> \<beta>\<^sup>2" 
    using assms divide_le[of "3/4" "(2^n - 1)" "\<beta>\<^sup>2"] of_nat_diff by auto
  then show "\<beta> \<ge> sqrt(3/(4*(2^n-1)))" using dim assms real_le_lsqrt by auto
qed 

lemma h1 [simp]: (*Find good name*)
  fixes n::nat
  assumes "n\<ge>1"
  shows "(2^n-1)/2^(n-1) \<ge> (1::real)" 
proof-
  have "(2^n-(1::real))/2^(n-1) = 2^n/2^(n-1) - 1/2^(n-1)" 
    using assms diff_divide_distrib by blast
  moreover have "(2::real) ^ n = 2 * 2 ^ (n - 1)"
      by (metis (no_types) assms le_add_diff_inverse power_add semiring_normalization_rules(33))
  ultimately have "(2^n-(1::real))/2^(n-1) = 2 - 1/2^(n-1)" by auto
  then show  "(2^n-1)/2^(n-1) \<ge> (1::real)" using assms by auto
qed


lemma (in grover) lower_bound_on_mean: (*also style does not work why? Would be helpful*)
  fixes \<alpha> \<beta>::real 
  assumes "v = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>))" (*All assumptions needed?*)
      and "state n v" 
      and "\<alpha> \<le> 1/2" and "n\<ge>2" and "\<beta>\<ge>0" and "\<alpha>\<ge>0" (*might be possible to take this one out*)
  shows "((-\<alpha> + (2^n-1)*\<beta>)/2^(n-1)) \<ge> 1/(2*(sqrt(2)^n))"
proof-
  have "((-\<alpha> + (2^n-1)*\<beta>)/2^(n-1)) = -\<alpha>/2^(n-1) + ((2^n-1)*\<beta>)/2^(n-1)" 
    using add_divide_distrib by blast
  then have f0: "((-\<alpha> + (2^n-1)*\<beta>)/2^(n-1)) = -\<alpha>/2^(n-1) + \<beta>*((2^n-1))/2^(n-1)" 
    by auto
  have "amp v = (cmod (\<alpha>))\<^sup>2" using amplitude_x_def assms searched_dom by auto
  then have "amp v \<le> 1/4" 
    using amplitude_x_def assms searched_dom cmod_def 
    by (smt cmod_power2 norm_of_real real_sqrt_divide real_sqrt_four real_sqrt_less_iff real_sqrt_one)
  moreover have "((2^n-1))/2^(n-1) \<ge> (1::nat)" using assms h1 by auto
  moreover have "\<beta> \<ge> sqrt(3/(4*(2^n-1)))" using lower_bound_on_\<beta>[of v \<alpha> \<beta>] assms calculation by auto
  ultimately have "\<beta>*((2^n-1))/2^(n-1) \<ge> sqrt(3/(4*(2^n-1))) * (2^n-1)/2^(n-1)" 
    using assms  
    by (simp add: divide_right_mono two_realpow_ge_one)
  then have "((-\<alpha> + (2^n-1)*\<beta>)/2^(n-1)) \<ge> -\<alpha>/2^(n-1) + sqrt(3/(4*(2^n-1))) * (2^n-1)/2^(n-1)" 
    using f0 by auto
  then have "... \<ge> -(1/2)/2^(n-1) + sqrt(3/(4*(2^n-1))) * (2^n-1)/2^(n-1)" 
    using assms amplitude_x_def 
    by (smt divide_right_mono zero_le_power)
  then have "... \<ge> (-(1/2) + sqrt(3/(4*(2^n-1))) * (2^n-1))*1/2^(n-1)"     
    using comm_semiring_class.distrib[of "-(1/2)" "sqrt(3/(4*(2^n-1))) * (2^n-1)" "1/2^(n-1)"] by auto
  then have "... \<ge> (-(1/2) + sqrt(1/4)*sqrt(3/(2^n-1)) * (2^n-1))*1/2^(n-1)" 
    by (metis (no_types, hide_lams) comm_monoid_mult_class.mult_1 divide_divide_eq_left mult.commute real_sqrt_mult 
        times_divide_eq_left times_divide_eq_right uminus_add_conv_diff)
  then have "... \<ge> (-(1/2) + 1/2*sqrt(3/(2^n-1)) * (2^n-1))*1/2^(n-1)" 
    by (simp add: real_sqrt_divide)
  moreover have "(-(1/2) + 1/2*sqrt(3/(2^n-1)) * (2^n-1)) = 1/2 * (-1 + sqrt(3/(2^n-1)) * (2^n-1))" 
    by simp
  moreover have "(-(1/2) + 1/2*sqrt(3/(2^n-1)) * (2^n-1))*1/2^(n-1) = (1/2 * (-1 + sqrt(3/(2^n-1)) * (2^n-1))) *1/2^(n-1)" 
    using calculation by presburger
  ultimately have "((-\<alpha> + (2^n-1)*\<beta>)/2^(n-1)) \<ge> (1/2 * (-1 + sqrt(3/(2^n-1)) * (2^n-1))) *1/2^(n-1)" by auto
  then have "... \<ge> (-1 + sqrt(3/(2^n-1)) * sqrt((2^n-1)\<^sup>2)) *1/2/2^(n-1)"            
    using assms by auto
  then have f1: "... \<ge> (-1 + sqrt(3*(2^n-1)\<^sup>2/(2^n-1))) *1/2/2^(n-1)" 
    by (metis (mono_tags, hide_lams) real_sqrt_mult times_divide_eq_left)
  have "(2^n-1) \<ge> 1" sorry
  moreover have "(2^n-1)\<^sup>2/(2^n-1) = (2^n-1)" sorry
  ultimately have "sqrt(3*(2^n-1)\<^sup>2/(2^n-1)) = sqrt(3*(2^n-1))" using dim sorry
 




  finally have "((-\<alpha> + (2^n-1)*\<beta>)/2^(n-1)) \<ge> (-(1/2) + sqrt(3*2^n-3))/2^(n-1)" sorry
  then show "((-\<alpha> + (2^n-1)*\<beta>)/2^(n-1)) \<ge> 1/(2*(sqrt(2)^n))" sorry
qed


lemma (in grover)
  fixes \<alpha> \<beta>::real (*In the end I might change these to complex, or make lemma that shows that always real*) 
  assumes "v = (Matrix.mat (2^n) 1 (\<lambda>(i,j). if i=x then \<alpha> else \<beta>))"
      and "state n v" 
      and "amp v \<le> 1/4" and "n\<ge>2" and "\<beta>\<ge>0"
    shows "amp (D * (q_oracle v)) \<ge> amp v + 1/(sqrt(2)^n)"
  oops
(*Show by induction that \<beta> is positiv after each round*)



abbreviation(in grover) start_state:: "complex Matrix.mat" where
"start_state \<equiv> (\<psi>\<^sub>1\<^sub>0 n)*(H * |one\<rangle>)"

primrec(in grover) grover_iteration::"nat\<Rightarrow>complex Matrix.mat\<Rightarrow>complex Matrix.mat" where
"grover_iteration 0 v = v"|
"grover_iteration (Suc n) v = grover_iteration n (D * (q_oracle v)) "

lemma (in grover)
  shows "(grover_iteration iterations start_state) = end" (*Find out what end is*)
  sorry



definition(in grover) grover_algo::"complex Matrix.mat" where
"grover_algo = (grover_iteration iterations (((H \<otimes>\<^bsup>n\<^esup>) * ( |zero\<rangle> \<otimes>\<^bsup>n\<^esup>))*(H * |one\<rangle>)))" 


lemma (in grover)
  shows "(cmod(grover_algo $$ (x,0)))\<^sup>2 \<ge> XXX" (*Put in right prob here*)
  sorry








(* assume a2: "i=x" 
    moreover have "(\<Sum> k \<in> {0 ..< 2^n}. (Matrix.row D i) $ k * (Matrix.col v j) $ k) = 
                   (\<Sum> k \<in> ({0 ..< 2^n}-{i}). (Matrix.row D i) $ k * (Matrix.col v j) $ k)
                 + (Matrix.row D i) $ i * (Matrix.col v j) $ i" 
      by (simp add: f0 sum_diff1)
    moreover have "i\<noteq>k \<and> k<2^n \<longrightarrow> (Matrix.row D i) $ k * (Matrix.col v j) $ k = 1/((2::nat)^(n-1)) * \<beta>" for k::nat
      using assms diffusion_operator_def a2 f0 by auto
    moreover have "i=k \<and> k<2^n \<longrightarrow> (Matrix.row D i) $ i * (Matrix.col v j) $ i = ((1-(2::nat)^n)/(2::nat)^(n-1)) * (-\<alpha>)" for k::nat
      using assms diffusion_operator_def by auto
    ultimately have "(\<Sum> k \<in> {0 ..< 2^n}. (Matrix.row D i) $ k * (Matrix.col v j) $ k) = 
                     (\<Sum> k \<in> ({0 ..< 2^n}-{i}).  1/((2::nat)^(n-1)) * \<beta>)
                   + ((1-(2::nat)^n)/(2::nat)^(n-1)) * (-\<alpha>)" 
      using assms diffusion_operator_def a2 f0 by auto
  moreover have "(\<Sum> k \<in> ({0 ..< 2^n}-{i}).  1/((2::nat)^(n-1)) * \<beta>) = of_nat (2 ^ n - Suc 0) * of_nat \<beta> / 2 ^ (n - Suc 0)" 
    using sum_without_x[of i "2^n" "1/((2::nat)^(n-1)) * \<beta>"] dim f0 by auto
  moreover have "of_nat (2 ^ n - Suc 0) * of_nat \<beta> / 2 ^ (n - Suc 0) = (2 ^ n - Suc 0) * \<beta> / 2 ^ (n - Suc 0)" by simp
  ultimately have "(\<Sum> k \<in> {0 ..< 2^n}. (Matrix.row D i) $ k * (Matrix.col v j) $ k)
                    = (2 ^ n - Suc 0) * \<beta> / 2 ^ (n - Suc 0)  + ((1-(2::nat)^n)/(2::nat)^(n-1)) * (-\<alpha>)" 
    by presburger
  moreover have "w $$ (i,j) = ((2::nat)^n-1)/(2::nat)^(n-1)*\<beta> +((1-(2::nat)^n)/(2::nat)^(n-1))*(-\<alpha>)" 
    using assms a2 a0 a1 by auto 
  ultimately have  "(D * v) $$ (i,j) = w $$ (i,j)" using f1 by simp

*)























end