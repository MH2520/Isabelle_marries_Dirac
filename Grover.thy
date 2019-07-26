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
  declare [[show_types]]
declare [[show_sorts]]


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
  assumes fun_dim: "n\<ge>1"
  assumes searched_dom: "x \<in> {(i::nat). i < 2^n}"
  assumes searched: "\<forall>i < 2^n. f(i) = 1 \<longleftrightarrow> i=x" 
(*Rephrase this without H on one in more general form? See if we need it*)
  assumes q_oracle_app: "\<forall>(A::nat\<Rightarrow>complex).  q_oracle (Matrix.mat (2^n) 1 (\<lambda>(i,j). A i) \<Otimes> (H * |one\<rangle>)) 
                         = Matrix.mat (2^(n+1)) 1 (\<lambda>(i,j). if (even i) then (-(1::nat))^f(i div 2) * A i 
                                      else (-(1::nat))^(f(i div 2)+1)* A i)"


context grover
begin

definition iterations::nat where
"iterations = nat \<lceil>(pi/4 * sqrt(2^n))\<rceil>"

lemma iterations_nat [simp]:
  shows "nat \<lceil>(pi/4 * sqrt(2^n))\<rceil> = \<lceil>(pi/4 * sqrt(2^n))\<rceil>"
proof-
  have "sqrt(2^n) \<ge> 0" using fun_dim by auto
  then have "(pi/4 * sqrt(2^n)) \<ge> 0" by auto
  then have "\<lceil>(pi/4 * sqrt(2^n))\<rceil> \<ge> 0" by linarith
  then show ?thesis by auto
qed

lemma f_ge_0: 
  shows "\<forall>x. (f x \<ge> 0)" by simp

lemma f_dom_not_zero: 
  shows "f \<in> ({i::nat. n \<ge> 1 \<and> i < 2^n} \<rightarrow>\<^sub>E {0,1})" 
  using fun_dom fun_dim by simp

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

lemma q_oracle_on_x:
  fixes A::"nat\<Rightarrow>complex"
  assumes "i < 2^(n+1)" and "i div 2 \<noteq> x" and "even i" and "j < 1"
  shows "q_oracle (Matrix.mat (2^n) 1 (\<lambda>(i,j). A i) \<Otimes> (H * |one\<rangle>)) $$(i,j) = (-1)^(f(i div 2)+1)* A i"
proof-
   have "q_oracle (Matrix.mat (2^n) 1 (\<lambda>(i,j). A i) \<Otimes> (H * |one\<rangle>)) $$(i,j) = (Matrix.mat (2^(n+1)) 1 (\<lambda>(i,j). if (even i) then (-1)^f(i div 2) * A i 
                                      else (-1)^(f(i div 2)+1)* A i)) $$(i,j)" 
    using assms q_oracle_app by auto
  then have "(Matrix.mat (2^(n+1)) 1 (\<lambda>(i,j). if (even i) then (-(1::nat))^f(i div 2) * A i 
                                      else (-(1::nat))^(f(i div 2)+1)* A i)) $$(i,j) = (-(1::nat))^(f(i div 2)+1)* A i"
    using assms sledgehammer
qed

end (*context grover*)


abbreviation(in grover) start_state:: "complex Matrix.mat" where
"start_state \<equiv> (\<psi>\<^sub>1\<^sub>0 n)*(H * |one\<rangle>)"

  






























end