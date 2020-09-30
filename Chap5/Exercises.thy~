theory Exercises
imports Main
begin

text \<open> Exercise 5.1 \<close>

lemma 
  assumes T: "\<forall> x y. T x y \<or> T y x"
  and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall> x y. T x y \<longrightarrow> A x y"
  and AA: "A x y"
shows "T x y"
proof(cases)
  assume a1:"T y x"
  from this and TA have "A y x" by blast
  from this and AA and A have a2:"x = y" by blast
  from this and a1 have "T x y" by simp
  from this show "T x y" by auto
next
  assume a1:"\<not> T y x"
  from this and T show "T x y" by blast
qed


text \<open> A more direct solution...
proof(rule ccontr)
  assume a1:"\<not> T x y"
  from this and T have a2:"T y x" by blast
  from this and TA have "A y x" by blast
  from this and A and AA have "x = y" by blast
  from this and a1 and a2 show "False" by blast 
qed
\<close>

text \<open> End of exercise 5.1 \<close>

text \<open> Exercise 5.2 \<close>

text \<open> End of Exercise 5.2 \<close>
