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
proof(rule ccontr)
  assume a1:"\<not> T x y"
  from this and T have a2:"T y x" by blast
  from this and TA have "A y x" by blast
  from this and A and AA have "x = y" by blast
  from this and a1 and a2 show "False" by blast 
qed



text \<open> A more direct solution...
proof(cases)
  assume a1:"T y x"
  from this and TA have "A y x" by auto
  from this and AA and A have a2:"x = y" by auto
  from this and a1 show "T x y" by simp
next
  assume a1:"\<not> T y x"
  from this and T show "T x y" by auto
qed
\<close>

text \<open> End of exercise 5.1 \<close>

text \<open> Exercise 5.2 \<close>

lemma "(\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs) 
\<or> (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof(cases)
  assume "2 dvd (length xs)"
  from this obtain k where l_xs:"length xs = 2*k" by(auto simp add: dvd_def)
  from this obtain ys where tys:"ys = take k xs" by(auto)
  from this obtain zs where dzs:"zs = drop k xs" by(auto)
  from this have l1:"length ys = k" using l_xs and tys by(auto)
  from this have f1:"xs = ys @ zs" using tys and dzs by(metis append_eq_conv_conj)
  from this have f2:"length ys = length zs" using l_xs and l1 by(auto)
  then show ?thesis using f1 and f2 by(auto)
next
  assume " \<not> 2 dvd (length xs)"
  from this have "\<exists> k. (length xs) = 2*k + 1" by(arith)
  from this obtain k where l_xs:"(length xs) = 2*k + 1" by(auto)
  from this obtain ys where tys:"ys = take (Suc k) xs" by(auto)
  from this obtain zs where dzs:"zs = drop (Suc k) xs" by(auto)
  from this have "length ys = Suc k" using l_xs and tys by(auto) 
  from this have f1:"xs = ys @ zs" using tys and dzs by(metis append_eq_conv_conj)
  from this have f2:"length ys = length zs + 1" using l_xs and tys and dzs by(auto)
  then show ?thesis using f1 and f2 by(auto)
qed

text \<open> End of Exercise 5.2 \<close>

text \<open> Exercise 5.3 \<close>

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"

lemma assumes a: "ev (Suc(Suc n))" shows "ev n"
proof -
  show "ev n" using a
  proof cases
    case evSS thus "ev n"  by (simp add: ev.evSS)
  qed
qed

text \<open> End of Exercise 5.3 \<close>



text \<open> End of Exercise 5.4 \<close>

lemma "\<not> ev (Suc (Suc (Suc 0)))" (is "\<not> ?P")
proof
 assume "?P"
 from this have "ev (Suc 0)" by (cases)
 from this show  False by (cases) 
qed

text \<open> End of Exercise 5.4 \<close>
  