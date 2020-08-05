theory Exercises
imports Main
begin

datatype aexp = N int | V string | Plus aexp aexp

type_synonym state = "string \<Rightarrow> int"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> int" where
"aval (N n) s = n" |
"aval (V x) s = s x"|
"aval (Plus a1 a2) s = (aval a1 s) + (aval a2 s)"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = (N n)" |
"asimp_const (V s) = (V s)" |
"asimp_const (Plus a1 a2) = 
(case (asimp_const a1, asimp_const a2) of
  ( N n1, N n2 ) \<Rightarrow> N (n1+n2) |
  ( b1, b2 ) \<Rightarrow> Plus b1 b2 
)"

value"asimp_const (Plus (N 1) (Plus (N 2) (N 3)))"

fun myPlus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"myPlus (N n) (N m) = N(n+m)" |
"myPlus (N n) a = (if n = 0 then a else Plus (N n) a)" |
"myPlus a (N n) = (if n = 0 then a else Plus a (N n))" |
"myPlus a b = Plus a b"

lemma aval_plus[simp] : "aval (myPlus a1 a2) s = aval a1 s + aval a2 s"
  apply(induction a1 rule:myPlus.induct)
  apply(auto)
done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = (N n)" |
"asimp (V s) = (V s)" |
"asimp (Plus a1 a2) = myPlus a1 a2"

lemma aval_asimp : "aval (asimp a) s = aval a s"
  apply(induction a rule: asimp.induct)
  apply(auto)
done

text \<open> Exercise 3.1 \<close>

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (Plus (N n) (N m)) = False" |
"optimal (N n) = True" |
"optimal (V s) = True" |
"optimal (Plus a1 a2) = conj (optimal a1) (optimal a2)"

lemma optimal_simplification : "optimal(asimp_const a) = True"
  apply(induction a)
  apply(auto split: aexp.split)
  done

text \<open> End of exercise 3.1 \<close>


text \<open> Exercise 3.2 - Tentativa 1 

fun prepare :: "aexp \<Rightarrow> aexp" where
"prepare (N n) = (N n)" |
"prepare (V s) = (V s)" |
"prepare (Plus a (N n)) = Plus (N n) (prepare a) " |
"prepare (Plus (V s) b) = Plus (prepare b ) (V s) " |
"prepare (Plus a b) = Plus (prepare a) (prepare b) "

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp (N n) = (N n)" |
"full_asimp (V s) = (V s)" |
"full_asimp (Plus (N n) (Plus (N m) b)) = Plus (N(n+m)) (full_asimp b)" |
"full_asimp (Plus a b) = Plus (full_asimp a) (full_asimp b)"

fun final :: "aexp \<Rightarrow> aexp" where
"final a = full_asimp (full_asimp (prepare a))"

value"final(Plus (N 1) (Plus (V x) (N 2)))"


End of exercise 3.2 \<close>

text \<open> Exercise 3.2 - Tentativa 2 \<close>

fun onlyN :: "aexp \<Rightarrow> int" where
"onlyN (N n) = n"|
"onlyN (V s) = 0"|
"onlyN (Plus a b) = onlyN a + onlyN b"

fun onlyV :: "aexp \<Rightarrow> aexp" where
"onlyV (N n) = (N 0)"|
"onlyV (V s) = (V s)"|
"onlyV (Plus a b) = asimp (Plus (onlyV a) (onlyV b))"

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp a = Plus (N (onlyN a)) (onlyV a)"

value"full_asimp(Plus (N 1) (Plus (V x) (N 2)))"

theorem full_asimp_correctness : "aval (full_asimp a) s = aval a s"
  apply(induction a)
  apply(auto)
done

text \<open> End of exercise 3.2 \<close>
end
