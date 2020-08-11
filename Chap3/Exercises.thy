theory Exercises
imports Main
begin

datatype aexp = N int | V string | Plus aexp aexp

type_synonym val = "int"
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

text \<open> Exercise 3.2 \<close>

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

text \<open> Exercise 3.3 \<close>

fun subst :: "string \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst str inp (V s) = (if str = s then inp else (V s))"|
"subst str inp (N n) = (N n)"|
"subst str inp (Plus a b) = Plus (subst str inp a) (subst str inp b)"

value"subst ''x'' (N 3) (Plus (V ''x'') (V ''y''))"

lemma substitution_lemma: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply(induction e)
  apply(auto)  
done

corollary substitution_consequence: "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply(induction e)
  apply(auto simp add: substitution_lemma)
  done

text \<open> End of exercise 3.3 \<close>

text \<open> Exercise 3.4

datatype AExp = N int | V string | Plus AExp AExp | Mult AExp AExp

fun Aval :: "AExp \<Rightarrow> state \<Rightarrow> int" where
"Aval (N n) s = n" |
"Aval (V x) s = s x"|
"Aval (Plus a1 a2) s = (Aval a1 s) + (Aval a2 s)"|
"Aval (Mult a1 a2) s = (Aval a1 s) * (Aval a2 s)"

fun myPlus2 :: "AExp \<Rightarrow> AExp \<Rightarrow> AExp" where
"myPlus2 (N n) (N m) = N(n+m)" |
"myPlus2 (N n) a = (if n = 0 then a else Plus (N n) a)" |
"myPlus2 a (N n) = (if n = 0 then a else Plus a (N n))" |
"myPlus2 a b = Plus a b"

fun myMult :: "AExp \<Rightarrow> AExp \<Rightarrow> AExp" where
"myMult (N n) (N m) = N(n*m)" |
"myMult (N n) a = (if n = 0 then (N 0) else Mult (N n) a)" |
"myMult a (N n) = (if n = 0 then (N 0) else Mult a (N n))" |
"myMult a b = Mult a b"

fun Asimp_const :: "AExp \<Rightarrow> AExp" where
"Asimp_const (N n) = (N n)" |
"Asimp_const (V s) = (V s)" |
"Asimp_const (Plus a1 a2) = 
(case (Asimp_const a1, Asimp_const a2) of
  ( N n1, N n2 ) \<Rightarrow> N (n1+n2) |
  ( b1, b2 ) \<Rightarrow> Plus b1 b2 
)"|
"Asimp_const (Mult a1 a2) = 
(case (Asimp_const a1, Asimp_const a2) of
  ( N n1, N n2 ) \<Rightarrow> N (n1*n2) |
  ( b1, b2 ) \<Rightarrow> Mult b1 b2 
)"

fun Asimp :: "AExp \<Rightarrow> AExp" where
"Asimp (N n) = (N n)" |
"Asimp (V s) = (V s)" |
"Asimp (Plus a1 a2) = myPlus2 (Asimp_const a1) (Asimp_const a2)"|
"Asimp (Mult a1 a2) = myMult (Asimp_const a1) (Asimp_const a2)"

value"Asimp (Mult (N 0) ((Plus (V ''x'') (Mult (N 3) (N 5)))))"

 End of exercise 3.4 \<close>

text \<open> Exercise 3.5 \<close>

datatype aexp2 = N2 int | V2 string | Plus2 aexp2 aexp2 | PostInc string | Div2 aexp2 aexp2

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state)" where
"aval2 (N2 n) st = ( n, st )"|
"aval2 (V2 s) st = ( st s, st )"|
"aval2 (Plus2 a b) st = ( fst (aval2 a st) + fst(aval2 b st), st )"|
"aval2 (PostInc s) st = (st s , st(s := 1 + st s))"|
"aval2 (Div2 a b) st = ( fst (aval2 a st) div fst (aval2 b st), st)"


text \<open> End of exercise 3.5 \<close>

text \<open> Exercise 3.6 \<close>

datatype lexp = Nl int | Vl string | Plusl lexp lexp | LET string lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
"lval (Nl n) s = n"|
"lval (Vl x) s = s x"|
"lval (Plusl e1 e2) s = (lval e1 s) + (lval e2 s)"|
"lval (LET x e1 e2) s = lval e2 (s (x := (lval e1 s)))"

text \<open> y=3 -> y+3 = 6 -> x+y = x+6. \<close>
value"lval (LET ''y'' ( Plusl (Vl ''y'') (Nl 3) ) ( Plusl (Vl ''x'') (Vl ''y'') )) ((%x.0)(''y'' := 3::int))"

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl n) = N n"|
"inline (Vl x) = V x"|
"inline (Plusl e1 e2) = Plus (inline e1) (inline e2)"|
"inline (LET x e1 e2) = subst x (inline e1) (inline e2)"

lemma "aval (inline e) s = lval e s"
  apply (induction e arbitrary:s)
  apply (auto simp add: substitution_lemma)    
done  

text \<open> End of exercise 3.6 \<close>
end
