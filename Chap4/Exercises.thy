theory Exercises
imports Main
begin

text \<open> Exercise 4.1 \<close>

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}"|
"set (Node t1 n t2) = {n} \<union> (set t1) \<union> (set t2)"

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True"|
"ord (Node t1 n t2) = ((\<forall>x \<in> (set t1). x \<le> n) \<and> (\<forall>x \<in> (set t2). x \<le> n) \<and> (ord t1) \<and> (ord t2))"

fun ins :: "int tree \<Rightarrow> int \<Rightarrow> int tree" where
"ins (Tip) j = Node Tip j Tip"|
"ins (Node t1 n t2) j = (if j=n
                        then (Node t1 n t2) 
                        else if j > n
                             then (Node (Node t1 n t2) j Tip)
                             else (Node (ins t1 j) n t2)
                        )"
value "ord (ins (Node (Node Tip (5::int) Tip) 6 (Node Tip 3 Tip)) 4)"

lemma set_ins: "set (ins t n) = {n} \<union> (set t)"
  apply(induction t arbitrary:n)
  apply(auto)
done

lemma ord_ins: "ord t \<Longrightarrow> ord (ins t n)"
  apply(induction t arbitrary:n)
  apply(auto simp add: set_ins)
  done

text \<open> End of exercise 4.1 \<close>

text \<open> Exercise 4.2 \<close>

inductive palindrome :: "'a list \<Rightarrow> bool" where
"palindrome []"|
"palindrome [a]"|
"palindrome xs \<Longrightarrow> palindrome (a#xs@[a])"

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction rule: palindrome.induct)
  apply(simp_all)
done

text \<open> End of exercise 4.2 \<close>

text \<open> Exercise 4.3 \<close>

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl : "star r x x" |
step : "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl' : "star' r x x" |
step' : "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma [simp]: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
  apply(auto intro: refl' step')
  done

lemma  "star r x y \<Longrightarrow> star' r x y"
  apply(induction rule:star.induct)
  apply(auto intro: refl')
done

lemma [simp]: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
  apply(auto intro: refl step)
done

lemma "star' r x y \<Longrightarrow> star r x y"
  apply(induction rule:star'.induct)
  apply(auto intro: refl)
done

text \<open> End of exercise 4.3 \<close>

text \<open> Exercise 4.4 \<close>

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
i0:"iter r 0 x x"|
iN:"r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (n+1) x z"

lemma "star r x y \<Longrightarrow> \<exists>n. iter r n x y"
  apply(induction rule: star.induct)
  apply(auto intro: i0 iN)
done

text \<open> End of exercise 4.4 \<close>

text \<open> Exercise 4.6 \<close>

datatype aexp = N int | V string | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> (string \<Rightarrow> int) \<Rightarrow> int" where
"aval (N a) s = a" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s"

inductive rel_aval :: "aexp \<Rightarrow> (string \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> bool" where
ra_N: "rel_aval (N a) s a" |
ra_V: "rel_aval (V x) s (s x)" |
ra_Plus: "rel_aval p s int_p \<Longrightarrow> rel_aval q s int_v \<Longrightarrow> rel_aval (Plus p q) s (int_p + int_v)" 

theorem rel_aval_aval: "rel_aval a s v \<Longrightarrow> aval a s = v"
  apply (induction rule: rel_aval.induct)
  apply (auto)
done

theorem aval_rel_aval: "aval a s = v \<Longrightarrow> rel_aval a s v"
  apply (induction a arbitrary: v)
  apply (auto intro: ra_N ra_V ra_Plus)
done

theorem "rel_aval a s v \<longleftrightarrow> aval a s = v"
  apply (auto intro: aval_rel_aval rel_aval_aval)
done 

text \<open> End of exercise 4.6 \<close>


