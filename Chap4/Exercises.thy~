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

text \<open> End of exercise 4.4 \<close>


