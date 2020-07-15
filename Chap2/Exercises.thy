theory Exercises
imports Main
begin

text \<open> Exercise 2.1 \<close>
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"
text \<open> End of exercise 2.1 \<close>


text \<open> Exercise 2.2 \<close>
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "add 0 n = n" | "add (Suc m) n = Suc (add m n)"

lemma add_m0[simp]: "add m 0 = m"
  apply(induction m)
  apply(auto)
done 

lemma add_suc[simp]: "add n (Suc m) = Suc (add n m)"
  apply(induction n)
  apply(auto)
 done

lemma add_assoc[simp]: "add (add a b) c = add a (add b c)"
  apply(induction a)
  apply(auto)
done

lemma add_comm[simp]: "add a b = add b a"
  apply(induction a)
  apply(auto)
done

fun double :: "nat \<Rightarrow> nat"
  where "double 0 = 0" | "double (Suc n) = add (Suc (Suc 0 ) ) (double n)"

lemma double_and_add : "double m = add m m"
  apply(induction m)
  apply(auto)
done
text \<open> Exercise 2.2 \<close>



text \<open> Exercise 2.3 \<close>
fun count :: " 'a \<Rightarrow> 'a list \<Rightarrow> nat "
  where 
    "count n Nil = 0" |
    "count n (Cons x xs) = add 0 (if n = x then add 1 (count n xs) else add 0 (count n xs))"

theorem upperBound_of_count : "count n xs \<le> length xs"
  apply(induction xs)
  apply(auto)
  done
text \<open> End of exercise 2.3 \<close>



text \<open> Exercise 2.4 \<close>
fun snoc :: " 'a list \<Rightarrow> 'a \<Rightarrow> 'a list "
  where 
    "snoc [] n =  [n]" |
    "snoc (x # xs) n = x # (snoc xs n) "

fun reverse :: " 'a list \<Rightarrow> 'a list "
  where
    "reverse [] = []" |
    "reverse (x # xs) = snoc (reverse xs) x"

lemma [simp]:"reverse (snoc xs a) = a # reverse xs"
  apply (induction xs)
  apply auto
done  

theorem rev_rev : "reverse (reverse xs) = xs"
  apply(induction xs)
  apply(auto)
  done
text \<open> End of exercise 2.4 \<close>



text \<open> Exercise 2.5 \<close>
fun sum :: " nat \<Rightarrow> nat "
  where "sum 0 = 0" | "sum (Suc n) = (Suc n) + (sum n)"

theorem known_fact : "sum n = n * (n+1) div 2"
  apply(induction n)
  apply(auto)
done
text \<open> End of exercise 2.5 \<close>



end
