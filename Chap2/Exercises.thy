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


text \<open> Exercise 2.6 \<close>
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: " 'a tree \<Rightarrow> 'a list "
  where "contents Tip = []" |
        "contents (Node t1 x t2) = x # (contents t1 @ contents t2)"

fun treesum :: " nat tree \<Rightarrow> nat  "
  where "treesum Tip = 0" |
        "treesum (Node t1 x t2) = sum_list (contents (Node t1 x t2))"

lemma treesum_equals_sum_list : "treesum myTree = sum_list (contents myTree)"
   apply(induction)
   apply(auto)
done
text \<open> End of exercise 2.6 \<close>

text \<open> Exercise 2.7 \<close>

datatype 'a tree2 = Tip 'a | Node "'a tree2" 'a "'a tree2"

fun mirror :: " 'a tree2 \<Rightarrow> 'a tree2"
  where "mirror (Tip x) = Tip x"|
        "mirror (Node t1 x t2) = Node (mirror t2) x (mirror t1)"

fun pre_order :: " 'a tree2 \<Rightarrow> 'a list "
  where "pre_order (Tip x) = x # []" |
        "pre_order (Node t1 x t2) = x # ( (pre_order t1) @ (pre_order t2) )"

fun post_order :: " 'a tree2 \<Rightarrow> 'a list "
  where "post_order (Tip x) = x # []" |
        "post_order (Node t1 x t2) = ( (post_order t1) @ (post_order t2) ) @ (x # [])"

text \<open>
      1
     /\
    2  3
   /\  /\
  4 5  6 7
pre: 1-2-4-5-3-6-7
post: 4-5-2-6-7-3-1
\<close>

value "rev(post_order (Node (Node (Tip 4) 2 (Tip 5)) 1 (Node (Tip 6) 3 (Tip (7::int)))))"
value "pre_order (mirror ((Node (Node (Tip 4) 2 (Tip 5)) 1 (Node (Tip 6) 3 (Tip (7::int))))))"

lemma relation_between_pre_and_post_order : "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
  apply(auto)
done

text \<open> End of exercise 2.7 \<close>

text \<open> End of exercise 2.8 \<close>

fun interspere :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "interspere n [] = [n]" |
        "interspere n [x] = [x]" |
        "interspere n (x # xs) = [x,n] @ (interspere n xs)"

lemma map_interspere_propertie : "map f (interspere n l) = interspere (f n) (map f l)"
  apply(induction l rule: interspere.induct)
  apply(auto)
done

text \<open> End of exercise 2.8 \<close>

text \<open> Exercise 2.9 \<close>

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "itadd 0 n = n"|
        "itadd (Suc m) n = itadd m (Suc n)"

lemma itadd_equals_add : "itadd m n = add m n"
  apply(induction m arbitrary: n)
  apply(auto)
done


text \<open> End of exercise 2.9 \<close>

text \<open> Exercise 2.10 \<close>


datatype tree0 = Tip | Node "tree0" "tree0"

fun nodes :: "tree0 \<Rightarrow> nat"
  where "nodes Tip = 1" |
        "nodes (Node t1 t2) = 1 + nodes t1 + nodes t2"

text \<open>
    N
   / \
  T   N
     / \
    T   T
\<close>
value "nodes (Node (Node Tip Tip) Tip)" 

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t )"

value "nodes (explode 0 (Node (Node Tip Tip) Tip))"
text \<open>
  So... My Tree0 has 5 elements. 
  Explode 0 -> 5. Right
  Explode 1 -> 5 + 5 + 1, since it duplicates the previous and add a node.
  Explode 2 -> 11 + 11 + 1, same reasoning as before...
  Therefore let's define n := nodes myTree and f(x) = 2x + 1
    0 -> n              :5
    1 -> f(n)           :11 2*5 + 1
    2 -> f(f(n))        :23 2(2*5+1) + 1
    3 -> f(f(f(n)))     :47 2*(2*(2*5 + 1) + 1
\<close>

fun size_explode :: "nat \<Rightarrow> tree0 \<Rightarrow> nat" where
"size_explode n t = 2^n * (nodes t) + 2^n - 1"

value "nodes (explode 0 (Node (Node Tip Tip) Tip))"
value "nodes (explode 1 (Node (Node Tip Tip) Tip))"
value "nodes (explode 2 (Node (Node Tip Tip) Tip))"

value "size_explode 0 (Node (Node Tip Tip) Tip)"
value "size_explode 1 (Node (Node Tip Tip) Tip)"
value "size_explode 2 (Node (Node Tip Tip) Tip)"

lemma expression : "nodes (explode n t) = size_explode n t"
  apply(induction n arbitrary:t)
  apply(auto simp add: algebra_simps)
done


text \<open> End of exercise 2.10 \<close>

text \<open> Exercise 2.11 \<close>

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const a) x = a" |
"eval (Add a b) x = (eval a x) + (eval b x)" |
"eval (Mult a b) x = (eval a x) * (eval b x)"


value"Add (Var) (Add (Var) (Const 3))"
text \<open> This seems to be x + x + 3 \<close>
value"eval (Add (Var) (Add (Var) (Const 3))) 10"
text \<open> 10 + 10 + 3 = 23, which is exactly the output. Wow. think I got it. \<close>

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] x = 0" |
"evalp (n # xs) x = n + evalp xs x * x"

value "evalp [4::int,2] 0"
value "evalp [4::int,2] 1"
value "evalp [4::int,2] 2"

text \<open>
The above definition is based on the fact that we can put the Var (namely x) in evidence.
\<close>

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0,1]"|
"coeffs (Const n) = [n]"|
"coeffs (Add a b) = (coeffs a) @ (coeffs b)"|
"coeffs (Mult a b) = coeffs a"

value "evalp (coeffs (Add (Const (4)) (Mult (Const (2)) Var))) 0"
value "evalp (coeffs (Add (Const (4)) (Mult (Const (2)) Var))) 1"
value "evalp (coeffs (Add (Const (4)) (Mult (Const (2)) Var))) 2"

value "eval (Add (Const (4)) (Mult (Const (2)) Var)) 0"
value "eval (Add (Const (4)) (Mult (Const (2)) Var)) 1"
value "eval (Add (Const (4)) (Mult (Const (2)) Var)) 2"

text \<open>
It seems to work fine when the expression is indeed a linear polynomial in it's most compact form.
But it's not working when it's not... For example x + x is returning [1,1] 
and the correct output is [2]
 \<close>


theorem voila : "evalp (coeffs e) x = eval e x"
  apply(induction e arbitrary:x)
  apply(auto)


text \<open> End of exercise 2.11 \<close>
end
