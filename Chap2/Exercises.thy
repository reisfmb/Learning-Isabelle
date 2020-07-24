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
end
