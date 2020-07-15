theory MyList
imports Main
begin

datatype 'a list = Nil | Cons 'a " 'a list "

fun app :: " 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list " 
  where "app Nil x = x" | "app (Cons x xs) y = Cons x (app xs y) "

fun rev :: " 'a list \<Rightarrow> 'a list "
  where "rev Nil = Nil" | "rev (Cons x xs) = app (rev xs) (Cons x Nil) "

lemma app_Nil2[simp] : "app xs Nil = xs"
  apply(induction xs)
  apply(auto)
done

lemma app_assoc[simp] : "app (app xs ys) zs = app xs (app ys zs)"
  apply(induction xs)
  apply(auto)
done

lemma rev_app_rev[simp] : "rev (app xs ys) = app (rev ys) (rev xs)"
  apply(induction xs)
  apply(auto)
done


theorem rev_rev [simp] : "rev (rev xs) = xs"
  apply(induction xs)
  apply(auto)
done

end



