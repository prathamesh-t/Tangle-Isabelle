

header {* Basic Operations on Matrices *}

theory Matrix_Tensor
imports
  Utility Matrix_Arith
begin

primrec times:: "nat ⇒ nat vec ⇒ nat vec"
where
"times n [] = []"|
"times n (y#ys) = (n*y)#(times n ys)"

lemma preserving_length: "length (times n y) = (length y)"
apply(induct_tac y)
apply(auto)
done

primrec product:: "nat vec ⇒ nat vec ⇒ nat vec"
where
"product [] ys = []"|
"product (x#xs) ys = (times x ys)@(product xs ys)"

theorem product_length : 
 "(length(product x y)) = (length x)*(length y)"
apply(induct_tac x)
apply(auto)
apply(simp add: preserving_length)
done

theorem vec_length: assumes "vec m x" and "vec n y"
shows "vec (m*n) (product x y)"
apply(simp add:vec_def)
apply(simp add:product_length)
apply (metis assms(1) assms(2) vec_def)
done

primrec list_tensor::" nat vec ⇒ nat mat ⇒nat mat"
where
"list_tensor xs []  = []"|
"list_tensor xs (ys#yss) = (product xs ys)#(list_tensor xs yss)"


theorem list_tensor_length : 
 "(length(list_tensor xs ys)) = (length ys)"
apply(induct_tac ys)
apply(auto)
done

(*
(* vector of given length *)
definition vec :: "nat \<Rightarrow> 'x vec \<Rightarrow> bool"
 where "vec n x = (length x = n)"

(* matrix of given number of rows and columns *)
definition mat :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> bool" where
 "mat nr nc m = (length m = nc \<and> Ball (set m) (vec nr))"

Set.Ball_def: Ball ?A ?P = (∀x. x ∈ ?A ⟶ ?P x)*)

find_theorems Ball

primrec tensor::" nat mat ⇒ nat mat ⇒nat mat" (infixl "⊗" 65)
where
"[]⊗yss  = []"|
"(xs#xss)⊗(yss) = (list_tensor xs yss)@(tensor xss yss)"

theorem well_defined_tensor:assumes "mat m n A" and "mat k l B" shows
"mat (m*k) (n*l) (A⊗B)"
sledgehammer






