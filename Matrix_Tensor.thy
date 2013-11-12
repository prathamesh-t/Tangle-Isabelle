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

theorem length_matrix: assumes "mat nr nc (y#ys)" and "length v = k"
and "(list_tensor v (y#ys) = x#xs)" 
 shows "(vec (nr*k) x)" 
proof-
have "list_tensor v (y#ys) = (product v y)#(list_tensor v ys)"  using list_tensor_def assms by auto
also have "(product v y) = x" using assms by auto
also have "length y = nr" using assms mat_def by (metis in_set_member member_rec(1) vec_def)
from this
 have "length (product v y) = nr*k" using assms product_length nat_mult_commute by auto
from this have "length x = nr*k" by (simp add: `product v y = x`)
from this have "vec (nr*k) x" using vec_def by auto
from this show ?thesis by auto
qed

lemma matrix_set_list: assumes "mat nr nc M" and "length v = k"
and " x ∈ set M" 
 shows "∃ys.∃zs.(ys@x#zs = M)" using assms set_def in_set_conv_decomp by metis

lemma matrix_short: assumes "M = x#xs" and "mat nr (nc+1) M" 
shows "mat nr nc xs"
proof-



lemma matrix_list_length:
assumes "mat nr nc M" and "length v = k"
and " (ys@x#zs = M)" 
 shows " (vec (nr*k) x"
proof-
let ?N = "x#zs"
let ?l = "length ys"
have "length M = length ys + (length (x#zs))" using assms(3) length_append by auto
from this have "length M = ?l + (length (x#zs))" by auto
from this have "length ?N = length M - ?l" by auto
from this have step1: "length ?N = nc - ?l" using assms mat_def by metis

have step2: "(y ∈ set M) ⟹ (vec nr y)" using mat_def assms by auto
have "(y ∈ set ?N) ⟹ (y ∈ set M)" using append_eq_conv_conj assms(3) in_mono set_drop_subset
 by auto
from this and step2 have "(y ∈ set ?N) ⟹ (vec nr y)" using Ball_def vec_def assms(1) by auto
from this have  "Ball (set ?N) (vec nr)" using Ball_def vec_def
append_assoc assms(1) assms(3) in_set_conv_decomp mat_def by metis
from this and step1 have step3:" mat nr (nc-?l) ?N" using mat_def by metis

let ?H = "(list_tensor v ?N)"
let ?y = "hd ?H"
from step3 and assms(2) have  "(vec (nr*k) ?y)" using length_matrix by auto


(*
theorem length_matrix: assumes "mat nr nc (y#ys)" and "length v = k"
and "(list_tensor v (y#ys) = x#xs)" 
 shows "(vec (nr*k) x)" *)

 



