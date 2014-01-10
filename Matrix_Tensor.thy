header {* Basic Operations on Matrices *}

theory Matrix_Tensor
imports
  Utility Matrix_Arith
begin

(*Matrix Tensor begins*)

locale mult = 
 fixes f::" 'a ⇒ 'a ⇒ 'a " (infixl "*" 60)
 assumes comm:" f a  b = f b  a "
 assumes assoc:" (f (f a b) c) = (f a (f b c))"
context mult
begin   
 
primrec times:: "'a ⇒ 'a vec ⇒ 'a vec"
where
"times n [] = []"|
"times n (y#ys) = (f n y)#(times n ys)"

lemma preserving_length: "length (times n y) = (length y)"
apply(induct_tac y)
apply(auto)
done

primrec product:: "'a vec ⇒ 'a vec ⇒ 'a vec"
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

primrec list_tensor::"'a vec ⇒ 'a mat ⇒'a mat"
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

primrec reduct :: "'a mat ⇒ 'a mat"
where
"reduct [] = []"
|"reduct (x#xs) = xs"

lemma length_reduct: assumes "m ≠ []"
shows "length (reduct m) +1  = (length m)"
apply(auto)
by (metis One_nat_def Suc_eq_plus1 assms list.size(4) neq_Nil_conv reduct.simps(2))

lemma mat_empty_column_length: assumes "mat nr nc M" and "M = []"
shows "nc = 0" 
proof-
have "(length M = nc)" using mat_def assms by metis
from this have "nc = 0" using assms by auto
from this show ?thesis by simp
qed

lemma vec_uniqueness: assumes "vec m v" and "vec n v" shows 
"m = n"
using vec_def assms(1) assms(2)  by metis

lemma mat_uniqueness: assumes "mat nr1 nc M" and "mat nr2 nc M" and "z = hd M" and "M ≠ []"
shows "(∀x∈(set M).(nr1 = nr2))" 
proof-
 have A:"z ∈ set M" using assms(1) assms(3) assms(4) set_def mat_def by (metis hd_in_set)
 have "Ball (set M) (vec nr1)" using mat_def assms(1) by auto 
  from this have step1: "((x ∈ (set M)) ⟶ (vec nr1 x))" using Ball_def assms by auto
  have "Ball (set M) (vec nr2)" using mat_def assms(2) by auto
  from this have step2: "((x ∈ (set M)) ⟶ (vec nr2 x))" using Ball_def assms by auto
  from step1 and step2 have step3:"∀x.((x ∈ (set M))⟶ ((vec nr1 x)∧ (vec nr2 x)))"
  by (metis `Ball (set M) (vec nr1)` `Ball (set M) (vec nr2)`)
  have "((vec nr1 x)∧ (vec nr2 x)) ⟶ (nr1 = nr2)" using vec_uniqueness by auto
  from this and step3  have "(∀x.((x ∈ (set M)) ⟶((nr1 = nr2))))" by 
 (metis vec_uniqueness) 
 from this have "(∀x∈(set M).(nr1 = nr2))" by auto 
 from this show ?thesis by auto
qed

 
lemma mat_empty_row_length: assumes "mat nr nc M" and "M = []"
shows "mat 0 nc M" 
proof-
have "set M = {}" using mat_def assms  empty_set  by auto
from this have "Ball (set M) (vec 0)" using Ball_def by auto
from this have "mat 0 nc M" using mat_def assms(1) assms(2) gen_length_code(1) length_code
 by (metis (full_types) )
from this show ?thesis by auto
qed

abbreviation null_matrix::"'a list list"
where
"null_matrix ≡ [Nil] "

lemma zero_matrix:" mat 0 0 []" using mat_def in_set_insert insert_Nil list.size(3) not_Cons_self2
 by (metis (full_types))

definition row_length:: "'a mat ⇒ nat"
where
"row_length xs ≡ if (xs = []) then 0 else (length (hd xs))"

lemma row_length_Nil: "row_length [] =0" using row_length_def by (metis )

lemma row_length_vect_mat: " row_length (list_tensor v m) = length v*(row_length m)"
proof(induct m)
 case Nil
  have "row_length [] = 0" using row_length_Nil by simp
  moreover have "list_tensor v [] = []" using list_tensor.simps(1) by auto 
  ultimately have " row_length (list_tensor v []) = length v*(row_length [])" using mult_0_right by (metis )
  from this show ?case by metis
 next  
  fix a m
  assume A:"row_length (list_tensor v m) = length v * row_length m"
  let ?case = "row_length (list_tensor v (a#m)) = (length v)*(row_length (a#m))" 
  have A:"row_length (a # m) = length a" using row_length_def by (metis hd.simps list.distinct(1))
  have "(list_tensor v  (a#m)) = (product v a)#(list_tensor v m)" using list_tensor_def list_tensor.simps(2)
  by auto
  from this have "row_length (list_tensor v (a#m)) = length (product v a)" using row_length_def  hd.simps
  by (metis list.distinct(1) list_tensor.simps(2))
  from this and product_length have "row_length (list_tensor v (a#m)) = (length v)*(length a)" by auto
  from this and A  have "row_length (list_tensor v (a#m)) = (length v)*(row_length (a#m))"
  by auto
  from this show ?case by auto
qed

primrec tensor::" 'a mat ⇒ 'a mat ⇒'a mat" (infixl "⊗" 63)
where
"tensor [] xs = []"|
"tensor (x#xs) ys = (list_tensor x ys)@(tensor xs ys)"

lemma tensor_null: "xs ⊗[] = []" 
apply(induct_tac xs)
apply(auto)
done

lemma hd_append:  assumes "xs ≠ []" shows "hd (xs@ys) = hd xs" using hd_def hd_append2 append_def 
apply(induct_tac ys)
apply(auto)
by (metis assms hd_append2)

lemma row_length_mat: "(row_length (m1⊗m2)) = (row_length m1)*(row_length m2)"
proof(induct m1)
 case Nil
   have "row_length ([]⊗m2) = 0" using tensor.simps(1) row_length_def by metis
   from this have "row_length ([]⊗m2) = (row_length [])*(row_length m2)"  
        by (metis comm_semiring_1_class.normalizing_semiring_rules(9) row_length_Nil)
   then show ?case by metis
 next
 fix a m1 
 assume "row_length (m1 ⊗ m2) = row_length m1 * row_length m2"
 let ?case = "row_length ((a # m1) ⊗ m2) = row_length (a # m1) * row_length m2"
 have B: "row_length (a#m1) = length a" using row_length_def by (metis hd.simps list.distinct(1))
 have "row_length ((a # m1) ⊗ m2) = row_length (a # m1) * row_length m2"
   proof(induct m2)
   case Nil
    show ?case using tensor_null row_length_def by (metis mult_0_right)
   next
    fix aa m2
    assume "row_length (a # m1 ⊗ m2) = row_length (a # m1) * row_length m2"
    let ?case= " row_length (a # m1 ⊗ aa # m2) = row_length (a # m1) * row_length (aa # m2)"
    have "aa#m2 ≠ []" by auto
    from this have "(list_tensor a (aa#m2)) ≠ []" using list_tensor_def by auto
    from this have "hd ((list_tensor a (aa#m2))@(m1⊗m2))= hd (list_tensor a (aa#m2)) " by auto

    from this have "hd ((a#m1)⊗(aa#m2)) = hd (list_tensor a (aa#m2))" using tensor.simps(2) by auto
    from this have s1: "row_length ((a#m1)⊗(aa#m2)) = row_length (list_tensor a (aa#m2))" 
           using row_length_def by (metis Nil_is_append_conv `list_tensor a (aa # m2) ≠ []` tensor.simps(2))
    have "row_length (list_tensor a (aa#m2)) = (length a)*row_length(aa#m2)" using row_length_vect_mat
    by metis   
    from this and s1  
     have "row_length (list_tensor a (aa#m2)) = (length a)*row_length(aa#m2)"
         by auto
   from this and B have "row_length (list_tensor a (aa#m2)) = (row_length (a#m1))*row_length(aa#m2)"    
        by auto
   from this  and s1 show ?case  by (auto)
   qed
  from this show ?case by auto
 qed

lemma hd_set:assumes "x ∈ set (a#M)" shows "(x = a) ∨ (x∈(set M))"
             using set_def assms set_ConsD  by auto


theorem matrix_row_length: assumes "mat nr nc M" 
shows "mat (row_length M) (length M) M"
proof(cases M)
case Nil
 have "row_length M= 0 " using row_length_def by (metis Nil)
 moreover have "length M = 0" by (metis Nil list.size(3))
 moreover  have "mat 0 0 M" using zero_matrix Nil by auto 
 ultimately show ?thesis  using mat_empty_row_length row_length_def mat_def  by metis
next
case (Cons a N) 
 have 1: "mat nr nc (a#N)" using assms Cons by auto
 from this have "(x ∈ set (a #N)) ⟶ (x = a) ∨ (x ∈ (set N))" using hd_set by auto
 from this and 1 have 2:"vec nr a" using  mat_def by (metis Ball_set_list_all list_all_simps(1))
 have "row_length (a#N) = length a" using row_length_def Cons hd.simps list.distinct(1) by metis
 from this have " vec (row_length (a#N)) a" using vec_def by auto
 from this and 2 have 3:"(row_length M)  = nr" using vec_uniqueness Cons by auto
 have  " nc = (length M)" using 1 and mat_def and assms by metis
 from this and 3 have "mat (row_length M) (length M) M" using assms by auto 
 from this show ?thesis by auto
qed

lemma reduct_matrix: assumes "mat (row_length (a#M)) (length (a#M)) (a#M)"
shows "mat (row_length M) (length M) M"
proof(cases M)
 case Nil
   show ?thesis using row_length_def zero_matrix Nil by (metis list.size(3))
 next   
 case (Cons b N)
  have 1: "b ∈ (set M)" using set_def  Cons ListMem_iff elem  by auto
  have "mat (row_length (a#M)) (length (a#M)) (a#M)" using assms by auto
  from this have "(x ∈ (set (a#M))) ⟶ ((x = a) ∨ (x ∈ set M))" by auto
  from this have " (x ∈ (set (a#M))) ⟶ (vec (row_length (a#M)) x)" using mat_def Ball_def assms 
      by metis
  from this have "(x ∈ (set (a#M))) ⟶ (vec (length a) x)" using row_length_def 
      by (metis hd.simps list.distinct(1))
  from this have 2:"x ∈ (set M) ⟶ (vec (length a) x)" by auto
  from this and 1 have 3:"(vec (length a) b)" by (metis assms in_set_member mat_def member_rec(1) vec_def) 
  have 5: "(vec (length b) b)" using vec_def by auto
  from this and 3 have "(length a) = (length b)" using vec_uniqueness by auto
  from this and 2 have 4: "x ∈ (set M) ⟶ (vec (length b) x)" by auto
  have 6:"row_length M = (length b)" using row_length_def hd.simps by (metis Cons list.distinct(1))
  from this and 4 have "x ∈ (set M) ⟶ (vec (row_length M) x)" by auto
  from this have "(∀x. (x ∈ (set M) ⟶ (vec (row_length M) x)))" by (metis Cons 5 6
   assms in_set_member mat_def member_rec(1) vec_uniqueness)
  from this have "Ball (set M) (vec (row_length M))" using Ball_def by auto
  from this have "(mat (row_length M) (length M) M)" using mat_def by auto
  from this show ?thesis by auto
  qed 

theorem well_defined_list_tensor:
"(mat (row_length M) (length M) M) ⟹(mat ((row_length M)*(length v)) (length M) (list_tensor v M))"
proof(induct M) 
 case Nil
  have "(list_tensor v []) = []" using list_tensor.simps(1) Nil  by simp
  moreover have "(row_length [] = 0)"  using row_length_def Nil by metis
  moreover have "(length []) = 0" using Nil by simp
  ultimately have "mat ((row_length [])*(length v)) (length []) (list_tensor v [])" using zero_matrix by (metis mult_zero_left)
  from this show ?case by simp
 next
 fix a M
 assume hyp :"(mat (row_length M) (length M) M ⟹ mat (row_length M * length v) (length M) (list_tensor v M))"
               " mat (row_length (a#M)) (length (a#M)) (a#M)"                      
  let ?case = "mat (row_length (a#M) * length v) (length (a#M)) (list_tensor v (a#M))"
  have step1: "mat (row_length M) (length M) M" using hyp(2) reduct_matrix by auto
  from this have step2:"mat (row_length M * length v) (length M) (list_tensor v M)" using hyp(1) by auto 
  have "mat (row_length (a#M) * length v) (length (a#M)) (list_tensor v (a#M))" 
    proof (cases M)
         case Nil 
     have 1:"(list_tensor v (a#M)) = [product v a]" using list_tensor.simps Nil by auto
     have   "(x ∈ (set [product v a])) ⟶  x = (product v a)" using set_def by auto
     from this have 2:" (x ∈ (set [product v a])) ⟶ (vec (length (product v a)) x)" using vec_def by metis 
     have "length (product v a) = (length v)*(length a)" using product_length by auto 
     from this have "length (product v a) = (length v)*(row_length (a#M))" using row_length_def hd.simps
     list.distinct(1) by metis
     from this and 2 have "(x ∈ (set [product v a])) ⟶ (vec ((length v)*(row_length (a#M))) x)" by auto
     from this and 1 have 3:"(x ∈ set (list_tensor v (a#M))) ⟶ vec ((length v)*(row_length (a#M))) x" 
     by auto
     have 4: "length (list_tensor v (a#M)) = (length (a#M))" using list_tensor_length by auto
     from this have "mat (row_length (a#M) * length v) (length (list_tensor v (a#M))) (list_tensor v (a#M))"
     using mat_def Ball_def by (metis (hide_lams, no_types) 
    "1" `length (product v a) = length v * row_length (a # M)` `length (product v a) = length v * length a` 
    hd_set in_set_insert insert_Nil length_code nat_mult_commute not_Cons_self2 product_length vec_def)
     from this show ?thesis using 4 by auto
     next 
     case (Cons b L)
      have 1:"x ∈ (set (a#M)) ⟶ ((x=a) ∨ (x ∈ (set M)))" using hd_set by auto
      have "mat (row_length (a#M)) (length (a#M)) (a#M)" using hyp by auto
      from this have "x∈ (set (a#M)) ⟶ (vec (row_length (a#M)) x)" using mat_def Ball_def by metis
      from this have "x∈ (set (a#M))⟶ (vec (length a) x)" using row_length_def hd.simps list.distinct(1)
      by (metis ) 
      from this and 1 have "x∈ (set M)⟶ (vec (length a) x)" by auto
      moreover have " b ∈ (set M)" using Cons by auto
      ultimately have "vec (length a) b" by (metis hyp(2) in_set_member mat_def member_rec(1) vec_def) 
      from this have "(length b) = (length a)" using vec_def vec_uniqueness by auto
      from this have 2:"row_length M = (length a)" using row_length_def hd.simps by (metis Cons list.distinct(1)) 
      
      have "  mat (row_length M * length v) (length M) (list_tensor v M)" using step2 by auto 
      from this have " Ball (set (list_tensor v M)) (vec ((row_length M)*(length v)))" using mat_def by auto
      from this have "(x ∈ set (list_tensor v M)) ⟶ (vec ((row_length M)*(length v)) x)" using mat_def Ball_def
      by auto
      from this have 3:" (x ∈ set (list_tensor v M)) ⟶ (vec ((length a)*(length v)) x)" using 2 by auto
  
      have "length (product v a) = (length a)*(length v)" by (metis nat_mult_commute product_length)  
      from this  have 4:" vec ((length a)*(length v)) (product v a)" using product_length vec_def 
             by (metis (full_types))

      have 5:"(length a) = (row_length (a#M))" using row_length_def hd.simps  list.distinct(1)  by (metis) 
 
      have "list_tensor v (a#M) = (product v a)#(list_tensor v M)" using list_tensor.simps(2) by auto
      from this have "(x ∈ set (list_tensor v (a#M)))⟶ ((x = (product v a)) ∨ (x ∈ (set (list_tensor v M)))) "
      using hd.simps hd_set by auto
      from this 3 4 have "(x ∈ set (list_tensor v (a#M)))⟶  vec ((length a)*(length v)) x" by auto
      from this 5 have "(x ∈ set (list_tensor v (a#M)))⟶  vec ((row_length (a#M))*(length v)) x" by auto
      from this have "∀x.((x ∈ set (list_tensor v (a#M)))⟶  vec ((row_length (a#M))*(length v)) x)"
       by (metis "2" "4" "5" `Ball (set (list_tensor v M)) (vec (row_length M * length v))` 
      hd_set list_tensor.simps(2))
      from this have 6: "Ball (set (list_tensor v (a#M))) (vec ((row_length (a#M))*(length v)))" using Ball_def by 
      auto
      have 7:"length (list_tensor v (a#M)) = length (a#M)" using list_tensor_length by auto
    
      from 6 and 7 have "mat ((row_length (a#M))*(length v)) (length (a#M)) (list_tensor v (a#M))"
        using mat_def
        by (metis (hide_lams, no_types) "5" `length (product v a) = length a * length v` length_code)
     from this show ?thesis by auto
     qed
    from hyp this show ?case by auto  
qed


lemma length_tensor:" (length (M1⊗M2)) = (length M1)*(length M2)"
proof(induct M1)
 case Nil
  show ?case by auto
 next
 case (Cons a M1)
 have "((a # M1) ⊗ M2) = (list_tensor a M2)@(M1 ⊗ M2)" using tensor.simps(2) by auto
 from this have 1:"length ((a # M1) ⊗ M2) = length ((list_tensor a M2)@(M1 ⊗ M2))" by auto
 have 2:"length ((list_tensor a M2)@(M1 ⊗ M2)) = length (list_tensor a M2)+ length (M1 ⊗ M2)" using append_def
 by auto
 have 3:"(length (list_tensor a M2)) = length M2" using list_tensor_length by (auto)
 have 4:"length (M1 ⊗ M2) = (length M1)*(length M2)" using  Cons.hyps by auto
 from this 2 3 have  "length ((list_tensor a M2)@(M1 ⊗ M2)) =  (length M2) + (length M1)*(length M2)"
 by auto
 from this have 5:"length ((list_tensor a M2)@(M1 ⊗ M2)) =  (1 + (length M1))*(length M2)" by auto
 have "length (a#M1) = 1+(length M1)" by auto
 from this have "((length (a # M1)) * (length M2)) = (1 + (length M1))*(length M2)" by auto 
 from 1 5 this have "length ((a # M1) ⊗ M2) = ((length (a # M1)) * (length M2))" by auto
 from this show ?case by auto
qed


lemma append_reduct_matrix: 
"(mat (row_length (M1@M2)) (length (M1@M2)) (M1@M2))
⟹(mat (row_length M2) (length M2) M2)"
proof(induct M1)
case Nil
 show ?thesis using Nil append.simps(1) by auto
next
case (Cons a M1)
 have "mat (row_length (M1 @ M2)) (length (M1 @ M2)) (M1 @ M2)" using reduct_matrix Cons.prems 
   append_Cons by metis
 from this have "(mat (row_length M2) (length M2) M2)" using Cons.hyps by auto
 from this show?thesis by simp
qed
(*proves that tensor product takes well defined matrices to well defined matrices*)
theorem well_defined_tensor:
"(mat (row_length M1) (length M1) M1) ∧ (mat (row_length M2) (length M2) M2)
⟹(mat ((row_length M1)*(row_length M2)) ((length M1)*(length M2)) (M1⊗M2))"
proof(induct M1)
 case Nil
  have "(row_length []) * (row_length M2) = 0" using row_length_def  mult_zero_left  by (metis)
  moreover have "(length []) * (length M2) = 0" using  mult_zero_left list.size(3) by auto 
  moreover have "[] ⊗ M2 = []" using tensor.simps(1) by auto
  ultimately have "mat (row_length [] * row_length M2) (length [] * length M2) ([] ⊗ M2)"
     using zero_matrix by metis
  from this show ?case by simp
 next
 case (Cons a M1)
 have step1: "mat (row_length (a # M1)) (length (a # M1)) (a # M1)" using Cons.prems by auto
 then have "mat (row_length (M1)) (length (M1)) (M1)" using reduct_matrix by auto
 moreover have "mat (row_length (M2)) (length (M2)) (M2)" using Cons.prems by auto
 ultimately have step2:"mat (row_length M1 * row_length M2) (length M1 * length M2) (M1 ⊗ M2)"
 using Cons.hyps by auto
 have 0:"row_length (a#M1) = length a" using row_length_def hd.simps list.distinct(1)  
      by metis
 have "mat (row_length (a # M1) * row_length M2) (length (a # M1) * length M2) (a # M1 ⊗ M2)"
  proof(cases M1)
   case Nil 
    have "(mat ((row_length M2)*(length a)) (length M2) (list_tensor a M2))" using Cons.prems 
    well_defined_list_tensor by auto
    moreover have "(length (a # M1)) * (length M2) = length M2" using Nil by auto
    moreover have "(a#M1)⊗M2 = (list_tensor a M2)" using Nil tensor.simps append.simps(1) by auto
    ultimately have "(mat ((row_length M2)*(row_length (a#M1))) ((length (a # M1)) * (length M2))
               ((a#M1)⊗M2))" using 0
             by auto
    from this show ?thesis using nat_mult_commute by metis
  next
  case (Cons b N1)
     have 1:"x ∈ (set (a#M1)) ⟶ ((x=a) ∨ (x ∈ (set M1)))" using hd_set by auto
     have "mat (row_length (a#M1)) (length (a#M1)) (a#M1)" using Cons.prems by auto
     from this have "x∈ (set (a#M1)) ⟶ (vec (row_length (a#M1)) x)" using mat_def Ball_def by metis
      from this have "x∈ (set (a#M1))⟶ (vec (length a) x)" using row_length_def hd.simps list.distinct(1)
      by (metis ) 
      from this and 1 have "x∈ (set M1)⟶ (vec (length a) x)" by auto
      moreover have " b ∈ (set M1)" using Cons by auto
      ultimately have "vec (length a) b" by (metis Cons.prems in_set_member mat_def member_rec(1) vec_def)
      from this have "(length b) = (length a)" using vec_def vec_uniqueness by auto
      from this have 2:"row_length M1 = (length a)" using row_length_def hd.simps by (metis Cons list.distinct(1)) 
      from this have "mat ((length a) * row_length M2) (length M1 * length M2) (M1 ⊗ M2)" using step2
      by auto
      from this have "Ball (set (M1⊗M2)) (vec ((length a)*(row_length M2))) " using mat_def by auto     
      from this have 3:"∀x. x ∈ (set (M1 ⊗ M2)) ⟶ (vec ((length a)*(row_length M2)) x)" using Ball_def by auto
    
    
      have "(mat ((row_length M2)*(length a)) (length M2) (list_tensor a M2))" using well_defined_list_tensor
       Cons.prems by auto
      from this have "Ball (set (list_tensor a M2)) (vec ((row_length M2)*(length a)))" using mat_def
         by auto
      from this have 4:"∀x. x ∈ (set (list_tensor a M2)) ⟶ (vec ((length a)*(row_length M2)) x)"
           using  nat_mult_commute by metis
      from this and 3 have 5: "∀x. (x ∈ (set (list_tensor a M2)))∨(x ∈ (set (M1 ⊗ M2))) 
                         ⟶ (vec ((length a)*(row_length M2)) x)"     by auto  

       have 6:"(a # M1 ⊗ M2) = (list_tensor a M2)@(M1 ⊗M2)" using tensor.simps(2) by auto 
       from this have "x ∈ (set (a # M1 ⊗ M2)) 
        ⟶ (x ∈ (set (list_tensor a M2)))∨(x ∈ (set (M1 ⊗ M2)))"
           using set_def append_def by auto
       from this and 5 have "∀x. (x ∈  (set (a # M1 ⊗ M2)))
                         ⟶ (vec ((length a)*(row_length M2)) x)" by auto
       from this have 7:"Ball (set (a # M1 ⊗ M2)) (vec ((row_length (a#M1))*(row_length M2)))" 
       using Ball_def 0 by auto
   
       have "(length ((a#M1)⊗M2)) = (length (a#M1))*(length M2)" using length_tensor by metis
       from this and 7 
           have "mat (row_length (a # M1) * row_length M2) (length (a # M1) * length M2) (a # M1 ⊗ M2)"
             using mat_def by (metis "0" `∀x. x ∈ set (a # M1 ⊗ M2) ⟶ vec (length a * row_length M2) x` length_tensor)
       from this show ?thesis by auto
       qed
     from this show ?case by auto
   qed


theorem effective_well_defined_tensor:
assumes "(mat (row_length M1) (length M1) M1)" and "(mat (row_length M2) (length M2) M2)"
shows "(mat ((row_length M1)*(row_length M2)) ((length M1)*(length M2)) (M1⊗M2))"
using well_defined_tensor assms by auto

definition natmod::"nat ⇒ nat ⇒ nat" (infixl "nmod" 50)
where
 "natmod x y = nat ((int x) mod (int y))"

theorem times_elements:
"∀i.((i<(length v)) ⟶ (times a v)!i = f a (v!i))"
apply(rule allI)
proof(induct v)
case Nil
have "(length [] = 0)" by auto
from this have "i <(length []) ⟹ False" by auto
moreover have "(times a []) = []" using times.simps(1) by auto 
ultimately have "(i<(length [])) ⟶ (times a [])!i = f a ([]!i)" by auto
from this have "∀i. ((i<(length [])) ⟶ (times a [])!i = f a ([]!i))" by auto
from this show ?case  by auto
next
case (Cons x xs)
have "∀i.((x#xs)!(i+1) = (xs)!i)" by auto

have 0:"((i<length (x#xs))⟶ ((i<(length xs)) ∨ (i = (length xs))))" by auto
have 1:" ((i<length xs) ⟶((times a xs)!i = f a (xs!i)))" by (metis Cons.hyps)
have "∀i.((x#xs)!(i+1) = (xs)!i)" by auto
have "((i <length (x#xs)) ⟶(times a (x#xs))!i = f a ((x#xs)!i))"  
 proof(cases i)
   case 0
    have "((times a (x#xs))!i) = f a x" using 0 times.simps(2) by auto
    from this have "(times a (x#xs))!i = f a ((x#xs)!i)" using 0 by auto
    from this show ?thesis by auto
    next
  case (Suc j)
    have 1:" (times a (x#xs))!i = ((f a x)#(times a xs))!i" using times.simps(2) by auto 
    have 2:"((f a x)#(times a xs))!i = (times a xs)!j" using Suc by auto
    have 3:"(i <length (x#xs)) ⟶ (j<length xs)" using One_nat_def Suc Suc_eq_plus1 list.size(4) not_less_eq 
    by metis
    have 4:"(j<length xs) ⟶ ((times a xs)!j = (f a (xs!j)))" using 1 by (metis Cons.hyps)
    have 5:"(x#xs)!i = (xs!j)" using Suc by (metis nth_Cons_Suc)
    from 1 2 4 5 have " (j<length xs) ⟶ ((times a (x#xs))!i = (f a ((x#xs)!i)))" by auto
    from 3 and this have "(i <length (x#xs)) ⟶ ((times a (x#xs))!i = (f a ((x#xs)!i)))" by auto
    from this show ?thesis  by auto
   qed
from this show ?case by auto
qed

lemma simpl_times_elements:assumes "(i<length xs)" shows "((i<(length v)) ⟶ (times a v)!i = f a (v!i))"
using times_elements by auto

(*preparatory lemmas*)
lemma append_simpl: "i<(length xs) ⟶ (xs@ys)!i = (xs!i)" 
using nth_append  by metis

lemma append_simpl2: "i ≥(length xs) ⟶ (xs@ys)!i = (ys!(i- (length xs)))" 
using nth_append less_asym  leD  by metis

lemma append_simpl3: 
assumes "i > (length y)"
shows " ((i <((length (z#zs))*(length y)))) ⟶ ((i - (length y))< (length zs)*(length y))"
proof-
have "length (z#zs) = (length zs)+1" by auto
from this have "(i <((length (z#zs))*(length y))) ⟶ (i <(((length zs)+1)*(length y)))"
by auto
from this have 1: "(i <((length (z#zs))*(length y))) ⟶ (i <((length zs)*(length y)+ (length y)))" by auto
have " (i <((length zs)*(length y)+ (length y))) = ((i - (length y)) <((length zs)*(length y)))"
using assms by auto
from this have "(i <((length (z#zs))*(length y))) ⟶ ((i - (length y)) <((length zs)*(length y)))"
by auto
from this show ?thesis by auto
qed

lemma append_simpl4: "
(i > (length y))
⟶ ((i <((length (z#zs))*(length y)))) ⟶ ((i - (length y))< (length zs)*(length y))"
using append_simpl3 by auto

lemma product_simpl: "i<(length y) ⟶ (product (z#zs) y)!i = (times z y)!i" 
proof-
have a: "product (z#zs) y = (times z y)@(product zs y)" by auto
from this have b: "length (times z y) = (length y)" using preserving_length by auto
from this have "i<(length (times z y)) ⟶ ((times z y)@(product zs y))!i = (times z y)!i" using append_simpl
by metis
from this b have "i<(length y) ⟶ ((times z y)@(product zs y))!i = (times z y)!i" by auto
from this a have "i<(length y) ⟶ (product (z#zs) y)!i = (times z y)!i" by auto
from this show ?thesis by auto
qed


lemma product_simpl2: "(i ≥ (length y)) ⟶ ((product (z#zs) y)!i = (product zs y)!(i- (length y)))" 
using product.simps(2) append_simpl2  preserving_length by metis

lemma division_product: 
assumes "(b::int)>0"
and "a>b"
shows " (a div b) = ((a - b) div b) + 1"
proof-
have " a -b > 0" using assms(2) by auto
have 1: "a - b = a + (-1)*b" by auto
have "(b ≠ 0) ⟶ ((a + b * c) div b = c + a div b)" using div_mult_self2 by auto
have "(b ≠ 0) ⟶ ((a + b * (-1)) div b = (-1) + a div b)" using div_mult_self2 by metis
from this 1 assms(1) have "((a - b) div b) = (-1) + a div b" using  
comm_semiring_1_class.normalizing_semiring_rules(7) less_int_code(1)
by metis
from this have "(a div b) = ((a - b) div b) + 1" by auto
from this show ?thesis by auto
qed

lemma int_nat_div: " (int a) div (int b) = int ((a::nat) div b)"
by (metis zdiv_int)

lemma int_nat_eq: assumes "int (a::nat) = int b"
shows "a = b" by (metis assms of_nat_eq_iff)

lemma nat_div: assumes "(b::nat) > 0" and "a>b"
shows "(a div b) = ((a - b) div b) + 1"
proof-
have 1:"(int b)>0" using assms(1) division_product by auto
moreover have "(int a)>(int b)" using assms(2) by auto
from this 1 have 2: " ((int a) div (int b)) = (((int a) - (int b)) div (int b)) + 1" using division_product
by auto
from int_nat_div have 3: "((int a) div (int b)) = int ( a div b)" by auto
from int_nat_div  assms(2) have 4: "(((int a) - (int b)) div (int b)) = int ((a - b) div b)" by (metis (full_types) less_asym not_less of_nat_diff)
have " (int x) + 1 = int (x +1)" by auto
from this 2 3 4 have "int (a div b) = int (((a - b) div b) + 1)" by auto
from this int_nat_eq have "(a div b) = ((a - b) div b) + 1" by auto
from this show ?thesis by auto
qed

lemma mod_eq:" (m::int) mod n = (m + (-1)*n) mod n"
using mod_mult_self1 by metis

lemma nat_mod_eq: "(int (m::nat)) mod (int n) = int ( m mod n)"
using Divides.transfer_int_nat_functions(2) by auto 

lemma nat_mod: assumes  "(m::nat) > n"
shows "(m::nat) mod n = (m -n) mod n"
using assms mod_if not_less_iff_gr_or_eq by auto 

lemma logic: assumes "A ⟶ B" and "¬A ⟶ B" shows "B" using assms(1) assms(2) by auto

theorem product_elements:
assumes " (y ≠ [])"
shows 
"∀i.((i<((length x)*(length y)))
⟶ ((product x y)!i) = f (x!(i div (length y))) (y!(i mod (length y))))"
 apply(rule allI)
 proof(induct x)
 case Nil
 have "(length [] = 0)" by auto
 also have "length (product [] y) = 0" using product.simps(1) by auto
 from this have "i <(length (product [] y)) ⟹ False" by auto
 moreover have "(product [] y) = []" by auto 
 moreover have "(i<(length (product [] y))) ⟶ 
 ((product x y)!i) = f (x!(i div (length y))) (y!(i mod (length y)))"  
 by auto
 from this show ?case  by auto
 next
 case (Cons z zs)
 have 1:"product (z#zs) y = (times z y)@(product zs y)" by auto
 have 2:"i<(length y)⟶((times z y)!i = f z (y!i))" using times_elements by auto
 moreover have 3:"i<(length y) ⟶ (product (z#zs) y)!i = (times z y)!i" using product_simpl by auto
 moreover  have "i<(length y) ⟶ (product (z#zs) y)!i = f z (y!i)" by (metis calculation(1) calculation(2))
 have "(y ≠ []) ⟶ (length y) >0 " by auto 
 have "(i <(length y)) ⟶  ((i div (length y)) = 0)" by auto
 from this have  6:"(i <(length y)) ⟶ (z#zs)!(i div (length y)) = z" using nth_Cons_0 by auto
 from this have 7:"(i <(length y)) ⟶ (i mod (length y)) = i" by auto
 from 2 6 7 have "(i < (length y)) ⟶ (times z y)!i = f  ((z#zs)!(i div (length y))) (y! (i mod (length y)))
 " by auto 
 from this 3 have step1:"((i < (length y)) ⟶ 
  ((i<((length x)*(length y)) ⟶ ((product (z#zs) y)!i 
  =  f  ((z#zs)!(i div (length y))) (y! (i mod (length y)))))))"
 by auto
 have "((length y) ≤ i) ⟶ (i - (length y)) ≥ 0" by auto
 have step2:" ((length y) < i) ⟶
  ((i < (length (z#zs)*(length y)))⟶((product (z#zs) y)!i) 
   = f ((z#zs)!(i div (length y))) (y!(i mod (length y))))"
  proof-
  have "(length y)>0" using assms by auto
  from this have 1: "(i > (length y))⟶(i div (length y)) = ((i-(length y)) div (length y)) + 1" using nat_div 
    by auto
  have "zs!j = (z#zs)!(j+1)" by auto
  from this have " (zs!((i - (length y)) div (length y))) = (z#zs)!(((i - (length y)) div (length y))+1)"
  by auto
  from this 1  have 2: "(i > (length y))⟶ (zs!((i - (length y)) div (length y)) = (z#zs)!(i div (length y)))"
  by auto
   have "(i > (length y))⟶((i mod (length y)) = ((i - (length y)) mod (length y)))" using nat_mod 
  by auto
  from this have 3:"(i > (length y))⟶((y! (i mod (length y))) = (y! ((i - (length y)) mod (length y))))" 
  by auto
  have 4:" (i > (length y))⟶(product (z#zs) y)!i =  (product zs y)!(i- (length y))" using product_simpl2 
  by auto
  have 5: " (i > (length y))⟶((i <((length (z#zs))*(length y)))) = ((i - (length y))< (length zs)*(length y))"
   by auto
  from this have 6:"∀i.((i<((length zs)*(length y)))
  ⟶ ((product zs y)!i) = f (zs!(i div (length y))) (y!(i mod (length y))))" using Cons.hyps by auto
  from this 5 have "(i > (length y))⟶((i<((length (z#zs))*(length y)))
  ⟶ ((product zs y)!(i -(length y))) = f (zs!((i -(length y)) div (length y))) (y!((i -(length y)) 
   mod (length y))))
   = ((i<((length zs)*(length y)))
  ⟶ ((product zs y)!i) = f (zs!(i div (length y))) (y!(i mod (length y))))
    " by auto
   from this 6 have "(i > (length y))⟶((i<((length (z#zs))*(length y)))
  ⟶ ((product zs y)!(i -(length y))) = f (zs!((i -(length y)) div (length y))) (y!((i -(length y)) 
   mod (length y))))" by auto
   from this 2 3 4 have  "(i > (length y))⟶((i<((length (z#zs))*(length y)))
  ⟶ ((product (z#zs) y)!i) = f ((z#zs)!(i div (length y))) (y!(i mod (length y))))"
  by auto
  from this show ?thesis  by auto
  qed
 have "((length y) = i) ⟶
 ((i < (length (z#zs)*(length y)))⟶((product (z#zs) y)!i) 
   = f ((z#zs)!(i div (length y))) (y!(i mod (length y))))"
  proof-
  have 1:"(i = (length y)) ⟶ ((product (z#zs) y)!i) = (product zs y)!0" using product_simpl2
   by auto
  have 2:"(i = length y) ⟶ (i mod (length y)) = 0" by auto
  have 3:"(i = length y) ⟶ (i div (length y)) = 1" 
    by (metis `y ≠ [] ⟶ 0 < length y` assms div_self less_numeral_extra(3))
  have 4: "(i = length y) ⟶ ((i < (length (z#zs))*(length y)) = (0 < (length zs)*(length y)))" by auto
  have " (z#zs)!1 = (zs!0)" by auto
  from this 3 have 5:" (i = length y) ⟶ ((z#zs)!(i div (length y))) = (zs!0)" by auto 
  have " ∀i.((i < (length zs)*(length y))⟶((product (zs) y)!i) 
    = f ((zs)!(i div (length y))) (y!(i mod (length y))))" using Cons.hyps by auto  
  from this 4 have 6:"(i = length y) ⟶((0 < ((length zs)*(length y)))⟶ (((product (zs) y)!0) 
    = f ((zs)!0) (y!0))) = ((i < ((length zs)*(length y)))⟶(((product zs y)!i) 
    = f ((zs)!(i div (length y))) (y!(i mod (length y)))))" by auto
  have 7: " (0 div (length y)) = 0" by auto
  have 8: " (0 mod (length y)) = 0" by auto
  have 9: "(0 < ((length zs)*(length y))) ⟶ ((product zs y)!0) 
    = f (zs!0) (y!0)" using 7 8 Cons.hyps by auto
  from this 4 5 8 have "(i = length y) ⟶ ((i < (length (z#zs))*(length y)) ⟶ (((product (zs) y)!0) 
    = f ((zs)!0) (y!0)))" 
  by auto
  from this 1 2 5 have "(i = length y) ⟶ ((i < (length (z#zs))*(length y)) ⟶ (((product ((z#zs)) y)!i) 
    = f ((z#zs)!(i div (length y))) (y!(i mod (length y)))))" by auto
  from this show ?thesis by auto
  qed
 from this step2 have step4: " (i ≥ (length y)) ⟶  ((i < (length (z#zs))*(length y)) ⟶ (((product ((z#zs)) y)!i) 
   = f ((z#zs)!(i div (length y))) (y!(i mod (length y)))))" by auto
 have "(i < (length y)) ∨ (i ≥ (length y))" by auto
 from this step1 step4 have " ((i < (length (z#zs))*(length y)) ⟶ (((product ((z#zs)) y)!i) 
   = f ((z#zs)!(i div (length y))) (y!(i mod (length y)))))" using logic by (metis "6" "7" 
  `i < length y ⟶ product (z # zs) y ! i = z * y ! i`) 
 from this show ?case by auto
 qed
(*list_tensor elements*)

lemma nat_int:  "nat (int x + int y) = x + y"
using nat_int of_nat_add by auto

lemma int_nat_equiv: "(x > 0) ⟶ (nat ((int x) + -1)+1) = x"
proof-
have "1 = nat (int 1)" by auto
have "-1 = -int 1" by auto
from this have 1:"(nat ((int x) + -1)+1) = (nat ((int x) + -1) + (nat (int 1)))" by auto
from this have 2:"  (x > 0) ⟶ nat ((int x) + -1 ) + (nat (int 1)) =  (nat (((int x)  + -1) + (int 1)))" 
using of_nat_add nat_int by auto
 have "  (nat (((int x)  + -1) + (int 1))) = (nat ((int x) + -1 + (int 1)))" by auto
from this have "  (nat (((int x)  + -1) + (int 1))) = (nat ((int x)))" by auto
from this have "(nat (((int x)  + -1) + (int 1))) = x" by auto
from this 1 2 have " (x > 0) ⟶ nat ((int x) + -1 ) + 1 = x" by auto
from this show ?thesis by auto
qed 

lemma list_int_nat: "(k>0) ⟶ ((x#xs)!k = xs!(nat ((int k)+-1)))"  
  proof-
  have " ((x#xs)!(k+1) = xs!k)" by auto
  have "j = (k+1) ⟶ (nat ((int j)+-1)) = k" by auto
  moreover have "(nat ((int j)+-1)) = k ⟶ ((nat ((int j)+-1)) + 1) = (k +1)" by auto
  moreover have "(j>0)⟶(((nat ((int j)+-1)) + 1) = j)" using  int_nat_equiv by (auto)
  moreover have "(k>0) ⟶ ((x#xs)!k = xs!(nat ((int k)+-1)))" 
  by (metis Suc_eq_plus1 int_nat_equiv nth_Cons_Suc)
  from this show ?thesis by auto
  qed

theorem list_tensor_elements: 
"∀i.∀j.(((i<((length v)*(row_length M)))∧(j < (length M)))∧(mat (row_length M) (length M) M)
⟶ ((list_tensor v M)!j!i) = f (v!(i div (row_length M))) (M!j!(i mod (row_length M))))"
 apply(rule allI)
 apply(rule allI)
 proof(induct M)
 case Nil
 have "row_length [] = 0" using row_length_def by auto
 from this have "(length v)*(row_length []) = 0" by auto
 from this have "((i<((length v)*(row_length [])))∧(j < (length []))) ⟶ False" by auto
 moreover have "list_tensor v [] = []" by auto 
 moreover have "(((i<((length v)*(row_length [])))∧(j < (length [])))
⟶ ((list_tensor v [])!j!i) = f (v!(i div (row_length []))) ([]!j!(i mod (row_length []))))"
 by auto
 from this show ?case by auto
 next
 case (Cons a M)
 have "(((i<((length v)*(row_length (a#M))))∧(j < (length (a#M))))∧(mat (row_length (a#M)) 
 (length (a#M)) (a#M))
⟶ ((list_tensor v (a#M))!j!i) = f (v!(i div (row_length (a#M)))) ((a#M)!j!(i mod (row_length (a#M)))))"
  proof(cases a)
  case Nil
  have "row_length ([]#M) = 0" using row_length_def by auto
  from this have "(length v)*(row_length ([]#M)) = 0" by auto
  from this have "((i<((length v)*(row_length ([]#M))))∧(j < (length ([]#M)))) ⟶ False" by auto
  moreover have "(((i<((length v)*(row_length ([]#M))))∧(j < (length ([]#M))))
  ⟶ ((list_tensor v ([]#M))!j!i) = f (v!(i div (row_length ([]#M)))) ([]!j!(i mod (row_length ([]#M)))))"
  by (metis calculation)
  from this show ?thesis by (metis Nil `length v * row_length ([] # M) = 0` less_nat_zero_code)
  next
  case (Cons x xs)
  have 1:"(a#M)!(j+1) = M!j" by auto
  have " (((i<((length v)*(row_length M)))∧(j < (length M)))∧ (mat (row_length M) (length M) M)
  ⟶ ((list_tensor v M)!j!i) = f (v!(i div (row_length M))) (M!j!(i mod (row_length M))))" 
  using Cons.hyps by auto
  have 2: "(row_length (a#M)) = (length a)" using row_length_def by auto
  from this have 3:"(i< (row_length (a#M))*(length v)) = (i < (length a)*(length v))" by auto
  have "a ≠ []" using Cons by auto
  from this have 4:" ∀i.((i < (length a)*(length v)) ⟶  
    ((product v a)!i) = f (v!(i div (length a))) (a!(i mod (length a))))" using product_elements Cons.hyps
  using nat_mult_commute by auto
  have "(list_tensor v (a#M))!0 = (product v a)" using list_tensor.simps(2) by auto
  from this 2 4 have 5: " ∀i.((i < (row_length (a#M))*(length v)) ⟶  
    ((list_tensor v (a#M))!0!i) = f (v!(i div (row_length (a#M)))) ((a#M)!0!(i mod (row_length (a#M)))))" 
  by auto 
  have "length (a#M)>0" by auto
  from this 5 have 6: "(j = 0)⟶
   ((((i < (row_length (a#M))*(length v)) ∧(j < (length (a#M))))
   ∧ (mat (row_length (a#M)) (length (a#M)) (a#M))   ⟶  
   ((list_tensor v (a#M))!j!i) = f (v!(i div (row_length (a#M)))) ((a#M)!j!(i mod (row_length (a#M))))))" 
   by auto 
  have " (((i < (row_length (a#M))*(length v)) ∧(j < (length (a#M))))
   ∧ (mat (row_length (a#M)) (length (a#M)) (a#M))   ⟶  
  ((list_tensor v (a#M))!j!i) = f (v!(i div (row_length (a#M)))) ((a#M)!j!(i mod (row_length (a#M)))))" 
   proof(cases M)
   case Nil
   have "(length (a#[])) = 1" by auto
   from this have "(j<(length (a#[]))) = (j = 0)" by auto
   from this have " ( (((i < (row_length (a#[]))*(length v)) ∧(j < (length (a#[]))))
   ∧ (mat (row_length (a#[])) (length (a#[])) (a#[]))   ⟶  
   ((list_tensor v (a#[]))!j!i) = f (v!(i div (row_length (a#[])))) ((a#[])!j!(i mod (row_length (a#[]))))))" 
   using 6 Nil by auto
   from this show ?thesis using Nil by auto 
   next
   case (Cons b N)
   have 7:"(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) ⟶ 
    (row_length (a#b#N) = (row_length (b#N)))" 
     proof-
     have "(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) ⟶ (b ∈ set (a#b#M))" by auto
     moreover have "(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) 
          ⟶ (Ball (set (a#b#N)) (vec (row_length (a#b#N))))"
          using mat_def by metis
     moreover have "(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) ⟶ (b ∈ (set (a#b#N)))⟶ 
                        (vec (row_length (a#b#N)) b)"  by (metis calculation(2))
     from this have "(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) 
       ⟶ (length b) = (row_length (a#b#N))" using vec_def by auto
     from this have "(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) 
          ⟶ (row_length (b#N)) = (row_length (a#b#N))" using row_length_def by auto
     then show ?thesis by auto
     qed
   have 8: "(j>0) ⟶ ((list_tensor v (b#N))!(nat ((int j)+-1))) = (list_tensor v (a#b#N))!j"
    using list_tensor.simps(2) using list_int_nat by metis
   have 9: "(j>0) ⟶ (((i < (row_length (b#N))*(length v)) ∧((nat ((int j)+-1)) < (length (b#N))))
           ∧ (mat (row_length (b#N)) (length (b#N)) (b#N))   ⟶  
           ((list_tensor v (b#N))!(nat ((int j)+-1))!i) = f (v!(i div (row_length (b#N)))) 
           ((b#N)!(nat ((int j)+-1))!(i mod (row_length (b#N)))))"
           using Cons.hyps Cons nat_mult_commute by metis
   have "(j>0) ⟶ ((nat ((int j) + -1)) < (length (b#N))) ⟶ ((nat ((int j) + -1) + 1) < length (a#b#N))"
    by auto
   from this have "(j>0) ⟶ ((nat ((int j) + -1)) < (length (b#N))) = (j < length (a#b#N))"
     by auto
   from this have  "(j>0) ⟶ (((i < (row_length (b#N))*(length v)) ∧ (j < length (a#b#N)))
     ∧ (mat (row_length (b#N)) (length (b#N)) (b#N))   ⟶  
     ((list_tensor v (b#N))!(nat ((int j)+-1))!i) = f (v!(i div (row_length (b#N)))) ((b#N)!(nat ((int j)+-1))!(i mod (row_length (b#N)))))"
      using Cons.hyps Cons nat_mult_commute by metis
   from this 8 have "(j>0) ⟶ (((i < (row_length (b#N))*(length v)) ∧ (j < length (a#b#N)))
     ∧ (mat (row_length (b#N)) (length (b#N)) (b#N))   ⟶  
     ((list_tensor v (a#b#N))!j!i) = f (v!(i div (row_length (b#N)))) ((b#N)!(nat ((int j)+-1))!(i mod (row_length (b#N)))))"
     by auto
   moreover have "(j>0) ⟶ (b#N)!(nat ((int j)+-1)) = (a#b#N)!j" using list_int_nat by metis
   moreover have " (j>0) ⟶ (((i < (row_length (b#N))*(length v)) ∧ (j < length (a#b#N)))
     ∧ (mat (row_length (b#N)) (length (b#N)) (b#N))   ⟶  
     ((list_tensor v (a#b#N))!j!i) = f (v!(i div (row_length (b#N)))) ((a#b#N)!j!(i mod (row_length (b#N)))))"
     by (metis calculation(1) calculation(2))
   from this have  " (j>0) ⟶ (((i < (row_length (b#N))*(length v)) ∧ (j < length (a#b#N)))
      ∧ (mat (row_length (a#b#N)) (length (a#b#N)) (a#b#N))   ⟶  
      ((list_tensor v (a#b#N))!j!i) = f (v!(i div (row_length (b#N)))) ((a#b#N)!j!(i mod (row_length (b#N)))))"
      using  reduct_matrix by (metis)
   moreover  have "(mat (row_length (a#b#N)) (length (a#b#N)) (a#b#N))
   ⟶(row_length (b#N)) = (row_length (a#b#N))" by (metis "7" Cons)
   moreover have 10:"  (j>0) ⟶ (((i < (row_length (a#b#N))*(length v)) ∧ (j < length (a#b#N)))
      ∧ (mat (row_length (a#b#N)) (length (a#b#N)) (a#b#N))   ⟶  
      ((list_tensor v (a#b#N))!j!i) = f (v!(i div (row_length (a#b#N)))) ((a#b#N)!j!(i mod (row_length (a#b#N)))))"
     by (metis calculation(3) calculation(4))
   have "(j = 0) ∨ (j > 0)" by auto
    from this 6 10 logic have "(((i < (row_length (a#b#N))*(length v)) ∧ (j < length (a#b#N)))
      ∧ (mat (row_length (a#b#N)) (length (a#b#N)) (a#b#N))   ⟶  
     ((list_tensor v (a#b#N))!j!i) = f (v!(i div (row_length (a#b#N)))) ((a#b#N)!j!(i mod (row_length (a#b#N)))))"
     using  Cons by metis
     from this show ?thesis by (metis Cons)
   qed
  from this show ?thesis by (metis nat_mult_commute)
  qed
  from this show ?case by auto
  qed
