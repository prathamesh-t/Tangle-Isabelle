header {* Basic Operations on Matrices *}

theory Matrix_Tensor
imports
  Utility Matrix_Arith
begin

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
 (* 1. ⋀a M1. length (M1 ⊗ M2) = length M1 * length M2 ⟹ length (a # M1 ⊗ M2) = length (a # M1) * length M2*)
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

theorem tensor_associativity: "(A⊗B)⊗C = A ⊗(B ⊗ C)" using tensor.simps append.simps sledgehammer 

(*To Prove-
That Tensors Commute with products*)
(*theorem multiplicative_distributivity:  mat k1 l1 M1 mat k2 l2 N1 mat l1 j1 M2 mat l2 j2 N2 shows 
( ((M1⊗N1)∘(M2⊗N2)) = (M1∘M2)⊗(M2∘N2)*)
  
end

 

      
