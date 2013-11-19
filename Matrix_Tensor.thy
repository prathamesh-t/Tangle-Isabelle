header {* Basic Operations on Matrices *}

theory Matrix_Tensor
imports
  Utility Matrix_Arith
begin(*Matrix Tensor begins*)

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



primrec tensor::" nat mat ⇒ nat mat ⇒nat mat" (infixl "⊗" 63)
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

theorem well_defined_mult: assumes "mat nr nc m" and "m ≠ []"  
shows "mat (nr*(length v)) nc (list_tensor v m)"
proof (induct m arbitrary:nr)
case (Cons a n)
 have "mat nr nc (a#n)" using 
 show ?case 
