theory Tangles_update
imports Datatype Main tangle_relation 
begin

(*each  block is a horizontal block built by putting basic tangle bricks next to each other.
(1) e1 is the straight line
(2) e2 is the up facing cusp
(3) e3 is the bottom facing cus
(4) e4 is the positive cross
(5) e5 is the negative cross*)
 
datatype brick = a1
                |a2
                |a3
                |a4
                |a5

datatype block = cement brick
                 |cons brick block  (infixr "#" 60)              

primrec bricklength::"brick ⇒ nat"
where
"bricklength a1 = 1"|
"bricklength a2 =  1"|
"bricklength a3 =  1"|
"bricklength a4 =  1"|
"bricklength a5 =  1"

primrec length::"block ⇒ nat"
where
"length (cement x) = bricklength x"|
"length (cons x y) = (bricklength x) + (length y)"


definition e1::block where "e1 ≡ (cement a1)"
definition e2::block where "e2 ≡ (cement a2)"
definition e3::block where "e3 ≡ (cement a3)"
definition e4::block where "e4 ≡ (cement a4)"
definition e5::block where "e5 ≡ (cement a5)"


(*count tells us the number of incoming and outgoing strangs of each block*)

primrec brickcount::"brick ⇒ int × int "
where
"brickcount a1 = (1,1)"|
"brickcount a2 = (0,2)"|
"brickcount a3 = (2,0)"|
"brickcount a4 = (2,2)"|
"brickcount a5 = (2,2)"


primrec count::"block ⇒ int × int "
where
"count (cement x) = (brickcount x)"
|"count (cons x y) = (fst (brickcount x) + fst (count y), snd (brickcount x) + snd (count y))"

lemma brickcount_nonnegative: "fst (brickcount x) ≥ 0" 
by 
(metis Nat_Transfer.transfer_nat_int_function_closures(6) brick.exhaust brick.simps(26)
 brick.simps(27) brick.simps(28) brick.simps(30) brickcount.simps(4) 
dbl_def dbl_simps(3) fst_conv less_imp_le one_plus_BitM order_refl semiring_norm(26) 
zero_less_numeral brickcount_def)

lemma count_nonnegative: "fst (count x) ≥ 0" 
apply(induct_tac x)
apply(auto)
apply(simp add:brickcount_nonnegative)
apply(simp add:count_def)
apply (metis (lifting) add_increasing brickcount_nonnegative)
done

primrec append :: "block => block => block" (infixr "⊗" 65) where
append_Nil: "(cement x) ⊗ ys = cons x ys" |
append_Cons: "((x#xs)⊗ys) = x#(xs⊗ys)"

lemma leftright_associativity: "(x⊗y)⊗z = x⊗(y⊗z)"
apply(induct_tac x)
apply(auto)
done

lemma left_associativity: "(x⊗y)⊗z = x⊗y⊗z"
apply(induct_tac x)
apply(auto)
done

lemma right_associativity: "x⊗(y⊗z) =x ⊗ y ⊗z"
apply(auto)
done


lemma count_positive: "((fst (count (cement x)) > 0) ∨ (fst (count y) > 0)) 
⟹ (fst (count (x#y)) > 0)" 
proof-
have "fst (count (x#y)) =  (fst (brickcount x) + fst (count y))" using count_def by auto
also have " (fst (brickcount x)) = fst (count (cement x))" using count_def by auto
then have "((fst (count (cement x))) > 0) = ((fst (brickcount x)) > 0)" using count_def by auto
then have "((fst (brickcount x) > 0) ∨ (fst (count y) > 0)) ⟹ (fst (brickcount x) + fst (count y))>0"
using count_nonnegative add_nonneg_pos add_pos_nonneg brickcount_nonnegative by metis
from this  show  "((fst (count (cement x)) > 0) ∨ (fst (count y) > 0)) 
⟹ (fst (count (x#y)) > 0)" by auto
qed
  
(*
lemma count_positive: "((fst (count x) > 0) ∨ (fst (count y) > 0)) ⟹ (fst (count (x⊗y)) > 0)" 
proof-
have "fst (count (x⊗y)) = (fst (count x) + fst (count y))" using count_def by auto
also have "((fst (count x) > 0) ∨ (fst (count y) > 0)) ⟹ (fst (count x) + fst (count y))>0"
using count_nonnegative add_nonneg_pos add_pos_nonneg by metis
then show  "((fst (count x) > 0) ∨ (fst (count y) > 0)) ⟹ (fst (count (x⊗y)) > 0)" by auto
qed  
*)

lemma trivial: "(count (a1 # e2)) = (1,3)"
apply (simp add: e2_def)
done

(*cusp is defined*)

primrec brick_cusp::"brick ⇒ bool"
where
"brick_cusp a1 = False"|
"brick_cusp a2 = True"|
"brick_cusp a3 = False"|
"brick_cusp a4 = False"|
"brick_cusp a5 = False"


primrec cusp::"block ⇒ bool"
where
"cusp (cement x) = brick_cusp x"|
"cusp (x#y) = (if (x= a2) then (cusp y) else False)"


lemma cusp_basic: "((cusp x) = False) ⟹ 
((x=e1)∨(x=e3)∨(x=e4)∨(x=e5))∨(∃y1.∃y2.∃y3.(x=(y1⊗y2⊗y3)∧ 
((y1=e1)∨(y1=e3)∨(y1=e4)∨(y1=e5))∨(y2=e1)∨(y2=e3)∨(y2=e4)∨(y2=e5))∨((y3=e1)∨(y3=e3)∨(y3=e4)∨(y3=e5)))"
by metis


lemma brickcount_zero_implies_a2:"(fst (brickcount x)= 0) ⟹ (x = a2)"
apply(case_tac "brickcount x")
apply(auto)
apply(case_tac "x")
apply(auto)
done

lemma brickcount_zero_implies_brick_cusp:"(fst (brickcount x)= 0) ⟹ (brick_cusp x)"
apply(case_tac "brick_cusp x")
apply(simp add: brickcount_zero_implies_a2)
apply(auto)
apply(case_tac "x")
apply(auto)
done

lemma count_zero_implies_cusp:"(fst (count x)= 0) ⟹ (cusp x)"
apply(case_tac "count x")
apply(simp add: brickcount_zero_implies_brick_cusp)
apply(auto)
apply(case_tac "x")
apply (metis brick_cusp.simps(2) brickcount_zero_implies_a2 count.simps(1) cusp.simps(1) fst_conv)
apply(case_tac "cusp x")
oops

(*cusp ends*)

primrec makestrand:: "nat ⇒ block"
where
"makestrand 0 = e1"
|"makestrand (Suc n) = a1#(makestrand n)"

(*walls are tangle diagrams obtained by placing a horizontal blocks a top each other*)

datatype walls = basic block
                |prod block  walls  (infixr "*" 66)

primrec compose :: "walls => walls => walls" (infixr "∘" 66) where
compose_Nil: "(basic x) ∘ ys =  prod x ys" |
compose_Cons: "((prod x xs)∘ys) = prod x (xs∘ys)"

lemma compose_leftassociativity: "(((x::walls) ∘ y) ∘ z) = (x∘y ∘z)"
apply(induct_tac x)
apply(auto)
done

lemma compose_rightassociativity: "(x::walls) ∘ (y ∘ z) = (x∘y ∘z)"
apply(induct_tac x)
apply(auto)
done


primrec wall_count:: "walls ⇒ int × int" where
"wall_count (basic x) = count x"                                               
|"wall_count (x*ys) = (fst (count x),snd (wall_count ys))"

definition abs::"int ⇒ int" where
"abs x ≡ if (x≥0) then x else (0-x)" 

primrec wall_list:: "walls ⇒ int list" where
"wall_list (basic x) = []"|
"wall_list (x * y) =  (abs (fst(wall_count y) - snd(count x)))#(wall_list y)"

lemma wall_count_compose: "wall_count (xs∘ys) = (fst (wall_count (xs)), snd(wall_count (ys)))"
apply(induct_tac xs)
apply(auto)
done 

(*test exercises*)
lemma trivial2: "wall_list (basic e1) = []"
apply(auto)
done


lemma trivial3: "fst(wall_count (basic e3))- snd(wall_count (basic e1)) = 1"
apply(simp add:e3_def e1_def)
done

lemma trivial4: "wall_list ((basic e3)∘(basic e1)∘(basic e1)) = [1,0]"
apply(simp add: e3_def e1_def)
apply(simp add:abs_def)
done


(*end of test exercises*)

primrec list_sum::"int list ⇒ int" 
where
"list_sum [] = 0"|
"list_sum (x#xs) = x+ list_sum xs"

(*diagram checks when a wall represents a knot diagram*)

typedef diagram = "{(x::walls).  (list_sum (wall_list x)+(abs(fst(wall_count x))
+ abs(snd(wall_count x)))) = 0}"
apply (rule_tac x = "prod e2 (basic e3)" in exI)
apply(auto)
apply(simp add:abs_def e2_def e3_def)
done

(*tangle relations are being defined here. Tangle equivalence is broken into many equivalances each 
of which is defined as a disjunction of many functions.*)

(*tangle_uncross*)

definition tanglerel_uncross_positiveflip::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_uncross_positiveflip x y ≡ (∃y1.∃z1.∃z2.∃z3.∃w1.∃w2.∃w3.∃y2.(x = Abs_diagram ((y1)
∘(basic (z1⊗e1⊗e2⊗w1)∘(basic (z2⊗e4⊗e1⊗w2))∘(basic (z3⊗e1⊗e3⊗w3))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e2⊗e1⊗w1))∘(basic (z2⊗e1⊗e4⊗w2))∘(basic (z3⊗e3⊗e1⊗w3))∘(y2)))∧((snd (count z1)) = 
(fst (count z2)))∧((snd (count z2)) = (fst (count z3))) ∧ ((snd (count w1)) = (fst
(count w2)))∧((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_positivestraighten::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_uncross_positivestraighten x y ≡ (∃y1.∃z1.∃z2.∃z3.∃w1.∃w2.∃w3.∃y2.(x = Abs_diagram ((y1)
∘(basic (z1⊗e2⊗e1⊗w1)∘(basic (z2⊗e1⊗e4⊗w2))∘(basic (z3⊗e3⊗e1⊗w3))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗w1))∘(basic (z2⊗e1⊗w2))∘(basic (z3⊗e1⊗w3))∘(y2)))∧((snd (count z1)) = 
(fst (count z2)))∧((snd (count z2)) = (fst (count z3))) ∧ ((snd (count w1)) = (fst
(count w2)))∧((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_negativeflip::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_uncross_negativeflip x y ≡ (∃y1.∃z1.∃z2.∃z3.∃w1.∃w2.∃w3.∃y2.(x = Abs_diagram ((y1)
∘(basic (z1⊗e1⊗e2⊗w1)∘(basic (z2⊗e5⊗e1⊗w2))∘(basic (z3⊗e1⊗e3⊗w3))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e2⊗e1⊗w1))∘(basic (z2⊗e1⊗e5⊗w2))∘(basic (z3⊗e3⊗e1⊗w3))∘(y2)))∧((snd (count z1)) = 
(fst (count z2)))∧((snd (count z2)) = (fst (count z3))) ∧ ((snd (count w1)) = (fst
(count w2)))∧((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_negativestraighten::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_uncross_negativestraighten x y ≡ (∃y1.∃z1.∃z2.∃z3.∃w1.∃w2.∃w3.∃y2.(x = Abs_diagram ((y1)
∘(basic (z1⊗e2⊗e1⊗w1)∘(basic (z2⊗e1⊗e5⊗w2))∘(basic (z3⊗e3⊗e1⊗w3))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗w1))∘(basic (z2⊗e1⊗w2))∘(basic (z3⊗e1⊗w3))∘(y2)))∧((snd (count z1)) = 
(fst (count z2)))∧((snd (count z2)) = (fst (count z3))) ∧ ((snd (count w1)) = (fst
(count w2)))∧((snd (count w2)) = (fst (count w3))))"

(*right positive moves- these are redundant cases but need to be proved formally*)
definition tanglerel_uncross_rightpositiveflip::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_uncross_rightpositiveflip x y ≡ (∃y1.∃w1.∃w2.∃w3.∃y2.(x = Abs_diagram ((y1)
∘(basic (e1⊗e2⊗w1)∘(basic (e4⊗e1⊗w2))∘(basic (e1⊗e3⊗w3))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (e2⊗e1⊗w1))∘(basic (e1⊗e4⊗w2))∘(basic (e3⊗e1⊗w3))∘(y2)))∧((snd (count w1)) = (fst
(count w2)))∧((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_rightpositivestraighten::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_uncross_rightpositivestraighten x y ≡ (∃y1.∃w1.∃w2.∃w3.∃y2.(x = Abs_diagram ((y1)
∘(basic (e2⊗e1⊗w1)∘(basic (e1⊗e4⊗w2))∘(basic (e3⊗e1⊗w3))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗w1))∘(basic (e1⊗w2))∘(basic (e1⊗w3))∘(y2)))∧((snd (count w1)) = (fst
(count w2)))∧((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_rightnegativeflip::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_uncross_rightnegativeflip x y ≡ (∃y1.∃w1.∃w2.∃w3.∃y2.(x = Abs_diagram ((y1)
∘(basic (e1⊗e2⊗w1)∘(basic (e5⊗e1⊗w2))∘(basic (e1⊗e3⊗w3))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (e2⊗e1⊗w1))∘(basic (e1⊗e5⊗w2))∘(basic (e3⊗e1⊗w3))∘(y2)))∧  ((snd (count w1)) = (fst
(count w2)))∧((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_rightnegativestraighten::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_uncross_rightnegativestraighten x y ≡ (∃y1.∃w1.∃w2.∃w3.∃y2.(x = Abs_diagram ((y1)
∘(basic (e2⊗e1⊗w1)∘(basic (e1⊗e5⊗w2))∘(basic (e3⊗e1⊗w3))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗w1))∘(basic (e1⊗w2))∘(basic (e1⊗w3))∘(y2)))∧ ((snd (count w1)) = (fst
(count w2)))∧((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_leftpositiveflip::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_uncross_leftpositiveflip x y ≡ (∃y1.∃z1.∃z2.∃z3.∃y2.(x = Abs_diagram ((y1)
∘(basic (z1⊗e1⊗e2)∘(basic (z2⊗e4⊗e1))∘(basic (z3⊗e1⊗e3))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e2⊗e1))∘(basic (z2⊗e1⊗e4))∘(basic (z3⊗e3⊗e1))∘(y2)))∧((snd (count z1)) = 
(fst (count z2)))∧((snd (count z2)) = (fst (count z3))))"

definition tanglerel_uncross_leftpositivestraighten::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_uncross_leftpositivestraighten x y ≡ (∃y1.∃z1.∃z2.∃z3.∃y2.(x = Abs_diagram ((y1)
∘(basic (z1⊗e2⊗e1)∘(basic (z2⊗e1⊗e4))∘(basic (z3⊗e3⊗e1))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1))∘(basic (z2⊗e1))∘(basic (z3⊗e1))∘(y2)))∧((snd (count z1)) = 
(fst (count z2)))∧((snd (count z2)) = (fst (count z3))))"

definition tanglerel_uncross_leftnegativeflip::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_uncross_leftnegativeflip x y ≡ (∃y1.∃z1.∃z2.∃z3.∃y2.(x = Abs_diagram ((y1)
∘(basic (z1⊗e1⊗e2)∘(basic (z2⊗e5⊗e1))∘(basic (z3⊗e1⊗e3))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic e1)∘(basic e1)∘(basic e1)∘(y2)))∧((snd (count z1)) = 
(fst (count z2)))∧((snd (count z2)) = (fst (count z3))))"

definition tanglerel_uncross_leftnegativestraighten::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_uncross_leftnegativestraighten x y ≡ (∃y1.∃z1.∃z2.∃z3.∃y2.(x = Abs_diagram ((y1)
∘(basic (z1⊗e2⊗e1)∘(basic (z2⊗e1⊗e5))∘(basic (z3⊗e3⊗e1))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1))∘(basic (z2⊗e1))∘(basic (z3⊗e1))∘(y2)))∧((snd (count z1)) = 
(fst (count z2)))∧((snd (count z2)) = (fst (count z3))))"

(*tangle_uncross definition*)
definition tanglerel_uncross::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_uncross x y ≡ 
((tanglerel_uncross_positiveflip x y)∨(tanglerel_uncross_positivestraighten x y)
∨(tanglerel_uncross_negativeflip x y)∨(tanglerel_uncross_negativestraighten x y)
∨(tanglerel_uncross_leftpositiveflip x y)∨(tanglerel_uncross_leftpositivestraighten x y)
∨(tanglerel_uncross_leftnegativeflip x y)∨(tanglerel_uncross_leftnegativestraighten x y)
∨(tanglerel_uncross_rightpositiveflip x y)∨(tanglerel_uncross_rightpositivestraighten x y)
∨(tanglerel_uncross_rightnegativeflip x y)∨(tanglerel_uncross_rightnegativestraighten x y))
"
(*tangle_uncross ends*)
(*tangle_pull begins*)

definition tanglerel_pull_posneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_posneg x y ≡  ∃y1.∃z1.∃z2.∃w1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e4⊗w1)∘(basic (z2⊗e5⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1⊗w1))∘(basic (z2⊗e1⊗e1⊗w2))∘(y2)))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = (fst (count w2))))"


definition tanglerel_pull_negpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_negpos x y ≡  ∃y1.∃z1.∃z2.∃w1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e5⊗w1)∘(basic (z2⊗e4⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1⊗w1))∘(basic (z2⊗e1⊗e1⊗w2))∘(y2)))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = (fst (count w2))))"

(*above cases are redundant*)  
(*null*)
definition tanglerel_pull_nullposneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_nullposneg x y ≡  ∃y1.∃y2.((x = Abs_diagram ((y1)
∘(basic (e4)∘(basic (e5)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e1))∘(basic (e1⊗e1))∘(y2))))"


definition tanglerel_pull_nullnegpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_nullnegpos x y ≡  ∃y1.∃y2.((x = Abs_diagram ((y1)
∘(basic (e5)∘(basic (e4)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e1))∘(basic (e1⊗e1))∘(y2))))"

(*following cases are redundant, infact all of them can be deduced from the nullcases*)
(*bottom right*)
definition tanglerel_pull_botrightposneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_botrightposneg x y ≡  ∃y1.∃z2.∃w1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (e4⊗w1)∘(basic (z2⊗e5⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)∘(basic (e1⊗e1⊗w1))∘(basic (z2⊗e1⊗e1⊗w2))∘(y2)))
∧((snd (count w1)) = (fst (count w2)))
∧((fst (count z2)) = 0))
"


definition tanglerel_pull_botrightnegpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_botrightnegpos x y ≡  ∃y1.∃z2.∃w1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (e5⊗w1)∘(basic (z2⊗e4⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e1⊗w1))∘(basic (z2⊗e1⊗e1⊗w2))∘(y2)))
∧((fst (count z2)) = 0)
∧((snd (count w1)) = (fst (count w2))))"

(*bottom left*)
definition tanglerel_pull_botleftposneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_botleftposneg x y ≡  ∃y1.∃z1.∃z2.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e4)∘(basic (z2⊗e5⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1))∘(basic (z2⊗e1⊗e1⊗w2))∘(y2)))
∧((snd (count z1)) = (fst (count z2)))
∧((fst (count w2)) = 0))"


definition tanglerel_pull_botleftnegpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_botleftnegpos x y ≡  ∃y1.∃z1.∃z2.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e5)∘(basic (z2⊗e4⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1))∘(basic (z2⊗e1⊗e1⊗w2))∘(y2)))
∧((snd (count z1)) = (fst (count z2)))
∧((fst (count w2)) = 0))"
   
(*top right*)

definition tanglerel_pull_toprightposneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_toprightposneg x y ≡  ∃y1.∃z1.∃w1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e4⊗w1)∘(basic (e5⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1⊗w1))∘(basic (e1⊗e1⊗w2))∘(y2)))
∧((snd (count z1)) = 0)
∧((snd (count w1)) = (fst (count w2))))"


definition tanglerel_pull_toprightnegpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_toprightnegpos x y ≡  ∃y1.∃z1.∃w1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e5⊗w1)∘(basic (e4⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1⊗w1))∘(basic (e1⊗e1⊗w2))∘(y2)))
∧((snd (count z1)) = 0)
∧((snd (count w1)) = (fst (count w2))))"
  
(*top left*)

definition tanglerel_pull_topleftposneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_topleftposneg x y ≡  ∃y1.∃z1.∃z2.∃w1.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e4⊗w1)∘(basic (z2⊗e5)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1⊗w1))∘(basic (z2⊗e1⊗e1))∘(y2)))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = 0))"


definition tanglerel_pull_topleftnegpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_topleftnegpos x y ≡  ∃y1.∃z1.∃z2.∃w1.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e5⊗w1)∘(basic (z2⊗e4)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1⊗w1))∘(basic (z2⊗e1⊗e1))∘(y2)))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = 0))"


(*top*)
definition tanglerel_pull_topposneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_topposneg x y ≡  ∃y1.∃z1.∃w1.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e4⊗w1)∘(basic (e5)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1⊗w1))∘(basic (e1⊗e1))∘(y2)))
∧((snd (count z1)) = 0)
∧((snd (count w1)) = 0))"


definition tanglerel_pull_topnegpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_topnegpos x y ≡  ∃y1.∃z1.∃w1.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e5⊗w1)∘(basic (e4)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1⊗w1))∘(basic (e1⊗e1))∘(y2)))
∧((snd (count z1)) = 0)
∧((snd (count w1)) = 0))"
  
(*bottom*)

definition tanglerel_pull_botposneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_botposneg x y ≡  ∃y1.∃z2.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (e4)∘(basic (z2⊗e5⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e1))∘(basic (z2⊗e1⊗e1⊗w2))∘(y2)))
∧(0 = (fst (count z2)))
∧(0 = (fst (count w2))))"


definition tanglerel_pull_botnegpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_botnegpos x y ≡  ∃y1.∃z1.∃w1.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e5⊗w1)∘(basic (e4)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1⊗w1))∘(basic (e1⊗e1))∘(y2)))
∧((snd (count z1)) = 0)
∧((snd (count w1)) = 0))"

(*right*)
definition tanglerel_pull_rightposneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_rightposneg x y ≡  ∃y1.∃w1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (e4⊗w1)∘(basic (e5⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e1⊗w1))∘(basic (e1⊗e1⊗w2))∘(y2)))
∧((snd (count w1)) = (fst (count w2))))"


definition tanglerel_pull_rightnegpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_rightnegpos x y ≡  ∃y1.∃w1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (e5⊗w1)∘(basic (e4⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e1⊗w1))∘(basic (e1⊗e1⊗w2))∘(y2)))
∧((snd (count w1)) = (fst (count w2))))"

(*left*)
definition tanglerel_pull_leftposneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_leftposneg x y ≡  ∃y1.∃z1.∃z2.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e4)∘(basic (z2⊗e5)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1))∘(basic (z2⊗e1⊗e1))∘(y2)))
∧((snd (count z1)) = (fst (count z2))))"

definition tanglerel_pull_leftnegpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_leftnegpos x y ≡  ∃y1.∃z1.∃z2.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e5)∘(basic (z2⊗e4)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1))∘(basic (z2⊗e1⊗e1))∘(y2)))
∧((snd (count z1)) = (fst (count z2))))"
  
  
(*leftcross*)

definition tanglerel_pull_leftcrossposneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_leftcrossposneg x y ≡  ∃y1.∃z2.∃w1.∃y2.((x = Abs_diagram ((y1)
∘(basic (e4⊗w1)∘(basic (z2⊗e5)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e1⊗w1))∘(basic (z2⊗e1⊗e1))∘(y2)))
∧(0 = (fst (count z2)))
∧((snd (count w1)) = 0))"


definition tanglerel_pull_leftcrossnegpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_leftcrossnegpos x y ≡  ∃y1.∃z2.∃w1.∃y2.((x = Abs_diagram ((y1)
∘(basic (e5⊗w1)∘(basic (z2⊗e4)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e1⊗w1))∘(basic (z2⊗e1⊗e1))∘(y2)))
∧(0 = (fst (count z2)))
∧((snd (count w1)) = 0))"
  
(*right cross*)

definition tanglerel_pull_rightcrossposneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_rightcrossposneg x y ≡  ∃y1.∃z1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e4)∘(basic (e5⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1))∘(basic (e1⊗e1⊗w2))∘(y2)))
∧((snd (count z1)) = 0)
∧(0 = (fst (count w2))))"


definition tanglerel_pull_rightcrossnegpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_rightcrossnegpos x y ≡  ∃y1.∃z1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e5)∘(basic (e4⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1))∘(basic (e1⊗e1⊗w2))∘(y2)))
∧((snd (count z1)) = 0)
∧(0 = (fst (count w2))))"
  
(*null leftbottom- denoted lb*)

definition tanglerel_pull_lbposneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_lbposneg x y ≡  ∃y1.∃z1.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e4)∘(basic (e5)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1))∘(basic (e1⊗e1))∘(y2)))
∧((snd (count z1)) = 0))"


definition tanglerel_pull_lbnegpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_lbnegpos x y ≡  ∃y1.∃z1.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e5)∘(basic (e4)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1))∘(basic (e1⊗e1))∘(y2)))
∧((snd (count z1)) = 0))"
  
(*null right bottom - denoted rb*)

definition tanglerel_pull_rbposneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_rbposneg x y ≡  ∃y1.∃w1.∃y2.((x = Abs_diagram ((y1)
∘(basic (e4⊗w1)∘(basic (e5)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e1⊗w1))∘(basic (e1⊗e1))∘(y2)))
∧((snd (count w1)) = 0))"


definition tanglerel_pull_rbnegpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_rbnegpos x y ≡  ∃y1.∃w1.∃y2.((x = Abs_diagram ((y1)
∘(basic (e5⊗w1)∘(basic (e4)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e1⊗w1))∘(basic (e1⊗e1))∘(y2)))
∧((snd (count w1)) = 0))"
  
(*null left top - denoted lt*)

definition tanglerel_pull_ltposneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_ltposneg x y ≡  ∃y1.∃z2.∃y2.((x = Abs_diagram ((y1)
∘(basic (e4)∘(basic (z2⊗e5)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e1))∘(basic (z2⊗e1⊗e1))∘(y2)))
∧(0 = (fst (count z2))))"


definition tanglerel_pull_ltnegpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_ltnegpos x y ≡  ∃y1.∃z2.∃y2.((x = Abs_diagram ((y1)
∘(basic (e5)∘(basic (z2⊗e4)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e1))∘(basic (z2⊗e1⊗e1))∘(y2)))
∧(0 = (fst (count z2))))"
  

(*null right top - denoted rt*)

definition tanglerel_pull_rtposneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_rtposneg x y ≡  ∃y1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (e4)∘(basic (e5⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e1))∘(basic (e1⊗e1⊗w2))∘(y2)))
∧(0 = (fst (count w2))))"


definition tanglerel_pull_rtnegpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_rtnegpos x y ≡  ∃y1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (e5)∘(basic (e4⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e1))∘(basic (e1⊗e1⊗w2))∘(y2)))
∧(0 = (fst (count w2))))"
  

(*tanglerel_pull definition*)
definition tanglerel_pull::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull x y ≡ ((tanglerel_pull_posneg x y) ∨ (tanglerel_pull_negpos x y)
∨ (tanglerel_pull_nullposneg x y) ∨ (tanglerel_pull_nullnegpos x y))
∨ (tanglerel_pull_rightposneg x y) ∨ (tanglerel_pull_rightnegpos x y)
∨ (tanglerel_pull_leftposneg x y) ∨ (tanglerel_pull_leftnegpos x y)
∨  (tanglerel_pull_toprightposneg x y) ∨ (tanglerel_pull_toprightnegpos x y)
∨ (tanglerel_pull_topleftposneg x y) ∨ (tanglerel_pull_topleftnegpos x y)
∨ (tanglerel_pull_botrightposneg x y) ∨ (tanglerel_pull_botrightnegpos x y)
∨ (tanglerel_pull_botleftposneg x y) ∨ (tanglerel_pull_botleftnegpos x y)
∨ (tanglerel_pull_rightcrossposneg x y) ∨ (tanglerel_pull_rightcrossnegpos x y)
∨ (tanglerel_pull_leftcrossposneg x y) ∨ (tanglerel_pull_leftcrossnegpos x y)
∨ (tanglerel_pull_rtposneg x y) ∨ (tanglerel_pull_rtnegpos x y)
∨ (tanglerel_pull_ltposneg x y) ∨ (tanglerel_pull_ltnegpos x y)
∨ (tanglerel_pull_rbposneg x y) ∨ (tanglerel_pull_rbnegpos x y)
∨ (tanglerel_pull_lbposneg x y) ∨ (tanglerel_pull_lbnegpos x y)
"                              

(*tanglerel_pull ends*)    
(*tanglerel_straighten*)

definition tanglerel_straighten_topdown::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_straighten_topdown x y ≡  ∃y1.∃z1.∃z2.∃w1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e1⊗e2⊗w1)∘(basic (z2⊗e3⊗e1⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗w1))∘(basic (z2⊗e1⊗w2))∘(y2))))
∧((snd (count z1)) = (fst (count z2)))
 ∧ ((snd (count w1)) = (fst (count w2)))"


definition tanglerel_straighten_downtop::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_straighten_downtop x y ≡  ∃y1.∃z1.∃z2.∃w1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e2⊗e1⊗w1)∘(basic (z2⊗e1⊗e3⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗w1))∘(basic (z2⊗e1⊗w2))∘(y2))))
∧((snd (count z1)) = (fst (count z2)))
 ∧ ((snd (count w1)) = (fst (count w2)))"


definition tanglerel_straighten_righttopdown::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_straighten_righttopdown x y ≡  ∃y1.∃w1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (e1⊗e2⊗w1)∘(basic (e3⊗e1⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗w1))∘(basic (e1⊗w2))∘(y2))))
 ∧ ((snd (count w1)) = (fst (count w2)))"


definition tanglerel_straighten_rightdowntop::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_straighten_rightdowntop x y ≡  ∃y1.∃w1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (e2⊗e1⊗w1)∘(basic (e1⊗e3⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗w1))∘(basic (e1⊗w2))∘(y2))))
 ∧ ((snd (count w1)) = (fst (count w2)))"



definition tanglerel_straighten_lefttopdown::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_straighten_lefttopdown x y ≡  ∃y1.∃z1.∃z2.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e3⊗e1)∘(basic (z2⊗e1⊗e2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1))∘(basic (z2⊗e1))∘(y2)))
∧((snd (count z1)) = (fst (count z2))))"



definition tanglerel_straighten_leftdowntop::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_straighten_leftdowntop x y ≡  ∃y1.∃z1.∃z2.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e2⊗e1)∘(basic (z2⊗e1⊗e3)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1))∘(basic (z2⊗e1))∘(y2))))
∧((snd (count z1)) = (fst (count z2)))"
(*definition straighten*)
definition tanglerel_straighten::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_straighten x y ≡ ((tanglerel_straighten_topdown x y) ∨ (tanglerel_straighten_downtop x y)
∨(tanglerel_straighten_righttopdown x y) ∨ (tanglerel_straighten_rightdowntop x y)
∨(tanglerel_straighten_lefttopdown x y) ∨ (tanglerel_straighten_leftdowntop x y))"

(*straighten ends*)
(*swing begins*)
definition tanglerel_swing_pos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_swing_pos x y ≡ ∃y1.∃z1.∃z2.∃z3.∃w1.∃w2.∃w3.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e4⊗e1⊗w1)∘(basic (z2⊗e1⊗e4⊗w2))∘(basic (z3⊗e4⊗e1⊗w3))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e4⊗w1)∘(basic (z2⊗e4⊗e1⊗w2))∘(basic (z3⊗e1⊗e4⊗w3))∘(y2))))
∧((snd (count z1)) = (fst (count z2)))∧((snd (count z2)) = (fst (count z3)))
 ∧ ((snd (count w1)) = (fst (count w2)))∧((snd (count w2)) = (fst (count w3))))"

definition tanglerel_swing_neg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_swing_neg x y ≡ ∃y1.∃z1.∃z2.∃z3.∃w1.∃w2.∃w3.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e5⊗e1⊗w1)∘(basic (z2⊗e1⊗e5⊗w2))∘(basic (z3⊗e5⊗e1⊗w3))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e5⊗w1)∘(basic (z2⊗e5⊗e1⊗w2))∘(basic (z3⊗e1⊗e5⊗w3))∘(y2)))))
∧((snd (count z1)) = (fst (count z2)))∧((snd (count z2)) = (fst (count z3)))
 ∧ ((snd (count w1)) = (fst (count w2)))∧((snd (count w2)) = (fst (count w3)))"

definition tanglerel_swing_rightpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_swing_rightpos x y ≡ ∃y1.∃w1.∃w2.∃w3.∃y2.((x = Abs_diagram ((y1)
∘(basic (e4⊗e1⊗w1)∘(basic (e1⊗e4⊗w2))∘(basic (e4⊗e1⊗w3))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e4⊗w1)∘(basic (e4⊗e1⊗w2))∘(basic (e1⊗e4⊗w3))∘(y2)))))
 ∧ ((snd (count w1)) = (fst (count w2)))∧((snd (count w2)) = (fst (count w3)))"



definition tanglerel_swing_rightneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_swing_rightneg x y ≡ ∃y1.∃w1.∃w2.∃w3.∃y2.((x = Abs_diagram ((y1)
∘(basic (e5⊗e1⊗w1)∘(basic (e1⊗e5⊗w2))∘(basic (e5⊗e1⊗w3))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e5⊗w1)∘(basic (e5⊗e1⊗w2))∘(basic (e1⊗e5⊗w3))∘(y2)))))
 ∧ ((snd (count w1)) = (fst (count w2)))∧((snd (count w2)) = (fst (count w3)))"

definition tanglerel_swing_leftpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_swing_leftpos x y ≡ ∃y1.∃z1.∃z2.∃z3.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e4⊗e1)∘(basic (z2⊗e1⊗e4))∘(basic (z3⊗e4⊗e1))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e4)∘(basic (z2⊗e4⊗e1))∘(basic (z3⊗e1⊗e4))∘(y2)))))
∧((snd (count z1)) = (fst (count z2)))∧((snd (count z2)) = (fst (count z3)))"



definition tanglerel_swing_leftneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_swing_leftneg x y ≡ ∃y1.∃z1.∃z2.∃z3.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e5⊗e1)∘(basic (z2⊗e1⊗e5))∘(basic (z3⊗e5⊗e1))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e5)∘(basic (z2⊗e5⊗e1))∘(basic (z3⊗e1⊗e5))∘(y2)))))
∧((snd (count z1)) = (fst (count z2)))∧((snd (count z2)) = (fst (count z3)))"

(*swing definition*)

definition tanglerel_swing::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_swing x y ≡ ((tanglerel_swing_pos x y) ∨ (tanglerel_swing_neg x y)
∨(tanglerel_swing_rightpos x y) ∨ (tanglerel_swing_rightneg x y)
∨(tanglerel_swing_leftpos x y) ∨ (tanglerel_swing_leftneg x y))"

(*swing ends*)
(* rotate moves*)

definition tanglerel_rotate_toppos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_rotate_toppos x y ≡  ∃y1.∃z1.∃z2.∃w1.∃w2.∃y2.((x = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e4⊗w1))∘(basic (z2⊗e3⊗e1⊗w2))∘(y2)))∧ ((y = Abs_diagram ((y1)
∘(basic (z1⊗e5⊗e1⊗w1)∘(basic (z2⊗e1⊗e3⊗w2)))∘(y2))))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = (fst (count w2))))"


definition tanglerel_rotate_topneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_rotate_topneg x y ≡  ∃y1.∃z1.∃z2.∃w1.∃w2.∃y2.((x = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e5⊗w1))∘(basic (z2⊗e3⊗e1⊗w2))∘(y2)))∧ ((y = Abs_diagram ((y1)
∘(basic (z1⊗e4⊗e1⊗w1)∘(basic (z2⊗e1⊗e3⊗w2)))∘(y2))))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = (fst (count w2))))"

definition tanglerel_rotate_downpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_rotate_downpos x y ≡  ∃y1.∃z1.∃z2.∃w1.∃w2.∃y2.((x = Abs_diagram
 ((y1)
∘(basic (z1⊗e3⊗e1⊗w1))∘(basic (z2⊗e1⊗e4⊗w2))∘(y2)))∧ ((y = Abs_diagram ((y1)
∘(basic (z1⊗e1⊗e3⊗w1)∘(basic (z2⊗e5⊗e1⊗w2)))∘(y2))))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = (fst (count w2))))"


definition tanglerel_rotate_downneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_rotate_downneg x y ≡  ∃y1.∃z1.∃z2.
∃w1.∃w2.∃y2.
((x = Abs_diagram ((y1)
∘(basic (z1⊗e3⊗e1⊗w1))∘(basic (z2⊗e1⊗e5⊗w2))∘(y2)))∧ ((y = Abs_diagram ((y1)
∘(basic (z1⊗e1⊗e3⊗w1)∘(basic (z2⊗e4⊗e1⊗w2)))∘(y2))))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = (fst (count w2))))"


definition tanglerel_rotate_righttoppos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_rotate_righttoppos x y ≡  ∃y1.∃w1.∃w2.∃y2.((x = Abs_diagram
 ((y1)
∘(basic (e1⊗e4⊗w1))∘(basic (e3⊗e1⊗w2))∘(y2)))∧ ((y = Abs_diagram ((y1)
∘(basic (e5⊗e1⊗w1)∘(basic (e1⊗e3⊗w2)))∘(y2))))
∧((snd (count w1)) = (fst (count w2))))"


definition tanglerel_rotate_righttopneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_rotate_righttopneg x y ≡  ∃y1.∃w1.∃w2.∃y2.((x = Abs_diagram
 ((y1)
∘(basic (e1⊗e5⊗w1))∘(basic (e3⊗e1⊗w2))∘(y2)))∧ ((y = Abs_diagram ((y1)
∘(basic (e4⊗e1⊗w1)∘(basic (e1⊗e3⊗w2)))∘(y2))))
∧((snd (count w1)) = (fst (count w2))))"

definition tanglerel_rotate_rightdownpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_rotate_rightdownpos x y ≡  ∃y1.∃w1.∃w2.∃y2.((x = Abs_diagram
 ((y1)
∘(basic (e3⊗e1⊗w1))∘(basic (e1⊗e4⊗w2))∘(y2)))∧ ((y = Abs_diagram ((y1)
∘(basic (e1⊗e3⊗w1)∘(basic (e5⊗e1⊗w2)))∘(y2))))
∧((snd (count w1)) = (fst (count w2))))"


definition tanglerel_rotate_rightdownneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_rotate_rightdownneg x y ≡  ∃y1.∃w1.∃w2.∃y2.
((x = Abs_diagram ((y1)
∘(basic (e3⊗e1⊗w1))∘(basic (e1⊗e5⊗w2))∘(y2)))∧ ((y = Abs_diagram ((y1)
∘(basic (e1⊗e3⊗w1)∘(basic (e4⊗e1⊗w2)))∘(y2))))
∧((snd (count w1)) = (fst (count w2))))"


definition tanglerel_rotate_lefttoppos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_rotate_lefttoppos x y ≡  ∃y1.∃z1.∃z2.∃y2.((x = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e4))∘(basic (z2⊗e3⊗e1))∘(y2)))∧ ((y = Abs_diagram ((y1)
∘(basic (z1⊗e5⊗e1)∘(basic (z2⊗e1⊗e3)))∘(y2))))
∧((snd (count z1)) = (fst (count z2))))"

definition tanglerel_rotate_lefttopneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_rotate_lefttopneg x y ≡  ∃y1.∃z1.∃z2.∃y2.((x = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e5))∘(basic (z2⊗e3⊗e1))∘(y2)))∧ ((y = Abs_diagram ((y1)
∘(basic (z1⊗e4⊗e1)∘(basic (z2⊗e1⊗e3)))∘(y2))))
∧((snd (count z1)) = (fst (count z2))))"

definition tanglerel_rotate_leftdownpos::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_rotate_leftdownpos x y ≡  ∃y1.∃z1.∃z2.∃y2.((x = Abs_diagram
 ((y1)
∘(basic (z1⊗e3⊗e1))∘(basic (z2⊗e1⊗e4))∘(y2)))∧ ((y = Abs_diagram ((y1)
∘(basic (z1⊗e1⊗e3)∘(basic (z2⊗e5⊗e1)))∘(y2))))
∧((snd (count z1)) = (fst (count z2))))"


definition tanglerel_rotate_leftdownneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_rotate_leftdownneg x y ≡  ∃y1.∃z1.∃z2.∃y2.
((x = Abs_diagram ((y1)
∘(basic (z1⊗e3⊗e1))∘(basic (z2⊗e1⊗e5))∘(y2)))∧ ((y = Abs_diagram ((y1)
∘(basic (z1⊗e1⊗e3)∘(basic (z2⊗e4⊗e1)))∘(y2))))
∧((snd (count z1)) = (fst (count z2))))"

(*rotate definition*)


definition tanglerel_rotate::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_rotate x y ≡ ((tanglerel_rotate_toppos x y) ∨ (tanglerel_rotate_topneg x y)
∨ (tanglerel_rotate_downpos x y) ∨ (tanglerel_rotate_downneg x y)
∨ (tanglerel_rotate_righttoppos x y) ∨ (tanglerel_rotate_righttopneg x y)
∨ (tanglerel_rotate_rightdownpos x y) ∨ (tanglerel_rotate_rightdownneg x y)
∨(tanglerel_rotate_lefttoppos x y) ∨ (tanglerel_rotate_lefttopneg x y)
∨ (tanglerel_rotate_leftdownpos x y) ∨ (tanglerel_rotate_leftdownneg x y))"

(*rotate ends*)
(*stranded operations begin*)

primrec brickstrand::"brick ⇒ bool"
where
"brickstrand a1 = True"|
"brickstrand a2 = False"|
"brickstrand a3 = False"|
"brickstrand a4 = False"|
"brickstrand a5 = False"

primrec strands::"block ⇒ bool"
where
"strands (cement x) = brickstrand x"|
"strands (x#ys) = (if (x= a1) then (strands ys) else False)"


lemma strands_test: "strands (a1#a2#a1#e1) = False" using e1_def strands_def brickstrand_def
compose_def by auto
(*
lemma strands_test: "strands (e1⊗e2⊗e1⊗e1) = False" using e1_def e2_def strands_def brickstrand_def
compose_def by auto
*)

(*Compress -  Compress has two levels of equivalences. It is a composition of Compress_null, compbelow
and compabove. compbelow and compabove are further written as disjunction of many other relations.
Compbelow refers to when the bottom row is extended or compressed. Compabove*)

definition tanglerel_compress_null::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compress_null x y ≡  ∃y2.∃A.∃B.((x = Abs_diagram
 ((A)∘(basic B)∘(y2)))∧(y = Abs_diagram ((A)∘(y2)))
∧ (strands B) ∧ ((snd (wall_count A))>0))"

(*compress below- abbreviated as compbelow*)
definition tanglerel_compbelow_down::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_down x y ≡  ∃z1.∃z2.∃w1.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((basic (z1⊗A⊗w1))∘(basic (z2⊗B⊗w2))∘(y2)))∧ ((y = Abs_diagram (
(basic (z1⊗w1)∘(basic (z2⊗A⊗w2)))∘(y2))))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = (fst (count w2)))
∧(strands B))"


definition tanglerel_compbelow_center::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_center x y ≡ ∃y1.∃z1.∃z2.∃w1.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A⊗w1))∘(basic (z2⊗B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1⊗w1))∘(basic (z2⊗A⊗w2))∘(y2)))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = (fst (count w2)))
∧((fst (count A)) = 0)
∧(strands B))"

(*three at a time- botright*)
definition tanglerel_compbelow_botright::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_botright x y ≡ ∃z2.∃w1.∃w2.∃y2.∃A.∃B.((x = Abs_diagram (
(basic (A⊗w1))∘(basic (z2⊗B⊗w2))∘(y2)))∧ ((y = Abs_diagram (
(basic (w1)∘(basic (z2⊗A⊗w2)))∘(y2))))
∧(0 = (fst (count z2)))
∧((snd (count w1)) = (fst (count w2)))
∧(strands B))"


definition tanglerel_compbelow_botleft::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_botleft x y ≡  ∃z1.∃z2.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((basic (z1⊗A))∘(basic (z2⊗B⊗w2))∘(y2)))∧ ((y = Abs_diagram (
(basic (z1)∘(basic (z2⊗A⊗w2)))∘(y2))))
∧((snd (count z1)) = (fst (count z2)))
∧(0 = (fst (count w2)))
∧(strands B))"


definition tanglerel_compbelow_centerbotright::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_centerbotright x y ≡ ∃y1.∃z2.∃w1.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (A⊗w1))∘(basic (z2⊗B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (w1))∘(basic (z2⊗A⊗w2))∘(y2)))
∧(0 = (fst (count z2)))
∧((snd (count w1)) = (fst (count w2)))
∧((fst (count A)) = 0)
∧(strands B))"


definition tanglerel_compbelow_centerbotleft::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_centerbotleft x y ≡ ∃y1.∃z1.∃z2.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A))∘(basic (z2⊗B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1))∘(basic (z2⊗A⊗w2))∘(y2)))
∧((snd (count z1)) = (fst (count z2)))
∧(0 = (fst (count w2)))
∧((fst (count A)) = 0)
∧(strands B))"


definition tanglerel_compbelow_centertopright::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_centertopright x y ≡ ∃y1.∃z1.∃w1.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A))∘(basic (B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1⊗w1))∘(basic (A⊗w2))∘(y2)))
∧((snd (count z1)) = 0)
∧((snd (count w1)) = (fst (count w2)))
∧((fst (count A)) = 0)
∧(strands B))"


definition tanglerel_compbelow_centertopleft::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_centertopleft x y ≡ ∃y1.∃z1.∃z2.∃w1.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A⊗w1))∘(basic (z2⊗B))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1⊗w1))∘(basic (z2⊗A))∘(y2)))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = 0)
∧((fst (count A)) = 0)
∧(strands B))"

(*two at a time*)

definition tanglerel_compbelow_right::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_right x y ≡  ∃w1.∃w2.∃y2.∃A.∃B.((x= Abs_diagram
 ((basic (A⊗w1))∘(basic (B⊗w2))∘(y2)))∧ (y = Abs_diagram (
(basic w1)∘(basic (B⊗w2))∘(y2)))
∧((snd (count w1)) = (fst (count w2)))
∧ (strands B)
∧ ((fst (count A)) = 0))"


definition tanglerel_compbelow_left::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_left x y ≡  ∃z1.∃z2.∃A.∃B.∃y2.((x = Abs_diagram
 ((basic (z1⊗A))∘(basic (z2⊗B))∘(y2)))∧ ((y = Abs_diagram (
(basic (z1)∘(basic (z2⊗A)))∘(y2))))
∧((snd (count z1)) = (fst (count z2)))
∧(strands B))"


definition tanglerel_compbelow_bottom::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_bottom x y ≡  ∃z2.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((basic (A))∘(basic (z2⊗B⊗w2))∘(y2)))∧ ((y = Abs_diagram (
(basic (z2⊗A⊗w2))∘(y2))))
∧(0 = (fst (count z2)))
∧(0 = (fst (count w2)))
∧(strands B))"


definition tanglerel_compbelow_centerright::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_centerright x y ≡ ∃y1.∃w1.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (A⊗w1))∘(basic (B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (w1))∘(basic (A⊗w2))∘(y2)))
∧((snd (count w1)) = (fst (count w2)))
∧((fst (count A)) = 0)
∧(strands B))"


definition tanglerel_compbelow_centerleft::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_centerleft x y ≡ ∃y1.∃z1.∃z2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A))∘(basic (z2⊗B))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1))∘(basic (z2⊗A))∘(y2)))
∧((snd (count z1)) = (fst (count z2)))
∧((fst (count A)) = 0)
∧(strands B))"


definition tanglerel_compbelow_centerbottom::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_centerbottom x y ≡ ∃y1.∃z2.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (A))∘(basic (z2⊗B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘(basic (z2⊗A⊗w2))∘(y2)))
∧(0 = (fst (count z2)))
∧(0 = (fst (count w2)))
∧((fst (count A)) = 0)
∧(strands B))"


definition tanglerel_compbelow_centertop::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_centertop x y ≡ ∃y1.∃z1.∃w1.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A⊗w1))∘(basic (B))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1⊗w1))∘(basic (A))∘(y2)))
∧((snd (count z1)) = 0)
∧((snd (count w1)) = 0)
∧((fst (count A)) = 0)
∧(strands B))"


definition tanglerel_compbelow_centerrightcross::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_centerrightcross x y ≡ ∃y1.∃z1.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A))∘(basic (B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1))∘(basic (A⊗w2))∘(y2)))
∧((snd (count z1)) = 0)
∧(0 = (fst (count w2)))
∧((fst (count 
A)) = 0)
∧(strands B))"


definition tanglerel_compbelow_centerleftcross::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_centerleftcross x y ≡ ∃y1.∃z2.∃w1.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (A⊗w1))∘(basic (z2⊗B))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (w1))∘(basic (z2⊗A))∘(y2)))
∧(0 = (fst (count z2)))
∧((snd (count w1)) = 0)
∧((fst (count A)) = 0)
∧(strands B))"

(*one at a time- abbreviated notation is used here. For instance- lb-left bottom exists*)

definition tanglerel_compbelow_lt::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_lt x y ≡  ∃z2.∃A.∃B.∃y2.((x = Abs_diagram
 ((basic (A))∘(basic (z2⊗B))∘(y2)))∧ ((y = Abs_diagram (
(basic (z2⊗A))∘(y2))))
∧(0 = (fst (count z2)))
∧(strands B))"


definition tanglerel_compbelow_rt::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_rt x y ≡  ∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((basic (A))∘(basic (B⊗w2))∘(y2)))∧ ((y = Abs_diagram (
(basic (A⊗w2))∘(y2))))
∧(0 = (fst (count w2)))
∧(strands B))"

(*center abbreviated one at a time*)

definition tanglerel_compbelow_centerlb::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_centerlb x y ≡ ∃y1.∃z1.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A))∘(basic (B))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1))∘(basic (A))∘(y2)))
∧((snd (count z1)) = 0)
∧((fst (count A)) = 0)
∧(strands B))"


definition tanglerel_compbelow_centerrb::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_centerrb x y ≡ ∃y1.∃w1.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (A⊗w1))∘(basic (B))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (w1))∘(basic (A))∘(y2)))
∧((snd (count w1)) = 0)
∧((fst (count A)) = 0)
∧(strands B))"


definition tanglerel_compbelow_centerlt::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_centerlt x y ≡ ∃y1.∃z2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (A))∘(basic (z2⊗B))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z2⊗A))∘(y2)))
∧(0 = (fst (count z2)))
∧((fst (count A)) = 0)
∧(strands B))"


definition tanglerel_compbelow_centerrt::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow_centerrt x y ≡ ∃y1.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (A))∘(basic (B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘(basic (A⊗w2))∘(y2)))
∧(0 = (fst (count w2)))
∧((fst (count A)) = 0)
∧(strands B))"
(*comp below definition*)

(*compbelow definition*)
definition tanglerel_compbelow::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compbelow x y ≡ (tanglerel_compbelow_down x y) ∨ (tanglerel_compbelow_center x y) 
∨ (tanglerel_compbelow_botright x y) ∨ (tanglerel_compbelow_botleft x y ) 
∨ (tanglerel_compbelow_centerbotleft x y) ∨ (tanglerel_compbelow_centerbotright x y)
∨ (tanglerel_compbelow_centertopright x y) ∨ (tanglerel_compbelow_centertopleft x y)
∨ (tanglerel_compbelow_right x y) ∨ (tanglerel_compbelow_left x y) ∨ (tanglerel_compbelow_bottom x y)
∨ (tanglerel_compbelow_centerleft x y) ∨ (tanglerel_compbelow_centerright x y)
∨ (tanglerel_compbelow_centerbottom x y) ∨ (tanglerel_compbelow_centertop x y)
∨(tanglerel_compbelow_centerrightcross x y) ∨ (tanglerel_compbelow_centerleftcross x y)
∨ (tanglerel_compbelow_lt x y) ∨ (tanglerel_compbelow_rt x y) 
∨ (tanglerel_compbelow_centerlb x y) ∨ (tanglerel_compbelow_centerrb x y)
∨ (tanglerel_compbelow_centerlt x y) ∨ (tanglerel_compbelow_centerrt x y)
"
(*comp above*)
definition tanglerel_compabove_up::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_up x y ≡  ∃z1.∃z2.∃w1.∃w2.∃A.∃B.∃y1.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A⊗w1))∘(basic (z2⊗B⊗w2))))∧ ((y = Abs_diagram ((y1)∘
(basic (z1⊗B⊗w1)∘(basic (z2⊗w2))))))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = (fst (count w2)))
∧(strands A))"


definition tanglerel_compabove_center::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_center x y ≡ ∃y1.∃z1.∃z2.∃w1.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A⊗w1))∘(basic (z2⊗B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1⊗B⊗w1))∘(basic (z2⊗w2))∘(y2)))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = (fst (count w2)))
∧((snd (count B)) = 0)
∧(strands A))"

(*three at a time*)
definition tanglerel_compabove_bottomright::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_bottomright x y ≡  ∃z2.∃w1.∃w2.∃A.∃B.∃y1.((x = Abs_diagram
 ((y1)∘(basic (A⊗w1))∘(basic (z2⊗B⊗w2))))∧ ((y = Abs_diagram (
(basic (B⊗w1)∘(basic (z2⊗w2))))))
∧(0 = (fst (count z2)))
∧((snd (count w1)) = (fst (count w2)))
∧(strands A))"


definition tanglerel_compabove_bottomleft::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_bottomleft x y ≡  ∃z1.∃z2.∃w2.∃A.∃B.∃y1.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A))∘(basic (z2⊗B⊗w2))))∧ ((y = Abs_diagram (
(y1)∘(basic (z1⊗B)∘(basic (z2⊗w2))))))
∧((snd (count z1)) = (fst (count z2)))
∧(0 = (fst (count w2)))
∧(strands A))"


definition tanglerel_compabove_topright::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_topright x y ≡  ∃z1.∃w1.∃w2.∃A.∃B.∃y1.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A⊗w1))∘(basic (B⊗w2))))∧ ((y = Abs_diagram (
(y1)∘(basic (z1⊗B⊗w1)∘(basic (w2))))))
∧((snd (count z1)) = 0)
∧((snd (count w1)) = (fst (count w2)))
∧(strands A))"


definition tanglerel_compabove_topleft::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_topleft x y ≡  ∃z1.∃z2.∃w1.∃A.∃B.∃y1.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A⊗w1))∘(basic (z2⊗B))))∧ ((y = Abs_diagram (
(y1)∘(basic (z1⊗B⊗w1)∘(basic (z2))))))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = 0)
∧(strands A))"


definition tanglerel_compabove_centerbottomright::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_centerbottomright x y ≡ ∃y1.∃z2.∃w1.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (A⊗w1))∘(basic (z2⊗B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (B⊗w1))∘(basic (z2⊗w2))∘(y2)))
∧(0 = (fst (count z2)))
∧((snd (count w1)) = (fst (count w2)))
∧((snd (count B)) = 0)
∧(strands A))"


definition tanglerel_compabove_centerbottomleft::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_centerbottomleft x y ≡ ∃y1.∃z1.∃z2.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A))∘(basic (z2⊗B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1⊗B))∘(basic (z2⊗w2))∘(y2)))
∧((snd (count z1)) = (fst (count z2)))
∧(0 = (fst (count w2)))
∧((snd (count B)) = 0)
∧(strands A))"


definition tanglerel_compabove_centertopright::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_centertopright x y ≡ ∃y1.∃z1.∃z2.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A))∘(basic (z2⊗B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1⊗B))∘(basic (z2⊗w2))∘(y2)))
∧((snd (count z1)) = (fst (count z2)))
∧(0 = (fst (count w2)))
∧((snd (count B)) = 0)
∧(strands A))"


definition tanglerel_compabove_centertopleft::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_centertopleft x y ≡ ∃y1.∃z1.∃z2.∃w1.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A⊗w1))∘(basic (z2⊗B))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1⊗B⊗w1))∘(basic (z2))∘(y2)))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = 0)
∧((snd (count B)) = 0)
∧(strands A))"
(*two at a time*)

definition tanglerel_compabove_right::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_right x y ≡  ∃w1.∃w2.∃A.∃B.∃y1.((x = Abs_diagram
 ((y1)∘(basic (A⊗w1))∘(basic (B⊗w2))))∧ ((y = Abs_diagram (
(y1)∘(basic (B⊗w1)∘(basic (w2))))))
∧((snd (count w1)) = (fst (count w2)))
∧(strands A))"


definition tanglerel_compabove_left::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_left x y ≡  ∃z1.∃z2.∃A.∃B.∃y1.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A))∘(basic (z2⊗B))))∧ ((y = Abs_diagram (
(y1)∘(basic (z1⊗B)∘(basic (z2))))))
∧((snd (count z1)) = (fst (count z2)))
∧(strands A))"


definition tanglerel_compabove_top::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_top x y ≡  ∃z1.∃z2.∃w1.∃w2.∃A.∃B.∃y1.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A⊗w1))∘(basic (B))))∧ ((y = Abs_diagram (
(y1)∘(basic (z1⊗B⊗w1)))))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = (fst (count w2)))
∧(strands A))"

(*two at a time-center*)

definition tanglerel_compabove_centerright::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_centerright x y ≡ ∃y1.∃w1.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (A⊗w1))∘(basic (B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (A⊗w1))∘(basic (w2))∘(y2)))
∧((snd (count w1)) = (fst (count w2)))
∧((snd (count B)) = 0)
∧(strands A))"

definition tanglerel_compabove_centerleft::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_centerleft x y ≡ ∃y1.∃z1.∃z2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A))∘(basic (z2⊗B))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1⊗B))∘(basic (z2))∘(y2)))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count B)) = 0)
∧(strands A))"


definition tanglerel_compabove_centertop::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_centertop x y ≡ ∃y1.∃z1.∃w1.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A⊗w1))∘(basic (B))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1⊗B⊗w1))∘(y2)))
∧((snd (count z1)) = 0)
∧((snd (count w1)) = 0)
∧((snd (count B)) = 0)
∧(strands A))"


definition tanglerel_compabove_centerbottom::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_centerbottom x y ≡ ∃y1.∃z2.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (A))∘(basic (z2⊗B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (B))∘(basic (z2⊗w2))∘(y2)))
∧(0 = (fst (count z2)))
∧((fst (count w2)) = 0)
∧((snd (count B)) = 0)
∧(strands A))"


definition tanglerel_compabove_centerrightcross::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_centerrightcross x y ≡ ∃y1.∃z2.∃w1.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (A⊗w1))∘(basic (z2⊗B))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (B⊗w1))∘(basic (z2))∘(y2)))
∧(0 = (fst (count z2)))
∧((snd (count w1)) = 0)
∧((snd (count B)) = 0)
∧(strands A))"

definition tanglerel_compabove_centerleftcross::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_centerleftcross x y ≡ ∃y1.∃z1.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A))∘(basic (B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1⊗B))∘(basic (w2))∘(y2)))
∧((snd (count z1)) = 0)
∧(0 = (fst (count w2)))
∧((snd (count B)) = 0)
∧(strands A))"
(*one at a time- abbreviated notion- for instance lb- left bottom block is present*)

definition tanglerel_compabove_lb::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_lb x y ≡  ∃z1.∃A.∃B.∃y1.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A))∘(basic (B))))∧ (y = Abs_diagram 
((y1)∘(basic (z1⊗B))))
∧((snd (count z1)) = 0)
∧(strands A))"

definition tanglerel_compabove_rb::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_rb x y ≡  ∃w1.∃A.∃B.∃y1.((x = Abs_diagram
 ((y1)∘(basic (A⊗w1))∘(basic (B))))∧ ((y = Abs_diagram ((y1)∘
(basic (B⊗w1)))))
∧((snd (count w1)) = 0)
∧(strands A))"

(*center- on at a time*)

definition tanglerel_compabove_centerlb::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_centerlb x y ≡ ∃y1.∃z1.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A))∘(basic (B))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1⊗B))∘(y2)))
∧((snd (count z1)) = 0)
∧((snd (count B)) = 0)
∧(strands A))"


definition tanglerel_compabove_centerrb::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_centerrb x y ≡ ∃y1.∃w1.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (A⊗w1))∘(basic (B))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (B⊗w1))∘(y2)))
∧((snd (count w1)) = 0)
∧((snd (count B)) = 0)
∧(strands A))"


definition tanglerel_compabove_centerlt::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_centerlt x y ≡ ∃y1.∃z1.∃z2.∃w1.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗A⊗w1))∘(basic (z2⊗B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (z1⊗B⊗w1))∘(basic (z2⊗w2))∘(y2)))
∧((snd (count z1)) = (fst (count z2)))
∧((snd (count w1)) = (fst (count w2)))
∧((snd (count B)) = 0)
∧(strands A))"



definition tanglerel_compabove_centerrt::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove_centerrt x y ≡ ∃y1.∃w2.∃A.∃B.∃y2.((x = Abs_diagram
 ((y1)∘(basic (A))∘(basic (B⊗w2))∘(y2)))∧ (y = Abs_diagram ((y1)∘
(basic (B))∘(basic (w2))∘(y2)))
∧((fst (count w2)) = 0)
∧((snd (count B)) = 0)
∧(strands A))"

(*compabove definition*)

(*compbelow definition*)
definition tanglerel_compabove::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_compabove x y ≡ (tanglerel_compabove_up x y)∨(tanglerel_compabove_center x y) 
∨ (tanglerel_compabove_bottomright x y) ∨ (tanglerel_compabove_bottomleft x y ) 
∨ (tanglerel_compabove_topright x y) ∨ (tanglerel_compabove_topleft x y) 
∨ (tanglerel_compabove_centerbottomleft x y) ∨ (tanglerel_compabove_centerbottomright x y)
∨ (tanglerel_compabove_centertopright x y) ∨ (tanglerel_compabove_centertopleft x y)
∨ (tanglerel_compabove_right x y) ∨ (tanglerel_compabove_left x y) ∨ (tanglerel_compabove_top x y)
∨ (tanglerel_compabove_centerleft x y) ∨ (tanglerel_compabove_centerright x y)
∨ (tanglerel_compabove_centerbottom x y) ∨ (tanglerel_compabove_centertop x y)
∨(tanglerel_compabove_centerrightcross x y) ∨ (tanglerel_compabove_centerleftcross x y)
∨ (tanglerel_compabove_lb x y) ∨ (tanglerel_compabove_rb x y) 
∨ (tanglerel_compabove_centerlb x y) ∨ (tanglerel_compabove_centerrb x y)
∨ (tanglerel_compabove_centerlt x y) ∨ (tanglerel_compabove_centerrt x y)"

(*definition compess*)
definition tanglerel_compress::"diagram ⇒ diagram => bool"
where
"tanglerel_compress x y ≡ (tanglerel_compress_null x y) ∨ (tanglerel_compbelow x y) 
∨ (tanglerel_compabove x y)"

(*slide*)
definition tanglerel_slide_left::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_slide_left x y ≡ ∃y1.∃y2.∃w1.∃w2.∃A.∃B.∃C.
((x = Abs_diagram((y1)∘(basic (A⊗w1))∘(basic (B⊗w2))∘(y2))) ∧
(y = Abs_diagram((y1)∘(basic (C⊗w1))∘(basic (A⊗w2))∘(y2)))
∧ ((snd (count w1)) = (fst (count w2)))
∧ (strands B)
∧ (strands C))"

definition tanglerel_slide_right::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_slide_right x y ≡ ∃y1.∃y2.∃z1.∃z2.∃A.∃B.∃C.
((x = Abs_diagram((y1)∘(basic (z1⊗A))∘(basic (z2⊗B))∘(y2))) ∧
(y = Abs_diagram((y1)∘(basic (z1⊗C))∘(basic (z2⊗A))∘(y2)))
∧ ((snd (count z1)) = (fst (count z2)))
∧ (strands B)
∧ (strands C))"

definition tanglerel_slide::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_slide x y ≡ ((tanglerel_slide_left x y) ∨ (tanglerel_slide_right x y))"

(*tanglerel_definition*)

definition tanglerel::"diagram =>diagram⇒bool"
where
"tanglerel x y = ((tanglerel_uncross x y) ∨ (tanglerel_pull x y) ∨ (tanglerel_straighten x y) 
∨(tanglerel_swing x y)∨(tanglerel_rotate x y) ∨ (tanglerel_compress x y) ∨ (tanglerel_slide x y)
∨  (tanglerel_uncross y x) ∨ (tanglerel_pull y x) ∨ (tanglerel_straighten y x) 
∨(tanglerel_swing y x)∨(tanglerel_rotate y x) ∨ (tanglerel_compress y x) ∨ (tanglerel_slide y x))
"
(* lemmas for proving that equivalence is well defined*)
lemma tanglerel_symp: "symp tanglerel" unfolding tanglerel_def symp_def by auto

(*find_theorems"rtranclp"*)
 
definition tanglerel_equiv::"diagram⇒diagram⇒bool"
where
"(tanglerel_equiv) = (tanglerel)^**" 
 
lemma reflective: "tanglerel_equiv x x" unfolding tanglerel_equiv_def by simp

lemma tangle_symmetry:"symp tanglerel_equiv" using tanglerel_symp symmetry3 
by (metis (full_types) tanglerel_equiv_def)

(*tangles upto equivalence are well defined*)
(*Tangle- Definition and the proof of being well defined*)

quotient_type Tangle = "diagram" / "tanglerel_equiv"
 morphisms Rep_tangles Abs_tangles
proof (rule equivpI)
show "reflp tanglerel_equiv" unfolding reflp_def reflective by (metis reflective)
show "symp tanglerel_equiv" using tangle_symmetry by auto
show "transp tanglerel_equiv" unfolding transp_def tanglerel_equiv_def rtranclp_trans by auto  
qed
(*additional Tanglerel*)

(*proof zone*)
lemma strand_makestrand: " strands (makestrand n)" 
apply(induct_tac n)
apply(auto)
apply(simp add:e1_def)
done

lemma test_00: "(makestrand (n+1)) = a1#(makestrand n)" by auto

lemma test_0: "(makestrand (n+1)) = e1⊗(makestrand n)" using e1_def test_00 append_Nil by metis

type_synonym convert = "block => nat"

definition fstcount:: convert  where "(fstcount x) = (nat (abs ((fst (count x)))))"

definition sndcount:: convert  where "(sndcount x) = (nat (snd (count x)))"


lemma makestrand_fstequality:"(fst (count (makestrand n))) = (int n)+1" 
apply (induct_tac n)
apply(auto)
apply(simp add: e1_def)
done

lemma makestrand_sndequality:"(snd (count (makestrand n))) = (int n)+1" 
apply (induct_tac n)
apply(auto)
apply(simp add: e1_def)
done

lemma makestrand_fstsndequality:"(fst (count (makestrand n))) = (snd (count (makestrand n)))" 
apply (induct_tac n)
apply(auto simp add:e1_def)
done

lemma nat_int:" ((int n)≥ 0)" by auto

lemma makestrands_positivelength:"(fst (count (makestrand n)))>0" using  nat_int makestrand_fstequality
by auto

lemma strands_even: "((a = Abs_diagram (x ∘(basic y)∘ z)) ∧ (strands y)) ⟹ (length y) > 1"
proof-
oops


theorem metaequivalence_left: 
assumes "(snd (count y1))>1" and "(z4 = makestrand (nat ((snd (count y1)) + (-2))+1))"
and "w4 = makestrand  (nat ((snd (count y1)) + (-2)))"
shows "tanglerel_equiv (Abs_diagram ((x1)∘(basic (e2⊗y1))∘(basic (e1⊗e1⊗z4))∘(basic (e1⊗e3⊗w4))∘z1))
             (Abs_diagram (x1 ∘ basic y1 ∘z1))" 
proof-
(*
assume A: "snd (count y1) >1" 
*)
let ?k = " (nat ((snd (count y1))+ (-2) ))" 

have C: " (z4 = makestrand (?k+1))" using assms by auto
let ?x2 = "x1 ∘ (basic y1)"


have preliminary_result1:"((snd (count y1))+(-1))>0" using assms by auto
have preliminary_result2:"((snd (count y1))+(-2))≥0" using assms by auto
have preliminary_result3: "strands z4" using C strand_makestrand by auto

have subresult0: "snd (wall_count ?x2) = snd (wall_count (basic y1))" 
           using wall_count_compose 
             by auto
have subresult1: "... = snd (count y1)" using wall_count_compose 
            by auto
have subresult2: "snd (wall_count ?x2) > 0"
            using subresult1 assms less_trans subresult0 zero_less_one 
            by auto
have subresult3: "fst (count (z4)) = fst (count (makestrand (?k+1)))"  
            using C makestrand_fstequality
            by auto
have subresult4: "fst (count (makestrand (?k+1))) = int(?k+1)+1"  
            using makestrand_fstequality
            by auto
have subresult5:"fst (count (z4)) =  int(?k)+2" 
           using subresult3 subresult4 
           by auto
have subresult6: "int (nat (snd (count y1) + -2)) = (snd (count y1)) + -2" 
           using int_nat_eq preliminary_result2
           by auto
have subresult7: "snd (count y1) = int(?k)+2" 
           using subresult6 
           by auto
have subresult8: "fst (count (z4)) = (snd (count y1))" 
           using subresult5 subresult7 
           by auto
have subresult_compress1: 
"(tanglerel_compress_null ((Abs_diagram (?x2∘(basic z4)∘z1))) (Abs_diagram (?x2∘z1)))" 
           using tanglerel_compress_null_def
           preliminary_result3 subresult0 subresult2
             by metis
have subresult_equiv1: 
"(tanglerel_equiv ((Abs_diagram (?x2∘(basic z4)∘z1))) (Abs_diagram (?x2∘z1)))" 
           using r_into_rtranclp subresult_compress1 tanglerel_equiv_def tanglerel_def  
           tanglerel_compress_def
                     by (metis)
have subresult_compress2: 
"(tanglerel_compress_null ((Abs_diagram ((?x2 ∘ basic z4)∘(basic z4)∘z1))) 
                            (Abs_diagram ((?x2 ∘ basic z4)∘z1)))" 
               using tanglerel_compress_null_def preliminary_result3 subresult0 subresult2   
               compose_leftassociativity
                    by (metis)
have subresult_equiv2: 
"(tanglerel_equiv ((Abs_diagram ((?x2 ∘ basic z4)∘(basic z4)∘z1))) 
                            (Abs_diagram ((?x2 ∘ basic z4)∘z1)))" 
               using tanglerel_compress_def tanglerel_def tanglerel_equiv_def
               r_into_rtranclp subresult_compress2   
                    by (metis)
have subresult_equiv3: 
"tanglerel_equiv ((Abs_diagram ((?x2 ∘ basic z4)∘(basic z4)∘z1))) 
                            (Abs_diagram ((?x2 ∘z1)))" 
               using tanglerel_equiv_def rtranclp_trans subresult_equiv1 subresult_equiv2 
               compose_leftassociativity
                            by (metis) 
have step1: 
"tanglerel_equiv (Abs_diagram (x1 ∘ basic y1 ∘ basic z4∘basic z4∘z1)) 
                            (Abs_diagram (x1 ∘ basic y1 ∘z1))" 
               using compose_leftassociativity subresult_equiv3 
               by auto
(*step 2 - inducing cusp*)

have w_subst: "w4 = (makestrand ?k)" using assms by auto

have step2_subresult0: "(makestrand (?k+1)) = (e1⊗(makestrand ?k))" 
 apply(simp add: e1_def)
 done

have step2_subresult1:"z4 = e1⊗(makestrand ?k)" using C step2_subresult0 by auto

have step2_subresult2: "(Abs_diagram (?x2 ∘ (basic z4) ∘(basic z4)∘z1)) =
(Abs_diagram (?x2  ∘ (basic (e1⊗w4))∘ (basic (e1 ⊗w4))∘z1))" 
                        using w_subst step2_subresult1 by auto

have step2_subresult3: "(snd (count w4)) = (fst (count w4))" using makestrand_fstsndequality w_subst
by auto

let ?x = "(Abs_diagram (?x2 ∘(basic (e2⊗e1⊗w4))∘(basic (e1⊗e3⊗w4))∘z1))"
let ?y = "(Abs_diagram (?x2 ∘(basic (e1⊗w4))∘(basic (e1⊗w4))∘z1))"

have step2_subresult4:
"∃y1.∃y2.∃w1.∃w2.(?x = Abs_diagram (y1 ∘ (basic (e2 ⊗ e1 ⊗ w1)) ∘ (basic (e1 ⊗ e3 ⊗ w2)) ∘ y2))"
  using exI by auto
 
have step2_subresult5:
"∃y1.∃y2.∃w1.∃w2.(?y = Abs_diagram (y1 ∘ (basic (e1 ⊗ w1)) ∘ (basic (e1 ⊗ w2)) ∘ y2))"
 using exI by auto

have step2_subresult6: 
" (∃y1.∃w1.∃w2.∃y2.((?x = Abs_diagram ((y1)
∘(basic (e2⊗e1⊗w1)∘(basic (e1⊗e3⊗w2)))∘(y2)))∧(?y = Abs_diagram
 ((y1)
∘(basic (e1⊗w1))∘(basic (e1⊗w2))∘(y2))))
 ∧ ((snd (count w1)) = (fst (count w2))))"
using  step2_subresult3 exI by auto

have step2_subresult7:
" tanglerel_straighten_rightdowntop ?x ?y"
using tanglerel_straighten_rightdowntop_def step2_subresult6 by auto

have step2_subresult8:"tanglerel ?x ?y" 
using tanglerel_def tanglerel_straighten_def step2_subresult7 by auto

have step2_subresult9: "tanglerel (Abs_diagram ((?x2) ∘(basic (e2⊗e1⊗w4))∘(basic (e1⊗e3⊗w4))∘z1)) 
              (Abs_diagram ((?x2) ∘(basic (e1⊗w4))∘(basic (e1⊗w4))∘z1))"
               using step2_subresult8 by auto 

have step2_equiv1: "tanglerel_equiv (Abs_diagram (x1∘basic y1∘(basic (e2⊗e1⊗w4))∘(basic (e1⊗e3⊗w4))∘z1)) 
              (Abs_diagram (x1∘basic y1 ∘(basic (e1⊗w4))∘(basic (e1⊗w4))∘z1))"
               using step2_subresult9 compose_leftassociativity r_into_rtranclp 
               tanglerel_equiv_def
                     by metis

have step2: "tanglerel_equiv (Abs_diagram (x1∘basic y1∘(basic (e2⊗z4))∘(basic (e1⊗e3⊗w4))∘z1)) 
              (Abs_diagram (x1∘basic y1 ∘(basic z4)∘(basic (z4))∘z1))"
               using  step2_subresult9 compose_leftassociativity r_into_rtranclp 
               tanglerel_equiv_def step2_subresult1 w_subst
                     by (metis)
(*step 3*)

have step3_preliminary1: "fst (count (v⊗w)) = fst (count (a2#(v⊗w)))" using count_def brickcount_def
by auto
have step3_preliminary2 : 
"count ((a2)#(e2⊗w4)) = (fst (brickcount (a2)) + fst (count (e2⊗w4)),
 snd (brickcount (a2)) + snd (count (e2⊗w4)))"
using count_def e2_def by auto
have step3_preliminary3: 
"(e2⊗(e1⊗w4)) = a2#(e1⊗w4)" using e2_def append_Nil by metis
have step3_subresult0 : 
"fst (count ((a2)#(e2⊗w4))) =  (fst (brickcount (a2)) + fst (count (e2⊗w4)))"
using count_def e2_def brickcount_def by auto
have step3_preliminary4 : 
"(fst (brickcount (a2)) + fst (count (e2⊗w4))) = fst (count (e2⊗w4))"
using brickcount_def by auto

have step3_preliminary5:
"fst (count (a2#(e2⊗w4))) =  fst (count (e2⊗w4))"
using  step3_preliminary4 step3_subresult0 by auto

have step3_preliminary6:
"fst (count ((e2)⊗(e2⊗w4))) =  fst (count (a2#(e2⊗w4)))"
using step3_preliminary3 
by (metis Tangles_update.append.append_Nil e2_def)

have step3_preliminary7:
"fst (count ((e2)⊗(e2⊗w4))) =  fst (count (e2⊗w4))"
using step3_preliminary5  step3_preliminary6 
by auto

have step3_subresult1 :"fst (wall_count (basic (e2⊗e1⊗w4))) = fst (wall_count (basic (e1⊗w4))) " 
using wall_count_def step3_preliminary7
 by (metis Tangles_update.append.append_Nil add_diff_cancel 
comm_monoid_add_class.add.left_neutral count.simps(2) e2_def fst_conv wall_count.simps(1))

have step3_subresult2: "fst (wall_count (basic (e1⊗w4))) = snd (count y1)" 
               using w_subst step2_subresult1 subresult8 by auto
have step3_subresult3: "fst (wall_count (basic (e2⊗e1⊗w4))) = snd (count y1)" 
               using step3_subresult1 step3_subresult2 by auto 
have step3_subresult4: "fst (wall_count (basic (e1⊗w4))) = snd (wall_count ?x2)" 
               using step3_subresult3 subresult0 wall_count_def step3_subresult2 subresult1 by auto 
have step3_subresult5: "fst (wall_count (basic (e1⊗w4))) = snd (wall_count (x1∘(basic y1)))" 
               using step3_subresult4  wall_count_def by auto
have step3_subresult6: "fst (brickcount a2) =  0" using brickcount_def by auto
have step3_subresult7: "fst (count e2) =  0" using e2_def count_def step3_subresult6 
by (metis count.simps(1))
have step3_subresult8: "strands (a1#e1)" using e1_def append_def strands_def  brickstrand.simps(1) 
                        strands.simps(1) strands.simps(2) 
                       by metis
have step3_subresult9: "(a1#e1) = (e1⊗e1)" using append_Nil e1_def
                        by metis
have step3_subresult10: "strands (e1⊗e1)" using step3_subresult8 step3_subresult9
                        by auto
let ?a0 = "(basic (e1⊗e3⊗w4))∘z1"
let ?b0 = "(e1⊗e1)"
let  ?a = "Abs_diagram ((x1)∘(basic (e2⊗y1))∘(basic (?b0⊗(e1⊗w4)))∘((basic (e1⊗e3⊗w4))∘z1))"
(*check b*)
let ?b = "Abs_diagram ((x1)∘(basic y1)∘(basic (e2 ⊗ (e1 ⊗ w4)))∘((basic (e1⊗e3⊗w4))∘z1))"

have step3_subresult11: "  ∃y1.∃w1.∃w2.∃A.∃B.∃y2.(?a = Abs_diagram
 ((y1)∘(basic (A⊗w1))∘(basic (B⊗w2))∘(y2)))"
using exI by metis

have step3_subresult12: " ∃y1.∃w1.∃w2.∃A.∃B.∃y2.(
?b =
(Abs_diagram
 ((y1)∘(basic (w1))∘(basic (A⊗w2))∘(y2))))"
using exI 
by metis

have step3_subresult13: "  ∃y1.∃w1.∃w2.∃A.∃B.∃y2.((?a = Abs_diagram
 ((y1)∘(basic (A⊗w1))∘(basic (B⊗w2))∘(y2))) ∧
 (?b = Abs_diagram
 ((y1)∘(basic (w1))∘(basic (A⊗w2))∘(y2)))
∧((snd (count w1)) = (fst (count w2)))
∧((fst (count A)) = 0)
∧(strands B))" 
using
step3_subresult11 step3_subresult12
compose_leftassociativity step2_subresult1 subresult8 w_subst
step3_subresult5 step3_subresult7 step3_subresult10 exI assms
leftright_associativity step2_subresult4 step2_subresult6
by (metis)

have step3_subresult14: "tanglerel_compbelow_centerright ?a ?b" using step3_subresult13 
tanglerel_compbelow_centerright_def by auto
have step3_subresult15: "tanglerel_compress ?a ?b" using step3_subresult14 tanglerel_compress_def 
tanglerel_compbelow_def by auto
have step3_subresult16: "tanglerel ?a ?b" using step3_subresult15 tanglerel_def by auto

have step3_subresult17: "tanglerel_equiv ?a ?b"
    using step3_subresult16 tanglerel_equiv_def r_into_rtranclp
       by (metis (full_types) r_into_rtranclp)

have step3_subresult18: "tanglerel_equiv 
(Abs_diagram ((x1)∘(basic (e2⊗y1))∘(basic ((e1⊗e1)⊗(e1⊗w4)))∘((basic (e1⊗e3⊗w4))∘z1)))
(Abs_diagram ((x1)∘(basic y1)∘(basic (e2 ⊗ (e1 ⊗ w4)))∘((basic (e1⊗e3⊗w4))∘z1)))"
 using step3_subresult17
by metis

have step3: 
"tanglerel_equiv (Abs_diagram ((x1)∘(basic (e2⊗y1))∘(basic (e1⊗e1⊗e1⊗w4))∘(basic (e1⊗e3⊗w4))∘z1))
 (Abs_diagram (((x1)∘(basic y1))∘(basic (e2 ⊗ z4))∘ (basic (e1⊗e3⊗w4))∘z1))" 
using step3_subresult18 leftright_associativity w_subst step2_subresult1 left_associativity
 compose_leftassociativity
by auto

(*combining steps*)
                      
have combine1: 
"tanglerel_equiv (Abs_diagram (x1∘basic y1∘(basic (e2⊗z4))∘(basic (e1⊗e3⊗w4))∘z1)) 
                            (Abs_diagram (x1 ∘ basic y1 ∘z1))" 
               using step1 step2 rtranclp_trans tanglerel_equiv_def by metis

have combine2:"tanglerel_equiv (Abs_diagram ((x1)∘(basic (e2⊗y1))∘(basic (e1⊗e1⊗z4))∘(basic (e1⊗e3⊗w4))∘z1))
             (Abs_diagram (x1 ∘ basic y1 ∘z1))" 
               using step3 combine1 tanglerel_equiv_def rtranclp_trans
                compose_leftassociativity leftright_associativity 
               step2 step2_subresult1 step2_subresult2 step3_subresult17 subresult_equiv3 
               w_subst
               by (metis) 
from combine2 show ?thesis by auto
qed

