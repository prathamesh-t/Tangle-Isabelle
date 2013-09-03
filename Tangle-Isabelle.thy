theory Tangles_SetRelation
imports Datatype Main tangle_relation
begin

datatype block = e1
                |e2
                |e3
                |e4
                |e5
                |Cons block block              (infixr "⊗" 65)

primrec count::"block ⇒ int × int "
where
"count e1 = (1,1)"|
"count e2 = (0,2)"|
"count e3 = (2,0)"|
"count e4 = (2,2)"|
"count e5 = (2,2)"|
"count (Cons x y) = (fst (count x) + fst (count y), snd (count x) + snd (count y))"

lemma trivial: " count (e1 ⊗ e2) = (1,3)"
apply(auto)
done

datatype walls = basic block
                |prod walls walls  (infixr "∘" 66)


primrec wall_count:: "walls => int × int" where
"wall_count (basic x) = count x"
|"wall_count (prod x y) = (fst (wall_count x),snd (wall_count y))"

definition abs::"int ⇒ int" where
"abs x ≡ if (x≥0) then x else (0-x)" 

primrec wall_list:: "walls ⇒ int list" where
"wall_list (basic x) = []"|
"wall_list (x ∘ y) =  (abs (fst(wall_count y) - snd(wall_count x)))#(wall_list y)"

lemma trivial2: "wall_list (basic e1) = []"
apply(auto)
done


lemma trivial3: "fst(wall_count (basic e3))- snd(wall_count (basic e1)) = 1"
apply(auto)
done

lemma trivial4: "wall_list ((basic e3)∘(basic e1)∘(basic e1)) = [1,0]"
apply(auto)
apply(simp add:abs_def)
apply(simp add:abs_def)
done

primrec list_sum::"int list ⇒ int" where
"list_sum [] = 0"|
"list_sum (x#xs) = x+ list_sum xs"


typedef diagram = "{(x::walls).  (list_sum (wall_list x)+(abs(fst(wall_count x))
+ abs(snd(wall_count x)))) = 0}"
apply (rule_tac x = "prod (basic e2) (basic e3)" in exI)
apply(auto)
apply(simp add:abs_def)
done

definition a::diagram where "a ≡ Abs_diagram (basic e1)"
definition b::diagram where "b ≡ Abs_diagram (basic e2)"
definition c::diagram where "c ≡ Abs_diagram (basic e3)"
definition d::diagram where "d  ≡ Abs_diagram (basic e4)"
definition e::diagram where "e ≡ Abs_diagram (basic e5)"


definition tanglerel_one::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_one x y ≡ (∃y1.∃z1.∃z2.∃z3.∃w1.∃w2.∃w3.∃y2.( x = Abs_diagram ((y1)
∘(basic (z1⊗e1⊗e2⊗w1)∘(basic (z2⊗e4⊗e1⊗w2))∘(basic (z3⊗e1⊗e3⊗w3))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e2⊗e1⊗w1)∘(basic (z2⊗e1⊗e4⊗w2))∘(basic (z3⊗e3⊗e1⊗w3))∘(y2)))) )
"

definition tanglerel_two::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_two x y ≡  ∃y1.∃z1.∃z2.∃z3.∃w1.∃w2.∃w3.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e4⊗w1)∘(basic (z2⊗e5⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e1⊗w1))∘(basic (z3⊗e1⊗e1⊗w3))∘(y2))))"

definition tanglerel_three::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_three x y ≡ ∃y1.∃z1.∃z2.∃z3.∃w1.∃w2.∃w3.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e4⊗e1⊗w1)∘(basic (z2⊗e1⊗e4⊗w2))∘(basic (z3⊗e4⊗e1⊗w3))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e4⊗w1)∘(basic (z2⊗e4⊗e1⊗w2))∘(basic (z3⊗e1⊗e4⊗w3))∘(y2)))))"

definition tanglerel_four::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_four x y ≡  ∃y1.∃z1.∃z2.∃w1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e3⊗e1⊗w1)∘(basic (z2⊗e1⊗e2⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗w1))∘(basic (z2⊗e1⊗w2))∘(y2))))"

definition tanglerel_five::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_five x y ≡  ∃y1.∃z1.∃z2.∃w1.∃w2.∃y2.((x = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗w1))∘(basic (z2⊗e1⊗w2))∘(y2)))∧ ((y = Abs_diagram ((y1)
∘(basic (z1⊗e1⊗e2⊗w1)∘(basic (z2⊗e3⊗e1⊗w2)))∘(y2)))))"

definition tanglerel_six::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_six x y ≡  ∃y1.∃z1.∃z2.∃w1.∃w2.∃y2.((x = Abs_diagram
 ((y1)
∘(basic (z1⊗e1⊗e4⊗w1))∘(basic (z2⊗e2⊗e1⊗w2))∘(y2)))∧ ((y = Abs_diagram ((y1)
∘(basic (z1⊗e4⊗e1⊗w1)∘(basic (z2⊗e1⊗e2⊗w2)))∘(y2)))))"

primrec strands::"block ⇒ bool"
where
"strands e1 = True"|
"strands e2 = False"|
"strands e3 = False"|
"strands e4 = False"|
"strands e5 = False"|
"strands (x⊗y) = (if (x= e1) then (strands y) else (strands x)∧(strands y))"

lemma trivial5: "strands (e1⊗e2⊗e1⊗e1) = False" by auto

definition tanglerel_seven::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_seven x y ≡  ∃y1.∃z.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z))∘(y2)))∧(strands z)∧((y = Abs_diagram ((y1)∘(y2)))))"

definition tanglerel_eight::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_eight x y ≡  ∃y1.∃z.∃y2.((x = Abs_diagram
 ((y1)∘(y2)))∧((y = Abs_diagram ((y1)∘(basic z)∘(y2))))∧(strands z) )"

lemma eight:"tanglerel_eight (Abs_diagram ((basic e4)∘(basic e4))) (Abs_diagram ((basic e4)
∘(basic (e1⊗e1))∘(basic e4)))" 
proof-
let ?x1 = "Abs_diagram ((basic e4)∘(basic e4))"
let ?x2 = "Abs_diagram ((basic e4)∘(basic (e1⊗e1))∘(basic e4))"
let ?y1 = "(basic e4)"
let ?y2 = "(basic e4)"
let ?z =  "(e1⊗e1)"
have "strands ?z" by simp 
have "(?x1 =  Abs_diagram
 ((?y1)∘(?y2)))∧((?x2 = Abs_diagram ((?y1)∘(basic ?z)∘(?y2))))∧(strands ?z)" by simp
then show ?thesis using tanglerel_eight_def by force
qed

definition tanglerel_nine::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_nine x y ≡  ∃y1.∃z1.∃z2.∃z3.∃w1.∃w2.∃w3.∃y2.((x = Abs_diagram
 ((y1)∘(basic (z1⊗w1))∘(basic (z2⊗w2))∘(y2)))∧
(y = Abs_diagram
 ((y1)∘(basic (z3⊗w2))∘(basic (z1⊗w3))∘(y2)))∧(strands w1)∧(strands z2)∧(strands z3)∧(strands w3)
∧((snd (count z1)) = (fst (count z2))) ∧((snd (count w1)) = (fst (count w2)))
∧((snd (count z3)) = (fst (count z1))) ∧((fst (count w3)) = (snd (count w2))))"


definition tanglerel_11::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_11 x y ≡ (∃y1.∃y2.( x = Abs_diagram ((y1)
∘(basic (e1⊗e3)∘(basic (e4⊗e1))∘(basic (e1⊗e2))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (e3⊗e1))∘(basic (e1⊗e4))∘(basic (e2⊗e1))∘(y2))))
"

definition tanglerel_12::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_12 x y ≡  ∃y1.∃y2.((x = Abs_diagram ((y1)
∘(basic e4)∘(basic e5)∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e1))∘(basic (e1⊗e1))∘(y2))))"

definition tanglerel_13::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_13 x y ≡ ∃y1.∃y2.((x = Abs_diagram ((y1)
∘(basic (e4⊗e1)∘(basic (e1⊗e4))∘(basic (e4⊗e1))∘(y2))))∧(y = Abs_diagram
 ((y1)
∘(basic (e1⊗e4)∘(basic (e4⊗e1))∘(basic (e1⊗e4))∘(y2)))))"

definition tanglerel_14::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_14 x y ≡  ∃y1.∃y2.((x = Abs_diagram ((y1)
∘(basic (e3⊗e1))∘(basic (e1⊗e2))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (e1))∘(basic e1)∘(y2))))"

definition tanglerel_15::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_15 x y ≡  ∃y1.∃y2.((x = Abs_diagram
 ((y1)
∘(basic (e1))∘(basic (e1))∘(y2)))∧ (y = Abs_diagram ((y1)
∘(basic (e1⊗e2))∘(basic (e3⊗e1))∘(y2))))"

definition tanglerel_16::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_16 x y ≡  ∃y1.∃y2.((x = Abs_diagram
 ((y1)
∘(basic (e1⊗e4))∘(basic (e2⊗e1))∘(y2)))∧ (y = Abs_diagram ((y1)
∘(basic (e4⊗e1))∘(basic (e1⊗e2))∘(y2))))"

definition tanglerel::"diagram =>diagram⇒bool"
where
"tanglerel x y = ((tanglerel_one x y) ∨ (tanglerel_two x y) ∨ (tanglerel_three x y) 
∨(tanglerel_four x y)∨(tanglerel_five x y) ∨ (tanglerel_six x y) ∨ (tanglerel_seven x y) 
∨ (tanglerel_eight x y)∨(tanglerel_nine x y)
∨(tanglerel_11 x y) ∨ (tanglerel_12 x y) ∨ (tanglerel_13 x y) ∨(tanglerel_14 x y)
∨(tanglerel_15 x y)∨(tanglerel_16 x y)
∨(tanglerel_one y x) ∨ (tanglerel_two y x) 
∨ (tanglerel_three y x) ∨(tanglerel_four y x)∨(tanglerel_five y x) ∨ (tanglerel_six y x) ∨ (tanglerel_seven y x) 
∨ (tanglerel_eight y x)∨(tanglerel_nine y x)
∨(tanglerel_11 y x) ∨ (tanglerel_12 y x) ∨ (tanglerel_13 y x) ∨(tanglerel_14 y x)
∨(tanglerel_15 y x)∨(tanglerel_16 y x))"

lemma tanglerel_symp: "symp tanglerel" unfolding tanglerel_def symp_def by auto

find_theorems"rtranclp"
 
definition tanglerel_equiv::"diagram⇒diagram⇒bool"
where
"(tanglerel_equiv) = (tanglerel)^**" 
 
lemma reflective: "tanglerel_equiv x x" unfolding tanglerel_equiv_def by simp

lemma tangle_symmetry:"symp tanglerel_equiv" using tanglerel_symp symmetry3 
by (metis (full_types) tanglerel_equiv_def)

(*lemma implication_and:"(A⟶ B⟶ C) = ((A∧B)⟶C)" by auto

lemma connective_commutativity:"((A∨B)∧(C∨D)) = ((A∧C)∨(A∧D)∨(B∧C)∨(B∧D))" by auto 
*)
quotient_type Tangle = "diagram" / "tanglerel_equiv"
 morphisms Rep_tangles Abs_tangles
proof (rule equivpI)
show "reflp tanglerel_equiv" unfolding reflp_def reflective by (metis reflective)
show "symp tanglerel_equiv" using tangle_symmetry by auto
show "transp tanglerel_equiv" unfolding transp_def tanglerel_equiv_def rtranclp_trans by auto  
qed

lemma test2: assumes "a =  Abs_diagram ((basic e3)∘(basic (e1⊗e1))∘ (basic e2))" 
and "b = Abs_diagram  ((basic e3)∘(basic e2))"
shows "(Abs_tangles a)= (Abs_tangles b)" using tanglerel_equiv_def tanglerel_def tanglerel_nine_def
proof-
have  "strands (e1⊗e1)" using strands_def by auto
then have " ∃y1.∃z.∃y2.
((b = Abs_diagram ((y1)∘(y2)))
∧((a = Abs_diagram ((y1)∘(basic z)∘(y2))))∧(strands z) )" 
using assms by force
then have "tanglerel_eight b a" using tanglerel_eight_def by auto
then have "tanglerel a b" using tanglerel_def by auto
then have "tanglerel^** a b" using r_into_rtranclp by auto
then have "tanglerel_equiv a b" using tanglerel_equiv_def by auto
thus ?thesis using Tangle.abs_eq_iff   by auto
qed

primrec cusp_detector::"block ⇒ bool"
where
" cusp_detector e1 = False"|
" cusp_detector e2 = False"|
" cusp_detector e3  = True"|
" cusp_detector e4 = False"|
" cusp_detector e5 = False"|
" cusp_detector (x⊗y) = (if (x= e3) then (cusp_detector y) else (cusp_detector x)∧(cusp_detector y))"



(*Some changes are being made here, will update the code soon) 


