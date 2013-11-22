theory invariant
imports Main Datatype Tangles_mod
begin

locale tangle_invariant=
 fixes f::" brick => 'a"
 fixes tens::"'a ⇒ 'a ⇒ 'a"
 fixes comp::"'a ⇒ 'a ⇒ 'a"
 assumes
  comp_assoc: "(comp (comp a b) c) = (comp a (comp b c))"
and tens_assoc: "(tens (tens a b) c) = (tens a (tens b c))"
and tens_comp: "comp (tens a b) (tens c d) = (tens (comp a c) (comp c d))" 
context tangle_invariant
begin

primrec block_inv::"block ⇒ 'a"
where  
"block_inv (cement x) = f x"|
"block_inv (a#xs) = tens (f a) (block_inv xs)"
   

primrec wall_inv::"walls ⇒ 'a"
where
"wall_inv (basic x) = (block_inv x)"|
"(wall_inv (a*xs)) = comp (block_inv a) (wall_inv xs)"

lemma tens_product:"block_inv (xs⊗ys) = tens (block_inv xs) (block_inv ys)"
apply(induct_tac xs)
apply(auto)
apply(simp add:tens_assoc)
done

lemma wall_inv:"wall_inv (xs ∘ ys) = comp (wall_inv xs) (wall_inv ys)"
apply(induct_tac xs)
apply(auto)
apply(simp add:comp_assoc)
done

definition map::"diagram ⇒ 'a"
where
"map x = (wall_inv (Rep_diagram x))"


lemma nameless: assumes "(comp (f (a_over))) (f (a_under)) = 
(comp (tens (f a_vert) (f a_vert)) (tens (f a_vert) (f a_vert)))"
and "tanglerel_pull_posneg x y"
shows "(map x) = (map y)"
proof-
have "tanglerel_pull_posneg x y" using assms(2) by simp
then have " ∃y1.∃z1.∃z2.∃w1.∃w2.∃y2.((x =  Abs_diagram ((y1)
∘(basic (z1⊗e_over⊗w1)∘(basic (z2⊗e_under⊗w2)))∘(y2)))∧(y = 
Abs_diagram  ((y1)
∘(basic (z1⊗e_vert⊗e_vert⊗w1))∘(basic (z2⊗e_vert⊗e_vert⊗w2))∘(y2)))
∧((snd (count z1)) = (fst (count z2))))" using tanglerel_pull_posneg_def by auto
from this obtain y1 z1 z2 w1 w2 y2 where "((x = Abs_diagram ((y1)
∘(basic (z1⊗e_over⊗w1)∘(basic (z2⊗e_under⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e_vert⊗e_vert⊗w1))∘(basic (z2⊗e_vert⊗e_vert⊗w2))∘(y2)))
∧((snd (count z1)) = (fst (count z2))))" by metis
from this have "x = Abs_diagram ((y1)
∘(basic (z1⊗e_over⊗w1)∘(basic (z2⊗e_under⊗w2)))∘(y2))" by auto
from this have "Rep_diagram x = ((y1)
∘(basic (z1⊗e_over⊗w1)∘(basic (z2⊗e_under⊗w2)))∘(y2))" using assms(3) sledgehammer

(*
definition tanglerel_pull_posneg::"diagram ⇒ diagram ⇒ bool"
where
"tanglerel_pull_posneg x y ≡  ∃y1.∃z1.∃z2.∃w1.∃w2.∃y2.((x = Abs_diagram ((y1)
∘(basic (z1⊗e_over⊗w1)∘(basic (z2⊗e_under⊗w2)))∘(y2)))∧(y = Abs_diagram
 ((y1)
∘(basic (z1⊗e_vert⊗e_vert⊗w1))∘(basic (z2⊗e_vert⊗e_vert⊗w2))∘(y2)))
∧((snd (count z1)) = (fst (count z2))))"



end

locale invariant= tangle_invariant+assumes "(tangle_equiv x y) ⟶ ((map x) = (map y))"
context invariant
begin
*)
