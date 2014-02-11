theory Tangle_Algebra
imports Tangles
begin

(*the following definition enables construction of a block*)
primrec make_vert_block:: "nat ⇒ block"
where
"make_vert_block 0 = (cement vert)"
|"make_vert_block (Suc n) = vert#(make_vert_block n)"

(*we defined the tensor of walls in accordance with the tensor algebra*)
fun tensor::"walls => walls => walls"
where
"tensor (basic x) (basic y) = (basic (x ⊗ y))"
|"tensor (x*xs) (basic y) = (if (codomain_block y = 0)then (x ⊗ y)*xs else 
(x ⊗ y)*(tensor xs (basic (make_vert_block (nat (codomain_block y- 1))))))"
|"tensor (basic x) (y*ys) = (if (codomain_block x = 0) then (x ⊗ y)*ys else 
(x ⊗ y)*(tensor (basic (make_vert_block (nat (codomain_block x- 1)))) ys))"
|"tensor (x*xs) (y*ys) = (x ⊗ y)* (tensor xs ys)"

lemma "tensor (basic (cement vert)) (basic (cement vert)) = (basic ((cement vert) ⊗ (cement vert)))"
by simp
(*
theorem well_definedness:
 assumes "well_defined_tangle x" 
    and "well_defined_tangle y" 
 shows"well_defined_tangle (tensor x y)"
proof(induct_tac x y rule: tensor.induct)
*)


end
