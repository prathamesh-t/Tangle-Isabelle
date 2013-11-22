theory invariant
imports Main Datatype Tangles
begin

locale tangle_invariant=
 fixes f::" brick => 'a"
 fixes tens::"'a ⇒ 'a ⇒ 'a"
 fixes comp::"'a ⇒ 'a ⇒ 'a"
 assumes
  tens_assoc: "(tens (tens a b) c) = (tens a (tens b c))"
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

definition map::"diagram ⇒ 'a"
where
"map x = (wall_inv (Rep_diagram x))"
end

locale invariant= tangle_invariant+assumes "(tangle_equiv x y) ⟶ ((map x) = (map y))"
context invariant
begin
