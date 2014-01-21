theory Component_def
imports Tangles
begin

(*strand types are defined - vertical, left/right over, left/right under, left/right cap, left/ right cup*)
 (*convention - left over is the over going strand from right to left*)

datatype strand = str_vert|str_lover|str_lunder|str_rover|str_runder|str_lcap|str_rcap|str_lcup|str_rcup

(*Each of the basic tangles are assigned the strand types which they are composed of*)
primrec brick_assign::"brick ⇒ strand list"
where
"brick_assign vert = [str_vert]"
|"brick_assign over = [str_rover, str_lunder]"
|"brick_assign under = [str_runder, str_lover]"
|"brick_assign cap = [str_rcap,str_lcap]"
|"brick_assign cup = [str_rcup,str_lcup]"

(*Each of the blocks are assigned a list of strand types*)
primrec block_assign::"block ⇒ strand list"
where
"block_assign (cement x) = (brick_assign x)"
|"block_assign (cons x xs) = (brick_assign x)@(block_assign xs)"

(*Each wall is assigned a list of list of strands - this definition automatically gives us 
a way to allot positions to strand types in the wall*)
primrec wall_assign::"walls ⇒ strand list list"
where
"wall_assign (basic x) = [(block_assign x)]"
|"wall_assign (prod x xs) = (block_assign x)#(wall_assign xs)"

(*Given an 2-tuple of natural number (i,j) which can be used to denote the position of a strand in a
wall , the following functions gives the set of strand types to its 
right in the block, while filtering out the strand types which are used in the caps and cups. This is important
to ensure alignment of strand types *)
(*cap-filter*)
definition cap_filter::"walls ⇒ nat × nat ⇒ strand set"
where
"cap_filter w x ≡ {(wall_assign w)!j!i| i j. j=(snd x)∧ (i<(fst x))∧ 
(((wall_assign w)!j!i ≠ str_rcap) ∨ ((wall_assign w)!j!i ≠ str_lcap)) }"

definition cap_count::"walls ⇒ nat × nat ⇒ nat"
where
"cap_count w x = card (cap_filter w x)"

(*cup-filter*)
definition cup_filter::"walls ⇒ nat × nat ⇒ strand set"
where
"cup_filter w x ≡ {(wall_assign w)!j!i| i j. j=(snd x)∧ (i<(fst x))∧ 
(((wall_assign w)!j!i ≠ str_rcup) ∨ ((wall_assign w)!j!i ≠ str_lcup)) }"

definition cup_count::"walls ⇒ nat × nat ⇒ nat"
where
"cup_count w x = card (cup_filter w x)"

(*relates vertical strand to the one below it*)
definition relation_vert::"walls ⇒ strand × nat × nat ⇒ strand × nat × nat ⇒ bool"
where 
"relation_vert w x y ≡ 
(((wall_assign w)!(snd (snd x))!(fst (snd x))) = str_vert)
∧((fst x)= (str_vert))
∧(((wall_assign w)!(snd (snd y))!(fst (snd y))) = (fst y))
∧ ((snd (snd y)) = (snd (snd x))+ 1) 
∧ (cap_count w (snd y) = cup_count w (snd x))"

(*relates the lcap to its rcap*)
definition relation_lcap_rcap::"walls ⇒ strand × nat × nat ⇒ strand × nat × nat ⇒ bool"
where 
"relation_lcap_rcap w x y ≡(((wall_assign w)!(snd (snd x))!(fst (snd x))) = str_lcap)∧
(((wall_assign w)!(snd (snd y))!(fst (snd y))) = str_rcap)∧((fst x) = str_lcap)∧(fst y = str_rcap)
∧((snd (snd y)) = (snd (snd x))) ∧ ((fst (snd y) = fst (snd x)+1))"


(*relates the lcap to the strand below*)
definition relation_lcap_below::"walls ⇒ strand × nat × nat ⇒ strand × nat × nat ⇒ bool"
where 
"relation_lcap_below w x y ≡(((wall_assign w)!(snd (snd x))!(fst (snd x))) = str_lcap)∧
(((wall_assign w)!(snd (snd y))!(fst (snd y))) = fst y)∧((fst x) = str_lcap)
∧((snd (snd y)) = (snd (snd x))+1) ∧ ((cap_count w (snd y) = cup_count w (snd x)))"


(*relates the rcap to the strand below*)
definition relation_rcap_below::"walls ⇒ strand × nat × nat ⇒ strand × nat × nat ⇒ bool"
where 
"relation_rcap_below w x y ≡(((wall_assign w)!(snd (snd x))!(fst (snd x))) = str_rcap)∧
(((wall_assign w)!(snd (snd y))!(fst (snd y))) = fst y)∧((fst x) = str_rcap)
∧((snd (snd y)) = (snd (snd x))+1) ∧ ((cap_count w (snd y) = cup_count w (snd x)))"


(*relates the lcup to rcup*)
definition relation_lcup_rcup::"walls ⇒ strand × nat × nat ⇒ strand × nat × nat ⇒ bool"
where 
"relation_lcup_rcup w x y ≡(((wall_assign w)!(snd (snd x))!(fst (snd x))) = str_lcup) ∧
(((wall_assign w)!(snd (snd y))!(fst (snd y))) = str_rcup) 
∧((fst x) = str_lcup)∧(fst y = str_rcup)
∧((snd (snd y)) = (snd (snd x))) ∧ (fst (snd y) = fst (snd x) + 1)"


(*relates the right over strand to the strand diagonally across from its origin point*)
definition relation_rover::"walls ⇒ strand × nat × nat ⇒ strand × nat × nat ⇒ bool"
where 
"relation_rover w x y ≡ (((wall_assign w)!(snd (snd x))!(fst (snd x))) = fst x)∧(fst x = str_rover)
∧(((wall_assign w)!(snd (snd y))!(fst (snd y))) = fst y)∧
(snd (snd y))= (snd (snd x) + 1) ∧ (cap_count w (snd y) = cup_count w (snd x) + 1)"

(*right under*)
definition relation_runder::"walls ⇒ strand × nat × nat ⇒ strand × nat × nat ⇒ bool"
where 
"relation_runder w x y ≡ (((wall_assign w)!(snd (snd x))!(fst (snd x))) = fst x)∧(fst x = str_runder)
∧(((wall_assign w)!(snd (snd y))!(fst (snd y))) = fst y)∧
(snd (snd y))= (snd (snd x) + 1) ∧ (cap_count w (snd y) = cup_count w (snd x) + 1)"

(*left-over*)
definition relation_lover::"walls ⇒ strand × nat × nat ⇒ strand × nat × nat ⇒ bool"
where 
"relation_lover w x y ≡ (((wall_assign w)!(snd (snd x))!(fst (snd x))) = fst x)∧(fst x = str_lover)
∧(((wall_assign w)!(snd (snd y))!(fst (snd y))) = fst y)∧
(snd (snd y))= (snd (snd x) + 1) ∧ (cap_count w (snd y) + 1 = cup_count w (snd x))"

(*left-under*)
definition relation_lunder::"walls ⇒ strand × nat × nat ⇒ strand × nat × nat ⇒ bool"
where 
"relation_lunder w x y ≡ (((wall_assign w)!(snd (snd x))!(fst (snd x))) = fst x)∧(fst x = str_lunder)
∧(((wall_assign w)!(snd (snd y))!(fst (snd y))) = fst y)∧
(snd (snd y))= (snd (snd x) + 1) ∧ (cap_count w (snd y) + 1 = cup_count w (snd x))"


(*The strand relation*)
definition strand_rel::"walls ⇒ strand × nat × nat ⇒ strand × nat × nat ⇒ bool"
where
"strand_rel w x y ≡ ((relation_lcap_rcap w x y) 
∨(relation_lcup_rcup w x y) ∨ (relation_vert w x y) ∨(relation_lcap_below w x y)
∨(relation_rcap_below w x y)∨ (relation_lover w x y) ∨ (relation_lunder w x y) 
∨(relation_rover w x y) ∨ (relation_runder w x y)) "


definition symmetrize::"('a ⇒ 'a ⇒ bool) ⇒ ('a ⇒ 'a ⇒ bool)"
where
"symmetrize r ≡ λ x y.(r x y)∨(r y x)"

(*The symmetrized strand relation*)
definition relation::"walls ⇒ strand × nat × nat ⇒ strand × nat × nat ⇒ bool"
where
"relation w ≡ (symmetrize (strand_rel w))"

(*Its transitive closure*)
definition strand_equivalence::"walls ⇒ strand × nat × nat ⇒ strand × nat × nat ⇒ bool"
where
"strand_equivalence w ≡ (relation w)^**"

(*orbit*)
definition orbit::"walls ⇒ strand × nat × nat ⇒(strand × nat × nat) set"
where
"orbit w x = {y. strand_equivalence w x y = True}"

(*orbit space- the set of components*)
definition orbit_space::"walls ⇒ (strand × nat × nat) set set"
where
"orbit_space w ≡ {(orbit w x)| x. ((fst x) = ((wall_assign w)!(snd (snd x))!(fst (snd x)))) }"

definition component_number::"walls ⇒ nat"
where
"component_number w ≡ card (orbit_space w)"
