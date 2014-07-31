theory Framed_Links
imports Links
begin

(*Defining- Framed Link Relations*)
definition framed_linkrel::"walls ⇒ walls ⇒ bool"
where
"framed_linkrel x y = ((framed_linkrel_uncross x y) ∨ (linkrel_pull x y) ∨ (linkrel_straighten x y) 
∨(linkrel_swing x y)∨(linkrel_rotate x y) ∨ (linkrel_compress x y) ∨ (linkrel_slide x y)
∨  (framed_linkrel_uncross y x) ∨ (linkrel_pull y x) ∨ (linkrel_straighten y x) 
∨(linkrel_swing y x)∨(linkrel_rotate y x) ∨ (linkrel_compress y x) ∨ (linkrel_slide y x))"

text{*Following lemma tells us that framed Link relations implies Link relation*}

lemma framed_linkrel_implies_linkrel: "(framed_linkrel x y) ⟹ (linkrel x y)"
using framed_uncross_implies_uncross framed_linkrel_def linkrel_def by auto


text{*Following lemma tells us that framed Link relation is Symmetric*}

lemma framed_linkrel_symp: "symp framed_linkrel" unfolding framed_linkrel_def symp_def by auto



text{*Following lemma construct equivalence among Links*}
 
definition framed_linkrel_diagram_left::"walls ⇒ walls ⇒ bool"
where
"framed_linkrel_diagram_left x y ≡ ∃A.∃B.∃C.((x =  ((A::walls) ⊗ B))∧ (y = (C ⊗ B)) 
                                     ∧ (framed_linkrel A C))"

definition framed_linkrel_diagram_right::"walls ⇒ walls ⇒ bool"
where
"framed_linkrel_diagram_right x y ≡ ∃A.∃B.∃C.((x = (A ⊗ B))∧ (y = (A ⊗ C)) 
                                  ∧ (framed_linkrel B C))"


definition framed_linkrel_diagram_center::"walls ⇒ walls ⇒ bool"
where
"framed_linkrel_diagram_center x y ≡ ∃A.∃B1.∃B2.∃C.((x = (A ∘ (B1::walls) ⊗ C))
                                           ∧ (y = (A ∘ (B2::walls) ⊗ C)) 
                                     ∧ (framed_linkrel B1 B2))"


definition framed_linkrel_diagram_middle_center::"walls ⇒ walls ⇒ bool"
where
"framed_linkrel_diagram_middle_center x y ≡ ∃A.∃B.∃C1.∃C2.∃D.∃E.((x = (A ∘ (B::walls) ⊗ C1 ⊗ D ∘ E))
                                           ∧ (y = (A ∘ (B::walls) ⊗ C2 ⊗ D ∘ E)) 
                                     ∧ (framed_linkrel C1 C2))"

definition framed_linkrel_diagram_middle_left:: "walls ⇒ walls ⇒ bool"
where
"framed_linkrel_diagram_middle_left x y ≡ ∃A.∃B1.∃B2.∃C.∃D.((x = (A ∘ ((B1::walls)⊗C) ∘D))
                                           ∧ (y = (A ∘ ((B2::walls) ⊗ C) ∘ D)) 
                                     ∧ (framed_linkrel B1 B2))"

definition framed_linkrel_diagram_middle_right::"walls ⇒ walls ⇒ bool"
where
"framed_linkrel_diagram_middle_right x y ≡ ∃A.∃B.∃C1.∃C2.∃D.((x = (A ∘ (B::walls)⊗C1∘ D))
                                           ∧ (y =  (A ∘ (B::walls) ⊗ C2 ∘ D)) 
                                     ∧ (framed_linkrel C1 C2))"

definition framed_linkrel_diagram_bottom_left::"walls ⇒ walls ⇒ bool"
where
"framed_linkrel_diagram_bottom_left x y ≡ ∃A1.∃A2.∃B.∃C.((x = (((A1::walls) ⊗ B) ∘ C)) 
                                                ∧((y = (((A2::walls) ⊗ B) ∘ C))) 
                                                ∧(framed_linkrel A1 A2))"
                
definition framed_linkrel_diagram_bottom_right::"walls ⇒ walls ⇒ bool"
where
"framed_linkrel_diagram_bottom_right x y ≡ ∃A.∃B1.∃B2.∃C.((x = (((A::walls) ⊗ B1) ∘ C)) 
                                                ∧((y = (((A::walls) ⊗ B2) ∘ C))) 
                                                ∧(framed_linkrel B1 B2))"
definition framed_linkrel_diagram_bottom_center::"walls ⇒ walls ⇒ bool"
where
"framed_linkrel_diagram_bottom_center x y ≡ ∃A.∃B1.∃B2.∃C.∃D.((x = (((A::walls) ⊗ B1 ⊗ C) ∘ D)) 
                                                ∧((y = (((A::walls) ⊗ B2 ⊗ C) ∘ D))) 
                                                ∧(framed_linkrel B1 B2))"

definition framed_linkrel_diagram_top_left::"walls ⇒ walls ⇒ bool"
where
"framed_linkrel_diagram_top_left x y ≡ ∃A.∃B1.∃B2.∃C.((x = (A ∘ ((B1::walls) ⊗  C)))
                                                ∧(y = (A ∘ ((B2::walls) ⊗ C)))
                                                ∧(framed_linkrel B1 B2))"
                
definition framed_linkrel_diagram_top_right::"walls ⇒ walls ⇒ bool"
where
"framed_linkrel_diagram_top_right x y ≡ ∃A.∃B.∃C1.∃C2.((x = (A ∘((B::walls) ⊗ C1))) 
                                                 ∧(y = (A ∘ (B ⊗ C2))) 
                                                 ∧(framed_linkrel C1 C2))"
definition framed_linkrel_diagram_top_center::"walls ⇒ walls ⇒ bool"
where
"framed_linkrel_diagram_top_center x y ≡ ∃A.∃B.∃C1.∃C2.∃D.((x = (A ∘  ((B::walls) ⊗ C1 ⊗ D)))
                                                ∧(y = ((A ∘ (B ⊗ C2 ⊗ D)))
                                                ∧(framed_linkrel C1 C2)))"


(*Framed_linkrel_diagram is the generating relation between two given Links*)
definition framed_linkrel_diagram::"walls ⇒ walls ⇒ bool"
where
"framed_linkrel_diagram x y ≡ (
(framed_linkrel_diagram_left x y)∨(framed_linkrel_diagram_right x y) ∨ (framed_linkrel_diagram_center x y)
∨(framed_linkrel_diagram_middle_left x y)∨(framed_linkrel_diagram_middle_right x y)
∨(framed_linkrel_diagram_middle_center x y)
∨(framed_linkrel_diagram_bottom_left x y)∨(framed_linkrel_diagram_bottom_left x y)
∨(framed_linkrel_diagram_bottom_center x y)
∨(framed_linkrel_diagram_top_left x y)∨(framed_linkrel_diagram_top_right x y)∨(framed_linkrel_diagram_top_center x y)
)"

(*proving the symmetry of framed_linkrel_diagram*)
lemma framed_symm_left:"(framed_linkrel_diagram_left x y) ⟹ (framed_linkrel_diagram_left y x)"
 using framed_linkrel_def framed_linkrel_diagram_left_def by auto

lemma framed_symm_right: "(framed_linkrel_diagram_right x y) ⟹ (framed_linkrel_diagram_right y x)"
 using framed_linkrel_def framed_linkrel_diagram_right_def by auto

lemma framed_symm_center:"(framed_linkrel_diagram_center x y) ⟹ (framed_linkrel_diagram_center y x)"
 using framed_linkrel_def framed_linkrel_diagram_center_def by auto

lemma framed_symm_middle_right:
  "(framed_linkrel_diagram_middle_right x y) ⟹ (framed_linkrel_diagram_middle_right y x)"
     unfolding framed_linkrel_def framed_linkrel_diagram_middle_right_def 
     by (metis linkrel_symp sympD)

lemma framed_symm_middle_left:
  "(framed_linkrel_diagram_middle_left x y) ⟹ (framed_linkrel_diagram_middle_left y x)"
     unfolding framed_linkrel_def framed_linkrel_diagram_middle_left_def 
     by (metis linkrel_symp sympD)

lemma framed_symm_middle_center:
  "(framed_linkrel_diagram_middle_center x y) ⟹ (framed_linkrel_diagram_middle_center y x)"
        unfolding framed_linkrel_def framed_linkrel_diagram_middle_center_def
        by (metis linkrel_symp sympD)

lemma framed_symm_bottom_left: 
  "(framed_linkrel_diagram_bottom_left x y) ⟹ (framed_linkrel_diagram_bottom_left y x)"
        unfolding framed_linkrel_def framed_linkrel_diagram_bottom_left_def 
        by (metis linkrel_symp sympD)

lemma framed_symm_bottom_right: 
 "(framed_linkrel_diagram_bottom_right x y) ⟹ (framed_linkrel_diagram_bottom_right y x)"
        unfolding framed_linkrel_def framed_linkrel_diagram_bottom_right_def 
        by (metis linkrel_symp sympD)

lemma framed_symm_bottom_center:
  "(framed_linkrel_diagram_bottom_center x y) ⟹ (framed_linkrel_diagram_bottom_center y x)"
         unfolding framed_linkrel_def framed_linkrel_diagram_bottom_center_def 
         by (metis linkrel_symp sympD)

lemma framed_symm_top_left:
 "(framed_linkrel_diagram_top_left x y) ⟹ (framed_linkrel_diagram_top_left y x)"
         unfolding framed_linkrel_def framed_linkrel_diagram_top_left_def 
         by (metis linkrel_symp sympD)

lemma framed_symm_top_right: 
 "(framed_linkrel_diagram_top_right x y) ⟹ (framed_linkrel_diagram_top_right y x)"
         unfolding framed_linkrel_def framed_linkrel_diagram_top_right_def 
         by (metis linkrel_symp sympD)

lemma framed_symm_top_center:
 "(framed_linkrel_diagram_top_center x y) ⟹ (framed_linkrel_diagram_top_center y x)"
         unfolding framed_linkrel_def framed_linkrel_diagram_top_center_def 
         by (metis linkrel_symp sympD)

lemma  symm_framed_linkrel_diagram:
  "(framed_linkrel_diagram x y)⟹ (framed_linkrel_diagram y x)"
        unfolding framed_linkrel_diagram_def using framed_symm_bottom_center framed_symm_bottom_left 
                  framed_symm_center framed_symm_left framed_symm_middle_center 
                  framed_symm_middle_left framed_symm_middle_right framed_symm_right 
                  framed_symm_top_center framed_symm_top_left framed_symm_top_right
        by metis

(*framed_linkrel_diagram_equiv is the equivalence class of walls*)

definition framed_linkrel_diagram_equiv::"walls⇒ walls ⇒ bool"
where
"framed_linkrel_diagram_equiv = (framed_linkrel_diagram)^**"

(*Proof that the Framed_Linkrel_Diagram_Equiv is symmetric*)
lemma symm_framed_linkrel_diagram_equiv:
  "framed_linkrel_diagram_equiv x y ⟹ (framed_linkrel_diagram_equiv y x)"
      using framed_linkrel_diagram_equiv_def symm_framed_linkrel_diagram symmetry3 symp_def
      by metis

lemma transitive_implication:
 assumes " ∀x.∀y.((r x y) ⟶(q x y))"
 shows "r^** x y ⟹ q^** x y"
proof(induction rule:rtranclp.induct)
 fix a
 let ?case = "q⇧*⇧* a a"
   show ?case by simp
 next
 fix a b c
 assume rtranclp : "r^** a b" "r b c" "q^** a b"
 let ?case = "q^** a c"
   have "(r b c)⟹ (q b c)" using assms by auto
   from this have "q b c" using assms rtranclp by auto
   from this  have "q^** a c" using rtranclp(3) rtranclp.rtrancl_into_rtrancl by auto
   thus ?case by simp
qed

definition framed_link_equiv::"diagram⇒ diagram ⇒ bool"
where
"framed_link_equiv x y = (framed_linkrel_diagram_equiv (Rep_diagram x) (Rep_diagram y))"

lemma ref: "(framed_link_equiv x x)"
unfolding framed_link_equiv_def framed_linkrel_diagram_equiv_def by auto

lemma sym:"(framed_link_equiv x y) ⟹ (framed_link_equiv y x)"
unfolding framed_link_equiv_def using symm_framed_linkrel_diagram_equiv  by auto

lemma trans:"(framed_link_equiv x y)∧ (framed_link_equiv y z) ⟹ (framed_link_equiv x z)"
using framed_link_equiv_def framed_linkrel_diagram_equiv_def rtranclp_trans by (metis)


quotient_type Framed_Link = "diagram" / "framed_link_equiv"
 morphisms Rep_framed_links Abs_framed_links
proof (rule equivpI)
show "reflp framed_link_equiv" 
   using reflp_def  framed_link_equiv_def framed_linkrel_diagram_equiv_def rtranclp.rtrancl_refl
   by (metis (full_types))
show "symp framed_link_equiv"
   using  framed_link_equiv_def symm_framed_linkrel_diagram_equiv symp_def
   by (metis)
show "transp framed_link_equiv"
   using trans unfolding framed_link_equiv_def transp_def by metis
qed

(*It remains to be proved that Framed_Link_Equiv implies Link_Equiv*)
(*Some junk code but needs to be relooked - 
(* we need to rewrite the definitions of framed_link_relations and repeat the above for framed_link_relations
definition framed_linkrel::"walls =>walls⇒bool"
where
"framed_linkrel x y = ((framed_linkrel_uncross x y) ∨ (linkrel_pull x y) ∨ (linkrel_straighten x y) 
∨(linkrel_swing x y)∨(linkrel_rotate x y) ∨ (linkrel_compress x y) ∨ (linkrel_slide x y)
∨  (framed_linkrel_uncross y x) ∨ (linkrel_pull y x) ∨ (linkrel_straighten y x) 
∨(linkrel_swing y x)∨(linkrel_rotate y x) ∨ (linkrel_compress y x) ∨ (linkrel_slide y x))"

text{*Following lemmas asserts that if two framed linked diagrams are equivalent, then the unframed 
links are equivalent*}

lemma framed_linkrel_implies_linkrel: "(framed_linkrel x y) ⟹ (linkrel x y)"
using framed_uncross_implies_uncross framed_linkrel_def linkrel_def by auto

text{* the link relations are symmetric*}
lemma linkrel_symp: "symp linkrel" unfolding linkrel_def symp_def by auto

lemma framed_linkrel_symp: "symp framed_linkrel" unfolding framed_linkrel_def symp_def by auto


definition framed_linkrel_equiv::"walls⇒walls⇒bool"
where
"(framed_linkrel_equiv) = (framed_linkrel)^**" 
 
text{*Following lemmas assert that if two framed link diagrams are related by the linkrel_equiv, then 
the corresponding link diagrams are equivalent*}

lemma transitive_implication:
assumes " ∀x.∀y.((r x y) ⟶(q x y))"
shows "r^** x y ⟹ q^** x y"
proof(induction rule:rtranclp.induct)
fix a
let ?case = "q⇧*⇧* a a"
show ?case by simp
next
fix a b c
assume rtranclp : "r^** a b" "r b c" "q^** a b"
let ?case = "q^** a c"
have "(r b c)⟹ (q b c)" using assms by auto
from this have "q b c" using assms rtranclp by auto
from this  have "q^** a c" using rtranclp(3) rtranclp.rtrancl_into_rtrancl by auto
thus ?case by simp
qed

theorem framed_equiv_implies_linkequiv: "(framed_linkrel_equiv x y) ⟹ (linkrel_equiv x y)"
using  framed_linkrel_equiv_def linkrel_equiv_def transitive_implication  
framed_linkrel_implies_linkrel
by metis
text{*Linkrel_equiv and Framed_Linkrel_equiv are  equivalence relations*}

lemma reflective: "linkrel_equiv x x" unfolding linkrel_equiv_def by simp

lemma framed_reflective: "framed_linkrel_equiv x x" unfolding framed_linkrel_equiv_def by simp

lemma link_symmetry:"symp linkrel_equiv" using linkrel_symp symmetry3 
by (metis (full_types) linkrel_equiv_def)


lemma link_symmetry2:"(linkrel_equiv x y)⟹ (linkrel_equiv y x)" using link_symmetry sympD
 by metis

lemma framed_link_symmetry:"symp framed_linkrel_equiv" using framed_linkrel_symp symmetry3 
by (metis (full_types) framed_linkrel_equiv_def)

(*following lemma proves that linkrel_equiv is transitive in the usual sense of the term*)
lemma linkrel_trans: assumes "linkrel_equiv x y" and "linkrel_equiv y z"
shows "linkrel_equiv x z"
using rtranclp_trans linkrel_equiv_def  by (metis (full_types) assms(1) assms(2))
*)*)
end
