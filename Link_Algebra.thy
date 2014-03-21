theory Link_Algebra
imports Tangles Tangle_Algebra Links
begin
(*
text{*We use locales to describe the axiomatic properties of the empty brick, which state that
empty brick commutes with regards to the tensor product. This properties holds true in the locale
empty_tensor*}
text{* It is assumed in the following locale that the composition of a wall with the empty wall 
returns the same wall*}



locale empty_compose = 
 fixes rel::"wall \<Rightarrow> wall \<Rightarrow> bool" (infixl "~" 65)
assumes domain_compose: "(domain_wall x = 0) \<Longrightarrow>(basic []) \<circ> x ~ x"
and codomain_compose: "(codomain_wall x = 0) \<Longrightarrow>(x \<circ> (basic [])) ~  x"

text{*If two wall are related by linkrel, then they give rise to the same tangles in this locale*}

locale Equivalence = empty_compose+
 assumes equality:"linkrel x y \<Longrightarrow> x ~ y"
 assumes compose_eq: "((B::wall) ~ D) \<and> ((A::wall) ~ C)
         \<and>(is_tangle_diagram A)\<and>(is_tangle_diagram B)
         \<and>(is_tangle_diagram C)\<and>(is_tangle_diagram D) 
         \<and>(domain_wall B)= (codomain_wall A)
         \<and>(domain_wall D)= (codomain_wall C)
                \<Longrightarrow>((A::wall) \<circ> B) ~ (C \<circ> D)"
 assumes tensor_eq:"((B::wall) ~ D) \<and> ((A::wall) ~ C) \<and>(is_tangle_diagram A)\<and>(is_tangle_diagram B)
 \<and>(is_tangle_diagram C)\<and>(is_tangle_diagram D) \<Longrightarrow>((A::wall) \<otimes> B) ~ (C \<otimes> D)"
 assumes refl:"A ~A"
 assumes sym:"A~B \<Longrightarrow> B~A"
 assumes trans: "transp rel"
begin

lemma transitivity:
assumes "A~ B" and "B~C" shows "A~C"
 using trans assms by (metis transp_def)
 (*
lemma "(x ~ y)\<and> (is_tangle_diagram x) \<Longrightarrow> is_tangle_diagram y"
 sledgehammer
*)
lemma "((B::wall) ~ D) \<and> ((A::wall) ~ C) \<and>(is_tangle_diagram A)\<and>(is_tangle_diagram B)
 \<and>(is_tangle_diagram C)\<and>(is_tangle_diagram D)  \<Longrightarrow> is_tangle_diagram (A \<otimes> B)\<and>  is_tangle_diagram (C \<otimes> D)"
   by (metis is_tangle_diagramness)

end

locale Tangle_Equivalence = Equivalence +
 fixes tangle_equivalence::"Tangle_Diagram \<Rightarrow> Tangle_Diagram \<Rightarrow> bool" (infixl "~" 65) 
 assumes Tangle_equality:"(x ~ y) = ((Abs_Tangle_Diagram x) ~ (Abs_Tangle_Diagram y))"
 begin


lemma assumes "linkrel A B"
shows "(Abs_Tangle_Diagram A) ~ (Abs_Tangle_Diagram B)" 
     using equality assms Tangle_equality by auto


text{*definition of a link as a boolean function*}
(*modify this*)
definition Link::"Tangle_Diagram \<Rightarrow> bool"
where
 "Link x \<equiv> ((abs (domain_wall (Rep_Tangle_Diagram x)) + abs (codomain_wall (Rep_Tangle_Diagram x))) = 0)"

definition Equivalent_Links::"Tangle_Diagram \<Rightarrow> Tangle_Diagram  \<Rightarrow> bool"
where
"Equivalent_Links x y \<equiv> (Link x) \<and> (Link y) \<and> (x ~ y)"

lemma domain_wall_empty:"domain_wall (basic []) = 0"
  by auto

lemma "basic ([]) \<circ> (basic ([])) ~ basic ([]) "
  using domain_block.simps(1) domain_compose domain_wall.simps(1) by auto
  
end

sublocale Tangle_Equivalence < Equivalence
 by unfold_locales 


locale Tangle_Invariant = Equivalence +
fixes funct::"wall \<Rightarrow> 'a" 
assumes invariance:"(rel x y) \<Longrightarrow> (funct x) = (funct y)"
begin

lemma "((funct x) \<noteq> (funct y)) \<longrightarrow> \<not> (x ~ y)" 
    using invariance by auto

end
*)

inductive Tangle_Equivalence :: "wall \<Rightarrow> wall  \<Rightarrow> bool"   (infixl "~" 64)
where
  refl [intro!, Pure.intro!, simp]: " a ~  a"
 |equality [Pure.intro]: "linkrel a b \<Longrightarrow>  a ~ b"
 |domain_compose:"(domain_wall a = 0) \<Longrightarrow>  a ~  ((basic empty_block)\<circ>a)"
 |codomain_compose:"(codomain_wall a = 0) \<Longrightarrow> a ~ (a \<circ> (basic empty_block))"
 |compose_eq:"((B::wall) ~ D) \<and> ((A::wall) ~ C)
         \<and>(is_tangle_diagram A)\<and>(is_tangle_diagram B)
         \<and>(is_tangle_diagram C)\<and>(is_tangle_diagram D) 
         \<and>(domain_wall B)= (codomain_wall A)
         \<and>(domain_wall D)= (codomain_wall C)
                \<Longrightarrow>((A::wall) \<circ> B) ~ (C \<circ> D)"
 |trans: "A~B \<Longrightarrow> B~C \<Longrightarrow> A ~ C"
 |sym:"A~ B \<Longrightarrow> B ~C"
 |tensor_eq: "((B::wall) ~ D) \<and> ((A::wall) ~ C) \<and>(is_tangle_diagram A)\<and>(is_tangle_diagram B)
 \<and>(is_tangle_diagram C)\<and>(is_tangle_diagram D) \<Longrightarrow>((A::wall) \<otimes> B) ~ (C \<otimes> D)" 

end


