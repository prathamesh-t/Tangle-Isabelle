theory Link_Algebra
imports Tangles Tangle_Algebra Links
begin

text{*We use locales to describe the axiomatic properties of the empty brick, which state that
empty brick commutes with regards to the tensor product. This properties holds true in the locale
empty_tensor*}

locale empty_tensor=
 fixes rel::"walls \<Rightarrow> walls \<Rightarrow> bool" (infixl "~" 65)
assumes left: "(x \<otimes> (basic (cement empty))) ~ x"
    and right:"((basic (cement empty)) \<otimes> x) ~ x"
context empty_tensor
 begin

text{*The fact that this property holds true for tensor between walls implies that it holds true 
for blocks *}
(*
theorem left_concatenate:"(x::block) \<otimes> (cement empty) = x"
proof-
have "(basic x) \<otimes> (basic (cement empty)) = (basic x)" using left by auto
then have "(basic (x \<otimes> (cement empty))) = (basic x)" by auto
then have "(x \<otimes> (cement empty)) = x" by auto
then show ?thesis by auto
qed


theorem right_concatenate: "(cement empty) \<otimes> x = x"
proof-
have "(basic (cement empty)) \<otimes> (basic x) = (basic x)" using right by metis
then have "(basic ((cement empty) \<otimes> x)) = (basic x)" by auto
then have "((cement empty) \<otimes> x) = x" by auto
then show ?thesis by auto
qed

text{*The property inherited at the level of construction of blocks*}

theorem left_empty_block:"(empty#(x::block)) = x"
proof-
have "(empty#x) = (cement empty) \<otimes> x" using concatenate_def by auto
with right_concatenate have "(empty#x) = x" by auto
then show ?thesis by auto
qed

theorem right_empty_block:"((x::brick)#(cement empty)) = cement x"
proof-
have "(x#(cement empty)) = (cement x) \<otimes> (cement empty)" using concatenate_def by auto
with left_concatenate have "(x#(cement empty)) = (cement x)" by auto
then show ?thesis by auto
qed
end
*)
end
text{* It is assumed in the following locale that the composition of a wall with the empty wall 
returns the same wall*}

locale empty_compose = empty_tensor + 
assumes domain_compose: "(domain_wall x = 0) \<Longrightarrow>(basic (cement empty)) \<circ> x ~ x"
and codomain_compose: "(codomain_wall x = 0) \<Longrightarrow>(x \<circ> (basic (cement empty))) ~  x"

text{*If two walls are related by linkrel, then they give rise to the same tangles in this locale*}

locale Equivalence = empty_tensor + empty_compose+
 assumes equality:"linkrel x y \<Longrightarrow> x ~ y"
 assumes "((B::walls) ~ D) \<and> ((A::walls) ~ C)
         \<and>(well_defined_tangle A)\<and>(well_defined_tangle B)
         \<and>(well_defined_tangle C)\<and>(well_defined_tangle D) 
         \<and>(domain_wall B)= (codomain_wall A)
         \<and>(domain_wall D)= (codomain_wall C)
                \<Longrightarrow>((A::walls) \<circ> B) ~ (C \<circ> D)"
 assumes tensor_eq:"((B::walls) ~ D) \<and> ((A::walls) ~ C) \<and>(well_defined_tangle A)\<and>(well_defined_tangle B)
 \<and>(well_defined_tangle C)\<and>(well_defined_tangle D) \<Longrightarrow>((A::walls) \<otimes> B) ~ (C \<otimes> D)"
 assumes refl:"A ~A"
 assumes sym:"A~B \<Longrightarrow> B~A"
 assumes trans:" (A~B) \<and> (B~C) \<Longrightarrow> (A~C)"

locale Tangle_Equivalence = Equivalence +
 fixes tangle_equivalence::"Tangle \<Rightarrow> Tangle \<Rightarrow> bool" (infixl "~" 65) 
 assumes Tangle_equality:"(x ~ y) \<Longrightarrow> ((Abs_Tangle x) ~ (Abs_Tangle y))"
 begin


lemma assumes "linkrel A B"
shows "Abs_Tangle A ~ Abs_Tangle B" using equality assms Tangle_equality by auto


text{*definition of a link as a boolean function*}

definition Link::"Tangle \<Rightarrow> bool"
where
 "Link x \<equiv> (well_defined (Rep_Tangle x))"

definition Equivalent_Links::"Tangle \<Rightarrow> Tangle  \<Rightarrow> bool"
where
"Equivalent_Links x y \<equiv> (Link x) \<and> (Link y) \<and> (x = y)"


lemma "basic (cement empty) = (basic (cement empty)) \<circ> (basic (cement empty))"
 by (metis domain.simps(6) domain_block.simps(1) domain_compose domain_wall.simps(1))
end

sublocale Tangle_Equivalence < Equivalence
 by unfold_locales 

locale Tangle_Invariant = Equivalence +
fixes funct::"walls \<Rightarrow> 'a" 
assumes "(x = y) \<Longrightarrow> (funct x) = (funct y)"

end

