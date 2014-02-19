theory Link_Algebra
imports Tangles Tangle_Algebra Links
begin

locale empty_tensor=
assumes left: "x \<otimes> (basic (cement empty)) = x"
and right:"(basic (cement empty)) \<otimes> x = x"
context empty_tensor
 begin

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
  
locale empty_compose = 
assumes domain_compose: "(domain_wall x = 0) \<Longrightarrow>(basic (cement empty)) \<circ> x =  x"
and codomain_compose: "(codomain_wall x = 0) \<Longrightarrow>(x \<circ> (basic (cement empty))) =  x"

locale Tangle = empty_tensor+empty_compose+
assumes
well_defined: "well_defined x"
begin

lemma "domain_wall x =0"
  using  Tangles.abs_zero well_defined well_defined_snd_wall_count
  by (metis)
end

locale Equivalence = Tangle +
 assumes "linkrel x y \<Longrightarrow> x = y"

locale Moves = Equivalence + 
  assumes "(B = D) \<and> (A = C) \<Longrightarrow>((A::walls) \<circ> B) = (C \<circ> D)"
  and "(B = D) \<and> (A = C) \<Longrightarrow>((A::walls) \<otimes> B) = (C \<otimes> D)"

locale Links = Moves + 
  assumes "well_defined x"
begin
lemma "basic (cement empty) = (basic (cement empty)) \<circ> (basic (cement empty))"
 by (metis domain.simps(6) domain_block.simps(1) domain_compose domain_wall.simps(1))
end

locale invariant = Links +
fixes funct::"walls \<Rightarrow> 'a" 
assumes "(x = y) \<Longrightarrow> (funct x) = (funct y)"


end
