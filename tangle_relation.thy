theory tangle_relation
imports Datatype Main
begin



lemma symmetry1: assumes "symp R" 
shows "∀x y. (x, y) ∈ {(x, y). R x y}⇧* ⟶ (y, x) ∈ {(x, y). R x y}⇧*" 
proof-
have  "R x y ⟶  R y x" by (metis assms sympD)
then have " (x, y) ∈ {(x, y). R x y} ⟶ (y, x) ∈ {(x, y). R x y}" by auto
then have 2:"∀ x y. (x, y) ∈ {(x, y). R x y} ⟶ (y, x) ∈ {(x, y). R x y}"
 by (metis (full_types) assms mem_Collect_eq split_conv sympE)
then have "sym {(x, y). R x y}" unfolding sym_def by auto
then have 3: "sym (rtrancl {(x, y). R x y})" using sym_rtrancl by auto
then show ?thesis by (metis symE)
qed

lemma symmetry2: assumes "∀x y. (x, y) ∈ {(x, y). R x y}⇧* ⟶ (y, x) ∈ {(x, y). R x y}⇧* "
shows "symp R^**" 
unfolding symp_def Enum.rtranclp_rtrancl_eq assms by (metis assms)

lemma symmetry3: assumes "symp R" shows "symp R^**" using assms symmetry1 symmetry2 by metis
(*
lemma invariance: assumes "R x y ⟹ (f x = f y)" shows "R^** x y ⟹ (f x = f y)" unfolding Enum.rtranclp_rtrancl_eq 
sledgehammer*)
end
