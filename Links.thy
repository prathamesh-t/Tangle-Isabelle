theory Links
imports Tangles Tangle_Algebra tangle_relation
begin


text{* Two Links diagrams represent the same link if and only if the diagrams can be related by a 
set of moves called the reidemeister moves. For links defined through Tangles, addition set of moves 
are needed to account for different tangle representations of the same link diagram.

We formalise these 'moves' in terms of relations. Each move is defined as a relation on diagrams. 
Two diagrams are then stated to be equivalent if the reflexive-symmetric-transitive closure of the 
disjunction of above relations holds true. A Link is defined as an element of the quotient type of
diagrams modulo equivalence relations. We formalise the definition of framed links on similar lines. 

In terms of formalising the moves, there is a trade off between choosing a small number of moves
from which all other moves can be obtained, which is conducive to probe invariance of a function 
on diagrams. However, such an approach might not be conducive to establish equivalence of two 
diagrams. We opt for the former approach of minimising the number of tangle moves. 
However, the moves that would be useful in practise are proved as theorems in
 Link_Equivalence_Theorems.thy *}

text{*link_uncross*}


definition linkrel_uncross_positiveflip::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_uncross_positiveflip x y \<equiv> (x =  (basic ((cement vert)\<otimes>(cement cup)))
                                           \<circ>(basic ((cement over)\<otimes>(cement vert)))
                                           \<circ>(basic ((cement vert)\<otimes>(cement cap))))
                                    \<and> (y = ((basic ((cement cup)\<otimes>(cement vert)))
                                            \<circ>(basic ((cement vert)\<otimes>(cement over)))
                                            \<circ>(basic ((cement cap)\<otimes>(cement vert)))))"


definition linkrel_uncross_positivestraighten::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_uncross_positivestraighten x y \<equiv> ((x = (basic ((cement cup)\<otimes>(cement vert)))
                                               \<circ>(basic ((cement vert)\<otimes>(cement over)))
                                               \<circ>(basic ((cement cap)\<otimes>(cement vert))))
                                      \<and>(y = (basic (cement vert))
                                           \<circ>(basic (cement vert))
                                           \<circ>(basic (cement vert))))"

definition linkrel_uncross_negativeflip::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_uncross_negativeflip x y \<equiv> (x =  (basic ((cement vert)\<otimes>(cement cup)))
                                           \<circ>(basic ((cement under)\<otimes>(cement vert)))
                                           \<circ>(basic ((cement vert)\<otimes>(cement cap))))
                                    \<and> (y = ((basic ((cement cup)\<otimes>(cement vert)))
                                            \<circ>(basic ((cement vert)\<otimes>(cement under)))
                                            \<circ>(basic ((cement cap)\<otimes>(cement vert)))))"
definition linkrel_uncross_negativestraighten::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_uncross_negativestraighten x y \<equiv> ((x = (basic ((cement cup)\<otimes>(cement vert)))
                                               \<circ>(basic ((cement vert)\<otimes>(cement under)))
                                               \<circ>(basic ((cement cap)\<otimes>(cement vert))))
                                      \<and>(y = (basic (cement vert))
                                           \<circ>(basic (cement vert))
                                           \<circ>(basic (cement vert))))"

text{*link_uncross definition*}
definition linkrel_uncross::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_uncross x y \<equiv> 
((linkrel_uncross_positiveflip x y)\<or>(linkrel_uncross_positivestraighten x y)
\<or>(linkrel_uncross_negativeflip x y)\<or>(linkrel_uncross_negativestraighten x y))"
text{*link_uncross ends*}

text{*framed linkrel_uncross*}

definition framed_linkrel_uncross::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"framed_linkrel_uncross x y \<equiv> 
((linkrel_uncross_positiveflip x y)\<or>(linkrel_uncross_negativeflip x y))"

lemma framed_uncross_implies_uncross: "(framed_linkrel_uncross x y) \<Longrightarrow> (linkrel_uncross x y)"
apply (simp add: framed_linkrel_uncross_def linkrel_uncross_def)
apply(auto)
done

text{*link_pull begins*}

definition linkrel_pull_posneg::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_pull_posneg x y \<equiv>  ((x = ((basic (cement over))\<circ>(basic  (cement under))))
                            \<and>(y = ((basic ((cement vert)\<otimes>(cement vert)))
                                   \<circ>(basic ((cement vert)\<otimes>(cement vert))))))"


definition linkrel_pull_negpos::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_pull_negpos x y \<equiv>  ((x = ((basic (cement under))\<circ>(basic  (cement over))))
                            \<and>(y = ((basic ((cement vert)\<otimes>(cement vert)))
                                   \<circ>(basic ((cement vert)\<otimes>(cement vert))))))"

text{*linkrel_pull definition*}
definition linkrel_pull::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_pull x y \<equiv> ((linkrel_pull_posneg x y) \<or> (linkrel_pull_negpos x y))"                   

text{*linkrel_pull ends*}    
text{*linkrel_straighten*}

definition linkrel_straighten_topdown::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_straighten_topdown x y \<equiv>  ((x =((basic ((cement vert)\<otimes>(cement cup)))
                                         \<circ>(basic ((cement cap)\<otimes>(cement vert)))))
                                   \<and>(y = ((basic (cement vert))\<circ>(basic (cement vert)))))"



definition linkrel_straighten_downtop::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_straighten_downtop x y \<equiv>  ((x =((basic ((cement cup)\<otimes>(cement vert)))
                                         \<circ>(basic ((cement vert)\<otimes>(cement cap)))))
                                   \<and>(y = ((basic (cement vert))\<circ>(basic (cement vert)))))"




text{*definition straighten*}
definition linkrel_straighten::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_straighten x y \<equiv> ((linkrel_straighten_topdown x y) \<or> (linkrel_straighten_downtop x y))"



text{*straighten ends*}
text{*swing begins*}
definition linkrel_swing_pos::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_swing_pos x y \<equiv> ((x = ((basic ((cement over)\<otimes>(cement vert))\<circ>(basic ((cement vert)\<otimes>(cement over)))
                               \<circ>(basic ((cement over)\<otimes>(cement vert))))))
                         \<and>(y = (basic ((cement vert)\<otimes>(cement over))\<circ>(basic ((cement over)\<otimes>(cement vert)))
                                \<circ>(basic ((cement vert)\<otimes>(cement over))))))"

definition linkrel_swing_neg::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_swing_neg x y \<equiv> ((x = ((basic ((cement under)\<otimes>(cement vert))\<circ>(basic ((cement vert)\<otimes>(cement under)))
                               \<circ>(basic ((cement under)\<otimes>(cement vert))))))
                         \<and>(y = (basic ((cement vert)\<otimes>(cement under))\<circ>(basic ((cement under)\<otimes>(cement vert)))
                                \<circ>(basic ((cement vert)\<otimes>(cement under))))))"

text{*swing definition*}

definition linkrel_swing::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_swing x y \<equiv> ((linkrel_swing_pos x y) \<or> (linkrel_swing_neg x y))"

text{*swing ends*}
text{* rotate moves*}

definition linkrel_rotate_toppos::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_rotate_toppos x y \<equiv>  ((x = ((basic ((cement vert)\<otimes>(cement over)))
                                     \<circ>(basic ((cement cap)\<otimes>(cement vert)))))
                             \<and> (y = ((basic ((cement under)\<otimes>(cement vert))
                                     \<circ>(basic ((cement vert)\<otimes>(cement cap)))))))"

definition linkrel_rotate_topneg::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_rotate_topneg x y \<equiv> ((x = ((basic ((cement vert)\<otimes>(cement under)))
                                     \<circ>(basic ((cement cap)\<otimes>(cement vert)))))
                             \<and> (y = ((basic ((cement over)\<otimes>(cement vert))
                                     \<circ>(basic ((cement vert)\<otimes>(cement cap)))))))"


definition linkrel_rotate_downpos::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_rotate_downpos x y \<equiv>  ((x = ((basic ((cement cap)\<otimes>(cement vert)))
                                     \<circ>(basic ((cement vert)\<otimes>(cement over)))))
                             \<and> (y = ((basic ((cement vert)\<otimes>(cement cap)))
                                    \<circ>(basic ((cement under)\<otimes>(cement vert))))))"



definition linkrel_rotate_downneg::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_rotate_downneg x y \<equiv>  ((x = ((basic ((cement cap)\<otimes>(cement vert)))
                                     \<circ>(basic ((cement vert)\<otimes>(cement under)))))
                             \<and> (y = ((basic ((cement vert)\<otimes>(cement cap)))
                                    \<circ>(basic ((cement over)\<otimes>(cement vert))))))"


text{*rotate definition*}


definition linkrel_rotate::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_rotate x y \<equiv> ((linkrel_rotate_toppos x y) \<or> (linkrel_rotate_topneg x y)
\<or> (linkrel_rotate_downpos x y) \<or> (linkrel_rotate_downneg x y))"

text{*rotate ends*}


text{*Compress -  Compress has two levels of equivalences. It is a composition of Compress_null, compbelow
and compabove. compbelow and compabove are further written as disjunction of many other relations.
Compbelow refers to when the bottom row is extended or compressed. Compabove refers to when the 
row above is extended or compressed*}

definition linkrel_compress_top::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_compress_top x y \<equiv>  \<exists>B.((x = (basic (make_vert_block (nat (domain_wall B - 1))))\<circ> B)
                              \<and>(y = (B \<circ> (basic (cement empty))))\<and>(codomain_wall B = 0))"


definition linkrel_compress_bottom::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_compress_bottom x y \<equiv>   \<exists>B.((x = B \<circ> (basic (make_vert_block (nat (domain_wall B - 1)))))
                              \<and>(y = ((basic (cement empty) \<circ> B)))\<and>(domain_wall B = 0))"
(*linkrel_compress*)
definition linkrel_compress::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_compress x y = ((linkrel_compress_top x y) \<or> (linkrel_compress_bottom x y))"

text{*slide relation refer to the relation where a crossing is slided over a vertical strand*}
definition linkrel_slide::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_slide x y \<equiv>  \<exists>B.((x = ((basic (make_vert_block (nat (domain_block B - 1))))\<circ>(basic B)))
               \<and>(y = ((basic B)\<circ>(basic (make_vert_block (nat (domain_block B - 1)))))))"

text{*empty compose-operation*}
definition linkrel_empty_compose_top::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_empty_compose_top x y \<equiv> (x = (y \<circ> (basic (cement empty))))\<and> (codomain_wall y = 0)"


definition linkrel_empty_compose_bottom::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_empty_compose_bottom x y \<equiv> (x = ((basic (cement empty)) \<circ> y))\<and> (domain_wall y = 0)"

definition linkrel_empty_compose::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_empty_compose x y \<equiv> (linkrel_empty_compose_top x y) \<or> (linkrel_empty_compose_bottom x y)"
text{*empty tensor-operation*}
definition linkrel_empty_tensor_left::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_empty_tensor_left x y \<equiv> (x = (basic (cement empty) \<otimes> y))"


definition linkrel_empty_tensor_right ::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_empty_tensor_right x y \<equiv> (x = ( y \<otimes> (basic (cement empty))))"


definition linkrel_empty_tensor::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_empty_tensor x y \<equiv> (linkrel_empty_tensor_left x y) \<or> (linkrel_empty_tensor_right x y)"


(*still working on- would tensor between walls suffice for this definition needs to be checked*)
(*reflexivity*)
definition linkrel_reflexive::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_reflexive x y \<equiv> (x = y)"


text{*linkrel_definition*}

definition linkrel::"walls =>walls \<Rightarrow>bool"
where
"linkrel x y = ((linkrel_uncross x y) \<or> (linkrel_pull x y) \<or> (linkrel_straighten x y) 
\<or>(linkrel_swing x y)\<or>(linkrel_rotate x y) \<or> (linkrel_compress x y) \<or> (linkrel_slide x y)
\<or>(linkrel_empty_compose x y)\<or>(linkrel_empty_tensor x y)
\<or>  (linkrel_uncross y x) \<or> (linkrel_pull y x) \<or> (linkrel_straighten y x) 
\<or>(linkrel_swing y x)\<or>(linkrel_rotate y x) \<or> (linkrel_compress y x) \<or> (linkrel_slide y x)
\<or>(linkrel_empty_compose y x)\<or> (linkrel_empty_tensor y x)
\<or> (linkrel_reflexive x y))"


text{* the link relations are symmetric*}
lemma linkrel_symp: "symp linkrel" unfolding linkrel_def symp_def linkrel_reflexive_def by auto

(*linkrel fitting in diagrams*)
definition linkrel_diagram_compose::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_diagram_compose x y \<equiv>\<exists>A1.\<exists>B1.\<exists>A2.\<exists>B2.(x = A1 \<circ> B1)\<and>(y = A2 \<circ> B2)\<and>(linkrel A1 A2)\<and>(linkrel B1 B2)"


definition linkrel_diagram_tensor::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_diagram_tensor x y \<equiv>\<exists>A1.\<exists>B1.\<exists>A2.\<exists>B2.(x = A1 \<otimes> B1)\<and>(y = A2 \<otimes> B2)\<and>(linkrel A1 A2)\<and>(linkrel B1 B2)"

(*proving symmetry of linkrel_diagram*)
definition linkrel_diagram::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_diagram x y \<equiv> (linkrel_diagram_compose x y) \<or> (linkrel_diagram_tensor x y)"

lemma symp_linkrel_diagram_compose: "symp linkrel_diagram_compose" 
unfolding linkrel_diagram_compose_def linkrel_symp  symp_def by (metis linkrel_symp symp_def)
lemma symp_linkrel_diagram_tensor: "symp linkrel_diagram_tensor"
unfolding symp_def linkrel_diagram_tensor_def linkrel_symp by (metis linkrel_symp symp_def)

lemma symm_linkrel_diagram:"(linkrel_diagram x y)\<Longrightarrow> (linkrel_diagram y x)"
 using linkrel_diagram_def sympE symp_linkrel_diagram_compose symp_linkrel_diagram_tensor
 by metis


(*linkrel_diagram fitting in links*)

definition linkrel_diagram_equiv::"walls\<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_diagram_equiv = (linkrel_diagram)^**"

lemma symm_linkrel_diagram_equiv:"linkrel_diagram_equiv x y \<Longrightarrow> (linkrel_diagram_equiv y x)"
      using linkrel_diagram_equiv_def symm_linkrel_diagram symmetry3 symp_def
      by metis

definition link_equiv::"diagram\<Rightarrow> diagram \<Rightarrow> bool"
where
"link_equiv x y = (linkrel_diagram_equiv (Rep_diagram x) (Rep_diagram y))"

lemma "(link_equiv x x)"
unfolding link_equiv_def linkrel_diagram_equiv_def by auto

lemma "(link_equiv x y) \<Longrightarrow> (link_equiv y x)"
unfolding link_equiv_def using symm_linkrel_diagram_equiv by auto

lemma "(link_equiv x y)\<and> (link_equiv y z) \<Longrightarrow> (link_equiv x z)"
using link_equiv_def linkrel_diagram_equiv_def rtranclp_trans by (metis)

text{*we defined the link relations for a framed link, which are the same as those of unframed 
links excluding the uncross relation which straightens out a cross*}

text{*links upto equivalence are well defined*}
text{*Link- Definition and the proof of being well defined*}

quotient_type Link = "diagram" / "link_equiv"
 morphisms Rep_links Abs_links
proof (rule equivpI)
show "reflp link_equiv" unfolding reflp_def using link_equiv_def linkrel_diagram_equiv_def rtranclp.rtrancl_refl
  by (metis (full_types) )
show "symp link_equiv" by (metis link_equiv_def symm_linkrel_diagram_equiv sympI)
show "transp link_equiv" unfolding transp_def link_equiv_def rtranclp_trans by (metis linkrel_diagram_equiv_def rtranclp_trans) 
qed

end

