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


type_synonym relation = "walls \<Rightarrow> walls \<Rightarrow> bool" 

text{* Link uncross*}
abbreviation right_over::"walls"
where
"right_over \<equiv> ((basic ((cement vert)\<otimes>(cement cup))) \<circ> (basic ((cement over)\<otimes>(cement vert)))
\<circ> (basic ((cement vert)\<otimes> (cement cap))))"

abbreviation left_over::"walls"
where
" left_over \<equiv> ((basic ((cement cup)\<otimes>(cement vert))) \<circ> (basic ((cement vert)\<otimes>(cement over)))
\<circ> (basic ((cement cap)\<otimes> (cement vert))))"

abbreviation right_under::"walls"
where
"right_under \<equiv>  ((basic ((cement vert)\<otimes>(cement cup))) \<circ> (basic ((cement under)\<otimes>(cement vert)))
\<circ> (basic ((cement vert)\<otimes> (cement cap))))"

abbreviation left_under::"walls"
where
"left_under \<equiv>  ((basic ((cement cup)\<otimes>(cement vert))) \<circ> (basic ((cement vert)\<otimes>(cement under)))
\<circ> (basic ((cement cap)\<otimes> (cement vert))))"

abbreviation straight_line::"walls"
where
"straight_line \<equiv> (basic (cement vert)) \<circ> (basic (cement vert)) \<circ> (basic (cement vert))"

definition uncross_positive_flip::relation
where
"uncross_positive_flip x y \<equiv> ((x = right_over)\<and>(y =  left_over))"

definition uncross_positive_straighten::relation
where
"uncross_positive_straighten x y \<equiv> ((x = right_over)\<and>(y = straight_line))"

definition uncross_negative_flip::relation
where
"uncross_negative_flip x y \<equiv> ((x = right_under)\<and>(y =  left_under))"


definition uncross_negative_straighten::relation
where
"uncross_negative_straighten x y \<equiv> ((x = right_over)\<and>(y = straight_line))"

(*The relation uncross*)
definition uncross::relation
where
"uncross x y \<equiv> ((uncross_positive_straighten x y)\<or>(uncross_positive_flip x y)
                \<or>(uncross_positive_straighten x y)\<or> (uncross_negative_flip x y))"



text{*swing begins*}

abbreviation r_over_braid::"walls"
where
"r_over_braid  \<equiv>  ((basic ((cement over)\<otimes>(cement vert))\<circ>(basic ((cement vert)\<otimes>(cement over)))
                 \<circ>(basic ((cement over)\<otimes>(cement vert)))))"



abbreviation l_over_braid::"walls"
where
"l_over_braid  \<equiv>   (basic ((cement vert)\<otimes>(cement over))\<circ>(basic ((cement over)\<otimes>(cement vert)))
                    \<circ>(basic ((cement vert)\<otimes>(cement over))))"


abbreviation r_under_braid::"walls"
where
"r_under_braid  \<equiv>  ((basic ((cement under)\<otimes>(cement vert))\<circ>(basic ((cement vert)\<otimes>(cement under)))
                 \<circ>(basic ((cement under)\<otimes>(cement vert)))))"

abbreviation l_under_braid::"walls"
where
"l_under_braid  \<equiv>   (basic ((cement vert)\<otimes>(cement under))\<circ>(basic ((cement under)\<otimes>(cement vert)))
                    \<circ>(basic ((cement vert)\<otimes>(cement under))))"

definition swing_pos::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"swing_pos x y \<equiv> (x = r_over_braid)\<and>(y = l_over_braid)"

definition swing_neg::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"swing_neg x y \<equiv>(x = r_under_braid)\<and>(y=l_under_braid)"

definition swing::relation
where
"swing x y \<equiv> (swing_pos x y)\<or>(swing_neg x y)"

text{*pull begins*}

definition pull_posneg::relation
where
"pull_posneg x y \<equiv>  ((x = ((basic (cement over))\<circ>(basic  (cement under))))
                            \<and>(y = ((basic ((cement vert)\<otimes>(cement vert)))
                                   \<circ>(basic ((cement vert)\<otimes>(cement vert))))))"


definition pull_negpos::relation
where
"pull_negpos x y \<equiv>  ((x = ((basic (cement under))\<circ>(basic  (cement over))))
                            \<and>(y = ((basic ((cement vert)\<otimes>(cement vert)))
                                   \<circ>(basic ((cement vert)\<otimes>(cement vert))))))"

text{* pull definition*}
definition pull::relation
where
"pull x y \<equiv> ((pull_posneg x y) \<or> (pull_negpos x y))"                   

text{*linkrel_pull ends*}    
text{*linkrel_straighten*}

definition straighten_topdown::relation
where
"straighten_topdown x y \<equiv>  ((x =((basic ((cement vert)\<otimes>(cement cup)))
                                         \<circ>(basic ((cement cap)\<otimes>(cement vert)))))
                                   \<and>(y = ((basic (cement vert))\<circ>(basic (cement vert)))))"



definition straighten_downtop::relation
where
"straighten_downtop x y \<equiv>  ((x =((basic ((cement cup)\<otimes>(cement vert)))
                                         \<circ>(basic ((cement vert)\<otimes>(cement cap)))))
                                   \<and>(y = ((basic (cement vert))\<circ>(basic (cement vert)))))"




text{*definition straighten*}
definition straighten::relation
where
"straighten x y \<equiv> ((straighten_topdown x y) \<or> (straighten_downtop x y))"



text{*straighten ends*}
text{* rotate moves*}

definition rotate_toppos::relation
where
"rotate_toppos x y \<equiv>  ((x = ((basic ((cement vert)\<otimes>(cement over)))
                                     \<circ>(basic ((cement cap)\<otimes>(cement vert)))))
                             \<and> (y = ((basic ((cement under)\<otimes>(cement vert))
                                     \<circ>(basic ((cement vert)\<otimes>(cement cap)))))))"

definition rotate_topneg::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"rotate_topneg x y \<equiv> ((x = ((basic ((cement vert)\<otimes>(cement under)))
                                     \<circ>(basic ((cement cap)\<otimes>(cement vert)))))
                             \<and> (y = ((basic ((cement over)\<otimes>(cement vert))
                                     \<circ>(basic ((cement vert)\<otimes>(cement cap)))))))"


definition rotate_downpos::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"rotate_downpos x y \<equiv>  ((x = ((basic ((cement cap)\<otimes>(cement vert)))
                                     \<circ>(basic ((cement vert)\<otimes>(cement over)))))
                             \<and> (y = ((basic ((cement vert)\<otimes>(cement cap)))
                                    \<circ>(basic ((cement under)\<otimes>(cement vert))))))"



definition rotate_downneg::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"rotate_downneg x y \<equiv>  ((x = ((basic ((cement cap)\<otimes>(cement vert)))
                                     \<circ>(basic ((cement vert)\<otimes>(cement under)))))
                             \<and> (y = ((basic ((cement vert)\<otimes>(cement cap)))
                                    \<circ>(basic ((cement over)\<otimes>(cement vert))))))"


text{*rotate definition*}


definition rotate::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"rotate x y \<equiv> ((rotate_toppos x y) \<or> (rotate_topneg x y)
\<or> (rotate_downpos x y) \<or> (rotate_downneg x y))"

text{*rotate ends*}


text{*Compress -  Compress has two levels of equivalences. It is a composition of Compress_null, compbelow
and compabove. compbelow and compabove are further written as disjunction of many other relations.
Compbelow refers to when the bottom row is extended or compressed. Compabove refers to when the 
row above is extended or compressed*}

definition compress_top::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"compress_top x y \<equiv>  \<exists>B.((x = (basic (make_vert_block (nat (domain_wall B - 1))))\<circ> B)
                              \<and>(y = (B \<circ> (basic (cement empty))))\<and>(codomain_wall B = 0))"


definition compress_bottom::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"compress_bottom x y \<equiv>   \<exists>B.((x = B \<circ> (basic (make_vert_block (nat (domain_wall B - 1)))))
                              \<and>(y = ((basic (cement empty) \<circ> B)))\<and>(domain_wall B = 0))"
(*linkrel_compress*)
definition compress::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"compress x y = ((compress_top x y) \<or> (compress_bottom x y))"

text{*slide relation refer to the relation where a crossing is slided over a vertical strand*}
definition slide::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"slide x y \<equiv>  \<exists>B.((x = ((basic (make_vert_block (nat (domain_block B - 1))))\<circ>(basic B)))
               \<and>(y = ((basic B)\<circ>(basic (make_vert_block (nat (domain_block B - 1)))))))"

text{*linkrel_definition*}

definition linkrel::"walls =>walls \<Rightarrow>bool"
where
"linkrel x y = ((uncross x y) \<or> (pull x y) \<or> (straighten x y) 
\<or>(swing x y)\<or>(rotate x y) \<or> (compress x y) \<or> (slide x y))"


definition framed_uncross::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"framed_uncross x y \<equiv> ((uncross_positive_flip x y)\<or>(uncross_negative_flip x y))"


definition framed_linkrel::"walls =>walls \<Rightarrow>bool"
where
"framed_linkrel x y = ((framed_uncross x y) \<or> (pull x y) \<or> (straighten x y) 
\<or>(swing x y)\<or>(rotate x y) \<or> (compress x y) \<or> (slide x y))"



lemma framed_uncross_implies_uncross: "(framed_uncross x y)\<Longrightarrow>(uncross x y)"
apply (simp add: framed_uncross_def uncross_def)
apply(auto)
done

end
