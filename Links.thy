theory Links
imports Tangles Tangle_Algebra
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

text{*stranded operations begin*}

primrec brickstrand::"brick \<Rightarrow> bool"
where
"brickstrand vert = True"|
"brickstrand cup = False"|
"brickstrand cap = False"|
"brickstrand over = False"|
"brickstrand under = False"

primrec strands::"block \<Rightarrow> bool"
where
"strands (cement x) = brickstrand x"|
"strands (x#ys) = (if (x= vert) then (strands ys) else False)"


lemma strands_test: "strands (vert#cup#vert#(cement vert)) = False" using strands_def brickstrand_def
compose_def by auto

text{*Compress -  Compress has two levels of equivalences. It is a composition of Compress_null, compbelow
and compabove. compbelow and compabove are further written as disjunction of many other relations.
Compbelow refers to when the bottom row is extended or compressed. Compabove refers to when the 
row above is extended or compressed*}

definition linkrel_compress::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_compress x y \<equiv>  \<exists>B.((x = (basic (make_vert_block (nat (domain_block B - 1))))\<circ>(basic B))
                              \<and>(y = (basic B)))"

text{*slide relation refer to the relation where a crossing is slided over a vertical strand*}
definition linkrel_slide::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"linkrel_slide x y \<equiv>  \<exists>B.((x = ((basic (make_vert_block (nat (domain_block B - 1))))\<circ>(basic B)))
               \<and>(y = ((basic B)\<circ>(basic (make_vert_block (nat (domain_block B - 1)))))))"

text{*linkrel_definition*}

definition linkrel::"walls =>walls \<Rightarrow>bool"
where
"linkrel x y = ((linkrel_uncross x y) \<or> (linkrel_pull x y) \<or> (linkrel_straighten x y) 
\<or>(linkrel_swing x y)\<or>(linkrel_rotate x y) \<or> (linkrel_compress x y) \<or> (linkrel_slide x y)
\<or>  (linkrel_uncross y x) \<or> (linkrel_pull y x) \<or> (linkrel_straighten y x) 
\<or>(linkrel_swing y x)\<or>(linkrel_rotate y x) \<or> (linkrel_compress y x) \<or> (linkrel_slide y x))
"

text{*we defined the link relations for a framed link, which are the same as those of unframed 
links excluding the uncross relation which straightens out a cross*}

definition framed_linkrel::"walls =>walls\<Rightarrow>bool"
where
"framed_linkrel x y = ((framed_linkrel_uncross x y) \<or> (linkrel_pull x y) \<or> (linkrel_straighten x y) 
\<or>(linkrel_swing x y)\<or>(linkrel_rotate x y) \<or> (linkrel_compress x y) \<or> (linkrel_slide x y)
\<or>  (framed_linkrel_uncross y x) \<or> (linkrel_pull y x) \<or> (linkrel_straighten y x) 
\<or>(linkrel_swing y x)\<or>(linkrel_rotate y x) \<or> (linkrel_compress y x) \<or> (linkrel_slide y x))
"

text{*Following lemmas asserts that if two framed linked diagrams are equivalent, then the unframed 
links are equivalent*}

lemma framed_linkrel_implies_linkrel: "(framed_linkrel x y) \<Longrightarrow> (linkrel x y)"
using framed_uncross_implies_uncross framed_linkrel_def linkrel_def by auto

text{* the link relations are symmetric*}
lemma linkrel_symp: "symp linkrel" unfolding linkrel_def symp_def by auto

lemma framed_linkrel_symp: "symp framed_linkrel" unfolding framed_linkrel_def symp_def by auto

 
text{*Linkrel_equiv is the reflexive-transitive closure of the Linkrel*}
definition linkrel_equiv::"walls\<Rightarrow>walls\<Rightarrow>bool"
where
"(linkrel_equiv) = (linkrel)^**" 


definition framed_linkrel_equiv::"walls\<Rightarrow>walls\<Rightarrow>bool"
where
"(framed_linkrel_equiv) = (framed_linkrel)^**" 
 
text{*Following lemmas assert that if two framed link diagrams are related by the linkrel_equiv, then 
the corresponding link diagrams are equivalent*}

lemma transitive_implication:
assumes " \<forall>x.\<forall>y.((r x y) \<longrightarrow>(q x y))"
shows "r^** x y \<Longrightarrow> q^** x y"
proof(induction rule:rtranclp.induct)
fix a
let ?case = "q\<^sup>*\<^sup>* a a"
show ?case by simp
next
fix a b c
assume rtranclp : "r^** a b" "r b c" "q^** a b"
let ?case = "q^** a c"
have "(r b c)\<Longrightarrow> (q b c)" using assms by auto
from this have "q b c" using assms rtranclp by auto
from this  have "q^** a c" using rtranclp(3) rtranclp.rtrancl_into_rtrancl by auto
thus ?case by simp
qed

theorem framed_equiv_implies_linkequiv: "(framed_linkrel_equiv x y) \<Longrightarrow> (linkrel_equiv x y)"
using  framed_linkrel_equiv_def linkrel_equiv_def transitive_implication  
framed_linkrel_implies_linkrel
by metis
text{*Linkrel_equiv and Framed_Linkrel_equiv are  equivalence relations*}

lemma reflective: "linkrel_equiv x x" unfolding linkrel_equiv_def by simp

lemma framed_reflective: "framed_linkrel_equiv x x" unfolding framed_linkrel_equiv_def by simp

lemma link_symmetry:"symp linkrel_equiv" using linkrel_symp symmetry3 
by (metis (full_types) linkrel_equiv_def)


lemma link_symmetry2:"(linkrel_equiv x y)\<Longrightarrow> (linkrel_equiv y x)" using link_symmetry sympD
 by metis

lemma framed_link_symmetry:"symp framed_linkrel_equiv" using framed_linkrel_symp symmetry3 
by (metis (full_types) framed_linkrel_equiv_def)

(*following lemma proves that linkrel_equiv is transitive in the usual sense of the term*)
lemma linkrel_trans: assumes "linkrel_equiv x y" and "linkrel_equiv y z"
shows "linkrel_equiv x z"
using rtranclp_trans linkrel_equiv_def  by (metis (full_types) assms(1) assms(2))

text{*links upto equivalence are well defined*}
text{*Link- Definition and the proof of being well defined*}
(*
quotient_type Link = "diagram" / "linkrel_equiv"
 morphisms Rep_links Abs_links
proof (rule equivpI)
show "reflp linkrel_equiv" unfolding reflp_def reflective by (metis reflective)
show "symp linkrel_equiv" using link_symmetry by auto
show "transp linkrel_equiv" unfolding transp_def linkrel_equiv_def rtranclp_trans by auto  
qed

quotient_type Framed_Link = "diagram" / "framed_linkrel_equiv"
 morphisms Rep_framed_links Abs_framed_links
proof (rule equivpI)
show "reflp framed_linkrel_equiv" unfolding reflp_def framed_reflective by (metis framed_reflective)
show "symp framed_linkrel_equiv" using framed_link_symmetry by auto
show "transp framed_linkrel_equiv" unfolding transp_def framed_linkrel_equiv_def rtranclp_trans by auto  
qed
*)
end
