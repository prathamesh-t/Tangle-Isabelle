theory Tangles
imports Datatype Main Typedef tangle_relation
begin

text{* This theory contains the definition of a Link. A link is defined as Link diagrams upto 
 equivalence moves. Link diagrams are defined in terms of the constituent tangles*}

text{*each  block is a horizontal block built by putting basic link bricks next to each other.
(1) vert is the straight line
(2) cup is the up facing is_cup
(3) cap is the bottom facing is_cup
(4) over is the positive cross
(5) under is the negative cross*}

datatype brick = vert
                |cup
                |cap
                |over
                |under

text{*block is obtained by putting bricks next to each other*}
datatype block = cement brick
                 |cons brick block  (infixr "#" 60)              

text{*walls are link diagrams obtained by placing a horizontal blocks a top each other*}

datatype walls = basic block
                |prod block  walls  (infixr "*" 66)

text{*Append gives us the block obtained by putting two blocks next to each other*}

primrec append_blocks :: "block => block => block" (infixr "\<otimes>" 65) where
append_blocks_Nil: "(cement x) \<otimes> ys = cons x ys" |
append_blocks_Cons: "((x#xs)\<otimes>ys) = x#(xs\<otimes>ys)"

text{*Associativity properties of append_blocks*}
lemma leftright_associativity: "(x\<otimes>y)\<otimes>z = x\<otimes>(y\<otimes>z)"
apply(induct_tac x)
apply(auto)
done

lemma left_associativity: "(x\<otimes>y)\<otimes>z = x\<otimes>y\<otimes>z"
apply(induct_tac x)
apply(auto)
done

lemma right_associativity: "x\<otimes>(y\<otimes>z) =x \<otimes> y \<otimes>z"
apply(auto)
done

text{*Compose gives us the wall obtained by putting a wall above another*}
primrec compose :: "walls => walls => walls" (infixr "\<circ>" 66) where
compose_Nil: "(basic x) \<circ> ys =  prod x ys" |
compose_Cons: "((prod x xs)\<circ>ys) = prod x (xs\<circ>ys)"

text{*Associativity properties of compose*}

lemma compose_leftassociativity: "(((x::walls) \<circ> y) \<circ> z) = (x\<circ>y \<circ>z)"
apply(induct_tac x)
apply(auto)
done

lemma compose_rightassociativity: "(x::walls) \<circ> (y \<circ> z) = (x\<circ>y \<circ>z)"
apply(induct_tac x)
apply(auto)
done



text{*block_length of a block is the number of bricks in a given block*}
primrec block_length::"block \<Rightarrow> nat"
where
"block_length (cement x) = 1"|
"block_length (cons x y) = 1 + (block_length y)"


text{*brickcount tells us the number of incoming and outgoing strangs of each brick.*}
 primrec brickcount::"brick \<Rightarrow> int \<times> int "
 where
 "brickcount vert = (1,1)"|
 "brickcount cup = (0,2)"|
 "brickcount cap = (2,0)"|
 "brickcount over = (2,2)"|
 "brickcount under = (2,2)"

text{*count tells us the number of incoming and outgoing strangs of each block.*}

 primrec count::"block \<Rightarrow> int \<times> int "
 where
 "count (cement x) = (brickcount x)"
 |"count (cons x y) = (fst (brickcount x) + fst (count y), snd (brickcount x) + snd (count y))"

text{*wall_count tells us the number of incoming and outgoing strangs of each wall.*}

primrec wall_count:: "walls \<Rightarrow> int \<times> int" where
"wall_count (basic x) = count x"                                               
|"wall_count (x*ys) = (fst (count x),snd (wall_count ys))"

text{*this lemma tells us the number of incoming and outgoing strands of a composition of two walls*}
lemma wall_count_compose: "wall_count (xs\<circ>ys) = (fst (wall_count (xs)), snd(wall_count (ys)))"
apply(induct_tac xs)
apply(auto)
done 

text{*absolute value*}
definition abs::"int \<Rightarrow> int" where
"abs x \<equiv> if (x\<ge>0) then x else (0-x)" 

text{*theorems about abs*}
lemma abs_zero: assumes "abs x = 0" shows "x = 0" using abs_def assms eq_iff_diff_eq_0
 by metis

lemma abs_zero_equality: assumes "abs (x - y) = 0" shows "x = y" using assms abs_zero  eq_iff_diff_eq_0
by auto

lemma abs_non_negative: " abs x \<ge> 0"
using abs_def diff_0 le_cases neg_0_le_iff_le 
by auto


lemma abs_non_negative_sum:  assumes " abs x + abs y = 0"
shows "abs x= 0" and "abs y = 0"
using abs_def diff_0 abs_non_negative  neg_0_le_iff_le 
add_nonneg_eq_0_iff assms
apply metis
by (metis abs_non_negative add_nonneg_eq_0_iff assms)


text{*the following lemmas are test lemmas*}
lemma cement_vert_count:" count (cement vert) = (1,1)"
using brickcount.simps(1) count.simps(1) by metis

lemma cement_cup_count:" count ((cement cup)) = (0,2)"
using brickcount.simps(2) count.simps(1) by metis


lemma cement_cap_count:" count ((cement cap)) = (2,0)"
using  brickcount.simps(3) count.simps(1) by metis

lemma cement_over_count:" count ((cement over)) = (2,2)"
using brickcount.simps(4) count.simps(1) by metis

lemma cement_under_count:" count ((cement under)) = (2,2)"
using  brickcount.simps(5) count.simps(1) by metis


text{*The following lemmas tell us that the number of incoming and outgoing strands of every brick 
is a non negative integer*}
lemma brickcount_nonnegative: "fst (brickcount x) \<ge> 0" 
by 
(metis Nat_Transfer.transfer_nat_int_function_closures(6) brick.exhaust brick.simps(26)
 brick.simps(27) brick.simps(28) brick.simps(30) brickcount.simps(4) 
dbl_def dbl_simps(3) fst_conv less_imp_le one_plus_BitM order_refl semiring_norm(26) 
zero_less_numeral brickcount_def)


lemma snd_brickcount_nonnegative: "snd (brickcount x) \<ge> 0" 
apply(simp add: brickcount_def)
by (metis Nat_Transfer.transfer_nat_int_function_closures(6) brick.exhaust brick.simps(26) 
brick.simps(27) brick.simps(28) brick.simps(29) brick.simps(30) dbl_simps(3) less_imp_le 
one_plus_BitM order_refl semiring_norm(26) snd_conv zero_less_numeral)


text{*The following lemmas tell us that the number of incoming and outgoing strands of every block 
is a non negative integer*}
lemma count_nonnegative: "fst (count x) \<ge> 0" 
apply(induct_tac x)
apply(auto)
apply(simp add:brickcount_nonnegative)
apply(simp add:count_def)
apply (metis (lifting) add_increasing brickcount_nonnegative)
done


lemma snd_count_nonnegative: "snd (count x) \<ge> 0" 
apply(induct_tac x)
apply(auto)
apply(simp add:snd_brickcount_nonnegative)
apply(simp add:count_def)
apply (metis (lifting) add_increasing snd_brickcount_nonnegative)
done

text{*The following lemmas tell us that if a block is appended to a block with incoming strands, then
the resultant block has incoming strands*}

lemma count_positive: "((fst (count (cement x)) > 0) \<or> (fst (count y) > 0)) 
\<Longrightarrow> (fst (count (x#y)) > 0)" 
proof-
have "fst (count (x#y)) =  (fst (brickcount x) + fst (count y))" using count_def by auto
also have " (fst (brickcount x)) = fst (count (cement x))" using count_def by auto
then have "((fst (count (cement x))) > 0) = ((fst (brickcount x)) > 0)" using count_def by auto
then have "((fst (brickcount x) > 0) \<or> (fst (count y) > 0)) \<Longrightarrow> (fst (brickcount x) + fst (count y))>0"
using count_nonnegative add_nonneg_pos add_pos_nonneg brickcount_nonnegative by metis
from this  show  "((fst (count (cement x)) > 0) \<or> (fst (count y) > 0)) 
\<Longrightarrow> (fst (count (x#y)) > 0)" by auto
qed
  
lemma fst_count_additive:  "fst (count (x\<otimes>y))= (fst (count x)) + (fst (count y))"
apply(induct_tac x)
apply(simp add: count_def)
apply(auto)
done

lemma snd_count_additive:  "snd (count (x\<otimes>y))= (snd (count x)) + (snd (count y))"
apply(induct_tac x)
apply(simp add: count_def)
apply(auto)
done

lemma fst_count_zero_sum: assumes "(fst (count x)) + (fst (count y)) = 0"
shows "fst (count x) = 0" and "fst (count y) = 0"
using count_positive count_nonnegative add_nonneg_eq_0_iff assms
apply metis
by (metis add_nonneg_eq_0_iff assms count_nonnegative)

lemma fst_count_positive: assumes "fst (count y)>0" or "fst (count x)>0"
shows "fst (count (x\<otimes>y)) > 0"
apply (simp add: fst_count_additive)
by (metis (mono_tags) add_less_cancel_left assms comm_semiring_1_class.normalizing_semiring_rules(6)
 count_nonnegative fst_count_additive le_neq_trans not_le)


lemma snd_count_positive: assumes "snd (count y)>0 " or "snd (count x)>0"
shows "snd (count (x\<otimes>y)) > 0"
apply (simp add: snd_count_additive)
by (metis (hide_lams, no_types) add_nonneg_eq_0_iff assms le_neq_trans snd_count_additive 
snd_count_nonnegative)



text{*We try to prove that if the first count of a block is zero, then it is composed of cups. In
order to do that we define the functions brick_is_cup and is_cup which check if a given block is 
composed of cups or if the blocks are composed of blocks*}

primrec brick_is_cup::"brick \<Rightarrow> bool"
where
"brick_is_cup vert = False"|
"brick_is_cup cup = True"|
"brick_is_cup cap = False"|
"brick_is_cup over = False"|
"brick_is_cup under = False"


primrec is_cup::"block \<Rightarrow> bool"
where
"is_cup (cement x) = brick_is_cup x"|
"is_cup (x#y) = (if (x= cup) then (is_cup y) else False)"


lemma is_cup_basic: "((is_cup x) = False) \<Longrightarrow> 
((x=(cement vert))\<or>(x=(cement cap))\<or>(x=(cement over))\<or>(x=(cement under)))\<or>(\<exists>y1.\<exists>y2.\<exists>y3.(x=(y1\<otimes>y2\<otimes>y3)\<and> 
((y1=(cement vert))\<or>(y1=(cement cap))\<or>(y1=(cement over))\<or>(y1=(cement under)))\<or>(y2=(cement vert))\<or>(y2=(cement cap))\<or>(y2=(cement over))\<or>(y2=(cement under)))\<or>((y3=(cement vert))\<or>(y3=(cement cap))\<or>(y3=(cement over))\<or>(y3=(cement under))))"
by metis



lemma brickcount_zero_implies_cup:"(fst (brickcount x)= 0) \<Longrightarrow> (x = cup)"
apply(case_tac "brickcount x")
apply(auto)
apply(case_tac "x")
apply(auto)
done

lemma brickcount_zero_implies_brick_is_cup:"(fst (brickcount x)= 0) \<Longrightarrow> (brick_is_cup x)"
apply(case_tac "brick_is_cup x")
apply(simp add: brickcount_zero_implies_cup)
apply(auto)
apply(case_tac "x")
apply(auto)
done

lemma count_zero_implies_is_cup:"(fst (count x)= 0) \<Longrightarrow> (is_cup x)"
proof(induction x)
case (cement y)
have "(fst (count (cement y))) = (fst (brickcount y))" by auto
from this have " (fst (count (cement y)) = 0) \<equiv>((fst (brickcount y))=0)"  by auto
from this  have " (fst (count (cement y)) = 0)  \<Longrightarrow>(brick_is_cup y)" using brickcount_zero_implies_brick_is_cup
by auto
from this have "(fst (count (cement y)) = 0)  \<Longrightarrow>(is_cup (cement y))" by auto 
from this show ?case using cement.prems by (auto) 
next
case (cons a y)
show ?case 
proof-
have step1: "fst (count (a # y)) = fst (brickcount a) + (fst  (count y))" by auto
from this and fst_count_zero_sum have"fst (count y) = 0" 
by (metis Tangles.append_blocks.append_blocks_Nil cons.prems fst_count_additive)
from this have step2: "(is_cup y)" using cons.IH by (auto) 
from this and step1 and fst_count_zero_sum  have "fst (brickcount a)= 0" by (metis cons.prems count.simps(1))
from this have "brick_is_cup a" using brickcount_zero_implies_brick_is_cup by auto
from this and assms have "a=cup" using brick_is_cup_def 
by (metis `fst (brickcount a) = 0` brickcount_zero_implies_cup)
from this and step2 have "is_cup (a#y)" using is_cup_def by auto
from this show ?case by auto
qed
qed


text{* We need a function that checks if a wall represents a knot diagram. The function well_defined 
serves this purpose. It ensures that all the incoming strands and outgoing strands of constituend 
blocks are matched and the wall itself has not incoming and outgoing strands. It is defined using 
the function wall_count_list gives the list of number of incoming strand of a constituent block 
minus the outgoing strand of the block below*}


primrec wall_count_list:: "walls \<Rightarrow> int list" where
"wall_count_list (basic x) = []"|
"wall_count_list (x * y) =  (abs (fst(wall_count y) - snd(count x)))#(wall_count_list y)"

lemma wall_count_list_compose: " wall_count_list (x \<circ> y) = 
(wall_count_list x)@((abs (fst(wall_count y) - snd(wall_count x)))#(wall_count_list y))"
apply(induct_tac x)
apply(auto)
apply(simp add: wall_count_compose)
done

primrec list_sum::"int list \<Rightarrow> int" 
where
"list_sum [] = 0"|
"list_sum (x#xs) = x+ list_sum xs"

lemma list_sum_non_negative:"list_sum(wall_count_list x) \<ge> 0"
apply(induct_tac x)
apply(auto)
apply(simp add: abs_non_negative)
done

definition well_defined::"walls \<Rightarrow> bool" where
"well_defined x \<equiv> ( (list_sum (wall_count_list x)+(abs(fst(wall_count x))
+ abs(snd(wall_count x)))) = 0)"

text{*well_defined walls as a type called diagram. The morphisms Abs_diagram maps a well defined wall to 
its diagram type and Rep_diagram maps the diagram back to the wall *}

typedef diagram = "{(x::walls). well_defined x}"
apply (rule_tac x = "prod (cement cup) (basic (cement cap))" in exI)
apply(auto)
apply(simp add:abs_def well_defined_def)
done

text{*The next few lemmas list the properties of well defined diagrams*}

text{*For a well defined diagram, the morphism Rep_diagram acts as an inverse of Abs_diagram- 
the morphism which maps a well defined wall to its representative in the type- diagram*}

lemma Abs_Rep_well_defined: assumes " well_defined x" shows "Rep_diagram (Abs_diagram x) = x"
using Rep_diagram Abs_diagram_inverse assms mem_Collect_eq  by auto

text{*The map Abs_diagram is injective*}
lemma Rep_Abs_well_defined: assumes " well_defined x"  and "well_defined y" 
and  "(Abs_diagram x) = (Abs_diagram y)"
shows "x = y"
using Rep_diagram Abs_diagram_inverse assms mem_Collect_eq  by metis

text{* restating the property of well_defined walls in terms of diagram*}
lemma well_defined_composition: 
"((list_sum (wall_count_list (Rep_diagram z))+(abs(fst(wall_count (Rep_diagram z)))
+ abs(snd(wall_count (Rep_diagram z))))) = 0)"
using Rep_diagram mem_Collect_eq well_defined_def by (metis (mono_tags))

lemma diagram_list_sum: 
"((list_sum (wall_count_list (Rep_diagram z))) = 0)"
using well_defined_composition abs_non_negative_sum list_sum_non_negative
abs_non_negative add_increasing add_nonneg_eq_0_iff
by metis 

lemma diagram_fst_wall_count: 
"(abs (fst (wall_count (Rep_diagram z))) = 0)"
using well_defined_composition abs_non_negative_sum list_sum_non_negative
abs_non_negative add_increasing add_nonneg_eq_0_iff wall_count_def
by metis

 
text{* In order to locally defined moves, it helps to prove that if composition of two walls is a 
well defined wall then the number of outgoing strands of the wall below are equal to the number of 
incoming strands of the wall above. The following lemmas prove that for a well defined wall, t
he number of incoming and outgoing strands are zero*}

lemma well_defined_fst_wall_count: 
assumes "well_defined x"
shows "(abs (fst (wall_count x)) = 0)"
using well_defined_composition abs_non_negative_sum list_sum_non_negative
abs_non_negative add_increasing add_nonneg_eq_0_iff wall_count_def
 assms well_defined_def
by (metis)

lemma diagram_snd_wall_count: 
"(abs (snd (wall_count (Rep_diagram z))) = 0)"
using well_defined_composition abs_non_negative_sum list_sum_non_negative
abs_non_negative add_increasing add_nonneg_eq_0_iff wall_count_def
by metis


lemma well_defined_snd_wall_count: 
assumes "well_defined x"
shows "(abs (snd (wall_count x)) = 0)"
using well_defined_composition abs_non_negative_sum list_sum_non_negative
abs_non_negative add_increasing add_nonneg_eq_0_iff wall_count_def
 assms well_defined_def
by (metis)

lemma wall_count_list_list_sum_non_negative:
"(list_sum (wall_count_list x)) \<ge> 0"
apply(induct_tac x) 
apply(auto)
apply (simp add: abs_non_negative add_increasing)
done

lemma wall_count_list_list_sum_abs:
"(list_sum (wall_count_list x)) = abs (list_sum (wall_count_list x))"
using wall_count_list_list_sum_non_negative abs_def by auto


lemma wall_count_list_list_sum_zero_add:
assumes "(list_sum (wall_count_list x)) + (list_sum (wall_count_list y)) = 0"
shows "(list_sum (wall_count_list x)) = 0" and "(list_sum (wall_count_list y)) = 0"
using abs_non_negative_sum wall_count_list_list_sum_abs assms 
apply metis 
by (metis add_nonneg_eq_0_iff assms wall_count_list_list_sum_non_negative)

lemma list_sum_append_blocks:
"list_sum (x@y) = (list_sum x) + (list_sum y)"
apply(induct_tac x)
apply(auto)
done

lemma wall_count_list_list_sum_compose:
"(list_sum (wall_count_list (x \<circ> y))) = 
(list_sum (wall_count_list x)) + (abs ( (fst (wall_count y)) - (snd (wall_count x)))) + 
(list_sum (wall_count_list y))"
using wall_count_list_compose list_sum_def append_blocks_def list_sum_append_blocks
by (metis ab_semigroup_add_class.add_ac(1) list_sum.simps(2))


lemma list_sum_compose: assumes "list_sum (wall_count_list x) = 0" and "list_sum (wall_count_list y) = 0"
and "(snd (wall_count x))= (fst (wall_count y))"
shows  "list_sum (wall_count_list (x\<circ>y)) = 0"
proof-
from  wall_count_list_list_sum_compose and assms and abs_def 
have "list_sum (wall_count_list (x\<circ>y)) = (list_sum (wall_count_list x))+(list_sum (wall_count_list y))"
by auto
from this and assms have "list_sum (wall_count_list (x\<circ>y)) = 0" by auto
from this show ?thesis by auto
qed

lemma diagram_wall_count_list:
assumes "(abs ( (fst (wall_count y)) - (snd (wall_count x))))>0"
shows "(list_sum (wall_count_list (x\<circ>y)) > 0)"
proof-
have "(list_sum (wall_count_list x) \<ge>0)" and "(list_sum (wall_count_list y)\<ge>  0)"  using 
wall_count_list_list_sum_non_negative by auto
then have  "(abs ( (fst (wall_count y)) - (snd (wall_count x))))>0" using assms by auto
then have "((list_sum (wall_count_list x)) + (abs ( (fst (wall_count y)) - (snd (wall_count x)))) + 
(list_sum (wall_count_list y))) > 0"
using abs_non_negative add_increasing add_nonneg_eq_0_iff
comm_monoid_add_class.add.left_neutral comm_semiring_1_class.normalizing_semiring_rules(24) 
le_neq_trans not_le order_refl wall_count_list_list_sum_non_negative well_defined_def by (metis add_strict_increasing2)
then have "(list_sum (wall_count_list (x \<circ> y))) = 
((list_sum (wall_count_list x)) + (abs ( (fst (wall_count y)) - (snd (wall_count x)))) + 
(list_sum (wall_count_list y)))" using wall_count_list_list_sum_compose by auto
then have  "(list_sum (wall_count_list (x \<circ> y))) > 0" 
by (metis 
`0 < list_sum (wall_count_list x) + Tangles.abs (fst (wall_count y) - snd (wall_count x)) + 
list_sum (wall_count_list y)`)
then show ?thesis by auto
qed

lemma diagram_wall_count_list_zero:
assumes "(list_sum (wall_count_list (x\<circ>y)) = 0)"
shows " (abs ( (fst (wall_count y)) - (snd (wall_count x))))=0"
using diagram_wall_count_list list_sum_non_negative abs_non_negative assms less_le by (metis)



lemma diagram_list_sum_zero:
 assumes "well_defined x"
shows "list_sum (wall_count_list x) = 0" 
proof-
have "list_sum (wall_count_list (Rep_diagram (Abs_diagram x))) = 0" using diagram_list_sum by metis
then have "Rep_diagram (Abs_diagram x) = x" using Abs_diagram_inverse assms mem_Collect_eq
by (auto)
then have "list_sum (wall_count_list x) = 0" using `list_sum (wall_count_list (Rep_diagram (Abs_diagram x))) = 0`
by (metis)
then show ?thesis by simp  
qed


lemma diagram_compose:
assumes "well_defined (x\<circ>y)"
shows " (abs ( (fst (wall_count y)) - (snd (wall_count x))))=0"
using diagram_list_sum_zero diagram_wall_count_list_zero assms by auto

lemma diagram_fst_equals_snd:
assumes "well_defined (x\<circ>y)"
shows " (fst (wall_count y)) = (snd (wall_count x))"
using diagram_compose abs_zero_equality assms  by auto


text{*if composition of two walls is a well defined wall then the two walls define well defined links*}
lemma diagram_list_sum_subsequence:
assumes "well_defined (x\<circ>y)"
shows "(list_sum (wall_count_list x) = 0)\<and>(list_sum (wall_count_list y) = 0)"
proof-
have "(abs ( (fst (wall_count y)) - (snd (wall_count x)))) = 0" using diagram_compose assms
by auto
from this have "(list_sum (wall_count_list x)) + (list_sum (wall_count_list y)) = 0" using diagram_list_sum_zero
wall_count_list_list_sum_compose assms plus_int_code(1)  by metis
from this have goal1: "(list_sum (wall_count_list x)) = 0" and goal2:"(list_sum (wall_count_list y)) = 0" using 
wall_count_list_list_sum_zero_add by auto
from this have "(list_sum (wall_count_list x) = 0)\<and>(list_sum (wall_count_list y) = 0)" by auto
from this show ?thesis by simp
qed


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

definition linkrel_uncross_positiveflip::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_uncross_positiveflip x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement vert)\<otimes>(cement cup)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement over)\<otimes>(cement vert)\<otimes>w2))
\<circ>(basic (z3\<otimes>(cement vert)\<otimes>(cement cap)\<otimes>w3))\<circ>(y2))))
\<and>(y = Abs_diagram ((y1)\<circ>(basic (z1\<otimes>(cement cup)\<otimes>(cement vert)\<otimes>w1))
\<circ>(basic (z2\<otimes>(cement vert)\<otimes>(cement over)\<otimes>w2))\<circ>(basic (z3\<otimes>(cement cap)\<otimes>(cement vert)\<otimes>w3))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count z2)) = (fst (count z3))) \<and> ((snd (count w1)) = (fst (count w2)))
\<and>((snd (count w2)) = (fst (count w3))))"

definition linkrel_uncross_positivestraighten::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_uncross_positivestraighten x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement cup)\<otimes>(cement vert)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement vert)\<otimes>(cement over)\<otimes>w2))\<circ>(basic (z3\<otimes>(cement cap)\<otimes>(cement vert)\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>(cement vert)\<otimes>w1))\<circ>(basic (z2\<otimes>(cement vert)\<otimes>w2))\<circ>(basic (z3\<otimes>(cement vert)\<otimes>w3))\<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))) \<and> ((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

definition linkrel_uncross_negativeflip::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_uncross_negativeflip x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement vert)\<otimes>(cement cup)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement under)\<otimes>(cement vert)\<otimes>w2))\<circ>(basic (z3\<otimes>(cement vert)\<otimes>(cement cap)\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>(cement cup)\<otimes>(cement vert)\<otimes>w1))\<circ>(basic (z2\<otimes>(cement vert)\<otimes>(cement under)\<otimes>w2))\<circ>(basic (z3\<otimes>(cement cap)\<otimes>(cement vert)\<otimes>w3))\<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))) \<and> ((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

definition linkrel_uncross_negativestraighten::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_uncross_negativestraighten x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement cup)\<otimes>(cement vert)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement vert)\<otimes>(cement under)\<otimes>w2))\<circ>(basic (z3\<otimes>(cement cap)\<otimes>(cement vert)\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>(cement vert)\<otimes>w1))\<circ>(basic (z2\<otimes>(cement vert)\<otimes>w2))\<circ>(basic (z3\<otimes>(cement vert)\<otimes>w3))\<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))) \<and> ((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

text{*link_uncross definition*}
definition linkrel_uncross::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_uncross x y \<equiv> 
((linkrel_uncross_positiveflip x y)\<or>(linkrel_uncross_positivestraighten x y)
\<or>(linkrel_uncross_negativeflip x y)\<or>(linkrel_uncross_negativestraighten x y))"
text{*link_uncross ends*}
text{*framed linkrel_uncross*}

definition framed_linkrel_uncross::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"framed_linkrel_uncross x y \<equiv> 
((linkrel_uncross_positiveflip x y)\<or>(linkrel_uncross_negativeflip x y))"

lemma framed_uncross_implies_uncross: "(framed_linkrel_uncross x y) \<Longrightarrow> (linkrel_uncross x y)"
apply (simp add: framed_linkrel_uncross_def linkrel_uncross_def)
apply(auto)
done

text{*link_pull begins*}

definition linkrel_pull_posneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_pull_posneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement over)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement under)\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>(cement vert)\<otimes>(cement vert)\<otimes>w1))\<circ>(basic (z2\<otimes>(cement vert)\<otimes>(cement vert)\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2))))"


definition linkrel_pull_negpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_pull_negpos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement under)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement over)\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>(cement vert)\<otimes>(cement vert)\<otimes>w1))\<circ>(basic (z2\<otimes>(cement vert)\<otimes>(cement vert)\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2))))"

text{*linkrel_pull definition*}
definition linkrel_pull::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_pull x y \<equiv> ((linkrel_pull_posneg x y) \<or> (linkrel_pull_negpos x y))"                   

text{*linkrel_pull ends*}    
text{*linkrel_straighten*}

definition linkrel_straighten_topdown::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_straighten_topdown x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement vert)\<otimes>(cement cup)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement cap)\<otimes>(cement vert)\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>(cement vert)\<otimes>w1))\<circ>(basic (z2\<otimes>(cement vert)\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2))))"


definition linkrel_straighten_downtop::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_straighten_downtop x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement cup)\<otimes>(cement vert)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement vert)\<otimes>(cement cap)\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>(cement vert)\<otimes>w1))\<circ>(basic (z2\<otimes>(cement vert)\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2))))"


definition linkrel_straighten_righttopdown::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_straighten_righttopdown x y \<equiv>  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w1)\<circ>(basic ((cement cap)\<otimes>(cement vert)\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic ((cement vert)\<otimes>w1))\<circ>(basic ((cement vert)\<otimes>w2))\<circ>(y2))))
 \<and> ((snd (count w1)) = (fst (count w2)))"


definition linkrel_straighten_rightdowntop::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_straighten_rightdowntop x y \<equiv>  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic ((cement cup)\<otimes>(cement vert)\<otimes>w1)\<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic ((cement vert)\<otimes>w1))\<circ>(basic ((cement vert)\<otimes>w2))\<circ>(y2))))
 \<and> ((snd (count w1)) = (fst (count w2)))"



definition linkrel_straighten_lefttopdown::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_straighten_lefttopdown x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement cup)\<otimes>(cement vert))\<circ>(basic (z2\<otimes>(cement vert)\<otimes>(cement cap))))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>(cement vert)))\<circ>(basic (z2\<otimes>(cement vert)))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2))))"


definition linkrel_straighten_leftdowntop::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_straighten_leftdowntop x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement vert)\<otimes>(cement cup))\<circ>(basic (z2\<otimes>(cement cap)\<otimes>(cement vert))))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>(cement vert)))\<circ>(basic (z2\<otimes>(cement vert)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))"

text{*definition straighten*}
definition linkrel_straighten::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_straighten x y \<equiv> ((linkrel_straighten_topdown x y) \<or> (linkrel_straighten_downtop x y)
\<or>(linkrel_straighten_righttopdown x y) \<or> (linkrel_straighten_rightdowntop x y)
\<or>(linkrel_straighten_lefttopdown x y) \<or> (linkrel_straighten_leftdowntop x y))"



text{*straighten ends*}
text{*swing begins*}
definition linkrel_swing_pos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_swing_pos x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement over)\<otimes>(cement vert)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement vert)\<otimes>(cement over)\<otimes>w2))\<circ>(basic (z3\<otimes>(cement over)\<otimes>(cement vert)\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>(cement vert)\<otimes>(cement over)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement over)\<otimes>(cement vert)\<otimes>w2))\<circ>(basic (z3\<otimes>(cement vert)\<otimes>(cement over)\<otimes>w3))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))\<and>((snd (count z2)) = (fst (count z3)))
 \<and> ((snd (count w1)) = (fst (count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

definition linkrel_swing_neg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_swing_neg x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement under)\<otimes>(cement vert)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement vert)\<otimes>(cement under)\<otimes>w2))\<circ>(basic (z3\<otimes>(cement under)\<otimes>(cement vert)\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>(cement vert)\<otimes>(cement under)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement under)\<otimes>(cement vert)\<otimes>w2))\<circ>(basic (z3\<otimes>(cement vert)\<otimes>(cement under)\<otimes>w3))\<circ>(y2)))))
\<and>((snd (count z1)) = (fst (count z2)))\<and>((snd (count z2)) = (fst (count z3)))
 \<and> ((snd (count w1)) = (fst (count w2)))\<and>((snd (count w2)) = (fst (count w3)))"

text{*swing definition*}

definition linkrel_swing::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_swing x y \<equiv> ((linkrel_swing_pos x y) \<or> (linkrel_swing_neg x y))"

text{*swing ends*}
text{* rotate moves*}

definition linkrel_rotate_toppos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_rotate_toppos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>(cement vert)\<otimes>(cement over)\<otimes>w1))\<circ>(basic (z2\<otimes>(cement cap)\<otimes>(cement vert)\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement under)\<otimes>(cement vert)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement vert)\<otimes>(cement cap)\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2))))"


definition linkrel_rotate_topneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_rotate_topneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>(cement vert)\<otimes>(cement under)\<otimes>w1))\<circ>(basic (z2\<otimes>(cement cap)\<otimes>(cement vert)\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement over)\<otimes>(cement vert)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement vert)\<otimes>(cement cap)\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2))))"

definition linkrel_rotate_downpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_rotate_downpos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>(cement cap)\<otimes>(cement vert)\<otimes>w1))\<circ>(basic (z2\<otimes>(cement vert)\<otimes>(cement over)\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement vert)\<otimes>(cement cap)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement under)\<otimes>(cement vert)\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2))))"


definition linkrel_rotate_downneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_rotate_downneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.
\<exists>w1.\<exists>w2.\<exists>y2.
((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement cap)\<otimes>(cement vert)\<otimes>w1))\<circ>(basic (z2\<otimes>(cement vert)\<otimes>(cement under)\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement vert)\<otimes>(cement cap)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement over)\<otimes>(cement vert)\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2))))"


text{*rotate definition*}


definition linkrel_rotate::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
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

definition linkrel_compress_null::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_compress_null x y \<equiv>  \<exists>y2.\<exists>A.\<exists>B.((x = Abs_diagram
 ((A)\<circ>(basic B)\<circ>(y2)))\<and>(y = Abs_diagram ((A)\<circ>(y2)))
\<and> (strands B) \<and> ((snd (wall_count A))>0))"

text{*two at a time*}

definition linkrel_compbelow_right::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_compbelow_right x y \<equiv>  \<exists>w1.\<exists>w2.\<exists>y2.\<exists>A.\<exists>B.((x= Abs_diagram
 ((basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram (
(basic w1)\<circ>(basic (A\<otimes>w2))\<circ>(y2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and> (strands B)
\<and> ((fst (count A)) = 0))"


definition linkrel_compbelow_left::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_compbelow_left x y \<equiv>  \<exists>z1.\<exists>z2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> ((y = Abs_diagram (
(basic (z1)\<circ>(basic (z2\<otimes>A)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>(strands B))"


definition linkrel_compbelow_bottomright::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_compbelow_bottomright x y \<equiv>  \<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((basic (A))\<circ>(basic (B\<otimes>w2))\<circ>(y2)))\<and> 
(y = Abs_diagram (
(basic (A\<otimes>w2))\<circ>(y2)))
\<and>(0 = (fst (count w2)))
\<and>(strands B))"


definition linkrel_compbelow_bottomleft::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_compbelow_bottomleft x y \<equiv>  \<exists>z2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((basic (A))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> 
(y = Abs_diagram (
(basic (z2 \<otimes> A))\<circ>(y2)))
\<and>(0 = (fst (count z2)))
\<and>(strands B))"


definition linkrel_compbelow_centerright::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_compbelow_centerright x y \<equiv> \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (w1))\<circ>(basic (A\<otimes>w2))\<circ>(y2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>((fst (count A)) = 0)
\<and>(strands B))"


definition linkrel_compbelow_centerleft::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_compbelow_centerleft x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1))\<circ>(basic (z2\<otimes>A))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((fst (count A)) = 0)
\<and>(strands B))"



text{*compbelow definition*}
definition linkrel_compbelow::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_compbelow x y \<equiv> 
(linkrel_compbelow_right x y) \<or> (linkrel_compbelow_left x y)
\<or> (linkrel_compbelow_centerleft x y) \<or> (linkrel_compbelow_centerright x y)
\<or> (linkrel_compbelow_bottomright x y) \<or> (linkrel_compbelow_bottomleft x y)
"

text{*comp above*}

definition linkrel_compabove_right::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_compabove_right x y \<equiv>  \<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y1.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))))\<and> ((y = Abs_diagram (
(y1)\<circ>(basic (B\<otimes>w1)\<circ>(basic (w2))))))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>(strands A))"


definition linkrel_compabove_left::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_compabove_left x y \<equiv>  \<exists>z1.\<exists>z2.\<exists>A.\<exists>B.\<exists>y1.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B))))\<and> ((y = Abs_diagram (
(y1)\<circ>(basic (B\<otimes>z1)\<circ>(basic (z2))))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>(strands A))"

definition linkrel_compabove_topright::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_compabove_topright x y \<equiv>  \<exists>w1.\<exists>A.\<exists>B.\<exists>y1.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B))))\<and> ((y = Abs_diagram (
(y1)\<circ>(basic (B\<otimes>w1)))))
\<and>((snd (count w1)) = 0)
\<and>(strands A))"

definition linkrel_compabove_topleft::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_compabove_topleft x y \<equiv>  \<exists>z1.\<exists>A.\<exists>B.\<exists>y1.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (B))))\<and> ((y = Abs_diagram (
(y1)\<circ>(basic (z1\<otimes>B)))))
\<and>((snd (count z1)) = 0)
\<and>(strands A))"
text{*two at a time-center*}


definition linkrel_compabove_centerleft::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_compabove_centerleft x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1\<otimes>B))\<circ>(basic (z2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count B)) = 0)
\<and>(strands A))"


definition linkrel_compabove_centerright::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_compabove_centerright x y \<equiv> \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B \<otimes> w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (B\<otimes>w1))\<circ>(basic (w2))\<circ>(y2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>((snd (count B)) = 0)
\<and>(strands A))"
text{*compabove definition*}

text{*compbelow definition*}
definition linkrel_compabove::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_compabove x y \<equiv> ((linkrel_compabove_topright x y) \<or> (linkrel_compabove_topleft x y) 
\<or> (linkrel_compabove_right x y) \<or> (linkrel_compabove_left x y) 
\<or> (linkrel_compabove_centerleft x y) \<or> (linkrel_compabove_centerright x y))"

text{*definition compess*}
definition linkrel_compress::"diagram \<Rightarrow> diagram => bool"
where
"linkrel_compress x y \<equiv> (linkrel_compress_null x y) \<or> (linkrel_compbelow x y) 
\<or> (linkrel_compabove x y)"

text{*slide relation refer to the relation where a crossing is slided over a vertical strand*}
definition linkrel_slide_left::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_slide_left x y \<equiv> \<exists>y1.\<exists>y2.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>C.
((x = Abs_diagram((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))\<circ>(y2))) \<and>
(y = Abs_diagram((y1)\<circ>(basic (C\<otimes>w1))\<circ>(basic (A\<otimes>w2))\<circ>(y2)))
\<and> ((snd (count w1)) = (fst (count w2)))
\<and> (strands B)
\<and> (strands C))"

definition linkrel_slide_right::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_slide_right x y \<equiv> \<exists>y1.\<exists>y2.\<exists>z1.\<exists>z2.\<exists>A.\<exists>B.\<exists>C.
((x = Abs_diagram((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B))\<circ>(y2))) \<and>
(y = Abs_diagram((y1)\<circ>(basic (z1\<otimes>C))\<circ>(basic (z2\<otimes>A))\<circ>(y2)))
\<and> ((snd (count z1)) = (fst (count z2)))
\<and> (strands B)
\<and> (strands C))"

definition linkrel_slide::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"linkrel_slide x y \<equiv> ((linkrel_slide_left x y) \<or> (linkrel_slide_right x y))"

text{*linkrel_definition*}

definition linkrel::"diagram =>diagram\<Rightarrow>bool"
where
"linkrel x y = ((linkrel_uncross x y) \<or> (linkrel_pull x y) \<or> (linkrel_straighten x y) 
\<or>(linkrel_swing x y)\<or>(linkrel_rotate x y) \<or> (linkrel_compress x y) \<or> (linkrel_slide x y)
\<or>  (linkrel_uncross y x) \<or> (linkrel_pull y x) \<or> (linkrel_straighten y x) 
\<or>(linkrel_swing y x)\<or>(linkrel_rotate y x) \<or> (linkrel_compress y x) \<or> (linkrel_slide y x))
"

text{*we defined the link relations for a framed link, which are the same as those of unframed 
links excluding the uncross relation which straightens out a cross*}

definition framed_linkrel::"diagram =>diagram\<Rightarrow>bool"
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
definition linkrel_equiv::"diagram\<Rightarrow>diagram\<Rightarrow>bool"
where
"(linkrel_equiv) = (linkrel)^**" 


definition framed_linkrel_equiv::"diagram\<Rightarrow>diagram\<Rightarrow>bool"
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


end
