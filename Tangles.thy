theory Tangles
imports Datatype Main Typedef 
begin

(*introductory lemma on relations*)

lemma symmetry1: assumes "symp R" 
shows "\<forall>x y. (x, y) \<in> {(x, y). R x y}\<^sup>* \<longrightarrow> (y, x) \<in> {(x, y). R x y}\<^sup>*" 
proof-
fix x y
have  "R x y \<longrightarrow>  R y x" by (metis assms sympD)
then have " (x, y) \<in> {(x, y). R x y} \<longrightarrow> (y, x) \<in> {(x, y). R x y}" by auto
then have 2:"\<forall> x y. (x, y) \<in> {(x, y). R x y} \<longrightarrow> (y, x) \<in> {(x, y). R x y}"
 by (metis (full_types) assms mem_Collect_eq split_conv sympE)
then have "sym {(x, y). R x y}" unfolding sym_def by auto
then have 3: "sym (rtrancl {(x, y). R x y})" using sym_rtrancl by auto
then show ?thesis by (metis symE)
qed

lemma symmetry2: assumes "\<forall>x y. (x, y) \<in> {(x, y). R x y}\<^sup>* \<longrightarrow> (y, x) \<in> {(x, y). R x y}\<^sup>* "
shows "symp R^**" 
unfolding symp_def Enum.rtranclp_rtrancl_eq assms by (metis assms)

lemma symmetry3: assumes "symp R" shows "symp R^**" using assms symmetry1 symmetry2 by metis



(*each  block is a horizontal block built by putting basic tangle bricks next to each other.
(1) e_vert is the straight line
(2) e_cup is the up facing cusp
(3) e_cap is the bottom facing cusp
(4) e_over is the positive cross
(5) e_under is the negative cross*)

datatype brick = vert
                |cup
                |cap
                |over
                |under

datatype block = cement brick
                 |cons brick block  (infixr "#" 60)              

primrec bricklength::"brick \<Rightarrow> nat"
where
"bricklength vert = 1"|
"bricklength cup =  1"|
"bricklength cap =  1"|
"bricklength over =  1"|
"bricklength under =  1"

primrec length::"block \<Rightarrow> nat"
where
"length (cement x) = bricklength x"|
"length (cons x y) = (bricklength x) + (length y)"


definition e_vert::block where "e_vert \<equiv> (cement vert)"
definition e_cup::block where "e_cup \<equiv> (cement cup)"
definition e_cap::block where "e_cap \<equiv> (cement cap)"
definition e_over::block where "e_over \<equiv> (cement over)"
definition e_under::block where "e_under \<equiv> (cement under)"


(*count tells us the number of incoming and outgoing strangs of each block*)

primrec brickcount::"brick \<Rightarrow> int \<times> int "
where
"brickcount vert = (1,1)"|
"brickcount cup = (0,2)"|
"brickcount cap = (2,0)"|
"brickcount over = (2,2)"|
"brickcount under = (2,2)"


primrec count::"block \<Rightarrow> int \<times> int "
where
"count (cement x) = (brickcount x)"
|"count (cons x y) = (fst (brickcount x) + fst (count y), snd (brickcount x) + snd (count y))"

lemma e_vert_count:" count (e_vert) = (1,1)"
using e_vert_def brickcount.simps(1) count.simps(1) by metis

lemma e_cup_count:" count (e_cup) = (0,2)"
using e_cup_def brickcount.simps(2) count.simps(1) by metis


lemma e_cap_count:" count (e_cap) = (2,0)"
using e_cap_def brickcount.simps(3) count.simps(1) by metis

lemma e_over_count:" count (e_over) = (2,2)"
using e_over_def brickcount.simps(4) count.simps(1) by metis

lemma e_under_count:" count (e_under) = (2,2)"
using e_under_def brickcount.simps(5) count.simps(1) by metis



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


primrec append :: "block => block => block" (infixr "\<otimes>" 65) where
append_Nil: "(cement x) \<otimes> ys = cons x ys" |
append_Cons: "((x#xs)\<otimes>ys) = x#(xs\<otimes>ys)"

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


lemma trivial: "(count (vert # e_cup)) = (1,3)"
apply (simp add: e_cup_def)
done

(*cusp is defined*)

primrec brick_cusp::"brick \<Rightarrow> bool"
where
"brick_cusp vert = False"|
"brick_cusp cup = True"|
"brick_cusp cap = False"|
"brick_cusp over = False"|
"brick_cusp under = False"


primrec cusp::"block \<Rightarrow> bool"
where
"cusp (cement x) = brick_cusp x"|
"cusp (x#y) = (if (x= cup) then (cusp y) else False)"


lemma cusp_basic: "((cusp x) = False) \<Longrightarrow> 
((x=e_vert)\<or>(x=e_cap)\<or>(x=e_over)\<or>(x=e_under))\<or>(\<exists>y1.\<exists>y2.\<exists>y3.(x=(y1\<otimes>y2\<otimes>y3)\<and> 
((y1=e_vert)\<or>(y1=e_cap)\<or>(y1=e_over)\<or>(y1=e_under))\<or>(y2=e_vert)\<or>(y2=e_cap)\<or>(y2=e_over)\<or>(y2=e_under))\<or>((y3=e_vert)\<or>(y3=e_cap)\<or>(y3=e_over)\<or>(y3=e_under)))"
by metis



lemma brickcount_zero_implies_cup:"(fst (brickcount x)= 0) \<Longrightarrow> (x = cup)"
apply(case_tac "brickcount x")
apply(auto)
apply(case_tac "x")
apply(auto)
done

lemma brickcount_zero_implies_brick_cusp:"(fst (brickcount x)= 0) \<Longrightarrow> (brick_cusp x)"
apply(case_tac "brick_cusp x")
apply(simp add: brickcount_zero_implies_cup)
apply(auto)
apply(case_tac "x")
apply(auto)
done

lemma count_zero_implies_cusp:"(fst (count x)= 0) \<Longrightarrow> (cusp x)"
proof(induction x)
case (cement y)
have "(fst (count (cement y))) = (fst (brickcount y))" by auto
from this have " (fst (count (cement y)) = 0) \<equiv>((fst (brickcount y))=0)"  by auto
from this  have " (fst (count (cement y)) = 0)  \<Longrightarrow>(brick_cusp y)" using brickcount_zero_implies_brick_cusp
by auto
from this have "(fst (count (cement y)) = 0)  \<Longrightarrow>(cusp (cement y))" by auto 
from this show ?case using cement.prems by (auto) 
next
case (cons a y)
show ?case 
proof-
have step1: "fst (count (a # y)) = fst (brickcount a) + (fst  (count y))" by auto
from this and fst_count_zero_sum have"fst (count y) = 0" 
by (metis Tangles.append.append_Nil cons.prems fst_count_additive)
from this have step2: "(cusp y)" using cons.IH by (auto) 
from this and step1 and fst_count_zero_sum  have "fst (brickcount a)= 0" by (metis cons.prems count.simps(1))
from this have "brick_cusp a" using brickcount_zero_implies_brick_cusp by auto
from this and assms have "a=cup" using brick_cusp_def 
by (metis `fst (brickcount a) = 0` brickcount_zero_implies_cup)
from this and step2 have "cusp (a#y)" using cusp_def by auto
from this show ?case by auto
qed
qed



(*cusp ends*)

primrec makestrand:: "nat \<Rightarrow> block"
where
"makestrand 0 = e_vert"
|"makestrand (Suc n) = vert#(makestrand n)"

(*walls are tangle diagrams obtained by placing a horizontal blocks a top each other*)

datatype walls = basic block
                |prod block  walls  (infixr "*" 66)

primrec compose :: "walls => walls => walls" (infixr "\<circ>" 66) where
compose_Nil: "(basic x) \<circ> ys =  prod x ys" |
compose_Cons: "((prod x xs)\<circ>ys) = prod x (xs\<circ>ys)"

lemma compose_leftassociativity: "(((x::walls) \<circ> y) \<circ> z) = (x\<circ>y \<circ>z)"
apply(induct_tac x)
apply(auto)
done

lemma compose_rightassociativity: "(x::walls) \<circ> (y \<circ> z) = (x\<circ>y \<circ>z)"
apply(induct_tac x)
apply(auto)
done


primrec wall_count:: "walls \<Rightarrow> int \<times> int" where
"wall_count (basic x) = count x"                                               
|"wall_count (x*ys) = (fst (count x),snd (wall_count ys))"


lemma wall_count_compose: "wall_count (xs\<circ>ys) = (fst (wall_count (xs)), snd(wall_count (ys)))"
apply(induct_tac xs)
apply(auto)
done 

definition abs::"int \<Rightarrow> int" where
"abs x \<equiv> if (x\<ge>0) then x else (0-x)" 

(*theorems about abs*)
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


primrec wall_list:: "walls \<Rightarrow> int list" where
"wall_list (basic x) = []"|
"wall_list (x * y) =  (abs (fst(wall_count y) - snd(count x)))#(wall_list y)"

lemma wall_list_compose: " wall_list (x \<circ> y) = 
(wall_list x)@((abs (fst(wall_count y) - snd(wall_count x)))#(wall_list y))"
apply(induct_tac x)
apply(auto)
apply(simp add: wall_count_compose)
done

(*test exercises*)

lemma trivial2: "wall_list (basic e_vert) = []"
apply(auto)
done


lemma trivial3: "fst(wall_count (basic e_cap))- snd(wall_count (basic e_vert)) = 1"
apply(simp add:e_cap_def e_vert_def)
done

lemma trivial4: "wall_list ((basic e_cap)\<circ>(basic e_vert)\<circ>(basic e_vert)) = [1,0]"
apply(simp add: e_cap_def e_vert_def)
apply(simp add:abs_def)
done


(*end of test exercises*)

primrec list_sum::"int list \<Rightarrow> int" 
where
"list_sum [] = 0"|
"list_sum (x#xs) = x+ list_sum xs"

lemma list_sum_non_negative:"list_sum(wall_list x) \<ge> 0"
apply(induct_tac x)
apply(auto)
apply(simp add: abs_non_negative)
done

(*diagram checks when a wall represents a knot diagram*)
definition well_defined::"walls \<Rightarrow> bool" where
"well_defined x \<equiv> ( (list_sum (wall_list x)+(abs(fst(wall_count x))
+ abs(snd(wall_count x)))) = 0)"

typedef diagram = "{(x::walls). well_defined x}"
apply (rule_tac x = "prod e_cup (basic e_cap)" in exI)
apply(auto)
apply(simp add:abs_def e_cup_def e_cap_def well_defined_def)
done

(*well_defined properties*)

lemma Abs_Rep_well_defined: assumes " well_defined x" shows "Rep_diagram (Abs_diagram x) = x"
using Rep_diagram Abs_diagram_inverse assms mem_Collect_eq  by auto


lemma Rep_Abs_well_defined: assumes " well_defined x"  and "well_defined y" 
and  "(Abs_diagram x) = (Abs_diagram y)"
shows "x = y"
using Rep_diagram Abs_diagram_inverse assms mem_Collect_eq  by metis


(* statement about diagrams*)
lemma well_defined_composition: 
"((list_sum (wall_list (Rep_diagram z))+(abs(fst(wall_count (Rep_diagram z)))
+ abs(snd(wall_count (Rep_diagram z))))) = 0)"
using Rep_diagram mem_Collect_eq well_defined_def by (metis (mono_tags))


lemma diagram_list_sum: 
"((list_sum (wall_list (Rep_diagram z))) = 0)"
using well_defined_composition abs_non_negative_sum list_sum_non_negative
abs_non_negative add_increasing add_nonneg_eq_0_iff
by metis 


lemma diagram_fst_wall_count: 
"(abs (fst (wall_count (Rep_diagram z))) = 0)"
using well_defined_composition abs_non_negative_sum list_sum_non_negative
abs_non_negative add_increasing add_nonneg_eq_0_iff wall_count_def
by metis


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

lemma wall_list_list_sum_non_negative:
"(list_sum (wall_list x)) \<ge> 0"
apply(induct_tac x) 
apply(auto)
apply (simp add: abs_non_negative add_increasing)
done

lemma wall_list_list_sum_abs:
"(list_sum (wall_list x)) = abs (list_sum (wall_list x))"
using wall_list_list_sum_non_negative abs_def by auto


lemma wall_list_list_sum_zero_add:
assumes "(list_sum (wall_list x)) + (list_sum (wall_list y)) = 0"
shows "(list_sum (wall_list x)) = 0" and "(list_sum (wall_list y)) = 0"
using abs_non_negative_sum wall_list_list_sum_abs assms 
apply metis 
by (metis add_nonneg_eq_0_iff assms wall_list_list_sum_non_negative)

lemma list_sum_append:
"list_sum (x@y) = (list_sum x) + (list_sum y)"
apply(induct_tac x)
apply(auto)
done

lemma wall_list_list_sum_compose:
"(list_sum (wall_list (x \<circ> y))) = 
(list_sum (wall_list x)) + (abs ( (fst (wall_count y)) - (snd (wall_count x)))) + 
(list_sum (wall_list y))"
using wall_list_compose list_sum_def append_def list_sum_append
by (metis ab_semigroup_add_class.add_ac(1) list_sum.simps(2))


lemma list_sum_compose: assumes "list_sum (wall_list x) = 0" and "list_sum (wall_list y) = 0"
and "(snd (wall_count x))= (fst (wall_count y))"
shows  "list_sum (wall_list (x\<circ>y)) = 0"
proof-
from  wall_list_list_sum_compose and assms and abs_def 
have "list_sum (wall_list (x\<circ>y)) = (list_sum (wall_list x))+(list_sum (wall_list y))"
by auto
from this and assms have "list_sum (wall_list (x\<circ>y)) = 0" by auto
from this show ?thesis by auto
qed

lemma diagram_wall_list:
assumes "(abs ( (fst (wall_count y)) - (snd (wall_count x))))>0"
shows "(list_sum (wall_list (x\<circ>y)) > 0)"
proof-
have "(list_sum (wall_list x) \<ge>0)" and "(list_sum (wall_list y)\<ge>  0)"  using 
wall_list_list_sum_non_negative by auto
then have  "(abs ( (fst (wall_count y)) - (snd (wall_count x))))>0" using assms by auto
then have "((list_sum (wall_list x)) + (abs ( (fst (wall_count y)) - (snd (wall_count x)))) + 
(list_sum (wall_list y))) > 0"
using abs_non_negative add_increasing add_nonneg_eq_0_iff
comm_monoid_add_class.add.left_neutral comm_semiring_1_class.normalizing_semiring_rules(24) 
le_neq_trans not_le order_refl wall_list_list_sum_non_negative well_defined_def by (metis add_strict_increasing2)
then have "(list_sum (wall_list (x \<circ> y))) = 
((list_sum (wall_list x)) + (abs ( (fst (wall_count y)) - (snd (wall_count x)))) + 
(list_sum (wall_list y)))" using wall_list_list_sum_compose by auto
then have  "(list_sum (wall_list (x \<circ> y))) > 0" 
by (metis 
`0 < list_sum (wall_list x) + Tangles.abs (fst (wall_count y) - snd (wall_count x)) + 
list_sum (wall_list y)`)
then show ?thesis by auto
qed

lemma diagram_wall_list_zero:
assumes "(list_sum (wall_list (x\<circ>y)) = 0)"
shows " (abs ( (fst (wall_count y)) - (snd (wall_count x))))=0"
using diagram_wall_list list_sum_non_negative abs_non_negative assms less_le by (metis)



lemma diagram_list_sum_zero:
 assumes "well_defined x"
shows "list_sum (wall_list x) = 0" 
proof-
have "list_sum (wall_list (Rep_diagram (Abs_diagram x))) = 0" using diagram_list_sum by metis
then have "Rep_diagram (Abs_diagram x) = x" using Abs_diagram_inverse assms mem_Collect_eq
by (auto)
then have "list_sum (wall_list x) = 0" using `list_sum (wall_list (Rep_diagram (Abs_diagram x))) = 0`
by (metis)
then show ?thesis by simp  
qed


lemma diagram_compose:
assumes "well_defined (x\<circ>y)"
shows " (abs ( (fst (wall_count y)) - (snd (wall_count x))))=0"
using diagram_list_sum_zero diagram_wall_list_zero assms by auto


lemma diagram_fst_equals_snd:
assumes "well_defined (x\<circ>y)"
shows " (fst (wall_count y)) = (snd (wall_count x))"
using diagram_compose abs_zero_equality assms  by auto

lemma diagram_list_sum_subsequence:
assumes "well_defined (x\<circ>y)"
shows "(list_sum (wall_list x) = 0)\<and>(list_sum (wall_list y) = 0)"
proof-
have "(abs ( (fst (wall_count y)) - (snd (wall_count x)))) = 0" using diagram_compose assms
by auto
from this have "(list_sum (wall_list x)) + (list_sum (wall_list y)) = 0" using diagram_list_sum_zero
wall_list_list_sum_compose assms plus_int_code(1)  by metis
from this have goal1: "(list_sum (wall_list x)) = 0" and goal2:"(list_sum (wall_list y)) = 0" using 
wall_list_list_sum_zero_add by auto
from this have "(list_sum (wall_list x) = 0)\<and>(list_sum (wall_list y) = 0)" by auto
from this show ?thesis by simp
qed
(*tangle relations are being defined here. Tangle equivalence is broken into many equivalances each 
of which is defined as a disjunction of many functions.*)
(*tangle_uncross*)

definition tanglerel_uncross_positiveflip::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross_positiveflip x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_vert\<otimes>e_cup\<otimes>w1)\<circ>(basic (z2\<otimes>e_over\<otimes>e_vert\<otimes>w2))\<circ>(basic (z3\<otimes>e_vert\<otimes>e_cap\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e_cup\<otimes>e_vert\<otimes>w1))\<circ>(basic (z2\<otimes>e_vert\<otimes>e_over\<otimes>w2))\<circ>(basic (z3\<otimes>e_cap\<otimes>e_vert\<otimes>w3))\<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))) \<and> ((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_positivestraighten::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross_positivestraighten x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_cup\<otimes>e_vert\<otimes>w1)\<circ>(basic (z2\<otimes>e_vert\<otimes>e_over\<otimes>w2))\<circ>(basic (z3\<otimes>e_cap\<otimes>e_vert\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e_vert\<otimes>w1))\<circ>(basic (z2\<otimes>e_vert\<otimes>w2))\<circ>(basic (z3\<otimes>e_vert\<otimes>w3))\<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))) \<and> ((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_negativeflip::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross_negativeflip x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_vert\<otimes>e_cup\<otimes>w1)\<circ>(basic (z2\<otimes>e_under\<otimes>e_vert\<otimes>w2))\<circ>(basic (z3\<otimes>e_vert\<otimes>e_cap\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e_cup\<otimes>e_vert\<otimes>w1))\<circ>(basic (z2\<otimes>e_vert\<otimes>e_under\<otimes>w2))\<circ>(basic (z3\<otimes>e_cap\<otimes>e_vert\<otimes>w3))\<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))) \<and> ((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_negativestraighten::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross_negativestraighten x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_cup\<otimes>e_vert\<otimes>w1)\<circ>(basic (z2\<otimes>e_vert\<otimes>e_under\<otimes>w2))\<circ>(basic (z3\<otimes>e_cap\<otimes>e_vert\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e_vert\<otimes>w1))\<circ>(basic (z2\<otimes>e_vert\<otimes>w2))\<circ>(basic (z3\<otimes>e_vert\<otimes>w3))\<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))) \<and> ((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

(*tangle_uncross definition*)
definition tanglerel_uncross::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross x y \<equiv> 
((tanglerel_uncross_positiveflip x y)\<or>(tanglerel_uncross_positivestraighten x y)
\<or>(tanglerel_uncross_negativeflip x y)\<or>(tanglerel_uncross_negativestraighten x y))"
(*tangle_uncross ends*)
(*framed tanglerel_uncross*)

definition framed_tanglerel_uncross::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"framed_tanglerel_uncross x y \<equiv> 
((tanglerel_uncross_positiveflip x y)\<or>(tanglerel_uncross_negativeflip x y))"

lemma framed_uncross_implies_uncross: "(framed_tanglerel_uncross x y) \<Longrightarrow> (tanglerel_uncross x y)"
apply (simp add: framed_tanglerel_uncross_def tanglerel_uncross_def)
apply(auto)
done

(*tangle_pull begins*)

definition tanglerel_pull_posneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_posneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_over\<otimes>w1)\<circ>(basic (z2\<otimes>e_under\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e_vert\<otimes>e_vert\<otimes>w1))\<circ>(basic (z2\<otimes>e_vert\<otimes>e_vert\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2))))"


definition tanglerel_pull_negpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_negpos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_under\<otimes>w1)\<circ>(basic (z2\<otimes>e_over\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e_vert\<otimes>e_vert\<otimes>w1))\<circ>(basic (z2\<otimes>e_vert\<otimes>e_vert\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2))))"

(*tanglerel_pull definition*)
definition tanglerel_pull::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull x y \<equiv> ((tanglerel_pull_posneg x y) \<or> (tanglerel_pull_negpos x y))"                   

(*tanglerel_pull ends*)    
(*tanglerel_straighten*)

definition tanglerel_straighten_topdown::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_straighten_topdown x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_vert\<otimes>e_cup\<otimes>w1)\<circ>(basic (z2\<otimes>e_cap\<otimes>e_vert\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e_vert\<otimes>w1))\<circ>(basic (z2\<otimes>e_vert\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2))))"


definition tanglerel_straighten_downtop::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_straighten_downtop x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_cup\<otimes>e_vert\<otimes>w1)\<circ>(basic (z2\<otimes>e_vert\<otimes>e_cap\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e_vert\<otimes>w1))\<circ>(basic (z2\<otimes>e_vert\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2))))"


definition tanglerel_straighten_righttopdown::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_straighten_righttopdown x y \<equiv>  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e_vert\<otimes>e_cup\<otimes>w1)\<circ>(basic (e_cap\<otimes>e_vert\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e_vert\<otimes>w1))\<circ>(basic (e_vert\<otimes>w2))\<circ>(y2))))
 \<and> ((snd (count w1)) = (fst (count w2)))"


definition tanglerel_straighten_rightdowntop::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_straighten_rightdowntop x y \<equiv>  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e_cup\<otimes>e_vert\<otimes>w1)\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e_vert\<otimes>w1))\<circ>(basic (e_vert\<otimes>w2))\<circ>(y2))))
 \<and> ((snd (count w1)) = (fst (count w2)))"



definition tanglerel_straighten_lefttopdown::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_straighten_lefttopdown x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_cup\<otimes>e_vert)\<circ>(basic (z2\<otimes>e_vert\<otimes>e_cap)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e_vert))\<circ>(basic (z2\<otimes>e_vert))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2))))"


definition tanglerel_straighten_leftdowntop::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_straighten_leftdowntop x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_vert\<otimes>e_cup)\<circ>(basic (z2\<otimes>e_cap\<otimes>e_vert)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e_vert))\<circ>(basic (z2\<otimes>e_vert))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))"

(*definition straighten*)
definition tanglerel_straighten::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_straighten x y \<equiv> ((tanglerel_straighten_topdown x y) \<or> (tanglerel_straighten_downtop x y)
\<or>(tanglerel_straighten_righttopdown x y) \<or> (tanglerel_straighten_rightdowntop x y)
\<or>(tanglerel_straighten_lefttopdown x y) \<or> (tanglerel_straighten_leftdowntop x y))"



(*straighten ends*)
(*swing begins*)
definition tanglerel_swing_pos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_swing_pos x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_over\<otimes>e_vert\<otimes>w1)\<circ>(basic (z2\<otimes>e_vert\<otimes>e_over\<otimes>w2))\<circ>(basic (z3\<otimes>e_over\<otimes>e_vert\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e_vert\<otimes>e_over\<otimes>w1)\<circ>(basic (z2\<otimes>e_over\<otimes>e_vert\<otimes>w2))\<circ>(basic (z3\<otimes>e_vert\<otimes>e_over\<otimes>w3))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))\<and>((snd (count z2)) = (fst (count z3)))
 \<and> ((snd (count w1)) = (fst (count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

definition tanglerel_swing_neg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_swing_neg x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_under\<otimes>e_vert\<otimes>w1)\<circ>(basic (z2\<otimes>e_vert\<otimes>e_under\<otimes>w2))\<circ>(basic (z3\<otimes>e_under\<otimes>e_vert\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e_vert\<otimes>e_under\<otimes>w1)\<circ>(basic (z2\<otimes>e_under\<otimes>e_vert\<otimes>w2))\<circ>(basic (z3\<otimes>e_vert\<otimes>e_under\<otimes>w3))\<circ>(y2)))))
\<and>((snd (count z1)) = (fst (count z2)))\<and>((snd (count z2)) = (fst (count z3)))
 \<and> ((snd (count w1)) = (fst (count w2)))\<and>((snd (count w2)) = (fst (count w3)))"

(*swing definition*)

definition tanglerel_swing::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_swing x y \<equiv> ((tanglerel_swing_pos x y) \<or> (tanglerel_swing_neg x y))"

(*swing ends*)
(* rotate moves*)

definition tanglerel_rotate_toppos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate_toppos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e_vert\<otimes>e_over\<otimes>w1))\<circ>(basic (z2\<otimes>e_cap\<otimes>e_vert\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_under\<otimes>e_vert\<otimes>w1)\<circ>(basic (z2\<otimes>e_vert\<otimes>e_cap\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2))))"


definition tanglerel_rotate_topneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate_topneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e_vert\<otimes>e_under\<otimes>w1))\<circ>(basic (z2\<otimes>e_cap\<otimes>e_vert\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_over\<otimes>e_vert\<otimes>w1)\<circ>(basic (z2\<otimes>e_vert\<otimes>e_cap\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2))))"

definition tanglerel_rotate_downpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate_downpos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e_cap\<otimes>e_vert\<otimes>w1))\<circ>(basic (z2\<otimes>e_vert\<otimes>e_over\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_vert\<otimes>e_cap\<otimes>w1)\<circ>(basic (z2\<otimes>e_under\<otimes>e_vert\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2))))"


definition tanglerel_rotate_downneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate_downneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.
\<exists>w1.\<exists>w2.\<exists>y2.
((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_cap\<otimes>e_vert\<otimes>w1))\<circ>(basic (z2\<otimes>e_vert\<otimes>e_under\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e_vert\<otimes>e_cap\<otimes>w1)\<circ>(basic (z2\<otimes>e_over\<otimes>e_vert\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2))))"


(*rotate definition*)


definition tanglerel_rotate::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate x y \<equiv> ((tanglerel_rotate_toppos x y) \<or> (tanglerel_rotate_topneg x y)
\<or> (tanglerel_rotate_downpos x y) \<or> (tanglerel_rotate_downneg x y))"

(*rotate ends*)

(*stranded operations begin*)

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


lemma strands_test: "strands (vert#cup#vert#e_vert) = False" using e_vert_def strands_def brickstrand_def
compose_def by auto

(*Compress -  Compress has two levels of equivalences. It is a composition of Compress_null, compbelow
and compabove. compbelow and compabove are further written as disjunction of many other relations.
Compbelow refers to when the bottom row is extended or compressed. Compabove*)

definition tanglerel_compress_null::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compress_null x y \<equiv>  \<exists>y2.\<exists>A.\<exists>B.((x = Abs_diagram
 ((A)\<circ>(basic B)\<circ>(y2)))\<and>(y = Abs_diagram ((A)\<circ>(y2)))
\<and> (strands B) \<and> ((snd (wall_count A))>0))"





(*two at a time*)

definition tanglerel_compbelow_right::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_right x y \<equiv>  \<exists>w1.\<exists>w2.\<exists>y2.\<exists>A.\<exists>B.((x= Abs_diagram
 ((basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram (
(basic w1)\<circ>(basic (B\<otimes>w2))\<circ>(y2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and> (strands B)
\<and> ((fst (count A)) = 0))"


definition tanglerel_compbelow_left::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_left x y \<equiv>  \<exists>z1.\<exists>z2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> ((y = Abs_diagram (
(basic (z1)\<circ>(basic (z2\<otimes>A)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>(strands B))"


definition tanglerel_compbelow_bottomright::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_bottomright x y \<equiv>  \<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((basic (A))\<circ>(basic (B\<otimes>w2))\<circ>(y2)))\<and> 
(y = Abs_diagram (
(basic (A\<otimes>w2))\<circ>(y2)))
\<and>(0 = (fst (count w2)))
\<and>(strands B))"


definition tanglerel_compbelow_bottomleft::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_bottomleft x y \<equiv>  \<exists>z2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((basic (A))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> 
(y = Abs_diagram (
(basic (A\<otimes>z2))\<circ>(y2)))
\<and>(0 = (fst (count z2)))
\<and>(strands B))"


definition tanglerel_compbelow_centerright::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_centerright x y \<equiv> \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (w1))\<circ>(basic (A\<otimes>w2))\<circ>(y2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>((fst (count A)) = 0)
\<and>(strands B))"


definition tanglerel_compbelow_centerleft::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_centerleft x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1))\<circ>(basic (z2\<otimes>A))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((fst (count A)) = 0)
\<and>(strands B))"



(*compbelow definition*)
definition tanglerel_compbelow::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow x y \<equiv> 
(tanglerel_compbelow_right x y) \<or> (tanglerel_compbelow_left x y)
\<or> (tanglerel_compbelow_centerleft x y) \<or> (tanglerel_compbelow_centerright x y)
"

(*comp above*)

definition tanglerel_compabove_right::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_right x y \<equiv>  \<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y1.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))))\<and> ((y = Abs_diagram (
(y1)\<circ>(basic (B\<otimes>w1)\<circ>(basic (w2))))))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>(strands A))"


definition tanglerel_compabove_left::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_left x y \<equiv>  \<exists>z1.\<exists>z2.\<exists>A.\<exists>B.\<exists>y1.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B))))\<and> ((y = Abs_diagram (
(y1)\<circ>(basic (B\<otimes>z1)\<circ>(basic (z2))))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>(strands A))"

definition tanglerel_compabove_topright::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_topright x y \<equiv>  \<exists>w1.\<exists>A.\<exists>B.\<exists>y1.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B))))\<and> ((y = Abs_diagram (
(y1)\<circ>(basic (B\<otimes>w1)))))
\<and>((snd (count w1)) = 0)
\<and>(strands A))"

definition tanglerel_compabove_topleft::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_topleft x y \<equiv>  \<exists>z1.\<exists>A.\<exists>B.\<exists>y1.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (B))))\<and> ((y = Abs_diagram (
(y1)\<circ>(basic (z1\<otimes>B)))))
\<and>((snd (count z1)) = 0)
\<and>(strands A))"
(*two at a time-center*)


definition tanglerel_compabove_centerleft::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_centerleft x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1\<otimes>B))\<circ>(basic (z2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count B)) = 0)
\<and>(strands A))"


definition tanglerel_compabove_centerright::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_centerright x y \<equiv> \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B \<otimes> w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (B\<otimes>w1))\<circ>(basic (w2))\<circ>(y2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>((snd (count B)) = 0)
\<and>(strands A))"
(*compabove definition*)

(*compbelow definition*)
definition tanglerel_compabove::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove x y \<equiv> ((tanglerel_compabove_topright x y) \<or> (tanglerel_compabove_topleft x y) 
\<or> (tanglerel_compabove_right x y) \<or> (tanglerel_compabove_left x y) 
\<or> (tanglerel_compabove_centerleft x y) \<or> (tanglerel_compabove_centerright x y))"

(*definition compess*)
definition tanglerel_compress::"diagram \<Rightarrow> diagram => bool"
where
"tanglerel_compress x y \<equiv> (tanglerel_compress_null x y) \<or> (tanglerel_compbelow x y) 
\<or> (tanglerel_compabove x y)"

(*slide*)
definition tanglerel_slide_left::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_slide_left x y \<equiv> \<exists>y1.\<exists>y2.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>C.
((x = Abs_diagram((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))\<circ>(y2))) \<and>
(y = Abs_diagram((y1)\<circ>(basic (C\<otimes>w1))\<circ>(basic (A\<otimes>w2))\<circ>(y2)))
\<and> ((snd (count w1)) = (fst (count w2)))
\<and> (strands B)
\<and> (strands C))"

definition tanglerel_slide_right::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_slide_right x y \<equiv> \<exists>y1.\<exists>y2.\<exists>z1.\<exists>z2.\<exists>A.\<exists>B.\<exists>C.
((x = Abs_diagram((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B))\<circ>(y2))) \<and>
(y = Abs_diagram((y1)\<circ>(basic (z1\<otimes>C))\<circ>(basic (z2\<otimes>A))\<circ>(y2)))
\<and> ((snd (count z1)) = (fst (count z2)))
\<and> (strands B)
\<and> (strands C))"

definition tanglerel_slide::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_slide x y \<equiv> ((tanglerel_slide_left x y) \<or> (tanglerel_slide_right x y))"

(*tanglerel_definition*)

definition tanglerel::"diagram =>diagram\<Rightarrow>bool"
where
"tanglerel x y = ((tanglerel_uncross x y) \<or> (tanglerel_pull x y) \<or> (tanglerel_straighten x y) 
\<or>(tanglerel_swing x y)\<or>(tanglerel_rotate x y) \<or> (tanglerel_compress x y) \<or> (tanglerel_slide x y)
\<or>  (tanglerel_uncross y x) \<or> (tanglerel_pull y x) \<or> (tanglerel_straighten y x) 
\<or>(tanglerel_swing y x)\<or>(tanglerel_rotate y x) \<or> (tanglerel_compress y x) \<or> (tanglerel_slide y x))
"


definition framed_tanglerel::"diagram =>diagram\<Rightarrow>bool"
where
"framed_tanglerel x y = ((framed_tanglerel_uncross x y) \<or> (tanglerel_pull x y) \<or> (tanglerel_straighten x y) 
\<or>(tanglerel_swing x y)\<or>(tanglerel_rotate x y) \<or> (tanglerel_compress x y) \<or> (tanglerel_slide x y)
\<or>  (framed_tanglerel_uncross y x) \<or> (tanglerel_pull y x) \<or> (tanglerel_straighten y x) 
\<or>(tanglerel_swing y x)\<or>(tanglerel_rotate y x) \<or> (tanglerel_compress y x) \<or> (tanglerel_slide y x))
"

lemma framed_tanglerel_implies_tanglerel: "(framed_tanglerel x y) \<Longrightarrow> (tanglerel x y)"
using framed_uncross_implies_uncross framed_tanglerel_def tanglerel_def by auto

(* lemmas for proving that equivalence is well defined*)
lemma tanglerel_symp: "symp tanglerel" unfolding tanglerel_def symp_def by auto

lemma framed_tanglerel_symp: "symp framed_tanglerel" unfolding framed_tanglerel_def symp_def by auto

 
definition tanglerel_equiv::"diagram\<Rightarrow>diagram\<Rightarrow>bool"
where
"(tanglerel_equiv) = (tanglerel)^**" 


definition framed_tanglerel_equiv::"diagram\<Rightarrow>diagram\<Rightarrow>bool"
where
"(framed_tanglerel_equiv) = (framed_tanglerel)^**" 
 

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

theorem framed_equiv_implies_tangleequiv: "(framed_tanglerel_equiv x y) \<Longrightarrow> (tanglerel_equiv x y)"
using  framed_tanglerel_equiv_def tanglerel_equiv_def transitive_implication  
framed_tanglerel_implies_tanglerel
by metis

lemma reflective: "tanglerel_equiv x x" unfolding tanglerel_equiv_def by simp

lemma framed_reflective: "framed_tanglerel_equiv x x" unfolding framed_tanglerel_equiv_def by simp

lemma tangle_symmetry:"symp tanglerel_equiv" using tanglerel_symp symmetry3 
by (metis (full_types) tanglerel_equiv_def)

lemma framed_tangle_symmetry:"symp framed_tanglerel_equiv" using framed_tanglerel_symp symmetry3 
by (metis (full_types) framed_tanglerel_equiv_def)

(*tangles upto equivalence are well defined*)
(*Tangle- Definition and the proof of being well defined*)

quotient_type Tangle = "diagram" / "tanglerel_equiv"
 morphisms Rep_tangles Abs_tangles
proof (rule equivpI)
show "reflp tanglerel_equiv" unfolding reflp_def reflective by (metis reflective)
show "symp tanglerel_equiv" using tangle_symmetry by auto
show "transp tanglerel_equiv" unfolding transp_def tanglerel_equiv_def rtranclp_trans by auto  
qed

quotient_type Framed_Tangle = "diagram" / "framed_tanglerel_equiv"
 morphisms Rep_framed_tangles Abs_framed_tangles
proof (rule equivpI)
show "reflp framed_tanglerel_equiv" unfolding reflp_def framed_reflective by (metis framed_reflective)
show "symp framed_tanglerel_equiv" using framed_tangle_symmetry by auto
show "transp framed_tanglerel_equiv" unfolding transp_def framed_tanglerel_equiv_def rtranclp_trans by auto  
qed

(*proof zone*)
lemma strand_makestrand: " strands (makestrand n)" 
apply(induct_tac n)
apply(auto)
apply(simp add:e_vert_def)
done

lemma test_00: "(makestrand (n+1)) = vert#(makestrand n)" by auto

lemma test_0: "(makestrand (n+1)) = e_vert\<otimes>(makestrand n)" using e_vert_def test_00 append_Nil by metis


lemma test_1: "(makestrand (n+1)) = (makestrand n)\<otimes>e_vert" 
apply(induct_tac n)
apply(auto)
apply(simp add:e_vert_def)
apply (metis Tangles.append.append_Nil leftright_associativity)
done

type_synonym convert = "block => nat"

definition fstcount:: convert  where "(fstcount x) = (nat (abs ((fst (count x)))))"

definition sndcount:: convert  where "(sndcount x) = (nat (snd (count x)))"


lemma makestrand_fstequality:"(fst (count (makestrand n))) = (int n)+1" 
apply (induct_tac n)
apply(auto)
apply(simp add: e_vert_def)
done

lemma makestrand_sndequality:"(snd (count (makestrand n))) = (int n)+1" 
apply (induct_tac n)
apply(auto)
apply(simp add: e_vert_def)
done

lemma makestrand_fstsndequality:"(fst (count (makestrand n))) = (snd (count (makestrand n)))" 
apply (induct_tac n)
apply(auto simp add:e_vert_def)
done

lemma nat_int:" ((int n)\<ge> 0)" by auto

lemma makestrands_positivelength:"(fst (count (makestrand n)))>0" using  nat_int makestrand_fstequality
by auto

lemma strands_even: "((a = Abs_diagram (x \<circ>(basic y)\<circ> z)) \<and> (strands y)) \<Longrightarrow> (length y) > 1"
proof-
oops

(*general theorems*)

theorem tanglerel_doublecompress_top: 
assumes "(snd (count y1))>1" and "(z4 = makestrand (nat ((snd (count y1)) + (-2))+1))"
and "w4 = makestrand  (nat ((snd (count y1)) + (-2)))"
shows "tanglerel_equiv (Abs_diagram (x1 \<circ> basic y1 \<circ> basic z4\<circ>basic z4\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 

proof-
let ?k = " (nat ((snd (count y1))+ (-2) ))" 

have C: " (z4 = makestrand (?k+1))" using assms by auto
let ?x2 = "x1 \<circ> (basic y1)"


have preliminary_result1:"((snd (count y1))+(-1))>0" using assms by auto
have preliminary_result2:"((snd (count y1))+(-2))\<ge>0" using assms by auto
have preliminary_result3: "strands z4" using C strand_makestrand by auto

have subresult0: "snd (wall_count ?x2) = snd (wall_count (basic y1))" 
           using wall_count_compose 
             by auto
have subresult1: "... = snd (count y1)" using wall_count_compose 
            by auto
have subresult2: "snd (wall_count ?x2) > 0"
            using subresult1 assms less_trans subresult0 zero_less_one 
            by auto
have subresult3: "fst (count (z4)) = fst (count (makestrand (?k+1)))"  
            using C makestrand_fstequality
            by auto
have subresult4: "fst (count (makestrand (?k+1))) = int(?k+1)+1"  
            using makestrand_fstequality
            by auto
have subresult5:"fst (count (z4)) =  int(?k)+2" 
           using subresult3 subresult4 
           by auto
have subresult6: "int (nat (snd (count y1) + -2)) = (snd (count y1)) + -2" 
           using int_nat_eq preliminary_result2
           by auto
have subresult7: "snd (count y1) = int(?k)+2" 
           using subresult6 
           by auto
have subresult8: "fst (count (z4)) = (snd (count y1))" 
           using subresult5 subresult7 
           by auto
have subresult_compress1: 
"(tanglerel_compress_null ((Abs_diagram (?x2\<circ>(basic z4)\<circ>z1))) (Abs_diagram (?x2\<circ>z1)))" 
           using tanglerel_compress_null_def
           preliminary_result3 subresult0 subresult2
             by metis
have subresult_equiv1: 
"(tanglerel_equiv ((Abs_diagram (?x2\<circ>(basic z4)\<circ>z1))) (Abs_diagram (?x2\<circ>z1)))" 
           using r_into_rtranclp subresult_compress1 tanglerel_equiv_def tanglerel_def  
           tanglerel_compress_def
                     by (metis)
have subresult_compress2: 
"(tanglerel_compress_null ((Abs_diagram ((?x2 \<circ> basic z4)\<circ>(basic z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ> basic z4)\<circ>z1)))" 
               using tanglerel_compress_null_def preliminary_result3 subresult0 subresult2   
               compose_leftassociativity
                    by (metis)
have subresult_equiv2: 
"(tanglerel_equiv ((Abs_diagram ((?x2 \<circ> basic z4)\<circ>(basic z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ> basic z4)\<circ>z1)))" 
               using tanglerel_compress_def tanglerel_def tanglerel_equiv_def
               r_into_rtranclp subresult_compress2   
                    by (metis)
have subresult_equiv3: 
"tanglerel_equiv ((Abs_diagram ((?x2 \<circ> basic z4)\<circ>(basic z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ>z1)))" 
               using tanglerel_equiv_def rtranclp_trans subresult_equiv1 subresult_equiv2 
               compose_leftassociativity
                            by (metis) 
have step1: 
"tanglerel_equiv (Abs_diagram (x1 \<circ> basic y1 \<circ> basic z4\<circ>basic z4\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using compose_leftassociativity subresult_equiv3 
               by auto

from step1 show ?thesis by auto
qed

theorem tanglerel_doublecompress_below:
assumes "(snd (wall_count x1))>1" and "(z4 = makestrand (nat ((snd (wall_count x1)) + (-2))+1))"
and "w4 = makestrand  (nat ((snd (wall_count x1)) + (-2)))"
shows "tanglerel_equiv (Abs_diagram (x1 \<circ> basic z4\<circ>basic z4 \<circ> basic y1\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))" 
proof-    

(*
assume A: "snd (count y1) >1" 
*)
let ?k = " (nat ((snd (wall_count x1))+ (-2) ))" 

have C: " (z4 = makestrand (?k+1))" using assms by auto
let ?x2 = "x1 \<circ> (basic y1)"


have preliminary_result1:"((snd (wall_count x1))+(-1))>0" using assms by auto
have preliminary_result2:"((snd (wall_count x1))+(-2))\<ge>0" using assms by auto
have preliminary_result3: "strands z4" using C strand_makestrand by auto

have subresult3: "fst (count (z4)) = fst (count (makestrand (?k+1)))"  
            using C makestrand_fstequality
            by auto
have subresult4: "fst (count (makestrand (?k+1))) = int(?k+1)+1"  
            using makestrand_fstequality
            by auto
have subresult5:"fst (count (z4)) =  int(?k)+2" 
           using subresult3 subresult4 
           by auto
have subresult6: "int (nat (snd (wall_count x1) + -2)) = (snd (wall_count x1)) + -2" 
           using int_nat_eq preliminary_result2
           by auto
have subresult7: "snd (wall_count x1) = int(?k)+2" 
           using subresult6 
           by auto
have subresult8: "fst (count (z4)) = (snd (wall_count x1))" 
           using subresult5 subresult7 
           by auto
have subresult_compress1: 
"(tanglerel_compress_null ((Abs_diagram (x1\<circ>(basic z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1)))" 
           using tanglerel_compress_null_def
           preliminary_result3 subresult8
                   by (metis C comm_semiring_1_class.normalizing_semiring_rules(24) makestrand_fstequality monoid_add_class.add.left_neutral of_nat_Suc zless_iff_Suc_zadd)
have subresult_equiv1: 
"(tanglerel_equiv  ((Abs_diagram (x1\<circ>(basic z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1)))" 
           using r_into_rtranclp subresult_compress1 tanglerel_equiv_def tanglerel_def  
           tanglerel_compress_def
                     by (metis)
have subresult_compress2: 
"(tanglerel_compress_null  ((Abs_diagram (x1\<circ>(basic z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1))) " 
               using tanglerel_compress_null_def preliminary_result3   
               compose_leftassociativity subresult_compress1
                   by auto
           
let ?z2 = "((basic z4)\<circ>(basic y1)\<circ>z1)"

have subresult_equiv2: 
"(tanglerel_compress_null (Abs_diagram (x1 \<circ> (basic z4)\<circ>(?z2)))
                           (Abs_diagram (x1\<circ>(?z2))))"
               using tanglerel_compress_null_def  C
               C comm_semiring_1_class.normalizing_semiring_rules(24) 
               int_one_le_iff_zero_less makestrand_fstequality preliminary_result3 
               subresult8 zle_iff_zadd
               by metis

have subresult_equiv3: 
"tanglerel_equiv (Abs_diagram (x1 \<circ> (basic z4)\<circ>(?z2))) 
                            (Abs_diagram (x1 \<circ> (?z2)))" 
               using tanglerel_equiv_def tanglerel_compress_def subresult_equiv2
                        by (metis (full_types) r_into_rtranclp tanglerel_def)
have subresult_equiv4: 
"tanglerel_equiv (Abs_diagram (x1 \<circ> basic z4\<circ>basic z4 \<circ> basic y1\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> (basic z4)\<circ>(basic y1)\<circ>z1))" 
               using compose_leftassociativity subresult_equiv3
               by auto
have step1: 
"tanglerel_equiv (Abs_diagram (x1 \<circ> basic z4\<circ>basic z4 \<circ> basic y1\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))" 
               using compose_leftassociativity subresult_equiv3 subresult_equiv1 rtranclp_trans
               by (metis (full_types) Tangle.abs_eq_iff )
from step1 show ?thesis by auto
qed

(*metaequivalence moves*)

theorem metaequivalence_left: 
assumes "(snd (count y1))>1"
and "w4 = makestrand  (nat ((snd (count y1)) + (-2)))"
shows "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))
             (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
proof-
let ?z4 = "makestrand (nat ((snd (count y1)) + (-2))+1)"                                                                                           
let ?k = " (nat ((snd (count y1))+ (-2) ))" 

have C: " (?z4 = makestrand (?k+1))" using assms by auto
let ?x2 = "x1 \<circ> (basic y1)"

have preliminary_result1:"((snd (count y1))+(-1))>0" using assms by auto
have preliminary_result2:"((snd (count y1))+(-2))\<ge>0" using assms by auto
have preliminary_result3: "strands ?z4" using C strand_makestrand by auto

have subresult0: "snd (wall_count ?x2) = snd (wall_count (basic y1))" 
           using wall_count_compose 
             by auto
have subresult1: "... = snd (count y1)" using wall_count_compose 
            by auto
have subresult2: "snd (wall_count ?x2) > 0"
            using subresult1 assms less_trans subresult0 zero_less_one 
            by auto
have subresult3: "fst (count (?z4)) = fst (count (makestrand (?k+1)))"  
            using C makestrand_fstequality
            by auto
have subresult4: "fst (count (makestrand (?k+1))) = int(?k+1)+1"  
            using makestrand_fstequality
            by auto
have subresult5:"fst (count (?z4)) =  int(?k)+2" 
           using subresult3 subresult4 
           by auto
have subresult6: "int (nat (snd (count y1) + -2)) = (snd (count y1)) + -2" 
           using int_nat_eq preliminary_result2
           by auto
have subresult7: "snd (count y1) = int(?k)+2" 
           using subresult6 
           by auto
have subresult8: "fst (count (?z4)) = (snd (count y1))" 
           using subresult5 subresult7 
           by auto
have subresult_compress1: 
"(tanglerel_compress_null ((Abs_diagram (?x2\<circ>(basic ?z4)\<circ>z1))) (Abs_diagram (?x2\<circ>z1)))" 
           using tanglerel_compress_null_def
           preliminary_result3 subresult0 subresult2
             by metis
have subresult_equiv1: 
"(tanglerel_equiv ((Abs_diagram (?x2\<circ>(basic ?z4)\<circ>z1))) (Abs_diagram (?x2\<circ>z1)))" 
           using r_into_rtranclp subresult_compress1 tanglerel_equiv_def tanglerel_def  
           tanglerel_compress_def
                     by (metis)
have subresult_compress2: 
"(tanglerel_compress_null ((Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>(basic ?z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>z1)))" 
               using tanglerel_compress_null_def preliminary_result3 subresult0 subresult2   
               compose_leftassociativity
                    by (metis)
have subresult_equiv2: 
"(tanglerel_equiv ((Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>(basic ?z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>z1)))" 
               using tanglerel_compress_def tanglerel_def tanglerel_equiv_def
               r_into_rtranclp subresult_compress2   
                    by (metis)
have subresult_equiv3: 
"tanglerel_equiv ((Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>(basic ?z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ>z1)))" 
               using tanglerel_equiv_def rtranclp_trans subresult_equiv1 subresult_equiv2 
               compose_leftassociativity
                            by (metis) 
have step1: 
"tanglerel_equiv (Abs_diagram (x1 \<circ> basic y1 \<circ> basic ?z4\<circ>basic ?z4\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using compose_leftassociativity subresult_equiv3 
               by auto

(*step 2 - inducing cusp*)

have w_subst: "w4 = (makestrand ?k)" using assms by auto

have step2_subresult0: "(makestrand (?k+1)) = (e_vert\<otimes>(makestrand ?k))" 
 apply(simp add: e_vert_def)
 done

have step2_subresult1:"?z4 = e_vert\<otimes>(makestrand ?k)" using C step2_subresult0 by auto

have step2_subresult2: "(Abs_diagram (?x2 \<circ> (basic ?z4) \<circ>(basic ?z4)\<circ>z1)) =
(Abs_diagram (?x2  \<circ> (basic (e_vert\<otimes>w4))\<circ> (basic (e_vert \<otimes>w4))\<circ>z1))" 
                        using w_subst step2_subresult1 by auto

have step2_subresult3: "(snd (count w4)) = (fst (count w4))" using makestrand_fstsndequality w_subst
by auto

let ?x = "(Abs_diagram (?x2 \<circ>(basic (e_cup\<otimes>e_vert\<otimes>w4))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))"
let ?y = "(Abs_diagram (?x2 \<circ>(basic (e_vert\<otimes>w4))\<circ>(basic (e_vert\<otimes>w4))\<circ>z1))"

have step2_subresult4:
"\<exists>y1.\<exists>y2.\<exists>w1.\<exists>w2.(?x = Abs_diagram (y1 \<circ> (basic (e_cup \<otimes> e_vert \<otimes> w1)) \<circ> (basic (e_vert \<otimes> e_cap \<otimes> w2)) \<circ> y2))"
  using exI by auto
 
have step2_subresult5:
"\<exists>y1.\<exists>y2.\<exists>w1.\<exists>w2.(?y = Abs_diagram (y1 \<circ> (basic (e_vert \<otimes> w1)) \<circ> (basic (e_vert \<otimes> w2)) \<circ> y2))"
 using exI by auto

have step2_subresult6: 
" (\<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.((?x = Abs_diagram ((y1)
\<circ>(basic (e_cup\<otimes>e_vert\<otimes>w1)\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w2)))\<circ>(y2)))\<and>(?y = Abs_diagram
 ((y1)
\<circ>(basic (e_vert\<otimes>w1))\<circ>(basic (e_vert\<otimes>w2))\<circ>(y2))))
 \<and> ((snd (count w1)) = (fst (count w2))))"
using  step2_subresult3 exI by auto

have step2_subresult7:
" tanglerel_straighten_rightdowntop ?x ?y"
using tanglerel_straighten_rightdowntop_def step2_subresult6 by auto

have step2_subresult8:"tanglerel ?x ?y" 
using tanglerel_def tanglerel_straighten_def step2_subresult7 by auto

have step2_subresult9: "tanglerel (Abs_diagram ((?x2) \<circ>(basic (e_cup\<otimes>e_vert\<otimes>w4))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1)) 
              (Abs_diagram ((?x2) \<circ>(basic (e_vert\<otimes>w4))\<circ>(basic (e_vert\<otimes>w4))\<circ>z1))"
               using step2_subresult8 by auto 

have step2_equiv1: "tanglerel_equiv (Abs_diagram (x1\<circ>basic y1\<circ>(basic (e_cup\<otimes>e_vert\<otimes>w4))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1)) 
              (Abs_diagram (x1\<circ>basic y1 \<circ>(basic (e_vert\<otimes>w4))\<circ>(basic (e_vert\<otimes>w4))\<circ>z1))"
               using step2_subresult9 compose_leftassociativity r_into_rtranclp 
               tanglerel_equiv_def
                     by metis

have step2: "tanglerel_equiv (Abs_diagram (x1\<circ>basic y1\<circ>(basic (e_cup\<otimes>?z4))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1)) 
              (Abs_diagram (x1\<circ>basic y1 \<circ>(basic ?z4)\<circ>(basic (?z4))\<circ>z1))"
               using  step2_subresult9 compose_leftassociativity r_into_rtranclp 
               tanglerel_equiv_def step2_subresult1 w_subst
                     by (metis)
(*step 3*)

have step3_preliminary1: "fst (count (v\<otimes>w)) = fst (count (cup#(v\<otimes>w)))" using count_def brickcount_def
by auto
have step3_preliminary2 : 
"count ((cup)#(e_cup\<otimes>w4)) = (fst (brickcount (cup)) + fst (count (e_cup\<otimes>w4)),
 snd (brickcount (cup)) + snd (count (e_cup\<otimes>w4)))"
using count_def e_cup_def by auto
have step3_preliminary3: 
"(e_cup\<otimes>(e_vert\<otimes>w4)) = cup#(e_vert\<otimes>w4)" using e_cup_def append_Nil by metis
have step3_subresult0 : 
"fst (count ((cup)#(e_cup\<otimes>w4))) =  (fst (brickcount (cup)) + fst (count (e_cup\<otimes>w4)))"
using count_def e_cup_def brickcount_def by auto
have step3_preliminary4 : 
"(fst (brickcount (cup)) + fst (count (e_cup\<otimes>w4))) = fst (count (e_cup\<otimes>w4))"
using brickcount_def by auto

have step3_preliminary5:
"fst (count (cup#(e_cup\<otimes>w4))) =  fst (count (e_cup\<otimes>w4))"
using  step3_preliminary4 step3_subresult0 by auto

have step3_preliminary6:
"fst (count ((e_cup)\<otimes>(e_cup\<otimes>w4))) =  fst (count (cup#(e_cup\<otimes>w4)))"
using step3_preliminary3 
by (metis Tangles.append.append_Nil e_cup_def)

have step3_preliminary7:
"fst (count ((e_cup)\<otimes>(e_cup\<otimes>w4))) =  fst (count (e_cup\<otimes>w4))"
using step3_preliminary5  step3_preliminary6 
by auto

have step3_subresult1 :"fst (wall_count (basic (e_cup\<otimes>e_vert\<otimes>w4))) = fst (wall_count (basic (e_vert\<otimes>w4))) " 
using wall_count_def step3_preliminary7
 by (metis Tangles.append.append_Nil add_diff_cancel 
comm_monoid_add_class.add.left_neutral count.simps(2) e_cup_def fst_conv wall_count.simps(1))

have step3_subresult2: "fst (wall_count (basic (e_vert\<otimes>w4))) = snd (count y1)" 
               using w_subst step2_subresult1 subresult8 by auto
have step3_subresult3: "fst (wall_count (basic (e_cup\<otimes>e_vert\<otimes>w4))) = snd (count y1)" 
               using step3_subresult1 step3_subresult2 by auto 
have step3_subresult4: "fst (wall_count (basic (e_vert\<otimes>w4))) = snd (wall_count ?x2)" 
               using step3_subresult3 subresult0 wall_count_def step3_subresult2 subresult1 by auto 
have step3_subresult5: "fst (wall_count (basic (e_vert\<otimes>w4))) = snd (wall_count (x1\<circ>(basic y1)))" 
               using step3_subresult4  wall_count_def by auto
have step3_subresult6: "fst (brickcount cup) =  0" using brickcount_def by auto
have step3_subresult7: "fst (count e_cup) =  0" using e_cup_def count_def step3_subresult6 
by (metis count.simps(1))
have step3_subresult8: "strands (vert#e_vert)" using e_vert_def append_def strands_def  brickstrand.simps(1) 
                        strands.simps(1) strands.simps(2) 
                       by metis
have step3_subresult9: "(vert#e_vert) = (e_vert\<otimes>e_vert)" using append_Nil e_vert_def
                        by metis
have step3_subresult10: "strands (e_vert\<otimes>e_vert)" using step3_subresult8 step3_subresult9
                        by auto
let ?a0 = "(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1"
let ?b0 = "(e_vert\<otimes>e_vert)"
let  ?a = "Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (?b0\<otimes>(e_vert\<otimes>w4)))\<circ>((basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))"
(*check b*)
let ?b = "Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic (e_cup \<otimes> (e_vert \<otimes> w4)))\<circ>((basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))"

have step3_subresult11: "  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.(?a = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))\<circ>(y2)))"
using exI by metis

have step3_subresult12: " \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.(
?b =
(Abs_diagram
 ((y1)\<circ>(basic (w1))\<circ>(basic (A\<otimes>w2))\<circ>(y2))))"
using exI 
by metis

have step3_subresult13: "  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((?a = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))\<circ>(y2))) \<and>
 (?b = Abs_diagram
 ((y1)\<circ>(basic (w1))\<circ>(basic (A\<otimes>w2))\<circ>(y2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>((fst (count A)) = 0)
\<and>(strands B))" 
using
step3_subresult11 step3_subresult12
compose_leftassociativity step2_subresult1 subresult8 w_subst
step3_subresult5 step3_subresult7 step3_subresult10 exI assms
leftright_associativity step2_subresult4 step2_subresult6
by (metis)

have step3_subresult14: "tanglerel_compbelow_centerright ?a ?b" using step3_subresult13 
tanglerel_compbelow_centerright_def by auto
have step3_subresult15: "tanglerel_compress ?a ?b" using step3_subresult14 tanglerel_compress_def 
tanglerel_compbelow_def by auto
have step3_subresult16: "tanglerel ?a ?b" using step3_subresult15 tanglerel_def by auto

have step3_subresult17: "tanglerel_equiv ?a ?b"
    using step3_subresult16 tanglerel_equiv_def r_into_rtranclp
       by (metis (full_types) r_into_rtranclp)

have step3_subresult18: "tanglerel_equiv 
(Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic ((e_vert\<otimes>e_vert)\<otimes>(e_vert\<otimes>w4)))\<circ>((basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1)))
(Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic (e_cup \<otimes> (e_vert \<otimes> w4)))\<circ>((basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1)))"
 using step3_subresult17
by metis

have step3: 
"tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>e_vert\<otimes>w4))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))
 (Abs_diagram (((x1)\<circ>(basic y1))\<circ>(basic (e_cup \<otimes> ?z4))\<circ> (basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))" 
using step3_subresult18 leftright_associativity w_subst step2_subresult1 left_associativity
 compose_leftassociativity
by auto

(*step 4*)

let ?p = "(x1)\<circ>(basic (e_cup\<otimes>y1))"
let ?q = "(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1"
let ?r = " basic (e_vert \<otimes> e_vert \<otimes> e_vert \<otimes> w4)"

have step4_subresult1: "strands (e_vert \<otimes> e_vert \<otimes> e_vert \<otimes> w4)"
using assms  Tangles.append.append_Nil e_vert_def preliminary_result3 step2_subresult1 strands.simps(2)
by metis

have step4_subresult2: "snd (count (e_cup\<otimes>y1)) =  snd (count (cup#y1))" 
using Tangles.append.append_Nil count_def e_cup_def by (metis)

have step4_subresult3: " snd (count (cup#y1)) =  2+ snd (count (y1))"
using step4_subresult2 count_def brickcount_def by auto

have step4_subresult4: "snd (count (e_cup\<otimes>y1)) > snd (count (y1))"
using step4_subresult2 step4_subresult3 add_strict_increasing dbl_def 
dbl_simps(3) order_refl zero_less_two
by auto

have step4_subresult5: "snd (count (e_cup\<otimes>y1)) > 1"
using step4_subresult4 assms
by auto

have step4_subresult6: "snd (wall_count ?p) = (snd (count (e_cup\<otimes>y1)))"
using wall_count_def  snd_conv wall_count.simps(1) wall_count_compose
by auto


have step4_subresult7: "snd (wall_count ?p) > 0"
using step4_subresult5 step4_subresult6 assms
by auto


have step4_subresult8: 
"tanglerel_compress_null 
(Abs_diagram (?p\<circ>(basic (e_vert \<otimes> e_vert \<otimes> e_vert \<otimes> w4))\<circ>?q))
 (Abs_diagram (?p\<circ>?q))"
using step4_subresult1 step4_subresult7 tanglerel_compress_null_def
by auto

have step4_subresult9: 
"tanglerel_compress
(Abs_diagram (?p\<circ>(basic (e_vert \<otimes> e_vert \<otimes> e_vert \<otimes> w4))\<circ>?q))
 (Abs_diagram (?p\<circ>?q))"
using step4_subresult8 tanglerel_compress_def
by auto


have step4_subresult10: 
"tanglerel
 (Abs_diagram (?p\<circ>?q))
(Abs_diagram (?p\<circ>(basic (e_vert \<otimes> e_vert \<otimes> e_vert \<otimes> w4))\<circ>?q))
"
using step4_subresult9 step4_subresult8 tanglerel_def
by auto


have step4_subresult11: 
"tanglerel_equiv
 (Abs_diagram (?p\<circ>?q))
(Abs_diagram (?p\<circ>(basic (e_vert \<otimes> e_vert \<otimes> e_vert \<otimes> w4))\<circ>?q))
"
using step4_subresult10 tanglerel_equiv_def compose_leftassociativity 
leftright_associativity r_into_rtranclp step3_subresult11 step3_subresult13
by metis

have step4: 
"tanglerel_equiv
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))
(Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert \<otimes> e_vert \<otimes> e_vert \<otimes> w4))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))
"
using step4_subresult10 tanglerel_equiv_def compose_leftassociativity 
leftright_associativity r_into_rtranclp step3_subresult11 step3_subresult13
by metis

(*combining steps*)
                      
have combine_vert: 
"tanglerel_equiv (Abs_diagram (x1\<circ>basic y1\<circ>(basic (e_cup\<otimes>?z4))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using step1 step2 rtranclp_trans tanglerel_equiv_def by metis

have combine_cup:"tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>?z4))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))
             (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using step3 combine_vert tanglerel_equiv_def rtranclp_trans
                compose_leftassociativity leftright_associativity 
               step2 step2_subresult1 step2_subresult2 step3_subresult17 subresult_equiv3 
               w_subst
               by (metis) 

have combine_compress:"tanglerel_equiv
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))
             (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
using combine_cup step4 
combine_vert tanglerel_equiv_def rtranclp_trans
                compose_leftassociativity leftright_associativity 
               step2 step2_subresult1 step2_subresult2 step3_subresult17 subresult_equiv3 
               w_subst
by metis

from this show ?thesis by auto
qed
(*Theorem ends*)
(*some lemmas used in the next theorem*)

lemma count_rightcompose:" count(v\<otimes>w) = (fst (count v) + fst (count w), snd (count v)+snd (count w))"
apply (induct_tac v)
apply (metis append.append_Nil count.simps(1) count.simps(2))
apply(auto)
done

lemma count_cup_rightcompose:" count(v\<otimes>e_cup) = (fst (count v), snd (count v)+2)"
apply (simp add:count_rightcompose e_cup_def)
done

lemma fstcount_cup_rightcompose:" fst (count(v\<otimes>e_cup)) = fst (count v)"
apply (simp add: count_cup_rightcompose)
done


(*theorem begins*)
theorem metaequivalence_right: 
assumes "(snd (count y1))>1" 
and "w4 = makestrand  (nat ((snd (count y1)) + (-2)))"
shows "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>e_cup))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
             (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
proof-
let ?k = " (nat ((snd (count y1))+ (-2) ))" 
let ?z4 = "makestrand (nat ((snd (count y1)) + (-2))+1)"
have C: " ?z4 = makestrand (?k+1)" using assms by auto
let ?x2 = "x1 \<circ> (basic y1)"
have preliminary_result1:"((snd (count y1))+(-1))>0" using assms by auto
have preliminary_result2:"((snd (count y1))+(-2))\<ge>0" using assms by auto
have preliminary_result3: "strands ?z4" using C strand_makestrand by auto
have subresult0: "snd (wall_count ?x2) = snd (wall_count (basic y1))" 
           using wall_count_compose 
             by auto
have subresult1: "... = snd (count y1)" using wall_count_compose 
            by auto
have subresult2: "snd (wall_count ?x2) > 0"
            using subresult1 assms less_trans subresult0 zero_less_one 
            by auto
have subresult3: "fst (count (?z4)) = fst (count (makestrand (?k+1)))"  
            using C makestrand_fstequality
            by auto
have subresult4: "fst (count (makestrand (?k+1))) = int(?k+1)+1"  
            using makestrand_fstequality
            by auto
have subresult5:"fst (count (?z4)) =  int(?k)+2" 
           using subresult3 subresult4 
           by auto
have subresult6: "int (nat (snd (count y1) + -2)) = (snd (count y1)) + -2" 
           using int_nat_eq preliminary_result2
           by auto
have subresult7: "snd (count y1) = int(?k)+2" 
           using subresult6 
           by auto
have subresult8: "fst (count (?z4)) = (snd (count y1))" 
           using subresult5 subresult7 
           by auto
have subresult_compress1: 
"(tanglerel_compress_null ((Abs_diagram (?x2\<circ>(basic ?z4)\<circ>z1))) (Abs_diagram (?x2\<circ>z1)))" 
           using tanglerel_compress_null_def
           preliminary_result3 subresult0 subresult2
             by metis
have subresult_equiv1: 
"(tanglerel_equiv ((Abs_diagram (?x2\<circ>(basic ?z4)\<circ>z1))) (Abs_diagram (?x2\<circ>z1)))" 
           using r_into_rtranclp subresult_compress1 tanglerel_equiv_def tanglerel_def  
           tanglerel_compress_def
                     by (metis)
have subresult_compress2: 
"(tanglerel_compress_null ((Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>(basic ?z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>z1)))" 
               using tanglerel_compress_null_def preliminary_result3 subresult0 subresult2   
               compose_leftassociativity
                    by (metis)
have subresult_equiv2: 
"(tanglerel_equiv ((Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>(basic ?z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>z1)))" 
               using tanglerel_compress_def tanglerel_def tanglerel_equiv_def
               r_into_rtranclp subresult_compress2   
                    by (metis)
have subresult_equiv3: 
"tanglerel_equiv ((Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>(basic ?z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ>z1)))" 
               using tanglerel_equiv_def rtranclp_trans subresult_equiv1 subresult_equiv2 
               compose_leftassociativity
                            by (metis) 
have step1: 
"tanglerel_equiv (Abs_diagram (x1 \<circ> basic y1 \<circ> basic ?z4\<circ>basic ?z4\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using compose_leftassociativity subresult_equiv3 
               by auto
(*step 2 - inducing cusp*)

have w_subst: "w4 = (makestrand ?k)" using assms by auto

have step2_subresult0: "(makestrand (?k+1)) = ((makestrand ?k) \<otimes>e_vert)" 
 by (metis test_00 test_1)
 
have step2_subresult1:"?z4 = (makestrand ?k)\<otimes>e_vert  " using C step2_subresult0 by auto

have step2_subresult2: "(Abs_diagram (?x2 \<circ> (basic ?z4) \<circ>(basic ?z4)\<circ>z1)) =
(Abs_diagram (?x2  \<circ> (basic (w4\<otimes>e_vert))\<circ> (basic (w4\<otimes>e_vert))\<circ>z1))" 
                        using w_subst step2_subresult1 by auto

have step2_subresult3: "(snd (count w4)) = (fst (count w4))" using makestrand_fstsndequality w_subst
by auto

let ?x = "(Abs_diagram (?x2 \<circ>(basic (w4\<otimes>e_vert\<otimes>e_cup))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"
let ?y = "(Abs_diagram (?x2 \<circ>(basic (w4\<otimes>e_vert))\<circ>(basic (w4\<otimes>e_vert))\<circ>z1))"

have step2_subresult4:
"\<exists>y1.\<exists>y2.\<exists>w1.\<exists>w2.(?x = Abs_diagram (y1 \<circ> (basic (w1\<otimes>e_vert\<otimes>e_cup)) \<circ> (basic (w2\<otimes>e_cap\<otimes>e_vert)) \<circ> y2))"
  using exI by auto
 
have step2_subresult5:
"\<exists>y1.\<exists>y2.\<exists>w1.\<exists>w2.(?y = Abs_diagram (y1 \<circ> (basic (w1\<otimes>e_vert)) \<circ> (basic (w2\<otimes>e_vert)) \<circ> y2))"
 using exI by auto

have step2_subresult6: 
" (\<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.((?x = Abs_diagram ((y1)
\<circ> (basic (w1\<otimes>e_vert\<otimes>e_cup)) \<circ> (basic (w2\<otimes>e_cap\<otimes>e_vert)) \<circ> y2)))
\<and>(?y = Abs_diagram (y1 \<circ> (basic (w1\<otimes>e_vert)) \<circ> (basic (w2\<otimes>e_vert)) \<circ> y2))
 \<and> ((snd (count w1)) = (fst (count w2))))"
using  step2_subresult3 exI by auto

have step2_subresult7:
" tanglerel_straighten_leftdowntop ?x ?y"
using tanglerel_straighten_leftdowntop_def 
compose_leftassociativity step2_subresult2 step2_subresult4 step2_subresult6 subresult8
by (metis)

have step2_subresult8:"tanglerel ?x ?y" 
using tanglerel_def tanglerel_straighten_def step2_subresult7 by auto

have step2_subresult9: "tanglerel (Abs_diagram ((?x2) \<circ>(basic (w4\<otimes>e_vert\<otimes>e_cup))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1)) 
              (Abs_diagram ((?x2) \<circ>(basic (w4\<otimes>e_vert))\<circ>(basic (w4\<otimes>e_vert))\<circ>z1))"
               using step2_subresult8 by auto 

have step2_equiv1: "tanglerel_equiv (Abs_diagram (x1\<circ>basic y1\<circ>(basic (w4\<otimes>e_vert\<otimes>e_cup))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1)) 
              (Abs_diagram (x1\<circ>basic y1 \<circ>(basic (w4\<otimes>e_vert))\<circ>(basic (w4\<otimes>e_vert))\<circ>z1))"
               using step2_subresult9 compose_leftassociativity r_into_rtranclp 
               tanglerel_equiv_def
                     by metis

have step2: "tanglerel_equiv (Abs_diagram (x1\<circ>basic y1\<circ>(basic (?z4\<otimes>e_cup))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1)) 
              (Abs_diagram (x1\<circ>basic y1 \<circ>(basic ?z4)\<circ>(basic (?z4))\<circ>z1))"
               using  step2_subresult9 compose_leftassociativity r_into_rtranclp 
               tanglerel_equiv_def step2_subresult1 w_subst leftright_associativity
                     by (metis )

(*step3 to be modified*)
(*step 3*)
have step3_preliminary1: "fst (count (v\<otimes>w)) = fst (count (cup#(v\<otimes>w)))" using count_def brickcount_def
by auto
have step3_preliminary2 : 
"count ((w4\<otimes>e_vert)\<otimes>e_cup) = ((fst (count (w4\<otimes>e_vert))), (snd (count (w4\<otimes>e_vert))+2))"
using fstcount_cup_rightcompose  count_cup_rightcompose
by (metis) 

have step3_preliminary3 : 
"fst (count ((w4\<otimes>e_vert)\<otimes>e_cup)) = (fst (count (w4\<otimes>e_vert)))"
using step3_preliminary2
by auto

have step3_subresult1 :
"fst (wall_count (basic ((w4\<otimes>e_vert)\<otimes>e_cup))) = fst (wall_count (basic (w4\<otimes>e_vert))) " 
using wall_count_def step3_preliminary3
 by (metis Tangles.append.append_Nil add_diff_cancel 
comm_monoid_add_class.add.left_neutral count.simps(2) e_cup_def fst_conv wall_count.simps(1))

have step3_subresult2: "fst (wall_count (basic (w4\<otimes>e_vert))) = snd (count y1)" 
               using w_subst step2_subresult1 subresult8 by auto
have step3_subresult3: "fst (wall_count (basic ((w4\<otimes>e_vert\<otimes>e_cup)))) = snd (count y1)" 
               using step3_subresult1 step3_subresult2 leftright_associativity
               by (auto)
have step3_subresult4: "fst (wall_count (basic (w4\<otimes>e_vert))) = snd (wall_count ?x2)" 
               using step3_subresult3 subresult0 wall_count_def step3_subresult2 subresult1 by auto 
have step3_subresult5: "fst (wall_count (basic (w4\<otimes>e_vert))) = snd (wall_count (x1\<circ>(basic y1)))" 
               using step3_subresult4  wall_count_def by auto
have step3_subresult6: "fst (brickcount cup) =  0" using brickcount_def by auto
have step3_subresult7: "fst (count e_cup) =  0" using e_cup_def count_def step3_subresult6 
by (metis count.simps(1))
have step3_subresult8: "strands (vert#e_vert)" using e_vert_def append_def strands_def  brickstrand.simps(1) 
                        strands.simps(1) strands.simps(2) 
                       by metis
have step3_subresult9: "(vert#e_vert) = (e_vert\<otimes>e_vert)" using append_Nil e_vert_def
                        by metis
have step3_subresult10: "strands (e_vert\<otimes>e_vert)" using step3_subresult8 step3_subresult9
                        by auto

(*need to edit from here*)

let  ?a = "Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> e_cup))\<circ>(basic (?z4\<otimes>e_vert\<otimes>e_vert))\<circ>((basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"
(*check b*)
let ?b = "Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((w4\<otimes>e_vert) \<otimes> e_cup))\<circ>((basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"

have step3_subresult11: "  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.(?a = Abs_diagram
 ((y1)\<circ>(basic (w1 \<otimes>A))\<circ>(basic (w2\<otimes>B))\<circ>(y2)))"
using exI by metis

have step3_subresult12: " \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.(
?b =
(Abs_diagram
 ((y1)\<circ>(basic (w1))\<circ>(basic (w2\<otimes>A))\<circ>(y2))))"
using exI 
by metis
(*check relations*)


let  ?a = "Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> e_cup))\<circ>(basic (?z4\<otimes>e_vert\<otimes>e_vert))\<circ>((basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"
(*check b*)
let ?b = "Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((w4\<otimes>e_vert) \<otimes> e_cup))\<circ>((basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"

have step3_subresult13: " \<exists>y1.\<exists>z1.\<exists>z2.\<exists>A.\<exists>B.\<exists>y2.((?a = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> (?b = Abs_diagram ((y1)\<circ>
(basic (z1))\<circ>(basic (z2\<otimes>A))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((fst (count A)) = 0)
\<and>(strands B))" 
using
step3_subresult11 step3_subresult12
compose_leftassociativity step2_subresult1 subresult8 w_subst
step3_subresult5 step3_subresult7 step3_subresult10 exI assms
leftright_associativity step2_subresult4 step2_subresult6
by metis

have step3_subresult14: "tanglerel_compbelow_centerleft ?a ?b" using step3_subresult13 
tanglerel_compbelow_centerright_def 
 step2_subresult3 step3_subresult11 step3_subresult7 tanglerel_compbelow_centerleft_def zero_reorient
 by (metis)

have step3_subresult15: "tanglerel_compress ?a ?b" using step3_subresult14 tanglerel_compress_def 
tanglerel_compbelow_def by auto
have step3_subresult16: "tanglerel ?a ?b" using step3_subresult15 tanglerel_def by auto

have step3_subresult17: "tanglerel_equiv ?a ?b"
    using step3_subresult16 tanglerel_equiv_def r_into_rtranclp
       by (metis (full_types) r_into_rtranclp)

have step3_subresult18: "tanglerel_equiv 
(Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> e_cup))\<circ>(basic (?z4\<otimes>e_vert\<otimes>e_vert))\<circ>((basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1)))
(Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((w4\<otimes>e_vert) \<otimes> e_cup))\<circ>((basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1)))"
 using step3_subresult17
by metis

have step3: "tanglerel_equiv 
(Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> e_cup))\<circ>(basic (?z4\<otimes>e_vert\<otimes>e_vert))\<circ>((basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1)))
(Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((?z4) \<otimes> e_cup))\<circ>((basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1)))"
using step3_subresult18 leftright_associativity w_subst step2_subresult1 left_associativity
 compose_leftassociativity
by metis

(*step 4*)

let ?p = "(x1)\<circ>(basic (y1 \<otimes> e_cup))"
let ?q = "(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1"
let ?r = " basic (?z4 \<otimes> e_vert \<otimes> e_vert)"

have step4_subresult1: "strands (?z4 \<otimes> e_vert \<otimes> e_vert)"
using assms  Tangles.append.append_Nil e_vert_def preliminary_result3 step2_subresult1 strands.simps(2)
leftright_associativity test_0
by (metis)

have step4_subresult2: "snd (count (y1\<otimes>e_cup)) =  snd (count (y1)) + 2"
apply (induct_tac y1)
apply (auto)
apply(simp add: e_cup_def count_def brickcount_def)
done

have step4_subresult4: "snd (count (y1 \<otimes> e_cup)) > snd (count (y1))"
using step4_subresult2 add_strict_increasing dbl_def 
dbl_simps(3) order_refl zero_less_two
by auto

have step4_subresult5: "snd (count (y1 \<otimes> e_cup)) > 1"
using step4_subresult4 assms
by auto

have step4_subresult6: "snd (wall_count ?p) = (snd (count (y1\<otimes>e_cup)))"
using wall_count_def  snd_conv wall_count.simps(1) wall_count_compose
by auto


have step4_subresult7: "snd (wall_count ?p) > 0"
using step4_subresult5 step4_subresult6 assms
by auto


have step4_subresult8: 
"tanglerel_compress_null 
(Abs_diagram (?p\<circ>(basic ((?z4) \<otimes> e_vert \<otimes> e_vert))\<circ>?q))
 (Abs_diagram (?p\<circ>?q))"
using step4_subresult1 step4_subresult7 tanglerel_compress_null_def
by metis

have step4_subresult9: 
"tanglerel_compress
(Abs_diagram (?p\<circ>(basic ((?z4) \<otimes> e_vert \<otimes> e_vert))\<circ>?q))
 (Abs_diagram (?p\<circ>?q))"
using step4_subresult8 tanglerel_compress_def
by auto


have step4_subresult10: 
"tanglerel
 (Abs_diagram (?p\<circ>?q))
(Abs_diagram (?p\<circ>(basic (?z4 \<otimes> e_vert \<otimes> e_vert))\<circ>?q))
"
using step4_subresult9 step4_subresult8 tanglerel_def
by auto


have step4_subresult11: 
"tanglerel_equiv
 (Abs_diagram (?p\<circ>?q))
(Abs_diagram (?p\<circ>(basic ((?z4) \<otimes> e_vert \<otimes> e_vert))\<circ>?q))
"
using step4_subresult10 tanglerel_equiv_def compose_leftassociativity 
leftright_associativity r_into_rtranclp step3_subresult11 step3_subresult13
by metis

have step4: 
"tanglerel_equiv
 (Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> e_cup))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
(Abs_diagram ((x1)\<circ>(basic (y1\<otimes>e_cup))\<circ>(basic (?z4\<otimes>e_vert \<otimes> e_vert))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
"
using step4_subresult10 tanglerel_equiv_def compose_leftassociativity 
leftright_associativity r_into_rtranclp step3_subresult11 step3_subresult13
by metis
(*combining steps*)
                   
have combine_vert: 
"tanglerel_equiv (Abs_diagram (x1\<circ>basic y1\<circ>(basic (?z4\<otimes>e_cup))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
                            (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using step1 step2 rtranclp_trans tanglerel_equiv_def by metis
have combine_cup:
"tanglerel_equiv 
(Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> e_cup))\<circ>(basic (?z4\<otimes>e_vert\<otimes>e_vert))\<circ>((basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1)))
   (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using step3 combine_vert tanglerel_equiv_def rtranclp_trans
                compose_leftassociativity leftright_associativity 
               step2 step2_subresult1 step2_subresult2 step3_subresult17 subresult_equiv3 
               w_subst
               by (metis) 

have combine_compress:
"tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> e_cup))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
 (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))"
using  combine_cup step4  rtranclp_trans  combine_vert tanglerel_equiv_def rtranclp_trans
                compose_leftassociativity leftright_associativity 
               step2 step2_subresult1 step2_subresult2 step3_subresult17 subresult_equiv3 
               w_subst
           by (metis (full_types) C nat_add_commute r_into_rtranclp step3_subresult16 step4_subresult10 test_0 test_1 wall_count.simps(1))
from combine_compress show ?thesis by simp
qed


(*theorem begins*)
theorem metaequivalence_bottomright: 
assumes "(fst (count y1))>1"
and "w4 = makestrand  (nat ((fst (count y1)) + (-2)))" and "well_defined (x1 \<circ> basic y1 \<circ>z1)"
shows "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert)\<circ>(basic (y1\<otimes>e_cap))\<circ>z1)))     
(Abs_diagram (x1 \<circ> (basic y1) \<circ>z1))" 
proof-
let ?z4 = "makestrand (nat ((fst (wall_count (basic y1))) + (-2))+1)"
let ?k = " (nat ((fst (count y1))+ (-2) ))" 

have C: " (?z4 = makestrand (?k+1))" using assms by auto

have preliminary_result0: "(fst (wall_count ((basic y1)\<circ>z1))) = (snd (wall_count x1))" 
using assms diagram_fst_equals_snd by metis
have preliminary_result1: " (fst (wall_count ((basic y1)\<circ>z1))) = (fst (count y1))" 
by (metis compose_Nil fst_eqD wall_count.simps(2))
have preliminary_result2: " (snd (wall_count x1)) = (fst (count y1))" using preliminary_result0 
preliminary_result1 by auto
have preliminary_result3:"((fst (count y1))+(-1))>0" using assms by auto
have preliminary_result4:"((fst (count y1))+(-2))\<ge>0" using assms by auto
have preliminary_result5: "strands ?z4" using C strand_makestrand by auto
have preliminary_result6: "(snd (wall_count x1))>1" using assms preliminary_result2 by auto

have subresult3: "snd (count (?z4)) = snd (count (makestrand (?k+1)))"  
            using C makestrand_fstequality
            by auto
have subresult4: "snd (count (makestrand (?k+1))) = int(?k+1)+1"  
            using makestrand_sndequality
            by auto
have subresult5:"snd (count (?z4)) =  int(?k)+2" 
           using subresult3 subresult4 
           by auto
have subresult6: "int (nat (fst (count y1) + -2)) = (fst (count y1)) + -2" 
           using int_nat_eq preliminary_result3 by auto
have subresult7: "fst (count y1) = int(?k)+2" 
           using subresult6 
           by auto
have subresult8: "snd (count (?z4)) = (fst (count y1))" 
           using subresult5 subresult7 
           by auto
have subresult_compress1: 
"(tanglerel_compress_null ((Abs_diagram (x1\<circ>(basic ?z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1)))" 
           using tanglerel_compress_null_def
           preliminary_result5 preliminary_result6 subresult8 
                   by (metis C comm_semiring_1_class.normalizing_semiring_rules(24) 
makestrand_fstequality monoid_add_class.add.left_neutral of_nat_Suc zless_iff_Suc_zadd)
have subresult_equiv1: 
"(tanglerel_equiv  ((Abs_diagram (x1\<circ>(basic ?z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1)))" 
           using r_into_rtranclp subresult_compress1 tanglerel_equiv_def tanglerel_def  
           tanglerel_compress_def
                     by (metis)

have subresult_compress2: 
"(tanglerel_compress_null  ((Abs_diagram (x1\<circ>(basic ?z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1))) " 
               using tanglerel_compress_null_def preliminary_result3   
               compose_leftassociativity subresult_compress1
                   by auto
           
let ?z2 = "((basic ?z4)\<circ>(basic y1)\<circ>z1)"

have subresult_equiv2: 
"(tanglerel_compress_null (Abs_diagram (x1 \<circ> (basic ?z4)\<circ>(?z2)))
                           (Abs_diagram (x1\<circ>(?z2))))"
               using tanglerel_compress_null_def  C
               C comm_semiring_1_class.normalizing_semiring_rules(24) 
               int_one_le_iff_zero_less makestrand_fstequality preliminary_result5 
               subresult8 zle_iff_zadd preliminary_result6  makestrand_fstsndequality 
               preliminary_result2
               by (metis)

have subresult_equiv3: 
"tanglerel_equiv (Abs_diagram (x1 \<circ> (basic ?z4)\<circ>(?z2))) 
                            (Abs_diagram (x1 \<circ> (?z2)))" 
               using tanglerel_equiv_def tanglerel_compress_def subresult_equiv2
                        by (metis (full_types) r_into_rtranclp tanglerel_def)
have subresult_equiv4: 
"tanglerel_equiv (Abs_diagram (x1 \<circ> basic ?z4\<circ>basic ?z4 \<circ> basic y1\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> (basic ?z4)\<circ>(basic y1)\<circ>z1))" 
               using compose_leftassociativity subresult_equiv3
               by auto
have step1: 
"tanglerel_equiv (Abs_diagram (x1 \<circ> basic ?z4\<circ>basic ?z4 \<circ> basic y1\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))" 
               using compose_leftassociativity subresult_equiv3 subresult_equiv1 rtranclp_trans
               by (metis (full_types) Tangle.abs_eq_iff )
(*step 2 - inducing cusp*)
(*need to edit from here*)
have w_subst: "w4 = (makestrand ?k)" using assms by auto

have step2_subresult0: "(makestrand (?k+1)) = ((makestrand ?k) \<otimes>e_vert)" 
 by (metis test_00 test_1)
 
have step2_subresult1:"?z4 = (makestrand ?k)\<otimes>e_vert  " using C step2_subresult0 by auto

have step2_subresult2: "(Abs_diagram (x1 \<circ> (basic ?z4) \<circ>(basic ?z4)\<circ> (basic y1)\<circ>z1)) =
(Abs_diagram (x1  \<circ> (basic (w4\<otimes>e_vert))\<circ> (basic (w4\<otimes>e_vert))\<circ>(basic y1)\<circ> z1))" 
                        using w_subst step2_subresult1 by auto

have step2_subresult3: "(snd (count w4)) = (fst (count w4))" using makestrand_fstsndequality w_subst
by auto
let ?z3 = " (basic y1)\<circ> z1"
let ?x = "(Abs_diagram (x1 \<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (w4\<otimes>e_vert\<otimes>e_cap))\<circ>(?z3)))"
let ?y = "(Abs_diagram (x1 \<circ>(basic (w4\<otimes>e_vert))\<circ>(basic (w4\<otimes>e_vert))\<circ> (?z3)))"

have step2_subresult4:
"\<exists>a.\<exists>b.\<exists>c.\<exists>d.(?x = Abs_diagram (a \<circ> (basic (b\<otimes>e_cup\<otimes>e_vert )) \<circ> (basic (c\<otimes>e_vert\<otimes>e_cap)) \<circ> d))"
  using exI by auto
 
have step2_subresult5:
"\<exists>a.\<exists>b.\<exists>c.\<exists>d.(?y = Abs_diagram (a \<circ> (basic (b\<otimes>e_vert)) \<circ> (basic (c\<otimes>e_vert)) \<circ> d))"
 using exI by auto

have step2_subresult6: 
" (\<exists>a.\<exists>b.\<exists>c.\<exists>d.((?x = Abs_diagram ((a)
\<circ> (basic (b\<otimes>e_cup\<otimes>e_vert)) \<circ> (basic (c\<otimes>e_vert\<otimes>e_cap)) \<circ> d)))
\<and>(?y = Abs_diagram (a \<circ> (basic (b\<otimes>e_vert)) \<circ> (basic (c\<otimes>e_vert)) \<circ> d))
 \<and> ((snd (count b)) = (fst (count c))))"
using  step2_subresult3 step2_subresult4 step2_subresult5 exI 
by auto

have step2_subresult7:
" tanglerel_straighten_lefttopdown ?x ?y"
using tanglerel_straighten_lefttopdown_def 
compose_leftassociativity step2_subresult2 step2_subresult4 step2_subresult6 subresult8
step2_subresult3 step2_subresult5
by auto

have step2_subresult8:"tanglerel ?x ?y" 
using tanglerel_def tanglerel_straighten_def step2_subresult7 by auto

have step2_subresult9: "tanglerel 
              (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (w4\<otimes>e_vert\<otimes>e_cap))\<circ>(?z3))) 
              (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>e_vert))\<circ>(basic (w4\<otimes>e_vert))\<circ>(?z3)))"
               using step2_subresult8 by auto

have step2_subresult10: "tanglerel_equiv 
              (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (w4\<otimes>e_vert\<otimes>e_cap))\<circ>((basic y1)\<circ> z1))) 
              (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>e_vert))\<circ>(basic (w4\<otimes>e_vert))\<circ>((basic y1)\<circ> z1)))"
               using step2_subresult9 compose_leftassociativity r_into_rtranclp 
               tanglerel_equiv_def
                     by metis

have step2_subresult11: "tanglerel_equiv 
              (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (w4\<otimes>e_vert\<otimes>e_cap))\<circ>(basic y1)\<circ> z1)) 
              (Abs_diagram ((x1) \<circ>(basic (?z4))\<circ>(basic (?z4))\<circ>((basic y1)\<circ> z1)))"
               using step2_subresult10 step2_subresult1 w_subst
                     by (auto)

have step2: "tanglerel_equiv 
              (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (?z4\<otimes>e_cap))\<circ>(basic y1)\<circ> z1)) 
              (Abs_diagram ((x1) \<circ>(basic (?z4))\<circ>(basic (?z4))\<circ>((basic y1)\<circ> z1)))"
               using step2_subresult11 step2_subresult1 
                   Tangle.abs_eq_iff compose_Nil leftright_associativity 
                   step1 step2_subresult4 step2_subresult6 subresult8 w_subst
                   by (metis)
(*step 3*)

have step3_subresult1 :
"snd (count  ?z4) = fst (count y1) " 
using assms preliminary_result6 subresult8
by auto
have step3_subresult2: "snd (count e_cap) = 0" using e_cup_def count_def brickcount_def 
 brickcount.simps(3) count.simps(1) e_cap_def snd_conv
by (metis)

have step3_subresult3: "strands (vert#e_vert)" using e_vert_def append_def strands_def  brickstrand.simps(1) 
                        strands.simps(1) strands.simps(2) 
                       by metis
have step3_subresult4: "(vert#e_vert) = (e_vert\<otimes>e_vert)" using append_Nil e_vert_def
                        by metis
have step3_subresult5: "strands (e_vert\<otimes>e_vert)" using step3_subresult3 step3_subresult4
                        by auto

let  ?a = 
"Abs_diagram (((x1) \<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert)))\<circ>(basic (?z4\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (y1\<otimes>e_cap))\<circ> z1) "

let ?b = " (Abs_diagram (((x1) \<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert)))\<circ>(basic (?z4\<otimes>e_cap))\<circ>(basic y1)\<circ> z1)) "
 
have step3_subresult6: " \<exists>a1.\<exists>b1.\<exists>b2.\<exists>A.\<exists>B.\<exists>a2.(?a = Abs_diagram
 ((a1)\<circ>(basic (b1\<otimes>A))\<circ>(basic (b2\<otimes>B))\<circ>(a2)))"
using exI by metis

have step3_subresult7: " \<exists>a1.\<exists>b1.\<exists>b2.\<exists>a2.\<exists>B.(
?b  = (Abs_diagram ((a1)\<circ>(basic (b1\<otimes>B))\<circ>(basic (b2))\<circ>(a2))))"
using exI 
by metis
(*check relations*)

have step3_subresult8: " \<exists>a1.\<exists>b1.\<exists>b2.\<exists>A.\<exists>B.\<exists>a2.((?a = Abs_diagram
 ((a1)\<circ>(basic (b1\<otimes>A))\<circ>(basic (b2\<otimes>B))\<circ>(a2)))\<and> 
(
?b  = (Abs_diagram ((a1)\<circ>(basic (b1\<otimes>B))\<circ>(basic (b2))\<circ>(a2))))
\<and>((snd (count b1)) = (fst (count b2)))
\<and>((snd (count B)) = 0)
\<and>(strands A))" 
using

compose_leftassociativity step2_subresult1 subresult8 w_subst
step3_subresult5 step3_subresult7  exI assms
leftright_associativity step2_subresult4 step2_subresult6
step3_subresult6 step3_subresult7
 step3_subresult1  step3_subresult2  step3_subresult5 exI assms
leftright_associativity compose_leftassociativity
by metis

have step3_subresult9: "tanglerel_compabove_centerleft ?a ?b" using step3_subresult8
tanglerel_compabove_centerleft_def 
 step2_subresult3 step3_subresult6 step3_subresult7  zero_reorient
 by (metis)

have step3_subresult10: "tanglerel_compabove ?a ?b" using step3_subresult9 
tanglerel_compabove_def by auto

have step3_subresult11: "tanglerel_compress ?a ?b" using step3_subresult10 
tanglerel_compress_def by auto
have step3_subresult12: "tanglerel ?a ?b" using step3_subresult11 tanglerel_def by auto

have step3_subresult13: "tanglerel_equiv ?a ?b"
    using step3_subresult12 tanglerel_equiv_def r_into_rtranclp
       by (metis (full_types) r_into_rtranclp)

have step3: "tanglerel_equiv
(Abs_diagram (((x1) \<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert)))\<circ>(basic (?z4\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (y1\<otimes>e_cap))\<circ> z1))
(Abs_diagram (((x1) \<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert)))\<circ>(basic (?z4\<otimes>e_cap))\<circ>(basic y1)\<circ> z1)) "
 using step3_subresult13 by auto

(*step 4*)

let ?p = "(x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))"
let ?q = "(basic (y1 \<otimes> e_cap))\<circ>z1"
let ?r = " basic (?z4 \<otimes> e_vert \<otimes> e_vert)"

have step4_subresult1: "strands (?z4 \<otimes> e_vert \<otimes> e_vert)"
using assms  Tangles.append.append_Nil e_vert_def preliminary_result3 step2_subresult1 strands.simps(2)
leftright_associativity test_0 strand_makestrand wall_count.simps(1)
by (metis )

have step4_subresult2: "fst (count (y1\<otimes>e_cap)) =  fst (count (y1)) + 2"
apply (induct_tac y1)
apply (auto)
apply(simp add: e_cap_def)
done

have step4_subresult4: "fst (count (y1 \<otimes> e_cap)) = fst (count (y1))+2"
using step4_subresult2 add_strict_increasing dbl_def 
dbl_simps(3) order_refl zero_less_two
by auto

have step4_subresult5: "fst (count (y1 \<otimes> e_cap)) > 1"
using step4_subresult4 assms
by auto

have step4_subresult6: "snd (wall_count ?p) = snd (count (w4\<otimes>e_cup\<otimes>e_vert))"
using wall_count_def  snd_conv wall_count.simps(1) wall_count_compose
by auto

have step4_subresult7: "snd (count (x\<otimes>e_vert)) >0 "
using snd_count_positive e_vert_def brickcount_def count_def 
makestrand.simps(1) makestrand_fstsndequality makestrands_positivelength
by (metis add_nonneg_eq_0_iff less_le snd_count_additive snd_count_nonnegative)


have step4_subresult8: "snd (count ((w4\<otimes>e_cup)\<otimes>e_vert)) > 0"
using step4_subresult7
by (metis add_nonneg_eq_0_iff brick.distinct(1) brickcount_zero_implies_cup count.simps(1) 
e_vert_def le_neq_trans makestrand.simps(1) makestrand_fstsndequality snd_count_additive snd_count_nonnegative)


have step4_subresult9: "snd (wall_count ?p) > 0"
using step4_subresult6 step4_subresult8
by (metis leftright_associativity)

have step4_subresult10: 
"tanglerel_compress_null 
(Abs_diagram (?p\<circ>?r\<circ>?q))
 (Abs_diagram (?p\<circ>?q))"
using step4_subresult1 step4_subresult7 tanglerel_compress_null_def leftright_associativity step4_subresult6 step4_subresult8
by (metis)

have step4_subresult11: 
"tanglerel_compress
 (Abs_diagram (?p\<circ>?r\<circ>?q))
(Abs_diagram (?p\<circ>?q))"
using step4_subresult10 tanglerel_compress_def
by auto


have step4_subresult12: 
"tanglerel
 (Abs_diagram (?p\<circ>?q))
(Abs_diagram (?p\<circ>?r\<circ>?q))"
using step4_subresult11 step4_subresult10 tanglerel_def
by auto

have step4_subresult13:
"tanglerel
(Abs_diagram ((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (?z4 \<otimes> e_vert \<otimes> e_vert))\<circ>(basic (y1 \<otimes> e_cap))\<circ>z1))
 (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (y1 \<otimes> e_cap))\<circ>z1))"
using step4_subresult12 
by (metis compose_leftassociativity tanglerel_def)

have step4: 
"tanglerel_equiv
(Abs_diagram ((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (?z4 \<otimes> e_vert \<otimes> e_vert))\<circ>(basic (y1 \<otimes> e_cap))\<circ>z1))
 (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (y1 \<otimes> e_cap))\<circ>z1))"
using step4_subresult10 tanglerel_equiv_def compose_leftassociativity 
leftright_associativity r_into_rtranclp step3_subresult11 step4_subresult12 step4_subresult13
by (metis (full_types))

(*combining steps*)
                      
have combine_vert: 
"tanglerel_equiv    (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (?z4\<otimes>e_cap))\<circ>(basic y1)\<circ> z1)) 
                   (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using step1 step2 rtranclp_trans tanglerel_equiv_def by metis

have combine_cup:
"tanglerel_equiv 
   (Abs_diagram (((x1) \<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert)))\<circ>(basic (?z4\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (y1\<otimes>e_cap))\<circ> z1))
   (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using step3 combine_vert tanglerel_equiv_def rtranclp_trans
                compose_leftassociativity leftright_associativity 
               step2 step2_subresult1 step2_subresult2  subresult_equiv3 
               w_subst
               by (metis) 
have combine_compress:
"tanglerel_equiv
(Abs_diagram ((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (y1 \<otimes> e_cap))\<circ>z1))
 (Abs_diagram ((x1)\<circ>(basic y1)\<circ>z1))"
using combine_cup step4 rtranclp_trans  combine_cup step4  rtranclp_trans  combine_vert tanglerel_equiv_def 
                compose_leftassociativity leftright_associativity 
               step2 step2_subresult1 step2_subresult2  subresult_equiv3 
               w_subst
by (metis converse_rtranclp_into_rtranclp step4_subresult12)
from combine_compress show ?thesis by (simp add: compose_leftassociativity)
qed

(*theorem begins*)
theorem metaequivalence_bottomleft: 
assumes "(fst (count y1))>1"
and "w4 = makestrand  (nat ((fst (count y1)) + (-2)))" and "well_defined (x1 \<circ> basic y1 \<circ>z1)"
shows "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4)\<circ>(basic (e_cap\<otimes>y1))\<circ>z1)))    
 (Abs_diagram (x1 \<circ> (basic y1) \<circ>z1))" 
proof-
let ?z4 ="makestrand (nat ((fst (wall_count (basic y1))) + (-2))+1)"
let ?k = " (nat ((fst (count y1))+ (-2) ))" 
have C: " (?z4 = makestrand (?k+1))" using assms by auto
have preliminary_result0: "(fst (wall_count ((basic y1)\<circ>z1))) = (snd (wall_count x1))" 
using assms diagram_fst_equals_snd by metis
have preliminary_result1: " (fst (wall_count ((basic y1)\<circ>z1))) = (fst (count y1))" 
by (metis compose_Nil fst_eqD wall_count.simps(2))
have preliminary_result2: " (snd (wall_count x1)) = (fst (count y1))" using preliminary_result0 
preliminary_result1 by auto
have preliminary_result3:"((fst (count y1))+(-1))>0" using assms by auto
have preliminary_result4:"((fst (count y1))+(-2))\<ge>0" using assms by auto
have preliminary_result5: "strands ?z4" using C strand_makestrand by auto
have preliminary_result6: "(snd (wall_count x1))>1" using assms preliminary_result2 by auto

have subresult3: "snd (count (?z4)) = snd (count (makestrand (?k+1)))"  
            using C makestrand_fstequality
            by auto
have subresult4: "snd (count (makestrand (?k+1))) = int(?k+1)+1"  
            using makestrand_sndequality
            by auto
have subresult5:"snd (count (?z4)) =  int(?k)+2" 
           using subresult3 subresult4 
           by auto
have subresult6: "int (nat (fst (count y1) + -2)) = (fst (count y1)) + -2" 
           using int_nat_eq preliminary_result3 by auto
have subresult7: "fst (count y1) = int(?k)+2" 
           using subresult6 
           by auto
have subresult8: "snd (count (?z4)) = (fst (count y1))" 
           using subresult5 subresult7 
           by auto
have subresult_compress1: 
"(tanglerel_compress_null ((Abs_diagram (x1\<circ>(basic ?z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1)))" 
           using tanglerel_compress_null_def
           preliminary_result5 preliminary_result6 subresult8 
                   by (metis C comm_semiring_1_class.normalizing_semiring_rules(24) 
makestrand_fstequality monoid_add_class.add.left_neutral of_nat_Suc zless_iff_Suc_zadd)
have subresult_equiv1: 
"(tanglerel_equiv  ((Abs_diagram (x1\<circ>(basic ?z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1)))" 
           using r_into_rtranclp subresult_compress1 tanglerel_equiv_def tanglerel_def  
           tanglerel_compress_def
                     by (metis)

have subresult_compress2: 
"(tanglerel_compress_null  ((Abs_diagram (x1\<circ>(basic ?z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1))) " 
               using tanglerel_compress_null_def preliminary_result3   
               compose_leftassociativity subresult_compress1
                   by auto
           
let ?z2 = "((basic ?z4)\<circ>(basic y1)\<circ>z1)"

have subresult_equiv2: 
"(tanglerel_compress_null (Abs_diagram (x1 \<circ> (basic ?z4)\<circ>(?z2)))
                           (Abs_diagram (x1\<circ>(?z2))))"
               using tanglerel_compress_null_def  C
               C comm_semiring_1_class.normalizing_semiring_rules(24) 
               int_one_le_iff_zero_less makestrand_fstequality preliminary_result5 
               subresult8 zle_iff_zadd preliminary_result6  makestrand_fstsndequality 
               preliminary_result2
               by (metis)

have subresult_equiv3: 
"tanglerel_equiv (Abs_diagram (x1 \<circ> (basic ?z4)\<circ>(?z2))) 
                            (Abs_diagram (x1 \<circ> (?z2)))" 
               using tanglerel_equiv_def tanglerel_compress_def subresult_equiv2
                        by (metis (full_types) r_into_rtranclp tanglerel_def)
have subresult_equiv4: 
"tanglerel_equiv (Abs_diagram (x1 \<circ> basic ?z4\<circ>basic ?z4 \<circ> basic y1\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> (basic ?z4)\<circ>(basic y1)\<circ>z1))" 
               using compose_leftassociativity subresult_equiv3
               by auto
have step1: 
"tanglerel_equiv (Abs_diagram (x1 \<circ> basic ?z4\<circ>basic ?z4 \<circ> basic y1\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))" 
               using compose_leftassociativity subresult_equiv3 subresult_equiv1 rtranclp_trans
               by (metis (full_types) Tangle.abs_eq_iff )
(*step 2 - inducing cusp*)
(*need to edit from here*)
have w_subst: "w4 = (makestrand ?k)" using assms by auto

have step2_subresult0: "(makestrand (?k+1)) = (e_vert\<otimes>(makestrand ?k))" 
 by (metis test_0)
 
have step2_subresult1:"?z4 = e_vert \<otimes>(makestrand ?k)  " using C step2_subresult0 by auto
                            
have step2_subresult2: "(Abs_diagram (x1 \<circ> (basic ?z4) \<circ>(basic ?z4)\<circ> (basic y1)\<circ>z1)) =
(Abs_diagram (x1  \<circ> (basic (e_vert \<otimes>w4))\<circ> (basic (e_vert \<otimes>w4))\<circ>(basic y1)\<circ> z1))" 
                        using w_subst step2_subresult1 by auto

have step2_subresult3: "(snd (count w4)) = (fst (count w4))" using makestrand_fstsndequality w_subst
by auto
let ?z3 = " (basic y1)\<circ> z1"
let ?x = "(Abs_diagram (x1 \<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4))\<circ>(basic (e_cap\<otimes>e_vert\<otimes>w4))\<circ>(?z3)))"
let ?y = "(Abs_diagram (x1 \<circ>(basic (e_vert\<otimes>w4))\<circ>(basic (e_vert\<otimes>w4))\<circ> (?z3)))"

have step2_subresult4:
"\<exists>a.\<exists>b.\<exists>c.\<exists>d.(?x = Abs_diagram (a \<circ> (basic (e_vert\<otimes>e_cup\<otimes>b )) \<circ> (basic (e_cap\<otimes>e_vert\<otimes>c)) \<circ> d))"
  using exI by auto
 
have step2_subresult5:
"\<exists>a.\<exists>b.\<exists>c.\<exists>d.(?y = Abs_diagram (a \<circ> (basic (e_vert\<otimes>b)) \<circ> (basic (e_vert\<otimes>c)) \<circ> d))"
 using exI by auto

have step2_subresult6: 
" (\<exists>a.\<exists>b.\<exists>c.\<exists>d.((?x = Abs_diagram ((a)
\<circ> (basic (e_vert\<otimes>e_cup\<otimes>b)) \<circ> (basic (e_cap\<otimes>e_vert\<otimes>c)) \<circ> d)))
\<and>(?y = Abs_diagram (a \<circ> (basic (e_vert\<otimes>b)) \<circ> (basic (e_vert\<otimes>c)) \<circ> d))
 \<and> ((snd (count b)) = (fst (count c))))"
using  step2_subresult3 step2_subresult4 step2_subresult5 exI 
by auto

have step2_subresult7:
" tanglerel_straighten_righttopdown ?x ?y"
using tanglerel_straighten_righttopdown_def 
compose_leftassociativity step2_subresult2 step2_subresult4 step2_subresult6 subresult8
step2_subresult3 step2_subresult5
by auto

have step2_subresult8:"tanglerel ?x ?y" 
using tanglerel_def tanglerel_straighten_def step2_subresult7 by auto

have step2_subresult9: "tanglerel 
              (Abs_diagram ((x1) \<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4))\<circ>(basic (e_cap\<otimes>e_vert\<otimes> w4))\<circ>(?z3))) 
              (Abs_diagram ((x1) \<circ>(basic (e_vert\<otimes>w4))\<circ>(basic (e_vert \<otimes>w4))\<circ>(?z3)))"
               using step2_subresult8 by auto

have step2_subresult10: "tanglerel_equiv 
              (Abs_diagram ((x1) \<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4))\<circ>(basic (e_cap\<otimes>e_vert\<otimes>w4))\<circ>((basic y1)\<circ> z1))) 
              (Abs_diagram ((x1) \<circ>(basic (e_vert\<otimes>w4))\<circ>(basic (e_vert\<otimes>w4))\<circ>((basic y1)\<circ> z1)))"
               using step2_subresult9 compose_leftassociativity r_into_rtranclp 
               tanglerel_equiv_def
                     by metis

have step2_subresult11: "tanglerel_equiv 
       (Abs_diagram ((x1) \<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4))\<circ>(basic (e_cap\<otimes>e_vert\<otimes>w4))\<circ>((basic y1)\<circ> z1)))     
              (Abs_diagram ((x1) \<circ>(basic (?z4))\<circ>(basic (?z4))\<circ>((basic y1)\<circ> z1)))"
               using step2_subresult10 step2_subresult1 w_subst
                     by (auto)

have step2: "tanglerel_equiv 
       (Abs_diagram ((x1) \<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4))\<circ>(basic (e_cap\<otimes>?z4))\<circ>((basic y1)\<circ> z1)))      
         (Abs_diagram ((x1) \<circ>(basic (?z4))\<circ>(basic (?z4))\<circ>((basic y1)\<circ> z1)))"
               using step2_subresult11 step2_subresult1 
                   Tangle.abs_eq_iff compose_Nil leftright_associativity 
                   step1 step2_subresult4 step2_subresult6 subresult8 w_subst
                   by (metis)
(*step 3*)

have step3_subresult1 :
"snd (count  ?z4) = fst (count y1) " 
using assms preliminary_result6 subresult8
by auto
have step3_subresult2: "snd (count e_cap) = 0" using e_cup_def count_def brickcount_def 
 brickcount.simps(3) count.simps(1) e_cap_def snd_conv
by (metis)

have step3_subresult3: "strands (vert#e_vert)" using e_vert_def append_def strands_def  brickstrand.simps(1) 
                        strands.simps(1) strands.simps(2) 
                       by metis
have step3_subresult4: "(vert#e_vert) = (e_vert\<otimes>e_vert)" using append_Nil e_vert_def
                        by metis
have step3_subresult5: "strands (e_vert\<otimes>e_vert)" using step3_subresult3 step3_subresult4
                        by auto

let  ?a = 
"Abs_diagram (((x1) \<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4)))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>?z4))\<circ>(basic (e_cap\<otimes>y1))\<circ> z1) "
let ?b = " (Abs_diagram (((x1) \<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4)))\<circ>(basic (e_cap\<otimes>?z4))\<circ>(basic y1)\<circ> z1)) "
 
have step3_subresult6: " \<exists>a1.\<exists>b1.\<exists>b2.\<exists>A.\<exists>B.\<exists>a2.(?a = Abs_diagram
 ((a1)\<circ>(basic (A \<otimes> b1))\<circ>(basic (B \<otimes> b2))\<circ>(a2)))"
using exI by metis

have step3_subresult7: " \<exists>a1.\<exists>b1.\<exists>b2.\<exists>a2.\<exists>B.(
?b  = (Abs_diagram ((a1)\<circ>(basic (B\<otimes>b1))\<circ>(basic (b2))\<circ>(a2))))"
using exI 
by metis
(*check relations*)

have step3_subresult8: " \<exists>a1.\<exists>b1.\<exists>b2.\<exists>A.\<exists>B.\<exists>a2.((?a = Abs_diagram
 ((a1)\<circ>(basic (A \<otimes>b1 ))\<circ>(basic (B \<otimes> b2))\<circ>(a2)))\<and> 
(
?b  = (Abs_diagram ((a1)\<circ>(basic (B\<otimes>b1))\<circ>(basic (b2))\<circ>(a2))))
\<and>((snd (count b1)) = (fst (count b2)))
\<and>((snd (count B)) = 0)
\<and>(strands A))" 
using

compose_leftassociativity step2_subresult1 subresult8 w_subst
step3_subresult5 step3_subresult7  exI assms
leftright_associativity step2_subresult4 step2_subresult6
step3_subresult6 step3_subresult7
 step3_subresult1  step3_subresult2  step3_subresult5 exI assms
leftright_associativity compose_leftassociativity
by metis

have step3_subresult9: "tanglerel_compabove_centerright ?a ?b" using step3_subresult8
tanglerel_compabove_centerright_def 
 step2_subresult3 step3_subresult6 step3_subresult7  zero_reorient
 by metis

have step3_subresult10: "tanglerel_compabove ?a ?b" using step3_subresult9 
tanglerel_compabove_def by auto

have step3_subresult11: "tanglerel_compress ?a ?b" using step3_subresult10 
tanglerel_compress_def by auto
have step3_subresult12: "tanglerel ?a ?b" using step3_subresult11 tanglerel_def by auto

have step3_subresult13: "tanglerel_equiv ?a ?b"
    using step3_subresult12 tanglerel_equiv_def r_into_rtranclp
       by (metis (full_types) r_into_rtranclp)

have step3: "tanglerel_equiv
(Abs_diagram (((x1) \<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4)))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>?z4))\<circ>(basic (e_cap\<otimes>y1))\<circ> z1))
(Abs_diagram (((x1) \<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4)))\<circ>(basic (e_cap \<otimes>?z4))\<circ>(basic y1)\<circ> z1)) "
 using step3_subresult13 by auto
 
(*"tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4)\<circ>(basic (e_vert\<otimes>e_vert\<otimes>?z4))\<circ>
(basic (e_cap\<otimes>y1))\<circ>z1)))     (Abs_diagram (x1 \<circ> (basic y1) \<circ>z1))*)

(*step 4*)

let ?p = "(x1)\<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4))"
let ?q = "(basic (e_cap \<otimes> y1))\<circ>z1"
let ?r = " basic (e_vert \<otimes> e_vert\<otimes>?z4)"

have step4_subresult1: "strands (e_vert \<otimes> e_vert\<otimes>?z4)"
using assms  Tangles.append.append_Nil e_vert_def preliminary_result3 step2_subresult1 strands.simps(2)
leftright_associativity test_0 strand_makestrand wall_count.simps(1)
by (metis )

have step4_subresult2: "fst (count (e_cap\<otimes>y1)) =  (fst (count e_cap)) + fst (count (y1)) "
using fst_count_additive by auto

have step4_subresult3: "fst (count (e_cap)) =  2"
using e_cap_def count_def brickcount_def 
by (metis brickcount.simps(3) count.simps(1) fst_conv)

have step4_subresult4: "fst (count (e_cap\<otimes>y1)) = fst (count (y1))+2"
using step4_subresult2 step4_subresult3 add_strict_increasing dbl_def 
dbl_simps(3) order_refl zero_less_two
by auto

have step4_subresult5: "fst (count (e_cap\<otimes>y1)) > 1"
using step4_subresult4 assms
by auto

have step4_subresult6: "snd (wall_count ?p) = snd (count (e_vert\<otimes>e_cup\<otimes>w4))"
using wall_count_def  snd_conv wall_count.simps(1) wall_count_compose
by auto

have step4_subresult7: "snd (count (e_vert\<otimes>x)) >0 "
using snd_count_positive e_vert_def brickcount_def count_def 
makestrand.simps(1) makestrand_fstsndequality makestrands_positivelength
by (metis add_nonneg_eq_0_iff antisym_conv1 snd_count_additive snd_count_nonnegative)


have step4_subresult8: "snd (count (e_vert\<otimes>(e_cap\<otimes>w4))) > 0"
using step4_subresult7
by (metis add_nonneg_eq_0_iff brickcount.simps(1) count.simps(1) e_vert_def le_neq_trans snd_conv
 snd_count_additive snd_count_nonnegative zero_neq_one)

have step4_subresult9: "snd (wall_count ?p) > 0"
using step4_subresult6 step4_subresult8
by (metis One_nat_def add_0_iff le_neq_trans makestrand.simps(1) makestrand_sndequality 
of_nat_1 of_nat_Suc snd_count_additive snd_count_nonnegative snd_count_positive zero_neq_one)


have step4_subresult10: 
"tanglerel_compress_null 
(Abs_diagram (?p\<circ>?r\<circ>?q))
 (Abs_diagram (?p\<circ>?q))"
using step4_subresult1 step4_subresult7 tanglerel_compress_null_def leftright_associativity step4_subresult6 step4_subresult8 
step4_subresult9
by (metis)

have step4_subresult11: 
"tanglerel_compress
 (Abs_diagram (?p\<circ>?r\<circ>?q))
(Abs_diagram (?p\<circ>?q))"
using step4_subresult10 tanglerel_compress_def
by auto


have step4_subresult12: 
"tanglerel
 (Abs_diagram (?p\<circ>?q))
(Abs_diagram (?p\<circ>?r\<circ>?q))"
using step4_subresult11 step4_subresult10 tanglerel_def
by auto


have step4_subresult13:
"tanglerel
(Abs_diagram ((x1)\<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>?z4))\<circ>(basic (e_cap \<otimes> y1))\<circ>z1))
 (Abs_diagram ((x1)\<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4))\<circ>(basic (e_cap \<otimes> y1))\<circ>z1))"
using step4_subresult12  compose_leftassociativity tanglerel_def
by metis

have step4: 
"tanglerel_equiv
(Abs_diagram ((x1)\<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4))\<circ>(basic (e_cap \<otimes> y1))\<circ>z1))
(Abs_diagram ((x1)\<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>?z4))\<circ>(basic (e_cap \<otimes> y1))\<circ>z1))
 "
using step4_subresult10 tanglerel_equiv_def compose_leftassociativity 
leftright_associativity r_into_rtranclp step3_subresult11 step4_subresult12 step4_subresult13
by (metis (full_types))

(*combining steps*)
                      
have combine_vert: 
"tanglerel_equiv  (Abs_diagram (((x1) \<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4)))\<circ>(basic (e_cap \<otimes>?z4))\<circ>(basic y1)\<circ> z1))
                  (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using step1 step2 rtranclp_trans tanglerel_equiv_def Tangle.abs_eq_iff compose_Nil 
               compose_leftassociativity step3_subresult7 step3_subresult8
               by (metis)

have combine_cup:
"tanglerel_equiv 
 (Abs_diagram (((x1) \<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4)))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>?z4))\<circ>(basic (e_cap\<otimes>y1))\<circ> z1))
  (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using step3 combine_vert tanglerel_equiv_def rtranclp_trans
                compose_leftassociativity leftright_associativity 
               step2 step2_subresult1 step2_subresult2  subresult_equiv3 
               w_subst
               by (metis) 
have combine_compress:
"tanglerel_equiv 
(Abs_diagram ((x1)\<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4))\<circ>(basic (e_cap \<otimes> y1))\<circ>z1))
  (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))"
using combine_cup step4 rtranclp_trans  combine_cup step4  rtranclp_trans  combine_vert tanglerel_equiv_def 
                compose_leftassociativity leftright_associativity 
               step2 step2_subresult1 step2_subresult2  subresult_equiv3 
               w_subst
by metis 

from combine_compress show ?thesis by (simp)
qed


theorem metaequivalence_left_drop: 
assumes "(snd (count y2))>1" and "(z4 = makestrand (nat ((snd (count y2)) + (-2))+1))"
and "w4 = makestrand  (nat ((snd (count y2)) + (-2)))" and "fst (count y2) = snd (count y1)"
shows "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1) \<circ>(basic (e_cup\<otimes>y2))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))"
proof- 
have "fst (brickcount cup) = 0" using brickcount_def by auto
from this have subresult2:"fst (count (e_cup)) = 0" using count_def e_cup_def count.simps(1) 
by (metis)
have subresult3: " strands (e_vert\<otimes>e_vert)" using e_vert_def append_Nil strands_def 
by (metis brickstrand.simps(1) strands.simps(1) strands.simps(2))
let ?a = "(Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2))
\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))"
let ?b = "(Abs_diagram ((x1 \<circ> (basic y1)) \<circ>(basic (e_cup\<otimes>y2))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))"
 have subresult4: "  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((?a = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))\<circ>(y2))) \<and>
 (?b = Abs_diagram
 ((y1)\<circ>(basic (w1))\<circ>(basic (A\<otimes>w2))\<circ>(y2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>((fst (count A)) = 0)
\<and>(strands B))" 
using assms subresult2 subresult3 by (metis compose_leftassociativity leftright_associativity) 
from this have "tanglerel_compbelow_centerright ?a ?b" using tanglerel_compbelow_centerright_def
by auto
from this have "tanglerel_compbelow ?a ?b" using tanglerel_compbelow_def by auto
from this have "tanglerel_compress ?a ?b" using tanglerel_compress_def by auto
then have " tanglerel ?a ?b" using tanglerel_def by auto
then have "tanglerel_equiv ?a ?b" using tanglerel_equiv_def  r_into_rtranclp by (metis)
then have subresult5: "tanglerel_equiv  
(Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))
(Abs_diagram ((x1 \<circ> (basic y1)) \<circ>(basic (e_cup\<otimes>y2))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))"
by auto
then show ?thesis by (simp add: compose_leftassociativity) 
qed

theorem metaequivalence_left_doubledrop: 
assumes "(snd (count y2))>1"
and "w4 = makestrand  (nat ((snd (count y2)) + (-2)))" and "fst (count y2) = snd (count y1)"
shows "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2))
            \<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))
             (Abs_diagram (x1 \<circ> basic y1\<circ> basic y2\<circ>z1))" 
proof-
let ?x = "x1 \<circ> (basic y1)"
have subresult1: "tanglerel_equiv 
   (Abs_diagram ((x1 \<circ> (basic y1)) \<circ>(basic (e_cup\<otimes>y2))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))
           (Abs_diagram ((x1 \<circ> (basic y1)) \<circ> basic y2 \<circ>z1))"  using assms metaequivalence_left 
             by auto
have subresult2: "tanglerel_equiv 
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))
(Abs_diagram (x1 \<circ> (basic y1) \<circ>(basic (e_cup\<otimes>y2))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))"
         using assms metaequivalence_left_drop compose_leftassociativity 
         by auto

then have "tanglerel_equiv 
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))
           (Abs_diagram (x1 \<circ> (basic y1) \<circ> basic y2 \<circ>z1))"  using subresult1  rtranclp_trans
           Tangle.abs_eq_iff compose_leftassociativity assms
           by metis

from this show  ?thesis by simp
qed
lemma metaequivalence_left_doubledrop_condition:"(
((snd (count y2))>1) 
\<and>(w4 = makestrand  (nat ((snd (count y2)) + (-2))))
\<and>(fst (count y2) = snd (count y1)))
\<Longrightarrow>
(tanglerel_equiv 
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))
           (Abs_diagram (x1 \<circ> (basic y1) \<circ> basic y2 \<circ>z1)))"
using metaequivalence_left_doubledrop by auto

theorem metaequivalence_right_drop: 

assumes "(snd (count y2))>1" 
and "w4 = makestrand  (nat ((snd (count y2)) + (-2)))" and "fst (count y2) = snd (count y1)"
shows "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>e_cup))\<circ>(basic (y2\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1) \<circ>(basic (y2\<otimes>e_cup))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"
proof-
have "fst (brickcount cup) = 0" using brickcount_def by auto
from this have subresult2:"fst (count (e_cup)) = 0" using count_def e_cup_def count.simps(1) 
by (metis)

have subresult3: " strands (e_vert\<otimes>e_vert)" using e_vert_def append_Nil strands_def 
by (metis brickstrand.simps(1) strands.simps(1) strands.simps(2))

let ?a = " (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>e_cup))\<circ>(basic (y2\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"

let ?b = "(Abs_diagram (x1 \<circ> (basic y1) \<circ>(basic (y2\<otimes>e_cup))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"
 

have subresult4: "  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((?a = Abs_diagram
 ((y1)\<circ>(basic (w1\<otimes>A))\<circ>(basic (w2\<otimes>B))\<circ>(y2))) \<and>
 (?b = Abs_diagram
 ((y1)\<circ>(basic (w1))\<circ>(basic (w2\<otimes>A))\<circ>(y2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>((fst (count A)) = 0)
\<and>(strands B))" 
using assms subresult2 subresult3 by (metis compose_leftassociativity leftright_associativity) 

from this have "tanglerel_compbelow_centerleft ?a ?b" using tanglerel_compbelow_centerleft_def
by auto

from this have "tanglerel_compbelow ?a ?b" using tanglerel_compbelow_def by auto

from this have "tanglerel_compress ?a ?b" using tanglerel_compress_def by auto
then have " tanglerel ?a ?b" using tanglerel_def by auto
then have "tanglerel_equiv ?a ?b" using tanglerel_equiv_def  r_into_rtranclp by (metis)
then have "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>e_cup))\<circ>(basic (y2\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1) \<circ>(basic (y2\<otimes>e_cup))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"
by auto
from this show ?thesis by auto
qed

theorem metaequivalence_right_doubledrop: 
assumes "(snd (count y2))>1" 
and "w4 = makestrand  (nat ((snd (count y2)) + (-2)))" and "fst (count y2) = snd (count y1)"
shows "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>e_cup))\<circ>(basic (y2\<otimes>e_vert\<otimes>e_vert))\<circ>
(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))" 
proof-
let ?x = "x1 \<circ> (basic y1)"
have subresult1: "tanglerel_equiv 
   (Abs_diagram ((x1 \<circ> (basic y1)) \<circ>(basic (e_cup\<otimes>y2))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w4))\<circ>z1))
           (Abs_diagram ((x1 \<circ> (basic y1)) \<circ> basic y2 \<circ>z1))"  using assms metaequivalence_left 
             by auto
then have " tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>e_cup))\<circ>(basic (y2\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1) \<circ>(basic (y2\<otimes>e_cup))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"
using metaequivalence_right_drop assms by auto
from this have  " tanglerel_equiv (Abs_diagram (((x1)\<circ>(basic (y1\<otimes>e_cup)))\<circ>(basic (y2\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
              (Abs_diagram ((x1 \<circ> (basic y1)) \<circ> basic y2 \<circ>z1))" 
               using subresult1  rtranclp_trans
           Tangle.abs_eq_iff compose_leftassociativity assms
              by (metis compose_Nil metaequivalence_right test_0 walls.distinct(1))
from this show  ?thesis using compose_leftassociativity by auto
qed



theorem metaequivalence_both_doubledrop: 
assumes "(snd (count y2))>1" 
and "w4 = makestrand  (nat ((snd (count y2)) + (-2)))" 
and "w5 = makestrand (nat ((snd (count y2))))"
and "fst (count y2) = snd (count y1)"
shows "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1\<otimes>e_cup))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2\<otimes>e_vert\<otimes>e_vert))\<circ>
(basic (e_vert\<otimes>e_cap\<otimes> w5)) \<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))" 

proof-
have subresult1: "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>e_cup))\<circ>(basic (y2\<otimes>e_vert\<otimes>e_vert))\<circ>
(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))" using assms metaequivalence_right_doubledrop
             by auto
let ?p1 = "y1 \<otimes> e_cup"
let ?p2 = "y2 \<otimes> e_vert \<otimes>e_vert"
let ?p3 = "(basic (w4 \<otimes> e_cap \<otimes> e_vert))\<circ>z1"
have  "(snd (count (x\<otimes>e_vert\<otimes>e_vert))) = (snd (count (x\<otimes>e_vert)) + 1)"
using e_vert_def append_Nil append_Cons brickcount_def count_def 
by (metis (hide_lams, no_types) brickcount.simps(1) count.simps(1) count_rightcompose
leftright_associativity snd_conv)
from this have subresult2:  "(snd (count (y2\<otimes>e_vert\<otimes>e_vert))) = (snd (count (y2)) + 2)"
using e_vert_def append_Nil  append_Cons brickcount_def count_def
by (metis (hide_lams, no_types) brickcount.simps(1) count.simps(1) count_rightcompose
dbl_def dbl_simps(3) snd_conv)
from this have "snd (count (y2 \<otimes> e_vert \<otimes> e_vert)) > (snd (count y2))" by auto
from this have step1: "snd (count (?p2)) > 1" using assms  by auto
have  "(fst (count (x\<otimes>e_vert\<otimes>e_vert))) = (fst (count (x\<otimes>e_vert)) + 1)"
using e_vert_def append_Nil append_Cons brickcount_def count_def 
by (metis (hide_lams, no_types) brickcount.simps(1) count.simps(1) count_rightcompose
leftright_associativity fst_conv)
from this have assm2_substep1: "(fst (count (y2\<otimes>e_vert\<otimes>e_vert))) = (fst (count (y2)) + 2)"
using e_vert_def append_Nil append_Cons brickcount_def count_def
by (metis (hide_lams, no_types) brickcount.simps(1) count.simps(1) count_rightcompose
dbl_def dbl_simps(3) fst_conv)
have "(snd (count (y1\<otimes>e_cup))) = (snd (count y1)) + 2"
using e_cup_def count_def snd_conv append_Cons count_cup_rightcompose  by auto
from this have "(snd (count (y1\<otimes>e_cup))) = ((fst (count y2)) +2)" using assms by auto
from this have step2: "fst (count ?p2) = snd (count ?p1)" using 
assm2_substep1  by auto
from subresult2 have "snd (count ?p2) = (snd (count y2)) + 2"  by auto
from this have subresult5: "w5 = makestrand (nat (((snd (count ?p2)) + (-2))))" using assms by auto
have subresult3: "(((snd (count ?p2))>1) \<and> (w5= makestrand  (nat ((snd (count ?p2)) + (-2))))
\<and>(fst (count ?p2) = snd (count ?p1)))"
using assms step1 step2 subresult5 by auto
from this have "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>?p1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>?p2))
            \<circ>(basic (e_vert\<otimes>e_cap\<otimes>w5))\<circ>?p3))
             (Abs_diagram (x1 \<circ> basic ?p1\<circ> basic ?p2\<circ>?p3))"
 using  metaequivalence_left_doubledrop_condition by auto
from this have subresult6: "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1 \<otimes> e_cup))
  \<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2 \<otimes> e_vert \<otimes>e_vert))
            \<circ>(basic (e_vert\<otimes>e_cap\<otimes>w5))\<circ>(basic (w4 \<otimes> e_cap \<otimes> e_vert))\<circ>z1))
             (Abs_diagram (x1 \<circ> basic (y1 \<otimes> e_cup)\<circ> basic (y2 \<otimes> e_vert \<otimes>e_vert)
\<circ>(basic (w4 \<otimes> e_cap \<otimes> e_vert))\<circ>z1))"
 using  metaequivalence_left_doubledrop_condition  by auto
 from this have "tanglerel_equiv 
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1 \<otimes> e_cup))
  \<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2 \<otimes> e_vert \<otimes>e_vert))
            \<circ>(basic (e_vert\<otimes>e_cap\<otimes>w5))\<circ>(basic (w4 \<otimes> e_cap \<otimes> e_vert))\<circ>z1))
 (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))"
using subresult1 rtranclp_trans Tangle.abs_eq_iff by (metis)
from this  show ?thesis by (simp)
qed

theorem metaequivalence_top_drop: assumes "(snd (count y1))>1" 
and "w4 = makestrand  (nat ((snd (count y1)) + (-2)))" 
and "w5 = makestrand (nat ((snd (count y1))))"
and "fst (count y2) = snd (count y1)"
shows "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_cap\<otimes> w5)) \<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1)\<circ> z1))" 
proof-
from metaequivalence_right and assms have subresult1: "tanglerel_equiv 
      (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>e_cup))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))" by auto
let ?y2 = "y1 \<otimes> e_cup"
let ?z2 = "(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1"
have subresult2:"(snd (count (?y2))) = (snd (count y1)) + 2"
using e_cup_def count_def snd_conv append_Cons count_cup_rightcompose by auto
from this and assms have subresult3:"(snd (count (?y2))) >1" by auto
from subresult2 have subresult4: "w5 = makestrand (nat (snd (count ?y2) + (-2)))" using assms by auto
from this and assms and subresult3 and metaequivalence_left have "tanglerel_equiv 
      (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>?y2))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5))\<circ>?z2))
               (Abs_diagram ((x1)\<circ>(basic (?y2))\<circ>?z2))" by auto
from this have "tanglerel_equiv 
      (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1\<otimes>e_cup))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
               (Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> e_cup))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))" by auto
from this and subresult1 have "tanglerel_equiv 
      (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1\<otimes>e_cup))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5))\<circ>(basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
            (Abs_diagram (x1 \<circ> (basic y1)\<circ> z1))" using rtranclp_trans Tangle.abs_eq_iff 
by metis
then show ?thesis by simp
qed

theorem metaequivalence_bottom_doubledrag: assumes "(fst (count y1))>1" 
and "w4 = makestrand  (nat ((fst (count y1)) + (-2)))" 
and "w5 = makestrand (nat ((fst (count y1))))"
and "well_defined (x1 \<circ> basic y1 \<circ> z1)" 
shows "tanglerel_equiv (Abs_diagram ((x1)\<circ>  (basic (w4\<otimes>e_cup\<otimes>e_vert)) \<circ>
(basic (e_vert\<otimes>e_cup\<otimes>w5))\<circ>(basic (e_cap\<otimes>y1\<otimes>e_cap))\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1)\<circ> z1))" 
proof-
have "(fst (count y1))>1" using assms by auto
also have  "w4 = makestrand  (nat ((fst (count y1)) + (-2)))" using assms by auto
 have "well_defined (x1 \<circ> basic y1 \<circ> z1)"  using assms by auto
from assms and metaequivalence_bottomright have subresult1: "tanglerel_equiv 
      (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (y1\<otimes>e_cap))\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))"  
by auto
let ?y2 = "y1 \<otimes> e_cap"
let ?x2 = "x1\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))"
have subresult2:"(fst (count (?y2))) = (fst (count y1)) + 2"
using e_cup_def count_def fst_conv append_Cons count_cup_rightcompose by (metis brickcount.simps(3) count.simps(1) e_cap_def fst_count_additive)
from this and assms have subresult3:"(fst (count (?y2))) >1" by auto
have subresult4: " snd (count (y1\<otimes>e_cap)) = snd (count y1)" using e_cap_def count_def snd_conv append_Cons count_cup_rightcompose
by (metis (hide_lams, no_types) brickcount.simps(3) comm_monoid_add_class.add.right_neutral 
count.simps(1) snd_count_additive)
have "snd (count (w4\<otimes>e_cup\<otimes>e_vert)) = snd (count w4) + snd (count e_cup) +
snd (count e_vert)" using leftright_associativity snd_count_additive by (auto)
from this have subresult5: "snd (count (w4\<otimes>e_cup\<otimes>e_vert)) = snd (count w4) +3"
using count_def e_cup_def e_vert_def snd_conv by (metis ab_semigroup_add_class.add_ac(1) 
brickcount.simps(1) brickcount.simps(2) count.simps(1) inc.simps(2) numeral_inc)
have "fst (count (w4\<otimes>e_cup\<otimes>e_vert)) =  fst (count w4) + fst (count e_cup) + fst( count e_vert)"
using leftright_associativity fst_count_additive by auto
from this have subresult6: "fst (count (w4\<otimes>e_cup\<otimes>e_vert)) =  fst (count w4) + 1"
using count_def e_cup_def e_vert_def fst_conv brickcount.simps(1) count.simps(1) fst_count_additive 
fstcount_cup_rightcompose
 by (metis (full_types))
have "(snd (count (makestrand n))) = (int n)+1"  using makestrand_sndequality by auto
have subresult7: "(fst (count w4)) = (int (nat ((fst (count y1)) + (-2))))+1" using assms makestrand_fstequality
by (metis)
have "(fst (count y1) + (-2)) \<ge> 0" using assms by auto
from this  have "(int (nat ((fst (count y1)) + (-2)))) = (fst (count y1) + (-2))" using int_nat_eq assms 
by auto
from this and subresult7
 have "fst (count w4) =  (fst (count y1)) + (-2) + 1" by auto
from this have subresult8: "fst (count w4) = fst (count y1) + (-1)" by auto
from this and makestrand_fstsndequality and assms have " snd (count w4) =  fst (count y1) + (-1)"
by auto
from this and subresult5 have "snd (count (w4\<otimes>e_cup\<otimes>e_vert)) = fst (count y1) + (-1) + 3" by auto
from this and subresult2 have subresult9: "snd (count (w4\<otimes>e_cup\<otimes>e_vert)) = fst (count (y1\<otimes>e_cap))" by auto
from subresult8 and subresult6 have subresult10: "fst (count (w4\<otimes>e_cup\<otimes>e_vert)) = fst (count y1)" by auto
from subresult2 have subresult11: "w5 = makestrand (nat (fst (count ?y2) + (-2)))" using assms by auto
have subresult12: "fst (wall_count ((basic y1)\<circ>z1)) = snd(wall_count x1)" 
using assms diagram_fst_equals_snd by metis
have  "fst (wall_count ((basic y1)\<circ>z1)) = fst(count y1)" using wall_count_def compose_def by auto
from this and subresult12 have "snd(wall_count x1) = (fst (count y1))" by simp
from this and subresult10 have subresult13: "snd(wall_count x1) = (fst (count (w4\<otimes>e_cup\<otimes>e_vert)))" by auto
have subresult14:"snd (wall_count (x1\<circ>(basic y1))) = fst(wall_count z1)" 
using assms diagram_fst_equals_snd by (metis compose_leftassociativity)
have "snd (wall_count (x1\<circ>(basic y1))) = snd (count y1)" using wall_count_def compose_def by (metis snd_conv wall_count.simps(1) wall_count_compose)
from subresult14 and this have subresult15: "fst(wall_count z1) =  snd (count y1)" by simp
from this and subresult4 have subresult16: "fst(wall_count z1) = snd (count ?y2)" by simp

have "(fst (wall_count ((basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic ?y2)\<circ>z1))) = fst (count (w4\<otimes>e_cup\<otimes>e_vert))"
by auto
from this and  subresult13 have subresult17: "snd(wall_count x1) = (fst (wall_count ((basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic ?y2)\<circ>z1)))"
by auto

have  "list_sum (wall_list (?y2*z1)) = 0" using subresult16 
by (metis add_nonneg_eq_0_iff assms(4) 
compose_Nil diagram_list_sum_zero diagram_wall_list_zero list_sum.simps(2) 
list_sum_append monoid_add_class.add.left_neutral subresult15 wall_list.simps(2) 
wall_list_compose wall_list_list_sum_non_negative)
from this have subresult18: " list_sum (wall_list ((basic ?y2)\<circ>z1)) = 0" by auto
from subresult9 have "snd (count (w4\<otimes>e_cup\<otimes>e_vert)) = (fst (wall_count (((basic ?y2)\<circ>z1))))"
by (metis fst_conv wall_count.simps(1) wall_count_compose)
from this and subresult18
have "list_sum (wall_list ((w4\<otimes>e_cup\<otimes>e_vert)*((basic ?y2)\<circ>z1))) = 0"
using 
add_nonneg_eq_0_iff assms(4) 
compose_Nil diagram_list_sum_zero diagram_wall_list_zero list_sum.simps(2) 
list_sum_append monoid_add_class.add.left_neutral subresult15 wall_list.simps(2) 
wall_list_compose wall_list_list_sum_non_negative
by (metis `fst (wall_count (basic y1 \<circ> z1)) = fst (count y1)` `
snd (wall_count x1) = fst (count y1)` diff_self subresult16 subresult9)
from this have subresult19: "list_sum (wall_list ((basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>((basic ?y2)\<circ>z1))) = 0"
by auto

from diagram_list_sum_subsequence have subresult20: " ((list_sum (wall_list x1) = 0)
\<and>((list_sum (wall_list ((basic y1)\<circ>z1)))=0))" using assms by metis
have "list_sum (wall_list ((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (y1\<otimes>e_cap))\<circ>z1)) = 
list_sum (wall_list ((x1))) + list_sum (wall_list ((basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (y1\<otimes>e_cap))\<circ>z1))
+ abs ((fst (wall_count ((basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (y1\<otimes>e_cap))\<circ>z1))) - (snd (wall_count x1)))"
using wall_list_list_sum_compose by auto
from this and subresult19 and subresult20 and subresult17 
have subresult21: "list_sum (wall_list ((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (y1\<otimes>e_cap))\<circ>z1)) =0"
by (metis diff_self monoid_add_class.add.right_neutral wall_list_list_sum_abs)

have subresult22:" (fst (wall_count ((x1)\<circ>(basic y1)\<circ>z1))) = fst(wall_count x1)" using wall_count_def
compose_Cons by (metis fst_conv wall_count_compose)
 have "abs( fst(wall_count (x1 \<circ>(basic y1)\<circ>z1))) = 0" using well_defined_fst_wall_count assms  
by metis
from subresult22 and this have subresult23:"abs (fst(wall_count x1)) = 0"  by auto

have subresult24:" (snd (wall_count ((x1)\<circ>(basic y1)\<circ>z1))) = snd(wall_count z1)" using wall_count_def
compose_Cons by (metis snd_conv wall_count_compose)
 have "abs( snd(wall_count (x1 \<circ>(basic y1)\<circ>z1))) = 0" using well_defined_snd_wall_count assms  
by metis
from subresult24 and this have subresult25:"abs (snd(wall_count z1)) = 0"  by auto
have subresult26:" (fst (wall_count (((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (y1\<otimes>e_cap))\<circ>z1))))
= fst(wall_count x1)" 
using wall_count_def compose_Cons by (metis fst_conv wall_count_compose)
from this and subresult23 
have subresult27:" abs (fst (wall_count (((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (y1\<otimes>e_cap))\<circ>z1)))) = 0" by auto
have subresult28:" (snd (wall_count (((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (y1\<otimes>e_cap))\<circ>z1))))
= snd (wall_count z1)" 
using wall_count_def compose_Cons
 by (metis snd_conv wall_count_compose)
from subresult24  and subresult25 and subresult28 and subresult21 have subresult29:
" abs (snd (wall_count (((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (y1\<otimes>e_cap))\<circ>z1))))= 0" by auto
from subresult27 and subresult29 and subresult21 have subresult30: "well_defined  
(((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (y1\<otimes>e_cap))\<circ>z1))" 
using monoid_add_class.add.left_neutral well_defined_def
by (auto)
from this and assms and subresult3 and metaequivalence_bottomleft and subresult30
have "tanglerel_equiv 
      (Abs_diagram ((?x2)\<circ>(basic (e_vert\<otimes>e_cup\<otimes> w5))\<circ>(basic (e_cap\<otimes>?y2))\<circ>z1))
               (Abs_diagram ((?x2)\<circ>(basic (?y2))\<circ>z1))"
using compose_leftassociativity subresult11
by (metis)
from this have "tanglerel_equiv
 (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cup\<otimes> w5))\<circ>(basic (e_cap\<otimes>y1\<otimes>e_cap))\<circ>z1))  
       (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (y1\<otimes>e_cap))\<circ>z1))" 
using compose_leftassociativity by auto
 

from this and subresult1 have "tanglerel_equiv 
 (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cup\<otimes> w5))\<circ>(basic (e_cap\<otimes>y1\<otimes>e_cap))\<circ>z1))   
          (Abs_diagram (x1 \<circ> (basic y1)\<circ> z1))" using rtranclp_trans Tangle.abs_eq_iff 
by metis
then show ?thesis by simp
qed


theorem metaequivalence_positive_cross: assumes "(fst (count y1))>1" and "(snd (count y2)) >1"
and "w4 = makestrand  (nat ((fst (count y1)) + (-2)))" 
and "w5 = makestrand (nat ((snd (count y2)) + (-2)))"
and "well_defined (x1 \<circ> basic y1 \<circ> basic y2 \<circ>z1)" 
shows "tanglerel_equiv (Abs_diagram ((x1)\<circ>  (basic (e_vert\<otimes>e_cup\<otimes>w4)) \<circ>
(basic (e_cap\<otimes>y1))\<circ>(basic (y2\<otimes>e_cup))\<circ>(basic (w5\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))" 
proof-
have subresult: "tanglerel_equiv (Abs_diagram ((x1)\<circ>  (basic (e_vert\<otimes>e_cup\<otimes>w4)) \<circ>
(basic (e_cap\<otimes>y1))\<circ>(basic y2)\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))" using assms metaequivalence_bottomleft
by auto
let ?x2 = "(x1)\<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4)) \<circ>(basic (e_cap\<otimes>y1))"
have "tanglerel_equiv (Abs_diagram (?x2\<circ>(basic (y2\<otimes>e_cup))\<circ>(basic (w5\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
           (Abs_diagram (?x2\<circ>(basic y2)\<circ>z1))" using assms metaequivalence_right by (metis (full_types))
from this have "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4)) \<circ>(basic (e_cap\<otimes>y1))
\<circ>(basic (y2\<otimes>e_cup))\<circ>(basic (w5\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
           (Abs_diagram ((x1)\<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4)) \<circ>(basic (e_cap\<otimes>y1))\<circ>(basic y2)\<circ>z1))"
using compose_leftassociativity by (auto)
from this and subresult have " tanglerel_equiv  (Abs_diagram ((x1)\<circ>(basic (e_vert\<otimes>e_cup\<otimes>w4)) \<circ>(basic (e_cap\<otimes>y1))
\<circ>(basic (y2\<otimes>e_cup))\<circ>(basic (w5\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))"
using rtranclp_trans Tangle.abs_eq_iff by metis
from this show ?thesis by simp
qed

theorem metaequivalence_negative_cross: assumes "(fst (count y1))>1" and "(snd (count y2)) >1"
and "w4 = makestrand  (nat ((fst (count y1)) + (-2)))" 
and "w5 = makestrand (nat ((snd (count y2)) + (-2)))"
and "well_defined (x1 \<circ> basic y1 \<circ> basic y2 \<circ>z1)" 
shows "tanglerel_equiv (Abs_diagram ((x1)\<circ>  (basic (w4\<otimes>e_cup\<otimes>e_vert)) \<circ>
(basic (y1 \<otimes>e_cap))\<circ>(basic (e_cup\<otimes>y2))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w5))\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))" 
proof-
have subresult: "tanglerel_equiv (Abs_diagram ((x1)\<circ>  (basic (w4\<otimes>e_cup\<otimes>e_vert)) \<circ>
(basic (y1\<otimes>e_cap))\<circ>(basic y2)\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))" using assms metaequivalence_bottomright
by auto
let ?x2 = "(x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert)) \<circ>(basic (y1 \<otimes>e_cap))"
have "tanglerel_equiv (Abs_diagram (?x2\<circ>(basic (e_cup\<otimes>y2))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w5))\<circ>z1))
           (Abs_diagram (?x2\<circ>(basic y2)\<circ>z1))" using assms metaequivalence_left by (metis (full_types))
from this have  "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert)) \<circ>(basic (y1 \<otimes>e_cap))
\<circ>(basic (e_cup\<otimes>y2))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w5))\<circ>z1))
           (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert)) \<circ>(basic (y1 \<otimes>e_cap))\<circ>(basic y2)\<circ>z1))"
using compose_leftassociativity by auto
from subresult and this have                              




" tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>e_cup\<otimes>e_vert)) \<circ>(basic (y1 \<otimes>e_cap))
\<circ>(basic (e_cup\<otimes>y2))\<circ>(basic (e_vert\<otimes>e_cap\<otimes>w5))\<circ>z1))
           (Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic y2)\<circ>z1))"
using Tangle.abs_eq_iff by (metis)
from this show ?thesis by simp
qed


theorem metaequivalence_thriple_drop: 
assumes "(snd (count y3))>1" 
and "w4 = makestrand  (nat ((snd (count y3)) + (-2)))" 
and "w5 = makestrand (nat ((snd (count y3))))"
and "fst (count y2) = snd (count y1)"
and "(fst (count y3)) = (snd (count y2))"
shows "tanglerel_equiv (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1\<otimes>e_cup))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2\<otimes>e_vert\<otimes>e_vert))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) \<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1)\<circ>(basic y2)\<circ>(basic y3)\<circ>z1))" 
proof-
let ?x2 = "x1\<circ> (basic y1)"
have  "tanglerel_equiv (Abs_diagram (?x2\<circ>(basic (e_cup\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) \<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
             (Abs_diagram (?x2\<circ>(basic y2)\<circ>(basic y3)\<circ>z1))" 
using metaequivalence_both_doubledrop assms by auto
from this have subresult1:
"tanglerel_equiv (Abs_diagram (x1\<circ> (basic y1)\<circ>(basic (e_cup\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) \<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
             (Abs_diagram (x1\<circ> (basic y1)\<circ>(basic y2)\<circ>(basic y3)\<circ>z1))" using compose_leftassociativity 
by simp
have subresult2: "fst (count e_cup) = 0" using e_cup_def 
count_def add_left_cancel comm_monoid_add_class.add.right_neutral fst_count_additive fstcount_cup_rightcompose
by (auto)
let ?z2 = "(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) 
\<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1"
let ?w2 = "y2 \<otimes> e_cup"
have "fst (count ?w2) = fst (count y2)" using fstcount_cup_rightcompose by auto
from this and assms have subresult3:"fst (count ?w2) = snd (count y1)" by auto

let ?B = "e_vert \<otimes> e_vert"
have subresult4: "strands ?B"
using Tangles.append.append_Nil e_vert_def makestrand.simps(1) strand_makestrand strands.simps(2)
 by (metis)
from subresult4 and subresult2 and subresult3 and exI have 
"(strands ?B) \<and> (fst (count ?w2) = snd (count y1)) \<and> (fst (count e_cup) = 0)"
by auto
from this and exI and tanglerel_compbelow_centerright_def have 
"tanglerel_compbelow_centerright 
(Abs_diagram (x1 \<circ> (basic (e_cup \<otimes> y1)) \<circ> (basic (?B\<otimes> ?w2)) \<circ> ?z2))
(Abs_diagram (x1 \<circ> (basic ( y1)) \<circ> (basic (e_cup \<otimes> ?w2)) \<circ> ?z2))"
by metis
from this and compose_leftassociativity and leftright_associativity have 
"tanglerel_compbelow_centerright 
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) \<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))
\<circ>z1))
 (Abs_diagram (x1\<circ>(basic y1)\<circ>(basic (e_cup\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) \<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"
by auto
from this have
"tanglerel_compbelow 
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) \<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))
\<circ>z1))
 (Abs_diagram (x1\<circ>(basic y1)\<circ>(basic (e_cup\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) \<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"
using tanglerel_compbelow_def by auto
from this have 
"tanglerel_compress
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) \<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))
\<circ>z1))
 (Abs_diagram (x1\<circ>(basic y1)\<circ>(basic (e_cup\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) \<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"
using tanglerel_compress_def by auto
from this have
"tanglerel
(Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) \<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))
\<circ>z1))
 (Abs_diagram (x1\<circ>(basic y1)\<circ>(basic (e_cup\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) \<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"
using tanglerel_def by auto
from this have 
"tanglerel_equiv
(Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) \<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))
\<circ>z1))
 (Abs_diagram (x1\<circ>(basic y1)\<circ>(basic (e_cup\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) \<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"
using tanglerel_equiv_def r_into_rtranclp by metis
from this and subresult1 and r_into_rtranclp rtranclp_trans have subresult5:
"tanglerel_equiv
(Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) \<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))
\<circ>z1))
(Abs_diagram (x1\<circ>(basic y1)\<circ>(basic y2)\<circ>(basic y3)\<circ>z1))"
by (metis Tangle.abs_eq_iff compose_Nil)

have "snd (count (e_cup \<otimes> y1)) = 2 + snd (count y1)" using snd_count_additive 
comm_semiring_1_class.normalizing_semiring_rules(24) count_cup_rightcompose snd_conv 
snd_count_additive by metis
from this and assms have subresult6: "snd (count (e_cup \<otimes> y1)) = 2 + fst (count y2)" by auto

let ?subs1 = "(e_cup \<otimes> y1)"
let ?subs2 = " (e_vert \<otimes> e_vert \<otimes> y2)"
have " fst (count (e_vert \<otimes> e_vert \<otimes> y2)) = 2 + fst (count y2)"
using fst_count_additive e_vert_count by auto 
from this and subresult6 have "snd (count (?subs1)) = 
fst (count (?subs2))" by auto
from this and subresult2 and subresult4 have
"(strands ?B) \<and> (fst (count ?subs2) = snd (count ?subs1)) \<and> (fst (count e_cup) = 0)" by auto

from this  exI and tanglerel_compbelow_centerleft_def  
have "tanglerel_compbelow_centerleft
 (Abs_diagram ((x1)\<circ>(basic (?subs1 \<otimes> e_cup))\<circ>(basic (?subs2\<otimes>?B))\<circ>
?z2))
 (Abs_diagram ((x1)\<circ>(basic (?subs1))\<circ>(basic (?subs2\<otimes>e_cup))\<circ>
?z2))" by metis
from this and leftright_associativity have
"tanglerel_compbelow_centerleft
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1 \<otimes> e_cup))\<circ>(basic (e_vert\<otimes>e_vert \<otimes> y2 \<otimes> e_vert \<otimes> e_vert))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) 
\<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) 
\<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"
by auto

from this and tanglerel_compbelow_def have
"tanglerel_compbelow
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1 \<otimes> e_cup))\<circ>(basic (e_vert\<otimes>e_vert \<otimes> y2 \<otimes> e_vert \<otimes> e_vert))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) 
\<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) 
\<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"
by auto

from this and tanglerel_compress_def and tanglerel_def have
"tanglerel
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1 \<otimes> e_cup))\<circ>(basic (e_vert\<otimes>e_vert \<otimes> y2 \<otimes> e_vert \<otimes> e_vert))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) 
\<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) 
\<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))"
by auto
from this and  tanglerel_equiv_def and  r_into_rtranclp have
"tanglerel_equiv
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1 \<otimes> e_cup))\<circ>(basic (e_vert\<otimes>e_vert \<otimes> y2 \<otimes> e_vert \<otimes> e_vert))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) 
\<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1))\<circ>(basic (e_vert\<otimes>e_vert\<otimes>y2\<otimes>e_cup))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) 
\<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))" by metis
from this and subresult5 and r_into_rtranclp rtranclp_trans have
 "tanglerel_equiv
 (Abs_diagram ((x1)\<circ>(basic (e_cup\<otimes>y1 \<otimes> e_cup))\<circ>(basic (e_vert\<otimes>e_vert \<otimes> y2 \<otimes> e_vert \<otimes> e_vert))\<circ>
(basic (e_vert\<otimes>e_vert\<otimes>y3\<otimes>e_vert\<otimes>e_vert))\<circ>(basic (e_vert\<otimes>e_cap\<otimes> w5)) 
\<circ> (basic (w4\<otimes>e_cap\<otimes>e_vert))\<circ>z1))
 (Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic y2)\<circ>(basic y3)\<circ>z1))"
by (metis Tangle.abs_eq_iff compose_Nil)
from this show ?thesis by auto
qed
