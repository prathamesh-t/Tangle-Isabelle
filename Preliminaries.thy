theory Preliminaries
imports Datatype Main Typedef 
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
                |empty

text{*block is obtained by putting bricks next to each other*}
datatype block = cement brick
                 |cons brick block  (infixr "#" 60)              

text{*walls are link diagrams obtained by placing a horizontal blocks a top each other*}
(* Consistent number - datatype wall *)
datatype walls = basic block
                |prod block  walls  (infixr "*" 66)

text{*Concatenate gives us the block obtained by putting two blocks next to each other*}


primrec concatenate :: "block => block => block" (infixr "\<otimes>" 65) where
concatenates_Nil: "(cement x) \<otimes> ys = cons x ys" |
concatenates_Cons: "((x#xs)\<otimes>ys) = x#(xs\<otimes>ys)"

text{*Associativity properties of concatenation*}
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

text{*Compose gives us the wall obtained by putting a wall above another, perhaps in an invalid way.
*}
primrec compose :: "walls => walls => walls" (infixr "\<circ>" 66) where
compose_Nil: "(basic x) \<circ> ys =  prod x ys" |
compose_Cons: "((prod x xs)\<circ>ys) = prod x (xs\<circ>ys)"

text{*Associativity properties of composition*}
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



(*domain tells us the number of incoming strands*)
 primrec domain::"brick \<Rightarrow> int"
 where
 "domain vert = 1"|
 "domain cup = 0"|
 "domain cap = 2"|
 "domain over = 2"|
 "domain under = 2"|
 "domain empty = 0"


(*co-domain tells us the number of outgoing strands*)
 primrec codomain::"brick \<Rightarrow> int"
 where
 "codomain vert = 1"|
 "codomain cup = 2"|
 "codomain cap = 0"|
 "codomain over = 2"|
 "codomain under = 2"|
 "codomain empty = 0"


(*domain_block tells us the number of incoming strands of a block*)
 primrec domain_block::"block \<Rightarrow> int "
 where
 "domain_block (cement x) = (domain x)"
 |"domain_block (cons x y) = (domain x + (domain_block y))"


(*codomain_block tells us the number of outgoing strands of a block*)

 primrec codomain_block::"block \<Rightarrow> int "
 where
 "codomain_block (cement x) = (codomain x)"
 |"codomain_block (cons x y) = (codomain x + (codomain_block y))"


(*domain_wall tells us the number of incoming strands of a wall*)

primrec domain_wall:: "walls \<Rightarrow> int" where
"domain_wall (basic x) = domain_block x"                                               
|"domain_wall (x*ys) = domain_block x"

(*domain_wall tells us the number of incoming strands of a wall*)

primrec codomain_wall:: "walls \<Rightarrow> int" where
"codomain_wall (basic x) = codomain_block x"                                               
|"codomain_wall (x*ys) = codomain_wall ys"

lemma domain_wall_compose: "domain_wall (xs\<circ>ys) = domain_wall xs"
    apply(induct_tac xs)
    apply(auto)
    done

lemma codomain_wall_compose: "codomain_wall (xs\<circ>ys) = codomain_wall ys"
    apply(induct_tac xs)
    apply(auto)
    done 

text{*this lemma tells us the number of incoming and outgoing strands of a composition of two walls*}


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

text{*The following lemmas tell us that the number of incoming and outgoing strands of every brick 
is a non negative integer*}
lemma domain_nonnegative: "(domain x) \<ge> 0" 
using domain.simps  brick.exhaust le_cases not_numeral_le_zero zero_le_one by (metis)


lemma codomain_nonnegative: "(codomain x) \<ge> 0" 
      apply(case_tac x)
      apply(auto)
      done

text{*The following lemmas tell us that the number of incoming and outgoing strands of every block 
is a non negative integer*}
lemma domain_block_nonnegative: "domain_block x \<ge> 0" 
    apply(induct_tac x)
    apply(auto)
    apply(simp add:domain_nonnegative)
    apply (simp add: add_increasing domain_nonnegative)
    done


lemma codomain_block_nonnegative: "(codomain_block x) \<ge> 0" 
    apply(induct_tac x)
    apply(auto)
    apply(simp add:codomain_nonnegative)
    apply (simp add: add_increasing codomain_nonnegative)
    done


text{*The following lemmas tell us that if a block is appended to a block with incoming strands, then
the resultant block has incoming strands*}

lemma domain_positive: "((domain_block (cement x)) > 0) \<or> ((domain_block y) > 0) 
\<Longrightarrow> (domain_block (x#y) > 0)" 
proof-
 have "(domain_block (x#y)) =  (domain x) + (domain_block y)"  by auto
 also have " (domain x) = (domain_block (cement x))" by auto
 then have "(domain_block (cement x) > 0) = (domain x > 0)"  by auto
 then have "((domain x > 0) \<or> (domain_block y > 0)) \<Longrightarrow> (domain x + domain_block y)>0"
    using domain_nonnegative add_nonneg_pos add_pos_nonneg domain_block_nonnegative by metis 
 from this  
       show "((domain_block(cement x)) > 0) \<or> ((domain_block y) > 0) \<Longrightarrow> (domain_block (x#y) > 0)" 
            by auto
qed
  
lemma domain_additive:  "(domain_block (x\<otimes>y))= (domain_block x) + (domain_block y)"
    apply(induct_tac x)
    apply(auto)
    done

lemma codomain_additive:   "(codomain_block (x\<otimes>y))= (codomain_block x) + (codomain_block y)"
    apply(induct_tac x)
    apply(auto)
    done

lemma domain_zero_sum: assumes "(domain_block x) + (domain_block y) = 0"
shows "domain_block x = 0" and "domain_block y = 0"
    using domain_block_nonnegative add_nonneg_eq_0_iff assms
    apply metis
    by (metis add_nonneg_eq_0_iff assms domain_block_nonnegative)

lemma domain_block_positive: assumes "domain_block y>0" or "domain_block y>0"
shows "(domain_block (x\<otimes>y)) > 0"
   apply (simp add: domain_additive)
   by (metis assms(1) domain_additive domain_block_nonnegative domain_zero_sum(2) less_le)

lemma codomain_block_positive: assumes "codomain_block y>0" or "codomain_block y>0"
shows "(codomain_block (x\<otimes>y)) > 0"
   apply (simp add: codomain_additive)
   using  assms(1) codomain_additive codomain_block_nonnegative eq_neg_iff_add_eq_0 
          le_less_trans less_le neg_less_0_iff_less
   by (metis)

text{*We prove that if the first count of a block is zero, then it is composed of cups and empty bricks. In
order to do that we define the functions brick_is_cup and is_cup which check if a given block is 
composed of cups or if the blocks are composed of blocks*}

primrec brick_is_cup::"brick \<Rightarrow> bool"
where
"brick_is_cup vert = False"|
"brick_is_cup cup = True"|
"brick_is_cup cap = False"|
"brick_is_cup over = False"|
"brick_is_cup under = False"|
"brick_is_cup empty = True"


primrec is_cup::"block \<Rightarrow> bool"
where
"is_cup (cement x) = brick_is_cup x"|
"is_cup (x#y) = (if (x= cup)\<or>(x=empty) then (is_cup y) else False)"
(*
(* Why three components??? Should not be true: CHECK*)
lemma is_cup_basic: "((is_cup x) = False) \<Longrightarrow> 
((x=(cement vert))\<or>(x=(cement cap))\<or>(x=(cement over))\<or>(x=(cement under)))\<or>(\<exists>y1.\<exists>y2.\<exists>y3.(x=(y1 \<otimes> y2\<otimes>y3)\<and> 
((y1=(cement vert))\<or>(y1=(cement cap))\<or>(y1=(cement over))\<or>(y1=(cement under)))
\<or>(y2=(cement vert))\<or>(y2=(cement cap))\<or>(y2=(cement over))\<or>(y2=(cement under)))
\<or>((y3=(cement vert))\<or>(y3=(cement cap))\<or>(y3=(cement over))\<or>(y3=(cement under))))"
by metis
*)


lemma brickcount_zero_implies_cup:"(domain x= 0) \<Longrightarrow> (x = cup)\<or> (x = empty)"
   apply(case_tac x)
   apply(auto)
   done

lemma brickcount_zero_implies_brick_is_cup:"(domain x= 0) \<Longrightarrow> (brick_is_cup x)"
 apply(case_tac x)
 apply(auto)
 done

lemma domain_zero_implies_is_cup:"(domain_block x= 0) \<Longrightarrow> (is_cup x)"
proof(induction x)
 case (cement y)
  have "(domain_block (cement y)) = (domain y)" 
       by auto
  from this have " (domain_block (cement y) = 0) \<equiv>(domain y=0)"  
       by auto
  then  have " (domain_block (cement y) = 0)  \<Longrightarrow>(brick_is_cup y)" 
       using brickcount_zero_implies_brick_is_cup
       by auto
  then have "(domain_block (cement y) = 0)  \<Longrightarrow>(is_cup (cement y))" by auto 
  from this show ?case using cement.prems by (auto) 
 next
 case (cons a y)
   show ?case 
   proof-
   have step1: "domain_block (a # y) =  (domain a) + (domain_block y)" 
               by auto
   with domain_zero_sum have"domain_block y = 0" 
               by (metis concatenates_Nil cons.prems domain_additive)
   then have step2: "(is_cup y)" 
               using cons.IH by (auto) 
   with step1 and domain_zero_sum  
            have "domain a= 0" 
                 by (metis cons.prems domain_block.simps(1))
   then  have "brick_is_cup a" 
               using brickcount_zero_implies_brick_is_cup by auto
   with assms have "a=cup \<or> a = empty" 
        using brick_is_cup_def by (metis `domain a = 0` brickcount_zero_implies_cup)
   with step2 have "is_cup (a#y)" 
        using is_cup_def by auto
   then show ?case by auto
 qed
qed


text{* We need a function that checks if a wall represents a knot diagram. The function well_defined 
serves this purpose. It ensures that all the incoming strands and outgoing strands of constituend 
blocks are matched and the wall itself has not incoming and outgoing strands. It is defined using 
the function wall_count_list gives the list of number of incoming strand of a constituent block 
minus the outgoing strand of the block below*}

(* Much easier approach, pattern match by single block is fine, constructor check one case*)

primrec list_sum::"int list \<Rightarrow> int" 
where
"list_sum [] = 0"|
"list_sum (x#xs) = x+ list_sum xs"



(*domain-co-domain-list*)
primrec domain_codomain_list:: "walls \<Rightarrow> int list" where
"domain_codomain_list (basic x) = []"|
"domain_codomain_list (x * y) =  (abs ((domain_wall y) - (codomain_block x)))#(domain_codomain_list y)"


lemma domain_codomain_list_compose: " domain_codomain_list (x \<circ> y) = 
(domain_codomain_list x)@((abs ((domain_wall y) -(codomain_wall x)))#(domain_codomain_list y))"
       apply(induct_tac x)
       apply(auto)
       apply(simp add: domain_wall_compose codomain_wall_compose)
       done


(* avoid the names well-defined ..., simply say is_lin, is_tangle*)

definition well_defined_tangle::"walls \<Rightarrow> bool" where
"well_defined_tangle x \<equiv>  (list_sum (domain_codomain_list x) = 0)"

primrec is_tangle_diagram::"walls \<Rightarrow>  bool"
where
"is_tangle_diagram (basic x) = True"
|"is_tangle_diagram (x*xs) = (if is_tangle_diagram xs then (codomain_block x = domain_wall xs) else False)"


definition is_link_diagram::"walls \<Rightarrow>  bool"
where
"is_link_diagram x \<equiv> (if (is_tangle_diagram x) 
                        then (abs (domain_wall x) + abs(codomain_wall x) = 0) 
                         else False)"

definition well_defined::"walls \<Rightarrow> bool" where
"well_defined x \<equiv> ( (list_sum (domain_codomain_list x)+(abs(domain_wall x))
+ abs(codomain_wall x)) = 0)"


lemma list_sum_non_negative:"list_sum(domain_codomain_list x) \<ge> 0"
apply(induct_tac x)
apply(auto)
apply(simp add: abs_non_negative)
done


end
