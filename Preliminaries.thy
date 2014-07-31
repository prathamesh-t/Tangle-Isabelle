theory Preliminaries
imports Datatype Main Typedef 
begin

text{* This theory Constains the definition of a Link. A link is defined as Link diagrams upto 
 equivalence moves. Link diagrams are defined in terms of the Constituent tangles*}

text{*each  block is a horizontal block built by putting basic link bricks next to each other.
(1) vert is the straight line
(2) cup is the up facing cup
(3) cap is the bottom facing 
(4) over is the positive cross
(5) under is the negative cross*}

datatype brick = vert
                |cup
                |cap
                |over
                |under
         
text{*block is obtained by putting bricks next to each other*}

type_synonym block = "brick list"

text{*wall are link diagrams obtained by placing a horizontal blocks a top each other*}
(* Consistent number - datatype wall *)
datatype wall =  basic block
                |prod block  wall  (infixr "*" 66)

text{*Concatenate gives us the block obtained by putting two blocks next to each other*}


primrec concatenate :: "block => block => block" (infixr "\<otimes>" 65) where
concatenates_Nil: "[] \<otimes> ys = ys" |
concatenates_Cons: "((x#xs)\<otimes>ys) = x#(xs\<otimes>ys)"

lemma empty_concatenate: "xs \<otimes> Nil = xs"
 apply(induct_tac xs)
 apply(auto)
 done

text{*Associativity properties of Conscatenation*}
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
primrec compose :: "wall => wall => wall" (infixr "\<circ>" 66) where
compose_Nil: "(basic x) \<circ>  ys = prod x ys" |
compose_Cons: "((prod x xs)\<circ>ys) = prod x (xs\<circ>ys)"

text{*Associativity properties of composition*}
lemma compose_leftassociativity: "(((x::wall) \<circ> y) \<circ> z) = (x\<circ>y \<circ>z)"
apply(induct_tac x)
apply(auto)
done

lemma compose_rightassociativity: "(x::wall) \<circ> (y \<circ> z) = (x\<circ>y \<circ>z)"
apply(induct_tac x)
apply(auto)
done



text{*block-length of a block is the number of bricks in a given block*}
primrec block_length::"block \<Rightarrow> nat"
where
"block_length [] = 0"|
"block_length (Cons x y) = 1 + (block_length y)"



(*domain tells us the number of incoming strands*)
 primrec domain::"brick \<Rightarrow> int"
 where
 "domain vert = 1"|
 "domain cup = 0"|
 "domain cap = 2"|
 "domain over = 2"|
 "domain under = 2"

lemma domain_non_negative:"\<forall>x.(domain x) \<ge> 0"
 
proof-
 have "\<forall>x.(x = vert)\<or>(x = over)\<or>(x=under)\<or>(x=cap)\<or>(x=cup)"
               by (metis brick.exhaust)  
 moreover have "\<forall>x.(((x = vert)\<or>(x = over)\<or>(x=under)\<or>(x=cap)\<or>(x=cup)) \<longrightarrow> (domain x) \<ge> 0)"
              using domain.simps by (metis order_refl zero_le_numeral zero_le_one)
 ultimately show ?thesis by auto
qed      
(*co-domain tells us the number of outgoing strands*)
 primrec codomain::"brick \<Rightarrow> int"
 where
 "codomain vert = 1"|
 "codomain cup = 2"|
 "codomain cap = 0"|
 "codomain over = 2"|
 "codomain under = 2"

(*domain-block tells us the number of incoming strands of a block*)
 primrec domain_block::"block \<Rightarrow> int "
 where
 "domain_block [] = 0"
 |"domain_block (Cons x y) = (domain x + (domain_block y))"

lemma domain_block_non_negative:"domain_block xs \<ge> 0"
      apply(induct_tac xs)
      apply(auto)
      apply(simp add:domain_non_negative)
      done
(*codomain-block tells us the number of outgoing strands of a block*)

 primrec codomain_block::"block \<Rightarrow> int "
 where
 "codomain_block [] = 0"
 |"codomain_block (Cons x y) = (codomain x + (codomain_block y))"


(*domain-wall tells us the number of incoming strands of a wall*)

primrec domain_wall:: "wall \<Rightarrow> int" where
"domain_wall (basic x) = domain_block x"                                               
|"domain_wall (x*ys) = domain_block x"

(*domain-wall tells us the number of incoming strands of a wall*)

fun codomain_wall:: "wall \<Rightarrow> int" where
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

text{*this lemma tells us the number of incoming and outgoing strands
of a composition of two wall*}


text{*absolute value*}
definition abs::"int \<Rightarrow> int" where
"abs x \<equiv> if (x\<ge>0) then x else (0-x)" 

text{*theorems about abs*}
lemma abs_zero: assumes "abs x = 0" shows "x = 0" 
 using abs_def assms eq_iff_diff_eq_0
 by metis

lemma abs_zero_equality: assumes "abs (x - y) = 0" shows "x = y" 
 using assms abs_zero  eq_iff_diff_eq_0 
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
    done


lemma codomain_block_nonnegative: "(codomain_block x) \<ge> 0" 
    apply(induct_tac x)
    apply(auto)
    apply(simp add:codomain_nonnegative)
    done


text{*The following lemmas tell us that if a block is appended to a block with incoming strands, then
the resultant block has incoming strands*}

lemma domain_positive: "((domain_block (x#Nil)) > 0) \<or> ((domain_block y) > 0) 
\<Longrightarrow> (domain_block (x#y) > 0)" 
proof-
 have "(domain_block (x#y)) =  (domain x) + (domain_block y)"  by auto
 also have " (domain x) = (domain_block (x#Nil))" by auto
 then have "(domain_block (x#Nil) > 0) = (domain x > 0)"  by auto
 then have "((domain x > 0) \<or> (domain_block y > 0)) \<Longrightarrow> (domain x + domain_block y)>0"
    using domain_nonnegative add_nonneg_pos add_pos_nonneg domain_block_nonnegative by metis 
 from this  
       show "((domain_block(x#Nil)) > 0) \<or> ((domain_block y) > 0) \<Longrightarrow> (domain_block (x#y) > 0)" 
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
order to do that we define the functions brick-is-cup and is-cup which check if a given block is 
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
"is_cup [] = True"|
"is_cup (x#y) = (if (x= cup) then (is_cup y) else False)"


lemma brickcount_zero_implies_cup:"(domain x= 0) \<Longrightarrow> (x = cup)"
   apply(case_tac x)
   apply(auto)
   done

lemma brickcount_zero_implies_brick_is_cup:"(domain x= 0) \<Longrightarrow> (brick_is_cup x)"
 apply(case_tac x)
 apply(auto)
 done

lemma domain_zero_implies_is_cup:"(domain_block x= 0) \<Longrightarrow> (is_cup x)"
proof(induction x)
 case Nil
  show ?case by auto
  next
 case (Cons a y)
   show ?case 
   proof-
   have step1: "domain_block (a # y) =  (domain a) + (domain_block y)" 
               by auto
   with domain_zero_sum have"domain_block y = 0" 
               by (metis (full_types) Cons.prems domain_block_nonnegative domain_positive leD neq_iff)
   then have step2: "(is_cup y)" 
               using Cons.IH by (auto) 
   with step1 and domain_zero_sum  
            have "domain a= 0" 
              by (metis `domain_block y = 0` comm_monoid_add_class.add.right_neutral Cons.prems)
   then  have "brick_is_cup a" 
               using brickcount_zero_implies_brick_is_cup by auto
   with assms have "a=cup" 
        using brick_is_cup_def by (metis `domain a = 0` brickcount_zero_implies_cup)
   with step2 have "is_cup (a#y)" 
        using is_cup_def by auto
   then show ?case by auto
 qed
qed


text{* We need a function that checks if a wall represents a knot diagram.*}

primrec is_tangle_diagram::"wall \<Rightarrow>  bool"
where
"is_tangle_diagram (basic x) = True"
|"is_tangle_diagram (x*xs) = (if is_tangle_diagram xs
                               then (codomain_block x = domain_wall xs) 
                               else False)"


definition is_link_diagram::"wall \<Rightarrow>  bool"
where
"is_link_diagram x \<equiv> (if (is_tangle_diagram x) 
                        then (abs (domain_wall x) + abs(codomain_wall x) = 0) 
                         else False)"


end
