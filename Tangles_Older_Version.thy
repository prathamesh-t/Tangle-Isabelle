theory Tangles_Older_Version
imports Datatype Main tangle_relation
begin

(*each  block is a horizontal block built by putting basic tangle bricks next to each other.
(1) e1 is the straight line
(2) e2 is the up facing cusp
(3) e3 is the bottom facing cus
(4) e4 is the positive cross
(5) e5 is the negative cross*)

datatype block = e1
                |e2
                |e3
                |e4
                |e5
                |Cons block block              (infixr "\<otimes>" 65)

(*count tells us the number of incoming and outgoing strangs of each block*)
primrec count::"block \<Rightarrow> int \<times> int "
where
"count e1 = (1,1)"|
"count e2 = (0,2)"|
"count e3 = (2,0)"|
"count e4 = (2,2)"|
"count e5 = (2,2)"|
"count (Cons x y) = (fst (count x) + fst (count y), snd (count x) + snd (count y))"

lemma trivial: " count (e1 \<otimes> e2) = (1,3)"
apply(auto)
done
(*walls are tangle diagrams obtained by placing a horizontal blocks a top each other*)

datatype walls = basic block
                |prod walls walls  (infixr "\<circ>" 66)


primrec wall_count:: "walls => int \<times> int" where
"wall_count (basic x) = count x"
|"wall_count (prod x y) = (fst (wall_count x),snd (wall_count y))"

definition abs::"int \<Rightarrow> int" where
"abs x \<equiv> if (x\<ge>0) then x else (0-x)" 

primrec wall_list:: "walls \<Rightarrow> int list" where
"wall_list (basic x) = []"|
"wall_list (x \<circ> y) =  (abs (fst(wall_count y) - snd(wall_count x)))#(wall_list y)"
(*test exercises*)
lemma trivial2: "wall_list (basic e1) = []"
apply(auto)
done


lemma trivial3: "fst(wall_count (basic e3))- snd(wall_count (basic e1)) = 1"
apply(auto)
done

lemma trivial4: "wall_list ((basic e3)\<circ>(basic e1)\<circ>(basic e1)) = [1,0]"
apply(auto)
apply(simp add:abs_def)
apply(simp add:abs_def)
done
(*end of test exercises*)

primrec list_sum::"int list \<Rightarrow> int" 
where
"list_sum [] = 0"|
"list_sum (x#xs) = x+ list_sum xs"

(*diagram checks when a wall represents a knot diagram*)

typedef diagram = "{(x::walls).  (list_sum (wall_list x)+(abs(fst(wall_count x))
+ abs(snd(wall_count x)))) = 0}"
apply (rule_tac x = "prod (basic e2) (basic e3)" in exI)
apply(auto)
apply(simp add:abs_def)
done

definition a::diagram where "a \<equiv> Abs_diagram (basic e1)"
definition b::diagram where "b \<equiv> Abs_diagram (basic e2)"
definition c::diagram where "c \<equiv> Abs_diagram (basic e3)"
definition d::diagram where "d  \<equiv> Abs_diagram (basic e4)"
definition e::diagram where "e \<equiv> Abs_diagram (basic e5)"

(*tangle relations are being defined here. Tangle equivalence is broken into many equivalances each 
of which is defined as a disjunction of many functions.*)

(*tangle_uncross*)

definition tanglerel_uncross_positiveflip::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross_positiveflip x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e2\<otimes>w1)\<circ>(basic (z2\<otimes>e4\<otimes>e1\<otimes>w2))\<circ>(basic (z3\<otimes>e1\<otimes>e3\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e2\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>e4\<otimes>w2))\<circ>(basic (z3\<otimes>e3\<otimes>e1\<otimes>w3))\<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))) \<and> ((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_positivestraighten::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross_positivestraighten x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e2\<otimes>e1\<otimes>w1)\<circ>(basic (z2\<otimes>e1\<otimes>e4\<otimes>w2))\<circ>(basic (z3\<otimes>e3\<otimes>e1\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>w2))\<circ>(basic (z3\<otimes>e1\<otimes>w3))\<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))) \<and> ((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_negativeflip::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross_negativeflip x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e2\<otimes>w1)\<circ>(basic (z2\<otimes>e5\<otimes>e1\<otimes>w2))\<circ>(basic (z3\<otimes>e1\<otimes>e3\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e2\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>e5\<otimes>w2))\<circ>(basic (z3\<otimes>e3\<otimes>e1\<otimes>w3))\<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))) \<and> ((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_negativestraighten::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross_negativestraighten x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e2\<otimes>e1\<otimes>w1)\<circ>(basic (z2\<otimes>e1\<otimes>e5\<otimes>w2))\<circ>(basic (z3\<otimes>e3\<otimes>e1\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>w2))\<circ>(basic (z3\<otimes>e1\<otimes>w3))\<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))) \<and> ((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

(*right positive moves- these are redundant cases but need to be proved formally*)
definition tanglerel_uncross_rightpositiveflip::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross_rightpositiveflip x y \<equiv> (\<exists>y1.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (e1\<otimes>e2\<otimes>w1)\<circ>(basic (e4\<otimes>e1\<otimes>w2))\<circ>(basic (e1\<otimes>e3\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e2\<otimes>e1\<otimes>w1))\<circ>(basic (e1\<otimes>e4\<otimes>w2))\<circ>(basic (e3\<otimes>e1\<otimes>w3))\<circ>(y2)))\<and>((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_rightpositivestraighten::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross_rightpositivestraighten x y \<equiv> (\<exists>y1.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (e2\<otimes>e1\<otimes>w1)\<circ>(basic (e1\<otimes>e4\<otimes>w2))\<circ>(basic (e3\<otimes>e1\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>w1))\<circ>(basic (e1\<otimes>w2))\<circ>(basic (e1\<otimes>w3))\<circ>(y2)))\<and>((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_rightnegativeflip::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross_rightnegativeflip x y \<equiv> (\<exists>y1.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (e1\<otimes>e2\<otimes>w1)\<circ>(basic (e5\<otimes>e1\<otimes>w2))\<circ>(basic (e1\<otimes>e3\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e2\<otimes>e1\<otimes>w1))\<circ>(basic (e1\<otimes>e5\<otimes>w2))\<circ>(basic (e3\<otimes>e1\<otimes>w3))\<circ>(y2)))\<and>  ((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_rightnegativestraighten::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross_rightnegativestraighten x y \<equiv> (\<exists>y1.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (e2\<otimes>e1\<otimes>w1)\<circ>(basic (e1\<otimes>e5\<otimes>w2))\<circ>(basic (e3\<otimes>e1\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>w1))\<circ>(basic (e1\<otimes>w2))\<circ>(basic (e1\<otimes>w3))\<circ>(y2)))\<and> ((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

definition tanglerel_uncross_leftpositiveflip::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross_leftpositiveflip x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e2)\<circ>(basic (z2\<otimes>e4\<otimes>e1))\<circ>(basic (z3\<otimes>e1\<otimes>e3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e2\<otimes>e1))\<circ>(basic (z2\<otimes>e1\<otimes>e4))\<circ>(basic (z3\<otimes>e3\<otimes>e1))\<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))))"

definition tanglerel_uncross_leftpositivestraighten::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross_leftpositivestraighten x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e2\<otimes>e1)\<circ>(basic (z2\<otimes>e1\<otimes>e4))\<circ>(basic (z3\<otimes>e3\<otimes>e1))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1))\<circ>(basic (z2\<otimes>e1))\<circ>(basic (z3\<otimes>e1))\<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))))"

definition tanglerel_uncross_leftnegativeflip::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross_leftnegativeflip x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e2)\<circ>(basic (z2\<otimes>e5\<otimes>e1))\<circ>(basic (z3\<otimes>e1\<otimes>e3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic e1)\<circ>(basic e1)\<circ>(basic e1)\<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))))"

definition tanglerel_uncross_leftnegativestraighten::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross_leftnegativestraighten x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>y2.(x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e2\<otimes>e1)\<circ>(basic (z2\<otimes>e1\<otimes>e5))\<circ>(basic (z3\<otimes>e3\<otimes>e1))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1))\<circ>(basic (z2\<otimes>e1))\<circ>(basic (z3\<otimes>e1))\<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))))"

(*tangle_uncross definition*)
definition tanglerel_uncross::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_uncross x y \<equiv> 
((tanglerel_uncross_positiveflip x y)\<or>(tanglerel_uncross_positivestraighten x y)
\<or>(tanglerel_uncross_negativeflip x y)\<or>(tanglerel_uncross_negativestraighten x y)
\<or>(tanglerel_uncross_leftpositiveflip x y)\<or>(tanglerel_uncross_leftpositivestraighten x y)
\<or>(tanglerel_uncross_leftnegativeflip x y)\<or>(tanglerel_uncross_leftnegativestraighten x y)
\<or>(tanglerel_uncross_rightpositiveflip x y)\<or>(tanglerel_uncross_rightpositivestraighten x y)
\<or>(tanglerel_uncross_rightnegativeflip x y)\<or>(tanglerel_uncross_rightnegativestraighten x y))
"
(*tangle_uncross ends*)
(*tangle_pull begins*)

definition tanglerel_pull_posneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_posneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e4\<otimes>w1)\<circ>(basic (z2\<otimes>e5\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>e1\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2))))"


definition tanglerel_pull_negpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_negpos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e5\<otimes>w1)\<circ>(basic (z2\<otimes>e4\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>e1\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2))))"

(*above cases are redundant*)  
(*null*)
definition tanglerel_pull_nullposneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_nullposneg x y \<equiv>  \<exists>y1.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e4)\<circ>(basic (e5)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e1))\<circ>(basic (e1\<otimes>e1))\<circ>(y2))))"


definition tanglerel_pull_nullnegpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_nullnegpos x y \<equiv>  \<exists>y1.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e5)\<circ>(basic (e4)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e1))\<circ>(basic (e1\<otimes>e1))\<circ>(y2))))"

(*following cases are redundant, infact all of them can be deduced from the nullcases*)
(*bottom right*)
definition tanglerel_pull_botrightposneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_botrightposneg x y \<equiv>  \<exists>y1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e4\<otimes>w1)\<circ>(basic (z2\<otimes>e5\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)\<circ>(basic (e1\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>e1\<otimes>w2))\<circ>(y2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>((fst (count z2)) = 0))
"


definition tanglerel_pull_botrightnegpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_botrightnegpos x y \<equiv>  \<exists>y1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e5\<otimes>w1)\<circ>(basic (z2\<otimes>e4\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>e1\<otimes>w2))\<circ>(y2)))
\<and>((fst (count z2)) = 0)
\<and>((snd (count w1)) = (fst (count w2))))"

(*bottom left*)
definition tanglerel_pull_botleftposneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_botleftposneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e4)\<circ>(basic (z2\<otimes>e5\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1))\<circ>(basic (z2\<otimes>e1\<otimes>e1\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((fst (count w2)) = 0))"


definition tanglerel_pull_botleftnegpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_botleftnegpos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e5)\<circ>(basic (z2\<otimes>e4\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1))\<circ>(basic (z2\<otimes>e1\<otimes>e1\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((fst (count w2)) = 0))"
   
(*top right*)

definition tanglerel_pull_toprightposneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_toprightposneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e4\<otimes>w1)\<circ>(basic (e5\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1\<otimes>w1))\<circ>(basic (e1\<otimes>e1\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = 0)
\<and>((snd (count w1)) = (fst (count w2))))"


definition tanglerel_pull_toprightnegpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_toprightnegpos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e5\<otimes>w1)\<circ>(basic (e4\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1\<otimes>w1))\<circ>(basic (e1\<otimes>e1\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = 0)
\<and>((snd (count w1)) = (fst (count w2))))"
  
(*top left*)

definition tanglerel_pull_topleftposneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_topleftposneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e4\<otimes>w1)\<circ>(basic (z2\<otimes>e5)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>e1))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = 0))"


definition tanglerel_pull_topleftnegpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_topleftnegpos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e5\<otimes>w1)\<circ>(basic (z2\<otimes>e4)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>e1))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = 0))"


(*top*)
definition tanglerel_pull_topposneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_topposneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>w1.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e4\<otimes>w1)\<circ>(basic (e5)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1\<otimes>w1))\<circ>(basic (e1\<otimes>e1))\<circ>(y2)))
\<and>((snd (count z1)) = 0)
\<and>((snd (count w1)) = 0))"


definition tanglerel_pull_topnegpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_topnegpos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>w1.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e5\<otimes>w1)\<circ>(basic (e4)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1\<otimes>w1))\<circ>(basic (e1\<otimes>e1))\<circ>(y2)))
\<and>((snd (count z1)) = 0)
\<and>((snd (count w1)) = 0))"
  
(*bottom*)

definition tanglerel_pull_botposneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_botposneg x y \<equiv>  \<exists>y1.\<exists>z2.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e4)\<circ>(basic (z2\<otimes>e5\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e1))\<circ>(basic (z2\<otimes>e1\<otimes>e1\<otimes>w2))\<circ>(y2)))
\<and>(0 = (fst (count z2)))
\<and>(0 = (fst (count w2))))"


definition tanglerel_pull_botnegpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_botnegpos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>w1.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e5\<otimes>w1)\<circ>(basic (e4)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1\<otimes>w1))\<circ>(basic (e1\<otimes>e1))\<circ>(y2)))
\<and>((snd (count z1)) = 0)
\<and>((snd (count w1)) = 0))"

(*right*)
definition tanglerel_pull_rightposneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_rightposneg x y \<equiv>  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e4\<otimes>w1)\<circ>(basic (e5\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e1\<otimes>w1))\<circ>(basic (e1\<otimes>e1\<otimes>w2))\<circ>(y2)))
\<and>((snd (count w1)) = (fst (count w2))))"


definition tanglerel_pull_rightnegpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_rightnegpos x y \<equiv>  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e5\<otimes>w1)\<circ>(basic (e4\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e1\<otimes>w1))\<circ>(basic (e1\<otimes>e1\<otimes>w2))\<circ>(y2)))
\<and>((snd (count w1)) = (fst (count w2))))"

(*left*)
definition tanglerel_pull_leftposneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_leftposneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e4)\<circ>(basic (z2\<otimes>e5)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1))\<circ>(basic (z2\<otimes>e1\<otimes>e1))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2))))"

definition tanglerel_pull_leftnegpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_leftnegpos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e5)\<circ>(basic (z2\<otimes>e4)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1))\<circ>(basic (z2\<otimes>e1\<otimes>e1))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2))))"
  
  
(*leftcross*)

definition tanglerel_pull_leftcrossposneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_leftcrossposneg x y \<equiv>  \<exists>y1.\<exists>z2.\<exists>w1.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e4\<otimes>w1)\<circ>(basic (z2\<otimes>e5)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>e1))\<circ>(y2)))
\<and>(0 = (fst (count z2)))
\<and>((snd (count w1)) = 0))"


definition tanglerel_pull_leftcrossnegpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_leftcrossnegpos x y \<equiv>  \<exists>y1.\<exists>z2.\<exists>w1.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e5\<otimes>w1)\<circ>(basic (z2\<otimes>e4)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>e1))\<circ>(y2)))
\<and>(0 = (fst (count z2)))
\<and>((snd (count w1)) = 0))"
  
(*right cross*)

definition tanglerel_pull_rightcrossposneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_rightcrossposneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e4)\<circ>(basic (e5\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1))\<circ>(basic (e1\<otimes>e1\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = 0)
\<and>(0 = (fst (count w2))))"


definition tanglerel_pull_rightcrossnegpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_rightcrossnegpos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e5)\<circ>(basic (e4\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1))\<circ>(basic (e1\<otimes>e1\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = 0)
\<and>(0 = (fst (count w2))))"
  
(*null leftbottom- denoted lb*)

definition tanglerel_pull_lbposneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_lbposneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e4)\<circ>(basic (e5)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1))\<circ>(basic (e1\<otimes>e1))\<circ>(y2)))
\<and>((snd (count z1)) = 0))"


definition tanglerel_pull_lbnegpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_lbnegpos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e5)\<circ>(basic (e4)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1))\<circ>(basic (e1\<otimes>e1))\<circ>(y2)))
\<and>((snd (count z1)) = 0))"
  
(*null right bottom - denoted rb*)

definition tanglerel_pull_rbposneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_rbposneg x y \<equiv>  \<exists>y1.\<exists>w1.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e4\<otimes>w1)\<circ>(basic (e5)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e1\<otimes>w1))\<circ>(basic (e1\<otimes>e1))\<circ>(y2)))
\<and>((snd (count w1)) = 0))"


definition tanglerel_pull_rbnegpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_rbnegpos x y \<equiv>  \<exists>y1.\<exists>w1.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e5\<otimes>w1)\<circ>(basic (e4)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e1\<otimes>w1))\<circ>(basic (e1\<otimes>e1))\<circ>(y2)))
\<and>((snd (count w1)) = 0))"
  
(*null left top - denoted lt*)

definition tanglerel_pull_ltposneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_ltposneg x y \<equiv>  \<exists>y1.\<exists>z2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e4)\<circ>(basic (z2\<otimes>e5)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e1))\<circ>(basic (z2\<otimes>e1\<otimes>e1))\<circ>(y2)))
\<and>(0 = (fst (count z2))))"


definition tanglerel_pull_ltnegpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_ltnegpos x y \<equiv>  \<exists>y1.\<exists>z2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e5)\<circ>(basic (z2\<otimes>e4)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e1))\<circ>(basic (z2\<otimes>e1\<otimes>e1))\<circ>(y2)))
\<and>(0 = (fst (count z2))))"
  

(*null right top - denoted rt*)

definition tanglerel_pull_rtposneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_rtposneg x y \<equiv>  \<exists>y1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e4)\<circ>(basic (e5\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e1))\<circ>(basic (e1\<otimes>e1\<otimes>w2))\<circ>(y2)))
\<and>(0 = (fst (count w2))))"


definition tanglerel_pull_rtnegpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull_rtnegpos x y \<equiv>  \<exists>y1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e5)\<circ>(basic (e4\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e1))\<circ>(basic (e1\<otimes>e1\<otimes>w2))\<circ>(y2)))
\<and>(0 = (fst (count w2))))"
  

(*tanglerel_pull definition*)
definition tanglerel_pull::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_pull x y \<equiv> ((tanglerel_pull_posneg x y) \<or> (tanglerel_pull_negpos x y)
\<or> (tanglerel_pull_nullposneg x y) \<or> (tanglerel_pull_nullnegpos x y))
\<or> (tanglerel_pull_rightposneg x y) \<or> (tanglerel_pull_rightnegpos x y)
\<or> (tanglerel_pull_leftposneg x y) \<or> (tanglerel_pull_leftnegpos x y)
\<or>  (tanglerel_pull_toprightposneg x y) \<or> (tanglerel_pull_toprightnegpos x y)
\<or> (tanglerel_pull_topleftposneg x y) \<or> (tanglerel_pull_topleftnegpos x y)
\<or> (tanglerel_pull_botrightposneg x y) \<or> (tanglerel_pull_botrightnegpos x y)
\<or> (tanglerel_pull_botleftposneg x y) \<or> (tanglerel_pull_botleftnegpos x y)
\<or> (tanglerel_pull_rightcrossposneg x y) \<or> (tanglerel_pull_rightcrossnegpos x y)
\<or> (tanglerel_pull_leftcrossposneg x y) \<or> (tanglerel_pull_leftcrossnegpos x y)
\<or> (tanglerel_pull_rtposneg x y) \<or> (tanglerel_pull_rtnegpos x y)
\<or> (tanglerel_pull_ltposneg x y) \<or> (tanglerel_pull_ltnegpos x y)
\<or> (tanglerel_pull_rbposneg x y) \<or> (tanglerel_pull_rbnegpos x y)
\<or> (tanglerel_pull_lbposneg x y) \<or> (tanglerel_pull_lbnegpos x y)
"                              

(*tanglerel_pull ends*)    
(*tanglerel_straighten*)

definition tanglerel_straighten_topdown::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_straighten_topdown x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e2\<otimes>w1)\<circ>(basic (z2\<otimes>e3\<otimes>e1\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>w2))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
 \<and> ((snd (count w1)) = (fst (count w2)))"


definition tanglerel_straighten_downtop::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_straighten_downtop x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e2\<otimes>e1\<otimes>w1)\<circ>(basic (z2\<otimes>e1\<otimes>e3\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>w2))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
 \<and> ((snd (count w1)) = (fst (count w2)))"


definition tanglerel_straighten_righttopdown::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_straighten_righttopdown x y \<equiv>  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e1\<otimes>e2\<otimes>w1)\<circ>(basic (e3\<otimes>e1\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>w1))\<circ>(basic (e1\<otimes>w2))\<circ>(y2))))
 \<and> ((snd (count w1)) = (fst (count w2)))"


definition tanglerel_straighten_rightdowntop::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_straighten_rightdowntop x y \<equiv>  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e2\<otimes>e1\<otimes>w1)\<circ>(basic (e1\<otimes>e3\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>w1))\<circ>(basic (e1\<otimes>w2))\<circ>(y2))))
 \<and> ((snd (count w1)) = (fst (count w2)))"



definition tanglerel_straighten_lefttopdown::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_straighten_lefttopdown x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e3\<otimes>e1)\<circ>(basic (z2\<otimes>e1\<otimes>e2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1))\<circ>(basic (z2\<otimes>e1))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2))))"



definition tanglerel_straighten_leftdowntop::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_straighten_leftdowntop x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e2\<otimes>e1)\<circ>(basic (z2\<otimes>e1\<otimes>e3)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1))\<circ>(basic (z2\<otimes>e1))\<circ>(y2))))
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
\<circ>(basic (z1\<otimes>e4\<otimes>e1\<otimes>w1)\<circ>(basic (z2\<otimes>e1\<otimes>e4\<otimes>w2))\<circ>(basic (z3\<otimes>e4\<otimes>e1\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e4\<otimes>w1)\<circ>(basic (z2\<otimes>e4\<otimes>e1\<otimes>w2))\<circ>(basic (z3\<otimes>e1\<otimes>e4\<otimes>w3))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))\<and>((snd (count z2)) = (fst (count z3)))
 \<and> ((snd (count w1)) = (fst (count w2)))\<and>((snd (count w2)) = (fst (count w3))))"

definition tanglerel_swing_neg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_swing_neg x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e5\<otimes>e1\<otimes>w1)\<circ>(basic (z2\<otimes>e1\<otimes>e5\<otimes>w2))\<circ>(basic (z3\<otimes>e5\<otimes>e1\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e5\<otimes>w1)\<circ>(basic (z2\<otimes>e5\<otimes>e1\<otimes>w2))\<circ>(basic (z3\<otimes>e1\<otimes>e5\<otimes>w3))\<circ>(y2)))))
\<and>((snd (count z1)) = (fst (count z2)))\<and>((snd (count z2)) = (fst (count z3)))
 \<and> ((snd (count w1)) = (fst (count w2)))\<and>((snd (count w2)) = (fst (count w3)))"

definition tanglerel_swing_rightpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_swing_rightpos x y \<equiv> \<exists>y1.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e4\<otimes>e1\<otimes>w1)\<circ>(basic (e1\<otimes>e4\<otimes>w2))\<circ>(basic (e4\<otimes>e1\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e4\<otimes>w1)\<circ>(basic (e4\<otimes>e1\<otimes>w2))\<circ>(basic (e1\<otimes>e4\<otimes>w3))\<circ>(y2)))))
 \<and> ((snd (count w1)) = (fst (count w2)))\<and>((snd (count w2)) = (fst (count w3)))"



definition tanglerel_swing_rightneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_swing_rightneg x y \<equiv> \<exists>y1.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e5\<otimes>e1\<otimes>w1)\<circ>(basic (e1\<otimes>e5\<otimes>w2))\<circ>(basic (e5\<otimes>e1\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e5\<otimes>w1)\<circ>(basic (e5\<otimes>e1\<otimes>w2))\<circ>(basic (e1\<otimes>e5\<otimes>w3))\<circ>(y2)))))
 \<and> ((snd (count w1)) = (fst (count w2)))\<and>((snd (count w2)) = (fst (count w3)))"

definition tanglerel_swing_leftpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_swing_leftpos x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e4\<otimes>e1)\<circ>(basic (z2\<otimes>e1\<otimes>e4))\<circ>(basic (z3\<otimes>e4\<otimes>e1))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e4)\<circ>(basic (z2\<otimes>e4\<otimes>e1))\<circ>(basic (z3\<otimes>e1\<otimes>e4))\<circ>(y2)))))
\<and>((snd (count z1)) = (fst (count z2)))\<and>((snd (count z2)) = (fst (count z3)))"



definition tanglerel_swing_leftneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_swing_leftneg x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e5\<otimes>e1)\<circ>(basic (z2\<otimes>e1\<otimes>e5))\<circ>(basic (z3\<otimes>e5\<otimes>e1))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e5)\<circ>(basic (z2\<otimes>e5\<otimes>e1))\<circ>(basic (z3\<otimes>e1\<otimes>e5))\<circ>(y2)))))
\<and>((snd (count z1)) = (fst (count z2)))\<and>((snd (count z2)) = (fst (count z3)))"

(*swing definition*)

definition tanglerel_swing::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_swing x y \<equiv> ((tanglerel_swing_pos x y) \<or> (tanglerel_swing_neg x y)
\<or>(tanglerel_swing_rightpos x y) \<or> (tanglerel_swing_rightneg x y)
\<or>(tanglerel_swing_leftpos x y) \<or> (tanglerel_swing_leftneg x y))"

(*swing ends*)
(* rotate moves*)

definition tanglerel_rotate_toppos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate_toppos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e4\<otimes>w1))\<circ>(basic (z2\<otimes>e3\<otimes>e1\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e5\<otimes>e1\<otimes>w1)\<circ>(basic (z2\<otimes>e1\<otimes>e3\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2))))"


definition tanglerel_rotate_topneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate_topneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e5\<otimes>w1))\<circ>(basic (z2\<otimes>e3\<otimes>e1\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e4\<otimes>e1\<otimes>w1)\<circ>(basic (z2\<otimes>e1\<otimes>e3\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2))))"

definition tanglerel_rotate_downpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate_downpos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e3\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>e4\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e3\<otimes>w1)\<circ>(basic (z2\<otimes>e5\<otimes>e1\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2))))"


definition tanglerel_rotate_downneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate_downneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.
\<exists>w1.\<exists>w2.\<exists>y2.
((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e3\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>e5\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e3\<otimes>w1)\<circ>(basic (z2\<otimes>e4\<otimes>e1\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2))))"


definition tanglerel_rotate_righttoppos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate_righttoppos x y \<equiv>  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e4\<otimes>w1))\<circ>(basic (e3\<otimes>e1\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (e5\<otimes>e1\<otimes>w1)\<circ>(basic (e1\<otimes>e3\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count w1)) = (fst (count w2))))"


definition tanglerel_rotate_righttopneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate_righttopneg x y \<equiv>  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e5\<otimes>w1))\<circ>(basic (e3\<otimes>e1\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (e4\<otimes>e1\<otimes>w1)\<circ>(basic (e1\<otimes>e3\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count w1)) = (fst (count w2))))"

definition tanglerel_rotate_rightdownpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate_rightdownpos x y \<equiv>  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (e3\<otimes>e1\<otimes>w1))\<circ>(basic (e1\<otimes>e4\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (e1\<otimes>e3\<otimes>w1)\<circ>(basic (e5\<otimes>e1\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count w1)) = (fst (count w2))))"


definition tanglerel_rotate_rightdownneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate_rightdownneg x y \<equiv>  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.
((x = Abs_diagram ((y1)
\<circ>(basic (e3\<otimes>e1\<otimes>w1))\<circ>(basic (e1\<otimes>e5\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (e1\<otimes>e3\<otimes>w1)\<circ>(basic (e4\<otimes>e1\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count w1)) = (fst (count w2))))"


definition tanglerel_rotate_lefttoppos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate_lefttoppos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e4))\<circ>(basic (z2\<otimes>e3\<otimes>e1))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e5\<otimes>e1)\<circ>(basic (z2\<otimes>e1\<otimes>e3)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2))))"

definition tanglerel_rotate_lefttopneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate_lefttopneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e5))\<circ>(basic (z2\<otimes>e3\<otimes>e1))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e4\<otimes>e1)\<circ>(basic (z2\<otimes>e1\<otimes>e3)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2))))"

definition tanglerel_rotate_leftdownpos::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate_leftdownpos x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e3\<otimes>e1))\<circ>(basic (z2\<otimes>e1\<otimes>e4))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e3)\<circ>(basic (z2\<otimes>e5\<otimes>e1)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2))))"


definition tanglerel_rotate_leftdownneg::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate_leftdownneg x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>y2.
((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e3\<otimes>e1))\<circ>(basic (z2\<otimes>e1\<otimes>e5))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e3)\<circ>(basic (z2\<otimes>e4\<otimes>e1)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2))))"

(*rotate definition*)


definition tanglerel_rotate::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_rotate x y \<equiv> ((tanglerel_rotate_toppos x y) \<or> (tanglerel_rotate_topneg x y)
\<or> (tanglerel_rotate_downpos x y) \<or> (tanglerel_rotate_downneg x y)
\<or> (tanglerel_rotate_righttoppos x y) \<or> (tanglerel_rotate_righttopneg x y)
\<or> (tanglerel_rotate_rightdownpos x y) \<or> (tanglerel_rotate_rightdownneg x y)
\<or>(tanglerel_rotate_lefttoppos x y) \<or> (tanglerel_rotate_lefttopneg x y)
\<or> (tanglerel_rotate_leftdownpos x y) \<or> (tanglerel_rotate_leftdownneg x y))"

(*rotate ends*)
(*stranded operations begin*)

primrec strands::"block \<Rightarrow> bool"
where
"strands e1 = True"|
"strands e2 = False"|
"strands e3 = False"|
"strands e4 = False"|
"strands e5 = False"|
"strands (x\<otimes>y) = (if (x= e1) then (strands y) else (strands x)\<and>(strands y))"


primrec cup::"block \<Rightarrow> bool"
where
"cup e1 = False"|
"cup e2 = True"|
"cup e3 = False"|
"cup e4 = False"|
"cup e5 = False"|
"cup (x\<otimes>y) = (if (x= e2) then (cup y) else (cup x)\<and>(cup y))"


lemma trivial5: "strands (e1\<otimes>e2\<otimes>e1\<otimes>e1) = False" by auto



(*Compress -  Compress has two levels of equivalences. It is a composition of Compress_null, compbelow
and compabove. compbelow and compabove are further written as disjunction of many other relations.
Compbelow refers to when the bottom row is extended or compressed. Compabove*)

definition tanglerel_compress_null::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compress_null x y \<equiv>  \<exists>y2.\<exists>A.\<exists>B.((x = Abs_diagram
 ((A)\<circ>(basic B)\<circ>(y2)))\<and>(y = Abs_diagram ((A)\<circ>(y2)))
\<and> (strands B))"

(*compress below- abbreviated as compbelow*)
definition tanglerel_compbelow_down::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_down x y \<equiv>  \<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((basic (z1\<otimes>A\<otimes>w1))\<circ>(basic (z2\<otimes>B\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram (
(basic (z1\<otimes>w1)\<circ>(basic (z2\<otimes>A\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>(strands B))"


definition tanglerel_compbelow_center::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_center x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A\<otimes>w1))\<circ>(basic (z2\<otimes>B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1\<otimes>w1))\<circ>(basic (z2\<otimes>A\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>((fst (count A)) = 0)
\<and>(strands B))"

(*three at a time- botright*)
definition tanglerel_compbelow_botright::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_botright x y \<equiv> \<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.\<exists>A.\<exists>B.((x = Abs_diagram (
(basic (A\<otimes>w1))\<circ>(basic (z2\<otimes>B\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram (
(basic (w1)\<circ>(basic (z2\<otimes>A\<otimes>w2)))\<circ>(y2))))
\<and>(0 = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>(strands B))"


definition tanglerel_compbelow_botleft::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_botleft x y \<equiv>  \<exists>z1.\<exists>z2.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram (
(basic (z1)\<circ>(basic (z2\<otimes>A\<otimes>w2)))\<circ>(y2))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>(0 = (fst (count w2)))
\<and>(strands B))"


definition tanglerel_compbelow_centerbotright::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_centerbotright x y \<equiv> \<exists>y1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (z2\<otimes>B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (w1))\<circ>(basic (z2\<otimes>A\<otimes>w2))\<circ>(y2)))
\<and>(0 = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>((fst (count A)) = 0)
\<and>(strands B))"


definition tanglerel_compbelow_centerbotleft::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_centerbotleft x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1))\<circ>(basic (z2\<otimes>A\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>(0 = (fst (count w2)))
\<and>((fst (count A)) = 0)
\<and>(strands B))"


definition tanglerel_compbelow_centertopright::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_centertopright x y \<equiv> \<exists>y1.\<exists>z1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1\<otimes>w1))\<circ>(basic (A\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = 0)
\<and>((snd (count w1)) = (fst (count w2)))
\<and>((fst (count A)) = 0)
\<and>(strands B))"


definition tanglerel_compbelow_centertopleft::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_centertopleft x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A\<otimes>w1))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1\<otimes>w1))\<circ>(basic (z2\<otimes>A))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = 0)
\<and>((fst (count A)) = 0)
\<and>(strands B))"

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


definition tanglerel_compbelow_bottom::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_bottom x y \<equiv>  \<exists>z2.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((basic (A))\<circ>(basic (z2\<otimes>B\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram (
(basic (z2\<otimes>A\<otimes>w2))\<circ>(y2))))
\<and>(0 = (fst (count z2)))
\<and>(0 = (fst (count w2)))
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


definition tanglerel_compbelow_centerbottom::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_centerbottom x y \<equiv> \<exists>y1.\<exists>z2.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (A))\<circ>(basic (z2\<otimes>B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>(basic (z2\<otimes>A\<otimes>w2))\<circ>(y2)))
\<and>(0 = (fst (count z2)))
\<and>(0 = (fst (count w2)))
\<and>((fst (count A)) = 0)
\<and>(strands B))"


definition tanglerel_compbelow_centertop::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_centertop x y \<equiv> \<exists>y1.\<exists>z1.\<exists>w1.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A\<otimes>w1))\<circ>(basic (B))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1\<otimes>w1))\<circ>(basic (A))\<circ>(y2)))
\<and>((snd (count z1)) = 0)
\<and>((snd (count w1)) = 0)
\<and>((fst (count A)) = 0)
\<and>(strands B))"


definition tanglerel_compbelow_centerrightcross::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_centerrightcross x y \<equiv> \<exists>y1.\<exists>z1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1))\<circ>(basic (A\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = 0)
\<and>(0 = (fst (count w2)))
\<and>((fst (count A)) = 0)
\<and>(strands B))"


definition tanglerel_compbelow_centerleftcross::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_centerleftcross x y \<equiv> \<exists>y1.\<exists>z2.\<exists>w1.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (w1))\<circ>(basic (z2\<otimes>A))\<circ>(y2)))
\<and>(0 = (fst (count z2)))
\<and>((snd (count w1)) = 0)
\<and>((fst (count A)) = 0)
\<and>(strands B))"

(*one at a time- abbreviated notation is used here. For instance- lb-left bottom exists*)

definition tanglerel_compbelow_lt::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_lt x y \<equiv>  \<exists>z2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((basic (A))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> ((y = Abs_diagram (
(basic (z2\<otimes>A))\<circ>(y2))))
\<and>(0 = (fst (count z2)))
\<and>(strands B))"


definition tanglerel_compbelow_rt::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_rt x y \<equiv>  \<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((basic (A))\<circ>(basic (B\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram (
(basic (A\<otimes>w2))\<circ>(y2))))
\<and>(0 = (fst (count w2)))
\<and>(strands B))"

(*center abbreviated one at a time*)

definition tanglerel_compbelow_centerlb::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_centerlb x y \<equiv> \<exists>y1.\<exists>z1.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (B))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1))\<circ>(basic (A))\<circ>(y2)))
\<and>((snd (count z1)) = 0)
\<and>((fst (count A)) = 0)
\<and>(strands B))"


definition tanglerel_compbelow_centerrb::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_centerrb x y \<equiv> \<exists>y1.\<exists>w1.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (w1))\<circ>(basic (A))\<circ>(y2)))
\<and>((snd (count w1)) = 0)
\<and>((fst (count A)) = 0)
\<and>(strands B))"


definition tanglerel_compbelow_centerlt::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_centerlt x y \<equiv> \<exists>y1.\<exists>z2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (A))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z2\<otimes>A))\<circ>(y2)))
\<and>(0 = (fst (count z2)))
\<and>((fst (count A)) = 0)
\<and>(strands B))"


definition tanglerel_compbelow_centerrt::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow_centerrt x y \<equiv> \<exists>y1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (A))\<circ>(basic (B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>(basic (A\<otimes>w2))\<circ>(y2)))
\<and>(0 = (fst (count w2)))
\<and>((fst (count A)) = 0)
\<and>(strands B))"
(*comp below definition*)

(*compbelow definition*)
definition tanglerel_compbelow::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compbelow x y \<equiv> (tanglerel_compbelow_down x y) \<or> (tanglerel_compbelow_center x y) 
\<or> (tanglerel_compbelow_botright x y) \<or> (tanglerel_compbelow_botleft x y ) 
\<or> (tanglerel_compbelow_centerbotleft x y) \<or> (tanglerel_compbelow_centerbotright x y)
\<or> (tanglerel_compbelow_centertopright x y) \<or> (tanglerel_compbelow_centertopleft x y)
\<or> (tanglerel_compbelow_right x y) \<or> (tanglerel_compbelow_left x y) \<or> (tanglerel_compbelow_bottom x y)
\<or> (tanglerel_compbelow_centerleft x y) \<or> (tanglerel_compbelow_centerright x y)
\<or> (tanglerel_compbelow_centerbottom x y) \<or> (tanglerel_compbelow_centertop x y)
\<or>(tanglerel_compbelow_centerrightcross x y) \<or> (tanglerel_compbelow_centerleftcross x y)
\<or> (tanglerel_compbelow_lt x y) \<or> (tanglerel_compbelow_rt x y) 
\<or> (tanglerel_compbelow_centerlb x y) \<or> (tanglerel_compbelow_centerrb x y)
\<or> (tanglerel_compbelow_centerlt x y) \<or> (tanglerel_compbelow_centerrt x y)
"
(*comp above*)
definition tanglerel_compabove_up::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_up x y \<equiv>  \<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y1.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A\<otimes>w1))\<circ>(basic (z2\<otimes>B\<otimes>w2))))\<and> ((y = Abs_diagram ((y1)\<circ>
(basic (z1\<otimes>B\<otimes>w1)\<circ>(basic (z2\<otimes>w2))))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>(strands A))"


definition tanglerel_compabove_center::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_center x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A\<otimes>w1))\<circ>(basic (z2\<otimes>B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1\<otimes>B\<otimes>w1))\<circ>(basic (z2\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>((snd (count B)) = 0)
\<and>(strands A))"

(*three at a time*)
definition tanglerel_compabove_bottomright::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_bottomright x y \<equiv>  \<exists>z2.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y1.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (z2\<otimes>B\<otimes>w2))))\<and> ((y = Abs_diagram (
(basic (B\<otimes>w1)\<circ>(basic (z2\<otimes>w2))))))
\<and>(0 = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>(strands A))"


definition tanglerel_compabove_bottomleft::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_bottomleft x y \<equiv>  \<exists>z1.\<exists>z2.\<exists>w2.\<exists>A.\<exists>B.\<exists>y1.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B\<otimes>w2))))\<and> ((y = Abs_diagram (
(y1)\<circ>(basic (z1\<otimes>B)\<circ>(basic (z2\<otimes>w2))))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>(0 = (fst (count w2)))
\<and>(strands A))"


definition tanglerel_compabove_topright::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_topright x y \<equiv>  \<exists>z1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y1.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A\<otimes>w1))\<circ>(basic (B\<otimes>w2))))\<and> ((y = Abs_diagram (
(y1)\<circ>(basic (z1\<otimes>B\<otimes>w1)\<circ>(basic (w2))))))
\<and>((snd (count z1)) = 0)
\<and>((snd (count w1)) = (fst (count w2)))
\<and>(strands A))"


definition tanglerel_compabove_topleft::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_topleft x y \<equiv>  \<exists>z1.\<exists>z2.\<exists>w1.\<exists>A.\<exists>B.\<exists>y1.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A\<otimes>w1))\<circ>(basic (z2\<otimes>B))))\<and> ((y = Abs_diagram (
(y1)\<circ>(basic (z1\<otimes>B\<otimes>w1)\<circ>(basic (z2))))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = 0)
\<and>(strands A))"


definition tanglerel_compabove_centerbottomright::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_centerbottomright x y \<equiv> \<exists>y1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (z2\<otimes>B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (B\<otimes>w1))\<circ>(basic (z2\<otimes>w2))\<circ>(y2)))
\<and>(0 = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>((snd (count B)) = 0)
\<and>(strands A))"


definition tanglerel_compabove_centerbottomleft::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_centerbottomleft x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1\<otimes>B))\<circ>(basic (z2\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>(0 = (fst (count w2)))
\<and>((snd (count B)) = 0)
\<and>(strands A))"


definition tanglerel_compabove_centertopright::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_centertopright x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1\<otimes>B))\<circ>(basic (z2\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>(0 = (fst (count w2)))
\<and>((snd (count B)) = 0)
\<and>(strands A))"


definition tanglerel_compabove_centertopleft::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_centertopleft x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A\<otimes>w1))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1\<otimes>B\<otimes>w1))\<circ>(basic (z2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = 0)
\<and>((snd (count B)) = 0)
\<and>(strands A))"
(*two at a time*)

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
(y1)\<circ>(basic (z1\<otimes>B)\<circ>(basic (z2))))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>(strands A))"


definition tanglerel_compabove_top::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_top x y \<equiv>  \<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y1.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A\<otimes>w1))\<circ>(basic (B))))\<and> ((y = Abs_diagram (
(y1)\<circ>(basic (z1\<otimes>B\<otimes>w1)))))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>(strands A))"

(*two at a time-center*)

definition tanglerel_compabove_centerright::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_centerright x y \<equiv> \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (A\<otimes>w1))\<circ>(basic (w2))\<circ>(y2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>((snd (count B)) = 0)
\<and>(strands A))"

definition tanglerel_compabove_centerleft::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_centerleft x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1\<otimes>B))\<circ>(basic (z2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count B)) = 0)
\<and>(strands A))"


definition tanglerel_compabove_centertop::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_centertop x y \<equiv> \<exists>y1.\<exists>z1.\<exists>w1.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A\<otimes>w1))\<circ>(basic (B))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1\<otimes>B\<otimes>w1))\<circ>(y2)))
\<and>((snd (count z1)) = 0)
\<and>((snd (count w1)) = 0)
\<and>((snd (count B)) = 0)
\<and>(strands A))"


definition tanglerel_compabove_centerbottom::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_centerbottom x y \<equiv> \<exists>y1.\<exists>z2.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (A))\<circ>(basic (z2\<otimes>B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (B))\<circ>(basic (z2\<otimes>w2))\<circ>(y2)))
\<and>(0 = (fst (count z2)))
\<and>((fst (count w2)) = 0)
\<and>((snd (count B)) = 0)
\<and>(strands A))"


definition tanglerel_compabove_centerrightcross::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_centerrightcross x y \<equiv> \<exists>y1.\<exists>z2.\<exists>w1.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (B\<otimes>w1))\<circ>(basic (z2))\<circ>(y2)))
\<and>(0 = (fst (count z2)))
\<and>((snd (count w1)) = 0)
\<and>((snd (count B)) = 0)
\<and>(strands A))"

definition tanglerel_compabove_centerleftcross::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_centerleftcross x y \<equiv> \<exists>y1.\<exists>z1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1\<otimes>B))\<circ>(basic (w2))\<circ>(y2)))
\<and>((snd (count z1)) = 0)
\<and>(0 = (fst (count w2)))
\<and>((snd (count B)) = 0)
\<and>(strands A))"
(*one at a time- abbreviated notion- for instance lb- left bottom block is present*)

definition tanglerel_compabove_lb::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_lb x y \<equiv>  \<exists>z1.\<exists>A.\<exists>B.\<exists>y1.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (B))))\<and> (y = Abs_diagram 
((y1)\<circ>(basic (z1\<otimes>B))))
\<and>((snd (count z1)) = 0)
\<and>(strands A))"

definition tanglerel_compabove_rb::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_rb x y \<equiv>  \<exists>w1.\<exists>A.\<exists>B.\<exists>y1.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B))))\<and> ((y = Abs_diagram ((y1)\<circ>
(basic (B\<otimes>w1)))))
\<and>((snd (count w1)) = 0)
\<and>(strands A))"

(*center- on at a time*)

definition tanglerel_compabove_centerlb::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_centerlb x y \<equiv> \<exists>y1.\<exists>z1.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (B))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1\<otimes>B))\<circ>(y2)))
\<and>((snd (count z1)) = 0)
\<and>((snd (count B)) = 0)
\<and>(strands A))"


definition tanglerel_compabove_centerrb::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_centerrb x y \<equiv> \<exists>y1.\<exists>w1.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (B\<otimes>w1))\<circ>(y2)))
\<and>((snd (count w1)) = 0)
\<and>((snd (count B)) = 0)
\<and>(strands A))"


definition tanglerel_compabove_centerlt::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_centerlt x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A\<otimes>w1))\<circ>(basic (z2\<otimes>B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (z1\<otimes>B\<otimes>w1))\<circ>(basic (z2\<otimes>w2))\<circ>(y2)))
\<and>((snd (count z1)) = (fst (count z2)))
\<and>((snd (count w1)) = (fst (count w2)))
\<and>((snd (count B)) = 0)
\<and>(strands A))"



definition tanglerel_compabove_centerrt::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove_centerrt x y \<equiv> \<exists>y1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (A))\<circ>(basic (B\<otimes>w2))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)\<circ>
(basic (B))\<circ>(basic (w2))\<circ>(y2)))
\<and>((fst (count w2)) = 0)
\<and>((snd (count B)) = 0)
\<and>(strands A))"

(*compabove definition*)

(*compbelow definition*)
definition tanglerel_compabove::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_compabove x y \<equiv> (tanglerel_compabove_up x y)\<or>(tanglerel_compabove_center x y) 
\<or> (tanglerel_compabove_bottomright x y) \<or> (tanglerel_compabove_bottomleft x y ) 
\<or> (tanglerel_compabove_topright x y) \<or> (tanglerel_compabove_topleft x y) 
\<or> (tanglerel_compabove_centerbottomleft x y) \<or> (tanglerel_compabove_centerbottomright x y)
\<or> (tanglerel_compabove_centertopright x y) \<or> (tanglerel_compabove_centertopleft x y)
\<or> (tanglerel_compabove_right x y) \<or> (tanglerel_compabove_left x y) \<or> (tanglerel_compabove_top x y)
\<or> (tanglerel_compabove_centerleft x y) \<or> (tanglerel_compabove_centerright x y)
\<or> (tanglerel_compabove_centerbottom x y) \<or> (tanglerel_compabove_centertop x y)
\<or>(tanglerel_compabove_centerrightcross x y) \<or> (tanglerel_compabove_centerleftcross x y)
\<or> (tanglerel_compabove_lb x y) \<or> (tanglerel_compabove_rb x y) 
\<or> (tanglerel_compabove_centerlb x y) \<or> (tanglerel_compabove_centerrb x y)
\<or> (tanglerel_compabove_centerlt x y) \<or> (tanglerel_compabove_centerrt x y)"

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
(* lemmas for proving that equivalence is well defined*)
lemma tanglerel_symp: "symp tanglerel" unfolding tanglerel_def symp_def by auto

(*find_theorems"rtranclp"*)
 
definition tanglerel_equiv::"diagram\<Rightarrow>diagram\<Rightarrow>bool"
where
"(tanglerel_equiv) = (tanglerel)^**" 
 
lemma reflective: "tanglerel_equiv x x" unfolding tanglerel_equiv_def by simp

lemma tangle_symmetry:"symp tanglerel_equiv" using tanglerel_symp symmetry3 
by (metis (full_types) tanglerel_equiv_def)

(*tangles upto equivalence are well defined*)
(*Tangle- Definition and the proof of being well defined*)

quotient_type Tangle = "diagram" / "tanglerel_equiv"
 morphisms Rep_tangles Abs_tangles
proof (rule equivpI)
show "reflp tanglerel_equiv" unfolding reflp_def reflective by (metis reflective)
show "symp tanglerel_equiv" using tangle_symmetry by auto
show "transp tanglerel_equiv" unfolding transp_def tanglerel_equiv_def rtranclp_trans by auto  
qed

(*links are well defined upto reidemeister moves-proof ends*)









 







