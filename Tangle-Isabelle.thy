theory Tangle-Isabelle
imports Datatype Main tangle_relation
begin

datatype block = e1
                |e2
                |e3
                |e4
                |e5
                |Cons block block              (infixr "\<otimes>" 65)

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

primrec list_sum::"int list \<Rightarrow> int" where
"list_sum [] = 0"|
"list_sum (x#xs) = x+ list_sum xs"


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


definition tanglerel_one::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_one x y \<equiv> (\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.( x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e2\<otimes>w1)\<circ>(basic (z2\<otimes>e4\<otimes>e1\<otimes>w2))\<circ>(basic (z3\<otimes>e1\<otimes>e3\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e2\<otimes>e1\<otimes>w1)\<circ>(basic (z2\<otimes>e1\<otimes>e4\<otimes>w2))\<circ>(basic (z3\<otimes>e3\<otimes>e1\<otimes>w3))\<circ>(y2)))) )
"

definition tanglerel_two::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_two x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e4\<otimes>w1)\<circ>(basic (z2\<otimes>e5\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e1\<otimes>w1))\<circ>(basic (z3\<otimes>e1\<otimes>e1\<otimes>w3))\<circ>(y2))))"

definition tanglerel_three::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_three x y \<equiv> \<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e4\<otimes>e1\<otimes>w1)\<circ>(basic (z2\<otimes>e1\<otimes>e4\<otimes>w2))\<circ>(basic (z3\<otimes>e4\<otimes>e1\<otimes>w3))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e4\<otimes>w1)\<circ>(basic (z2\<otimes>e4\<otimes>e1\<otimes>w2))\<circ>(basic (z3\<otimes>e1\<otimes>e4\<otimes>w3))\<circ>(y2)))))"

definition tanglerel_four::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_four x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e3\<otimes>e1\<otimes>w1)\<circ>(basic (z2\<otimes>e1\<otimes>e2\<otimes>w2)))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>w2))\<circ>(y2))))"

definition tanglerel_five::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_five x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>w1))\<circ>(basic (z2\<otimes>e1\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e2\<otimes>w1)\<circ>(basic (z2\<otimes>e3\<otimes>e1\<otimes>w2)))\<circ>(y2)))))"

definition tanglerel_six::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_six x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>w1.\<exists>w2.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (z1\<otimes>e1\<otimes>e4\<otimes>w1))\<circ>(basic (z2\<otimes>e2\<otimes>e1\<otimes>w2))\<circ>(y2)))\<and> ((y = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>e4\<otimes>e1\<otimes>w1)\<circ>(basic (z2\<otimes>e1\<otimes>e2\<otimes>w2)))\<circ>(y2)))))"

primrec strands::"block \<Rightarrow> bool"
where
"strands e1 = True"|
"strands e2 = False"|
"strands e3 = False"|
"strands e4 = False"|
"strands e5 = False"|
"strands (x\<otimes>y) = (if (x= e1) then (strands y) else (strands x)\<and>(strands y))"

lemma trivial5: "strands (e1\<otimes>e2\<otimes>e1\<otimes>e1) = False" by auto

definition tanglerel_seven::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_seven x y \<equiv>  \<exists>y1.\<exists>z.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z))\<circ>(y2)))\<and>(strands z)\<and>((y = Abs_diagram ((y1)\<circ>(y2)))))"

definition tanglerel_eight::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_eight x y \<equiv>  \<exists>y1.\<exists>z.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(y2)))\<and>((y = Abs_diagram ((y1)\<circ>(basic z)\<circ>(y2))))\<and>(strands z) )"

lemma eight:"tanglerel_eight (Abs_diagram ((basic e4)\<circ>(basic e4))) (Abs_diagram ((basic e4)
\<circ>(basic (e1\<otimes>e1))\<circ>(basic e4)))" 
proof-
let ?x1 = "Abs_diagram ((basic e4)\<circ>(basic e4))"
let ?x2 = "Abs_diagram ((basic e4)\<circ>(basic (e1\<otimes>e1))\<circ>(basic e4))"
let ?y1 = "(basic e4)"
let ?y2 = "(basic e4)"
let ?z =  "(e1\<otimes>e1)"
have "strands ?z" by simp 
have "(?x1 =  Abs_diagram
 ((?y1)\<circ>(?y2)))\<and>((?x2 = Abs_diagram ((?y1)\<circ>(basic ?z)\<circ>(?y2))))\<and>(strands ?z)" by simp
then show ?thesis using tanglerel_eight_def by force
qed

definition tanglerel_nine::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_nine x y \<equiv>  \<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.((x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>w1))\<circ>(basic (z2\<otimes>w2))\<circ>(y2)))\<and>
(y = Abs_diagram
 ((y1)\<circ>(basic (z3\<otimes>w2))\<circ>(basic (z1\<otimes>w3))\<circ>(y2)))\<and>(strands w1)\<and>(strands z2)\<and>(strands z3)\<and>(strands w3)
\<and>((snd (count z1)) = (fst (count z2))) \<and>((snd (count w1)) = (fst (count w2)))
\<and>((snd (count z3)) = (fst (count z1))) \<and>((fst (count w3)) = (snd (count w2))))"


definition tanglerel_11::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_11 x y \<equiv> (\<exists>y1.\<exists>y2.( x = Abs_diagram ((y1)
\<circ>(basic (e1\<otimes>e3)\<circ>(basic (e4\<otimes>e1))\<circ>(basic (e1\<otimes>e2))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e3\<otimes>e1))\<circ>(basic (e1\<otimes>e4))\<circ>(basic (e2\<otimes>e1))\<circ>(y2))))
"

definition tanglerel_12::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_12 x y \<equiv>  \<exists>y1.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic e4)\<circ>(basic e5)\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e1))\<circ>(basic (e1\<otimes>e1))\<circ>(y2))))"

definition tanglerel_13::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_13 x y \<equiv> \<exists>y1.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e4\<otimes>e1)\<circ>(basic (e1\<otimes>e4))\<circ>(basic (e4\<otimes>e1))\<circ>(y2))))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e4)\<circ>(basic (e4\<otimes>e1))\<circ>(basic (e1\<otimes>e4))\<circ>(y2)))))"

definition tanglerel_14::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_14 x y \<equiv>  \<exists>y1.\<exists>y2.((x = Abs_diagram ((y1)
\<circ>(basic (e3\<otimes>e1))\<circ>(basic (e1\<otimes>e2))\<circ>(y2)))\<and>(y = Abs_diagram
 ((y1)
\<circ>(basic (e1))\<circ>(basic e1)\<circ>(y2))))"

definition tanglerel_15::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_15 x y \<equiv>  \<exists>y1.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (e1))\<circ>(basic (e1))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)
\<circ>(basic (e1\<otimes>e2))\<circ>(basic (e3\<otimes>e1))\<circ>(y2))))"

definition tanglerel_16::"diagram \<Rightarrow> diagram \<Rightarrow> bool"
where
"tanglerel_16 x y \<equiv>  \<exists>y1.\<exists>y2.((x = Abs_diagram
 ((y1)
\<circ>(basic (e1\<otimes>e4))\<circ>(basic (e2\<otimes>e1))\<circ>(y2)))\<and> (y = Abs_diagram ((y1)
\<circ>(basic (e4\<otimes>e1))\<circ>(basic (e1\<otimes>e2))\<circ>(y2))))"

definition tanglerel::"diagram =>diagram\<Rightarrow>bool"
where
"tanglerel x y = ((tanglerel_one x y) \<or> (tanglerel_two x y) \<or> (tanglerel_three x y) 
\<or>(tanglerel_four x y)\<or>(tanglerel_five x y) \<or> (tanglerel_six x y) \<or> (tanglerel_seven x y) 
\<or> (tanglerel_eight x y)\<or>(tanglerel_nine x y)
\<or>(tanglerel_11 x y) \<or> (tanglerel_12 x y) \<or> (tanglerel_13 x y) \<or>(tanglerel_14 x y)
\<or>(tanglerel_15 x y)\<or>(tanglerel_16 x y)
\<or>(tanglerel_one y x) \<or> (tanglerel_two y x) 
\<or> (tanglerel_three y x) \<or>(tanglerel_four y x)\<or>(tanglerel_five y x) \<or> (tanglerel_six y x) \<or> (tanglerel_seven y x) 
\<or> (tanglerel_eight y x)\<or>(tanglerel_nine y x)
\<or>(tanglerel_11 y x) \<or> (tanglerel_12 y x) \<or> (tanglerel_13 y x) \<or>(tanglerel_14 y x)
\<or>(tanglerel_15 y x)\<or>(tanglerel_16 y x))"

lemma tanglerel_symp: "symp tanglerel" unfolding tanglerel_def symp_def by auto

find_theorems"rtranclp"
 
definition tanglerel_equiv::"diagram\<Rightarrow>diagram\<Rightarrow>bool"
where
"(tanglerel_equiv) = (tanglerel)^**" 
 
lemma reflective: "tanglerel_equiv x x" unfolding tanglerel_equiv_def by simp

lemma tangle_symmetry:"symp tanglerel_equiv" using tanglerel_symp symmetry3 
by (metis (full_types) tanglerel_equiv_def)

(*lemma implication_and:"(A\<longrightarrow> B\<longrightarrow> C) = ((A\<and>B)\<longrightarrow>C)" by auto

lemma connective_commutativity:"((A\<or>B)\<and>(C\<or>D)) = ((A\<and>C)\<or>(A\<and>D)\<or>(B\<and>C)\<or>(B\<and>D))" by auto 
*)
quotient_type Tangle = "diagram" / "tanglerel_equiv"
 morphisms Rep_tangles Abs_tangles
proof (rule equivpI)
show "reflp tanglerel_equiv" unfolding reflp_def reflective by (metis reflective)
show "symp tanglerel_equiv" using tangle_symmetry by auto
show "transp tanglerel_equiv" unfolding transp_def tanglerel_equiv_def rtranclp_trans by auto  
qed

lemma test2: assumes "a =  Abs_diagram ((basic e3)\<circ>(basic (e1\<otimes>e1))\<circ> (basic e2))" 
and "b = Abs_diagram  ((basic e3)\<circ>(basic e2))"
shows "(Abs_tangles a)= (Abs_tangles b)" using tanglerel_equiv_def tanglerel_def tanglerel_nine_def
proof-
have  "strands (e1\<otimes>e1)" using strands_def by auto
then have " \<exists>y1.\<exists>z.\<exists>y2.
((b = Abs_diagram ((y1)\<circ>(y2)))
\<and>((a = Abs_diagram ((y1)\<circ>(basic z)\<circ>(y2))))\<and>(strands z) )" 
using assms by force
then have "tanglerel_eight b a" using tanglerel_eight_def by auto
then have "tanglerel a b" using tanglerel_def by auto
then have "tanglerel^** a b" using r_into_rtranclp by auto
then have "tanglerel_equiv a b" using tanglerel_equiv_def by auto
thus ?thesis using Tangle.abs_eq_iff   by auto
qed

primrec cusp_detector::"block \<Rightarrow> bool"
where
" cusp_detector e1 = False"|
" cusp_detector e2 = False"|
" cusp_detector e3  = True"|
" cusp_detector e4 = False"|
" cusp_detector e5 = False"|
" cusp_detector (x\<otimes>y) = (if (x= e3) then (cusp_detector y) else (cusp_detector x)\<and>(cusp_detector y))"



(*Some changes are being made here, will update the code soon) 


