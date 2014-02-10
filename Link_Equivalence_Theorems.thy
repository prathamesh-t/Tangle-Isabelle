theory Link_Equivalence_Theorems
imports Tangles
begin

lemma linkrel_trans: assumes "linkrel_equiv x y" and "linkrel_equiv y z"
shows "linkrel_equiv x z"
using rtranclp_trans linkrel_equiv_def  by (metis (full_types) assms(1) assms(2))


text{* We prove a set of theorems which prove equivalence of certain class of link diagrams. These
equivalences are useful in practise to prove equivalence of two given link diagrams. These theorems
also enable to understand why the defined relations are sufficient*}

text {* The following function constructs a block of n-vertical strands for a given n. *}

primrec make_vert_block:: "nat \<Rightarrow> block"
where
"make_vert_block 0 = (cement vert)"
|"make_vert_block (Suc n) = vert#(make_vert_block n)"

(*proof that the make_vert_block function constructs a block with vertical strands*)
lemma strand_make_vert_block: " strands (make_vert_block n)" 
  apply(induct_tac n)
  apply(auto)
  done


lemma make_vert_induct: "(make_vert_block (n+1)) = vert#(make_vert_block n)" by auto

(*make_vert_block of n+1 strings in terms expressed as a product of make_vert_block n strings and 
cement vert*)
lemma make_vert_induct_left: "(make_vert_block (n+1)) = (cement vert)\<otimes>(make_vert_block n)" 
                   using make_vert_induct append_blocks_Nil by metis


lemma make_vert_induct_right: "(make_vert_block (n+1)) = (make_vert_block n)\<otimes>(cement vert)" 
  apply(induct_tac n)
  apply(auto)
  apply (metis Tangles.append_blocks.append_blocks_Nil leftright_associativity)
  done

(*number of incoming strings of the block constructed by (make_vert_block n) is n+1*) 
lemma make_vert_block_fstequality:"(fst (count (make_vert_block n))) = (int n)+1" 
  apply (induct_tac n)
  apply(auto)
  done


lemma int_nat_condition:"(x>y) \<Longrightarrow> int (nat (x + - y)) - z = x + -y - z"                    
  by auto


(*number of outgoing strings of the block constructed by (make_vert_block n) is n+1*) 
lemma make_vert_block_sndequality:"(snd (count (make_vert_block n))) = (int n)+1" 
  apply (induct_tac n)
  apply(auto)
  done


(*number of incoming strings and outgoing strands of the block constructed by (make_vert_block n) 
are equal*) 
lemma make_vert_block_fstsndequality:
"(fst (count (make_vert_block n))) = (snd (count (make_vert_block n)))" 
   apply (induct_tac n)
   apply(auto)
   done

lemma nat_int:" ((int n)\<ge> 0)" by auto


(*number of incoming strings of the block constructed by (make_vert_block n) is always positive*) 
lemma make_vert_blocks_positiveblock_length:"(fst (count (make_vert_block n)))>0" 
  using  nat_int make_vert_block_fstequality
  by auto




(*non seperating block refers to a block which has outgoing strands. In other words, it is not 
block which seperates two disjoint components of a link*)



definition non_seperating_block::"block \<Rightarrow> bool"
where
"non_seperating_block x \<equiv> (snd (count x)>1) "


text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1 \<circ>z1), where y1 is a 
block with outgoing strands, the following theorem proves that it is equivalent to the link 
diagram obtained by adding two blocks of vertical strands above y1*}

theorem linkrel_doublecompress_top: 
assumes "non_seperating_block y1" 
  and "(z4 = make_vert_block (nat ((snd (count y1)) + (-2))+1))"
shows "linkrel_equiv (Abs_diagram (x1 \<circ> basic y1 \<circ> basic z4\<circ> basic z4\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 

proof-
 let ?k = " (nat ((snd (count y1))+ (-2) ))" 
 let ?x2 = "x1 \<circ> (basic y1)"
 have 1: " (z4 = make_vert_block (?k+1))" using assms by auto
 also have "((snd (count y1))+(-1))>0" 
         using assms non_seperating_block_def by auto
 then have 2:"((snd (count y1))+(-2))\<ge>0" using assms by auto
 have  3:"strands z4" using 1 strand_make_vert_block by auto
 have  4:"snd (wall_count ?x2) = snd (wall_count (basic y1))" 
           using wall_count_compose by auto
 have  "... = snd (count y1)" using wall_count_compose by auto
 then have 5:"snd (wall_count ?x2) > 0"
            using  assms less_trans 4  zero_less_one non_seperating_block_def by auto
 then have 6: "fst (count (z4)) = fst (count (make_vert_block (?k+1)))"  
            using 1 make_vert_block_fstequality by auto
 have  "fst (count (make_vert_block (?k+1))) = int(?k+1)+1"  
            using make_vert_block_fstequality by auto
 then have 7: "fst (count (z4)) =  int(?k)+2" 
           using 6  by auto
 have  "int (nat (snd (count y1) + -2)) = (snd (count y1)) + -2" 
           using int_nat_eq 2  by auto
 then have  "snd (count y1) = int(?k)+2" 
           by auto
 then have  "fst (count (z4)) = (snd (count y1))" 
           using 7 by auto
 have  
"(linkrel_compress_null ((Abs_diagram (?x2\<circ>(basic z4)\<circ>z1))) (Abs_diagram (?x2\<circ>z1)))" 
           using linkrel_compress_null_def 3 5  by metis
 then have 8: 
 "(linkrel_equiv ((Abs_diagram (?x2\<circ>(basic z4)\<circ>z1))) (Abs_diagram (?x2\<circ>z1)))" 
           using r_into_rtranclp  linkrel_equiv_def linkrel_def  
           linkrel_compress_def by (metis)
 have
 "(linkrel_compress_null ((Abs_diagram ((?x2 \<circ> basic z4)\<circ>(basic z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ> basic z4)\<circ>z1)))" 
               using linkrel_compress_null_def  3  5 compose_leftassociativity
                    by (metis)
 then have 
 "(linkrel_equiv ((Abs_diagram ((?x2 \<circ> basic z4)\<circ>(basic z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ> basic z4)\<circ>z1)))" 
               using linkrel_compress_def linkrel_def linkrel_equiv_def
               r_into_rtranclp   
                    by (metis)
 then have 
"linkrel_equiv ((Abs_diagram ((?x2 \<circ> basic z4)\<circ>(basic z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ>z1)))" 
               using linkrel_equiv_def rtranclp_trans 8
               compose_leftassociativity
                            by (metis) 
 then have 
 "linkrel_equiv (Abs_diagram (x1 \<circ> basic y1 \<circ> basic z4\<circ>basic z4\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using compose_leftassociativity  
               by auto
 then show ?thesis by simp
 qed

text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1 \<circ>z1), where y1 is a 
block with outgoing strands, the following theorem proves that it is equivalent to the link 
diagram obtained by adding two blocks of vertical strands below y1*}

theorem linkrel_doublecompress_below:
 assumes "(snd (wall_count x1))>1" 
 and "(z4 = make_vert_block (nat ((snd (wall_count x1)) + (-2))+1))"
 shows "linkrel_equiv (Abs_diagram (x1 \<circ> basic z4\<circ>basic z4 \<circ> basic y1\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))" 
 proof-    
 let ?k = " (nat ((snd (wall_count x1))+ (-2) ))" 
 have 1: " (z4 = make_vert_block (?k+1))" using assms by auto
 then have 2: "strands z4" using strand_make_vert_block by auto
 let ?x2 = "x1 \<circ> (basic y1)"
 have 3:"((snd (wall_count x1))+(-2))\<ge>0" using assms by auto
 also have 4: "fst (count (z4)) = fst (count (make_vert_block (?k+1)))"  
            using 1 make_vert_block_fstequality
            by auto
 also have 5: "fst (count (make_vert_block (?k+1))) = int(?k+1)+1"  
            using make_vert_block_fstequality
            by auto
 then have 6:"fst (count (z4)) =  int(?k)+2" 
           using 4 5 
           by auto
 have  "int (nat (snd (wall_count x1) + -2)) = (snd (wall_count x1)) + -2" 
           using 3 int_nat_eq 
           by auto
 then have  "snd (wall_count x1) = int(?k)+2" 
                by auto
 then have  7:"fst (count (z4)) = (snd (wall_count x1))" 
           using 6 
           by auto
  also have 
 "(linkrel_compress_null ((Abs_diagram (x1\<circ>(basic z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1)))" 
            using linkrel_compress_null_def 2   1 
           comm_semiring_1_class.normalizing_semiring_rules(24) make_vert_block_fstequality 
           monoid_add_class.add.left_neutral of_nat_Suc zless_iff_Suc_zadd 7 by (metis)
 then have "(linkrel ((Abs_diagram (x1\<circ>(basic z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1)))" 
          unfolding linkrel_def linkrel_compress_def by auto
 then have 8:"(linkrel_equiv ((Abs_diagram (x1\<circ>(basic z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1)))" 
          unfolding linkrel_equiv_def by auto
 let ?z2 = "((basic z4)\<circ>(basic y1)\<circ>z1)"
 have 
 "(linkrel_compress_null (Abs_diagram (x1 \<circ> (basic z4)\<circ>(?z2)))
                           (Abs_diagram (x1\<circ>(?z2))))"
               using linkrel_compress_null_def  1
                comm_semiring_1_class.normalizing_semiring_rules(24) 
               int_one_le_iff_zero_less make_vert_block_fstequality 2 
                zle_iff_zadd 7
               by metis
 then have 
 "linkrel_equiv (Abs_diagram (x1 \<circ> (basic z4)\<circ>(?z2))) 
                            (Abs_diagram (x1 \<circ> (?z2)))" 
               using linkrel_equiv_def linkrel_compress_def r_into_rtranclp linkrel_def
                        by (metis (full_types) )
 then  have 
 "linkrel_equiv (Abs_diagram (x1 \<circ> basic z4\<circ>basic z4 \<circ> basic y1\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> (basic z4)\<circ>(basic y1)\<circ>z1))" 
               using compose_leftassociativity
               by auto
 then have 
 "linkrel_equiv (Abs_diagram (x1 \<circ> basic z4\<circ>basic z4 \<circ> basic y1\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))" 
               using compose_leftassociativity rtranclp_trans 8  linkrel_trans by metis              
 then show ?thesis  by simp
 qed

(*metaequivalence moves*)

text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1 \<circ>z1), where y1 is a 
block with outgoing strands, the following theorem proves that it is equivalent to a link 
diagram in which there exists a block appended to the left of y1 *}

theorem metaequivalence_left: 
 assumes "non_seperating_block y1" 
(*y1 has outgoing strands*)
 and  "w4 = make_vert_block  (nat ((snd (count y1)) + (-2)))"
(*w4 is the block with only vert strands with a strand less than y1*) 
 shows "linkrel_equiv 
 (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
             (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
(*every diagram is equivalent to the diagram obtained by stretching it and pulling a string below 
on the left of the stretched part*)   
proof-
(* proof is broken into three steps- the first step involves stretching the strand, the second step
involves pulling a strand below. The third step involves combining the first two steps*)
 let ?x2 = "x1 \<circ> (basic y1)"
 let ?z4 = "make_vert_block (nat ((snd (count y1)) + (-2))+1)"                                                                                           
 let ?k = " (nat ((snd (count y1))+ (-2) ))" 
(*Step 1 tells us that the diagram that the wall x1 \<circ> basic y1 \<circ> z1 gives rise to, is equivalent to 
the diagram obtained by stretching the diagram above the block y1*)
 have step1: 
"linkrel_equiv (Abs_diagram (x1 \<circ> basic y1 \<circ> basic ?z4\<circ>basic ?z4\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using compose_leftassociativity linkrel_doublecompress_top assms 
               non_seperating_block_def by auto
 (*Step 2 tells us that the diagram obtained above by stretching is equivalent to the diagram 
obtained by perturbing it a bit as to induce a cup and a cap on the left portion of the diagram*)
 have step2: "linkrel_equiv (Abs_diagram (x1\<circ>basic y1\<circ>(basic ((cement cup)\<otimes>?z4))
                                          \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1)) 
              (Abs_diagram (x1\<circ>basic y1 \<circ>(basic ?z4)\<circ>(basic (?z4))\<circ>z1))"
 proof-
  {
     have 1: "w4 = (make_vert_block ?k)" using assms by auto
     moreover have 2: 
              "(make_vert_block (?k+1)) = ((cement vert)\<otimes>(make_vert_block ?k))" by simp
     have "?z4 = (cement vert)\<otimes>(make_vert_block ?k)" by auto
     then have  
               "(Abs_diagram (?x2 \<circ> (basic ?z4) \<circ>(basic ?z4)\<circ>z1)) =
                (Abs_diagram (?x2  \<circ> (basic ((cement vert)\<otimes>w4))\<circ> (basic ((cement vert) \<otimes>w4))\<circ>z1))" 
                        using 1  by auto
     have 3:"(snd (count w4)) = (fst (count w4))" 
               using make_vert_block_fstsndequality 1 by auto
     let ?x = "(Abs_diagram (?x2 \<circ>(basic ((cement cup)\<otimes>(cement vert)\<otimes>w4))
                        \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"
     let ?y = "(Abs_diagram (?x2 \<circ>(basic ((cement vert)\<otimes>w4))\<circ>(basic ((cement vert)\<otimes>w4))\<circ>z1))"
     have
       "\<exists>y1.\<exists>y2.\<exists>w1.\<exists>w2.
        (?x = Abs_diagram (y1 \<circ> (basic ((cement cup) \<otimes> (cement vert) \<otimes> w1)) 
                  \<circ> (basic ((cement vert) \<otimes> (cement cap) \<otimes> w2)) \<circ> y2))"
              using exI by auto
     then have  
       "(\<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.
        ((?x = Abs_diagram ((y1)\<circ>(basic ((cement cup)\<otimes>(cement vert)\<otimes>w1)
                           \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w2)))\<circ>(y2)))
         \<and>(?y = Abs_diagram ((y1)\<circ>(basic ((cement vert)\<otimes>w1))\<circ>(basic ((cement vert)\<otimes>w2))\<circ>(y2))))
         \<and>((snd (count w1)) = (fst (count w2))))"
              using  exI 3 by auto
     then have 
       " linkrel_straighten_rightdowntop ?x ?y"
              using linkrel_straighten_rightdowntop_def by auto
     then have "linkrel ?x ?y" 
              using linkrel_def linkrel_straighten_def  by auto
     then have  "linkrel (Abs_diagram ((?x2) \<circ>(basic ((cement cup)\<otimes>(cement vert)\<otimes>w4))
                                      \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1)) 
                          (Abs_diagram ((?x2) \<circ>(basic ((cement vert)\<otimes>w4))
                                       \<circ>(basic ((cement vert)\<otimes>w4))\<circ>z1))"
               by auto 
     then have "linkrel_equiv 
                     (Abs_diagram (x1\<circ>basic y1\<circ>(basic ((cement cup)\<otimes>(cement vert)\<otimes>w4))
                                         \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1)) 
                     (Abs_diagram (x1\<circ>basic y1 \<circ>(basic ((cement vert)\<otimes>w4))
                                          \<circ>(basic ((cement vert)\<otimes>w4))\<circ>z1))"
               using  compose_leftassociativity r_into_rtranclp 
               linkrel_equiv_def
                     by metis
     then have "linkrel_equiv (Abs_diagram (x1\<circ>basic y1\<circ>(basic ((cement cup)\<otimes>?z4))
                                    \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1)) 
                       (Abs_diagram (x1\<circ>basic y1 \<circ>(basic ?z4)\<circ>(basic (?z4))\<circ>z1))"
               using  compose_leftassociativity r_into_rtranclp 
               linkrel_equiv_def 2 by (metis calculation)
                    
     then show ?thesis by auto
     }
     qed
(* Step3 tells us that that perturbed diagram introduced in the step above is equivalent to the 
 the diagram obtained by pulling the cup to the left of the block y1*)
 have step3: 
 "linkrel_equiv 
   (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
        \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>(cement vert)\<otimes>w4))
        \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
   (Abs_diagram (((x1)\<circ>(basic y1))\<circ>(basic ((cement cup) \<otimes> ?z4))
         \<circ> (basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"  
 proof-
   {
    have "fst (count (v\<otimes>w)) = fst (count (cup#(v\<otimes>w)))" using count_def brickcount_def
        by auto
    also have "count ((cup)#((cement cup)\<otimes>w4)) 
           = (fst (brickcount (cup)) + fst (count ((cement cup)\<otimes>w4))
                   , snd (brickcount (cup)) + snd (count ((cement cup)\<otimes>w4)))"
        using count_def by auto
    have 4: "((cement cup)\<otimes>((cement vert)\<otimes>w4)) = cup#((cement vert)\<otimes>w4)" 
        using append_blocks_Nil by metis
    have 5:"fst (count ((cup)#((cement cup)\<otimes>w4)))
          = (fst (brickcount(cup)) + fst (count ((cement cup)\<otimes>w4)))"
        using count_def  brickcount_def by auto
   have  
   "(fst (brickcount (cup)) + fst (count ((cement cup)\<otimes>w4))) = fst (count ((cement cup)\<otimes>w4))"
       using brickcount_def by auto
   then have 
  "fst (count (cup#((cement cup)\<otimes>w4))) =  fst (count ((cement cup)\<otimes>w4))"
       by auto
   moreover have 
    "fst (count (((cement cup))\<otimes>((cement cup)\<otimes>w4))) =  fst (count (cup#((cement cup)\<otimes>w4)))"
       using 5 by (metis Tangles.append_blocks.append_blocks_Nil)
   moreover then have 
   "fst (count (((cement cup))\<otimes>((cement cup)\<otimes>w4))) =  fst (count ((cement cup)\<otimes>w4))"
       by auto
   then have 6:"fst (wall_count (basic ((cement cup)\<otimes>(cement vert)\<otimes>w4))) 
                  = fst (wall_count (basic ((cement vert)\<otimes>w4))) " 
      using wall_count_def 
      by (metis append_blocks.append_blocks_Nil add_diff_cancel 
          comm_monoid_add_class.add.left_neutral count.simps(2) fst_conv wall_count.simps(1))
   have  "w4 = (make_vert_block ?k)" using assms by auto
   moreover have  "(make_vert_block (?k+1)) = ((cement vert)\<otimes>(make_vert_block ?k))" 
      by simp
   moreover have 7:"?z4 = (cement vert)\<otimes>(make_vert_block ?k)" 
           by auto    
   moreover have "  fst (count (make_vert_block (nat (snd (count y1) + -2) + 1))) =
                    int (nat (snd (count y1) + -2) + 1) + 1" 
          unfolding count.simps make_vert_block_fstequality by auto
   moreover have "int (nat (snd (count y1) + -2) + 1)  = (snd (count y1)) + -1" 
          using non_seperating_block_def assms(1) int_nat_condition by auto
   moreover then have " int (nat (snd (count y1) + -2) + 1) + 1 = snd(count y1)" by auto
   ultimately have "fst (count (make_vert_block (nat (snd (count y1) + -2) + 1))) = 
              (snd (count y1))"  by auto
   moreover then have "fst (wall_count (basic ((cement cup)\<otimes>(cement vert)\<otimes>w4))) 
                =  fst (count (make_vert_block (nat (snd (count y1) + -2) + 1)))"
                          using 7 6 wall_count.simps(1) 
                          by (metis assms(2))
   ultimately have 8 : "fst (wall_count (basic ((cement cup)\<otimes>(cement vert)\<otimes>w4))) 
                                       = snd (count y1)" 
               using 6  by auto 
   moreover have  "fst (wall_count (basic ((cement vert)\<otimes>w4))) = snd (wall_count ?x2)" 
               using 8 wall_count.simps 
               by (metis snd_conv 6 wall_count_compose) 
   then have 9 : "fst (wall_count (basic ((cement vert)\<otimes>w4))) 
          = snd (wall_count (x1\<circ>(basic y1)))" 
               using  wall_count_def by auto
   have  "fst (brickcount cup) =  0" using brickcount_def by auto
   then have 10:"fst (count (cement cup)) =  0" using count.simps(1)
                by (metis )
   have  "strands (vert#(cement vert))" 
               using  append_blocks_def strands_def  
               brickstrand.simps(1) strands.simps(1) strands.simps(2) 
                       by metis
   moreover have  "(vert#(cement vert)) = ((cement vert)\<otimes>(cement vert))" using append_blocks_Nil 
                        by metis
   ultimately have 11: "strands ((cement vert)\<otimes>(cement vert))" 
          by metis
   let ?a0 = "(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1"
   let ?b0 = "((cement vert)\<otimes>(cement vert))"
   let  ?a =  "Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic (?b0\<otimes>((cement vert)\<otimes>w4)))
        \<circ>((basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"
   let ?b = "Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((cement cup) \<otimes> ((cement vert) \<otimes> w4)))
        \<circ>((basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"
   have " \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.(?a = Abs_diagram ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))\<circ>(y2)))"
          using exI by metis
   also have " \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.(
         ?b = (Abs_diagram  ((y1)\<circ>(basic (w1))\<circ>(basic (A\<otimes>w2))\<circ>(y2))))"
          using exI 
          by metis
   then have "  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.((?a = Abs_diagram
   ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))\<circ>(y2))) \<and>
   (?b = Abs_diagram
   ((y1)\<circ>(basic (w1))\<circ>(basic (A\<otimes>w2))\<circ>(y2)))
    \<and>((snd (count w1)) = (fst (count w2)))
    \<and>((fst (count A)) = 0)
    \<and>(strands B))" 
          using  compose_leftassociativity 9 10 11 exI assms leftright_associativity  6 8 
          wall_count.simps(1) by (metis)
   then have  "linkrel_compbelow_centerright ?a ?b" 
          using linkrel_compbelow_centerright_def by auto
   then have  "linkrel_compress ?a ?b" 
          using  linkrel_compress_def linkrel_compbelow_def by auto
   then have "linkrel ?a ?b" 
          using  linkrel_def by auto
   then have  "linkrel_equiv ?a ?b"
          using  linkrel_equiv_def r_into_rtranclp by (metis (full_types) r_into_rtranclp)
   then have "linkrel_equiv 
            (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic (((cement vert)\<otimes>(cement vert))
                           \<otimes>((cement vert)\<otimes>w4)))\<circ>((basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1)))
            (Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((cement cup) \<otimes> ((cement vert) \<otimes> w4)))
                           \<circ>((basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1)))"
          by metis
   then have step3: 
   "linkrel_equiv 
           (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
                 \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>(cement vert)\<otimes>w4))
                 \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
           (Abs_diagram (((x1)\<circ>(basic y1))\<circ>(basic ((cement cup) \<otimes> ?z4))
                 \<circ> (basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))" 
          using leftright_associativity left_associativity compose_leftassociativity 
          by (metis "7" assms(2))
   then show ?thesis by simp
 }
 qed
(*step 4 involves compressing the diagram obtained in step3 by pulling the cap below*)
 have step4: 
 "linkrel_equiv
  (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
  (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
   \<circ>(basic ((cement vert) \<otimes> (cement vert) \<otimes> (cement vert) \<otimes> w4))
   \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))" 
 proof-
 {
    let ?p = "(x1)\<circ>(basic ((cement cup)\<otimes>y1))"
    let ?q = "(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1"
    let ?r = " basic ((cement vert) \<otimes> (cement vert) \<otimes> (cement vert) \<otimes> w4)"
    have 1:"strands ((cement vert) \<otimes> (cement vert) \<otimes> (cement vert) \<otimes> w4)"
       using assms(2)  append_blocks.append_blocks_Nil  
       strands.simps(2) by (metis strand_make_vert_block)
    have  "snd (count ((cement cup)\<otimes>y1)) =  snd (count (cup#y1))" 
       using append_blocks.append_blocks_Nil count_def  by (metis)
    also have  " snd (count (cup#y1)) =  2+ snd (count (y1))"
       using  count_def brickcount_def by auto
    then have "snd (count ((cement cup)\<otimes>y1)) > snd (count (y1))"
       using   add_strict_increasing dbl_def 
       dbl_simps(3) order_refl zero_less_two by auto
    then have  "snd (count ((cement cup)\<otimes>y1)) > 1"
      using assms non_seperating_block_def by auto
    moreover have  "snd (wall_count ?p) = (snd (count ((cement cup)\<otimes>y1)))"
      using wall_count_def  snd_conv wall_count.simps(1) wall_count_compose by auto
    ultimately have  "snd (wall_count ?p) > 0"
      using   assms by auto
    then have  
     "linkrel_compress_null 
      (Abs_diagram (?p\<circ>(basic ((cement vert) \<otimes> (cement vert) \<otimes> (cement vert) \<otimes> w4))\<circ>?q))
      (Abs_diagram (?p\<circ>?q))"
       using 1 linkrel_compress_null_def by metis
    moreover then have 
     "linkrel_compress
      (Abs_diagram (?p\<circ>(basic ((cement vert) \<otimes> (cement vert) \<otimes> (cement vert) \<otimes> w4))\<circ>?q))
      (Abs_diagram (?p\<circ>?q))"
        using linkrel_compress_def by auto
    ultimately have 
    "linkrel (Abs_diagram (?p\<circ>?q))
    (Abs_diagram (?p\<circ>(basic ((cement vert) \<otimes> (cement vert) \<otimes> (cement vert) \<otimes> w4))\<circ>?q))"
      using linkrel_def by auto
    then have 
    "linkrel_equiv
    (Abs_diagram (?p\<circ>?q))
    (Abs_diagram (?p\<circ>(basic ((cement vert) \<otimes> (cement vert) \<otimes> (cement vert) \<otimes> w4))\<circ>?q))"
       using linkrel_equiv_def compose_leftassociativity 
       leftright_associativity r_into_rtranclp  by (metis (full_types))
    then have  
    "linkrel_equiv
    (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
    (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
                \<circ>(basic ((cement vert) \<otimes> (cement vert) \<otimes> (cement vert) \<otimes> w4))
                \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"
       using  linkrel_equiv_def compose_leftassociativity 
       leftright_associativity r_into_rtranclp  by metis
    then show ?thesis by simp
  }
  qed
 (*we now obtain the result by combining the steps*)                    
 have "linkrel_equiv
  (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
             (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))"
 proof- 
 {
   have 
  "linkrel_equiv 
    (Abs_diagram (x1\<circ>basic y1\<circ>(basic ((cement cup)\<otimes>?z4))
            \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1)) 
    (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using step1 step2 rtranclp_trans linkrel_equiv_def by metis
   moreover then have
   "linkrel_equiv (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
    \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>?z4))\<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
             (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
           using step3  linkrel_equiv_def rtranclp_trans compose_leftassociativity 
           leftright_associativity step2   linkrel_trans 
            by (metis (full_types) append_blocks_Nil assms(2) make_vert_induct) 
   moreover then have combine_compress:"linkrel_equiv
   (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
             (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
   using  step4 linkrel_equiv_def rtranclp_trans compose_leftassociativity 
   leftright_associativity step2 linkrel_trans  by (metis assms(2) link_symmetry2 make_vert_induct_left)
   then show ?thesis by simp
   }
   qed
 then show ?thesis by auto
qed


text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1 \<circ>z1), where y1 is a 
block with outgoing strands, the following theorem proves that it is equivalent to a link 
diagram in which there exists a cup appended to the right of y1 *}

(*count of a block which is constructed by appending two blocks*)
lemma count_rightcompose:
   "count(v\<otimes>w) = (fst (count v) + fst (count w), snd (count v)+snd (count w))"
  apply (induct_tac v)
  apply (metis append_blocks.append_blocks_Nil count.simps(1) count.simps(2))
  apply(auto)
  done


(*count of a block which is constructed by appending a block to (cement cup)*)
lemma count_cup_rightcompose:" count(v\<otimes>(cement cup)) = (fst (count v), snd (count v)+2)"
  apply (simp add:count_rightcompose)
  done

lemma fstcount_cup_rightcompose:" fst (count(v\<otimes>(cement cup))) = fst (count v)"
  apply (simp add: count_cup_rightcompose)
  done


theorem metaequivalence_right: 
 assumes "(snd (count y1))>1" 
 (*the block y1 has outgoing strands*)
 and "w4 = make_vert_block  (nat ((snd (count y1)) + (-2)))"
 (*w4 is the vertical strand which consists of (snd (count y1)-1 strands*)
 shows "linkrel_equiv 
        (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>(cement cup)))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
        (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
(*every diagram is equivalent to the diagram obtained by stretching it and pulling a string below 
on the right of the stretched part*)   
proof-
(* proof is broken into three steps- the first step involves stretching the strand, the second step
involves pulling a strand below. The third step involves combining the first two steps*)

 let ?k = " (nat ((snd (count y1))+ (-2) ))" 
 let ?z4 = "make_vert_block (nat ((snd (count y1)) + (-2))+1)"
 have 1: " ?z4 = make_vert_block (?k+1)" using assms by auto
 let ?x2 = "x1 \<circ> (basic y1)"
 (*Step 1 tells us that the diagram that the wall x1 \<circ> basic y1 \<circ> z1 gives rise to, is equivalent to 
the diagram obtained by stretching the diagram above the block y1*)
 have step1: 
"linkrel_equiv (Abs_diagram (x1 \<circ> basic y1 \<circ> basic ?z4\<circ>basic ?z4\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using compose_leftassociativity linkrel_doublecompress_top assms 
               non_seperating_block_def by auto
 (*Step 2 tells us that the diagram obtained above by stretching is equivalent to the diagram 
obtained by perturbing it a bit as to induce a cup and a cap on the right portion of the diagram*)
 have step2: "linkrel_equiv 
               (Abs_diagram (x1\<circ>basic y1\<circ>(basic (?z4\<otimes>(cement cup)))
                             \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)) 
              (Abs_diagram (x1\<circ>basic y1 \<circ>(basic ?z4)\<circ>(basic (?z4))\<circ>z1))"
 proof-
 {
    have 2: "w4 = (make_vert_block ?k)" using assms by auto
    also  have 3:"(make_vert_block (?k+1)) = ((make_vert_block ?k) \<otimes>(cement vert))" 
               by (metis make_vert_induct make_vert_induct_right)
    then have 4:"?z4 = (make_vert_block ?k)\<otimes>(cement vert)  " 
               using 1 by auto
    then have "(Abs_diagram (?x2 \<circ> (basic ?z4) \<circ>(basic ?z4)\<circ>z1)) 
              = (Abs_diagram (?x2  \<circ> (basic (w4\<otimes>(cement vert)))\<circ> (basic (w4\<otimes>(cement vert)))\<circ>z1))" 
                        using 2 by auto
    have 5: "(snd (count w4)) = (fst (count w4))" 
                        using make_vert_block_fstsndequality 2 by auto
    let ?x = "(Abs_diagram (?x2 \<circ>(basic (w4\<otimes>(cement vert)\<otimes>(cement cup)))
                        \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
    let ?y = "(Abs_diagram (?x2 \<circ>(basic (w4\<otimes>(cement vert)))\<circ>(basic (w4\<otimes>(cement vert)))\<circ>z1))"
    have  
    " (\<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.((?x = Abs_diagram ((y1) \<circ>(basic (w1\<otimes>(cement vert)\<otimes>(cement cup)))
                                           \<circ>(basic (w2\<otimes>(cement cap)\<otimes>(cement vert))) \<circ> y2)))
     \<and>(?y = Abs_diagram (y1 \<circ> (basic (w1\<otimes>(cement vert))) \<circ> (basic (w2\<otimes>(cement vert))) \<circ> y2))
     \<and> ((snd (count w1)) = (fst (count w2))))"
               using  5 exI by auto 
    then have "linkrel_straighten_leftdowntop ?x ?y"
               using linkrel_straighten_leftdowntop_def compose_leftassociativity  
               by (metis)
    then have "linkrel ?x ?y" 
                using linkrel_def linkrel_straighten_def by auto
    then have  "linkrel (Abs_diagram ((?x2) \<circ>(basic (w4\<otimes>(cement vert)\<otimes>(cement cup)))
                \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)) 
              (Abs_diagram ((?x2) \<circ>(basic (w4\<otimes>(cement vert)))\<circ>(basic (w4\<otimes>(cement vert)))\<circ>z1))"
                by auto 
    then have "linkrel_equiv (Abs_diagram (x1\<circ>basic y1\<circ>(basic (w4\<otimes>(cement vert)\<otimes>(cement cup)))
                                   \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)) 
              (Abs_diagram (x1\<circ>basic y1 \<circ>(basic (w4\<otimes>(cement vert)))\<circ>(basic (w4\<otimes>(cement vert)))\<circ>z1))"
               using  compose_leftassociativity r_into_rtranclp 
               linkrel_equiv_def
                     by metis
    then have "linkrel_equiv 
               (Abs_diagram (x1\<circ>basic y1\<circ>(basic (?z4\<otimes>(cement cup)))
                             \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)) 
              (Abs_diagram (x1\<circ>basic y1 \<circ>(basic ?z4)\<circ>(basic (?z4))\<circ>z1))"
               using   compose_leftassociativity r_into_rtranclp 
               linkrel_equiv_def 4 2 leftright_associativity  by (metis )
    then show ?thesis by simp
   }
   qed
(* Step3 tells us that that perturbed diagram introduced in the step above is equivalent to the 
 the diagram obtained by pulling the cup to the left of the block y1*)
 have step3: "linkrel_equiv 
 (Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (?z4\<otimes>(cement vert)\<otimes>(cement vert)))
                                 \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)))
 (Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((?z4) \<otimes> (cement cup)))
                                 \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)))"
 proof-
{
    have "count ((w4\<otimes>(cement vert))\<otimes>(cement cup))  
           =  ((fst (count (w4\<otimes>(cement vert)))), (snd (count (w4\<otimes>(cement vert)))+2))"
             by (metis count_cup_rightcompose)
    then have "fst (count ((w4\<otimes>(cement vert))\<otimes>(cement cup))) = (fst (count (w4\<otimes>(cement vert))))"
             by auto
    then have 2:"fst (wall_count (basic ((w4\<otimes>(cement vert))\<otimes>(cement cup)))) 
                           = fst (wall_count (basic (w4\<otimes>(cement vert)))) " 
             using wall_count_def  append_blocks.append_blocks_Nil add_diff_cancel 
              comm_monoid_add_class.add.left_neutral count.simps(2) fst_conv wall_count.simps(1)
             by (metis)
    have 3: "w4 = (make_vert_block ?k)" using assms by auto
    have 4: "(make_vert_block (?k+1)) = ((make_vert_block ?k) \<otimes>(cement vert))" 
               by (metis make_vert_induct make_vert_induct_right) 
    have "fst (count (make_vert_block (nat (snd (count y1) + -2) + 1))) =
                    int (nat (snd (count y1) + -2) + 1) + 1" 
          unfolding count.simps make_vert_block_fstequality by auto
    moreover have "int (nat (snd (count y1) + -2) + 1)  = (snd (count y1)) + -1" 
          using non_seperating_block_def assms(1) int_nat_condition by auto
    moreover then have " int (nat (snd (count y1) + -2) + 1) + 1 = snd(count y1)" by auto
    ultimately have 5:"fst (count (make_vert_block (nat (snd (count y1) + -2) + 1)))  
                       = (snd (count y1))"  by auto
    have "fst (brickcount cup) =  0" using brickcount_def by auto
    then have 6:"fst (count (cement cup)) =  0" 
                  using count_def by (metis count.simps(1))
    have "strands (vert#(cement vert))" 
                       using append_blocks_def strands_def  brickstrand.simps(1) 
                        strands.simps(1) strands.simps(2) 
                       by metis
    moreover have  "(vert#(cement vert)) = ((cement vert)\<otimes>(cement vert))" 
                       using append_blocks_Nil  by metis
    ultimately have 7: "strands ((cement vert)\<otimes>(cement vert))" 
                       by metis
    let  ?a = "Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (?z4\<otimes>(cement vert)\<otimes>(cement vert)))
            \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
    let ?b = "Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((w4\<otimes>(cement vert)) \<otimes> (cement cup)))
            \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
    have 8: "  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.
                  (?a = Abs_diagram ((y1)\<circ>(basic (w1 \<otimes>A))\<circ>(basic (w2\<otimes>B))\<circ>(y2)))"
                       using exI by metis
    have 9: " \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.
                               (?b = (Abs_diagram ((y1)\<circ>(basic (w1))\<circ>(basic (w2\<otimes>A))\<circ>(y2))))"
                       using exI by metis
    let  ?a = "Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (?z4\<otimes>(cement vert)\<otimes>(cement vert)))
                           \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
    let ?b = "Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((w4\<otimes>(cement vert)) \<otimes> (cement cup)))
                           \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
    have " \<exists>y1.\<exists>z1.\<exists>z2.\<exists>A.\<exists>B.\<exists>y2.(
                             (?a = Abs_diagram ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))
                            \<and> (?b = Abs_diagram ((y1) \<circ>(basic (z1))\<circ>(basic (z2\<otimes>A))\<circ>(y2)))
                            \<and>((snd (count z1)) = (fst (count z2)))
                            \<and>((fst (count A)) = 0)
                            \<and>(strands B))" 
           using 8 9 compose_leftassociativity 6 7  exI assms leftright_associativity  
           by (metis 4 5)
    then have  "linkrel_compbelow_centerleft ?a ?b" 
                        using linkrel_compbelow_centerright_def 8  
                        linkrel_compbelow_centerleft_def zero_reorient
                        by (metis)
   then have  "linkrel_compress ?a ?b" 
           using  linkrel_compress_def linkrel_compbelow_def by auto
   then have  "linkrel ?a ?b" 
           using  linkrel_def by auto
   then have "linkrel_equiv ?a ?b"
          using linkrel_equiv_def r_into_rtranclp
          by (metis (full_types) r_into_rtranclp)
   then have  "linkrel_equiv 
       (Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (?z4\<otimes>(cement vert)\<otimes>(cement vert)))
               \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)))
       (Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((w4\<otimes>(cement vert)) \<otimes> (cement cup)))
               \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)))"
            by metis
   then have "linkrel_equiv 
        (Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (?z4\<otimes>(cement vert)\<otimes>(cement vert)))
                                 \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)))
        (Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((?z4) \<otimes> (cement cup)))
                                 \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)))"
             using leftright_associativity 3  left_associativity compose_leftassociativity 4 
             by (metis)
   from this show ?thesis by simp
 }
 qed
(*step 4 involves compressing the diagram obtained in step3 by pulling the cap below*)
 have step4:"linkrel_equiv
       (Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
       (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>(cement cup)))\<circ>(basic (?z4\<otimes>(cement vert) \<otimes> (cement vert)))
                               \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
      proof-
 {
   let ?p = "(x1)\<circ>(basic (y1 \<otimes> (cement cup)))"
   let ?q = "(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1"
   let ?r = " basic (?z4 \<otimes> (cement vert) \<otimes> (cement vert))"
   have 2: "strands (?z4 \<otimes> (cement vert) \<otimes> (cement vert))"
       using assms  append_blocks.append_blocks_Nil  
     strands.simps(2) leftright_associativity make_vert_induct_left by (metis strand_make_vert_block make_vert_induct_right)
   have  "snd (count (y1\<otimes>(cement cup))) =  snd (count (y1)) + 2"
           apply (induct_tac y1)
           apply (auto)
           done
   then have  "snd (count (y1 \<otimes> (cement cup))) > snd (count (y1))"
          using add_strict_increasing dbl_def dbl_simps(3) order_refl zero_less_two
          by auto
   then have  "snd (count (y1 \<otimes> (cement cup))) > 1"
          using assms by auto
   moreover have  "snd (wall_count ?p) = (snd (count (y1\<otimes>(cement cup))))"
          using wall_count_def  snd_conv wall_count.simps(1) wall_count_compose by auto
   ultimately have  "snd (wall_count ?p) > 0"
          using  assms by auto
   then have "linkrel_compress_null 
             (Abs_diagram (?p\<circ>(basic ((?z4) \<otimes> (cement vert) \<otimes> (cement vert)))\<circ>?q))
             (Abs_diagram (?p\<circ>?q))"
          using 2  linkrel_compress_null_def by metis
   then have "linkrel_compress
              (Abs_diagram (?p\<circ>(basic ((?z4) \<otimes> (cement vert) \<otimes> (cement vert)))\<circ>?q))
              (Abs_diagram (?p\<circ>?q))"
           using linkrel_compress_def by auto
   then have "linkrel
              (Abs_diagram (?p\<circ>?q))
              (Abs_diagram (?p\<circ>(basic (?z4 \<otimes> (cement vert) \<otimes> (cement vert)))\<circ>?q))"
           using linkrel_def by auto
   then have "linkrel_equiv
                (Abs_diagram (?p\<circ>?q))
                (Abs_diagram (?p\<circ>(basic ((?z4) \<otimes> (cement vert) \<otimes> (cement vert)))\<circ>?q))"
           using  linkrel_equiv_def compose_leftassociativity 
           leftright_associativity r_into_rtranclp  by metis
   then have "linkrel_equiv
       (Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
       (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>(cement cup)))\<circ>(basic (?z4\<otimes>(cement vert) \<otimes> (cement vert)))
                               \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
         using  linkrel_equiv_def compose_leftassociativity 
         leftright_associativity r_into_rtranclp  by metis
   from this show ?thesis by simp
  }
 qed

 (*combining steps*)                  
 {
   have combine_vert: 
   "linkrel_equiv 
     (Abs_diagram (x1\<circ>basic y1\<circ>(basic (?z4\<otimes>(cement cup)))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
     (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
        using step1 step2 rtranclp_trans linkrel_equiv_def by metis
   have combine_cup:
    "linkrel_equiv 
     (Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (?z4\<otimes>(cement vert)\<otimes>(cement vert)))
              \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)))
     (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using step3 combine_vert linkrel_equiv_def rtranclp_trans
                compose_leftassociativity leftright_associativity 
               step2  
                 by (metis (full_types))
   have combine_compress:
    "linkrel_equiv 
      (Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
      (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))"
             using  combine_cup step4  rtranclp_trans  combine_vert linkrel_equiv_def rtranclp_trans
             compose_leftassociativity leftright_associativity 
             step2   1 nat_add_commute r_into_rtranclp  make_vert_induct_left make_vert_induct_right 
             wall_count.simps(1) by (metis (full_types))
 from combine_compress show ?thesis by simp
 }
qed

text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1 \<circ>z1), where y1 is a 
block with incoming strands, the following theorem proves that it is equivalent to a link 
diagram in which there exists a cap appended to the right of y1 *}


theorem metaequivalence_bottomright: 
 assumes "(fst (count y1))>1"
(*Assumes that the number of incoming strands is greater than or equal to 1*)
 and "w4 = make_vert_block  (nat ((fst (count y1)) + (-2)))" 
(*w3 is the block composed of vertical strands such that the number of vertical strands is one less
 than the number of incoming vertical strands of y1*) 
 and "well_defined (x1 \<circ> basic y1 \<circ>z1)"
 shows "linkrel_equiv 
      (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert))\<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1)))     
      (Abs_diagram (x1 \<circ> (basic y1) \<circ>z1))" 
(*every diagram is equivalent to the diagram obtained by stretching it and pulling a string above 
on the right of the stretched part*)   
proof-
(* proof is broken into three steps- the first step involves stretching the strand, the second step
involves pulling a strand above. The third step involves combining the first two steps*)
 let ?z4 = "make_vert_block (nat ((fst (wall_count (basic y1))) + (-2))+1)"
 let ?k = " (nat ((fst (count y1))+ (-2) ))" 
 (*helper theorems- Following results are simplifications which are used in all the steps below*)
 
  have 1: " (?z4 = make_vert_block (?k+1))" using assms by auto
  have 2: "w4 = (make_vert_block ?k)" using assms by auto
  have 3: "(make_vert_block (?k+1)) = ((make_vert_block ?k) \<otimes>(cement vert))" 
        by (metis make_vert_induct make_vert_induct_right)
  have 4:"?z4 = (make_vert_block ?k)\<otimes>(cement vert)  " 
          using 1 3 by auto
 (*Step 1 tells us that the diagram that the wall x1 \<circ> basic y1 \<circ> z1 gives rise to, is equivalent to 
the diagram obtained by stretching the diagram below the block y1*)
 then have step1: 
 "linkrel_equiv 
           (Abs_diagram (x1 \<circ> basic ?z4\<circ>basic ?z4 \<circ> basic y1\<circ>z1)) 
           (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))" 
  proof-
    have "fst (count y1) = snd (wall_count x1)" 
         using wall_count.simps assms(3) well_defined_def 
         compose_Nil diagram_fst_equals_snd fst_eqD   by metis
    then show ?thesis 
          using compose_leftassociativity rtranclp_trans 
          linkrel_doublecompress_below assms(1) by auto
    qed
                                                 
 (*Step 2 tells us that the diagram obtained above by stretching is equivalent to the diagram 
obtained by perturbing it a bit as to induce a cup and a cap on the right side of the diagram*)
  have step2: "linkrel_equiv 
              (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (?z4\<otimes>(cement cap)))\<circ>(basic y1)\<circ> z1)) 
              (Abs_diagram ((x1) \<circ>(basic (?z4))\<circ>(basic (?z4))\<circ>((basic y1)\<circ> z1)))"
 proof-
 {
    have 5: "(snd (count w4)) = (fst (count w4))" 
          using make_vert_block_fstsndequality 2 by auto
    let ?z3 = " (basic y1)\<circ> z1"
    let ?x = "(Abs_diagram (x1 \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                        \<circ>(basic (w4\<otimes>(cement vert)\<otimes>(cement cap)))\<circ>(?z3)))"
    let ?y = "(Abs_diagram (x1 \<circ>(basic (w4\<otimes>(cement vert)))\<circ>(basic (w4\<otimes>(cement vert)))\<circ> (?z3)))"
    have 
       "linkrel_straighten_lefttopdown ?x ?y"
          using linkrel_straighten_lefttopdown_def compose_leftassociativity 
          5  by auto
    then have "linkrel ?x ?y" 
          using linkrel_def linkrel_straighten_def  by auto      
    then have  
     "linkrel 
       (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                \<circ>(basic (w4\<otimes>(cement vert)\<otimes>(cement cap)))\<circ>(?z3))) 
       (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>(cement vert)))\<circ>(basic (w4\<otimes>(cement vert)))\<circ>(?z3)))"
               by auto
    then have "linkrel_equiv 
       (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                          \<circ>(basic (w4\<otimes>(cement vert)\<otimes>(cement cap)))\<circ>((basic y1)\<circ> z1))) 
       (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>(cement vert)))\<circ>(basic (w4\<otimes>(cement vert)))\<circ>((basic y1)\<circ> z1)))"
               using  compose_leftassociativity r_into_rtranclp linkrel_equiv_def
              by metis
    then have  "linkrel_equiv 
              (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (w4\<otimes>(cement vert)\<otimes>(cement cap)))\<circ>(basic y1)\<circ> z1)) 
              (Abs_diagram ((x1) \<circ>(basic (?z4))\<circ>(basic (?z4))\<circ>((basic y1)\<circ> z1)))"
               using  4 2
                     by (auto)
    then have  "linkrel_equiv 
              (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (?z4\<otimes>(cement cap)))\<circ>(basic y1)\<circ> z1)) 
              (Abs_diagram ((x1) \<circ>(basic (?z4))\<circ>(basic (?z4))\<circ>((basic y1)\<circ> z1)))"
               using  4 
                   Link.abs_eq_iff compose_Nil leftright_associativity 
                   step1  2
                   by (metis)
    from this show ?thesis by simp
    }
    qed
(* Step3 tells us that that perturbed diagram introduced in the step above is equivalent to the 
 the diagram obtained by pulling the cup to the right of the block y1*) 
 have step3:  "linkrel_equiv
    (Abs_diagram (((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert))))
                 \<circ>(basic (?z4\<otimes>(cement vert)\<otimes>(cement vert)))\<circ>(basic (y1\<otimes>(cement cap)))\<circ> z1))
    (Abs_diagram (((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert))))\<circ>(basic (?z4\<otimes>(cement cap)))
                 \<circ>(basic y1)\<circ> z1)) "
proof-
 {
   have 5: " (snd (wall_count x1)) = (fst (count y1))" 
       proof-
        have "(fst (wall_count ((basic y1)\<circ>z1))) = (snd (wall_count x1))" 
            using assms diagram_fst_equals_snd by metis
        moreover have " (fst (wall_count ((basic y1)\<circ>z1))) = (fst (count y1))" 
            by (metis compose_Nil fst_eqD wall_count.simps(2))
        ultimately show ?thesis by auto
        qed
   have  "snd (count (?z4)) = snd (count (make_vert_block (?k+1)))"  
       using 1 make_vert_block_fstequality by auto
   moreover have  "snd (count (make_vert_block (?k+1))) = int(?k+1)+1"  
            using make_vert_block_sndequality by auto
   ultimately have 6:"snd (count (?z4)) =  int(?k)+2" 
           by auto
   have "((fst (count y1))+(-1))>0" 
            using assms by auto
   then have  "int (nat (fst (count y1) + -2)) = (fst (count y1)) + -2" 
           using int_nat_eq  by auto
   moreover then  have "fst (count y1) = int(?k)+2" 
           by auto
   with 6 have 7: "snd (count (?z4)) = (fst (count y1))" 
             by auto
   have 8: "snd (count (cement cap)) = 0" 
             using  count_def brickcount_def brickcount.simps(3) count.simps(1) snd_conv by (metis)
   have "strands (vert#(cement vert))" using append_blocks_def strands_def  
                       brickstrand.simps(1) strands.simps(1) strands.simps(2) by metis
   moreover have "(vert#(cement vert)) = ((cement vert)\<otimes>(cement vert))"
             using append_blocks_Nil  by metis
   ultimately have 9: "strands ((cement vert)\<otimes>(cement vert))" 
             by metis
   let  ?a = "Abs_diagram (((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert))))
            \<circ>(basic (?z4\<otimes>(cement vert)\<otimes>(cement vert)))\<circ>(basic (y1\<otimes>(cement cap)))\<circ> z1) "
   let ?b = " (Abs_diagram (((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert))))
            \<circ>(basic (?z4\<otimes>(cement cap)))\<circ>(basic y1)\<circ> z1)) "
   have " \<exists>a1.\<exists>b1.\<exists>b2.\<exists>A.\<exists>B.\<exists>a2.(?a = Abs_diagram ((a1)\<circ>(basic (b1\<otimes>A))\<circ>(basic (b2\<otimes>B))\<circ>(a2))
     \<and>(?b  = (Abs_diagram ((a1)\<circ>(basic (b1\<otimes>B))\<circ>(basic (b2))\<circ>(a2))))
     \<and>((snd (count b1)) = (fst (count b2)))
     \<and>((snd (count B)) = 0)
     \<and>(strands A))" 
           using compose_leftassociativity 4 7 2  
            exI assms leftright_associativity  
              8  9 
           exI assms leftright_associativity compose_leftassociativity by metis
   then have "linkrel_compabove_centerleft ?a ?b" 
            using linkrel_compabove_centerleft_def 
               zero_reorient
            by (metis)
   then have "linkrel_compabove ?a ?b" 
           using  linkrel_compabove_def by auto
   then have  "linkrel_compress ?a ?b" 
           using  linkrel_compress_def by auto
   then have "linkrel ?a ?b" 
           using linkrel_def by auto
   then have  "linkrel_equiv ?a ?b"
           using  linkrel_equiv_def r_into_rtranclp by (metis (full_types) )
   from this show ?thesis by simp
 }
 qed
(*step 4 involves compressing the diagram obtained in step3 by pulling the cap above*)
  have step4: 
 "linkrel_equiv
    (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                      \<circ>(basic (?z4\<otimes>(cement vert)\<otimes>(cement vert)))\<circ>(basic (y1 \<otimes> (cement cap)))\<circ>z1))
    (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (y1 \<otimes> (cement cap)))\<circ>z1))"
 proof- 
 {
    let ?p = "(x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))"
    let ?q = "(basic (y1 \<otimes> (cement cap)))\<circ>z1"
    let ?r = " basic (?z4 \<otimes> (cement vert) \<otimes> (cement vert))"
    have 5: "snd (wall_count ?p) = snd (count (w4\<otimes>(cement cup)\<otimes>(cement vert)))"
         using wall_count_def  snd_conv wall_count.simps(1) wall_count_compose by auto
    have 6: "snd (count (x\<otimes>(cement vert))) >0 "
          using snd_count_positive  brickcount_def count_def make_vert_block.simps(1)  
          make_vert_block_fstsndequality make_vert_blocks_positiveblock_length
           add_nonneg_eq_0_iff less_le snd_count_additive snd_count_nonnegative
          by (metis)
   then have "snd (count ((w4\<otimes>(cement cup))\<otimes>(cement vert))) > 0"
          using add_nonneg_eq_0_iff brick.distinct(1) brickcount_zero_implies_cup 
          count.simps(1) le_neq_trans make_vert_block.simps(1) make_vert_block_fstsndequality 
          snd_count_additive snd_count_nonnegative by (metis)
   moreover then have "snd (wall_count ?p) > 0"
          using 5  by (metis leftright_associativity)
   moreover have "strands (?z4 \<otimes> (cement vert) \<otimes> (cement vert))"
         using assms  append_blocks.append_blocks_Nil  4 
         strands.simps(2) leftright_associativity make_vert_induct_left strand_make_vert_block wall_count.simps(1)
         by (metis) 
   ultimately have  
        "linkrel_compress_null (Abs_diagram (?p\<circ>?r\<circ>?q)) (Abs_diagram (?p\<circ>?q))"
           using  6 linkrel_compress_null_def leftright_associativity 
           by (metis)
   then have 
         "linkrel_compress (Abs_diagram (?p\<circ>?r\<circ>?q)) (Abs_diagram (?p\<circ>?q))"
          using linkrel_compress_def by auto
   then have  
       "linkrel (Abs_diagram (?p\<circ>?q)) (Abs_diagram (?p\<circ>?r\<circ>?q))"
          using linkrel_def by auto
   then have 
      "linkrel
         (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                      \<circ>(basic (?z4 \<otimes> (cement vert) \<otimes> (cement vert)))
                      \<circ>(basic (y1 \<otimes> (cement cap)))\<circ>z1))
         (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (y1 \<otimes> (cement cap)))\<circ>z1))"
      by (metis compose_leftassociativity linkrel_def)
   then have  
   "linkrel_equiv
     (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                   \<circ>(basic (?z4 \<otimes> (cement vert) \<otimes> (cement vert)))\<circ>(basic (y1 \<otimes> (cement cap)))\<circ>z1))
     (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (y1 \<otimes> (cement cap)))\<circ>z1))"
       using  linkrel_equiv_def compose_leftassociativity leftright_associativity 
      r_into_rtranclp   by (metis (full_types))
   from this show ?thesis by simp
 }
 qed

(*by combining the  steps, we get the desired equivalence*)
 {
 have combine_vert: 
 "linkrel_equiv    
        (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                   \<circ>(basic (?z4\<otimes>(cement cap)))\<circ>(basic y1)\<circ> z1)) 
        (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
        using step1 step2 rtranclp_trans linkrel_equiv_def by metis
 have combine_cup:
 "linkrel_equiv 
   (Abs_diagram (((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert))))
                \<circ>(basic (?z4\<otimes>(cement vert)\<otimes>(cement vert)))\<circ>(basic (y1\<otimes>(cement cap)))\<circ> z1))
   (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using step3 combine_vert linkrel_equiv_def rtranclp_trans compose_leftassociativity 
               leftright_associativity step2 4    
               2 by (metis) 
 have combine_compress:
 "linkrel_equiv
   (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (y1 \<otimes> (cement cap)))\<circ>z1))
   (Abs_diagram ((x1)\<circ>(basic y1)\<circ>z1))"
               using combine_cup step4 rtranclp_trans  combine_cup step4 rtranclp_trans 
               compose_leftassociativity leftright_associativity 
               step2 4   
               2 linkrel_equiv_def converse_rtranclp_into_rtranclp 
               by (metis compose_Nil link_symmetry2 linkrel_trans)
 from combine_compress show ?thesis by (simp add: compose_leftassociativity)
 }
 qed

text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1 \<circ>z1), where y1 is a 
block with incoming strands, the following theorem proves that it is equivalent to a link 
diagram in which there exists a cap appended to the left of y1 *}


 theorem metaequivalence_bottomleft: 
 assumes "(fst (count y1))>1"
 (*number of incoming strands of y1 is greater than 1*)
 and "w4 = make_vert_block  (nat ((fst (count y1)) + (-2)))"
 (*w4 is a block consisting of only vertical strands which sum up to one less than the number of 
 incoming strands of y1*) 
 and "well_defined (x1 \<circ> basic y1 \<circ>z1)"
 (*(x1\<circ>basic y1\<circ>z1) is a well defined wall*)
 shows 
  "linkrel_equiv 
        (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)\<circ>(basic ((cement cap)\<otimes>y1))\<circ>z1)))    
        (Abs_diagram (x1 \<circ> (basic y1) \<circ>z1))" 
(*every diagram is equivalent to the diagram obtained by stretching it and pulling a string above
 on the left of the stretched part*)   
proof-
(* proof is broken into three steps- the first step involves stretching the strand, the second step
involves pulling a strand below. The third step involves combining the first two steps*)
(*these are the helper lemmas that are used in simplification and clarification later*)

 let ?z4 ="make_vert_block (nat ((fst (wall_count (basic y1))) + (-2))+1)"
 let ?k = " (nat ((fst (count y1))+ (-2) ))" 
 have 1: " (?z4 = make_vert_block (?k+1))" 
      using assms by auto
  have 2: "w4 = (make_vert_block ?k)" 
      using assms by auto
 have 3: "(make_vert_block (?k+1)) = ((cement vert)\<otimes>(make_vert_block ?k))" 
     by (metis make_vert_induct_left)
 have 4:"?z4 = (cement vert) \<otimes>(make_vert_block ?k)  " 
     using 1 3 by auto     
 (*Step 1 tells us that the diagram that the wall x1 \<circ> basic y1 \<circ> z1 gives rise to, is equivalent to 
the diagram obtained by stretching the diagram below the block y1*)
 have step1: 
 "linkrel_equiv 
           (Abs_diagram (x1 \<circ> basic ?z4\<circ>basic ?z4 \<circ> basic y1\<circ>z1)) 
           (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))" 
      proof-
        have "fst (count y1) = snd (wall_count x1)" 
          using wall_count.simps assms(3) well_defined_def 
          compose_Nil diagram_fst_equals_snd fst_eqD   by metis
       then show ?thesis using compose_leftassociativity rtranclp_trans linkrel_doublecompress_below 
          assms(1) by auto
       qed
(*Step 2 tells us that the diagram obtained above by stretching is equivalent to the diagram 
obtained by perturbing it a bit as to induce a cup and a cap on the left portion of the diagram*)
 have step2: 
    "linkrel_equiv 
      (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))\<circ>(basic ((cement cap)\<otimes>?z4))
                    \<circ>((basic y1)\<circ> z1)))      
      (Abs_diagram ((x1) \<circ>(basic (?z4))\<circ>(basic (?z4))\<circ>((basic y1)\<circ> z1)))"
 proof-
 {
   have 5: "(snd (count w4)) = (fst (count w4))" 
      using make_vert_block_fstsndequality 2 by auto
   let ?z3 = " (basic y1)\<circ> z1"
   let ?x = "(Abs_diagram (x1 \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
            \<circ>(basic ((cement cap)\<otimes>(cement vert)\<otimes>w4))\<circ>(?z3)))"
   let ?y = "(Abs_diagram (x1 \<circ>(basic ((cement vert)\<otimes>w4))\<circ>(basic ((cement vert)\<otimes>w4))\<circ> (?z3)))"
   have 6:
   "\<exists>a.\<exists>b.\<exists>c.\<exists>d.(?x = Abs_diagram (a \<circ> (basic ((cement vert)\<otimes>(cement cup)\<otimes>b )) 
                    \<circ> (basic ((cement cap)\<otimes>(cement vert)\<otimes>c)) \<circ> d))"
       using exI by auto
   have 
   "\<exists>a.\<exists>b.\<exists>c.\<exists>d.(?y = Abs_diagram (a \<circ> (basic ((cement vert)\<otimes>b)) \<circ> (basic ((cement vert)\<otimes>c)) \<circ> d))"
       using exI by auto
   then have 
   "(\<exists>a.\<exists>b.\<exists>c.\<exists>d.(
  (?x = Abs_diagram ((a)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>b))\<circ>(basic ((cement cap)
                  \<otimes>(cement vert)\<otimes>c))\<circ>d)))
   \<and>(?y = Abs_diagram (a \<circ> (basic ((cement vert)\<otimes>b)) \<circ> (basic ((cement vert)\<otimes>c)) \<circ> d))
   \<and> ((snd (count b)) = (fst (count c))))"
       using  5 6 exI 
       by auto
   then have "linkrel_straighten_righttopdown ?x ?y"
      using linkrel_straighten_righttopdown_def compose_leftassociativity 6  5 
      by auto
   then have "linkrel ?x ?y" 
      using linkrel_def linkrel_straighten_def  by auto
   then have  
     "linkrel 
         (Abs_diagram ((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
                      \<circ>(basic ((cement cap)\<otimes>(cement vert)\<otimes> w4))\<circ>(?z3))) 
         (Abs_diagram ((x1) \<circ>(basic ((cement vert)\<otimes>w4))\<circ>(basic ((cement vert) \<otimes>w4))\<circ>(?z3)))"
         by auto
   then have 
    "linkrel_equiv 
      (Abs_diagram ((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
                    \<circ>(basic ((cement cap)\<otimes>(cement vert)\<otimes>w4))\<circ>((basic y1)\<circ> z1))) 
      (Abs_diagram ((x1) \<circ>(basic ((cement vert)\<otimes>w4))\<circ>(basic ((cement vert)\<otimes>w4))\<circ>((basic y1)\<circ> z1)))"
           using  compose_leftassociativity r_into_rtranclp linkrel_equiv_def
           by metis
   then have 
    "linkrel_equiv 
       (Abs_diagram ((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
                    \<circ>(basic ((cement cap)\<otimes>(cement vert)\<otimes>w4))\<circ>((basic y1)\<circ> z1)))     
       (Abs_diagram ((x1) \<circ>(basic (?z4))\<circ>(basic (?z4))\<circ>((basic y1)\<circ> z1)))"
            using 4 2
            by (auto)
   then have "linkrel_equiv 
      (Abs_diagram ((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
           \<circ>(basic ((cement cap)\<otimes>?z4))\<circ>((basic y1)\<circ> z1)))      
      (Abs_diagram ((x1) \<circ>(basic (?z4))\<circ>(basic (?z4))\<circ>((basic y1)\<circ> z1)))"
             using 4 Link.abs_eq_iff compose_Nil leftright_associativity step1 2
             by (metis)
   from this show ?thesis by simp
   }
   qed
(* Step3 tells us that that perturbed diagram introduced in the step above is equivalent to the 
 the diagram obtained by pulling the cap above to the left of the block y1*)
  have step3: 
 "linkrel_equiv
    (Abs_diagram (((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)))
             \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>?z4))\<circ>(basic ((cement cap)\<otimes>y1))\<circ> z1))
    (Abs_diagram (((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)))
              \<circ>(basic ((cement cap) \<otimes>?z4))\<circ>(basic y1)\<circ> z1)) "
 proof-
 {
   have "((fst (count y1))+(-1))>0" 
      using assms by auto
   then have  "snd (count (?z4)) = snd (count (make_vert_block (?k+1)))"  
      using 1 make_vert_block_fstequality by auto
   moreover then have  "snd (count (make_vert_block (?k+1))) = int(?k+1)+1"  
       using make_vert_block_sndequality
       by auto
   ultimately have 5:"snd (count (?z4)) =  int(?k)+2" 
        by auto
   have "((fst (count y1))+(-1))>0" 
      using assms by auto
   then have  "int (nat (fst (count y1) + -2)) = (fst (count y1)) + -2" 
       using int_nat_eq   by auto
   moreover then have "fst (count y1) = int(?k)+2" 
       by auto
   with 5 have 6: "snd (count (?z4)) = (fst (count y1))" 
         by auto
   with assms have 7 :
   "snd (count  ?z4) = fst (count y1) " 
       by auto
   have 8: "snd (count (cement cap)) = 0" 
       using  count_def brickcount_def  brickcount.simps(3) count.simps(1) snd_conv by (metis)
   have  "strands (vert#(cement vert))" 
       using  append_blocks_def strands_def  
       brickstrand.simps(1) strands.simps(1) strands.simps(2) by metis
   moreover have "(vert#(cement vert)) = ((cement vert)\<otimes>(cement vert))" 
        using append_blocks_Nil by metis
   ultimately have 9: "strands ((cement vert)\<otimes>(cement vert))" 
        by metis
   let  ?a ="Abs_diagram (((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)))
                       \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>?z4))\<circ>(basic ((cement cap)\<otimes>y1))\<circ> z1) "
   let ?b = " (Abs_diagram (((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)))
                       \<circ>(basic ((cement cap)\<otimes>?z4))\<circ>(basic y1)\<circ> z1)) "
   have  " \<exists>a1.\<exists>b1.\<exists>b2.\<exists>A.\<exists>B.\<exists>a2.(
                   (?a = Abs_diagram ((a1)\<circ>(basic (A \<otimes>b1 ))\<circ>(basic (B \<otimes> b2))\<circ>(a2))) 
                 \<and> (?b  = (Abs_diagram ((a1)\<circ>(basic (B\<otimes>b1))\<circ>(basic (b2))\<circ>(a2))))
                 \<and>((snd (count b1)) = (fst (count b2)))
                 \<and>((snd (count B)) = 0)
                 \<and>(strands A))" 
          using compose_leftassociativity 4  2 
          exI assms leftright_associativity  7  8  9 
          exI assms leftright_associativity compose_leftassociativity
          by metis
   then have  "linkrel_compabove_centerright ?a ?b" 
          using linkrel_compabove_centerright_def 
          zero_reorient by metis
   then have  "linkrel_compabove ?a ?b" 
          using  linkrel_compabove_def by auto
   then have "linkrel_compress ?a ?b" 
          using linkrel_compress_def by auto
   then have "linkrel ?a ?b" 
          using  linkrel_def by auto
   then have "linkrel_equiv ?a ?b"
          using linkrel_equiv_def r_into_rtranclp  
          by (metis (full_types) r_into_rtranclp)
   from this show ?thesis by auto
 }
 qed
(*step 4 involves compressing the diagram obtained in step3 by pulling the cap below*)
 have step4: 
  "linkrel_equiv
     (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))\<circ>(basic ((cement cap) \<otimes> y1))\<circ>z1))
     (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
                     \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>?z4))\<circ>(basic ((cement cap) \<otimes> y1))\<circ>z1))"
 proof-
{
   let ?p = "(x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))"
   let ?q = "(basic ((cement cap) \<otimes> y1))\<circ>z1"
   let ?r = " basic ((cement vert) \<otimes> (cement vert)\<otimes>?z4)"
   have 5: "strands ((cement vert) \<otimes> (cement vert)\<otimes>?z4)"
             using assms  append_blocks.append_blocks_Nil 4 
             strands.simps(2) leftright_associativity make_vert_induct_left strand_make_vert_block 
             wall_count.simps(1) by (metis)
   have 6: "snd (wall_count ?p) = snd (count ((cement vert)\<otimes>(cement cup)\<otimes>w4))"
             using wall_count_def  snd_conv wall_count.simps(1) wall_count_compose by auto 
   with 6 have  "snd (wall_count ?p) > 0"
            by (metis One_nat_def add_0_iff le_neq_trans make_vert_block.simps(1) 
            make_vert_block_sndequality of_nat_1 of_nat_Suc snd_count_additive 
            snd_count_nonnegative snd_count_positive zero_neq_one)
   then have 
     "linkrel_compress_null  (Abs_diagram (?p\<circ>?r\<circ>?q)) (Abs_diagram (?p\<circ>?q))"
           using 5  linkrel_compress_null_def 
           leftright_associativity 6  by (metis)
   then have 
     "linkrel_compress  (Abs_diagram (?p\<circ>?r\<circ>?q)) (Abs_diagram (?p\<circ>?q))"
           using linkrel_compress_def by auto
   moreover then have
      "linkrel (Abs_diagram (?p\<circ>?q)) (Abs_diagram (?p\<circ>?r\<circ>?q))"
           using  linkrel_def by auto
   moreover then have 
   "linkrel
     (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
                  \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>?z4))\<circ>(basic ((cement cap) \<otimes> y1))\<circ>z1))
      (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))\<circ>(basic ((cement cap) \<otimes> y1))\<circ>z1))"
            using compose_leftassociativity linkrel_def by metis
   ultimately have 
   "linkrel_equiv
     (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))\<circ>(basic ((cement cap) \<otimes> y1))\<circ>z1))
     (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
                     \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>?z4))\<circ>(basic ((cement cap) \<otimes> y1))\<circ>z1))"
             using  linkrel_equiv_def compose_leftassociativity 
             leftright_associativity r_into_rtranclp 
              by (metis (full_types))
   then show ?thesis by simp
   }
   qed
 (*we now need to use transitivity to combine the equivalences proved in above steps to prove the
  desired equivalence*)                      
 {
 have combine_vert: 
  "linkrel_equiv  (Abs_diagram (((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)))
                                \<circ>(basic ((cement cap) \<otimes>?z4))\<circ>(basic y1)\<circ> z1))
                  (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))"
             using step1 step2 rtranclp_trans linkrel_equiv_def Link.abs_eq_iff compose_Nil 
             compose_leftassociativity  
             by (metis 1 3   make_vert_induct_left make_vert_induct_right 2)                    
 have combine_cup:
  "linkrel_equiv 
      (Abs_diagram (((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)))
                   \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>?z4))\<circ>(basic ((cement cap)\<otimes>y1))\<circ> z1))
       (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using step3 combine_vert linkrel_equiv_def rtranclp_trans
               compose_leftassociativity leftright_associativity 
               step2 2 by (metis) 
 have combine_compress:
  "linkrel_equiv 
      (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))\<circ>(basic ((cement cap) \<otimes> y1))\<circ>z1))
      (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))"
               using combine_cup step4 rtranclp_trans  combine_cup step4  rtranclp_trans  
               linkrel_equiv_def  compose_leftassociativity leftright_associativity 
               step2 4 2 by metis 
 from combine_compress show ?thesis by (simp)
 }
qed


text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1\<circ> basic y2 \<circ>z1), 
where y2 is a block with outgoing strands, in the following section we prove 
that given link diagram  is equivalent to a link diagram in 
which there exists a cup appended to the left of y1  and two vertical strands to the left to y2*}


theorem metaequivalence_left_drop: 
 assumes "(snd (count y2))>1" 
  and "(z4 = make_vert_block (nat ((snd (count y2)) + (-2))+1))"
  and "w4 = make_vert_block  (nat ((snd (count y2)) + (-2)))" 
  and "fst (count y2) = snd (count y1)"
 shows "linkrel_equiv 
         (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2))
                       \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
         (Abs_diagram (x1 \<circ> (basic y1) \<circ>(basic ((cement cup)\<otimes>y2))
                       \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"
 proof- 
 let ?a = "(Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2))
           \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"
 let ?b = "(Abs_diagram ((x1 \<circ> (basic y1)) \<circ>(basic ((cement cup)\<otimes>y2))
           \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"
 have "  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.
          (?a = Abs_diagram ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))\<circ>(y2)) 
        \<and> (?b = Abs_diagram ((y1)\<circ>(basic (w1))\<circ>(basic (A\<otimes>w2))\<circ>(y2)))
        \<and> ((snd (count w1)) = (fst (count w2)))
        \<and> ((fst (count A)) = 0)
        \<and> (strands B))" 
  proof-
     have "fst (brickcount cup) = 0" using brickcount_def by auto
     then have "fst (count ((cement cup))) = 0" using count_def  count.simps(1) 
        by (metis)
     moreover then have " strands ((cement vert)\<otimes>(cement vert))" using  append_blocks_Nil strands_def 
       by (metis brickstrand.simps(1) strands.simps(1) strands.simps(2))
     ultimately show ?thesis using assms by (metis compose_leftassociativity leftright_associativity) 
  qed
  then have "linkrel_compbelow_centerright ?a ?b" 
        using linkrel_compbelow_centerright_def by auto
  then have "linkrel_compbelow ?a ?b" 
        using linkrel_compbelow_def by auto
  then have "linkrel_compress ?a ?b" 
        using linkrel_compress_def by auto
  then have " linkrel ?a ?b" 
         using linkrel_def by auto
  then have "linkrel_equiv ?a ?b" 
         using linkrel_equiv_def  r_into_rtranclp by (metis)
 then show ?thesis by (simp add: compose_leftassociativity) 
 qed

 theorem metaequivalence_left_doubledrop: 
 assumes "(snd (count y2))>1"
      and "w4 = make_vert_block  (nat ((snd (count y2)) + (-2)))" 
      and "fst (count y2) = snd (count y1)"
 shows "linkrel_equiv 
           (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2))
                         \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
           (Abs_diagram (x1 \<circ> basic y1\<circ> basic y2\<circ>z1))" 
 proof-
 let ?x = "x1 \<circ> (basic y1)"
 have 
  "linkrel_equiv 
    (Abs_diagram ((x1 \<circ> (basic y1)) \<circ>(basic ((cement cup)\<otimes>y2))
                 \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
    (Abs_diagram ((x1 \<circ> (basic y1)) \<circ> basic y2 \<circ>z1))"  
                using assms metaequivalence_left non_seperating_block_def by auto
 moreover have
   "linkrel_equiv 
       (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2))
                    \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
       (Abs_diagram (x1 \<circ> (basic y1) \<circ>(basic ((cement cup)\<otimes>y2))
                     \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"
           using assms metaequivalence_left_drop compose_leftassociativity by auto
  ultimately have 
  "linkrel_equiv 
       (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2))
                    \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
       (Abs_diagram (x1 \<circ> (basic y1) \<circ> basic y2 \<circ>z1))"  
          using   rtranclp_trans  Link.abs_eq_iff compose_leftassociativity assms 
          by metis
 from this show  ?thesis by simp
 qed

 lemma metaequivalence_left_doubledrop_condition:
 "(((snd (count y2))>1) 
 \<and>(w4 = make_vert_block  (nat ((snd (count y2)) + (-2))))
 \<and>(fst (count y2) = snd (count y1)))
\<Longrightarrow>
 (linkrel_equiv 
      (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2))
                   \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
      (Abs_diagram (x1 \<circ> (basic y1) \<circ> basic y2 \<circ>z1)))"
using metaequivalence_left_doubledrop by auto

text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1\<circ> basic y2 \<circ>z1), 
where y2 is a block with outgoing strands, in the following section we prove 
that given link diagram  is equivalent to a link diagram in 
which there exists a cup appended to the right of y1  and two vertical strands to the right to y2*}

theorem metaequivalence_right_drop: 
assumes "(snd (count y2))>1" 
 and "w4 = make_vert_block  (nat ((snd (count y2)) + (-2)))" 
 and "fst (count y2) = snd (count y1)"
shows 
  "linkrel_equiv 
          (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>(cement cup)))\<circ>(basic (y2\<otimes>(cement vert)\<otimes>(cement vert)))
                            \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
          (Abs_diagram (x1 \<circ> (basic y1) \<circ>(basic (y2\<otimes>(cement cup)))
                            \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
proof-
 let ?a = " (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>(cement cup)))\<circ>(basic (y2\<otimes>(cement vert)\<otimes>(cement vert)))
                         \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
 let ?b = "(Abs_diagram (x1 \<circ> (basic y1) \<circ>(basic (y2\<otimes>(cement cup)))
                           \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
 have "\<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.(
   (?a = Abs_diagram ((y1)\<circ>(basic (w1\<otimes>A))\<circ>(basic (w2\<otimes>B))\<circ>(y2))) 
  \<and>(?b = Abs_diagram ((y1)\<circ>(basic (w1))\<circ>(basic (w2\<otimes>A))\<circ>(y2)))
  \<and>((snd (count w1)) = (fst (count w2)))
  \<and>((fst (count A)) = 0)
  \<and>(strands B))" 
 proof- 
   have "fst (brickcount cup) = 0" using brickcount_def by auto
   then have "fst (count ((cement cup))) = 0" 
       using count_def  count.simps(1) by (metis)
   moreover have  " strands ((cement vert)\<otimes>(cement vert))" 
       using  append_blocks_Nil strands_def 
       by (metis brickstrand.simps(1) strands.simps(1) strands.simps(2))
   ultimately show ?thesis using assms(3)  by (metis)
   qed
 then have "linkrel_compbelow_centerleft ?a ?b" 
       using linkrel_compbelow_centerleft_def by auto
 then have "linkrel_compbelow ?a ?b" 
       using linkrel_compbelow_def by auto
 then have "linkrel_compress ?a ?b" 
       using linkrel_compress_def by auto
 then have " linkrel ?a ?b" 
       using linkrel_def by auto
 then have "linkrel_equiv ?a ?b" 
       using linkrel_equiv_def  r_into_rtranclp by (metis)
 then have 
      "linkrel_equiv 
         (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>(cement cup)))\<circ>(basic (y2\<otimes>(cement vert)\<otimes>(cement vert)))
                      \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
         (Abs_diagram (x1 \<circ> (basic y1) \<circ>(basic (y2\<otimes>(cement cup)))
                      \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
 by auto
 then show ?thesis by auto
qed

theorem metaequivalence_right_doubledrop: 
 assumes "(snd (count y2))>1" 
  and "w4 = make_vert_block  (nat ((snd (count y2)) + (-2)))" 
  and "fst (count y2) = snd (count y1)"
 shows "linkrel_equiv 
          (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>(cement cup)))\<circ>(basic (y2\<otimes>(cement vert)\<otimes>(cement vert)))
                        \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
          (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))" 
proof-
 let ?x = "x1 \<circ> (basic y1)"
 have 1: 
  "linkrel_equiv 
     (Abs_diagram ((x1 \<circ> (basic y1)) \<circ>(basic ((cement cup)\<otimes>y2))
                  \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
     (Abs_diagram ((x1 \<circ> (basic y1)) \<circ> basic y2 \<circ>z1))"  
                using assms metaequivalence_left non_seperating_block_def  by auto
 then have "linkrel_equiv 
      (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>(cement cup)))\<circ>(basic (y2\<otimes>(cement vert)\<otimes>(cement vert)))
                  \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
      (Abs_diagram (x1 \<circ> (basic y1) \<circ>(basic (y2\<otimes>(cement cup)))
                  \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
                 using metaequivalence_right_drop assms by auto
 then have  
     "linkrel_equiv 
         (Abs_diagram (((x1)\<circ>(basic (y1\<otimes>(cement cup))))
            \<circ>(basic (y2\<otimes>(cement vert)\<otimes>(cement vert)))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
         (Abs_diagram ((x1 \<circ> (basic y1)) \<circ> basic y2 \<circ>z1))" 
               using 1  rtranclp_trans Link.abs_eq_iff compose_leftassociativity assms
              by (metis compose_Nil metaequivalence_right make_vert_induct_left walls.distinct(1))
 then show  ?thesis using compose_leftassociativity by auto
qed



text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1\<circ> basic y2 \<circ>z1), 
where y2 is a block with outgoing strands, in the following section we prove  that given link 
diagram  is equivalent to an extended link diagram in which there exist  cups appended to the 
left and right of y1 and a pair of two vertical strands to the left and right of y2*}

theorem metaequivalence_both_doubledrop: 
assumes "(snd (count y2))>1" 
 and "w4 = make_vert_block  (nat ((snd (count y2)) + (-2)))" 
 and "w5 = make_vert_block (nat ((snd (count y2))))"
 and "fst (count y2) = snd (count y1)"
shows "linkrel_equiv 
             (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1\<otimes>(cement cup)))
                 \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2\<otimes>(cement vert)\<otimes>(cement vert)))
                 \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5)) 
                 \<circ> (basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
             (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))" 

proof-
 have 1: 
  "linkrel_equiv 
       (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>(cement cup)))\<circ>(basic (y2\<otimes>(cement vert)\<otimes>(cement vert)))
              \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
      (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))" 
    using assms metaequivalence_right_doubledrop by auto
 let ?p1 = "y1 \<otimes> (cement cup)"
 let ?p2 = "y2 \<otimes> (cement vert) \<otimes>(cement vert)"
 let ?p3 = "(basic (w4 \<otimes> (cement cap) \<otimes> (cement vert)))\<circ>z1"
 have  "(snd (count (x\<otimes>(cement vert)\<otimes>(cement vert)))) = (snd (count (x\<otimes>(cement vert))) + 1)"
   using append_blocks_Nil append_blocks_Cons brickcount_def count_def 
   by (metis (hide_lams, no_types) brickcount.simps(1) count.simps(1) count_rightcompose
      leftright_associativity snd_conv)
 then have 2:"(snd (count (y2\<otimes>(cement vert)\<otimes>(cement vert)))) = (snd (count (y2)) + 2)"
   using  append_blocks_Nil  append_blocks_Cons brickcount_def count_def 
   by (metis (hide_lams, no_types) brickcount.simps(1) count.simps(1) count_rightcompose
      dbl_def dbl_simps(3) snd_conv)
 then have "snd (count (y2 \<otimes> (cement vert) \<otimes> (cement vert))) > (snd (count y2))" 
   by auto
 then have 3: "snd (count (?p2)) > 1" 
   using assms  by auto
 have  "(fst (count (x\<otimes>(cement vert)\<otimes>(cement vert)))) = (fst (count (x\<otimes>(cement vert))) + 1)"
   using  append_blocks_Nil append_blocks_Cons brickcount_def count_def 
   by (metis (hide_lams, no_types) brickcount.simps(1) count.simps(1) count_rightcompose
     leftright_associativity fst_conv)
 then have "(fst (count (y2\<otimes>(cement vert)\<otimes>(cement vert)))) = (fst (count (y2)) + 2)"
    using  append_blocks_Nil append_blocks_Cons brickcount_def count_def
    by (metis (hide_lams, no_types) brickcount.simps(1) count.simps(1) count_rightcompose
    dbl_def dbl_simps(3) fst_conv)
 moreover have "(snd (count (y1\<otimes>(cement cup)))) = (snd (count y1)) + 2"
    using  count_def snd_conv append_blocks_Cons count_cup_rightcompose  by auto
 moreover then have "(snd (count (y1\<otimes>(cement cup)))) = ((fst (count y2)) +2)" 
    using assms by auto
 ultimately have 4: "fst (count ?p2) = snd (count ?p1)" 
      by auto
 from 2 have "snd (count ?p2) = (snd (count y2)) + 2"  
   by auto
 then have "w5 = make_vert_block (nat (((snd (count ?p2)) + (-2))))" 
    using assms by auto
 then have  "(((snd (count ?p2))>1) 
                   \<and> (w5= make_vert_block  (nat ((snd (count ?p2)) + (-2))))
                   \<and>(fst (count ?p2) = snd (count ?p1)))"
   using assms 3 4 by auto
 then  have 
   "linkrel_equiv 
         (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>?p1))\<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>?p2))
                      \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w5))\<circ>?p3))
         (Abs_diagram (x1 \<circ> basic ?p1\<circ> basic ?p2\<circ>?p3))"
    using metaequivalence_left_doubledrop_condition by auto
 then have 6: 
   "linkrel_equiv 
         (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1 \<otimes> (cement cup)))
               \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2 \<otimes> (cement vert) \<otimes>(cement vert)))
               \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w5))
               \<circ> (basic (w4 \<otimes> (cement cap) \<otimes> (cement vert)))\<circ>z1))
         (Abs_diagram (x1 \<circ> basic (y1 \<otimes> (cement cup))\<circ> basic (y2 \<otimes> (cement vert) \<otimes>(cement vert))
               \<circ>(basic (w4 \<otimes> (cement cap) \<otimes> (cement vert)))\<circ>z1))"
    using metaequivalence_left_doubledrop_condition  by auto
 then have 
  "linkrel_equiv 
        (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1 \<otimes> (cement cup)))
                     \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2 \<otimes> (cement vert) \<otimes>(cement vert)))
                     \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w5))
                     \<circ>(basic (w4 \<otimes> (cement cap) \<otimes> (cement vert)))\<circ>z1))
        (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))"
    using 1 rtranclp_trans Link.abs_eq_iff by (metis)
 then show ?thesis by (simp)
qed



text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1\<circ>z1), 
where y1 is a block with outgoing strands, in the following section we prove 
that given link diagram  is equivalent to a link diagram in 
which there exists a cup appended to the left of y1*}


theorem metaequivalence_top_drop: 
assumes "(snd (count y1))>1" 
 and "w4 = make_vert_block  (nat ((snd (count y1)) + (-2)))" 
 and "w5 = make_vert_block (nat ((snd (count y1))))"
 and "fst (count y2) = snd (count y1)"
shows 
  "linkrel_equiv 
          (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1\<otimes>(cement cup))) 
                        \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5)) 
                        \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
          (Abs_diagram (x1 \<circ> (basic y1)\<circ> z1))" 
proof-
 from metaequivalence_right and assms have 1: 
     "linkrel_equiv 
        (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>(cement cup)))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
        (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))" 
      by auto
 let ?y2 = "y1 \<otimes> (cement cup)"
 let ?z2 = "(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1"
 have 2:"(snd (count (?y2))) = (snd (count y1)) + 2"
      using  count_def snd_conv append_blocks_Cons count_cup_rightcompose by auto
 with assms have 3:"(snd (count (?y2))) >1" by auto
 from 2 have 4: "w5 = make_vert_block (nat (snd (count ?y2) + (-2)))" 
      using assms by auto
 with assms 3 metaequivalence_left have 
  "linkrel_equiv 
     (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>?y2))\<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))\<circ>?z2))
     (Abs_diagram ((x1)\<circ>(basic (?y2))\<circ>?z2))" 
     using non_seperating_block_def by metis
 then have 
   "linkrel_equiv 
      (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1\<otimes>(cement cup)))
                   \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                   \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
      (Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))" 
     by auto
 with 1 have 
  "linkrel_equiv 
      (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1\<otimes>(cement cup)))
                    \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                    \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
     (Abs_diagram (x1 \<circ> (basic y1)\<circ> z1))" 
    using rtranclp_trans Link.abs_eq_iff  by metis
 then show ?thesis by simp
qed



text{* Given a link diagram which represents a well defined wall of the form (x1 \<circ> basic y1\<circ> z1), 
where y1 is a block with outgoing strands, in the following section we prove that given link 
diagram  is equivalent to an extended link diagram in which there exist caps appended to the 
left and right of y1*}

theorem metaequivalence_bottom_doubledrag: 
assumes "(fst (count y1))>1" 
 and "w4 = make_vert_block  (nat ((fst (count y1)) + (-2)))" 
 and "w5 = make_vert_block (nat ((fst (count y1))))"
 and "well_defined (x1 \<circ> basic y1 \<circ> z1)" 
shows "linkrel_equiv 
        (Abs_diagram ((x1)\<circ>  (basic (w4\<otimes>(cement cup)\<otimes>(cement vert))) 
                     \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w5))
                     \<circ>(basic ((cement cap)\<otimes>y1\<otimes>(cement cap)))\<circ>z1))
        (Abs_diagram (x1 \<circ> (basic y1)\<circ> z1))" 
proof-
 have "(fst (count y1))>1" using assms by auto
 also have  "w4 = make_vert_block  (nat ((fst (count y1)) + (-2)))" 
      using assms by auto
 have "well_defined (x1 \<circ> basic y1 \<circ> z1)"  using assms by auto
 from assms and metaequivalence_bottomright have 1: 
   "linkrel_equiv 
      (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1))
      (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))"  
      by auto
 let ?y2 = "y1 \<otimes> (cement cap)"
 let ?x2 = "x1\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))"
 have 2:"(fst (count (?y2))) = (fst (count y1)) + 2"
      using count_def fst_conv append_blocks_Cons count_cup_rightcompose 
      by (metis brickcount.simps(3) count.simps(1) fst_count_additive)
 with assms have 3:
     "(fst (count (?y2))) >1" 
     by auto
 have 4: " snd (count (y1\<otimes>(cement cap))) = snd (count y1)" 
     using  count_def snd_conv append_blocks_Cons count_cup_rightcompose
     by (metis (hide_lams, no_types) brickcount.simps(3) comm_monoid_add_class.add.right_neutral 
     count.simps(1) snd_count_additive)
 have "snd (count (w4\<otimes>(cement cup)\<otimes>(cement vert))) = snd (count w4) + snd (count (cement cup)) +
       snd (count (cement vert))" using leftright_associativity snd_count_additive 
     by (auto)
 then have 5: "snd (count (w4\<otimes>(cement cup)\<otimes>(cement vert))) = snd (count w4) +3"
     using count_def  snd_conv by (metis ab_semigroup_add_class.add_ac(1) brickcount.simps(1) 
     brickcount.simps(2) count.simps(1) inc.simps(2) numeral_inc)
 have "fst (count (w4\<otimes>(cement cup)\<otimes>(cement vert))) 
            =  fst (count w4) + fst (count (cement cup)) + fst( count (cement vert))"
     using leftright_associativity fst_count_additive by auto
 then have 6: "fst (count (w4\<otimes>(cement cup)\<otimes>(cement vert))) =  fst (count w4) + 1"
     using count_def  fst_conv brickcount.simps(1) count.simps(1) fst_count_additive 
     fstcount_cup_rightcompose by (metis (full_types))
 have 7: "(fst (count w4)) = (int (nat ((fst (count y1)) + (-2))))+1" 
      using assms make_vert_block_fstequality by (metis)
 have "(fst (count y1) + (-2)) \<ge> 0" using assms by auto
 then have "(int (nat ((fst (count y1)) + (-2)))) = (fst (count y1) + (-2))" 
      using int_nat_eq assms by auto
 with 7
            have "fst (count w4) =  (fst (count y1)) + (-2) + 1" 
      by auto
 then have 8: "fst (count w4) = fst (count y1) + (-1)" by auto
 with make_vert_block_fstsndequality and assms have 
           "snd (count w4) =  fst (count y1) + (-1)"
      by auto
 with 5 have 
          "snd (count (w4\<otimes>(cement cup)\<otimes>(cement vert))) = fst (count y1) + (-1) + 3" 
      by auto
 with 2 have 9: 
           "snd (count (w4\<otimes>(cement cup)\<otimes>(cement vert))) = fst (count (y1\<otimes>(cement cap)))" 
      by auto
 from 8 and 6 have 10: 
          "fst (count (w4\<otimes>(cement cup)\<otimes>(cement vert))) = fst (count y1)" 
      by auto
 from 2 have 11: 
          "w5 = make_vert_block (nat (fst (count ?y2) + (-2)))" 
      using assms by auto
 have 12: "fst (wall_count ((basic y1)\<circ>z1)) = snd(wall_count x1)" 
      using assms diagram_fst_equals_snd by metis
 have  "fst (wall_count ((basic y1)\<circ>z1)) = fst(count y1)" 
      using wall_count_def compose_def by auto
 with 12 have "snd(wall_count x1) = (fst (count y1))" by simp
 with 10 have 13: 
          "snd(wall_count x1) = (fst (count (w4\<otimes>(cement cup)\<otimes>(cement vert))))" 
      by auto
 have 14:"snd (wall_count (x1\<circ>(basic y1))) = fst(wall_count z1)" 
      using assms diagram_fst_equals_snd by (metis compose_leftassociativity)
 have "snd (wall_count (x1\<circ>(basic y1))) = snd (count y1)" 
      using wall_count_def compose_def by (metis snd_conv wall_count.simps(1) wall_count_compose)
 from 14 and this have 15: "fst(wall_count z1) =  snd (count y1)" 
       by simp
 with 4 have 16: "fst(wall_count z1) = snd (count ?y2)" 
       by simp
 have "(fst (wall_count ((basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic ?y2)\<circ>z1))) 
        = fst (count (w4\<otimes>(cement cup)\<otimes>(cement vert)))"
       by auto
 with  13 have 17: 
        "snd(wall_count x1) 
         = (fst (wall_count ((basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic ?y2)\<circ>z1)))"
        by auto
 have  "list_sum (wall_count_list (?y2*z1)) = 0" 
        using 16 add_nonneg_eq_0_iff assms(4)compose_Nil diagram_list_sum_zero 
        diagram_wall_count_list_zero list_sum.simps(2) list_sum_append_blocks 
        monoid_add_class.add.left_neutral 15 wall_count_list.simps(2) 
        wall_count_list_compose wall_count_list_list_sum_non_negative 
        by (metis)
 then have 18: " list_sum (wall_count_list ((basic ?y2)\<circ>z1)) = 0" 
        by auto
 from 9 have 
        "snd (count (w4\<otimes>(cement cup)\<otimes>(cement vert))) = (fst (wall_count (((basic ?y2)\<circ>z1))))"
        by (metis fst_conv wall_count.simps(1) wall_count_compose)
 with 18
      have "list_sum (wall_count_list ((w4\<otimes>(cement cup)\<otimes>(cement vert))*((basic ?y2)\<circ>z1))) = 0"
      using add_nonneg_eq_0_iff assms(4) compose_Nil diagram_list_sum_zero 
      diagram_wall_count_list_zero list_sum.simps(2) list_sum_append_blocks 
      monoid_add_class.add.left_neutral 15 wall_count_list.simps(2) 
      wall_count_list_compose wall_count_list_list_sum_non_negative
      by (metis `fst (wall_count (basic y1 \<circ> z1)) = fst (count y1)` `
      snd (wall_count x1) = fst (count y1)` diff_self 16 9)
 then have 19: 
      "list_sum (wall_count_list ((basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>((basic ?y2)\<circ>z1))) = 0"
      by auto
 from diagram_list_sum_subsequence have 20: 
       " ((list_sum (wall_count_list x1) = 0)
        \<and>((list_sum (wall_count_list ((basic y1)\<circ>z1)))=0))" 
      using assms by metis
 have "
   list_sum (wall_count_list ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                \<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1)) 
    = list_sum (wall_count_list ((x1))) 
    + list_sum (wall_count_list ((basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                \<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1)) 
    + abs ((fst (wall_count ((basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                 \<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1))) 
            - (snd (wall_count x1)))"
        using wall_count_list_list_sum_compose by auto
 with 19 and 20 and 17 
     have 21: 
      "list_sum (wall_count_list ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                                  \<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1)) 
                         = 0"
         by (metis diff_self monoid_add_class.add.right_neutral wall_count_list_list_sum_abs)
 have 22: 
      "(fst (wall_count ((x1)\<circ>(basic y1)\<circ>z1))) = fst(wall_count x1)" 
        using wall_count_def compose_Cons by (metis fst_conv wall_count_compose)
 have "abs( fst(wall_count (x1 \<circ>(basic y1)\<circ>z1))) = 0" 
        using well_defined_fst_wall_count assms  by metis
 from 22 and this have 23:"abs (fst(wall_count x1)) = 0"  
        by auto
 have 24:" (snd (wall_count ((x1)\<circ>(basic y1)\<circ>z1))) = snd(wall_count z1)" 
        using wall_count_def compose_Cons 
        by (metis snd_conv wall_count_compose)
 have "abs( snd(wall_count (x1 \<circ>(basic y1)\<circ>z1))) = 0" 
        using well_defined_snd_wall_count assms by metis
 from 24 and this have 25:"abs (snd(wall_count z1)) = 0"  
        by auto
 have 26: 
  "(fst (wall_count (((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1))))
                         = fst(wall_count x1)" 
          using wall_count_def compose_Cons by (metis fst_conv wall_count_compose)
 with 23 have 27:
   "abs (fst (wall_count (((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
           \<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1)))) = 0" by auto
 have 28:" (snd (wall_count (((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
           \<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1))))
                      = snd (wall_count z1)" 
           using wall_count_def compose_Cons by (metis snd_conv wall_count_compose)
 from 24  and 25 and 28 and 21 have 29:
  "abs (snd (wall_count (((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
           \<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1))))=
                   0" 
            by auto
 from 27 and 29 and 21 have 30: 
   "well_defined  (((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1))" 
           using monoid_add_class.add.left_neutral well_defined_def by (auto)
 with assms and 3 and metaequivalence_bottomleft and 30
  have "linkrel_equiv 
       (Abs_diagram ((?x2)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes> w5))\<circ>(basic ((cement cap)\<otimes>?y2))\<circ>z1))
       (Abs_diagram ((?x2)\<circ>(basic (?y2))\<circ>z1))"
            using compose_leftassociativity 11 by (metis)
 then have 
   "linkrel_equiv
     (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
             \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes> w5))\<circ>(basic ((cement cap)\<otimes>y1\<otimes>(cement cap)))\<circ>z1))  
     (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1))" 
 using compose_leftassociativity by auto
 with 1 have 
   "linkrel_equiv 
       (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
             \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes> w5))\<circ>(basic ((cement cap)\<otimes>y1\<otimes>(cement cap)))\<circ>z1))   
       (Abs_diagram (x1 \<circ> (basic y1)\<circ> z1))" using rtranclp_trans Link.abs_eq_iff 
 by metis
 then show ?thesis by simp
qed



text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1\<circ> basic y2 \<circ>z1), 
where y1 is a block with incoming strands and y2 is a block with outgoing strands, 
in the following section we prove that given link diagram  is equivalent to a link diagram in 
which there exists a cap appended to the left of y1  and a cap to the right of  y2*}


theorem metaequivalence_positive_cross: 
assumes "(fst (count y1))>1" 
 and "(snd (count y2)) >1"
 and "w4 = make_vert_block  (nat ((fst (count y1)) + (-2)))" 
 and "w5 = make_vert_block (nat ((snd (count y2)) + (-2)))"
 and "well_defined (x1 \<circ> basic y1 \<circ> basic y2 \<circ>z1)" 
shows "linkrel_equiv 
           (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)) 
                 \<circ>(basic ((cement cap)\<otimes>y1))\<circ>(basic (y2\<otimes>(cement cup)))
                 \<circ>(basic (w5\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
           (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))" 
proof-
 have subresult: 
  "linkrel_equiv 
       (Abs_diagram ((x1)\<circ>  (basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
                    \<circ>(basic ((cement cap)\<otimes>y1))\<circ>(basic y2)\<circ>z1))
       (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))" using assms metaequivalence_bottomleft
    by auto
 let ?x2 = "(x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)) \<circ>(basic ((cement cap)\<otimes>y1))"
 have "linkrel_equiv 
          (Abs_diagram (?x2\<circ>(basic (y2\<otimes>(cement cup)))\<circ>(basic (w5\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
          (Abs_diagram (?x2\<circ>(basic y2)\<circ>z1))" using assms metaequivalence_right 
       by (metis (full_types))
 then have 
          "linkrel_equiv 
             (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
                           \<circ>(basic ((cement cap)\<otimes>y1))\<circ>(basic (y2\<otimes>(cement cup)))
                           \<circ>(basic (w5\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
             (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))\<circ>(basic ((cement cap)\<otimes>y1))
                           \<circ>(basic y2)\<circ>z1))"
       using compose_leftassociativity by (auto)
 with subresult have 
   "linkrel_equiv  
        (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)) \<circ>(basic ((cement cap)\<otimes>y1))
                      \<circ>(basic (y2\<otimes>(cement cup)))\<circ>(basic (w5\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
        (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))"
         using rtranclp_trans Link.abs_eq_iff by metis
 then show ?thesis by simp
qed



text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1\<circ> basic y2 \<circ>z1), 
where y1 is a block with incoming strands and y2 is a block with outgoing strands, in the 
following section we prove that given link diagram  is equivalent to an extended link diagram in 
which there exists a cap appended to the right of y1  and a cup to the left to y2*}

theorem metaequivalence_negative_cross: 
assumes "(fst (count y1))>1" 
 and "(snd (count y2)) >1"
 and "w4 = make_vert_block  (nat ((fst (count y1)) + (-2)))" 
 and "w5 = make_vert_block (nat ((snd (count y2)) + (-2)))"
 and "well_defined (x1 \<circ> basic y1 \<circ> basic y2 \<circ>z1)" 
shows 
  "linkrel_equiv 
        (Abs_diagram ((x1)\<circ>  (basic (w4\<otimes>(cement cup)\<otimes>(cement vert))) 
                     \<circ>(basic (y1 \<otimes>(cement cap)))\<circ>(basic ((cement cup)\<otimes>y2))
                     \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w5))\<circ>z1))
        (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))" 
proof-
 have subresult: 
  "linkrel_equiv 
        (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert))) \<circ>(basic (y1\<otimes>(cement cap)))
                     \<circ>(basic y2)\<circ>z1))
         (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))" 
        using assms metaequivalence_bottomright by auto
 let ?x2 = "(x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert))) \<circ>(basic (y1 \<otimes>(cement cap)))"
 have "linkrel_equiv 
          (Abs_diagram (?x2\<circ>(basic ((cement cup)\<otimes>y2))
                       \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w5))\<circ>z1))
           (Abs_diagram (?x2\<circ>(basic y2)\<circ>z1))" 
         using assms metaequivalence_left non_seperating_block_def by (metis (full_types))
 then have 
     "linkrel_equiv 
           (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert))) \<circ>(basic (y1 \<otimes>(cement cap)))
                         \<circ>(basic ((cement cup)\<otimes>y2))\<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w5))\<circ>z1))
           (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert))) \<circ>(basic (y1 \<otimes>(cement cap)))
                         \<circ>(basic y2)\<circ>z1))"
           using compose_leftassociativity by auto
 from subresult and this have 
     "linkrel_equiv 
           (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                                 \<circ>(basic (y1 \<otimes>(cement cap)))\<circ>(basic ((cement cup)\<otimes>y2))
                                  \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w5))\<circ>z1))
           (Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic y2)\<circ>z1))"
              using Link.abs_eq_iff by (metis)
 then show ?thesis by simp
qed



text{* Given a link diagram which represents a wall of the form 
(x1 \<circ> basic y1\<circ> basic y2 \<circ> basic y3 \<circ>z1) such that 
 y2 is a block with outgoing strands ,the number of outgoing strands of y1 are equal to 
the number of incoming strand of y2 and the number of outgoing strands of y2 are equal to the 
number of incoming strand of y2. In the following theorem we prove that given link diagram  is 
equivalent to a link diagram in which there exists a cup appended to the left of y1  and two 
vertical strands to the left to y2*}

theorem metaequivalence_thriple_drop: 
assumes "(snd (count y3))>1" 
 and "w4 = make_vert_block  (nat ((snd (count y3)) + (-2)))" 
 and "w5 = make_vert_block (nat ((snd (count y3))))"
 and "fst (count y2) = snd (count y1)"
 and "(fst (count y3)) = (snd (count y2))"
shows 
 "linkrel_equiv 
       (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1\<otimes>(cement cup)))
                     \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2\<otimes>(cement vert)\<otimes>(cement vert)))
                     \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                     \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                     \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
       (Abs_diagram (x1 \<circ> (basic y1)\<circ>(basic y2)\<circ>(basic y3)\<circ>z1))" 
proof-
 let ?x2 = "x1\<circ> (basic y1)"
 have  "linkrel_equiv 
           (Abs_diagram (?x2\<circ>(basic ((cement cup)\<otimes>y2\<otimes>(cement cup)))
                        \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                        \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                        \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
            (Abs_diagram (?x2\<circ>(basic y2)\<circ>(basic y3)\<circ>z1))" 
       using metaequivalence_both_doubledrop assms by auto
 then have 1:
 "linkrel_equiv 
      (Abs_diagram (x1\<circ> (basic y1)\<circ>(basic ((cement cup)\<otimes>y2\<otimes>(cement cup)))
                 \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                 \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5)) \<circ> (basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
      (Abs_diagram (x1\<circ> (basic y1)\<circ>(basic y2)\<circ>(basic y3)\<circ>z1))" 
    using compose_leftassociativity by simp
 have 2: "fst (count (cement cup)) = 0" 
       using count_def add_left_cancel comm_monoid_add_class.add.right_neutral fst_count_additive 
       fstcount_cup_rightcompose by (auto)
 let ?z2 = "(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
            \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1"
 let ?w2 = "y2 \<otimes> (cement cup)"
 have "fst (count ?w2) = fst (count y2)" 
        using fstcount_cup_rightcompose by auto
 with assms have 3:"fst (count ?w2) = snd (count y1)" 
        by auto
 let ?B = "(cement vert) \<otimes> (cement vert)"
 have 4: "strands ?B"
        using append_blocks.append_blocks_Nil make_vert_block.simps(1) strand_make_vert_block 
        strands.simps(2) by (metis)
 from 4 and 2 and 3 and exI  have 
       "(strands ?B) \<and> (fst (count ?w2) = snd (count y1)) \<and> (fst (count (cement cup)) = 0)"
        by auto
 with exI and linkrel_compbelow_centerright_def have 
        "linkrel_compbelow_centerright 
              (Abs_diagram (x1 \<circ> (basic ((cement cup) \<otimes> y1)) \<circ> (basic (?B\<otimes> ?w2)) \<circ> ?z2))
              (Abs_diagram (x1 \<circ> (basic ( y1)) \<circ> (basic ((cement cup) \<otimes> ?w2)) \<circ> ?z2))"
        by metis
 with compose_leftassociativity and leftright_associativity have 
       "linkrel_compbelow_centerright 
             (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
                           \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2\<otimes>(cement cup)))
                           \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                           \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                           \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
             (Abs_diagram (x1\<circ>(basic y1)\<circ>(basic ((cement cup)\<otimes>y2\<otimes>(cement cup)))
                            \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                            \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                            \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
        by auto
 then have
 "linkrel_compbelow 
    (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
                 \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2\<otimes>(cement cup)))
                 \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                 \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                 \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
   (Abs_diagram (x1\<circ>(basic y1)\<circ>(basic ((cement cup)\<otimes>y2\<otimes>(cement cup)))
                \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
   using linkrel_compbelow_def by auto
 then have 
  "linkrel_compress
     (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
                  \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2\<otimes>(cement cup)))
                  \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                  \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                  \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
    (Abs_diagram (x1\<circ>(basic y1)\<circ>(basic ((cement cup)\<otimes>y2\<otimes>(cement cup)))
                  \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                  \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                  \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))" 
      using linkrel_compress_def by auto
 then have
  "linkrel
      (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
                   \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2\<otimes>(cement cup)))
                   \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                   \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                    \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
         (Abs_diagram (x1\<circ>(basic y1)\<circ>(basic ((cement cup)\<otimes>y2\<otimes>(cement cup)))
                    \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                    \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                    \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
     using linkrel_def by auto
 then have 
 "linkrel_equiv
        (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
               \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2\<otimes>(cement cup)))
               \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
               \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5)) \<circ> (basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))
                \<circ>z1))
         (Abs_diagram (x1\<circ>(basic y1)\<circ>(basic ((cement cup)\<otimes>y2\<otimes>(cement cup)))
                      \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                      \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5)) 
                      \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
     using linkrel_equiv_def r_into_rtranclp by metis
 with 1 and r_into_rtranclp rtranclp_trans have 5:
     "linkrel_equiv
             (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
                \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2\<otimes>(cement cup)))
                \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5)) \<circ> (basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))
                \<circ>z1))
             (Abs_diagram (x1\<circ>(basic y1)\<circ>(basic y2)\<circ>(basic y3)\<circ>z1))"
      by (metis Link.abs_eq_iff compose_Nil)
 have "snd (count ((cement cup) \<otimes> y1)) = 2 + snd (count y1)" 
       using snd_count_additive comm_semiring_1_class.normalizing_semiring_rules(24) 
       count_cup_rightcompose snd_conv snd_count_additive by metis
 with assms have 6: "snd (count ((cement cup) \<otimes> y1)) = 2 + fst (count y2)" 
       by auto
 let ?subs1 = "((cement cup) \<otimes> y1)"
 let ?subs2 = " ((cement vert) \<otimes> (cement vert) \<otimes> y2)"
 have " fst (count ((cement vert) \<otimes> (cement vert) \<otimes> y2)) = 2 + fst (count y2)"
       using fst_count_additive  by auto 
 with 6 have "snd (count (?subs1)) = fst (count (?subs2))" 
       by auto
 with 2 and 4 have
    "(strands ?B) \<and> (fst (count ?subs2) = snd (count ?subs1)) \<and> (fst (count (cement cup)) = 0)" 
       by auto
 with exI and linkrel_compbelow_centerleft_def  
 have "linkrel_compbelow_centerleft
          (Abs_diagram ((x1)\<circ>(basic (?subs1 \<otimes> (cement cup)))\<circ>(basic (?subs2\<otimes>?B))\<circ>?z2))
          (Abs_diagram ((x1)\<circ>(basic (?subs1))\<circ>(basic (?subs2\<otimes>(cement cup)))\<circ>?z2))"  
      by metis
 with leftright_associativity have
 "linkrel_compbelow_centerleft
          (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1 \<otimes> (cement cup)))
                    \<circ>(basic ((cement vert)\<otimes>(cement vert) \<otimes> y2 \<otimes> (cement vert) \<otimes> (cement vert)))
                    \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                    \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                    \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
          (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
                    \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2\<otimes>(cement cup)))
                    \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                    \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                    \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"      
        by auto
 with linkrel_compbelow_def have
  "linkrel_compbelow
          (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1 \<otimes> (cement cup)))
                      \<circ>(basic ((cement vert)\<otimes>(cement vert) \<otimes> y2 \<otimes> (cement vert) \<otimes> (cement vert)))
                      \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                      \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                      \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
           (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
                        \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2\<otimes>(cement cup)))
                        \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                        \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                        \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
     by auto
 with linkrel_compress_def and linkrel_def have
 "linkrel
    (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1 \<otimes> (cement cup)))
           \<circ>(basic ((cement vert)\<otimes>(cement vert) \<otimes> y2 \<otimes> (cement vert) \<otimes> (cement vert)))
           \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
           \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5)) 
           \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
     (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
           \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2\<otimes>(cement cup)))
           \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
           \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
     by auto
 with  linkrel_equiv_def and  r_into_rtranclp have
 "linkrel_equiv
    (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1 \<otimes> (cement cup)))
             \<circ>(basic ((cement vert)\<otimes>(cement vert) \<otimes> y2 \<otimes> (cement vert) \<otimes> (cement vert)))
             \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
             \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
    (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
            \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2\<otimes>(cement cup)))
            \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
            \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))" 
       by metis
 with 5 and r_into_rtranclp rtranclp_trans have
  "linkrel_equiv
      (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1 \<otimes> (cement cup)))
                  \<circ>(basic ((cement vert)\<otimes>(cement vert) \<otimes> y2 \<otimes> (cement vert) \<otimes> (cement vert)))
                  \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                  \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5)) 
                  \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
       (Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic y2)\<circ>(basic y3)\<circ>z1))"
         by (metis Link.abs_eq_iff compose_Nil)
 then show ?thesis by auto
qed
end
