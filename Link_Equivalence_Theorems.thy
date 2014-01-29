theory Link_Equivalence_Theorems
imports Tangles
begin

text{* We prove a set of theorems which prove equivalence of certain class of link diagrams. These
equivalences are useful in practise to prove equivalence of two given link diagrams. These theorems
also enable to understand why the defined relations are sufficient*}

text {* The following function constructs a block of n-vertical strands for a given n. *}

primrec make_vert_block:: "nat \<Rightarrow> block"
where
"make_vert_block 0 = (cement vert)"
|"make_vert_block (Suc n) = vert#(make_vert_block n)"

lemma strand_make_vert_block: " strands (make_vert_block n)" 
  apply(induct_tac n)
  apply(auto)
  done

lemma test_00: "(make_vert_block (n+1)) = vert#(make_vert_block n)" by auto

lemma test_0: "(make_vert_block (n+1)) = (cement vert)\<otimes>(make_vert_block n)" 
                   using test_00 append_blocks_Nil by metis


lemma test_1: "(make_vert_block (n+1)) = (make_vert_block n)\<otimes>(cement vert)" 
  apply(induct_tac n)
  apply(auto)
  apply (metis Tangles.append_blocks.append_blocks_Nil leftright_associativity)
  done

type_synonym convert = "block => nat"

definition fstcount:: convert  where "(fstcount x) = (nat (abs ((fst (count x)))))"

definition sndcount:: convert  where "(sndcount x) = (nat (snd (count x)))"

lemma make_vert_block_fstequality:"(fst (count (make_vert_block n))) = (int n)+1" 
  apply (induct_tac n)
  apply(auto)
  done

lemma make_vert_block_sndequality:"(snd (count (make_vert_block n))) = (int n)+1" 
  apply (induct_tac n)
  apply(auto)
  done

lemma make_vert_block_fstsndequality:
"(fst (count (make_vert_block n))) = (snd (count (make_vert_block n)))" 
   apply (induct_tac n)
   apply(auto)
   done

lemma nat_int:" ((int n)\<ge> 0)" by auto

lemma make_vert_blocks_positiveblock_length:"(fst (count (make_vert_block n)))>0" 
  using  nat_int make_vert_block_fstequality
  by auto



text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1 \<circ>z1), where y1 is a 
block with outgoing strands, the following theorem proves that it is equivalent to the link 
diagram obtained by adding two blocks of vertical strands above y1*}

theorem linkrel_doublecompress_top: 
assumes "(snd (count y1))>1" and "(z4 = make_vert_block (nat ((snd (count y1)) + (-2))+1))"
and "w4 = make_vert_block  (nat ((snd (count y1)) + (-2)))"
shows "linkrel_equiv (Abs_diagram (x1 \<circ> basic y1 \<circ> basic z4\<circ>basic z4\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 

proof-
 let ?k = " (nat ((snd (count y1))+ (-2) ))" 
 have C: " (z4 = make_vert_block (?k+1))" using assms by auto
 let ?x2 = "x1 \<circ> (basic y1)"
 have preliminary_result1:"((snd (count y1))+(-1))>0" using assms by auto
 have preliminary_result2:"((snd (count y1))+(-2))\<ge>0" using assms by auto
 have preliminary_result3: "strands z4" using C strand_make_vert_block by auto
 have subresult0: "snd (wall_count ?x2) = snd (wall_count (basic y1))" 
           using wall_count_compose 
             by auto
 have subresult1: "... = snd (count y1)" using wall_count_compose 
            by auto
 have subresult2: "snd (wall_count ?x2) > 0"
            using subresult1 assms less_trans subresult0 zero_less_one 
            by auto
 have subresult3: "fst (count (z4)) = fst (count (make_vert_block (?k+1)))"  
            using C make_vert_block_fstequality
            by auto
 have subresult4: "fst (count (make_vert_block (?k+1))) = int(?k+1)+1"  
            using make_vert_block_fstequality
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
"(linkrel_compress_null ((Abs_diagram (?x2\<circ>(basic z4)\<circ>z1))) (Abs_diagram (?x2\<circ>z1)))" 
           using linkrel_compress_null_def
           preliminary_result3 subresult0 subresult2
             by metis
 have subresult_equiv1: 
 "(linkrel_equiv ((Abs_diagram (?x2\<circ>(basic z4)\<circ>z1))) (Abs_diagram (?x2\<circ>z1)))" 
           using r_into_rtranclp subresult_compress1 linkrel_equiv_def linkrel_def  
           linkrel_compress_def
                     by (metis)
 have subresult_compress2: 
 "(linkrel_compress_null ((Abs_diagram ((?x2 \<circ> basic z4)\<circ>(basic z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ> basic z4)\<circ>z1)))" 
               using linkrel_compress_null_def preliminary_result3 subresult0 subresult2   
               compose_leftassociativity
                    by (metis)
 have subresult_equiv2: 
 "(linkrel_equiv ((Abs_diagram ((?x2 \<circ> basic z4)\<circ>(basic z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ> basic z4)\<circ>z1)))" 
               using linkrel_compress_def linkrel_def linkrel_equiv_def
               r_into_rtranclp subresult_compress2   
                    by (metis)
 have subresult_equiv3: 
"linkrel_equiv ((Abs_diagram ((?x2 \<circ> basic z4)\<circ>(basic z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ>z1)))" 
               using linkrel_equiv_def rtranclp_trans subresult_equiv1 subresult_equiv2 
               compose_leftassociativity
                            by (metis) 
 have step1: 
 "linkrel_equiv (Abs_diagram (x1 \<circ> basic y1 \<circ> basic z4\<circ>basic z4\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using compose_leftassociativity subresult_equiv3 
               by auto
 from step1 show ?thesis by auto
 qed


text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1 \<circ>z1), where y1 is a 
block with outgoing strands, the following theorem proves that it is equivalent to the link 
diagram obtained by adding two blocks of vertical strands below y1*}

theorem linkrel_doublecompress_below:
 assumes "(snd (wall_count x1))>1" 
 and "(z4 = make_vert_block (nat ((snd (wall_count x1)) + (-2))+1))"
 and "w4 = make_vert_block  (nat ((snd (wall_count x1)) + (-2)))"
 shows "linkrel_equiv (Abs_diagram (x1 \<circ> basic z4\<circ>basic z4 \<circ> basic y1\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))" 
 proof-    
 let ?k = " (nat ((snd (wall_count x1))+ (-2) ))" 
 have C: " (z4 = make_vert_block (?k+1))" using assms by auto
 let ?x2 = "x1 \<circ> (basic y1)"
 have preliminary_result1:"((snd (wall_count x1))+(-1))>0" using assms by auto
 have preliminary_result2:"((snd (wall_count x1))+(-2))\<ge>0" using assms by auto
 have preliminary_result3: "strands z4" using C strand_make_vert_block by auto
 have subresult3: "fst (count (z4)) = fst (count (make_vert_block (?k+1)))"  
            using C make_vert_block_fstequality
            by auto
 have subresult4: "fst (count (make_vert_block (?k+1))) = int(?k+1)+1"  
            using make_vert_block_fstequality
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
 "(linkrel_compress_null ((Abs_diagram (x1\<circ>(basic z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1)))" 
           using linkrel_compress_null_def preliminary_result3 subresult8  C 
           comm_semiring_1_class.normalizing_semiring_rules(24) make_vert_block_fstequality 
           monoid_add_class.add.left_neutral of_nat_Suc zless_iff_Suc_zadd by (metis)
 have subresult_equiv1: 
 "(linkrel_equiv  ((Abs_diagram (x1\<circ>(basic z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1)))" 
           using r_into_rtranclp subresult_compress1 linkrel_equiv_def linkrel_def  
           linkrel_compress_def
                     by (metis)
 have subresult_compress2: 
 "(linkrel_compress_null  ((Abs_diagram (x1\<circ>(basic z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1))) " 
               using linkrel_compress_null_def preliminary_result3   
               compose_leftassociativity subresult_compress1
                   by auto          
 let ?z2 = "((basic z4)\<circ>(basic y1)\<circ>z1)"
 have subresult_equiv2: 
 "(linkrel_compress_null (Abs_diagram (x1 \<circ> (basic z4)\<circ>(?z2)))
                           (Abs_diagram (x1\<circ>(?z2))))"
               using linkrel_compress_null_def  C
               C comm_semiring_1_class.normalizing_semiring_rules(24) 
               int_one_le_iff_zero_less make_vert_block_fstequality preliminary_result3 
               subresult8 zle_iff_zadd
               by metis

 have subresult_equiv3: 
 "linkrel_equiv (Abs_diagram (x1 \<circ> (basic z4)\<circ>(?z2))) 
                            (Abs_diagram (x1 \<circ> (?z2)))" 
               using linkrel_equiv_def linkrel_compress_def subresult_equiv2
                        by (metis (full_types) r_into_rtranclp linkrel_def)
 have subresult_equiv4: 
 "linkrel_equiv (Abs_diagram (x1 \<circ> basic z4\<circ>basic z4 \<circ> basic y1\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> (basic z4)\<circ>(basic y1)\<circ>z1))" 
               using compose_leftassociativity subresult_equiv3
               by auto
 have step1: 
 "linkrel_equiv (Abs_diagram (x1 \<circ> basic z4\<circ>basic z4 \<circ> basic y1\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))" 
               using compose_leftassociativity subresult_equiv3 subresult_equiv1 rtranclp_trans
               by (metis (full_types) Link.abs_eq_iff )
 from step1 show ?thesis by auto
 qed

(*metaequivalence moves*)

text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1 \<circ>z1), where y1 is a 
block with outgoing strands, the following theorem proves that it is equivalent to a link 
diagram in which there exists a block appended to the left of y1 *}

theorem metaequivalence_left: 
 assumes "(snd (count y1))>1"
 and "w4 = make_vert_block  (nat ((snd (count y1)) + (-2)))"
 shows "linkrel_equiv 
 (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
             (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
proof-
 let ?z4 = "make_vert_block (nat ((snd (count y1)) + (-2))+1)"                                                                                           
 let ?k = " (nat ((snd (count y1))+ (-2) ))" 
 have C: " (?z4 = make_vert_block (?k+1))" using assms by auto
 let ?x2 = "x1 \<circ> (basic y1)"
 have preliminary_result1:"((snd (count y1))+(-1))>0" using assms by auto
 have preliminary_result2:"((snd (count y1))+(-2))\<ge>0" using assms by auto
 have preliminary_result3: "strands ?z4" using C strand_make_vert_block by auto
 have subresult0: "snd (wall_count ?x2) = snd (wall_count (basic y1))" 
           using wall_count_compose 
             by auto
 have subresult1: "... = snd (count y1)" using wall_count_compose 
            by auto
 have subresult2: "snd (wall_count ?x2) > 0"
            using subresult1 assms less_trans subresult0 zero_less_one 
            by auto
 have subresult3: "fst (count (?z4)) = fst (count (make_vert_block (?k+1)))"  
            using C make_vert_block_fstequality
            by auto
 have subresult4: "fst (count (make_vert_block (?k+1))) = int(?k+1)+1"  
            using make_vert_block_fstequality
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
 "(linkrel_compress_null ((Abs_diagram (?x2\<circ>(basic ?z4)\<circ>z1))) (Abs_diagram (?x2\<circ>z1)))" 
           using linkrel_compress_null_def
           preliminary_result3 subresult0 subresult2
             by metis
 have subresult_equiv1: 
 "(linkrel_equiv ((Abs_diagram (?x2\<circ>(basic ?z4)\<circ>z1))) (Abs_diagram (?x2\<circ>z1)))" 
           using r_into_rtranclp subresult_compress1 linkrel_equiv_def linkrel_def  
           linkrel_compress_def
                     by (metis)
 have subresult_compress2: 
 "(linkrel_compress_null ((Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>(basic ?z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>z1)))" 
               using linkrel_compress_null_def preliminary_result3 subresult0 subresult2   
               compose_leftassociativity
                    by (metis)
 have subresult_equiv2: 
 "(linkrel_equiv ((Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>(basic ?z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>z1)))" 
               using linkrel_compress_def linkrel_def linkrel_equiv_def
               r_into_rtranclp subresult_compress2   
                    by (metis)
 have subresult_equiv3: 
 "linkrel_equiv ((Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>(basic ?z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ>z1)))" 
               using linkrel_equiv_def rtranclp_trans subresult_equiv1 subresult_equiv2 
               compose_leftassociativity
                            by (metis) 
 have step1: 
"linkrel_equiv (Abs_diagram (x1 \<circ> basic y1 \<circ> basic ?z4\<circ>basic ?z4\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using compose_leftassociativity subresult_equiv3 
               by auto
(*step2*)
 have w_subst: "w4 = (make_vert_block ?k)" using assms by auto
 have step2_subresult0: "(make_vert_block (?k+1)) = ((cement vert)\<otimes>(make_vert_block ?k))" 
  apply(simp)
  done
 have step2_subresult1:"?z4 = (cement vert)\<otimes>(make_vert_block ?k)" using C step2_subresult0 by auto
 have step2_subresult2: "(Abs_diagram (?x2 \<circ> (basic ?z4) \<circ>(basic ?z4)\<circ>z1)) =
 (Abs_diagram (?x2  \<circ> (basic ((cement vert)\<otimes>w4))\<circ> (basic ((cement vert) \<otimes>w4))\<circ>z1))" 
                        using w_subst step2_subresult1 by auto
 have step2_subresult3: "(snd (count w4)) = (fst (count w4))" using make_vert_block_fstsndequality 
                         w_subst by auto
 let ?x = "(Abs_diagram (?x2 \<circ>(basic ((cement cup)\<otimes>(cement vert)\<otimes>w4))
                        \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"
 let ?y = "(Abs_diagram (?x2 \<circ>(basic ((cement vert)\<otimes>w4))\<circ>(basic ((cement vert)\<otimes>w4))\<circ>z1))"
 have step2_subresult4:
  "\<exists>y1.\<exists>y2.\<exists>w1.\<exists>w2.
  (?x = Abs_diagram (y1 \<circ> (basic ((cement cup) \<otimes> (cement vert) \<otimes> w1)) 
                  \<circ> (basic ((cement vert) \<otimes> (cement cap) \<otimes> w2)) \<circ> y2))"
  using exI by auto
 have step2_subresult5:
   "\<exists>y1.\<exists>y2.\<exists>w1.\<exists>w2.
      (?y = Abs_diagram (y1 \<circ> (basic ((cement vert) \<otimes> w1)) \<circ> (basic ((cement vert) \<otimes> w2)) \<circ> y2))"
 using exI by auto
 have step2_subresult6: 
  "(\<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.
     ((?x = Abs_diagram ((y1)\<circ>(basic ((cement cup)\<otimes>(cement vert)\<otimes>w1)
           \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w2)))\<circ>(y2)))
    \<and>(?y = Abs_diagram ((y1)\<circ>(basic ((cement vert)\<otimes>w1))\<circ>(basic ((cement vert)\<otimes>w2))\<circ>(y2))))
    \<and> ((snd (count w1)) = (fst (count w2))))"
   using  step2_subresult3 exI by auto
 have step2_subresult7:
   " linkrel_straighten_rightdowntop ?x ?y"
     using linkrel_straighten_rightdowntop_def step2_subresult6 by auto
 have step2_subresult8:"linkrel ?x ?y" 
  using linkrel_def linkrel_straighten_def step2_subresult7 by auto
 have step2_subresult9: "linkrel (Abs_diagram ((?x2) \<circ>(basic ((cement cup)\<otimes>(cement vert)\<otimes>w4))
                             \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1)) 
              (Abs_diagram ((?x2) \<circ>(basic ((cement vert)\<otimes>w4))\<circ>(basic ((cement vert)\<otimes>w4))\<circ>z1))"
               using step2_subresult8 by auto 
 have step2_equiv1: "linkrel_equiv (Abs_diagram (x1\<circ>basic y1\<circ>(basic ((cement cup)\<otimes>(cement vert)\<otimes>w4))
                              \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1)) 
              (Abs_diagram (x1\<circ>basic y1 \<circ>(basic ((cement vert)\<otimes>w4))\<circ>(basic ((cement vert)\<otimes>w4))\<circ>z1))"
               using step2_subresult9 compose_leftassociativity r_into_rtranclp 
               linkrel_equiv_def
                     by metis
 have step2: "linkrel_equiv (Abs_diagram (x1\<circ>basic y1\<circ>(basic ((cement cup)\<otimes>?z4))\<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1)) 
              (Abs_diagram (x1\<circ>basic y1 \<circ>(basic ?z4)\<circ>(basic (?z4))\<circ>z1))"
               using  step2_subresult9 compose_leftassociativity r_into_rtranclp 
               linkrel_equiv_def step2_subresult1 w_subst
                     by (metis)
(*step 3*)
 have step3_preliminary1: "fst (count (v\<otimes>w)) = fst (count (cup#(v\<otimes>w)))" using count_def brickcount_def
   by auto
 have step3_preliminary2 : 
  "count ((cup)#((cement cup)\<otimes>w4)) = (fst (brickcount (cup)) + fst (count ((cement cup)\<otimes>w4)),
  snd (brickcount (cup)) + snd (count ((cement cup)\<otimes>w4)))"
 using count_def by auto
 have step3_preliminary3: 
  "((cement cup)\<otimes>((cement vert)\<otimes>w4)) = cup#((cement vert)\<otimes>w4)" using append_blocks_Nil by metis
 have step3_subresult0 : 
   "fst (count ((cup)#((cement cup)\<otimes>w4))) =  (fst (brickcount (cup)) + fst (count ((cement cup)\<otimes>w4)))"
     using count_def  brickcount_def by auto
 have step3_preliminary4 : 
   "(fst (brickcount (cup)) + fst (count ((cement cup)\<otimes>w4))) = fst (count ((cement cup)\<otimes>w4))"
   using brickcount_def by auto
 have step3_preliminary5:
  "fst (count (cup#((cement cup)\<otimes>w4))) =  fst (count ((cement cup)\<otimes>w4))"
   using  step3_preliminary4 step3_subresult0 by auto
 have step3_preliminary6:
    "fst (count (((cement cup))\<otimes>((cement cup)\<otimes>w4))) =  fst (count (cup#((cement cup)\<otimes>w4)))"
  using step3_preliminary3 
   by (metis Tangles.append_blocks.append_blocks_Nil)
 have step3_preliminary7:
  "fst (count (((cement cup))\<otimes>((cement cup)\<otimes>w4))) =  fst (count ((cement cup)\<otimes>w4))"
 using step3_preliminary5  step3_preliminary6 
  by auto
 have step3_subresult1 :"fst (wall_count (basic ((cement cup)\<otimes>(cement vert)\<otimes>w4))) 
                  = fst (wall_count (basic ((cement vert)\<otimes>w4))) " 
   using wall_count_def step3_preliminary7
      by (metis append_blocks.append_blocks_Nil add_diff_cancel 
   comm_monoid_add_class.add.left_neutral count.simps(2) fst_conv wall_count.simps(1))
 have step3_subresult2: "fst (wall_count (basic ((cement vert)\<otimes>w4))) = snd (count y1)" 
               using w_subst step2_subresult1 subresult8 by auto
 have step3_subresult3: "fst (wall_count (basic ((cement cup)\<otimes>(cement vert)\<otimes>w4))) = snd (count y1)" 
               using step3_subresult1 step3_subresult2 by auto 
 have step3_subresult4: "fst (wall_count (basic ((cement vert)\<otimes>w4))) = snd (wall_count ?x2)" 
               using step3_subresult3 subresult0 wall_count_def step3_subresult2 subresult1 by auto 
 have step3_subresult5: "fst (wall_count (basic ((cement vert)\<otimes>w4))) 
          = snd (wall_count (x1\<circ>(basic y1)))" 
               using step3_subresult4  wall_count_def by auto
 have step3_subresult6: "fst (brickcount cup) =  0" using brickcount_def by auto
 have step3_subresult7: "fst (count (cement cup)) =  0" using  count_def step3_subresult6 
    by (metis count.simps(1))
 have step3_subresult8: "strands (vert#(cement vert))" using  append_blocks_def strands_def  
   brickstrand.simps(1) strands.simps(1) strands.simps(2) 
                       by metis
 have step3_subresult9: "(vert#(cement vert)) = ((cement vert)\<otimes>(cement vert))" using append_blocks_Nil 
                        by metis
 have step3_subresult10: "strands ((cement vert)\<otimes>(cement vert))" 
       using step3_subresult8 step3_subresult9 by metis
 let ?a0 = "(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1"
 let ?b0 = "((cement vert)\<otimes>(cement vert))"
 let  ?a =  "Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic (?b0\<otimes>((cement vert)\<otimes>w4)))
        \<circ>((basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"
 let ?b = "Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((cement cup) \<otimes> ((cement vert) \<otimes> w4)))
        \<circ>((basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"
 have step3_subresult11: "  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.(?a = Abs_diagram
 ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))\<circ>(y2)))"
    using exI by metis
 have step3_subresult12: " \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.(
  ?b = (Abs_diagram  ((y1)\<circ>(basic (w1))\<circ>(basic (A\<otimes>w2))\<circ>(y2))))"
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
 have step3_subresult14: "linkrel_compbelow_centerright ?a ?b" using step3_subresult13 
      linkrel_compbelow_centerright_def by auto
 have step3_subresult15: "linkrel_compress ?a ?b" using step3_subresult14 linkrel_compress_def 
       linkrel_compbelow_def by auto
  have step3_subresult16: "linkrel ?a ?b" using step3_subresult15 linkrel_def by auto
  have step3_subresult17: "linkrel_equiv ?a ?b"
    using step3_subresult16 linkrel_equiv_def r_into_rtranclp
       by (metis (full_types) r_into_rtranclp)
 have step3_subresult18: "linkrel_equiv 
   (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic (((cement vert)\<otimes>(cement vert))
  \<otimes>((cement vert)\<otimes>w4)))\<circ>((basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1)))
  (Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((cement cup) \<otimes> ((cement vert) \<otimes> w4)))\<circ>((basic ((cement vert)
  \<otimes>(cement cap)\<otimes>w4))\<circ>z1)))"
    using step3_subresult17
 by metis
 have step3: 
 "linkrel_equiv 
   (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
        \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>(cement vert)\<otimes>w4))
        \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
 (Abs_diagram (((x1)\<circ>(basic y1))\<circ>(basic ((cement cup) \<otimes> ?z4))
         \<circ> (basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))" 
      using step3_subresult18 leftright_associativity w_subst step2_subresult1 left_associativity
          compose_leftassociativity by auto
 (*step 4*)
 let ?p = "(x1)\<circ>(basic ((cement cup)\<otimes>y1))"
 let ?q = "(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1"
 let ?r = " basic ((cement vert) \<otimes> (cement vert) \<otimes> (cement vert) \<otimes> w4)"
 have step4_subresult1: "strands ((cement vert) \<otimes> (cement vert) \<otimes> (cement vert) \<otimes> w4)"
     using assms  append_blocks.append_blocks_Nil  preliminary_result3 step2_subresult1 
     strands.simps(2) by metis
 have step4_subresult2: "snd (count ((cement cup)\<otimes>y1)) =  snd (count (cup#y1))" 
     using append_blocks.append_blocks_Nil count_def  by (metis)
 have step4_subresult3: " snd (count (cup#y1)) =  2+ snd (count (y1))"
     using step4_subresult2 count_def brickcount_def by auto
 have step4_subresult4: "snd (count ((cement cup)\<otimes>y1)) > snd (count (y1))"
     using step4_subresult2 step4_subresult3 add_strict_increasing dbl_def 
     dbl_simps(3) order_refl zero_less_two by auto
 have step4_subresult5: "snd (count ((cement cup)\<otimes>y1)) > 1"
     using step4_subresult4 assms by auto
 have step4_subresult6: "snd (wall_count ?p) = (snd (count ((cement cup)\<otimes>y1)))"
     using wall_count_def  snd_conv wall_count.simps(1) wall_count_compose by auto
 have step4_subresult7: "snd (wall_count ?p) > 0"
    using step4_subresult5 step4_subresult6 assms by auto
 have step4_subresult8: 
   "linkrel_compress_null 
     (Abs_diagram (?p\<circ>(basic ((cement vert) \<otimes> (cement vert) \<otimes> (cement vert) \<otimes> w4))\<circ>?q))
     (Abs_diagram (?p\<circ>?q))"
       using step4_subresult1 step4_subresult7 linkrel_compress_null_def by metis
 have step4_subresult9: 
    "linkrel_compress
      (Abs_diagram (?p\<circ>(basic ((cement vert) \<otimes> (cement vert) \<otimes> (cement vert) \<otimes> w4))\<circ>?q))
      (Abs_diagram (?p\<circ>?q))"
        using step4_subresult8 linkrel_compress_def by auto
 have step4_subresult10: 
  "linkrel (Abs_diagram (?p\<circ>?q))
   (Abs_diagram (?p\<circ>(basic ((cement vert) \<otimes> (cement vert) \<otimes> (cement vert) \<otimes> w4))\<circ>?q))"
      using step4_subresult9 step4_subresult8 linkrel_def by auto
 have step4_subresult11: 
  "linkrel_equiv
   (Abs_diagram (?p\<circ>?q))
   (Abs_diagram (?p\<circ>(basic ((cement vert) \<otimes> (cement vert) \<otimes> (cement vert) \<otimes> w4))\<circ>?q))"
     using step4_subresult10 linkrel_equiv_def compose_leftassociativity 
     leftright_associativity r_into_rtranclp step3_subresult11 step3_subresult13 by metis
 have step4: 
 "linkrel_equiv
  (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
  (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
   \<circ>(basic ((cement vert) \<otimes> (cement vert) \<otimes> (cement vert) \<otimes> w4))
   \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"
     using step4_subresult10 linkrel_equiv_def compose_leftassociativity 
     leftright_associativity r_into_rtranclp step3_subresult11 step3_subresult13 by metis
 (*combining steps*)                    
 have combine_vert: 
  "linkrel_equiv 
    (Abs_diagram (x1\<circ>basic y1\<circ>(basic ((cement cup)\<otimes>?z4))
            \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1)) 
    (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using step1 step2 rtranclp_trans linkrel_equiv_def by metis
 have combine_cup:
  "linkrel_equiv (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))
    \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>?z4))\<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
             (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
           using step3 combine_vert linkrel_equiv_def rtranclp_trans compose_leftassociativity 
           leftright_associativity step2 step2_subresult1 step2_subresult2 step3_subresult17 
           subresult_equiv3  w_subst by (metis) 
 have combine_compress:"linkrel_equiv
  (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
             (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
  using combine_cup step4 combine_vert linkrel_equiv_def rtranclp_trans compose_leftassociativity 
  leftright_associativity step2 step2_subresult1 step2_subresult2 step3_subresult17 subresult_equiv3 
               w_subst by metis
 from this show ?thesis by auto
 qed

text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1 \<circ>z1), where y1 is a 
block with outgoing strands, the following theorem proves that it is equivalent to a link 
diagram in which there exists a cup appended to the right of y1 *}

lemma count_rightcompose:" count(v\<otimes>w) = (fst (count v) + fst (count w), snd (count v)+snd (count w))"
  apply (induct_tac v)
  apply (metis append_blocks.append_blocks_Nil count.simps(1) count.simps(2))
  apply(auto)
  done

lemma count_cup_rightcompose:" count(v\<otimes>(cement cup)) = (fst (count v), snd (count v)+2)"
  apply (simp add:count_rightcompose)
  done

lemma fstcount_cup_rightcompose:" fst (count(v\<otimes>(cement cup))) = fst (count v)"
  apply (simp add: count_cup_rightcompose)
  done

theorem metaequivalence_right: 
 assumes "(snd (count y1))>1" 
 and "w4 = make_vert_block  (nat ((snd (count y1)) + (-2)))"
 shows "linkrel_equiv 
        (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>(cement cup)))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
        (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
proof-
 let ?k = " (nat ((snd (count y1))+ (-2) ))" 
 let ?z4 = "make_vert_block (nat ((snd (count y1)) + (-2))+1)"
 have C: " ?z4 = make_vert_block (?k+1)" using assms by auto
 let ?x2 = "x1 \<circ> (basic y1)"
 have preliminary_result1:"((snd (count y1))+(-1))>0" using assms by auto
 have preliminary_result2:"((snd (count y1))+(-2))\<ge>0" using assms by auto
 have preliminary_result3: "strands ?z4" using C strand_make_vert_block by auto
 have subresult0: "snd (wall_count ?x2) = snd (wall_count (basic y1))" 
           using wall_count_compose 
             by auto
 have subresult1: "... = snd (count y1)" using wall_count_compose 
            by auto
 have subresult2: "snd (wall_count ?x2) > 0"
            using subresult1 assms less_trans subresult0 zero_less_one 
            by auto
 have subresult3: "fst (count (?z4)) = fst (count (make_vert_block (?k+1)))"  
            using C make_vert_block_fstequality
            by auto
 have subresult4: "fst (count (make_vert_block (?k+1))) = int(?k+1)+1"  
            using make_vert_block_fstequality
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
 "(linkrel_compress_null ((Abs_diagram (?x2\<circ>(basic ?z4)\<circ>z1))) (Abs_diagram (?x2\<circ>z1)))" 
           using linkrel_compress_null_def
           preliminary_result3 subresult0 subresult2
             by metis
 have subresult_equiv1: 
 "(linkrel_equiv ((Abs_diagram (?x2\<circ>(basic ?z4)\<circ>z1))) (Abs_diagram (?x2\<circ>z1)))" 
           using r_into_rtranclp subresult_compress1 linkrel_equiv_def linkrel_def 
           linkrel_compress_def by (metis)
 have subresult_compress2: 
 "(linkrel_compress_null ((Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>(basic ?z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>z1)))" 
               using linkrel_compress_null_def preliminary_result3 subresult0 subresult2   
               compose_leftassociativity
               by (metis)
 have subresult_equiv2: 
 "(linkrel_equiv ((Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>(basic ?z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>z1)))" 
               using linkrel_compress_def linkrel_def linkrel_equiv_def
               r_into_rtranclp subresult_compress2   
               by (metis)
 have subresult_equiv3: 
 "linkrel_equiv ((Abs_diagram ((?x2 \<circ> basic ?z4)\<circ>(basic ?z4)\<circ>z1))) 
                            (Abs_diagram ((?x2 \<circ>z1)))" 
               using linkrel_equiv_def rtranclp_trans subresult_equiv1 subresult_equiv2 
               compose_leftassociativity
                            by (metis) 
 have step1: 
 "linkrel_equiv (Abs_diagram (x1 \<circ> basic y1 \<circ> basic ?z4\<circ>basic ?z4\<circ>z1)) 
                            (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using compose_leftassociativity subresult_equiv3 
               by auto
(*step 2 - inducing is_cup*)
 have w_subst: "w4 = (make_vert_block ?k)" using assms by auto
 have step2_subresult0: "(make_vert_block (?k+1)) = ((make_vert_block ?k) \<otimes>(cement vert))" 
               by (metis test_00 test_1)
 have step2_subresult1:"?z4 = (make_vert_block ?k)\<otimes>(cement vert)  " using C step2_subresult0 by auto
 have step2_subresult2: "(Abs_diagram (?x2 \<circ> (basic ?z4) \<circ>(basic ?z4)\<circ>z1)) =
   (Abs_diagram (?x2  \<circ> (basic (w4\<otimes>(cement vert)))\<circ> (basic (w4\<otimes>(cement vert)))\<circ>z1))" 
                        using w_subst step2_subresult1 by auto
 have step2_subresult3: "(snd (count w4)) = (fst (count w4))" 
                        using make_vert_block_fstsndequality w_subst by auto
 let ?x = "(Abs_diagram (?x2 \<circ>(basic (w4\<otimes>(cement vert)\<otimes>(cement cup)))
                        \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
 let ?y = "(Abs_diagram (?x2 \<circ>(basic (w4\<otimes>(cement vert)))\<circ>(basic (w4\<otimes>(cement vert)))\<circ>z1))"
 have step2_subresult4:
  "\<exists>y1.\<exists>y2.\<exists>w1.\<exists>w2.
   (?x = Abs_diagram (y1 \<circ> (basic (w1\<otimes>(cement vert)\<otimes>(cement cup))) 
    \<circ> (basic (w2\<otimes>(cement cap)\<otimes>(cement vert))) \<circ> y2))"
              using exI by auto
 have step2_subresult5:
 "\<exists>y1.\<exists>y2.\<exists>w1.\<exists>w2.(?y = Abs_diagram (y1 \<circ> (basic (w1\<otimes>(cement vert))) 
                   \<circ> (basic (w2\<otimes>(cement vert))) \<circ> y2))"
               using exI by auto
 have step2_subresult6: 
   " (\<exists>y1.\<exists>w1.\<exists>w2.\<exists>y2.((?x = Abs_diagram ((y1)
    \<circ> (basic (w1\<otimes>(cement vert)\<otimes>(cement cup))) \<circ> (basic (w2\<otimes>(cement cap)\<otimes>(cement vert))) \<circ> y2)))
    \<and>(?y = Abs_diagram (y1 \<circ> (basic (w1\<otimes>(cement vert))) \<circ> (basic (w2\<otimes>(cement vert))) \<circ> y2))
    \<and> ((snd (count w1)) = (fst (count w2))))"
               using  step2_subresult3 exI by auto 
 have step2_subresult7:"linkrel_straighten_leftdowntop ?x ?y"
               using linkrel_straighten_leftdowntop_def compose_leftassociativity step2_subresult2 
               step2_subresult4 step2_subresult6 subresult8 by (metis)
 have step2_subresult8:"linkrel ?x ?y" 
                using linkrel_def linkrel_straighten_def step2_subresult7 by auto
 have step2_subresult9: "linkrel (Abs_diagram ((?x2) \<circ>(basic (w4\<otimes>(cement vert)\<otimes>(cement cup)))
                \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)) 
              (Abs_diagram ((?x2) \<circ>(basic (w4\<otimes>(cement vert)))\<circ>(basic (w4\<otimes>(cement vert)))\<circ>z1))"
               using step2_subresult8 by auto 
 have step2_equiv1:"linkrel_equiv (Abs_diagram (x1\<circ>basic y1\<circ>(basic (w4\<otimes>(cement vert)\<otimes>(cement cup)))
                                   \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)) 
              (Abs_diagram (x1\<circ>basic y1 \<circ>(basic (w4\<otimes>(cement vert)))\<circ>(basic (w4\<otimes>(cement vert)))\<circ>z1))"
               using step2_subresult9 compose_leftassociativity r_into_rtranclp 
               linkrel_equiv_def
                     by metis
 have step2: "linkrel_equiv 
               (Abs_diagram (x1\<circ>basic y1\<circ>(basic (?z4\<otimes>(cement cup)))
                             \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)) 
              (Abs_diagram (x1\<circ>basic y1 \<circ>(basic ?z4)\<circ>(basic (?z4))\<circ>z1))"
               using  step2_subresult9 compose_leftassociativity r_into_rtranclp 
               linkrel_equiv_def step2_subresult1 w_subst leftright_associativity  by (metis )
 (*step 3*)
 have step3_preliminary1: "fst (count (v\<otimes>w)) = fst (count (cup#(v\<otimes>w)))" 
               using count_def brickcount_def by auto
 have step3_preliminary2 : 
       "count ((w4\<otimes>(cement vert))\<otimes>(cement cup)) = 
                 ((fst (count (w4\<otimes>(cement vert)))), (snd (count (w4\<otimes>(cement vert)))+2))"
              using fstcount_cup_rightcompose  count_cup_rightcompose by (metis) 
 have step3_preliminary3 : 
       "fst (count ((w4\<otimes>(cement vert))\<otimes>(cement cup))) = (fst (count (w4\<otimes>(cement vert))))"
              using step3_preliminary2 by auto
 have step3_subresult1 :
    "fst (wall_count (basic ((w4\<otimes>(cement vert))\<otimes>(cement cup)))) 
                              = fst (wall_count (basic (w4\<otimes>(cement vert)))) " 
             using wall_count_def step3_preliminary3 append_blocks.append_blocks_Nil add_diff_cancel 
              comm_monoid_add_class.add.left_neutral count.simps(2) fst_conv wall_count.simps(1)
             by (metis)
 have step3_subresult2: "fst (wall_count (basic (w4\<otimes>(cement vert)))) = snd (count y1)" 
              using w_subst step2_subresult1 subresult8 by auto
 have step3_subresult3: "fst (wall_count (basic ((w4\<otimes>(cement vert)\<otimes>(cement cup))))) = snd (count y1)" 
               using step3_subresult1 step3_subresult2 leftright_associativity
               by (auto)
 have step3_subresult4: "fst (wall_count (basic (w4\<otimes>(cement vert)))) = snd (wall_count ?x2)" 
               using step3_subresult3 subresult0 wall_count_def step3_subresult2 subresult1 by auto 
 have step3_subresult5: "fst (wall_count (basic (w4\<otimes>(cement vert)))) 
                         = snd (wall_count (x1\<circ>(basic y1)))" 
               using step3_subresult4  wall_count_def by auto
 have step3_subresult6: "fst (brickcount cup) =  0" using brickcount_def by auto
 have step3_subresult7: "fst (count (cement cup)) =  0" using count_def step3_subresult6 
                           by (metis count.simps(1))
 have step3_subresult8: "strands (vert#(cement vert))" 
                       using append_blocks_def strands_def  brickstrand.simps(1) 
                        strands.simps(1) strands.simps(2) 
                       by metis
 have step3_subresult9: "(vert#(cement vert)) = ((cement vert)\<otimes>(cement vert))" 
                       using append_blocks_Nil  by metis
 have step3_subresult10: "strands ((cement vert)\<otimes>(cement vert))" 
                        using step3_subresult8 step3_subresult9 by metis
 let  ?a = "Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (?z4\<otimes>(cement vert)\<otimes>(cement vert)))
            \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"

 let ?b = "Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((w4\<otimes>(cement vert)) \<otimes> (cement cup)))
            \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
 have step3_subresult11: "  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.
                             (?a = Abs_diagram ((y1)\<circ>(basic (w1 \<otimes>A))\<circ>(basic (w2\<otimes>B))\<circ>(y2)))"
                       using exI by metis
 have step3_subresult12: " \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.
                               (?b = (Abs_diagram ((y1)\<circ>(basic (w1))\<circ>(basic (w2\<otimes>A))\<circ>(y2))))"
                       using exI by metis
 let  ?a = "Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (?z4\<otimes>(cement vert)\<otimes>(cement vert)))
                           \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
 let ?b = "Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((w4\<otimes>(cement vert)) \<otimes> (cement cup)))
                           \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
 have step3_subresult13: " \<exists>y1.\<exists>z1.\<exists>z2.\<exists>A.\<exists>B.\<exists>y2.(
                             (?a = Abs_diagram ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))
                            \<and> (?b = Abs_diagram ((y1) \<circ>(basic (z1))\<circ>(basic (z2\<otimes>A))\<circ>(y2)))
                            \<and>((snd (count z1)) = (fst (count z2)))
                            \<and>((fst (count A)) = 0)
                            \<and>(strands B))" 
           using step3_subresult11 step3_subresult12 compose_leftassociativity step2_subresult1 
           subresult8 w_subst step3_subresult5 step3_subresult7 step3_subresult10 exI assms
           leftright_associativity step2_subresult4 step2_subresult6
           by metis
 have step3_subresult14: "linkrel_compbelow_centerleft ?a ?b" using step3_subresult13 
 linkrel_compbelow_centerright_def 
 step2_subresult3 step3_subresult11 step3_subresult7 linkrel_compbelow_centerleft_def zero_reorient
           by (metis)
 have step3_subresult15: "linkrel_compress ?a ?b" 
           using step3_subresult14 linkrel_compress_def linkrel_compbelow_def by auto
 have step3_subresult16: "linkrel ?a ?b" 
           using step3_subresult15 linkrel_def by auto
 have step3_subresult17: "linkrel_equiv ?a ?b"
          using step3_subresult16 linkrel_equiv_def r_into_rtranclp
          by (metis (full_types) r_into_rtranclp)
 have step3_subresult18: "linkrel_equiv 
 (Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (?z4\<otimes>(cement vert)\<otimes>(cement vert)))
               \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)))
 (Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((w4\<otimes>(cement vert)) \<otimes> (cement cup)))
               \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)))"
           using step3_subresult17 by metis
 have step3: "linkrel_equiv 
 (Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (?z4\<otimes>(cement vert)\<otimes>(cement vert)))
                                 \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)))
 (Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic ((?z4) \<otimes> (cement cup)))
                                 \<circ>((basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1)))"
       using step3_subresult18 leftright_associativity w_subst step2_subresult1 left_associativity
       compose_leftassociativity by metis
(*step 4*)
 let ?p = "(x1)\<circ>(basic (y1 \<otimes> (cement cup)))"
 let ?q = "(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1"
 let ?r = " basic (?z4 \<otimes> (cement vert) \<otimes> (cement vert))"
 have step4_subresult1: "strands (?z4 \<otimes> (cement vert) \<otimes> (cement vert))"
    using assms  append_blocks.append_blocks_Nil preliminary_result3 step2_subresult1 
     strands.simps(2) leftright_associativity test_0 by (metis)
 have step4_subresult2: "snd (count (y1\<otimes>(cement cup))) =  snd (count (y1)) + 2"
           apply (induct_tac y1)
           apply (auto)
           done
 have step4_subresult4: "snd (count (y1 \<otimes> (cement cup))) > snd (count (y1))"
          using step4_subresult2 add_strict_increasing dbl_def dbl_simps(3) order_refl zero_less_two
          by auto
 have step4_subresult5: "snd (count (y1 \<otimes> (cement cup))) > 1"
          using step4_subresult4 assms by auto
 have step4_subresult6: "snd (wall_count ?p) = (snd (count (y1\<otimes>(cement cup))))"
          using wall_count_def  snd_conv wall_count.simps(1) wall_count_compose by auto
 have step4_subresult7: "snd (wall_count ?p) > 0"
          using step4_subresult5 step4_subresult6 assms by auto
 have step4_subresult8: 
  "linkrel_compress_null 
             (Abs_diagram (?p\<circ>(basic ((?z4) \<otimes> (cement vert) \<otimes> (cement vert)))\<circ>?q))
             (Abs_diagram (?p\<circ>?q))"
          using step4_subresult1 step4_subresult7 linkrel_compress_null_def by metis
 have step4_subresult9: 
  "linkrel_compress
              (Abs_diagram (?p\<circ>(basic ((?z4) \<otimes> (cement vert) \<otimes> (cement vert)))\<circ>?q))
              (Abs_diagram (?p\<circ>?q))"
           using step4_subresult8 linkrel_compress_def by auto
 have step4_subresult10: 
 "linkrel
              (Abs_diagram (?p\<circ>?q))
              (Abs_diagram (?p\<circ>(basic (?z4 \<otimes> (cement vert) \<otimes> (cement vert)))\<circ>?q))"
           using step4_subresult9 step4_subresult8 linkrel_def by auto
 have step4_subresult11: 
 "linkrel_equiv
                (Abs_diagram (?p\<circ>?q))
                (Abs_diagram (?p\<circ>(basic ((?z4) \<otimes> (cement vert) \<otimes> (cement vert)))\<circ>?q))"
           using step4_subresult10 linkrel_equiv_def compose_leftassociativity 
           leftright_associativity r_into_rtranclp step3_subresult11 step3_subresult13 by metis
 have step4: 
 "linkrel_equiv
       (Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
       (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>(cement cup)))\<circ>(basic (?z4\<otimes>(cement vert) \<otimes> (cement vert)))
                               \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
         using step4_subresult10 linkrel_equiv_def compose_leftassociativity 
         leftright_associativity r_into_rtranclp step3_subresult11 step3_subresult13 by metis
 (*combining steps*)                  
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
               step2 step2_subresult1 step2_subresult2 step3_subresult17 subresult_equiv3 
               w_subst  by (metis) 
 have combine_compress:
 "linkrel_equiv 
      (Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
      (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))"
             using  combine_cup step4  rtranclp_trans  combine_vert linkrel_equiv_def rtranclp_trans
             compose_leftassociativity leftright_associativity 
             step2 step2_subresult1 step2_subresult2 step3_subresult17 subresult_equiv3  w_subst
             C nat_add_commute r_into_rtranclp step3_subresult16  step4_subresult10 test_0 test_1 
             wall_count.simps(1) by (metis (full_types))
 from combine_compress show ?thesis by simp
 qed

text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1 \<circ>z1), where y1 is a 
block with incoming strands, the following theorem proves that it is equivalent to a link 
diagram in which there exists a cap appended to the right of y1 *}


theorem metaequivalence_bottomright: 
 assumes "(fst (count y1))>1"
 and "w4 = make_vert_block  (nat ((fst (count y1)) + (-2)))" 
 and "well_defined (x1 \<circ> basic y1 \<circ>z1)"
 shows "linkrel_equiv 
      (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert))\<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1)))     
      (Abs_diagram (x1 \<circ> (basic y1) \<circ>z1))" 
proof-
 let ?z4 = "make_vert_block (nat ((fst (wall_count (basic y1))) + (-2))+1)"
 let ?k = " (nat ((fst (count y1))+ (-2) ))" 
 have C: " (?z4 = make_vert_block (?k+1))" using assms by auto
 have preliminary_result0: "(fst (wall_count ((basic y1)\<circ>z1))) = (snd (wall_count x1))" 
   using assms diagram_fst_equals_snd by metis
 have preliminary_result1: " (fst (wall_count ((basic y1)\<circ>z1))) = (fst (count y1))" 
   by (metis compose_Nil fst_eqD wall_count.simps(2))
 have preliminary_result2: " (snd (wall_count x1)) = (fst (count y1))" 
   using preliminary_result0 preliminary_result1 by auto
 have preliminary_result3:"((fst (count y1))+(-1))>0" 
   using assms by auto
 have preliminary_result4:"((fst (count y1))+(-2))\<ge>0" 
   using assms by auto
 have preliminary_result5: "strands ?z4" 
   using C strand_make_vert_block by auto
 have preliminary_result6: "(snd (wall_count x1))>1" 
   using assms preliminary_result2 by auto
 have subresult3: "snd (count (?z4)) = snd (count (make_vert_block (?k+1)))"  
   using C make_vert_block_fstequality by auto
 have subresult4: "snd (count (make_vert_block (?k+1))) = int(?k+1)+1"  
            using make_vert_block_sndequality by auto
 have subresult5:"snd (count (?z4)) =  int(?k)+2" 
           using subresult3 subresult4 by auto
 have subresult6: "int (nat (fst (count y1) + -2)) = (fst (count y1)) + -2" 
           using int_nat_eq preliminary_result3 by auto
 have subresult7: "fst (count y1) = int(?k)+2" 
           using subresult6 by auto
 have subresult8: "snd (count (?z4)) = (fst (count y1))" 
           using subresult5 subresult7 by auto
 have subresult_compress1: 
  "(linkrel_compress_null 
       (Abs_diagram (x1\<circ>(basic ?z4)\<circ>(basic y1)\<circ>z1)) 
       (Abs_diagram (x1\<circ>(basic y1)\<circ>z1)))" 
           using linkrel_compress_null_def preliminary_result5 preliminary_result6 subresult8 
           C comm_semiring_1_class.normalizing_semiring_rules(24) make_vert_block_fstequality 
           monoid_add_class.add.left_neutral of_nat_Suc zless_iff_Suc_zadd
           by (metis)
 have subresult_equiv1: 
 "(linkrel_equiv  
           ((Abs_diagram (x1\<circ>(basic ?z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1)))" 
           using r_into_rtranclp subresult_compress1 linkrel_equiv_def linkrel_def 
           linkrel_compress_def by (metis)
 have subresult_compress2: 
 "(linkrel_compress_null  
           (Abs_diagram (x1\<circ>(basic ?z4)\<circ>(basic y1)\<circ>z1)) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1))) " 
            using linkrel_compress_null_def preliminary_result3   
            compose_leftassociativity subresult_compress1 by auto          
 let ?z2 = "((basic ?z4)\<circ>(basic y1)\<circ>z1)"
 have subresult_equiv2: 
 "(linkrel_compress_null 
         (Abs_diagram (x1 \<circ> (basic ?z4)\<circ>(?z2)))
         (Abs_diagram (x1\<circ>(?z2))))"
          using linkrel_compress_null_def  C comm_semiring_1_class.normalizing_semiring_rules(24) 
          int_one_le_iff_zero_less make_vert_block_fstequality preliminary_result5 subresult8 
          zle_iff_zadd preliminary_result6  make_vert_block_fstsndequality preliminary_result2
          by (metis)
 have subresult_equiv3: 
 "linkrel_equiv 
           (Abs_diagram (x1 \<circ> (basic ?z4)\<circ>(?z2))) 
           (Abs_diagram (x1 \<circ> (?z2)))"
          using linkrel_equiv_def linkrel_compress_def subresult_equiv2  r_into_rtranclp linkrel_def
          by (metis (full_types))
 have subresult_equiv4: 
 "linkrel_equiv 
            (Abs_diagram (x1 \<circ> basic ?z4\<circ>basic ?z4 \<circ> basic y1\<circ>z1)) 
            (Abs_diagram (x1 \<circ> (basic ?z4)\<circ>(basic y1)\<circ>z1))" 
          using compose_leftassociativity subresult_equiv3 by auto
 have step1: 
 "linkrel_equiv 
           (Abs_diagram (x1 \<circ> basic ?z4\<circ>basic ?z4 \<circ> basic y1\<circ>z1)) 
           (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))" 
         using compose_leftassociativity subresult_equiv3 subresult_equiv1 rtranclp_trans
         by (metis (full_types) Link.abs_eq_iff )
(*step 2*)
 have w_subst: "w4 = (make_vert_block ?k)" using assms by auto
 have step2_subresult0: "(make_vert_block (?k+1)) = ((make_vert_block ?k) \<otimes>(cement vert))" 
        by (metis test_00 test_1)
 have step2_subresult1:"?z4 = (make_vert_block ?k)\<otimes>(cement vert)  " 
          using C step2_subresult0 by auto
 have step2_subresult2: 
  "(Abs_diagram (x1 \<circ> (basic ?z4) \<circ>(basic ?z4)\<circ> (basic y1)\<circ>z1)) =
   (Abs_diagram (x1  \<circ> (basic (w4\<otimes>(cement vert)))\<circ> (basic (w4\<otimes>(cement vert)))\<circ>(basic y1)\<circ> z1))" 
          using w_subst step2_subresult1 by auto
 have step2_subresult3: "(snd (count w4)) = (fst (count w4))" 
          using make_vert_block_fstsndequality w_subst by auto
 let ?z3 = " (basic y1)\<circ> z1"
 let ?x = "(Abs_diagram (x1 \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                        \<circ>(basic (w4\<otimes>(cement vert)\<otimes>(cement cap)))\<circ>(?z3)))"
 let ?y = "(Abs_diagram (x1 \<circ>(basic (w4\<otimes>(cement vert)))\<circ>(basic (w4\<otimes>(cement vert)))\<circ> (?z3)))"
 have step2_subresult4:
  "\<exists>a.\<exists>b.\<exists>c.\<exists>d.
    (?x = Abs_diagram (a \<circ> (basic (b\<otimes>(cement cup)\<otimes>(cement vert) )) 
                      \<circ> (basic (c\<otimes>(cement vert)\<otimes>(cement cap))) \<circ> d))"
          using exI by auto
 have step2_subresult5:
 "\<exists>a.\<exists>b.\<exists>c.\<exists>d.(?y = Abs_diagram (a \<circ> (basic (b\<otimes>(cement vert))) \<circ> (basic (c\<otimes>(cement vert))) \<circ> d))"
          using exI by auto
 have step2_subresult6: 
 "(\<exists>a.\<exists>b.\<exists>c.\<exists>d.
  ((?x = Abs_diagram ((a) \<circ> (basic (b\<otimes>(cement cup)\<otimes>(cement vert))) 
                      \<circ>(basic (c\<otimes>(cement vert)\<otimes>(cement cap))) \<circ> d)))
  \<and>(?y = Abs_diagram (a \<circ> (basic (b\<otimes>(cement vert))) \<circ> (basic (c\<otimes>(cement vert))) \<circ> d))
  \<and>((snd (count b)) = (fst (count c))))"
          using  step2_subresult3 step2_subresult4 step2_subresult5 exI  by auto
 have step2_subresult7:
 "linkrel_straighten_lefttopdown ?x ?y"
          using linkrel_straighten_lefttopdown_def compose_leftassociativity step2_subresult2 
          step2_subresult4 step2_subresult6 subresult8 step2_subresult3 step2_subresult5 by auto
 have step2_subresult8:"linkrel ?x ?y" 
          using linkrel_def linkrel_straighten_def step2_subresult7 by auto      
 have step2_subresult9: 
 "linkrel 
       (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                \<circ>(basic (w4\<otimes>(cement vert)\<otimes>(cement cap)))\<circ>(?z3))) 
       (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>(cement vert)))\<circ>(basic (w4\<otimes>(cement vert)))\<circ>(?z3)))"
               using step2_subresult8 by auto
 have step2_subresult10: "linkrel_equiv 
       (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                          \<circ>(basic (w4\<otimes>(cement vert)\<otimes>(cement cap)))\<circ>((basic y1)\<circ> z1))) 
       (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>(cement vert)))\<circ>(basic (w4\<otimes>(cement vert)))\<circ>((basic y1)\<circ> z1)))"
               using step2_subresult9 compose_leftassociativity r_into_rtranclp linkrel_equiv_def
              by metis
 have step2_subresult11: "linkrel_equiv 
              (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (w4\<otimes>(cement vert)\<otimes>(cement cap)))\<circ>(basic y1)\<circ> z1)) 
              (Abs_diagram ((x1) \<circ>(basic (?z4))\<circ>(basic (?z4))\<circ>((basic y1)\<circ> z1)))"
               using step2_subresult10 step2_subresult1 w_subst
                     by (auto)
 have step2: "linkrel_equiv 
              (Abs_diagram ((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (?z4\<otimes>(cement cap)))\<circ>(basic y1)\<circ> z1)) 
              (Abs_diagram ((x1) \<circ>(basic (?z4))\<circ>(basic (?z4))\<circ>((basic y1)\<circ> z1)))"
               using step2_subresult11 step2_subresult1 
                   Link.abs_eq_iff compose_Nil leftright_associativity 
                   step1 step2_subresult4 step2_subresult6 subresult8 w_subst
                   by (metis)
(*step 3*)
 have step3_subresult1 :"snd (count  ?z4) = fst (count y1) " 
              using assms preliminary_result6 subresult8 by auto
 have step3_subresult2: "snd (count (cement cap)) = 0" 
             using  count_def brickcount_def brickcount.simps(3) count.simps(1) snd_conv by (metis)
 have step3_subresult3: "strands (vert#(cement vert))" using append_blocks_def strands_def  
                       brickstrand.simps(1) strands.simps(1) strands.simps(2) by metis
 have step3_subresult4: "(vert#(cement vert)) = ((cement vert)\<otimes>(cement vert))"
             using append_blocks_Nil  by metis
 have step3_subresult5: "strands ((cement vert)\<otimes>(cement vert))" 
             using step3_subresult3 step3_subresult4 by metis
 let  ?a = "Abs_diagram (((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert))))
            \<circ>(basic (?z4\<otimes>(cement vert)\<otimes>(cement vert)))\<circ>(basic (y1\<otimes>(cement cap)))\<circ> z1) "
 let ?b = " (Abs_diagram (((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert))))
            \<circ>(basic (?z4\<otimes>(cement cap)))\<circ>(basic y1)\<circ> z1)) "
 have step3_subresult6: " \<exists>a1.\<exists>b1.\<exists>b2.\<exists>A.\<exists>B.\<exists>a2.
                 (?a = Abs_diagram ((a1)\<circ>(basic (b1\<otimes>A))\<circ>(basic (b2\<otimes>B))\<circ>(a2)))"
          using exI by metis
 have step3_subresult7: " \<exists>a1.\<exists>b1.\<exists>b2.\<exists>a2.\<exists>B.
                  (?b  = (Abs_diagram ((a1)\<circ>(basic (b1\<otimes>B))\<circ>(basic (b2))\<circ>(a2))))"
          using exI by metis
 have step3_subresult8: " \<exists>a1.\<exists>b1.\<exists>b2.\<exists>A.\<exists>B.\<exists>a2.
       (?a = Abs_diagram ((a1)\<circ>(basic (b1\<otimes>A))\<circ>(basic (b2\<otimes>B))\<circ>(a2))
     \<and>(?b  = (Abs_diagram ((a1)\<circ>(basic (b1\<otimes>B))\<circ>(basic (b2))\<circ>(a2))))
     \<and>((snd (count b1)) = (fst (count b2)))
     \<and>((snd (count B)) = 0)
     \<and>(strands A))" 
           using compose_leftassociativity step2_subresult1 subresult8 w_subst step3_subresult5 
           step3_subresult7  exI assms leftright_associativity step2_subresult4 step2_subresult6
           step3_subresult6 step3_subresult7 step3_subresult1  step3_subresult2  step3_subresult5 
           exI assms leftright_associativity compose_leftassociativity by metis
 have step3_subresult9: "linkrel_compabove_centerleft ?a ?b" 
            using step3_subresult8 linkrel_compabove_centerleft_def 
            step2_subresult3 step3_subresult6 step3_subresult7  zero_reorient
            by (metis)
 have step3_subresult10: "linkrel_compabove ?a ?b" 
           using step3_subresult9  linkrel_compabove_def by auto
 have step3_subresult11: "linkrel_compress ?a ?b" 
           using step3_subresult10  linkrel_compress_def by auto
 have step3_subresult12: "linkrel ?a ?b" 
           using step3_subresult11 linkrel_def by auto
 have step3_subresult13: "linkrel_equiv ?a ?b"
           using step3_subresult12 linkrel_equiv_def r_into_rtranclp by (metis (full_types) )
 have step3: 
  "linkrel_equiv
    (Abs_diagram (((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert))))
                 \<circ>(basic (?z4\<otimes>(cement vert)\<otimes>(cement vert)))\<circ>(basic (y1\<otimes>(cement cap)))\<circ> z1))
    (Abs_diagram (((x1) \<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert))))\<circ>(basic (?z4\<otimes>(cement cap)))
                 \<circ>(basic y1)\<circ> z1)) "
 using step3_subresult13 by auto
(*step 4*)
 let ?p = "(x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))"
 let ?q = "(basic (y1 \<otimes> (cement cap)))\<circ>z1"
 let ?r = " basic (?z4 \<otimes> (cement vert) \<otimes> (cement vert))"
 have step4_subresult1: "strands (?z4 \<otimes> (cement vert) \<otimes> (cement vert))"
         using assms  append_blocks.append_blocks_Nil  preliminary_result3 step2_subresult1 
         strands.simps(2) leftright_associativity test_0 strand_make_vert_block wall_count.simps(1)
         by (metis)
 have step4_subresult2: "fst (count (y1\<otimes>(cement cap))) =  fst (count (y1)) + 2"
         apply (induct_tac y1)
         apply (auto)
         done
 have step4_subresult4: "fst (count (y1 \<otimes> (cement cap))) = fst (count (y1))+2"
          using step4_subresult2 add_strict_increasing dbl_def dbl_simps(3) order_refl zero_less_two
          by auto
 have step4_subresult5: "fst (count (y1 \<otimes> (cement cap))) > 1"
          using step4_subresult4 assms by auto
 have step4_subresult6: "snd (wall_count ?p) = snd (count (w4\<otimes>(cement cup)\<otimes>(cement vert)))"
          using wall_count_def  snd_conv wall_count.simps(1) wall_count_compose by auto
 have step4_subresult7: "snd (count (x\<otimes>(cement vert))) >0 "
          using snd_count_positive  brickcount_def count_def make_vert_block.simps(1)  
          make_vert_block_fstsndequality make_vert_blocks_positiveblock_length
           add_nonneg_eq_0_iff less_le snd_count_additive snd_count_nonnegative
          by (metis)
 have step4_subresult8: "snd (count ((w4\<otimes>(cement cup))\<otimes>(cement vert))) > 0"
          using step4_subresult7 add_nonneg_eq_0_iff brick.distinct(1) brickcount_zero_implies_cup 
          count.simps(1) le_neq_trans make_vert_block.simps(1) make_vert_block_fstsndequality 
          snd_count_additive snd_count_nonnegative by (metis)
 have step4_subresult9: "snd (wall_count ?p) > 0"
           using step4_subresult6 step4_subresult8 by (metis leftright_associativity)
 have step4_subresult10: 
        "linkrel_compress_null (Abs_diagram (?p\<circ>?r\<circ>?q)) (Abs_diagram (?p\<circ>?q))"
           using step4_subresult1 step4_subresult7 linkrel_compress_null_def leftright_associativity 
           step4_subresult6 step4_subresult8 by (metis)
 have step4_subresult11: 
    "linkrel_compress (Abs_diagram (?p\<circ>?r\<circ>?q)) (Abs_diagram (?p\<circ>?q))"
          using step4_subresult10 linkrel_compress_def by auto
 have step4_subresult12: 
     "linkrel (Abs_diagram (?p\<circ>?q)) (Abs_diagram (?p\<circ>?r\<circ>?q))"
          using step4_subresult11 step4_subresult10 linkrel_def by auto
 have step4_subresult13:
 "linkrel
  (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (?z4 \<otimes> (cement vert) \<otimes> (cement vert)))\<circ>(basic (y1 \<otimes> (cement cap)))\<circ>z1))
  (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (y1 \<otimes> (cement cap)))\<circ>z1))"
        using step4_subresult12 by (metis compose_leftassociativity linkrel_def)
 have step4: 
 "linkrel_equiv
   (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                 \<circ>(basic (?z4 \<otimes> (cement vert) \<otimes> (cement vert)))\<circ>(basic (y1 \<otimes> (cement cap)))\<circ>z1))
   (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (y1 \<otimes> (cement cap)))\<circ>z1))"
       using step4_subresult10 linkrel_equiv_def compose_leftassociativity leftright_associativity 
      r_into_rtranclp step3_subresult11 step4_subresult12 step4_subresult13 by (metis (full_types))
(*combining steps*)
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
               leftright_associativity step2 step2_subresult1 step2_subresult2  subresult_equiv3 
               w_subst by (metis) 
 have combine_compress:
 "linkrel_equiv
   (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (y1 \<otimes> (cement cap)))\<circ>z1))
   (Abs_diagram ((x1)\<circ>(basic y1)\<circ>z1))"
               using combine_cup step4 rtranclp_trans  combine_cup step4 rtranclp_trans 
               compose_leftassociativity leftright_associativity 
               step2 step2_subresult1 step2_subresult2  subresult_equiv3 
               w_subst linkrel_equiv_def converse_rtranclp_into_rtranclp step4_subresult12
               by (metis )
 from combine_compress show ?thesis by (simp add: compose_leftassociativity)
 qed

text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1 \<circ>z1), where y1 is a 
block with incoming strands, the following theorem proves that it is equivalent to a link 
diagram in which there exists a cap appended to the left of y1 *}

(*need to align from here*)
 theorem metaequivalence_bottomleft: 
 assumes "(fst (count y1))>1"
 and "w4 = make_vert_block  (nat ((fst (count y1)) + (-2)))" and "well_defined (x1 \<circ> basic y1 \<circ>z1)"
 shows 
  "linkrel_equiv 
        (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)\<circ>(basic ((cement cap)\<otimes>y1))\<circ>z1)))    
        (Abs_diagram (x1 \<circ> (basic y1) \<circ>z1))" 
 proof-
 let ?z4 ="make_vert_block (nat ((fst (wall_count (basic y1))) + (-2))+1)"
 let ?k = " (nat ((fst (count y1))+ (-2) ))" 
 have C: " (?z4 = make_vert_block (?k+1))" 
      using assms by auto
 have preliminary_result0: "(fst (wall_count ((basic y1)\<circ>z1))) = (snd (wall_count x1))" 
      using assms diagram_fst_equals_snd by metis
 have preliminary_result1: " (fst (wall_count ((basic y1)\<circ>z1))) = (fst (count y1))" 
      by (metis compose_Nil fst_eqD wall_count.simps(2))
 have preliminary_result2: " (snd (wall_count x1)) = (fst (count y1))" 
      using preliminary_result0 preliminary_result1 by auto
 have preliminary_result3:"((fst (count y1))+(-1))>0" 
      using assms by auto
 have preliminary_result4:"((fst (count y1))+(-2))\<ge>0" 
      using assms by auto
 have preliminary_result5: "strands ?z4" 
      using C strand_make_vert_block by auto
 have preliminary_result6: "(snd (wall_count x1))>1" 
      using assms preliminary_result2 by auto
 have subresult3: "snd (count (?z4)) = snd (count (make_vert_block (?k+1)))"  
      using C make_vert_block_fstequality by auto
 have subresult4: "snd (count (make_vert_block (?k+1))) = int(?k+1)+1"  
       using make_vert_block_sndequality
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
  "(linkrel_compress_null 
           ((Abs_diagram (x1\<circ>(basic ?z4)\<circ>(basic y1)\<circ>z1))) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1)))" 
       using linkrel_compress_null_def preliminary_result5 preliminary_result6 subresult8 
       by (metis C comm_semiring_1_class.normalizing_semiring_rules(24) 
       make_vert_block_fstequality monoid_add_class.add.left_neutral of_nat_Suc zless_iff_Suc_zadd)
 have subresult_equiv1: 
 "(linkrel_equiv  
           (Abs_diagram (x1\<circ>(basic ?z4)\<circ>(basic y1)\<circ>z1)) 
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1)))" 
           using r_into_rtranclp subresult_compress1 linkrel_equiv_def linkrel_def  
           linkrel_compress_def  by (metis)
 have subresult_compress2: 
 "(linkrel_compress_null  
           (Abs_diagram (x1\<circ>(basic ?z4)\<circ>(basic y1)\<circ>z1))
           (Abs_diagram (x1\<circ>(basic y1)\<circ>z1))) " 
          using linkrel_compress_null_def preliminary_result3   
          compose_leftassociativity subresult_compress1
           by auto           
 let ?z2 = "((basic ?z4)\<circ>(basic y1)\<circ>z1)"
 have subresult_equiv2: 
 "(linkrel_compress_null 
             (Abs_diagram (x1 \<circ> (basic ?z4)\<circ>(?z2)))
             (Abs_diagram (x1\<circ>(?z2))))"
          using linkrel_compress_null_def C comm_semiring_1_class.normalizing_semiring_rules(24) 
          int_one_le_iff_zero_less make_vert_block_fstequality preliminary_result5 
          subresult8 zle_iff_zadd preliminary_result6  make_vert_block_fstsndequality 
          preliminary_result2  by (metis)
 have subresult_equiv3: 
 "linkrel_equiv 
             (Abs_diagram (x1 \<circ> (basic ?z4)\<circ>(?z2))) 
             (Abs_diagram (x1 \<circ> (?z2)))" 
       using linkrel_equiv_def linkrel_compress_def subresult_equiv2
       by (metis (full_types) r_into_rtranclp linkrel_def)
 have subresult_equiv4: 
 "linkrel_equiv 
           (Abs_diagram (x1 \<circ> basic ?z4\<circ>basic ?z4 \<circ> basic y1\<circ>z1)) 
           (Abs_diagram (x1 \<circ> (basic ?z4)\<circ>(basic y1)\<circ>z1))" 
       using compose_leftassociativity subresult_equiv3
       by auto
 have step1: 
 "linkrel_equiv 
            (Abs_diagram (x1 \<circ> basic ?z4\<circ>basic ?z4 \<circ> basic y1\<circ>z1)) 
            (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))" 
       using compose_leftassociativity subresult_equiv3 subresult_equiv1 rtranclp_trans
       by (metis (full_types) Link.abs_eq_iff )
(*step 2*)
 have w_subst: "w4 = (make_vert_block ?k)" 
      using assms by auto
 have step2_subresult0: "(make_vert_block (?k+1)) = ((cement vert)\<otimes>(make_vert_block ?k))" 
     by (metis test_0)
 have step2_subresult1:"?z4 = (cement vert) \<otimes>(make_vert_block ?k)  " 
     using C step2_subresult0 by auto                         
 have step2_subresult2: 
   "(Abs_diagram (x1 \<circ> (basic ?z4) \<circ>(basic ?z4)\<circ> (basic y1)\<circ>z1)) =
    (Abs_diagram (x1  \<circ> (basic ((cement vert) \<otimes>w4))\<circ> (basic ((cement vert) \<otimes>w4))\<circ>(basic y1)\<circ> z1))" 
     using w_subst step2_subresult1 by auto
 have step2_subresult3: "(snd (count w4)) = (fst (count w4))" 
     using make_vert_block_fstsndequality w_subst by auto
 let ?z3 = " (basic y1)\<circ> z1"
 let ?x = "(Abs_diagram (x1 \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
            \<circ>(basic ((cement cap)\<otimes>(cement vert)\<otimes>w4))\<circ>(?z3)))"
 let ?y = "(Abs_diagram (x1 \<circ>(basic ((cement vert)\<otimes>w4))\<circ>(basic ((cement vert)\<otimes>w4))\<circ> (?z3)))"
 have step2_subresult4:
 "\<exists>a.\<exists>b.\<exists>c.\<exists>d.(?x = Abs_diagram (a \<circ> (basic ((cement vert)\<otimes>(cement cup)\<otimes>b )) 
                    \<circ> (basic ((cement cap)\<otimes>(cement vert)\<otimes>c)) \<circ> d))"
       using exI by auto
 have step2_subresult5:
  "\<exists>a.\<exists>b.\<exists>c.\<exists>d.(?y = Abs_diagram (a \<circ> (basic ((cement vert)\<otimes>b)) \<circ> (basic ((cement vert)\<otimes>c)) \<circ> d))"
       using exI by auto
 have step2_subresult6: 
 "(\<exists>a.\<exists>b.\<exists>c.\<exists>d.(
  (?x = Abs_diagram ((a)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>b))\<circ>(basic ((cement cap)
                  \<otimes>(cement vert)\<otimes>c))\<circ>d)))
 \<and>(?y = Abs_diagram (a \<circ> (basic ((cement vert)\<otimes>b)) \<circ> (basic ((cement vert)\<otimes>c)) \<circ> d))
 \<and> ((snd (count b)) = (fst (count c))))"
       using  step2_subresult3 step2_subresult4 step2_subresult5 exI 
       by auto
 have step2_subresult7:
 "linkrel_straighten_righttopdown ?x ?y"
      using linkrel_straighten_righttopdown_def compose_leftassociativity step2_subresult2 
      step2_subresult4 step2_subresult6 subresult8 step2_subresult3 step2_subresult5
      by auto
 have step2_subresult8:"linkrel ?x ?y" 
      using linkrel_def linkrel_straighten_def step2_subresult7 by auto
 have step2_subresult9: 
     "linkrel 
         (Abs_diagram ((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
                      \<circ>(basic ((cement cap)\<otimes>(cement vert)\<otimes> w4))\<circ>(?z3))) 
         (Abs_diagram ((x1) \<circ>(basic ((cement vert)\<otimes>w4))\<circ>(basic ((cement vert) \<otimes>w4))\<circ>(?z3)))"
           using step2_subresult8 by auto
 have step2_subresult10: 
    "linkrel_equiv 
      (Abs_diagram ((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
                    \<circ>(basic ((cement cap)\<otimes>(cement vert)\<otimes>w4))\<circ>((basic y1)\<circ> z1))) 
      (Abs_diagram ((x1) \<circ>(basic ((cement vert)\<otimes>w4))\<circ>(basic ((cement vert)\<otimes>w4))\<circ>((basic y1)\<circ> z1)))"
           using step2_subresult9 compose_leftassociativity r_into_rtranclp linkrel_equiv_def
           by metis
 have step2_subresult11: 
   "linkrel_equiv 
       (Abs_diagram ((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
                    \<circ>(basic ((cement cap)\<otimes>(cement vert)\<otimes>w4))\<circ>((basic y1)\<circ> z1)))     
       (Abs_diagram ((x1) \<circ>(basic (?z4))\<circ>(basic (?z4))\<circ>((basic y1)\<circ> z1)))"
            using step2_subresult10 step2_subresult1 w_subst
            by (auto)
 have step2: 
    "linkrel_equiv 
      (Abs_diagram ((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
           \<circ>(basic ((cement cap)\<otimes>?z4))\<circ>((basic y1)\<circ> z1)))      
      (Abs_diagram ((x1) \<circ>(basic (?z4))\<circ>(basic (?z4))\<circ>((basic y1)\<circ> z1)))"
             using step2_subresult11 step2_subresult1 Link.abs_eq_iff compose_Nil 
             leftright_associativity step1 step2_subresult4 step2_subresult6 subresult8 w_subst
             by (metis)
(*step 3*)
 have step3_subresult1 :
   "snd (count  ?z4) = fst (count y1) " 
       using assms preliminary_result6 subresult8
       by auto
 have step3_subresult2: "snd (count (cement cap)) = 0" 
       using  count_def brickcount_def  brickcount.simps(3) count.simps(1) snd_conv by (metis)
 have step3_subresult3: "strands (vert#(cement vert))" 
       using  append_blocks_def strands_def  
       brickstrand.simps(1) strands.simps(1) strands.simps(2) by metis
 have step3_subresult4: "(vert#(cement vert)) = ((cement vert)\<otimes>(cement vert))" 
        using append_blocks_Nil by metis
 have step3_subresult5: "strands ((cement vert)\<otimes>(cement vert))" 
        using step3_subresult3 step3_subresult4
        by metis
 let  ?a ="Abs_diagram (((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)))
                       \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>?z4))\<circ>(basic ((cement cap)\<otimes>y1))\<circ> z1) "
 let ?b = " (Abs_diagram (((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)))
                       \<circ>(basic ((cement cap)\<otimes>?z4))\<circ>(basic y1)\<circ> z1)) "
 have step3_subresult6: " \<exists>a1.\<exists>b1.\<exists>b2.\<exists>A.\<exists>B.\<exists>a2.(?a = Abs_diagram
                          ((a1)\<circ>(basic (A \<otimes> b1))\<circ>(basic (B \<otimes> b2))\<circ>(a2)))"
          using exI by metis
 have step3_subresult7: " \<exists>a1.\<exists>b1.\<exists>b2.\<exists>a2.\<exists>B.
                           (?b  = (Abs_diagram ((a1)\<circ>(basic (B\<otimes>b1))\<circ>(basic (b2))\<circ>(a2))))"
          using exI by metis
 have step3_subresult8: " \<exists>a1.\<exists>b1.\<exists>b2.\<exists>A.\<exists>B.\<exists>a2.(
                   (?a = Abs_diagram ((a1)\<circ>(basic (A \<otimes>b1 ))\<circ>(basic (B \<otimes> b2))\<circ>(a2))) 
                 \<and> (?b  = (Abs_diagram ((a1)\<circ>(basic (B\<otimes>b1))\<circ>(basic (b2))\<circ>(a2))))
                 \<and>((snd (count b1)) = (fst (count b2)))
                 \<and>((snd (count B)) = 0)
                 \<and>(strands A))" 
          using compose_leftassociativity step2_subresult1 subresult8 w_subst step3_subresult5 
          step3_subresult7  exI assms leftright_associativity step2_subresult4 step2_subresult6
          step3_subresult6 step3_subresult7 step3_subresult1  step3_subresult2  step3_subresult5 
          exI assms leftright_associativity compose_leftassociativity
          by metis
 have step3_subresult9: "linkrel_compabove_centerright ?a ?b" 
          using step3_subresult8 linkrel_compabove_centerright_def step2_subresult3 step3_subresult6 
          step3_subresult7  zero_reorient by metis
 have step3_subresult10: "linkrel_compabove ?a ?b" 
          using step3_subresult9 linkrel_compabove_def by auto
 have step3_subresult11: "linkrel_compress ?a ?b" 
          using step3_subresult10 linkrel_compress_def by auto
 have step3_subresult12: "linkrel ?a ?b" 
          using step3_subresult11 linkrel_def by auto
 have step3_subresult13: "linkrel_equiv ?a ?b"
          using step3_subresult12 linkrel_equiv_def r_into_rtranclp  
          by (metis (full_types) r_into_rtranclp)
 have step3: 
 "linkrel_equiv
    (Abs_diagram (((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)))
             \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>?z4))\<circ>(basic ((cement cap)\<otimes>y1))\<circ> z1))
    (Abs_diagram (((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)))
              \<circ>(basic ((cement cap) \<otimes>?z4))\<circ>(basic y1)\<circ> z1)) "
            using step3_subresult13 by auto
(*step 4*)
 let ?p = "(x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))"
 let ?q = "(basic ((cement cap) \<otimes> y1))\<circ>z1"
 let ?r = " basic ((cement vert) \<otimes> (cement vert)\<otimes>?z4)"
 have step4_subresult1: "strands ((cement vert) \<otimes> (cement vert)\<otimes>?z4)"
             using assms  append_blocks.append_blocks_Nil preliminary_result3 step2_subresult1 
             strands.simps(2) leftright_associativity test_0 strand_make_vert_block 
             wall_count.simps(1) by (metis)
 have step4_subresult2: "fst (count ((cement cap)\<otimes>y1)) =  
                                              (fst (count (cement cap))) + fst (count (y1)) "
             using fst_count_additive by auto
 have step4_subresult3: "fst (count ((cement cap))) =  2"
             using  count_def brickcount_def  by (metis brickcount.simps(3) count.simps(1) fst_conv)
 have step4_subresult4: "fst (count ((cement cap)\<otimes>y1)) = fst (count (y1))+2"
             using step4_subresult2 step4_subresult3 add_strict_increasing dbl_def dbl_simps(3) 
            order_refl zero_less_two by auto
 have step4_subresult5: "fst (count ((cement cap)\<otimes>y1)) > 1" using step4_subresult4 assms by auto
 have step4_subresult6: "snd (wall_count ?p) = snd (count ((cement vert)\<otimes>(cement cup)\<otimes>w4))"
             using wall_count_def  snd_conv wall_count.simps(1) wall_count_compose by auto 
 have step4_subresult7: "snd (count ((cement vert)\<otimes>x)) >0 "
            using snd_count_positive  brickcount_def count_def make_vert_block.simps(1) 
            make_vert_block_fstsndequality make_vert_blocks_positiveblock_length
            by (metis add_nonneg_eq_0_iff antisym_conv1 snd_count_additive snd_count_nonnegative)
 have step4_subresult8: "snd (count ((cement vert)\<otimes>((cement cap)\<otimes>w4))) > 0"
            using step4_subresult7
            by (metis add_nonneg_eq_0_iff brickcount.simps(1) count.simps(1) le_neq_trans snd_conv
            snd_count_additive snd_count_nonnegative zero_neq_one)
 have step4_subresult9: "snd (wall_count ?p) > 0"
            using step4_subresult6 step4_subresult8
            by (metis One_nat_def add_0_iff le_neq_trans make_vert_block.simps(1) 
            make_vert_block_sndequality of_nat_1 of_nat_Suc snd_count_additive 
            snd_count_nonnegative snd_count_positive zero_neq_one)
 have step4_subresult10: 
    "linkrel_compress_null  (Abs_diagram (?p\<circ>?r\<circ>?q)) (Abs_diagram (?p\<circ>?q))"
           using step4_subresult1 step4_subresult7 linkrel_compress_null_def 
           leftright_associativity step4_subresult6 step4_subresult8 step4_subresult9 by (metis)
 have step4_subresult11: 
     "linkrel_compress  (Abs_diagram (?p\<circ>?r\<circ>?q)) (Abs_diagram (?p\<circ>?q))"
           using step4_subresult10 linkrel_compress_def by auto
 have step4_subresult12: 
      "linkrel (Abs_diagram (?p\<circ>?q)) (Abs_diagram (?p\<circ>?r\<circ>?q))"
           using step4_subresult11 step4_subresult10 linkrel_def by auto
 have step4_subresult13:
 "linkrel
     (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
                  \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>?z4))\<circ>(basic ((cement cap) \<otimes> y1))\<circ>z1))
      (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))\<circ>(basic ((cement cap) \<otimes> y1))\<circ>z1))"
            using step4_subresult12  compose_leftassociativity linkrel_def by metis
 have step4: 
 "linkrel_equiv
     (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))\<circ>(basic ((cement cap) \<otimes> y1))\<circ>z1))
     (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
                     \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>?z4))\<circ>(basic ((cement cap) \<otimes> y1))\<circ>z1))"
             using step4_subresult10 linkrel_equiv_def compose_leftassociativity 
             leftright_associativity r_into_rtranclp step3_subresult11 step4_subresult12 
             step4_subresult13 by (metis (full_types))
 (*combining steps*)                      
 have combine_vert: 
  "linkrel_equiv  (Abs_diagram (((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)))
                                \<circ>(basic ((cement cap) \<otimes>?z4))\<circ>(basic y1)\<circ> z1))
                  (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))"
             using step1 step2 rtranclp_trans linkrel_equiv_def Link.abs_eq_iff compose_Nil 
             compose_leftassociativity step3_subresult7 step3_subresult8
             by (metis C step2_subresult0 step2_subresult10 step2_subresult2 step2_subresult4 
             step2_subresult5 test_0 test_1 w_subst)                    
 have combine_cup:
  "linkrel_equiv 
      (Abs_diagram (((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)))
                   \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>?z4))\<circ>(basic ((cement cap)\<otimes>y1))\<circ> z1))
       (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))" 
               using step3 combine_vert linkrel_equiv_def rtranclp_trans
               compose_leftassociativity leftright_associativity 
               step2 step2_subresult1 step2_subresult2  subresult_equiv3 
               w_subst
               by (metis) 
 have combine_compress:
  "linkrel_equiv 
      (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))\<circ>(basic ((cement cap) \<otimes> y1))\<circ>z1))
      (Abs_diagram (x1 \<circ> basic y1 \<circ>z1))"
               using combine_cup step4 rtranclp_trans  combine_cup step4  rtranclp_trans  
               linkrel_equiv_def  compose_leftassociativity leftright_associativity 
               step2 step2_subresult1 step2_subresult2  subresult_equiv3 
               w_subst by metis 
 from combine_compress show ?thesis by (simp)
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
 have "fst (brickcount cup) = 0" using brickcount_def by auto
 from this have subresult2:"fst (count ((cement cup))) = 0" using count_def  count.simps(1) 
       by (metis)
 have subresult3: " strands ((cement vert)\<otimes>(cement vert))" using  append_blocks_Nil strands_def 
       by (metis brickstrand.simps(1) strands.simps(1) strands.simps(2))
 let ?a = "(Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2))
           \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"
 let ?b = "(Abs_diagram ((x1 \<circ> (basic y1)) \<circ>(basic ((cement cup)\<otimes>y2))
           \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"
 have subresult4: "  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.
          (?a = Abs_diagram ((y1)\<circ>(basic (A\<otimes>w1))\<circ>(basic (B\<otimes>w2))\<circ>(y2)) 
        \<and> (?b = Abs_diagram ((y1)\<circ>(basic (w1))\<circ>(basic (A\<otimes>w2))\<circ>(y2)))
        \<and> ((snd (count w1)) = (fst (count w2)))
        \<and> ((fst (count A)) = 0)
        \<and> (strands B))" 
       using assms subresult2 subresult3 
       by (metis compose_leftassociativity leftright_associativity) 
 from this have "linkrel_compbelow_centerright ?a ?b" 
        using linkrel_compbelow_centerright_def by auto
 from this have "linkrel_compbelow ?a ?b" 
        using linkrel_compbelow_def by auto
 from this have "linkrel_compress ?a ?b" 
        using linkrel_compress_def by auto
 then have " linkrel ?a ?b" 
         using linkrel_def by auto
 then have "linkrel_equiv ?a ?b" 
         using linkrel_equiv_def  r_into_rtranclp by (metis)
 then have subresult5: 
 "linkrel_equiv  
     (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2))
                   \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
     (Abs_diagram ((x1 \<circ> (basic y1)) \<circ>(basic ((cement cup)\<otimes>y2))
                   \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"
            by auto
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
 have subresult1: 
  "linkrel_equiv 
    (Abs_diagram ((x1 \<circ> (basic y1)) \<circ>(basic ((cement cup)\<otimes>y2))
                 \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
    (Abs_diagram ((x1 \<circ> (basic y1)) \<circ> basic y2 \<circ>z1))"  
                using assms metaequivalence_left by auto
 have subresult2: 
   "linkrel_equiv 
       (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2))
                    \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
       (Abs_diagram (x1 \<circ> (basic y1) \<circ>(basic ((cement cup)\<otimes>y2))
                     \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))"
           using assms metaequivalence_left_drop compose_leftassociativity by auto
 then have 
  "linkrel_equiv 
       (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1))\<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y2))
                    \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
       (Abs_diagram (x1 \<circ> (basic y1) \<circ> basic y2 \<circ>z1))"  
          using subresult1  rtranclp_trans  Link.abs_eq_iff compose_leftassociativity assms 
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
 have "fst (brickcount cup) = 0" using brickcount_def by auto
 from this have subresult2:"fst (count ((cement cup))) = 0" 
     using count_def  count.simps(1) by (metis)
 have subresult3: " strands ((cement vert)\<otimes>(cement vert))" 
     using  append_blocks_Nil strands_def 
     by (metis brickstrand.simps(1) strands.simps(1) strands.simps(2))
 let ?a = " (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>(cement cup)))\<circ>(basic (y2\<otimes>(cement vert)\<otimes>(cement vert)))
                         \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
 let ?b = "(Abs_diagram (x1 \<circ> (basic y1) \<circ>(basic (y2\<otimes>(cement cup)))
                           \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
 have subresult4: "  \<exists>y1.\<exists>w1.\<exists>w2.\<exists>A.\<exists>B.\<exists>y2.(
   (?a = Abs_diagram ((y1)\<circ>(basic (w1\<otimes>A))\<circ>(basic (w2\<otimes>B))\<circ>(y2))) 
  \<and>(?b = Abs_diagram ((y1)\<circ>(basic (w1))\<circ>(basic (w2\<otimes>A))\<circ>(y2)))
  \<and>((snd (count w1)) = (fst (count w2)))
  \<and>((fst (count A)) = 0)
  \<and>(strands B))" 
       using assms subresult2 subresult3 
       by (metis compose_leftassociativity leftright_associativity) 
 from this have "linkrel_compbelow_centerleft ?a ?b" 
       using linkrel_compbelow_centerleft_def by auto
 from this have "linkrel_compbelow ?a ?b" 
       using linkrel_compbelow_def by auto
 from this have "linkrel_compress ?a ?b" 
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
 from this show ?thesis by auto
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
 have subresult1: 
  "linkrel_equiv 
     (Abs_diagram ((x1 \<circ> (basic y1)) \<circ>(basic ((cement cup)\<otimes>y2))
                  \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w4))\<circ>z1))
     (Abs_diagram ((x1 \<circ> (basic y1)) \<circ> basic y2 \<circ>z1))"  
                using assms metaequivalence_left  by auto
 then have "linkrel_equiv 
      (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>(cement cup)))\<circ>(basic (y2\<otimes>(cement vert)\<otimes>(cement vert)))
                  \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
      (Abs_diagram (x1 \<circ> (basic y1) \<circ>(basic (y2\<otimes>(cement cup)))
                  \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))"
                 using metaequivalence_right_drop assms by auto
 from this have  
     "linkrel_equiv 
         (Abs_diagram (((x1)\<circ>(basic (y1\<otimes>(cement cup))))
            \<circ>(basic (y2\<otimes>(cement vert)\<otimes>(cement vert)))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
         (Abs_diagram ((x1 \<circ> (basic y1)) \<circ> basic y2 \<circ>z1))" 
               using subresult1  rtranclp_trans Link.abs_eq_iff compose_leftassociativity assms
              by (metis compose_Nil metaequivalence_right test_0 walls.distinct(1))
 from this show  ?thesis using compose_leftassociativity by auto
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
 have subresult1: 
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
 then have subresult2:"(snd (count (y2\<otimes>(cement vert)\<otimes>(cement vert)))) = (snd (count (y2)) + 2)"
   using  append_blocks_Nil  append_blocks_Cons brickcount_def count_def 
   by (metis (hide_lams, no_types) brickcount.simps(1) count.simps(1) count_rightcompose
      dbl_def dbl_simps(3) snd_conv)
 then have "snd (count (y2 \<otimes> (cement vert) \<otimes> (cement vert))) > (snd (count y2))" 
   by auto
 from this have step1: "snd (count (?p2)) > 1" 
   using assms  by auto
 have  "(fst (count (x\<otimes>(cement vert)\<otimes>(cement vert)))) = (fst (count (x\<otimes>(cement vert))) + 1)"
   using  append_blocks_Nil append_blocks_Cons brickcount_def count_def 
   by (metis (hide_lams, no_types) brickcount.simps(1) count.simps(1) count_rightcompose
     leftright_associativity fst_conv)
 then have assm2_substep1:"(fst (count (y2\<otimes>(cement vert)\<otimes>(cement vert)))) = (fst (count (y2)) + 2)"
    using  append_blocks_Nil append_blocks_Cons brickcount_def count_def
    by (metis (hide_lams, no_types) brickcount.simps(1) count.simps(1) count_rightcompose
    dbl_def dbl_simps(3) fst_conv)
 have "(snd (count (y1\<otimes>(cement cup)))) = (snd (count y1)) + 2"
    using  count_def snd_conv append_blocks_Cons count_cup_rightcompose  by auto
 then have "(snd (count (y1\<otimes>(cement cup)))) = ((fst (count y2)) +2)" 
    using assms by auto
 then  have step2: "fst (count ?p2) = snd (count ?p1)" 
    using assm2_substep1  by auto
 from subresult2 have "snd (count ?p2) = (snd (count y2)) + 2"  
   by auto
 from this have subresult5: "w5 = make_vert_block (nat (((snd (count ?p2)) + (-2))))" 
    using assms by auto
 have subresult3: "(((snd (count ?p2))>1) 
                   \<and> (w5= make_vert_block  (nat ((snd (count ?p2)) + (-2))))
                   \<and>(fst (count ?p2) = snd (count ?p1)))"
   using assms step1 step2 subresult5 by auto
 then  have 
   "linkrel_equiv 
         (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>?p1))\<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>?p2))
                      \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes>w5))\<circ>?p3))
         (Abs_diagram (x1 \<circ> basic ?p1\<circ> basic ?p2\<circ>?p3))"
    using metaequivalence_left_doubledrop_condition by auto
 then have subresult6: 
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
    using subresult1 rtranclp_trans Link.abs_eq_iff by (metis)
 from this  show ?thesis by (simp)
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
 from metaequivalence_right and assms have subresult1: 
     "linkrel_equiv 
        (Abs_diagram ((x1)\<circ>(basic (y1\<otimes>(cement cup)))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
        (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))" 
      by auto
 let ?y2 = "y1 \<otimes> (cement cup)"
 let ?z2 = "(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1"
 have subresult2:"(snd (count (?y2))) = (snd (count y1)) + 2"
      using  count_def snd_conv append_blocks_Cons count_cup_rightcompose by auto
 from this and assms have subresult3:"(snd (count (?y2))) >1" by auto
 from subresult2 have subresult4: "w5 = make_vert_block (nat (snd (count ?y2) + (-2)))" 
      using assms by auto
 from this and assms and subresult3 and metaequivalence_left have 
  "linkrel_equiv 
     (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>?y2))\<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))\<circ>?z2))
     (Abs_diagram ((x1)\<circ>(basic (?y2))\<circ>?z2))" 
     by auto
 then have 
   "linkrel_equiv 
      (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1\<otimes>(cement cup)))
                   \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))
                   \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
      (Abs_diagram ((x1)\<circ>(basic (y1 \<otimes> (cement cup)))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))" 
     by auto
 from this and subresult1 have 
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
 from assms and metaequivalence_bottomright have subresult1: 
   "linkrel_equiv 
      (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1))
      (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))"  
      by auto
 let ?y2 = "y1 \<otimes> (cement cap)"
 let ?x2 = "x1\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))"
 have subresult2:"(fst (count (?y2))) = (fst (count y1)) + 2"
      using count_def fst_conv append_blocks_Cons count_cup_rightcompose 
      by (metis brickcount.simps(3) count.simps(1) fst_count_additive)
 from this and assms have subresult3:
     "(fst (count (?y2))) >1" 
     by auto
 have subresult4: " snd (count (y1\<otimes>(cement cap))) = snd (count y1)" 
     using  count_def snd_conv append_blocks_Cons count_cup_rightcompose
     by (metis (hide_lams, no_types) brickcount.simps(3) comm_monoid_add_class.add.right_neutral 
     count.simps(1) snd_count_additive)
 have "snd (count (w4\<otimes>(cement cup)\<otimes>(cement vert))) = snd (count w4) + snd (count (cement cup)) +
       snd (count (cement vert))" using leftright_associativity snd_count_additive 
     by (auto)
 from this have subresult5: "snd (count (w4\<otimes>(cement cup)\<otimes>(cement vert))) = snd (count w4) +3"
     using count_def  snd_conv by (metis ab_semigroup_add_class.add_ac(1) brickcount.simps(1) 
     brickcount.simps(2) count.simps(1) inc.simps(2) numeral_inc)
 have "fst (count (w4\<otimes>(cement cup)\<otimes>(cement vert))) 
            =  fst (count w4) + fst (count (cement cup)) + fst( count (cement vert))"
     using leftright_associativity fst_count_additive by auto
 from this have subresult6: "fst (count (w4\<otimes>(cement cup)\<otimes>(cement vert))) =  fst (count w4) + 1"
     using count_def  fst_conv brickcount.simps(1) count.simps(1) fst_count_additive 
     fstcount_cup_rightcompose by (metis (full_types))
 have "(snd (count (make_vert_block n))) = (int n)+1"  
      using make_vert_block_sndequality by auto
 have subresult7: "(fst (count w4)) = (int (nat ((fst (count y1)) + (-2))))+1" 
      using assms make_vert_block_fstequality by (metis)
 have "(fst (count y1) + (-2)) \<ge> 0" using assms by auto
 from this  have "(int (nat ((fst (count y1)) + (-2)))) = (fst (count y1) + (-2))" 
      using int_nat_eq assms by auto
 from this and subresult7
            have "fst (count w4) =  (fst (count y1)) + (-2) + 1" 
      by auto
 from this have subresult8: "fst (count w4) = fst (count y1) + (-1)" by auto
 from this and make_vert_block_fstsndequality and assms have 
           "snd (count w4) =  fst (count y1) + (-1)"
      by auto
 from this and subresult5 have 
          "snd (count (w4\<otimes>(cement cup)\<otimes>(cement vert))) = fst (count y1) + (-1) + 3" 
      by auto
 from this and subresult2 have subresult9: 
           "snd (count (w4\<otimes>(cement cup)\<otimes>(cement vert))) = fst (count (y1\<otimes>(cement cap)))" 
      by auto
 from subresult8 and subresult6 have subresult10: 
          "fst (count (w4\<otimes>(cement cup)\<otimes>(cement vert))) = fst (count y1)" 
      by auto
 from subresult2 have subresult11: 
          "w5 = make_vert_block (nat (fst (count ?y2) + (-2)))" 
      using assms by auto
 have subresult12: "fst (wall_count ((basic y1)\<circ>z1)) = snd(wall_count x1)" 
      using assms diagram_fst_equals_snd by metis
 have  "fst (wall_count ((basic y1)\<circ>z1)) = fst(count y1)" 
      using wall_count_def compose_def by auto
 from this and subresult12 have "snd(wall_count x1) = (fst (count y1))" by simp
 from this and subresult10 have subresult13: 
          "snd(wall_count x1) = (fst (count (w4\<otimes>(cement cup)\<otimes>(cement vert))))" 
      by auto
 have subresult14:"snd (wall_count (x1\<circ>(basic y1))) = fst(wall_count z1)" 
      using assms diagram_fst_equals_snd by (metis compose_leftassociativity)
 have "snd (wall_count (x1\<circ>(basic y1))) = snd (count y1)" 
      using wall_count_def compose_def by (metis snd_conv wall_count.simps(1) wall_count_compose)
 from subresult14 and this have subresult15: "fst(wall_count z1) =  snd (count y1)" 
       by simp
 from this and subresult4 have subresult16: "fst(wall_count z1) = snd (count ?y2)" 
       by simp
 have "(fst (wall_count ((basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic ?y2)\<circ>z1))) 
        = fst (count (w4\<otimes>(cement cup)\<otimes>(cement vert)))"
       by auto
 from this and  subresult13 have subresult17: 
        "snd(wall_count x1) 
         = (fst (wall_count ((basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic ?y2)\<circ>z1)))"
        by auto
 have  "list_sum (wall_count_list (?y2*z1)) = 0" 
        using subresult16 add_nonneg_eq_0_iff assms(4)compose_Nil diagram_list_sum_zero 
        diagram_wall_count_list_zero list_sum.simps(2) list_sum_append_blocks 
        monoid_add_class.add.left_neutral subresult15 wall_count_list.simps(2) 
        wall_count_list_compose wall_count_list_list_sum_non_negative 
        by (metis)
 from this have subresult18: " list_sum (wall_count_list ((basic ?y2)\<circ>z1)) = 0" 
        by auto
 from subresult9 have 
        "snd (count (w4\<otimes>(cement cup)\<otimes>(cement vert))) = (fst (wall_count (((basic ?y2)\<circ>z1))))"
        by (metis fst_conv wall_count.simps(1) wall_count_compose)
 from this and subresult18
      have "list_sum (wall_count_list ((w4\<otimes>(cement cup)\<otimes>(cement vert))*((basic ?y2)\<circ>z1))) = 0"
      using add_nonneg_eq_0_iff assms(4) compose_Nil diagram_list_sum_zero 
      diagram_wall_count_list_zero list_sum.simps(2) list_sum_append_blocks 
      monoid_add_class.add.left_neutral subresult15 wall_count_list.simps(2) 
      wall_count_list_compose wall_count_list_list_sum_non_negative
      by (metis `fst (wall_count (basic y1 \<circ> z1)) = fst (count y1)` `
      snd (wall_count x1) = fst (count y1)` diff_self subresult16 subresult9)
 from this have subresult19: 
      "list_sum (wall_count_list ((basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>((basic ?y2)\<circ>z1))) = 0"
      by auto
 from diagram_list_sum_subsequence have subresult20: 
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
 from this and subresult19 and subresult20 and subresult17 
     have subresult21: 
      "list_sum (wall_count_list ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
                                  \<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1)) 
                         = 0"
         by (metis diff_self monoid_add_class.add.right_neutral wall_count_list_list_sum_abs)
 have subresult22: 
      "(fst (wall_count ((x1)\<circ>(basic y1)\<circ>z1))) = fst(wall_count x1)" 
        using wall_count_def compose_Cons by (metis fst_conv wall_count_compose)
 have "abs( fst(wall_count (x1 \<circ>(basic y1)\<circ>z1))) = 0" 
        using well_defined_fst_wall_count assms  by metis
 from subresult22 and this have subresult23:"abs (fst(wall_count x1)) = 0"  
        by auto
 have subresult24:" (snd (wall_count ((x1)\<circ>(basic y1)\<circ>z1))) = snd(wall_count z1)" 
        using wall_count_def compose_Cons 
        by (metis snd_conv wall_count_compose)
 have "abs( snd(wall_count (x1 \<circ>(basic y1)\<circ>z1))) = 0" 
        using well_defined_snd_wall_count assms by metis
 from subresult24 and this have subresult25:"abs (snd(wall_count z1)) = 0"  
        by auto
 have subresult26: 
  "(fst (wall_count (((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1))))
                         = fst(wall_count x1)" 
          using wall_count_def compose_Cons by (metis fst_conv wall_count_compose)
 from this and subresult23 have subresult27:
   "abs (fst (wall_count (((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
           \<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1)))) = 0" by auto
 have subresult28:" (snd (wall_count (((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
           \<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1))))
                      = snd (wall_count z1)" 
           using wall_count_def compose_Cons by (metis snd_conv wall_count_compose)
 from subresult24  and subresult25 and subresult28 and subresult21 have subresult29:
  "abs (snd (wall_count (((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
           \<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1))))=
                   0" 
            by auto
 from subresult27 and subresult29 and subresult21 have subresult30: 
   "well_defined  (((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1))" 
           using monoid_add_class.add.left_neutral well_defined_def by (auto)
 from this and assms and subresult3 and metaequivalence_bottomleft and subresult30
  have "linkrel_equiv 
       (Abs_diagram ((?x2)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes> w5))\<circ>(basic ((cement cap)\<otimes>?y2))\<circ>z1))
       (Abs_diagram ((?x2)\<circ>(basic (?y2))\<circ>z1))"
            using compose_leftassociativity subresult11 by (metis)
 from this have 
   "linkrel_equiv
     (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))
             \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes> w5))\<circ>(basic ((cement cap)\<otimes>y1\<otimes>(cement cap)))\<circ>z1))  
     (Abs_diagram ((x1)\<circ>(basic (w4\<otimes>(cement cup)\<otimes>(cement vert)))\<circ>(basic (y1\<otimes>(cement cap)))\<circ>z1))" 
 using compose_leftassociativity by auto
 from this and subresult1 have 
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
 from this have 
          "linkrel_equiv 
             (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
                           \<circ>(basic ((cement cap)\<otimes>y1))\<circ>(basic (y2\<otimes>(cement cup)))
                           \<circ>(basic (w5\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
             (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))\<circ>(basic ((cement cap)\<otimes>y1))
                           \<circ>(basic y2)\<circ>z1))"
       using compose_leftassociativity by (auto)
 from this and subresult have 
   "linkrel_equiv  
        (Abs_diagram ((x1)\<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4)) \<circ>(basic ((cement cap)\<otimes>y1))
                      \<circ>(basic (y2\<otimes>(cement cup)))\<circ>(basic (w5\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
        (Abs_diagram (x1 \<circ> (basic y1)\<circ> (basic y2)\<circ>z1))"
         using rtranclp_trans Link.abs_eq_iff by metis
 from this show ?thesis by simp
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
         using assms metaequivalence_left by (metis (full_types))
 from this have 
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
 from this show ?thesis by simp
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
 from this have subresult1:
 "linkrel_equiv 
      (Abs_diagram (x1\<circ> (basic y1)\<circ>(basic ((cement cup)\<otimes>y2\<otimes>(cement cup)))
                 \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                 \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5)) \<circ> (basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
      (Abs_diagram (x1\<circ> (basic y1)\<circ>(basic y2)\<circ>(basic y3)\<circ>z1))" 
    using compose_leftassociativity by simp
 have subresult2: "fst (count (cement cup)) = 0" 
       using count_def add_left_cancel comm_monoid_add_class.add.right_neutral fst_count_additive 
       fstcount_cup_rightcompose by (auto)
 let ?z2 = "(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
            \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5))\<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1"
 let ?w2 = "y2 \<otimes> (cement cup)"
 have "fst (count ?w2) = fst (count y2)" 
        using fstcount_cup_rightcompose by auto
 from this and assms have subresult3:"fst (count ?w2) = snd (count y1)" 
        by auto
 let ?B = "(cement vert) \<otimes> (cement vert)"
 have subresult4: "strands ?B"
        using append_blocks.append_blocks_Nil make_vert_block.simps(1) strand_make_vert_block 
        strands.simps(2) by (metis)
 from subresult4 and subresult2 and subresult3 and exI  have 
       "(strands ?B) \<and> (fst (count ?w2) = snd (count y1)) \<and> (fst (count (cement cup)) = 0)"
        by auto
 from this and exI and linkrel_compbelow_centerright_def have 
        "linkrel_compbelow_centerright 
              (Abs_diagram (x1 \<circ> (basic ((cement cup) \<otimes> y1)) \<circ> (basic (?B\<otimes> ?w2)) \<circ> ?z2))
              (Abs_diagram (x1 \<circ> (basic ( y1)) \<circ> (basic ((cement cup) \<otimes> ?w2)) \<circ> ?z2))"
        by metis
 from this and compose_leftassociativity and leftright_associativity have 
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
 from this have
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
 from this have 
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
 from this have
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
 from this have 
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
 from this and subresult1 and r_into_rtranclp rtranclp_trans have subresult5:
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
 from this and assms have subresult6: "snd (count ((cement cup) \<otimes> y1)) = 2 + fst (count y2)" 
       by auto
 let ?subs1 = "((cement cup) \<otimes> y1)"
 let ?subs2 = " ((cement vert) \<otimes> (cement vert) \<otimes> y2)"
 have " fst (count ((cement vert) \<otimes> (cement vert) \<otimes> y2)) = 2 + fst (count y2)"
       using fst_count_additive  by auto 
 from this and subresult6 have "snd (count (?subs1)) = fst (count (?subs2))" 
       by auto
 from this and subresult2 and subresult4 have
    "(strands ?B) \<and> (fst (count ?subs2) = snd (count ?subs1)) \<and> (fst (count (cement cup)) = 0)" 
       by auto
 from this  exI and linkrel_compbelow_centerleft_def  
 have "linkrel_compbelow_centerleft
          (Abs_diagram ((x1)\<circ>(basic (?subs1 \<otimes> (cement cup)))\<circ>(basic (?subs2\<otimes>?B))\<circ>?z2))
          (Abs_diagram ((x1)\<circ>(basic (?subs1))\<circ>(basic (?subs2\<otimes>(cement cup)))\<circ>?z2))"  
      by metis
 from this and leftright_associativity have
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
 from this and linkrel_compbelow_def have
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
 from this and linkrel_compress_def and linkrel_def have
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
 from this and  linkrel_equiv_def and  r_into_rtranclp have
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
 from this and subresult5 and r_into_rtranclp rtranclp_trans have
  "linkrel_equiv
      (Abs_diagram ((x1)\<circ>(basic ((cement cup)\<otimes>y1 \<otimes> (cement cup)))
                  \<circ>(basic ((cement vert)\<otimes>(cement vert) \<otimes> y2 \<otimes> (cement vert) \<otimes> (cement vert)))
                  \<circ>(basic ((cement vert)\<otimes>(cement vert)\<otimes>y3\<otimes>(cement vert)\<otimes>(cement vert)))
                  \<circ>(basic ((cement vert)\<otimes>(cement cap)\<otimes> w5)) 
                  \<circ>(basic (w4\<otimes>(cement cap)\<otimes>(cement vert)))\<circ>z1))
       (Abs_diagram ((x1)\<circ>(basic y1)\<circ>(basic y2)\<circ>(basic y3)\<circ>z1))"
         by (metis Link.abs_eq_iff compose_Nil)
 from this show ?thesis by auto
qed
(*prove above with sufficient condition being a well defined wall*)
end
