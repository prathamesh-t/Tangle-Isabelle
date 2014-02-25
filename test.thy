theory test
imports Tangles 
begin
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

type_synonym convert = "block => nat"

definition fstcount:: convert  where "(fstcount x) = (nat (abs ((fst (count x)))))"

definition sndcount:: convert  where "(sndcount x) = (nat (snd (count x)))"


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



text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1 \<circ>z1), where y1 is a 
block with outgoing strands, the following theorem proves that it is equivalent to the link 
diagram obtained by adding two blocks of vertical strands above y1*}

(*non seperating block refers to a block which has outgoing strands. In other words, it is not 
block which seperates two disjoint components of a link*)



definition non_seperating_block::"block \<Rightarrow> bool"
where
"non_seperating_block x \<equiv> (snd (count x)>1) "

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

text{* Given a link diagram which represents a wall of the form (x1 \<circ> basic y1 \<circ>z1), where y1 is a 
block with outgoing strands, the following theorem proves that it is equivalent to the link 
diagram obtained by adding two blocks of vertical strands above y1*}

(*non seperating block refers to a block which has outgoing strands. In other words, it is not 
block which seperates two disjoint components of a link*)


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
 have 1: " (?z4 = make_vert_block (?k+1))" 
      using assms by auto
  have 2: "w4 = (make_vert_block ?k)" 
      using assms by auto
 have 3: "(make_vert_block (?k+1)) = ((cement vert)\<otimes>(make_vert_block ?k))" 
     by (metis make_vert_induct_left)
 have 4:"?z4 = (cement vert) \<otimes>(make_vert_block ?k)  " 
     using 1 3 by auto     

 have "fst (count y1) = snd (wall_count x1)" using wall_count.simps assms(3) well_defined_def 
      compose_Nil diagram_fst_equals_snd fst_eqD   by metis
 then have step1: 
 "linkrel_equiv 
           (Abs_diagram (x1 \<circ> basic ?z4\<circ>basic ?z4 \<circ> basic y1\<circ>z1)) 
           (Abs_diagram (x1 \<circ> (basic y1)\<circ>z1))" 
         using compose_leftassociativity rtranclp_trans linkrel_doublecompress_below assms(1) by auto
    
(*step 2*) 
 have step2: 
    "linkrel_equiv 
      (Abs_diagram ((x1) \<circ>(basic ((cement vert)\<otimes>(cement cup)\<otimes>w4))
           \<circ>(basic ((cement cap)\<otimes>?z4))\<circ>((basic y1)\<circ> z1)))      
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
 then have
 "linkrel_straighten_righttopdown ?x ?y"
      using linkrel_straighten_righttopdown_def compose_leftassociativity 
      6  5 
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
(*step 3*)
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
(*step 4*)
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
 (*combining steps*)                      
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
 qed
