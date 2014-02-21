theory example
imports Link_Algebra Links
begin

text{*We prove that the link diagram with a single crossing is equivalent to the unknot*}
context Equivalence
begin

lemma left_over_well_defined:"well_defined_tangle left_over"
 proof-
 have "left_over = 
               (((cement cup)\<otimes>(cement vert))
              *((cement vert)\<otimes>(cement over))
              *(basic ((cement cap)\<otimes>(cement vert))))" 
     by auto
 then have "(domain_codomain_list (basic ((cement cap)\<otimes>(cement vert)))) = []" 
     using domain_codomain_list.simps by auto
 moreover have "domain_wall (basic ((cement cap)\<otimes>(cement vert))) = 3" 
     by auto 
 moreover have "codomain_block ((cement vert)\<otimes>(cement over)) = 3" 
     by auto
 ultimately 
   have "domain_codomain_list 
        (((cement vert)\<otimes>(cement over))*(basic ((cement cap)\<otimes>(cement vert))))
            = [0]" 
     using domain_codomain_list.simps abs_def by auto
 then have 
  "domain_wall (((cement vert)\<otimes>(cement over))*(basic ((cement cap)\<otimes>(cement vert)))) = 3" 
     by auto
 moreover have "codomain_block ((cement cup)\<otimes>(cement vert)) = 3" 
     by auto
 then have "domain_codomain_list left_over = [0,0]" using domain_codomain_list.simps abs_def
     by auto
 then have "list_sum (domain_codomain_list left_over) = 0" 
     by auto
 then show ?thesis unfolding well_defined_tangle_def by auto
 qed

lemma straight_line_well_defined:"well_defined_tangle straight_line"
 proof-
 have "straight_line = ((cement vert)*((cement vert)*(basic (cement vert))))"
        by auto
 then have "(domain_codomain_list (basic (cement vert))) = []" 
        using domain_codomain_list.simps by auto
 moreover have "domain_wall (basic (cement vert)) =1 " 
        by auto 
 moreover have "codomain_block (cement vert) = 1" 
        by auto
 ultimately have "domain_codomain_list ((cement vert)*(basic (cement vert)))= [0]" 
        using domain_codomain_list.simps abs_def by auto
 then have "domain_wall ((cement vert)*(basic (cement vert)))
       = 1" by auto
 moreover have "codomain_block (cement vert) = 1" by auto
 then have "domain_codomain_list straight_line = [0,0]" 
       using domain_codomain_list.simps abs_def
       by auto
 then have "list_sum (domain_codomain_list straight_line) = 0" by auto
 then show ?thesis unfolding well_defined_tangle_def by auto
 qed


theorem example:"(Abs_Tangle ((basic ((cement cup) \<otimes> (cement cup))) 
\<circ>(basic ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) 
\<circ> (basic ((cement cap) \<otimes> (cement cap)))))= 
 (Abs_Tangle ((basic (cement cup)) \<circ> (basic (cement cap))))" 

proof-
 have "left_over =  ((basic ((cement cup)\<otimes>(cement vert)))
           \<circ>(basic ((cement vert)\<otimes>(cement over)))
           \<circ>(basic ((cement cap)\<otimes>(cement vert))))" by auto
 have "straight_line = (basic (cement vert))
          \<circ>(basic (cement vert))
          \<circ>(basic (cement vert))" by auto
 have "uncross_negative_straighten left_over straight_line"
        using uncross_negative_straighten_def by auto
 then have "linkrel left_over straight_line" unfolding linkrel_def uncross_def by auto
 then have 1:" (left_over) = (straight_line)" using equality by auto    
 let ?w1 = "(basic ((cement cup) \<otimes> (cement vert) \<otimes> (cement vert))) 
           \<circ>(basic ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) 
           \<circ>(basic ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert)))"
 have 2:"left_over \<otimes> straight_line = ?w1" 
     proof-
     have "basic ((cement cap) \<otimes> (cement vert)) \<otimes> (basic (cement vert)) 
                  =   (basic ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert)))"
                 unfolding tensor.simps  by auto
     then have "((basic ((cement vert)\<otimes>(cement over)))
           \<circ>(basic ((cement cap)\<otimes>(cement vert)))) 
       \<otimes>  ((basic (cement vert))\<circ> (basic (cement vert)))
    = (basic ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) 
           \<circ>(basic ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert)))"
            unfolding tensor.simps by auto
     then show ?thesis by auto
     qed
 let ?w2 = "basic ((cement vert) \<otimes> (cement vert)) 
           \<circ>(basic ((cement vert) \<otimes> (cement vert))) 
           \<circ>(basic ((cement vert) \<otimes> (cement vert)))"
 have 3:"straight_line \<otimes> straight_line = (?w2)"
     proof-
     have "(basic (cement vert)) \<otimes> (basic (cement vert)) = (basic ((cement vert) \<otimes> (cement vert)))"
          by auto
     then have "((basic (cement vert))\<circ>(basic (cement vert)))
                \<otimes>((basic (cement vert))\<circ>(basic (cement vert))) 
             = (basic ((cement vert) \<otimes> (cement vert))) 
               \<circ>(basic ((cement vert) \<otimes> (cement vert)))"
               by auto
    then show ?thesis by auto 
    qed
 have "well_defined_tangle (left_over) \<and> (well_defined_tangle straight_line)\<and> (straight_line=left_over)" 
     using left_over_well_defined straight_line_well_defined 1  by auto
 then have "(left_over \<otimes> straight_line) = (straight_line \<otimes> straight_line)"
       using 1  tensor_eq  by auto
 have "well_defined_tangle (?w1)" unfolding well_defined_tangle_def list_sum_def domain_codomain_list_def
          concatenate_def by (metis block.distinct(1) right_empty_block)              
 then have  "Abs_Tangle (left_over \<otimes> straight_line) = Abs_Tangle (left_over) \<otimes> Abs_Tangle( straight_line)" 
    unfolding compose_Tangle_def
 moreover have "\<exists>A2.\<exists>B2. (?y \<otimes> ?z)= (A2 \<otimes> B2)" by metis
 moreover have "linkrel ?z ?z" unfolding linkrel_def linkrel_reflexive_def by auto
 ultimately have "linkrel_diagram_tensor (?x \<otimes> ?z) (?y \<otimes> ?z)" using 1  linkrel_diagram_tensor_def
            by metis
 then have "linkrel_diagram_tensor ?w1 ?w2" using 2 3 by auto
 then have "linkrel_diagram ?w1 ?w2" unfolding linkrel_diagram_def by auto
 then have 
have 1:"codomain_block (cement cap) = 0"  by auto
 have 2: "make_vert_block (nat (domain_block (cement cap))) = ((cement vert) \<otimes> (cement vert))" 
     using concatenate.simps
     sledgehammer
 let ?B = "(cement cap)"
 let ?A = "(cement vert) \<otimes> (cement vert)"
 let ?x = "(Abs_diagram ((basic ((cement cup) \<otimes> (cement cup))) 
   \<circ>(basic ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) 
   \<circ> (basic ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert))) \<circ>(basic  (cement cap))))"
 let ?y = " (Abs_diagram ((basic ((cement cup) \<otimes> (cement cup))) 
               \<circ>(basic ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) \<circ>(basic ((cement cap) \<otimes> (cement cap)))))"
 let ?y1 = "(basic ((cement cup) \<otimes> (cement cup))) \<circ>(basic ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) "
 let ?z1 = "(cement cap)"
 have 3:"?x = Abs_diagram ((?y1)\<circ>(basic (?z1\<otimes>?A))\<circ>(basic (?B)))" by auto
 have 4:"?y = Abs_diagram ((?y1)\<circ>(basic (?z1\<otimes>?B)))" by auto
 from 1 2 3 4 have "((?x = Abs_diagram
 ((?y1)\<circ>(basic (?z1\<otimes>?A))\<circ>(basic (?B))))\<and> ((?y = Abs_diagram (
(?y1)\<circ>(basic (?z1\<otimes>?B)))))
\<and>((snd (count ?z1)) = 0)
\<and>(strands ?A))" by auto
  from this have"\<exists>z1.\<exists>A.\<exists>B.\<exists>y1.((?x = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>A))\<circ>(basic (B))))\<and> ((?y = Abs_diagram (
  (y1)\<circ>(basic (z1\<otimes>B)))))\<and>((snd (count z1)) = 0)\<and>(strands A))" by metis
 from this have "linkrel_compabove_topleft ?x ?y" using linkrel_compabove_topleft_def by auto
 from this have "linkrel_compabove ?x ?y" using linkrel_compabove_def by auto
 from this have "linkrel_compress ?x ?y" using linkrel_compress_def by auto
 from this have  "linkrel ?x ?y" using linkrel_def by auto
 from this have "linkrel_equiv ?x ?y" using linkrel_equiv_def r_into_rtranclp by metis
  from this have step1: "linkrel_equiv ?y ?x" using link_symmetry2 by auto

 let ?x = "(Abs_diagram ((basic (cement cup)) \<circ> (basic ((cement cup) \<otimes> (cement vert) \<otimes> (cement vert))) 
           \<circ>(basic ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) 
           \<circ> (basic ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert))) \<circ>(basic  (cement cap))))"
 let ?y = "(Abs_diagram ((basic ((cement cup) \<otimes> (cement cup))) 
           \<circ>(basic ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) 
           \<circ> (basic ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert))) \<circ>(basic  (cement cap))))"
 let ?A = "(cement cup)"
 let ?z2 = " (cement cup)"
 have 1: "fst (count ?z2) = 0" using   count.simps(1) brickcount.simps fst_conv by (metis) 
 let ?B = "(cement vert) \<otimes> (cement vert)"
 let ?y2 = "(basic ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) 
            \<circ> (basic ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert))) \<circ>(basic  (cement cap))"
 have "?x =  Abs_diagram ((basic (?A))\<circ>(basic (?z2\<otimes>?B))\<circ>(?y2))" by auto
 moreover have "?y = Abs_diagram ((basic (?z2 \<otimes> ?A))\<circ>(?y2))" by auto
 ultimately have "((?x = Abs_diagram ((basic (?A))\<circ>(basic (?z2\<otimes>?B))\<circ>(?y2)))
                 \<and> (?y = Abs_diagram ((basic (?z2 \<otimes> ?A))\<circ>(?y2))) \<and>((fst (count ?z2)) = 0)
                 \<and>(strands ?B))" using 1 2 by auto
 from this have "\<exists>z2.\<exists>A.\<exists>B.\<exists>y2.((?x = Abs_diagram ((basic (A))\<circ>(basic (z2\<otimes>B))\<circ>(y2)))\<and> 
                  (?y = Abs_diagram ((basic (z2 \<otimes> A))\<circ>(y2))) \<and>(0 = (fst (count z2))) 
                  \<and>(strands B))" by metis
 from this have "linkrel_compbelow_bottomleft ?x ?y" using linkrel_compbelow_bottomleft_def 
                          by auto
 from this have "linkrel_equiv ?x ?y" 
         using linkrel_equiv_def r_into_rtranclp 
          linkrel_def linkrel_compress_def linkrel_compbelow_def
            by metis
 then have step2:"linkrel_equiv ?y ?x" using link_symmetry2 by auto
 let ?x1 = " (basic (cement cup))"
 let ?y1 = " ((cement cup) \<otimes> (cement vert) \<otimes> (cement vert))"
 let ?y2 = " ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))"
 let ?y3 = " ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert))"
 let ?z1 = " (basic  (cement cap))"  
 let ?w4 =  "make_vert_block  (nat ((snd (count ?y3)) + (-2)))" 
 let ?w5 = "make_vert_block (nat ((snd (count ?y3))))"
 have 10:"(snd (count ?y1)) = snd (count ((cement cup))) + snd (count ((cement vert) \<otimes> (cement vert))) " using snd_conv 
          count.simps(2) brickcount.simps
           by (metis snd_count_additive)
 have 11:"snd (count ((cement cup))) = 2" using snd_conv count.simps(1)  brickcount.simps      
               by metis
 moreover have 12:"snd (count ((cement vert) \<otimes> (cement vert))) = (snd (count ((cement vert)))) + (snd (count ((cement vert))))"
               by (metis snd_count_additive)
 moreover have 13:"(snd (count (cement vert))) = 1" by auto
 ultimately have 14:"(snd (count ?y1)) = 4" using 10 11 by auto
 have 15:"fst (count ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) 
  = ((fst (count (cement vert))) + (fst (count (cement over)))+ (fst (count (cement vert))))"
 using count.simps(2) by (metis comm_semiring_1_class.normalizing_semiring_rules(24) fst_count_additive)
 have 16:"snd (count ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) 
  = ((snd (count (cement vert))) + (snd (count (cement over)))+ (snd (count (cement vert))))"
 using count.simps(2) by (metis comm_semiring_1_class.normalizing_semiring_rules(24) snd_count_additive)
 have 17:"(count (cement vert)) = (1,1)" using count.simps(1)   by auto
 have 18:"(count (cement over)) = (2,2)" using count.simps(1)   by auto
 from 15 16 17 18 have 19:"fst (count ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) 
       = 4" using fst_count_additive fst_conv  by (metis add_One 
 add_One_commute inc.simps(1) inc.simps(2) inc.simps(3) numeral_inc one_plus_numeral)
 from 15 16 17 18 have 20:"snd (count ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) 
       = 4" using snd_count_additive snd_conv  by (metis add_One 
 add_One_commute inc.simps(1) inc.simps(2) inc.simps(3) numeral_inc one_plus_numeral)
 have 21:"fst (count ?y2)  = (snd (count ?y1))" using 14 19 by auto
 have 22:"fst (count (cement cap)) = 2" using count.simps(1) brickcount.simps(3) fst_conv  by (metis ) 
 have "fst (count ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert))) 
  = ((fst (count (cement cap))) + (fst (count (cement vert)))+ (fst (count (cement vert))))"  using count.simps(2) 
   using count.simps(2) fst_count_additive by auto
 from this 21 17 have " fst (count ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert)))  = 4" using fst_count_additive fst_conv
           by (metis "22" inc.simps(1) inc.simps(2) inc.simps(3) numeral_inc)
 then have 23:" fst (count ?y3) = (snd (count ?y2))" using 20 by auto
 have 24:"snd (count (cement cap)) = 0" using count.simps(1) brickcount.simps(3) snd_conv  by (metis) 
 have 25:"snd (count ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert))) 
  = ((snd (count (cement cap))) + (snd (count (cement vert)))+ (snd (count (cement vert))))"
     using count.simps(2) 
   using count.simps(2) snd_count_additive by auto
 from this have 26:"snd (count ?y3) = 2"  using snd_count_additive snd_conv
       by (metis "13" "24" one_add_one plus_int_code(2))
 from this have 27:"snd (count ?y3) > 1" by auto
 have "linkrel_equiv (Abs_diagram ((?x1) \<circ>(basic ((cement cup) \<otimes> ?y1 \<otimes> (cement cup)))
         \<circ> (basic ((cement vert) \<otimes> (cement vert) \<otimes> ?y2 \<otimes> (cement vert) \<otimes> (cement vert))) 
         \<circ> (basic ((cement vert) \<otimes>(cement vert) \<otimes> ?y3 \<otimes> (cement vert) \<otimes> (cement vert)))
         \<circ> (basic ((cement vert) \<otimes> (cement cap) \<otimes> ?w5)) \<circ> (basic (?w4 \<otimes>(cement cap) \<otimes> (cement vert))) \<circ> ?z1))
             (Abs_diagram (?x1 \<circ> (basic ?y1) \<circ>(basic ?y2) \<circ> (basic ?y3) \<circ> ?z1))"
         using 27 23 21 metaequivalence_thriple_drop by metis
 then have step4: "linkrel_equiv  (Abs_diagram (?x1 \<circ> (basic ?y1) \<circ>(basic ?y2) \<circ> (basic ?y3) \<circ> ?z1))
          (Abs_diagram ((?x1) \<circ>(basic ((cement cup) \<otimes> ?y1 \<otimes> (cement cup)))
         \<circ> (basic ((cement vert) \<otimes> (cement vert) \<otimes> ?y2 \<otimes> (cement vert) \<otimes> (cement vert))) 
         \<circ> (basic ((cement vert) \<otimes>(cement vert) \<otimes> ?y3 \<otimes> (cement vert) \<otimes> (cement vert)))
         \<circ> (basic ((cement vert) \<otimes> (cement cap) \<otimes> ?w5)) \<circ> (basic (?w4 \<otimes>(cement cap) \<otimes> (cement vert))) \<circ> ?z1))
            " using link_symmetry2 by metis

 let ?t1 = " (Abs_diagram ((?x1) \<circ>(basic ((cement cup) \<otimes> ?y1 \<otimes> (cement cup)))
         \<circ> (basic ((cement vert) \<otimes> (cement vert) \<otimes> ?y2 \<otimes> (cement vert) \<otimes> (cement vert))) 
         \<circ> (basic ((cement vert) \<otimes>(cement vert) \<otimes> ?y3 \<otimes> (cement vert) \<otimes> (cement vert)))
         \<circ> (basic ((cement vert) \<otimes> (cement cap) \<otimes> ?w5)) \<circ> (basic (?w4 \<otimes>(cement cap) \<otimes> (cement vert))) \<circ> ?z1))"
 let ?y1 = "?x1"
 let ?z1 = "(cement cup)"
 let ?w1 = "(cement vert) \<otimes> (cement cup)"
 let ?z2 = "(cement vert) \<otimes> (cement vert)"
 let ?w2 = "(cement vert) \<otimes> (cement vert) \<otimes> (cement vert)"
 let ?z3 = "(cement vert) \<otimes> (cement vert) "
 let ?w3 = "(cement vert) \<otimes> (cement vert) \<otimes> (cement vert)"
 let ?y2 = " (basic ((cement vert) \<otimes> (cement cap) \<otimes> ?w5)) \<circ> (basic (?w4 \<otimes>(cement cap) \<otimes> (cement vert))) \<circ> (basic (cement cap))"
  let ?t2 = "Abs_diagram ((?y1)
       \<circ>(basic (?z1\<otimes>(cement vert)\<otimes>?w1))\<circ>(basic (?z2\<otimes>(cement vert)\<otimes>?w2))\<circ>(basic (?z3\<otimes>(cement vert)\<otimes>?w3))\<circ>(?y2))"

 have 29:"?t1 =  Abs_diagram ((?y1)
 \<circ>(basic (?z1\<otimes>(cement cup)\<otimes>(cement vert)\<otimes>?w1)\<circ>(basic (?z2\<otimes>(cement vert)\<otimes>(cement over)\<otimes>?w2))\<circ>(basic (?z3\<otimes>(cement cap)\<otimes>(cement vert)\<otimes>?w3))
  \<circ>(?y2)))" by (metis leftright_associativity)
 have 30:"snd (count ?z1) = (fst (count ?z2))"
   proof-
   have "snd (count ?z1) = 2" using 11 by auto
   moreover have 31:"fst (count ?z2) = 2" 
        using  dbl_def dbl_simps(3)  fst_conv fst_count_additive  by auto
   ultimately show ?thesis by auto
   qed
 have 31:"snd (count ?z2) = (fst (count ?z3))"
  proof-
  have "snd (count ?z2) = 2" using  "12" "13" one_add_one by auto
  then show ?thesis using "11" "30"  by auto
  qed
 have 32:"snd (count ?w1) = fst (count ?w2)"
   proof-
     have "snd (count (cement vert)) = 1" by auto
     then have "snd (count ?w1) = 3" using snd_conv count.simps brickcount.simps 
     append.append_Nil by auto
     moreover have "fst (count ?w2) = 3" using  "11" "30" 
      fst_count_additive fst_eqD one_plus_numeral semiring_norm(3)    
           by auto
     ultimately show ?thesis by auto
     qed
 have 33:"snd (count ?w2) = fst (count ?w3)"
   proof-
   have "snd (count ?w2) = 3" using snd_conv count.simps brickcount.simps   "13"
    comm_semiring_1_class.normalizing_semiring_rules(24) dbl_inc_def dbl_inc_simps(3)
    snd_count_additive by auto 
   moreover have "fst (count ?w3) = 3" using  "11" "30" 
     fst_count_additive fst_eqD one_plus_numeral semiring_norm(3)    
           by auto
   ultimately show ?thesis by auto
   qed
 have "(\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(?t1 = Abs_diagram ((y1)
\<circ>(basic (z1\<otimes>(cement cup)\<otimes>(cement vert)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement vert)\<otimes>(cement over)\<otimes>w2))
\<circ>(basic (z3\<otimes>(cement cap)\<otimes>(cement vert)\<otimes>w3))\<circ>(y2)))))"
       by (metis leftright_associativity)
 moreover have "(\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(?t2 = Abs_diagram ((y1)\<circ>(basic (z1\<otimes>(cement vert)\<otimes>w1))\<circ>(basic (z2\<otimes>(cement vert)\<otimes>w2))\<circ>(basic (z3\<otimes>(cement vert)\<otimes>w3))
  \<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))) \<and> ((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))"  
  by (metis (hide_lams, no_types) "11" "22" "26" "30" "31" "32" fst_count_additive leftright_associativity 
  snd_count_additive)
 ultimately have  "(\<exists>y1.\<exists>z1.\<exists>z2.\<exists>z3.\<exists>w1.\<exists>w2.\<exists>w3.\<exists>y2.(?t1 = Abs_diagram ((y1)
 \<circ>(basic (z1\<otimes>(cement cup)\<otimes>(cement vert)\<otimes>w1)\<circ>(basic (z2\<otimes>(cement vert)\<otimes>(cement over)\<otimes>w2))
  \<circ>(basic (z3\<otimes>(cement cap)\<otimes>(cement vert)\<otimes>w3))\<circ>(y2))))
 \<and>(?t2 = Abs_diagram
 ((y1)\<circ>(basic (z1\<otimes>(cement vert)\<otimes>w1))\<circ>(basic (z2\<otimes>(cement vert)\<otimes>w2))\<circ>(basic (z3\<otimes>(cement vert)\<otimes>w3))\<circ>(y2)))\<and>((snd (count z1)) = 
(fst (count z2)))\<and>((snd (count z2)) = (fst (count z3))) \<and> ((snd (count w1)) = (fst
(count w2)))\<and>((snd (count w2)) = (fst (count w3))))" using 30 31 32 33  
   by (metis leftright_associativity snd_count_additive)
 from this have "linkrel_uncross_positivestraighten ?t1 ?t2" 
     using  linkrel_uncross_positivestraighten_def by auto   
 from this have "linkrel ?t1 ?t2" using linkrel_def linkrel_uncross_def by auto
 from this have step5: "linkrel_equiv ?t1 ?t2" using linkrel_equiv_def by (metis r_into_rtranclp)
 let ?x1 = ?x1
 let ?z1 = "basic (cement cap)"
 let ?y1 = "(cement vert) \<otimes> (cement vert)"
 let ?y2 = "(cement vert) \<otimes> (cement vert)"
 let ?y3 = "(cement vert) \<otimes> (cement vert)"
   
 have 34:"?t2 =  (Abs_diagram ((?x1) \<circ>(basic ((cement cup) \<otimes> ?y1 \<otimes> (cement cup)))
         \<circ> (basic ((cement vert) \<otimes> (cement vert) \<otimes> ?y2 \<otimes> (cement vert) \<otimes> (cement vert))) 
         \<circ> (basic ((cement vert) \<otimes>(cement vert) \<otimes> ?y3 \<otimes> (cement vert) \<otimes> (cement vert)))
         \<circ> (basic ((cement vert) \<otimes> (cement cap) \<otimes> ?w5)) \<circ> (basic (?w4 \<otimes>(cement cap) \<otimes> (cement vert))) \<circ> ?z1))" 
    by (metis leftright_associativity)
 have 35:"snd (count ((cement vert) \<otimes> (cement vert))) = (fst (count ((cement vert) \<otimes> (cement vert))))" using 31 by auto
 have 36:"snd (count ?y3) >1 " using "12" "13" less_add_one by auto
 have 37: "snd (count ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert))) = snd (count ?y3)"
   by (metis "12" "24" "25" comm_monoid_add_class.add.left_neutral)  
 then have "nat (snd (count ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert)))+-2)  =  (nat (snd (count ?y3)+-2))"
                        by auto
 from this have 38:"?w4 = make_vert_block  (nat (snd (count (?y3))+-2))" by auto
 from 37 have 39:"?w5 = make_vert_block (nat (snd (count ?y3)))" by auto
 from 34 35 36 38 39 have step6:"linkrel_equiv ?t2  
         (Abs_diagram (?x1 \<circ> (basic ?y1) \<circ>(basic ?y2) \<circ> (basic ?y3) \<circ> ?z1))" 
          using metaequivalence_thriple_drop by metis
 let ?t3 = "(Abs_diagram (?x1 \<circ> (basic ?y1) \<circ>(basic ?y2) \<circ> (basic ?y3) \<circ> ?z1))"
 have 40:"strands ?y1" using strands_def   "2" by (metis)
 have 41:"snd (wall_count ?x1) = 2" using wall_count_def  "11" wall_count.simps(1)  by auto
 then have 42:" snd (wall_count ?x1) > 0" by auto
 then have "linkrel_compress_null ?t3 (Abs_diagram (?x1 \<circ>(basic ?y2) \<circ> (basic ?y3) \<circ> ?z1))"
              using linkrel_compress_null_def 40 42 by metis
 then have 43:"linkrel_equiv ?t3 (Abs_diagram (?x1 \<circ>(basic ?y2) \<circ> (basic ?y3) \<circ> ?z1))"
                        using linkrel_compress_def linkrel_def linkrel_equiv_def r_into_rtranclp
                          by (metis (full_types))
 moreover have "linkrel_compress_null  (Abs_diagram (?x1 \<circ>(basic ?y2) \<circ> (basic ?y3) \<circ> ?z1))
                              (Abs_diagram (?x1  \<circ> (basic ?y3) \<circ> ?z1))"
                  using linkrel_compress_null_def 40 42 by metis
 then have 44:"linkrel_equiv (Abs_diagram (?x1 \<circ>(basic ?y2) \<circ> (basic ?y3) \<circ> ?z1))
                                 (Abs_diagram (?x1  \<circ> (basic ?y3) \<circ> ?z1))"
                        using linkrel_compress_def linkrel_def linkrel_equiv_def r_into_rtranclp
                          by (metis (full_types))
 moreover have "linkrel_compress_null  (Abs_diagram (?x1 \<circ> (basic ?y3) \<circ> ?z1))
                              (Abs_diagram ((basic (cement cup))  \<circ> (basic (cement cap))))"
                  using linkrel_compress_null_def 40 42 by metis
 then have 45:"linkrel_equiv (Abs_diagram (?x1 \<circ> (basic ?y3) \<circ> ?z1))
                                 (Abs_diagram ((basic (cement cup)) \<circ> (basic (cement cap))))"
                        using linkrel_compress_def linkrel_def linkrel_equiv_def r_into_rtranclp
                          by (metis (full_types))
 then have 46:"linkrel_equiv (Abs_diagram (?x1 \<circ>(basic ?y2) \<circ> (basic ?y3) \<circ> ?z1))
                                   (Abs_diagram ((basic (cement cup)) \<circ> (basic (cement cap))))"
                   using 44 45 linkrel_equiv_def by (metis rtranclp_trans)
 then have step7: "linkrel_equiv  ?t3
                                   (Abs_diagram ((basic (cement cup)) \<circ> (basic (cement cap))))" 
                       using 43 rtranclp_trans linkrel_equiv_def by metis
 then have step8: "linkrel_equiv  ?t2
                                   (Abs_diagram ((basic (cement cup)) \<circ> (basic (cement cap))))" 
                 using step6 rtranclp_trans linkrel_equiv_def by (metis (full_types))
 have "((linkrel_equiv ?t1 ?t2) \<and> (linkrel_equiv  ?t2
                                   (Abs_diagram ((basic (cement cup)) \<circ> (basic (cement cap))))))
  \<Longrightarrow> (linkrel_equiv  ?t1 (Abs_diagram ((basic (cement cup)) \<circ> (basic (cement cap)))))"
    using linkrel_trans by auto  
 then have step9: "linkrel_equiv  ?t1
                                   (Abs_diagram ((basic (cement cup)) \<circ> (basic (cement cap))))" 
                 using step8 step5 by auto
                         
 then have step10: "linkrel_equiv 
        (Abs_diagram ((basic (cement cup)) \<circ>(basic ((cement cup) \<otimes> (cement vert) \<otimes> (cement vert))) \<circ> (basic
  ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) \<circ> (basic ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert))) \<circ> (basic  (cement cap))))
                                          (Abs_diagram ((basic (cement cup)) \<circ> (basic (cement cap))))"  
            using step4 rtranclp_trans linkrel_equiv_def 
    by (metis (full_types))
 then have step11: "linkrel_equiv  (Abs_diagram
     (basic ((cement cup) \<otimes> (cement cup)) \<circ>
      basic ((cement vert) \<otimes> (cement over) \<otimes> (cement vert)) \<circ> basic ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert)) \<circ> basic (cement cap)))
           (Abs_diagram ((basic (cement cup)) \<circ> (basic (cement cap))))"  
            using step2 rtranclp_trans linkrel_equiv_def by metis
 then have " linkrel_equiv  (Abs_diagram
     (basic ((cement cup) \<otimes> (cement cup)) \<circ>
      basic ((cement vert) \<otimes> (cement over) \<otimes> (cement vert)) \<circ> basic ((cement cap) \<otimes> (cement cap))))
           (Abs_diagram ((basic (cement cup)) \<circ> (basic (cement cap))))" 
                        using step1 rtranclp_trans linkrel_equiv_def by metis
 from this show ?thesis by auto
 qed
*)
end
