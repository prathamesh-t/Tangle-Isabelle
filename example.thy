theory example
imports Tangles
begin

lemma tanglerel_trans: assumes "tanglerel_equiv x y" and "tanglerel_equiv y z"
shows "tanglerel_equiv x z"
using rtranclp_trans tanglerel_equiv_def  by (metis (full_types) assms(1) assms(2))

theorem example:"tanglerel_equiv (Abs_diagram ((basic ((cement cup) ⊗ (cement cup))) ∘(basic ((cement vert) ⊗ (cement over) ⊗ (cement vert))) 
∘ (basic ((cement cap) ⊗ (cement cap)))))
 (Abs_diagram ((basic (cement cup)) ∘ (basic (cement cap))))" 
proof-
 have 1:"snd (count (cement cap)) = 0" using count.simps by auto
 have 2: "strands ((cement vert) ⊗ (cement vert))" using strands.simps  append.simps 
  by (metis makestrand.simps(1) strand_makestrand)
 let ?B = "(cement cap)"
 let ?A = "(cement vert) ⊗ (cement vert)"
 let ?x = "(Abs_diagram ((basic ((cement cup) ⊗ (cement cup))) 
   ∘(basic ((cement vert) ⊗ (cement over) ⊗ (cement vert))) 
   ∘ (basic ((cement cap) ⊗ (cement vert) ⊗ (cement vert))) ∘(basic  (cement cap))))"
 let ?y = " (Abs_diagram ((basic ((cement cup) ⊗ (cement cup))) 
               ∘(basic ((cement vert) ⊗ (cement over) ⊗ (cement vert))) ∘(basic ((cement cap) ⊗ (cement cap)))))"
 let ?y1 = "(basic ((cement cup) ⊗ (cement cup))) ∘(basic ((cement vert) ⊗ (cement over) ⊗ (cement vert))) "
 let ?z1 = "(cement cap)"
 have 3:"?x = Abs_diagram ((?y1)∘(basic (?z1⊗?A))∘(basic (?B)))" by auto
 have 4:"?y = Abs_diagram ((?y1)∘(basic (?z1⊗?B)))" by auto
 from 1 2 3 4 have "((?x = Abs_diagram
 ((?y1)∘(basic (?z1⊗?A))∘(basic (?B))))∧ ((?y = Abs_diagram (
(?y1)∘(basic (?z1⊗?B)))))
∧((snd (count ?z1)) = 0)
∧(strands ?A))" by auto
  from this have"∃z1.∃A.∃B.∃y1.((?x = Abs_diagram
 ((y1)∘(basic (z1⊗A))∘(basic (B))))∧ ((?y = Abs_diagram (
(y1)∘(basic (z1⊗B)))))
∧((snd (count z1)) = 0)
∧(strands A))" by metis
 from this have "tanglerel_compabove_topleft ?x ?y" using tanglerel_compabove_topleft_def by auto
 from this have "tanglerel_compabove ?x ?y" using tanglerel_compabove_def by auto
 from this have "tanglerel_compress ?x ?y" using tanglerel_compress_def by auto
 from this have  "tanglerel ?x ?y" using tanglerel_def by auto
 from this have "tanglerel_equiv ?x ?y" using tanglerel_equiv_def r_into_rtranclp by metis
  from this have step1: "tanglerel_equiv ?y ?x" using tangle_symmetry2 by auto

 let ?x = "(Abs_diagram ((basic (cement cup)) ∘ (basic ((cement cup) ⊗ (cement vert) ⊗ (cement vert))) 
           ∘(basic ((cement vert) ⊗ (cement over) ⊗ (cement vert))) 
           ∘ (basic ((cement cap) ⊗ (cement vert) ⊗ (cement vert))) ∘(basic  (cement cap))))"
 let ?y = "(Abs_diagram ((basic ((cement cup) ⊗ (cement cup))) 
           ∘(basic ((cement vert) ⊗ (cement over) ⊗ (cement vert))) 
           ∘ (basic ((cement cap) ⊗ (cement vert) ⊗ (cement vert))) ∘(basic  (cement cap))))"
 let ?A = "(cement cup)"
 let ?z2 = " (cement cup)"
 have 1: "fst (count ?z2) = 0" using   count.simps(1) brickcount.simps fst_conv by (metis) 
 let ?B = "(cement vert) ⊗ (cement vert)"
 let ?y2 = "(basic ((cement vert) ⊗ (cement over) ⊗ (cement vert))) 
            ∘ (basic ((cement cap) ⊗ (cement vert) ⊗ (cement vert))) ∘(basic  (cement cap))"
 have "?x =  Abs_diagram ((basic (?A))∘(basic (?z2⊗?B))∘(?y2))" by auto
 moreover have "?y = Abs_diagram ((basic (?z2 ⊗ ?A))∘(?y2))" by auto
 ultimately have "((?x = Abs_diagram ((basic (?A))∘(basic (?z2⊗?B))∘(?y2)))
                 ∧ (?y = Abs_diagram ((basic (?z2 ⊗ ?A))∘(?y2))) ∧((fst (count ?z2)) = 0)
                 ∧(strands ?B))" using 1 2 by auto
 from this have "∃z2.∃A.∃B.∃y2.((?x = Abs_diagram ((basic (A))∘(basic (z2⊗B))∘(y2)))∧ 
                  (?y = Abs_diagram ((basic (z2 ⊗ A))∘(y2))) ∧(0 = (fst (count z2))) 
                  ∧(strands B))" by metis
 from this have "tanglerel_compbelow_bottomleft ?x ?y" using tanglerel_compbelow_bottomleft_def 
                          by auto
 from this have "tanglerel_equiv ?x ?y" 
         using tanglerel_equiv_def r_into_rtranclp 
          tanglerel_def tanglerel_compress_def tanglerel_compbelow_def
            by metis
 then have step2:"tanglerel_equiv ?y ?x" using tangle_symmetry2 by auto
 let ?x1 = " (basic (cement cup))"
 let ?y1 = " ((cement cup) ⊗ (cement vert) ⊗ (cement vert))"
 let ?y2 = " ((cement vert) ⊗ (cement over) ⊗ (cement vert))"
 let ?y3 = " ((cement cap) ⊗ (cement vert) ⊗ (cement vert))"
 let ?z1 = " (basic  (cement cap))"  
 let ?w4 =  "makestrand  (nat ((snd (count ?y3)) + (-2)))" 
 let ?w5 = "makestrand (nat ((snd (count ?y3))))"
 have 10:"(snd (count ?y1)) = snd (count ((cement cup))) + snd (count ((cement vert) ⊗ (cement vert))) " using snd_conv 
          count.simps(2) brickcount.simps
           by (metis snd_count_additive)
 have 11:"snd (count ((cement cup))) = 2" using snd_conv count.simps(1)  brickcount.simps      
               by metis
 moreover have 12:"snd (count ((cement vert) ⊗ (cement vert))) = (snd (count ((cement vert)))) + (snd (count ((cement vert))))"
               by (metis snd_count_additive)
 moreover have 13:"(snd (count (cement vert))) = 1" by auto
 ultimately have 14:"(snd (count ?y1)) = 4" using 10 11 by auto
 have 15:"fst (count ((cement vert) ⊗ (cement over) ⊗ (cement vert))) 
  = ((fst (count (cement vert))) + (fst (count (cement over)))+ (fst (count (cement vert))))"
 using count.simps(2) by (metis comm_semiring_1_class.normalizing_semiring_rules(24) fst_count_additive)
 have 16:"snd (count ((cement vert) ⊗ (cement over) ⊗ (cement vert))) 
  = ((snd (count (cement vert))) + (snd (count (cement over)))+ (snd (count (cement vert))))"
 using count.simps(2) by (metis comm_semiring_1_class.normalizing_semiring_rules(24) snd_count_additive)
 have 17:"(count (cement vert)) = (1,1)" using count.simps(1)   by auto
 have 18:"(count (cement over)) = (2,2)" using count.simps(1)   by auto
 from 15 16 17 18 have 19:"fst (count ((cement vert) ⊗ (cement over) ⊗ (cement vert))) 
       = 4" using fst_count_additive fst_conv  by (metis add_One 
 add_One_commute inc.simps(1) inc.simps(2) inc.simps(3) numeral_inc one_plus_numeral)
 from 15 16 17 18 have 20:"snd (count ((cement vert) ⊗ (cement over) ⊗ (cement vert))) 
       = 4" using snd_count_additive snd_conv  by (metis add_One 
 add_One_commute inc.simps(1) inc.simps(2) inc.simps(3) numeral_inc one_plus_numeral)
 have 21:"fst (count ?y2)  = (snd (count ?y1))" using 14 19 by auto
 have 22:"fst (count (cement cap)) = 2" using count.simps(1) brickcount.simps(3) fst_conv  by (metis ) 
 have "fst (count ((cement cap) ⊗ (cement vert) ⊗ (cement vert))) 
  = ((fst (count (cement cap))) + (fst (count (cement vert)))+ (fst (count (cement vert))))"  using count.simps(2) 
   using count.simps(2) fst_count_additive by auto
 from this 21 17 have " fst (count ((cement cap) ⊗ (cement vert) ⊗ (cement vert)))  = 4" using fst_count_additive fst_conv
           by (metis "22" inc.simps(1) inc.simps(2) inc.simps(3) numeral_inc)
 then have 23:" fst (count ?y3) = (snd (count ?y2))" using 20 by auto
 have 24:"snd (count (cement cap)) = 0" using count.simps(1) brickcount.simps(3) snd_conv  by (metis) 
 have 25:"snd (count ((cement cap) ⊗ (cement vert) ⊗ (cement vert))) 
  = ((snd (count (cement cap))) + (snd (count (cement vert)))+ (snd (count (cement vert))))"
     using count.simps(2) 
   using count.simps(2) snd_count_additive by auto
 from this have 26:"snd (count ?y3) = 2"  using snd_count_additive snd_conv
       by (metis "13" "24" one_add_one plus_int_code(2))
 from this have 27:"snd (count ?y3) > 1" by auto
 have "tanglerel_equiv (Abs_diagram ((?x1) ∘(basic ((cement cup) ⊗ ?y1 ⊗ (cement cup)))
         ∘ (basic ((cement vert) ⊗ (cement vert) ⊗ ?y2 ⊗ (cement vert) ⊗ (cement vert))) 
         ∘ (basic ((cement vert) ⊗(cement vert) ⊗ ?y3 ⊗ (cement vert) ⊗ (cement vert)))
         ∘ (basic ((cement vert) ⊗ (cement cap) ⊗ ?w5)) ∘ (basic (?w4 ⊗(cement cap) ⊗ (cement vert))) ∘ ?z1))
             (Abs_diagram (?x1 ∘ (basic ?y1) ∘(basic ?y2) ∘ (basic ?y3) ∘ ?z1))"
         using 27 23 21 metaequivalence_thriple_drop by metis
 then have step4: "tanglerel_equiv  (Abs_diagram (?x1 ∘ (basic ?y1) ∘(basic ?y2) ∘ (basic ?y3) ∘ ?z1))
          (Abs_diagram ((?x1) ∘(basic ((cement cup) ⊗ ?y1 ⊗ (cement cup)))
         ∘ (basic ((cement vert) ⊗ (cement vert) ⊗ ?y2 ⊗ (cement vert) ⊗ (cement vert))) 
         ∘ (basic ((cement vert) ⊗(cement vert) ⊗ ?y3 ⊗ (cement vert) ⊗ (cement vert)))
         ∘ (basic ((cement vert) ⊗ (cement cap) ⊗ ?w5)) ∘ (basic (?w4 ⊗(cement cap) ⊗ (cement vert))) ∘ ?z1))
            " using tangle_symmetry2 by metis

 let ?t1 = " (Abs_diagram ((?x1) ∘(basic ((cement cup) ⊗ ?y1 ⊗ (cement cup)))
         ∘ (basic ((cement vert) ⊗ (cement vert) ⊗ ?y2 ⊗ (cement vert) ⊗ (cement vert))) 
         ∘ (basic ((cement vert) ⊗(cement vert) ⊗ ?y3 ⊗ (cement vert) ⊗ (cement vert)))
         ∘ (basic ((cement vert) ⊗ (cement cap) ⊗ ?w5)) ∘ (basic (?w4 ⊗(cement cap) ⊗ (cement vert))) ∘ ?z1))"
 let ?y1 = "?x1"
 let ?z1 = "(cement cup)"
 let ?w1 = "(cement vert) ⊗ (cement cup)"
 let ?z2 = "(cement vert) ⊗ (cement vert)"
 let ?w2 = "(cement vert) ⊗ (cement vert) ⊗ (cement vert)"
 let ?z3 = "(cement vert) ⊗ (cement vert) "
 let ?w3 = "(cement vert) ⊗ (cement vert) ⊗ (cement vert)"
 let ?y2 = " (basic ((cement vert) ⊗ (cement cap) ⊗ ?w5)) ∘ (basic (?w4 ⊗(cement cap) ⊗ (cement vert))) ∘ (basic (cement cap))"
  let ?t2 = "Abs_diagram ((?y1)
       ∘(basic (?z1⊗(cement vert)⊗?w1))∘(basic (?z2⊗(cement vert)⊗?w2))∘(basic (?z3⊗(cement vert)⊗?w3))∘(?y2))"

 have 29:"?t1 =  Abs_diagram ((?y1)
 ∘(basic (?z1⊗(cement cup)⊗(cement vert)⊗?w1)∘(basic (?z2⊗(cement vert)⊗(cement over)⊗?w2))∘(basic (?z3⊗(cement cap)⊗(cement vert)⊗?w3))
  ∘(?y2)))" by (metis leftright_associativity)
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
   have "snd (count ?w1) = 3" using snd_conv count.simps brickcount.simps 
    Tangles.append.append_Nil  trivial by metis
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
   have "(∃y1.∃z1.∃z2.∃z3.∃w1.∃w2.∃w3.∃y2.(?t1 = Abs_diagram ((y1)
∘(basic (z1⊗(cement cup)⊗(cement vert)⊗w1)∘(basic (z2⊗(cement vert)⊗(cement over)⊗w2))
∘(basic (z3⊗(cement cap)⊗(cement vert)⊗w3))∘(y2)))))"
       by (metis leftright_associativity)
   moreover have "(∃y1.∃z1.∃z2.∃z3.∃w1.∃w2.∃w3.∃y2.(?t2 = Abs_diagram ((y1)∘(basic (z1⊗(cement vert)⊗w1))∘(basic (z2⊗(cement vert)⊗w2))∘(basic (z3⊗(cement vert)⊗w3))
  ∘(y2)))∧((snd (count z1)) = 
(fst (count z2)))∧((snd (count z2)) = (fst (count z3))) ∧ ((snd (count w1)) = (fst
(count w2)))∧((snd (count w2)) = (fst (count w3))))"  
by (metis (hide_lams, no_types) "11" "22" "26" "30" "31" "32" fst_count_additive leftright_associativity 
snd_count_additive)
   ultimately have  "(∃y1.∃z1.∃z2.∃z3.∃w1.∃w2.∃w3.∃y2.(?t1 = Abs_diagram ((y1)
∘(basic (z1⊗(cement cup)⊗(cement vert)⊗w1)∘(basic (z2⊗(cement vert)⊗(cement over)⊗w2))∘(basic (z3⊗(cement cap)⊗(cement vert)⊗w3))∘(y2))))
 ∧(?t2 = Abs_diagram
 ((y1)∘(basic (z1⊗(cement vert)⊗w1))∘(basic (z2⊗(cement vert)⊗w2))∘(basic (z3⊗(cement vert)⊗w3))∘(y2)))∧((snd (count z1)) = 
(fst (count z2)))∧((snd (count z2)) = (fst (count z3))) ∧ ((snd (count w1)) = (fst
(count w2)))∧((snd (count w2)) = (fst (count w3))))" using 30 31 32 33  
   by (metis leftright_associativity snd_count_additive)
   from this have "tanglerel_uncross_positivestraighten ?t1 ?t2" 
     using  tanglerel_uncross_positivestraighten_def by auto   
   from this have "tanglerel ?t1 ?t2" using tanglerel_def tanglerel_uncross_def by auto
   from this have step5: "tanglerel_equiv ?t1 ?t2" using tanglerel_equiv_def by (metis r_into_rtranclp)
   let ?x1 = ?x1
   let ?z1 = "basic (cement cap)"
   let ?y1 = "(cement vert) ⊗ (cement vert)"
   let ?y2 = "(cement vert) ⊗ (cement vert)"
   let ?y3 = "(cement vert) ⊗ (cement vert)"
   
   have 34:"?t2 =  (Abs_diagram ((?x1) ∘(basic ((cement cup) ⊗ ?y1 ⊗ (cement cup)))
         ∘ (basic ((cement vert) ⊗ (cement vert) ⊗ ?y2 ⊗ (cement vert) ⊗ (cement vert))) 
         ∘ (basic ((cement vert) ⊗(cement vert) ⊗ ?y3 ⊗ (cement vert) ⊗ (cement vert)))
         ∘ (basic ((cement vert) ⊗ (cement cap) ⊗ ?w5)) ∘ (basic (?w4 ⊗(cement cap) ⊗ (cement vert))) ∘ ?z1))" 
    by (metis leftright_associativity)
  have 35:"snd (count ((cement vert) ⊗ (cement vert))) = (fst (count ((cement vert) ⊗ (cement vert))))" using 31 by auto
  have 36:"snd (count ?y3) >1 " using "12" "13" less_add_one by auto
  have 37: "snd (count ((cement cap) ⊗ (cement vert) ⊗ (cement vert))) = snd (count ?y3)" by (metis "12" "24" "25" comm_monoid_add_class.add.left_neutral)
  then have "nat (snd (count ((cement cap) ⊗ (cement vert) ⊗ (cement vert)))+-2)  =  (nat (snd (count ?y3)+-2))"
                        by auto
  from this have 38:"?w4 = makestrand  (nat (snd (count (?y3))+-2))" by auto
  from 37 have 39:"?w5 = makestrand (nat (snd (count ?y3)))" by auto
  from 34 35 36 38 39 have step6:"tanglerel_equiv ?t2  
         (Abs_diagram (?x1 ∘ (basic ?y1) ∘(basic ?y2) ∘ (basic ?y3) ∘ ?z1))" 
          using metaequivalence_thriple_drop by metis
   let ?t3 = "(Abs_diagram (?x1 ∘ (basic ?y1) ∘(basic ?y2) ∘ (basic ?y3) ∘ ?z1))"
   have 40:"strands ?y1" using strands_def   "2" by (metis)
   have 41:"snd (wall_count ?x1) = 2" using wall_count_def  "11" wall_count.simps(1)  by auto
   then have 42:" snd (wall_count ?x1) > 0" by auto
   then have "tanglerel_compress_null ?t3 (Abs_diagram (?x1 ∘(basic ?y2) ∘ (basic ?y3) ∘ ?z1))"
              using tanglerel_compress_null_def 40 42 by metis
   then have 43:"tanglerel_equiv ?t3 (Abs_diagram (?x1 ∘(basic ?y2) ∘ (basic ?y3) ∘ ?z1))"
                        using tanglerel_compress_def tanglerel_def tanglerel_equiv_def r_into_rtranclp
                          by (metis (full_types))
   moreover have "tanglerel_compress_null  (Abs_diagram (?x1 ∘(basic ?y2) ∘ (basic ?y3) ∘ ?z1))
                              (Abs_diagram (?x1  ∘ (basic ?y3) ∘ ?z1))"
                  using tanglerel_compress_null_def 40 42 by metis
    then have 44:"tanglerel_equiv (Abs_diagram (?x1 ∘(basic ?y2) ∘ (basic ?y3) ∘ ?z1))
                                 (Abs_diagram (?x1  ∘ (basic ?y3) ∘ ?z1))"
                        using tanglerel_compress_def tanglerel_def tanglerel_equiv_def r_into_rtranclp
                          by (metis (full_types))
   moreover have "tanglerel_compress_null  (Abs_diagram (?x1 ∘ (basic ?y3) ∘ ?z1))
                              (Abs_diagram ((basic (cement cup))  ∘ (basic (cement cap))))"
                  using tanglerel_compress_null_def 40 42 by metis
   then have 45:"tanglerel_equiv (Abs_diagram (?x1 ∘ (basic ?y3) ∘ ?z1))
                                 (Abs_diagram ((basic (cement cup)) ∘ (basic (cement cap))))"
                        using tanglerel_compress_def tanglerel_def tanglerel_equiv_def r_into_rtranclp
                          by (metis (full_types))
    then have 46:"tanglerel_equiv (Abs_diagram (?x1 ∘(basic ?y2) ∘ (basic ?y3) ∘ ?z1))
                                   (Abs_diagram ((basic (cement cup)) ∘ (basic (cement cap))))"
                   using 44 45 tanglerel_equiv_def by (metis rtranclp_trans)
    then have step7: "tanglerel_equiv  ?t3
                                   (Abs_diagram ((basic (cement cup)) ∘ (basic (cement cap))))" 
                       using 43 rtranclp_trans tanglerel_equiv_def by metis
   then have step8: "tanglerel_equiv  ?t2
                                   (Abs_diagram ((basic (cement cup)) ∘ (basic (cement cap))))" 
                 using step6 rtranclp_trans tanglerel_equiv_def by (metis (full_types))
(*check this*)
   have "((tanglerel_equiv ?t1 ?t2) ∧ (tanglerel_equiv  ?t2
                                   (Abs_diagram ((basic (cement cup)) ∘ (basic (cement cap))))))
  ⟹ (tanglerel_equiv  ?t1 (Abs_diagram ((basic (cement cup)) ∘ (basic (cement cap)))))"
  using tanglerel_trans by auto  
  then have step9: "tanglerel_equiv  ?t1
                                   (Abs_diagram ((basic (cement cup)) ∘ (basic (cement cap))))" 
                 using step8 step5 by auto
                         
  then have step10: "tanglerel_equiv 
        (Abs_diagram ((basic (cement cup)) ∘(basic ((cement cup) ⊗ (cement vert) ⊗ (cement vert))) ∘ (basic
  ((cement vert) ⊗ (cement over) ⊗ (cement vert))) ∘ (basic ((cement cap) ⊗ (cement vert) ⊗ (cement vert))) ∘ (basic  (cement cap))))
                                          (Abs_diagram ((basic (cement cup)) ∘ (basic (cement cap))))"  
            using step4 rtranclp_trans tanglerel_equiv_def 
    by (metis (full_types))
   then have step11: "tanglerel_equiv  (Abs_diagram
     (basic ((cement cup) ⊗ (cement cup)) ∘
      basic ((cement vert) ⊗ (cement over) ⊗ (cement vert)) ∘ basic ((cement cap) ⊗ (cement vert) ⊗ (cement vert)) ∘ basic (cement cap)))
           (Abs_diagram ((basic (cement cup)) ∘ (basic (cement cap))))"  
            using step2 rtranclp_trans tanglerel_equiv_def by metis
   then have " tanglerel_equiv  (Abs_diagram
     (basic ((cement cup) ⊗ (cement cup)) ∘
      basic ((cement vert) ⊗ (cement over) ⊗ (cement vert)) ∘ basic ((cement cap) ⊗ (cement cap))))
           (Abs_diagram ((basic (cement cup)) ∘ (basic (cement cap))))" 
                        using step1 rtranclp_trans tanglerel_equiv_def by metis
   from this show ?thesis by auto
  qed
end
