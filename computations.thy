theory computations
imports Kauffman_Matrix
begin


lemma unlink_computation:
 "rat_poly_plus (rat_poly_times (rat_poly_times A A) (rat_poly_times A A))
     (rat_poly_plus
       (rat_poly_times 2 (rat_poly_times A (rat_poly_times A (rat_poly_times B B))))
       (rat_poly_times (rat_poly_times B B) (rat_poly_times B B))) =
             ((A^4)+(B^4)+2)"
  proof-
  have "(rat_poly_times (rat_poly_times A A) (rat_poly_times A A)) = A^4"
             by (metis comm_semiring_1_class.normalizing_semiring_rules(18) comm_semiring_1_class.normalizing_semiring_rules(31) numeral_times_numeral power2_eq_square semiring_norm(12) semiring_norm(13))
  moreover have "(rat_poly_times (rat_poly_times B B) (rat_poly_times B B))
             = B^4"
             by (metis comm_semiring_1_class.normalizing_semiring_rules(18) comm_semiring_1_class.normalizing_semiring_rules(31) numeral_times_numeral power2_eq_square semiring_norm(12) semiring_norm(13))
  moreover have "(rat_poly_times 2 (rat_poly_times A (rat_poly_times A (rat_poly_times B B))))
               = 2"
       using inverse1  by (metis mult_2_right one_add_one rat_poly.assoc rat_poly.comm)
   ultimately show ?thesis by auto
qed

lemma computation_swingpos:
" rat_poly_plus (rat_poly_times B (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) B))
     (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
       (rat_poly_times A (A - rat_poly_times (rat_poly_times B B) B))) =
    rat_poly_times A (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) A)" (is "?l = ?r")
   proof-
     have 1:"(A - rat_poly_times (rat_poly_times B B) B)
               = A - (B^3)"
             by (metis power3_eq_cube)
     then have 2:"(rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) B)
                 = A*B - (B^3)*B"
              by (metis minus_right_distributivity)
    then have "... = 1 - (B^4)"
              using inverse1 by (metis (hide_lams, no_types) Suc_numeral comm_semiring_1_class.normalizing_semiring_rules(12) comm_semiring_1_class.normalizing_semiring_rules(18) comm_semiring_1_class.normalizing_semiring_rules(30) comm_semiring_1_class.normalizing_semiring_rules(31) comm_semiring_1_class.normalizing_semiring_rules(7) mult_Suc_right numeral_One numeral_plus_numeral power2_eq_square power3_eq_cube semiring_norm(2) semiring_norm(6))
    then have "(rat_poly_times B (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) B))
                      = B - (B^4)*B"
             using 2  by (metis comm_semiring_1_class.normalizing_semiring_rules(12) comm_semiring_1_class.normalizing_semiring_rules(7) minus_left_distributivity)
   then have 3:"(rat_poly_times B (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) B))
                  = B - (B^5)"
                 by (metis Suc_numeral add_One_commute comm_semiring_1_class.normalizing_semiring_rules(28) semiring_norm(3))
    have "(rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
       (rat_poly_times A (A - rat_poly_times (rat_poly_times B B) B)))
                 =  (A - (B^3))*(A*( A - (B^3)))"
             using 1 by auto
    moreover then have "... =  (A - (B^3))*(A*A - (A*(B^3)))"
                    by (metis minus_left_distributivity) 
    moreover then have "... = (A - (B^3))*(A*A - (B^2))"
                   using inverse1 by (metis (hide_lams, no_types) comm_semiring_1_class.normalizing_semiring_rules(12) comm_semiring_1_class.normalizing_semiring_rules(19) power2_eq_square power3_eq_cube)
    moreover then have "... = A*(A*A - (B^2)) - (B^3)*(A*A - (B^2))"
                  by (metis minus_right_distributivity)
    moreover then have "... = ((A^3) - B) - B + (B^5)"
         proof-
         have "A*(A*A - (B^2)) = (A*A*A - A*(B^2))"
                   by (metis (hide_lams, no_types) comm_semiring_1_class.normalizing_semiring_rules(18) comm_semiring_1_class.normalizing_semiring_rules(34) diff_0_right diff_minus_eq_add minus_diff_eq minus_mult_right)
         moreover have "... = (A*A*A - A*(B*B))"
                   by (metis power2_eq_square)
         moreover have "...  = ((A^3) - ((A::rat_poly)*B)*B)"
                   by (metis comm_semiring_1_class.normalizing_semiring_rules(17) power3_eq_cube) 
         moreover have "... = ((A^3) - ((1::rat_poly)*B))"
                  by (metis inverse1)
         moreover have "... = (A^3) - B"
                  by (metis comm_semiring_1_class.normalizing_semiring_rules(11))   
         ultimately have s1:"(A::rat_poly)*(A*A - (B^2)) = (A^3) - (B::rat_poly)"
                 by metis
         have "((B::rat_poly)^3)*(A*A - (B^2)) = (B^3)*(A*A) - (B^(3::nat))*(B^2)"
                    by (metis minus_left_distributivity power3_eq_cube)  
         moreover then have "... = (((B::rat_poly)^3)*(A*A) - (B^5))"
                    using power_add by (metis (hide_lams, no_types) comm_semiring_1_class.normalizing_semiring_rules(7) numeral_plus_numeral semiring_norm(2) semiring_norm(7)) 
         moreover then have "... =  ((((B::rat_poly)*B*B)*(A*A)) - (B^5))"
                     by (metis power3_eq_cube)   
         moreover then have "... = ((((B::rat_poly)*(B*(B*A)*A))) - (B^5))"                     
                     by auto
         moreover then have "... = ((((B::rat_poly)*(B*(1)*A))) - (B^5))"  
                     using inverse2 by auto
         moreover then have "... =  ((((B::rat_poly)*(B*A))) - (B^5))"  
                     by auto
         moreover then have "... = ((((B::rat_poly))) - (B^5))"  
                      using inverse2 by (metis comm_semiring_1_class.normalizing_semiring_rules(12))  
         ultimately have "((B::rat_poly)^3)*(A*A - (B^2)) = ((B::rat_poly) - (B^5))"  
                      by auto
         then have "A*(A*A - (B^2)) - (B^3)*(A*A - (B^2))
                       = (A^3) - (B::rat_poly) - ((B::rat_poly) - (B^5))"  
                    using s1 by auto
         then show ?thesis by auto
         qed          
 ultimately have "(rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
       (rat_poly_times A (A - rat_poly_times (rat_poly_times B B) B)))
             = ((A^3) - B) - B + (B^5)"
          by auto
 then have "?l =  B - (B^5) +  ((A^3) - B) - B + (B^5)"
               using 3 by auto
 then have 4:"?l = (A^3) - B"
              by auto
  have "?r =  A*((A - rat_poly_times (rat_poly_times B B) B)*A)"
             by auto
  moreover then have "... = A*(A - (B^3))*A"
              using 1 by auto
  moreover have "... = A*(A*A - (B^3)*A)"
              by (metis comm_semiring_1_class.normalizing_semiring_rules(7) minus_left_distributivity) 
 moreover have "... = A*(A*A - (B*B*B)*A)"
              by (metis power3_eq_cube)
  moreover have "... = A*(A*A - (B*B*(B*A)))"
               by auto
  moreover have "... = A*(A*A - B*B)"
              by (metis comm_monoid_mult_class.mult.right_neutral inverse2)
  moreover have "... = A*A*A - A*(B*B)"
              by (metis minus_left_distributivity rat_poly.comm)
  moreover have "... = A^3 - (A*B)*B"
              by (metis ab_semigroup_mult_class.mult_ac(1) power3_eq_cube)
  moreover have "... = A^3 - B"
             using inverse1 by (metis monoid_mult_class.mult.left_neutral)
  ultimately have "?r =  A^3 - B"
               by auto
  then show ?thesis using 4 by auto
qed

lemma computation2:
" rat_poly_plus (rat_poly_times A (rat_poly_times (B - rat_poly_times (rat_poly_times A A) A) A))
     (rat_poly_times (B - rat_poly_times (rat_poly_times A A) A)
       (rat_poly_times B (B - rat_poly_times (rat_poly_times A A) A))) =
    rat_poly_times B (rat_poly_times (B - rat_poly_times (rat_poly_times A A) A) B)" (is "?l = ?r")
   proof-
     have 1:"(B - rat_poly_times (rat_poly_times A A) A)
               = B - (A^3)"
             by (metis power3_eq_cube)
     then have 2:"(rat_poly_times (B - rat_poly_times (rat_poly_times A A) A) A)
                 = B*A - (A^3)*A"
              by (metis minus_right_distributivity)
    then have "... = 1 - (A^4)"
              using inverse2 by (metis (hide_lams, no_types) Suc_numeral comm_semiring_1_class.normalizing_semiring_rules(12) comm_semiring_1_class.normalizing_semiring_rules(18) comm_semiring_1_class.normalizing_semiring_rules(30) comm_semiring_1_class.normalizing_semiring_rules(31) comm_semiring_1_class.normalizing_semiring_rules(7) mult_Suc_right numeral_One numeral_plus_numeral power2_eq_square power3_eq_cube semiring_norm(2) semiring_norm(6))
    then have "(rat_poly_times A (rat_poly_times (B - rat_poly_times (rat_poly_times A A) A) A))
                      = A - (A^4)*A"
             using 2  by (metis comm_semiring_1_class.normalizing_semiring_rules(12) comm_semiring_1_class.normalizing_semiring_rules(7) minus_left_distributivity)
   then have 3:"(rat_poly_times A (rat_poly_times (B - rat_poly_times (rat_poly_times A A) A) A))
                  = A - (A^5)"
                 by (metis Suc_numeral add_One_commute comm_semiring_1_class.normalizing_semiring_rules(28) semiring_norm(3))
    have "(rat_poly_times (B - rat_poly_times (rat_poly_times A A) A)
       (rat_poly_times B (B - rat_poly_times (rat_poly_times A A) A)))
                 =  (B - (A^3))*(B*( B - (A^3)))"
             using 1 by auto
    moreover then have "... =  (B - (A^3))*(B*B - (B*(A^3)))"
                    by (metis minus_left_distributivity) 
    moreover then have "... = (B - (A^3))*(B*B - (A^2))"
                   using inverse2 by (metis (hide_lams, no_types) comm_semiring_1_class.normalizing_semiring_rules(12) comm_semiring_1_class.normalizing_semiring_rules(19) power2_eq_square power3_eq_cube)
    moreover then have "... = B*(B*B - (A^2)) - (A^3)*(B*B - (A^2))"
                  by (metis minus_right_distributivity)
    moreover then have "... = ((B^3) - A) - A + (A^5)"
         proof-
         have "B*(B*B - (A^2)) = (B*B*B - B*(A^2))"
                   by (metis (hide_lams, no_types) comm_semiring_1_class.normalizing_semiring_rules(18) comm_semiring_1_class.normalizing_semiring_rules(34) diff_0_right diff_minus_eq_add minus_diff_eq minus_mult_right)
         moreover have "... = (B*B*B - B*(A*A))"
                   by (metis power2_eq_square)
         moreover have "...  = ((B^3) - ((B::rat_poly)*A)*A)"
                   by (metis comm_semiring_1_class.normalizing_semiring_rules(17) power3_eq_cube) 
         moreover have "... = ((B^3) - ((1::rat_poly)*A))"
                  by (metis inverse2)
         moreover have "... = (B^3) - A"
                  by (metis comm_semiring_1_class.normalizing_semiring_rules(11))   
         ultimately have s1:"(B::rat_poly)*(B*B - (A^2)) = (B^3) - (A::rat_poly)"
                 by metis
         have "((A::rat_poly)^3)*(B*B - (A^2)) = (A^3)*(B*B) - (A^(3::nat))*(A^2)"
                    by (metis minus_left_distributivity power3_eq_cube)  
         moreover then have "... = (((A::rat_poly)^3)*(B*B) - (A^5))"
                    using power_add by (metis (hide_lams, no_types) comm_semiring_1_class.normalizing_semiring_rules(7) numeral_plus_numeral semiring_norm(2) semiring_norm(7)) 
         moreover then have "... =  ((((A::rat_poly)*A*A)*(B*B)) - (A^5))"
                     by (metis power3_eq_cube)   
         moreover then have "... = ((((A::rat_poly)*(A*(A*B)*B))) - (A^5))"                     
                     by auto
         moreover then have "... = ((((A::rat_poly)*(A*(1)*B))) - (A^5))"  
                     using inverse1 by auto
         moreover then have "... =  ((((A::rat_poly)*(A*B))) - (A^5))"  
                     by auto
         moreover then have "... = ((((A::rat_poly))) - (A^5))"  
                      using inverse1 by (metis comm_semiring_1_class.normalizing_semiring_rules(12))  
         ultimately have "((A::rat_poly)^3)*(B*B - (A^2)) = ((A::rat_poly) - (A^5))"  
                      by auto
         then have "B*(B*B - (A^2)) - (A^3)*(B*B - (A^2))
                       = (B^3) - (A::rat_poly) - ((A::rat_poly) - (A^5))"  
                    using s1 by auto
         then show ?thesis by auto
         qed          
 ultimately have "(rat_poly_times (B - rat_poly_times (rat_poly_times A A) A)
       (rat_poly_times B (B - rat_poly_times (rat_poly_times A A) A)))
             = ((B^3) - A) - A + (A^5)"
          by auto
 then have "?l =  A - (A^5) +  ((B^3) - A) - A + (A^5)"
               using 3 by auto
 then have 4:"?l = (B^3) - A"
              by auto
  have "?r =  B*((B - rat_poly_times (rat_poly_times A A) A)*B)"
             by auto
  moreover then have "... = B*(B - (A^3))*B"
              using 1 by auto
  moreover have "... = B*(B*B - (A^3)*B)"
              by (metis comm_semiring_1_class.normalizing_semiring_rules(7) minus_left_distributivity) 
 moreover have "... = B*(B*B - (A*A*A)*B)"
              by (metis power3_eq_cube)
  moreover have "... = B*(B*B - (A*A*(A*B)))"
               by auto
  moreover have "... = B*(B*B - A*A)"
              by (metis comm_monoid_mult_class.mult.right_neutral inverse1)
  moreover have "... = B*B*B - B*(A*A)"
              by (metis minus_left_distributivity rat_poly.comm)
  moreover have "... = B^3 - (B*A)*A"
              by (metis ab_semigroup_mult_class.mult_ac(1) power3_eq_cube)
  moreover have "... = B^3 - A"
             using inverse2 by (metis monoid_mult_class.mult.left_neutral)
  ultimately have "?r =  B^3 - A"
               by auto
  then show ?thesis using 4 by auto
qed

lemma computation_swingneg:"rat_poly_times B (rat_poly_times (B - rat_poly_times (rat_poly_times A A) A) B) =
    rat_poly_plus
     (rat_poly_times (B - rat_poly_times (rat_poly_times A A) A)
       (rat_poly_times B (B - rat_poly_times (rat_poly_times A A) A)))
     (rat_poly_times A (rat_poly_times (B - rat_poly_times (rat_poly_times A A) A) A))"
        using computation2 by auto     
lemma computation_toppos:"rat_poly_inv (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) A) =
    rat_poly_times (B - rat_poly_times (rat_poly_times A A) A) B"(is "?l = ?r")
   proof-
   have "(rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) A)
                = ((A - ((B*B)*B))*A)"
                   by auto
   moreover then have "... = (A*A) - ((B*B)*B)*A"
                  by (metis minus_left_distributivity rat_poly.comm)  
   moreover then have "... = (A*A) - (B*B)*(B*A)"
                  by auto
   moreover then have "... = (A*A) - (B*B)"
                  by (metis comm_semiring_1_class.normalizing_semiring_rules(12) inverse2)             
  ultimately have "?l = rat_poly_inv ((A*A) - (B*B))"
                  by auto
  then have 1:"?l = (B*B) - (A*A)"
                by auto
  have "?r =(B - ((A*A) *A))*B"
           by auto 
  moreover have "... = B*B - ((A*A)*A)*B"
           by (metis minus_left_distributivity rat_poly.comm)  
  moreover have "... = (B*B) - ((A*A)*(A*B))"
          by auto
  moreover have "... = ((B::rat_poly)*B) - (A*A)"
       using inverse1   by (metis (hide_lams, no_types) comm_monoid_mult_class.mult.right_neutral)         
  ultimately have "?r = (B*B) - (A*A)"
          by auto
  then show ?thesis using 1 by auto
qed
                
(*rat_poly_times A (A - rat_poly_times (rat_poly_times B B) B) =
    rat_poly_inv (rat_poly_times B (B - rat_poly_times (rat_poly_times A A) A))*)

lemma computation_downpos_prelim:
"rat_poly_inv (rat_poly_times (B - rat_poly_times (rat_poly_times A A) A) B) =
    rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) A"(is "?l = ?r")
   proof-
   have "(rat_poly_times (B - rat_poly_times (rat_poly_times A A) A) B)
                = ((B - ((A*A)*A))*B)"
                   by auto
   moreover then have "... = (B*B) - ((A*A)*A)*B"
                  by (metis minus_left_distributivity rat_poly.comm)  
   moreover then have "... = (B*B) - (A*A)*(A*B)"
                  by auto
   moreover then have "... = (B*B) - (A*A)"
                  by (metis comm_semiring_1_class.normalizing_semiring_rules(12) inverse1)             
  ultimately have "?l = rat_poly_inv ((B*B) - (A*A))"
                  by auto
  then have 1:"?l = (A*A) - (B*B)"
                by auto
  have "?r =(A - ((B*B) *B))*A"
           by auto 
  moreover have "... = A*A - ((B*B)*B)*A"
           by (metis minus_left_distributivity rat_poly.comm)  
  moreover have "... = (A*A) - ((B*B)*(B*A))"
          by auto
  moreover have "... = ((A::rat_poly)*A) - (B*B)"
       using inverse2   by (metis (hide_lams, no_types) comm_monoid_mult_class.mult.right_neutral)         
  ultimately have "?r = (A*A) - (B*B)"
          by auto
  then show ?thesis using 1 by auto
qed

lemma computation_downpos:"rat_poly_times A (A - rat_poly_times (rat_poly_times B B) B) =
    rat_poly_inv (rat_poly_times B (B - rat_poly_times (rat_poly_times A A) A))"
       using computation_downpos_prelim by (metis rat_poly.comm)


lemma computatition_positive_flip:"rat_poly_plus
     (rat_poly_inv (rat_poly_times A (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) A)))
     (rat_poly_inv (rat_poly_times B (rat_poly_times A B))) =
    rat_poly_inv (rat_poly_times A (rat_poly_times A A))" (is "?l = ?r")
 proof- 
 have "(rat_poly_inv (rat_poly_times B (rat_poly_times A B)))
                 = (rat_poly_inv (rat_poly_times B 1))"
          using inverse1 by auto
 moreover have "... = - B"
        by auto
 ultimately have 1:"(rat_poly_inv (rat_poly_times B (rat_poly_times A B))) = - B"
       by auto
 have " (rat_poly_times A (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) A))
         = A*((A - ((B*B)*B))*A)"
          by auto
 moreover then have "... = A*((A*A) - ((B*B)*B*A))"
          by (metis minus_left_distributivity rat_poly.comm)
 moreover then have "... = A*((A*A) - ((B*B)*1))"
         using inverse2 by auto
 moreover then have "... = A*((A*A) - (B*B))"
          by auto
 moreover then have "... = A*(A*A) - (A*(B*B))"
         by (metis minus_left_distributivity)
 moreover then have "... = (A*(A*A)) - (1*B)"
         using inverse1 by auto
 moreover then have "... =  (A*(A*A)) - B"
         by auto
 ultimately have "(rat_poly_times A (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) A))
                     = (A*(A*A)) - B"
            by auto
 then have "rat_poly_inv (rat_poly_times A (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) A))
                  = B - (A*A*A)"
           by auto
 then have 3:"?l = - (A*A*A)"
           using 1 by auto
 moreover have "?r = - (A*A*A)"
            by auto
 ultimately show ?thesis by auto
qed


lemma computation_negative_flip:"rat_poly_plus
     (rat_poly_inv (rat_poly_times B (rat_poly_times (B - rat_poly_times (rat_poly_times A A) A) B)))
     (rat_poly_inv (rat_poly_times A (rat_poly_times B A))) =
    rat_poly_inv (rat_poly_times B (rat_poly_times B B))" (is "?l = ?r")
 proof- 
 have "(rat_poly_inv (rat_poly_times A (rat_poly_times B A)))
                 = (rat_poly_inv (rat_poly_times A 1))"
          using inverse2 by auto
 moreover have "... = - A"
        by auto
 ultimately have 1:"(rat_poly_inv (rat_poly_times A (rat_poly_times B A))) = - A"
       by auto
 have " (rat_poly_times B (rat_poly_times (B - rat_poly_times (rat_poly_times A A) A) B))
         = B*((B - ((A*A)*A))*B)"
          by auto
 moreover then have "... = B*((B*B) - ((A*A)*A*B))"
          by (metis minus_left_distributivity rat_poly.comm)
 moreover then have "... = B*((B*B) - ((A*A)*1))"
         using inverse1 by auto
 moreover then have "... = B*((B*B) - (A*A))"
          by auto
 moreover then have "... = B*(B*B) - (B*(A*A))"
         by (metis minus_left_distributivity)
 moreover then have "... = (B*(B*B)) - (1*A)"
         using inverse2 by auto
 moreover then have "... =  (B*(B*B)) - A"
         by auto
 ultimately have "(rat_poly_times B (rat_poly_times (B - rat_poly_times (rat_poly_times A A) A) B))
                     = (B*(B*B)) - A"
            by auto
 then have "rat_poly_inv (rat_poly_times B (rat_poly_times (B - rat_poly_times (rat_poly_times A A) A) B))
                  = A - (B*B*B)"
           by auto
 then have 3:"?l = - (B*B*B)"
           using 1 by auto
 moreover have "?r = - (B*B*B)"
            by auto
 ultimately show ?thesis by auto
qed


lemma computation_pull_pos_neg:
"rat_poly_plus (rat_poly_times B (B - rat_poly_times (rat_poly_times A A) A))
     (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) A) = 0"
      proof-
      have " rat_poly_times (rat_poly_times A A) A
                       = ((A*A)*A)"
                  by auto
     then have "rat_poly_times B (B - rat_poly_times (rat_poly_times A A) A)
                     = B*B - B*((A*A)*A)"
             using minus_left_distributivity by auto    
      moreover have "... = B*B - (B*(A*(A*A)))"
                      by auto
      moreover have "... = B*B - ((B*A)*(A*A))"
                      by auto
      moreover have "... = B*B - A*A"
                      using inverse2 by auto
      ultimately have 1:"rat_poly_times B (B - rat_poly_times (rat_poly_times A A) A)
                               =  B*B - A*A"
                by auto
      have "rat_poly_times (rat_poly_times B B) B = (B*B)*B"
                by auto
      then have "(rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) A)
                  = (A*A) - ((B*B)*B)*A"
              using minus_right_distributivity by auto
      moreover have "... = (A*A) - ((B*B)*(B*A))"
                     by auto
      moreover have "... = (A*A) - (B*B)"
                    using inverse2 by auto
      ultimately have 2:"(rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) A)
                  = (A*A) - (B*B)"
                    by auto
      have "B*B - A*A + (A*A) - (B*B) = 0"
                  by auto
      with 1 2 show ?thesis by auto
  qed

lemma aux1:"(A - rat_poly_times (rat_poly_times B B) B)
         = A - (B^3)"
  using power3_eq_cube by (metis)

lemma square_subtract:"(((p::rat_poly) - (q::rat_poly))^2)
         = (p^2) - (2*p*q) + (q^2)"
   proof-
   have 1:"(((p::rat_poly) - (q::rat_poly))^2)
             = (p- q)*(p - q)"
             by (metis power2_eq_square)
   then have "(p - q)*(p - q) = (p - q)*p - (p - q)*q"
             by (metis minus_right_distributivity rat_poly.comm)
   moreover have "(p - q)*p = p*p - q*p"
                 by (metis minus_left_distributivity rat_poly.comm)
   moreover have "(p - q)*q = p*q - q*q"
                 by (metis minus_left_distributivity rat_poly.comm)
   ultimately have "(p - q)*(p - q) = p*p - q*p - (p*q - q*q)"
                by auto
   moreover have "... = (p*p) - q*p - p*q + q*q"
               by auto
   moreover have "... = (p^2) -p*q - p*q + (q^2)"
               by (metis comm_semiring_1_class.normalizing_semiring_rules(7) power2_eq_square)
   ultimately show ?thesis using 1 by auto
qed

lemma cube_minus:"\<forall>p q.((((p::rat_poly) - (q::rat_poly))^3) 
                = (p^3) - 3*(p^2)*(q) + 3*(p)*(q^2) - (q^3))" 
 apply(rule allI)
 apply(rule allI)
 proof-
 fix p q
 have 1:"(((p::rat_poly) - (q::rat_poly))^3) = (p - q)*(p-q)^2"
        by (metis comm_semiring_1_class.normalizing_semiring_rules(7) power2_eq_square power3_eq_cube)       
 then have "(p-q)^2 = (p^2) - (2*p*q) + (q^2)"
            using square_subtract by auto
 then have 2:"(p - q)*(p-q)^2 = (p - q)*((p^2) - (2*p*q) + (q^2))"
                    by auto
 moreover have 3:"(p - q)*((p^2) - (2*p*q) + (q^2))
                   = p*((p^2) - (2*p*q) + (q^2)) 
               - (q*((p^2) - (2*p*q) + (q^2)))"
            by (metis minus_right_distributivity)
 moreover have "p*((p^2) - (2*p*q) + (q^2)) 
                   = p*(p^2) - p*(2*p*q) + (p*(q^2))"
               by (metis comm_semiring_1_class.normalizing_semiring_rules(34) minus_left_distributivity)
 moreover have "p*(p^2) = p^3"
                by (metis comm_semiring_1_class.normalizing_semiring_rules(7) power2_eq_square power3_eq_cube)
 moreover have "p*(2*p*q) = 2*(p^2)*q"
                by (metis (hide_lams, no_types) comm_semiring_1_class.normalizing_semiring_rules(19) comm_semiring_1_class.normalizing_semiring_rules(7) power2_eq_square)
 ultimately have 4:"p*((p^2) - (2*p*q) + (q^2)) 
                   = (p^3) - (2*(p^2)*q) + (p*(q^2))"
                by auto
 have "q*((p^2) - (2*p*q) + (q^2)) 
                   = q*(p^2) - q*(2*p*q) + (q*(q^2))"
               by (metis comm_semiring_1_class.normalizing_semiring_rules(34) minus_left_distributivity)
 moreover have "q*(p^2) = (p^2)*q"
                by (metis comm_semiring_1_class.normalizing_semiring_rules(7) power2_eq_square power3_eq_cube)
 moreover have "q*(2*p*q) = 2*p*(q^2)"
                by (metis (hide_lams, no_types) comm_semiring_1_class.normalizing_semiring_rules(19) comm_semiring_1_class.normalizing_semiring_rules(7) power2_eq_square)
 ultimately have 5:"q*((p^2) - (2*p*q) + (q^2)) 
                   = (p^2)*q - 2*p*(q^2) + (q^3)"
                by (metis comm_semiring_1_class.normalizing_semiring_rules(7) power2_eq_square power3_eq_cube)
 with 1 2 3 4 have "(p - q)^3
                      = (p^3) - (2*(p^2)*q) + (p*(q^2)) 
                          - ((p^2)*q - 2*p*(q^2) + (q^3))"
               by auto
 moreover have "... = (p^3) - (2*(p^2)*q) + (p*(q^2)) 
                     - (p^2)*q + 2*p*(q^2) - (q^3)"
                by auto
 moreover have "... = (p^3) - 3*(p^2)*(q) + 3*(p)*(q^2) - (q^3)" 
                by auto
 ultimately show " (p - q) ^ 3 =
          rat_poly_plus (p ^ 3 - rat_poly_times (rat_poly_times 3 (p\<twosuperior>)) q)
           (rat_poly_times (rat_poly_times 3 p) (q\<twosuperior>)) -
          q ^ 3" by auto
qed

lemma power_mult: "((p::rat_poly)^m)^n= (p)^(m*(n::nat))"
       by (metis power_mult)


lemma cube_minus2:
fixes p q
shows "(((p::rat_poly) - (q::rat_poly))^3) 
                = (p^3) - 3*(p^2)*(q) + 3*(p)*(q^2) - (q^3)" 
        using cube_minus by auto

lemma subst_poly:assumes "a = b" shows "(p::rat_poly)*a = p*b"
           using assms by auto

lemma sub1: assumes "p*q = 1"
       shows "r*(p*q) = r*1"
         using assms by metis

lemma n_distrib:"(A^(n::nat))*(B^n) = (A*B)^n"
       apply(induct_tac n)
       apply(auto)
       done

lemma rat_poly_id_pow:"(1::rat_poly)^n = 1"
     apply(induct_tac n)
     apply(auto)
      done         


lemma power_prod:"(A^(n::nat))*(B^n) = (1::rat_poly)"
        apply(simp add:n_distrib)
        apply(simp add:inverse1)
        done
lemma "(pCons 0 1) \<noteq> 0"
          by (metis non_zero var_def)      
(* 
lemma "(B^3)*(A^2) = B"
     proof-
      have "(B^3) = B*B*B"
           by (metis power3_eq_cube)
      moreover have "(A^2) = A*A"
           by (metis power2_eq_square)
      ultimately have "(B^3)*(A^2) = (B*B*B)*(A*A)"
                by metis
       moreover have "... = (B*B)*(B*A)*A"
                by auto
       moreover have "... = (B*B)*(1::rat_poly)*A"
                by (metis inverse2)
       moreover have "... = (B*B)*A"
                by auto
       moreover have "... = (B*(B*A))"
                by auto
        moreover have "... = (B*(1::rat_poly))"
                using inverse2 by auto
        moreover have "... = B"
                 by auto
        ultimately show ?thesis sledgehammer

lemma "(rat_poly_times (rat_poly_times A A)
       (rat_poly_plus
         (rat_poly_times B
           (rat_poly_times B
             (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
               (rat_poly_times A A))))
         (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
           (rat_poly_plus
             (rat_poly_times B (rat_poly_times B (rat_poly_times A A)))
             (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
               (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
                 (rat_poly_times A A)))))))
= (A^7 + A^4 - 2*(A^3) + 2*B - B^5)"
proof-
have "(rat_poly_times B
           (rat_poly_times B
             (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
               (rat_poly_times A A))))
         = (B*B)*(A - (B^3))*(A*A)"
         using aux1 by auto
then have 1:"(rat_poly_times B
           (rat_poly_times B
             (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
               (rat_poly_times A A)))) = (A - (B^3))"
          by (metis (hide_lams, no_types) aux1 comm_semiring_1_class.normalizing_semiring_rules(11) comm_semiring_1_class.normalizing_semiring_rules(17) comm_semiring_1_class.normalizing_semiring_rules(19) comm_semiring_1_class.normalizing_semiring_rules(7) diff_0 inverse1 minus_diff_eq minus_minus minus_mult_left minus_mult_minus minus_mult_right semiring_norm(3))
then have 2:"(rat_poly_plus
             (rat_poly_times B (rat_poly_times B (rat_poly_times A A)))
             (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
               (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
                 (rat_poly_times A A))))= (1 + ((A - (B^3))^2)*(A^2))"
     proof-
     have "(rat_poly_times B (rat_poly_times B (rat_poly_times A A)))
                 = 1"
               by (metis comm_semiring_1_class.normalizing_semiring_rules(19) inverse1 rat_poly.right_id)
     moreover have "(rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
               (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
                 (rat_poly_times A A)))
                              = ((A - (B^3))^2)*(A^2)"
                      using aux1 power2_eq_square by (metis (hide_lams, no_types) comm_semiring_1_class.normalizing_semiring_rules(19) comm_semiring_1_class.normalizing_semiring_rules(7))
    ultimately show ?thesis by auto
   qed
 then have 3:" (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
           (rat_poly_plus
             (rat_poly_times B (rat_poly_times B (rat_poly_times A A)))
             (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
               (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
                 (rat_poly_times A A)))))
                  = (A -(B^3))*(1 + ((A - (B^3))^2)*(A^2))"
        using aux1 by auto
 have "... = (A -(B^3))*(1 + ((A - (B^3))*((A - (B^3))*(A^2))))"  
             by (metis (hide_lams, no_types) comm_semiring_1_class.normalizing_semiring_rules(19) comm_semiring_1_class.normalizing_semiring_rules(7) power2_eq_square)
 then have "... = (A -(B^3))*(1 + ((A - (B^3))*((A*(A^2) - (B^3)*(A^2)))))"
             by (metis (hide_lams, mono_tags) comm_semiring_1_class.normalizing_semiring_rules(18) comm_semiring_1_class.normalizing_semiring_rules(7) minus_left_distributivity power2_eq_square)
 then have "... 
 have "  (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
                 (rat_poly_times A A))
                = (rat_poly_times A (rat_poly_times A A)) - 
                    (rat_poly_times (rat_poly_times (rat_poly_times B B) B)
                        (rat_poly_times A A))"
                 by (metis minus_left_distributivity rat_poly.comm)
 have "(A -(B^3))*(1 + ((A - (B^3))^2)*(A^2))
            = (A^5) - (B^7) - (2*A) + (2*(B^3)) - (B^7)" (is "?l = ?r")
     proof-
     have "?l = (A -(B^3))*1 + (A -(B^3))*((A - (B^3))^2)*(A^2)"
           by (metis (hide_lams, no_types) comm_semiring_1_class.normalizing_semiring_rules(18) comm_semiring_1_class.normalizing_semiring_rules(34))
     then have "... = (A -(B^3)) + ((A - (B^3))^3)*(A^2)"
            by (metis comm_monoid_mult_class.mult.right_neutral comm_semiring_1_class.normalizing_semiring_rules(7) power2_eq_square power3_eq_cube)    
     have "((A - (B^3))^3) = (A^3)-(3*(A^2)*(B^3)) 
               + (3*A*((B^3)^2))-(B^3)^3"
            using cube_minus2 sorry
     moreover have "(A^2)*(B^3)  = B"
               proof-
               have 0:"A \<noteq> (0::rat_poly)" 
                    using A_non_zero by auto
               have 1:"((A^2)*(B^3)) = (A^2)*(B^2)*B"
                  by (metis comm_semiring_1_class.normalizing_semiring_rules(18) power2_eq_square power3_eq_cube)
               moreover have "(A^2)*(B^2) = (1::rat_poly)"
                  using power_prod by auto
               then have 2:"(A^2)*(B^2)*B = (1::rat_poly)*B"
                         by auto
               moreover then have 3:"... = B"
                        by auto
               ultimately show ?thesis using 0 1 B_non_zero by auto
               qed    *)         
end

