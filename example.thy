theory example
imports Link_Algebra Links
begin

text{*We prove that a link diagram with a single crossing is equivalent to the unknot*}

context Tangle_Equivalence
begin
lemma prelim_cup_compress:
 " ((basic (cup#[])) \<circ> (basic (vert # vert # []))) ~
      ((basic [])\<circ>(basic (cup#[])))"  
 proof-
 have "domain_wall (basic (cup # [])) = 0" 
           by auto
 moreover have "codomain_wall (basic (cup # [])) = 2" 
          by auto
 moreover 
     have "make_vert_block (nat (codomain_wall (basic (cup # [])))) 
                                    = (vert # vert # [])"
          unfolding make_vert_block_def 
           by (metis (mono_tags) calculation(2) nat_2 nat_rec_0 nat_rec_Suc)
 ultimately 
  have "compress_bottom 
          ((basic (cup#[])) \<circ> (basic (vert # vert # []))) 
          ((basic []) \<circ>(basic (cup#[])))" 
           using compress_bottom_def by metis
 then have "compress  ((basic (cup#[])) \<circ> (basic (vert # vert # []))) 
      ((basic [])\<circ>(basic (cup#[])))" 
          using compress_def by auto
 then have "linkrel ((basic (cup#[])) \<circ> (basic (vert # vert # []))) 
      ((basic [])\<circ>(basic (cup#[])))" 
          unfolding linkrel_def by auto
 then show ?thesis using equality by auto
 qed

lemma cup_compress:
 "(basic (cup#[])) \<circ> (basic (vert # vert # [])) ~ (basic (cup#[]))"
 proof-
 have " ((basic (cup#[])) \<circ> (basic (vert # vert # []))) ~
      ((basic [])\<circ>(basic (cup#[])))"  
         using prelim_cup_compress  by auto
 moreover have "((basic [])\<circ>(basic (cup#[]))) ~  (basic (cup#[]))"
         using domain_compose by auto
 ultimately show ?thesis using transitivity by metis
 qed
 
abbreviation x::"wall"
where
"x \<equiv>   (basic [cup,cup])\<circ>(basic [vert,over,vert]) \<circ> (basic [cap,cap])"

abbreviation y::"wall"
where
"y \<equiv>    (basic [cup]) \<circ> (basic [cap])"

theorem example:
  "x ~ y" 
proof-
have "uncross_negative_straighten left_over straight_line" 
    using uncross_negative_straighten_def by auto
then have "uncross left_over straight_line"
    using uncross_def by auto
then have "linkrel left_over straight_line"
    using linkrel_def by auto
then have 1:"left_over ~ straight_line"
    using equality by auto
moreover have 2:"straight_line ~ straight_line"
   using refl by auto
have 3:"(left_over \<otimes> straight_line) ~ (straight_line \<otimes> straight_line)"
 proof-
  have "is_tangle_diagram (left_over)"
    unfolding is_tangle_diagram_def by auto 
  moreover have "is_tangle_diagram (straight_line)"
    unfolding is_tangle_diagram_def by auto
  ultimately show ?thesis using 1 2 by (metis tensor_eq)
 qed
then have 4:
  "((basic (cup#[])) \<circ> (left_over \<otimes> straight_line)) 
           ~   ((basic (cup#[])) \<circ> (straight_line \<otimes> straight_line))"
  proof-
  have "is_tangle_diagram (left_over \<otimes> straight_line)"
        by auto
  moreover have "is_tangle_diagram (straight_line \<otimes> straight_line)"
        by auto
  moreover have "is_tangle_diagram (basic (cup#[]))" 
         by auto
  moreover have "domain_wall (left_over \<otimes> straight_line) = (codomain_wall (basic (cup#[])))"
        unfolding domain_wall_def by auto
  moreover have "domain_wall (straight_line \<otimes> straight_line) = (codomain_wall (basic (cup#[])))"
        unfolding domain_wall_def by auto
  moreover have "(basic (cup#[])) ~ (basic (cup#[]))" 
        using refl by auto
  ultimately show ?thesis 
        using compose_eq 3  by (metis is_tangle_diagram.simps(1) refl)
  qed
 
moreover have 5:"  (basic [cup])\<circ> (straight_line \<otimes> straight_line) 
                 ~ (basic [cup])"
  proof-
   have 0:
   "(basic ([cup])) \<circ> (straight_line \<otimes> straight_line) = (basic [cup]) \<circ>(basic [vert,vert]) 
                                                         \<circ> (basic [vert,vert])\<circ>(basic [vert,vert])"
           by auto
   let ?x ="(basic (cup#[]))
   \<circ>(basic (vert#vert#[])) \<circ> (basic (vert#vert#[]))
   \<circ> (basic (vert#vert#[]))"
   let ?x1 = " (basic (vert#vert#[]))\<circ> (basic (vert#vert#[]))"
   have 1:"?x ~ ((basic (cup#[])) \<circ> ?x1)"
   proof-
    have "(basic (cup#[]))\<circ>(basic (vert # vert # [])) ~ (basic (cup#[]))"
         using cup_compress by auto
    moreover have "is_tangle_diagram  (basic (cup#[]))" 
         using is_tangle_diagram_def by auto
    moreover have "is_tangle_diagram ((basic (cup#[]))\<circ>(basic (vert # vert # [])))"
         using is_tangle_diagram_def by auto
    moreover have "is_tangle_diagram (?x1)"
        by auto
    moreover have "?x1 ~ ?x1" 
        using refl by auto       
    moreover have 
     "codomain_wall (basic (cup#[])) = domain_wall  (basic (vert#vert#[]))"
           by auto
    moreover have "(basic (cup#[])) ~ (basic (cup#[]))"
         using refl by auto
    ultimately show ?thesis 
                 using compose_eq codomain_wall_compose compose_leftassociativity 
                 converse_composition_of_tangle_diagrams domain_wall_compose
                 by (metis)
    qed
   have 2: " ((basic (cup#[])) \<circ> ?x1) ~ (basic (cup#[]))"
    proof-
     have "
     ((basic (cup # []))\<circ>(basic (vert # vert # [])))\<circ>(basic (vert # vert # [])) 
          ~ ((basic(cup#[]))\<circ>(basic(vert#vert#[])))"
     proof-
      have "(basic (cup#[]))\<circ>(basic (vert # vert # [])) ~ (basic (cup#[]))"
         using cup_compress by auto
      moreover have "(basic(vert#vert#[])) ~ (basic(vert#vert#[]))" 
         using refl by auto  
      moreover have "is_tangle_diagram  (basic (cup#[]))" 
         using is_tangle_diagram_def by auto
      moreover have "is_tangle_diagram ((basic (cup#[]))\<circ>(basic (vert # vert # [])))"
         using is_tangle_diagram_def by auto
      moreover have "is_tangle_diagram ((basic(vert#vert#[])))"
         by auto     
      moreover have 
         "codomain_wall ((basic (cup#[]))\<circ>  (basic(vert#vert#[]))) 
                       = domain_wall  (basic(vert#vert#[]))  "
         by auto
      moreover 
         have "codomain_wall (basic (cup#[])) = domain_wall (basic(vert#vert#[]))"
         by auto       
      ultimately show ?thesis 
                 using compose_eq 
                 by metis
      qed 
    then have "((basic (cup#[])) \<circ> ?x1) ~
           ((basic(cup#[]))\<circ>(basic(vert#vert#[])))"
      by auto
    then show ?thesis using cup_compress transitivity by (metis (full_types)) 
   qed
   from 0 1 2 show ?thesis using trans transp_def transitivity  compose_Nil by (metis (full_types))
   qed
 let ?y = "((basic ([])) \<circ> (basic (cup#[])))  "
 let ?temp = "(basic (vert#over#vert#[]))\<circ>(basic (cap#vert#vert#[])) "  
 have 45:"(left_over \<otimes> straight_line) = 
          ((basic (cup#vert#vert#[])) \<circ> ?temp)"  
          using tensor.simps by (metis compose_Nil concatenates_Cons concatenates_Nil)
 then have 55:"(basic (cup#[])) \<circ> (left_over \<otimes> straight_line) 
             =  (basic (cup#[])) \<circ>  (basic (cup#vert#vert#[])) \<circ> ?temp"
                 by auto
 then have 
"(basic (cup#[])) \<circ> (basic (cup#vert#vert#[]))
   =  (basic (([]) \<otimes>(cup#[])))\<circ>(basic ((cup#[])\<otimes>(vert#vert#[])))"
         using concatenate.simps  by auto
 then have 6:
 "(basic (cup#[])) \<circ> (basic (cup#vert#vert#[]))
          = ((basic ([]))\<circ>(basic (cup#[])))
            \<otimes>((basic (cup#[])) \<circ>(basic (vert#vert#[])))"
         using tensor.simps by auto
 then have "((basic (cup#[])) \<circ>(basic (vert#vert#[]))) 
                   ~ (basic ([]))\<circ>(basic (cup#[]))"
         using prelim_cup_compress by auto
 moreover have "((basic ([]))\<circ>(basic (cup#[]))) 
                       ~ ((basic ([]))\<circ>(basic (cup#[])))"
         using refl by auto
 moreover have "is_tangle_diagram ((basic (cup#[])) \<circ>(basic (vert#vert#[])))"
                by auto
 moreover have "is_tangle_diagram ((basic ([]))\<circ>(basic (cup#[]))) "
                by auto
 ultimately have 7:"?y \<otimes> ((basic (cup#[])) \<circ>(basic (vert#vert#[])))~ ((?y) \<otimes> (?y))"
        using tensor_eq 
        by (metis cup_compress Nil_right_tensor is_tangle_diagram.simps(1) refl)
 then have " ((?y) \<otimes> (?y)) = (basic (([]) \<otimes> ([])))
                   \<circ> ((basic (cup#[])) \<otimes> (basic (cup#[])))"
                using tensor.simps(4)  by (metis compose_Nil) 
 then have "  ((?y) \<otimes> (?y)) = (basic ([])) \<circ>((basic (cup#cup#[])))"
                  using tensor.simps(1) concatenate_def by auto
 then have "(?y) \<otimes> ((basic (cup#[])) \<circ>(basic (vert#vert#[])))
             ~ (basic ([])) \<circ>(basic (cup#cup#[]))" 
              using 7 by auto
  moreover have "(basic ([]))\<circ>(basic (cup#cup#[]))~(basic (cup#cup#[]))"
               proof-
               have "domain_wall (basic (cup#cup#[])) = 0"
                    by auto
                then show ?thesis using domain_compose by auto
                qed
  ultimately have "(?y) \<otimes> ((basic (cup#[])) \<circ>(basic (vert#vert#[])))
             ~  (basic (cup#cup#[]))"
                using transitivity by (metis) 
  then have " (basic(cup#[]))\<circ>(basic(cup#vert#vert#[]))~(basic(cup#cup#[]))" 
           by auto
  moreover have "?temp ~ ?temp"
           using refl by auto
  moreover  have "is_tangle_diagram ((basic(cup#[]))\<circ>(basic(cup#vert#vert#[])))"
           by auto
  moreover have "is_tangle_diagram (basic(cup#cup#[]))"
           by auto
  moreover have "is_tangle_diagram  (?temp)"
           by auto
  moreover have "codomain_wall  ((basic(cup#[]))\<circ>(basic(cup#vert#vert#[])))
                    = domain_wall ?temp"
             by auto
   moreover have "codomain_wall (basic(cup#cup#[])) = domain_wall ?temp"
             by auto
   ultimately have 8:" ((basic(cup#[]))\<circ>(basic(cup#vert#vert#[]))) \<circ>(?temp)
                       ~ (basic(cup#cup#[])) \<circ> (?temp)"
               using compose_eq by metis
   then have "((basic(cup#cup#[])) \<circ> (?temp)) 
                 ~ ((basic(cup#[])) \<circ> (left_over \<otimes> straight_line))"
              using 55 compose_leftassociativity sym   
               by metis 
   moreover have "((basic(cup#[])) \<circ> (left_over \<otimes> straight_line)) 
                    ~ ((basic(cup#[])) \<circ> (straight_line \<otimes> straight_line))"
                  using 4 by auto
   ultimately have "(basic(cup#cup#[])) \<circ> (?temp) 
                  ~ (basic (cup # []))\<circ>(straight_line \<otimes> straight_line)"
            using trans transp_def 4 45 by (metis (full_types))
  then have "(basic(cup#cup#[])) \<circ> (?temp)  ~ (basic (cup # []))"
            using trans transp_def 5 by metis
  moreover have "(basic (cap#[])) ~ (basic (cap#[]))"
            using refl by auto
  moreover have "is_tangle_diagram ((basic(cup#cup#[])) \<circ> (?temp))"
            by auto
  moreover have "is_tangle_diagram (basic (cup # []))"
           by auto
  moreover have "is_tangle_diagram (basic (cap # []))"
           by auto
  moreover have "codomain_wall ((basic(cup#cup#[])) \<circ> (?temp)) 
                   = domain_wall (basic (cap # []))"
           by auto
  moreover have "codomain_wall (basic(cup#[])) = domain_wall (basic (cap # []))"
            by auto
 ultimately have 9:"((basic(cup#cup#[])) \<circ> (?temp)) \<circ> (basic (cap#[]))
                     ~ (basic (cup#[])) \<circ> (basic (cap#[]))"
              using compose_eq by metis
  let ?z = "((basic(cup#cup#[])) \<circ> (basic(vert#over#vert#[])))"
  have 10:"((basic(cup#cup#[])) \<circ> (?temp)) \<circ> (basic (cap#[]))
              = ?z \<circ> ((basic(cap#vert#vert#[])) \<circ> (basic (cap#[])))"
      by auto
  then have 11:"((basic(cap#vert#vert#[])) \<circ> (basic (cap#[])))
 = ((basic ((cap#[])\<otimes>(vert#vert#[])))\<circ>(basic (([]) \<otimes>(cap#[]))))"
      unfolding concatenate_def by auto
  then have 12:" ((basic(cap#vert#vert#[])) \<circ> (basic (cap#[])))
 = ((basic (cap#[]))\<circ>(basic ([])))
\<otimes>((basic (vert#vert#[]))\<circ>(basic (cap#[])))"
  using tensor.simps by auto
 let ?w = "((basic (cap#[]))\<circ>(basic ([])))"
 have 13:"((basic (vert#vert#[]))\<circ>(basic (cap#[]))) ~ ?w"
      proof-
      have "codomain_wall (basic (cap#[])) = 0" 
       by auto
      moreover have "domain_wall (basic (cap#[])) = 2" by auto
      moreover then have "(vert#vert#[]) 
                          = make_vert_block (nat (domain_wall (basic (cap#[]))))"
               using make_vert_block_def domain_wall_def by (metis Suc_eq_plus1_left 
               make_vert_block.simps(1) make_vert_block.simps(2) nat_1 nat_numeral one_add_one 
               transfer_nat_int_numerals(2))
     ultimately have "compress_top  ((basic (vert#vert#[]))\<circ>(basic (cap#[]))) ?w"
               using compress_top_def by auto
     then have "compress ((basic (vert#vert#[]))\<circ>(basic (cap#[]))) ?w" 
               using compress_def by auto
     then have "linkrel  ((basic (vert#vert#[]))\<circ>(basic (cap#[]))) ?w" 
               using linkrel_def by auto
     then have " ((basic (vert#vert#[]))\<circ>(basic (cap#[]))) ~ ?w"
               using equality by auto
     then show ?thesis by simp
     qed
 moreover have "is_tangle_diagram ((basic (vert#vert#[]))\<circ>(basic (cap#[])))"
       by auto
 moreover have "is_tangle_diagram ?w"
      by auto
 moreover have "?w ~ ?w" 
      using refl by auto
 ultimately have 14:"(?w) \<otimes> ((basic (vert#vert#[]))\<circ>(basic (cap#[]))) ~ ((?w)\<otimes> (?w))"
     using tensor_eq by metis
 then have "((basic(cap#vert#vert#[])) \<circ> (basic (cap#[]))) ~ ((?w)\<otimes> (?w))"
     using 13 by auto
 moreover have " ((?w)\<otimes> (?w)) = (basic (cap#cap#[])) \<circ> (basic ([]))"
          using tensor.simps by auto
 ultimately have "((basic(cap#vert#vert#[])) \<circ> (basic (cap#[]))) ~ 
                           (basic (cap#cap#[])) \<circ> (basic ([]))"
               by auto
 moreover have "?z ~ ?z" 
           using refl by auto
 moreover have "domain_wall ((basic(cap#cap#[])) \<circ> (basic ([])))
                                = codomain_wall (?z)"
               by auto
 moreover have "domain_wall (((basic(cap#vert#vert#[])) \<circ> (basic (cap#[]))))
                                = codomain_wall (?z)" 
              by auto
 moreover have "is_tangle_diagram ((basic(cap#vert#vert#[])) \<circ> (basic (cap#[])))"
              by auto
 moreover have "is_tangle_diagram (?z)"
              by auto
 moreover have "is_tangle_diagram  ((basic(cap#cap#[])) \<circ> (basic ([])))"
             by auto
 ultimately have 14:" (?z) \<circ>  ((basic(cap#vert#vert#[])) \<circ> (basic (cap#[])))
                      ~ (?z) \<circ> ((basic(cap#cap#[])) \<circ> (basic ([])))"
               using compose_eq by metis
 moreover  have "((?z) \<circ> ((basic(cap#cap#[]))) \<circ> (basic ([]))) 
                ~ ((?z) \<circ> (basic(cap#cap#[])))"
               using codomain_compose
       by (metis `is_tangle_diagram (basic [cap, cap] \<circ> basic [])` codomain_wall_compose compose_leftassociativity converse_composition_of_tangle_diagrams domain_wall_empty)
 ultimately have "(?z) \<circ>  ((basic(cap#vert#vert#[])) \<circ> (basic (cap#[])))
                     ~ ((?z) \<circ> (basic(cap#cap#[])))"
             using trans transp_def by metis
 then have "((?z) \<circ> (basic(cap#cap#[]))) ~ ((basic (cup#[]))\<circ>(basic (cap#[])))"
        using 9 10 trans transp_def by (metis sym transitivity)
 then show ?thesis by auto
qed
     
 end       
