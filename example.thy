theory example
imports Link_Algebra Links
begin

text{*We prove that the link diagram with a single crossing is equivalent to the unknot*}

context Tangle_Equivalence
begin
lemma prelim_cup_compress:
 " ((basic (cup#empty_block)) \<circ> (basic (vert # vert # empty_block))) ~
      ((basic empty_block)\<circ>(basic (cup#empty_block)))"  
 proof-
 have "domain_wall (basic (cup # empty_block)) = 0" 
           by auto
 moreover have "codomain_wall (basic (cup # empty_block)) = 2" 
          by auto
 moreover 
     have "make_vert_block (nat (codomain_wall (basic (cup # empty_block)))) 
                                    = (vert # vert # empty_block)"
          unfolding make_vert_block_def 
           by (metis (mono_tags) calculation(2) nat_2 nat_rec_0 nat_rec_Suc)
 ultimately 
  have "compress_bottom 
          ((basic (cup#empty_block)) \<circ> (basic (vert # vert # empty_block))) 
          ((basic empty_block) \<circ>(basic (cup#empty_block)))" 
           using compress_bottom_def by metis
 then have "compress  ((basic (cup#empty_block)) \<circ> (basic (vert # vert # empty_block))) 
      ((basic empty_block)\<circ>(basic (cup#empty_block)))" 
          using compress_def by auto
 then have "linkrel ((basic (cup#empty_block)) \<circ> (basic (vert # vert # empty_block))) 
      ((basic empty_block)\<circ>(basic (cup#empty_block)))" 
          unfolding linkrel_def by auto
 then show ?thesis using equality by auto
 qed

lemma cup_compress:
 "(basic (cup#empty_block)) \<circ> (basic (vert # vert # empty_block)) ~ (basic (cup#empty_block))"
 proof-
 have " ((basic (cup#empty_block)) \<circ> (basic (vert # vert # empty_block))) ~
      ((basic empty_block)\<circ>(basic (cup#empty_block)))"  
         using prelim_cup_compress  by auto
 moreover have "((basic empty_block)\<circ>(basic (cup#empty_block))) ~  (basic (cup#empty_block))"
         using domain_compose by auto
 ultimately show ?thesis using transitivity by metis
 qed
 
abbreviation x::"wall"
where
"x \<equiv>   ((basic (cup#cup#empty_block))\<circ>(basic (vert#over#vert#empty_block)) 
\<circ> (basic (cap#cap#empty_block)))"

abbreviation y::"wall"
where
"y \<equiv>    ((basic (cup#empty_block)) \<circ> (basic (cap#empty_block)))"

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
  "((basic (cup#empty_block)) \<circ> (left_over \<otimes> straight_line)) 
           ~   ((basic (cup#empty_block)) \<circ> (straight_line \<otimes> straight_line))"
  proof-
  have "is_tangle_diagram (left_over \<otimes> straight_line)"
        by auto
  moreover have "is_tangle_diagram (straight_line \<otimes> straight_line)"
        by auto
  moreover have "is_tangle_diagram (basic (cup#empty_block))" 
         by auto
  moreover have "domain_wall (left_over \<otimes> straight_line) = (codomain_wall (basic (cup#empty_block)))"
        unfolding domain_wall_def by auto
  moreover have "domain_wall (straight_line \<otimes> straight_line) = (codomain_wall (basic (cup#empty_block)))"
        unfolding domain_wall_def by auto
  moreover have "(basic (cup#empty_block)) ~ (basic (cup#empty_block))" 
        using refl by auto
  ultimately show ?thesis 
        using compose_eq 3  by (metis is_tangle_diagram.simps(1) refl)
  qed
 
moreover have 5:"  ((basic (cup#empty_block))\<circ> (straight_line \<otimes> straight_line)) 
                 ~ (basic (cup#empty_block))"
  proof-
   have 0:
   "(basic (cup#empty_block)) \<circ> (straight_line \<otimes> straight_line) = (basic (cup#empty_block))
   \<circ>(basic (vert#vert#empty_block)) \<circ> (basic (vert#vert#empty_block))
   \<circ> (basic (vert#vert#empty_block))"
           by auto
   let ?x ="(basic (cup#empty_block))
   \<circ>(basic (vert#vert#empty_block)) \<circ> (basic (vert#vert#empty_block))
   \<circ> (basic (vert#vert#empty_block))"
   let ?x1 = " (basic (vert#vert#empty_block))\<circ> (basic (vert#vert#empty_block))"
   have 1:"?x ~ ((basic (cup#empty_block)) \<circ> ?x1)"
   proof-
    have "(basic (cup#empty_block))\<circ>(basic (vert # vert # empty_block)) ~ (basic (cup#empty_block))"
         using cup_compress by auto
    moreover have "is_tangle_diagram  (basic (cup#empty_block))" 
         using is_tangle_diagram_def by auto
    moreover have "is_tangle_diagram ((basic (cup#empty_block))\<circ>(basic (vert # vert # empty_block)))"
         using is_tangle_diagram_def by auto
    moreover have "is_tangle_diagram (?x1)"
        by auto
    moreover have "?x1 ~ ?x1" 
        using refl by auto       
    moreover have 
     "codomain_wall (basic (cup#empty_block)) = domain_wall  (basic (vert#vert#empty_block))"
           by auto
    moreover have "(basic (cup#empty_block)) ~ (basic (cup#empty_block))"
         using refl by auto
    ultimately show ?thesis 
                 using compose_eq codomain_wall_compose compose_leftassociativity 
                 converse_composition_of_tangle_diagrams domain_wall_compose
                 by (metis)
    qed
   have 2: " ((basic (cup#empty_block)) \<circ> ?x1) ~ (basic (cup#empty_block))"
    proof-
     have "
     ((basic (cup # empty_block))\<circ>(basic (vert # vert # empty_block)))\<circ>(basic (vert # vert # empty_block)) 
          ~ ((basic(cup#empty_block))\<circ>(basic(vert#vert#empty_block)))"
     proof-
      have "(basic (cup#empty_block))\<circ>(basic (vert # vert # empty_block)) ~ (basic (cup#empty_block))"
         using cup_compress by auto
      moreover have "(basic(vert#vert#empty_block)) ~ (basic(vert#vert#empty_block))" 
         using refl by auto  
      moreover have "is_tangle_diagram  (basic (cup#empty_block))" 
         using is_tangle_diagram_def by auto
      moreover have "is_tangle_diagram ((basic (cup#empty_block))\<circ>(basic (vert # vert # empty_block)))"
         using is_tangle_diagram_def by auto
      moreover have "is_tangle_diagram ((basic(vert#vert#empty_block)))"
         by auto     
      moreover have 
         "codomain_wall ((basic (cup#empty_block))\<circ>  (basic(vert#vert#empty_block))) 
                       = domain_wall  (basic(vert#vert#empty_block))  "
         by auto
      moreover 
         have "codomain_wall (basic (cup#empty_block)) = domain_wall (basic(vert#vert#empty_block))"
         by auto       
      ultimately show ?thesis 
                 using compose_eq 
                 by metis
      qed 
    then have "((basic (cup#empty_block)) \<circ> ?x1) ~
           ((basic(cup#empty_block))\<circ>(basic(vert#vert#empty_block)))"
      by auto
    then show ?thesis using cup_compress transitivity by (metis (full_types)) 
   qed
   from 0 1 2 show ?thesis using transitivity  compose_Nil  by (metis)
   qed
 let ?y = "((basic (empty_block)) \<circ> (basic (cup#empty_block)))  "
 let ?temp = "(basic (vert#over#vert#empty_block))\<circ>(basic (cap#vert#vert#empty_block)) "  
 have 45:"(left_over \<otimes> straight_line) = 
          ((basic (cup#vert#vert#empty_block)) \<circ> ?temp)"  
          using tensor.simps by (metis compose_Nil concatenates_Cons concatenates_Nil)
 then have 55:"(basic (cup#empty_block)) \<circ> (left_over \<otimes> straight_line) 
             =  (basic (cup#empty_block)) \<circ>  (basic (cup#vert#vert#empty_block)) \<circ> ?temp"
                 by auto
 then have 
"(basic (cup#empty_block)) \<circ> (basic (cup#vert#vert#empty_block))
   =  (basic ((empty_block) \<otimes>(cup#empty_block)))\<circ>(basic ((cup#empty_block)\<otimes>(vert#vert#empty_block)))"
         using concatenate.simps  by auto
 then have 6:
 "(basic (cup#empty_block)) \<circ> (basic (cup#vert#vert#empty_block))
          = ((basic (empty_block))\<circ>(basic (cup#empty_block)))
            \<otimes>((basic (cup#empty_block)) \<circ>(basic (vert#vert#empty_block)))"
         using tensor.simps by auto
 then have "((basic (cup#empty_block)) \<circ>(basic (vert#vert#empty_block))) 
                   ~ (basic (empty_block))\<circ>(basic (cup#empty_block))"
         using prelim_cup_compress by auto
 moreover have "((basic (empty_block))\<circ>(basic (cup#empty_block))) 
                       ~ ((basic (empty_block))\<circ>(basic (cup#empty_block)))"
         using refl by auto
 moreover have "is_tangle_diagram ((basic (cup#empty_block)) \<circ>(basic (vert#vert#empty_block)))"
                by auto
 moreover have "is_tangle_diagram ((basic (empty_block))\<circ>(basic (cup#empty_block))) "
                by auto
 ultimately have 7:"?y \<otimes> ((basic (cup#empty_block)) \<circ>(basic (vert#vert#empty_block)))~ ((?y) \<otimes> (?y))"
        using tensor_eq 
        by (metis cup_compress empty_block_right_tensor is_tangle_diagram.simps(1) refl)
 then have " ((?y) \<otimes> (?y)) = (basic ((empty_block) \<otimes> (empty_block)))
                   \<circ> ((basic (cup#empty_block)) \<otimes> (basic (cup#empty_block)))"
                using tensor.simps(4)  by (metis compose_Nil) 
 then have "  ((?y) \<otimes> (?y)) = (basic (empty_block)) \<circ>((basic (cup#cup#empty_block)))"
                  using tensor.simps(1) concatenate_def by auto
 then have "(?y) \<otimes> ((basic (cup#empty_block)) \<circ>(basic (vert#vert#empty_block)))
             ~ (basic (empty_block)) \<circ>(basic (cup#cup#empty_block))" 
              using 7 by auto
  moreover have "(basic (empty_block))\<circ>(basic (cup#cup#empty_block))~(basic (cup#cup#empty_block))"
               proof-
               have "domain_wall (basic (cup#cup#empty_block)) = 0"
                    by auto
                then show ?thesis using domain_compose by auto
                qed
  ultimately have "(?y) \<otimes> ((basic (cup#empty_block)) \<circ>(basic (vert#vert#empty_block)))
             ~  (basic (cup#cup#empty_block))"
                using transitivity by (metis) 
  then have " (basic(cup#empty_block))\<circ>(basic(cup#vert#vert#empty_block))~(basic(cup#cup#empty_block))" 
           by auto
  moreover have "?temp ~ ?temp"
           using refl by auto
  moreover  have "is_tangle_diagram ((basic(cup#empty_block))\<circ>(basic(cup#vert#vert#empty_block)))"
           by auto
  moreover have "is_tangle_diagram (basic(cup#cup#empty_block))"
           by auto
  moreover have "is_tangle_diagram  (?temp)"
           by auto
  moreover have "codomain_wall  ((basic(cup#empty_block))\<circ>(basic(cup#vert#vert#empty_block)))
                    = domain_wall ?temp"
             by auto
   moreover have "codomain_wall (basic(cup#cup#empty_block)) = domain_wall ?temp"
             by auto
   ultimately have 8:" ((basic(cup#empty_block))\<circ>(basic(cup#vert#vert#empty_block))) \<circ>(?temp)
                       ~ (basic(cup#cup#empty_block)) \<circ> (?temp)"
               using compose_eq by metis
   then have "((basic(cup#cup#empty_block)) \<circ> (?temp)) 
                 ~ ((basic(cup#empty_block)) \<circ> (left_over \<otimes> straight_line))"
              using 55 compose_leftassociativity sym   
               by metis 
   moreover have "((basic(cup#empty_block)) \<circ> (left_over \<otimes> straight_line)) 
                    ~ ((basic(cup#empty_block)) \<circ> (straight_line \<otimes> straight_line))"
                  using 4 by auto
   ultimately have "(basic(cup#cup#empty_block)) \<circ> (?temp) 
                  ~ (basic (cup # empty_block))\<circ>(straight_line \<otimes> straight_line)"
            using trans transp_def 4 45 by metis 
  then have "(basic(cup#cup#empty_block)) \<circ> (?temp)  ~ (basic (cup # empty_block))"
            using trans transp_def 5 by metis
  moreover have "(basic (cap#empty_block)) ~ (basic (cap#empty_block))"
            using refl by auto
  moreover have "is_tangle_diagram ((basic(cup#cup#empty_block)) \<circ> (?temp))"
            by auto
  moreover have "is_tangle_diagram (basic (cup # empty_block))"
           by auto
  moreover have "is_tangle_diagram (basic (cap # empty_block))"
           by auto
  moreover have "codomain_wall ((basic(cup#cup#empty_block)) \<circ> (?temp)) 
                   = domain_wall (basic (cap # empty_block))"
           by auto
  moreover have "codomain_wall (basic(cup#empty_block)) = domain_wall (basic (cap # empty_block))"
            by auto
 ultimately have 9:"((basic(cup#cup#empty_block)) \<circ> (?temp)) \<circ> (basic (cap#empty_block))
                     ~ (basic (cup#empty_block)) \<circ> (basic (cap#empty_block))"
              using compose_eq by metis
  let ?z = "((basic(cup#cup#empty_block)) \<circ> (basic(vert#over#vert#empty_block)))"
  have 10:"((basic(cup#cup#empty_block)) \<circ> (?temp)) \<circ> (basic (cap#empty_block))
              = ?z \<circ> ((basic(cap#vert#vert#empty_block)) \<circ> (basic (cap#empty_block)))"
      by auto
  then have 11:"((basic(cap#vert#vert#empty_block)) \<circ> (basic (cap#empty_block)))
 = ((basic ((cap#empty_block)\<otimes>(vert#vert#empty_block)))\<circ>(basic ((empty_block) \<otimes>(cap#empty_block))))"
      unfolding concatenate_def by auto
  then have 12:" ((basic(cap#vert#vert#empty_block)) \<circ> (basic (cap#empty_block)))
 = ((basic (cap#empty_block))\<circ>(basic (empty_block)))
\<otimes>((basic (vert#vert#empty_block))\<circ>(basic (cap#empty_block)))"
  using tensor.simps by auto
 let ?w = "((basic (cap#empty_block))\<circ>(basic (empty_block)))"
 have 13:"((basic (vert#vert#empty_block))\<circ>(basic (cap#empty_block))) ~ ?w"
      proof-
      have "codomain_wall (basic (cap#empty_block)) = 0" 
       by auto
      moreover have "domain_wall (basic (cap#empty_block)) = 2" by auto
      moreover then have "(vert#vert#empty_block) 
                          = make_vert_block (nat (domain_wall (basic (cap#empty_block))))"
               using make_vert_block_def domain_wall_def by (metis Suc_eq_plus1_left 
               make_vert_block.simps(1) make_vert_block.simps(2) nat_1 nat_numeral one_add_one 
               transfer_nat_int_numerals(2))
     ultimately have "compress_top  ((basic (vert#vert#empty_block))\<circ>(basic (cap#empty_block))) ?w"
               using compress_top_def by auto
     then have "compress ((basic (vert#vert#empty_block))\<circ>(basic (cap#empty_block))) ?w" 
               using compress_def by auto
     then have "linkrel  ((basic (vert#vert#empty_block))\<circ>(basic (cap#empty_block))) ?w" 
               using linkrel_def by auto
     then have " ((basic (vert#vert#empty_block))\<circ>(basic (cap#empty_block))) ~ ?w"
               using equality by auto
     then show ?thesis by simp
     qed
 moreover have "is_tangle_diagram ((basic (vert#vert#empty_block))\<circ>(basic (cap#empty_block)))"
       by auto
 moreover have "is_tangle_diagram ?w"
      by auto
 moreover have "?w ~ ?w" 
      using refl by auto
 ultimately have 14:"(?w) \<otimes> ((basic (vert#vert#empty_block))\<circ>(basic (cap#empty_block))) ~ ((?w)\<otimes> (?w))"
     using tensor_eq by metis
 then have "((basic(cap#vert#vert#empty_block)) \<circ> (basic (cap#empty_block))) ~ ((?w)\<otimes> (?w))"
     using 13 by auto
 moreover have " ((?w)\<otimes> (?w)) = (basic (cap#cap#empty_block)) \<circ> (basic (empty_block))"
          using tensor.simps by auto
 ultimately have "((basic(cap#vert#vert#empty_block)) \<circ> (basic (cap#empty_block))) ~ 
                           (basic (cap#cap#empty_block)) \<circ> (basic (empty_block))"
               by auto
 moreover have "?z ~ ?z" 
           using refl by auto
 moreover have "domain_wall ((basic(cap#cap#empty_block)) \<circ> (basic (empty_block)))
                                = codomain_wall (?z)"
               by auto
 moreover have "domain_wall (((basic(cap#vert#vert#empty_block)) \<circ> (basic (cap#empty_block))))
                                = codomain_wall (?z)" 
              by auto
 moreover have "is_tangle_diagram ((basic(cap#vert#vert#empty_block)) \<circ> (basic (cap#empty_block)))"
              by auto
 moreover have "is_tangle_diagram (?z)"
              by auto
 moreover have "is_tangle_diagram  ((basic(cap#cap#empty_block)) \<circ> (basic (empty_block)))"
             by auto
 ultimately have 14:" (?z) \<circ>  ((basic(cap#vert#vert#empty_block)) \<circ> (basic (cap#empty_block)))
                      ~ (?z) \<circ> ((basic(cap#cap#empty_block)) \<circ> (basic (empty_block)))"
               using compose_eq by metis
 moreover  have "((?z) \<circ> ((basic(cap#cap#empty_block))) \<circ> (basic (empty_block))) 
                ~ ((?z) \<circ> (basic(cap#cap#empty_block)))"
               using codomain_compose by (metis `codomain_wall (basic (cup # cup # empty_block)) = domain_wall (basic (vert # over # vert # empty_block) \<circ> basic (cap # vert # vert # empty_block))` `domain_wall (basic (cap # cap # empty_block) \<circ> basic empty_block) = codomain_wall (basic (cup # cup # empty_block) \<circ> basic (vert # over # vert # empty_block))` `is_tangle_diagram (basic (cap # cap # empty_block) \<circ> basic empty_block)` codomain_wall_compose comp_of_tangle_dgms compose_eq compose_leftassociativity converse_composition_of_tangle_diagrams domain_wall_compose domain_wall_empty is_tangle_diagram.simps(1) refl)
 ultimately have "(?z) \<circ>  ((basic(cap#vert#vert#empty_block)) \<circ> (basic (cap#empty_block)))
                     ~ ((?z) \<circ> (basic(cap#cap#empty_block)))"
             using trans transp_def by metis
 then have "((?z) \<circ> (basic(cap#cap#empty_block))) ~ ((basic (cup#empty_block))\<circ>(basic (cap#empty_block)))"
        using 9 10 trans transp_def by (metis sym transitivity)
 then show ?thesis by auto
qed
     
        
