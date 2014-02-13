theory example
imports Links
begin

lemma assumes "well_defined x" shows "Rep_diagram (Abs_diagram x) = x"
 using Abs_Rep_well_defined assms by auto

text{*We prove that the link diagram with a single crossing is equivalent to the unknot*}


lemma linkrel_trans: assumes "link_equiv x y" and "link_equiv y z"
shows "link_equiv x z"
using rtranclp_trans link_equiv_def linkrel_diagram_equiv_def by (metis (full_types) assms(1) assms(2))

theorem example:
assumes "A = (Abs_diagram ((basic (cement cup)) 
               \<circ>(basic ((cement cup) \<otimes> (cement vert) \<otimes> (cement vert))) 
               \<circ>(basic ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) 
               \<circ>(basic ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert)))
               \<circ> (basic (cement cap))))"
and "B = (Abs_diagram  ((basic (cement cup))\<circ>((basic ((cement vert)\<otimes>(cement vert)))
                                      \<circ>(basic ((cement vert)\<otimes>(cement vert)))
                                      \<circ>(basic ((cement vert)\<otimes>(cement vert)))) 
                                      \<circ>(basic (cement cap))))" 
shows "link_equiv A B"
proof-
 let ?A = "(basic ((cement cup) \<otimes> (cement vert) \<otimes> (cement vert))) 
               \<circ>(basic ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) 
               \<circ>(basic ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert)))"
 let ?B = " ((basic ((cement cup) \<otimes> (cement vert))) 
               \<circ>(basic ((cement vert) \<otimes> (cement over))) 
               \<circ>(basic ((cement cap) \<otimes> (cement vert))))"
 let ?C = "((basic (cement vert)) \<circ> (basic (cement vert)) \<circ> (basic (cement vert)))"
 have 1:"?A = ?B\<otimes>?C"
 proof-
   have  "?B
           =  ((cement cup) \<otimes> (cement vert)) 
               *((basic ((cement vert) \<otimes> (cement over))) 
               \<circ>(basic ((cement cap) \<otimes> (cement vert))))"
              unfolding compose_def by auto
   then have 2:"?C = (cement vert) *((basic (cement vert)) \<circ> (basic (cement vert)))"
            unfolding compose_def by auto
   let ?B1 = "((basic ((cement vert) \<otimes> (cement over))) 
               \<circ>(basic ((cement cap) \<otimes> (cement vert))))"
   let ?C1= "((basic (cement vert)) \<circ> (basic (cement vert)))"
   have 3:"?B \<otimes> ?C =  ((cement cup) \<otimes> (cement vert) \<otimes> (cement vert)) * (?B1 \<otimes> ?C1)"
                   unfolding tensor.simps(4) by auto
   then have "?B \<otimes> ?C = (basic ((cement cup) \<otimes> (cement vert) \<otimes> (cement vert))) \<circ> (?B1 \<otimes> ?C1)"
                   unfolding compose_def by auto
   moreover then have "?B1 \<otimes> ?C1 = ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))* 
                                   ((basic ((cement cap) \<otimes> (cement vert))) \<otimes> (basic (cement vert)))"
                       by auto
   moreover then have "?B1 \<otimes> ?C1 = 
                         (basic ((cement vert) \<otimes> (cement over) \<otimes> (cement vert))) 
                       \<circ>((basic ((cement cap) \<otimes> (cement vert))) \<otimes> (basic (cement vert))) "
                         by auto
   moreover then have "((basic ((cement cap) \<otimes> (cement vert))) \<otimes> (basic (cement vert))) = 
                       (basic ((cement cap) \<otimes> (cement vert) \<otimes> (cement vert)))"
                          by auto
   ultimately have "?B \<otimes> ?C = ?A" by auto
   from this show ?thesis by simp
 qed  
 moreover have "linkrel_uncross_positivestraighten 
                         ?B ((basic (cement vert))\<circ>(basic (cement vert)) \<circ>(basic (cement vert)))"
     using linkrel_uncross_positivestraighten_def by auto
 then have 2:"linkrel  ?B ((basic (cement vert))\<circ>(basic (cement vert)) \<circ>(basic (cement vert)))"
    using linkrel_def linkrel_uncross_def by auto
 let ?X = "((basic (cement cup)) \<circ> (?B \<otimes> ?C) \<circ> (basic (cement cap)))"
 let ?Y = "((basic (cement cup))\<circ>(((basic (cement vert))\<circ>(basic (cement vert))\<circ>(basic (cement vert)))\<otimes> ?C)
           \<circ> (basic (cement cap)))"
 have "\<exists>A.\<exists>B1.\<exists>B2.\<exists>C.\<exists>D.(?X = (A \<circ> (B1\<otimes> C) \<circ> D))"
           using exI by metis
 moreover have "\<exists>A.\<exists>B1.\<exists>B2.\<exists>C.\<exists>D.(?Y = (A \<circ> (B2 \<otimes> C)\<circ> D))" using exI by metis
 ultimately have "\<exists>A.\<exists>B1.\<exists>B2.\<exists>C.\<exists>D.((?X = (A \<circ> (B1\<otimes> C)\<circ> D))\<and> (?Y = (A \<circ> (B2 \<otimes> C)\<circ> D)))"  
                using exI by metis
 from this and 2 have "\<exists>A.\<exists>B1.\<exists>B2.\<exists>C.\<exists>D.((?X = (A \<circ> (B1\<otimes> C) \<circ> D))\<and> (?Y = (A \<circ>(B2 \<otimes> C)\<circ> D)) 
                                             \<and> (linkrel B1 B2))"
                               by metis
 from this have 3: "linkrel_diagram_middle_left ?X ?Y" unfolding linkrel_diagram_middle_left_def by auto   
 have 4:"(((basic (cement vert))\<circ>(basic (cement vert)) \<circ>(basic (cement vert))) \<otimes>?C)
         = ((basic ((cement vert)\<otimes>(cement vert)))\<circ>(basic ((cement vert)\<otimes>(cement vert)))\<circ>
            (basic ((cement vert)\<otimes>(cement vert))))" by auto
 let ?Z = " ((basic (cement cup))\<circ>((basic ((cement vert)\<otimes>(cement vert)))
                                      \<circ>(basic ((cement vert)\<otimes>(cement vert)))
                                      \<circ>(basic ((cement vert)\<otimes>(cement vert)))) 
                                      \<circ>(basic (cement cap)))"
 from 4 have "?Z = ?Y" by auto
 from this 3 have "linkrel_diagram_middle_left ?X ?Z" by auto
 from this have "linkrel_diagram ?X ?Z" unfolding linkrel_diagram_def by auto
 then have 5:"linkrel_diagram_equiv ?X ?Z" unfolding linkrel_diagram_equiv_def r_into_rtranclp by auto

 have "well_defined ?X"
    proof-
     have "domain_codomain_list ?Z = [0,0,0,0]" 
      proof-
         let ?X1 = " (cement cup)"
         let ?X2 = "((cement cup) \<otimes> (cement vert) \<otimes> (cement vert))"
         let ?X3 = "((cement vert) \<otimes> (cement over) \<otimes> (cement vert))"
         let ?X4 =  "((cement cap) \<otimes> (cement vert) \<otimes> (cement vert))"
         let ?X5 =  " (basic (cement cap))"
         have "?X = (?X1)*(?X2)*(?X3)*(?X4)*(?X5)" using compose_def by auto
         have 1:"domain_codomain_list ((?X4)*(?X5)) = [0]" 
          proof-
           have "codomain_block (?X4) = 2" by auto
           moreover have "domain_wall (?X5) = 2" by auto
           ultimately have "domain_codomain_list ((?X4)*(?X5)) = [0]" 
                unfolding domain_codomain_list.simps 
                by (metis Tangles.abs_zero diagram_snd_wall_count diff_self)
           from this show ?thesis by auto
          qed
         have 2:"domain_codomain_list ((?X3)*(?X4)*(?X5)) = [0,0]"           
           proof-
            have "codomain_block (?X3) = 4" by auto
            moreover have "domain_wall ((?X4)*(?X5)) = 4" by auto
            ultimately  have "domain_codomain_list ((?X3)*(?X4)*(?X5)) = [0,0]" 
                       unfolding domain_codomain_list.simps 
                       using 1
                       by auto
            from this show ?thesis by auto
           qed
         have "domain_codomain_list ((?X2)*(?X3)*(?X4)*(?X5)) = [0,0,0]"
          proof-
           have "codomain_block ?X2 = 4" by auto
           moreover have "domain_wall ((?X3)*(?X4)*(?X5)) = 4" by auto
           ultimately have "domain_codomain_list ((?X2)*(?X3)*(?X4)*(?X5)) = [0,0,0]" 
                     unfolding domain_codomain_list.simps 
                     using 1 2 
                     by auto
           from this show ?thesis by auto
          qed
        then have "codomain_block ?X1 = 2" by auto
        moreover have "domain_wall ((?X2)*(?X3)*(?X4)*(?X5)) = 2" by auto
        ultimately have "domain_codomain_list ?X = [0,0,0,0]"
                     unfolding domain_codomain_list.simps
                     using 1 2 by auto
        then show ?thesis by simp
   qed
   moreover have "domain_wall ?X = 0" and "codomain_wall ?X = 0" by auto
   ultimately have "well_defined ?X" using well_defined_def list_sum_def by auto
   then show ?thesis by auto
   qed 
 then have 6: "Rep_diagram (Abs_diagram ?X) = ?X" 
        using  Abs_Rep_well_defined by auto
 have "well_defined ?Z"
    proof-
     have "domain_codomain_list ?Z = [0,0,0,0]" 
      proof-
         let ?Z1 = "(cement cup)"
         let ?Z2 = "((cement vert)\<otimes>(cement vert))"
         let ?Z3 =  "(basic (cement cap))"
         have "?Z = (?Z1)*(?Z2)*(?Z2)*(?Z2)*(?Z3)" using compose_def by auto
         have 1:"domain_codomain_list ((?Z2)*(?Z3)) = [0]" 
          proof-
           have "codomain_block (?Z2) = 2" by auto
           moreover have "domain_wall (?Z3) = 2" by auto
           ultimately have "domain_codomain_list ((?Z2)*(?Z3)) = [0]" 
                unfolding domain_codomain_list.simps 
                by (metis Tangles.abs_zero diagram_snd_wall_count diff_self)
           from this show ?thesis by auto
          qed
         have 2:"domain_codomain_list ((?Z2)*(?Z2)*(?Z3)) = [0,0]"           
           proof-
            have "codomain_block (?Z2) = 2" by auto
            moreover have "domain_wall ((?Z2)*(?Z3)) = 2" by auto
            ultimately  have "domain_codomain_list ((?Z2)*(?Z2)*(?Z3)) = [0,0]" 
                       unfolding domain_codomain_list.simps 
                       using 1
                       by auto
            from this show ?thesis by auto
           qed
         have "domain_codomain_list ((?Z2)*(?Z2)*(?Z2)*(?Z3)) = [0,0,0]"
          proof-
           have "codomain_block ?Z2 = 2" by auto
           moreover have "domain_wall ((?Z2)*(?Z2)*(?Z3)) = 2" by auto
           ultimately have "domain_codomain_list ((?Z2)*(?Z2)*(?Z2)*(?Z3)) = [0,0,0]" 
                     unfolding domain_codomain_list.simps 
                     using 1 2 
                     by auto
           from this show ?thesis by auto
          qed
        then have "codomain_block ?Z1 = 2" by auto
        moreover have "domain_wall ((?Z2)*(?Z2)*(?Z2)*(?Z3)) = 2" by auto
        ultimately have "domain_codomain_list ?Z = [0,0,0,0]"
                     unfolding domain_codomain_list.simps
                     using 1 2 by auto
        then show ?thesis by simp
   qed
   moreover have "domain_wall ?Z = 0" and "codomain_wall ?Z = 0" by auto
   ultimately have "well_defined ?Z" using well_defined_def list_sum_def by auto
   then show ?thesis by auto
   qed
 then have 7: "Rep_diagram (Abs_diagram ?Z) = ?Z" 
        using  Abs_Rep_well_defined by auto
 with 5 6 7 have "link_equiv (Abs_diagram ?X) (Abs_diagram ?Z)" unfolding link_equiv_def by auto
 from this show ?thesis using assms by auto
 qed

(*need to modify it slightly by adding the relevant moves for compression and proving that the above
is equal to a circle*)
end
