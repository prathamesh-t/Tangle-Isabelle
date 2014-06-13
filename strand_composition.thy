theory strand_composition
imports Comp
begin


(*new definitions*)

inductive valid::"(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> bool"
where
Nil:"valid S1 S2 []"
|dom_tuple:"((dom m, dom n) \<in> S1) \<Longrightarrow> (valid S1 S2 [(dom m, dom n)])"
|codom_tuple:"((codom m, codom n) \<in> S2) \<Longrightarrow>(valid S1 S2 [(codom m, codom n)])  "
|dom_first:"((dom m, dom n) \<in> S1)\<and>((codom n, codom k) \<in> S2)\<and>(valid S1 S2 ((codom n, codom k)#xs)) 
              \<Longrightarrow> (valid S1 S2 ((dom m, dom n)#((codom n, codom k)#xs)))"
|codom_first:"((dom n, dom k) \<in> S1)\<and>((codom m, codom n) \<in> S2)\<and>(valid S1 S2 ((dom n, dom k)#xs)) 
              \<Longrightarrow> (valid S1 S2 ((codom m, codom n)#((dom n, dom k)#xs)))"


lemma "valid {(dom (1::nat), dom 2),(dom 3, dom 4)} {(codom 2, codom 3)}  
[(dom (1::nat), dom 2),(codom (2::nat), codom 3),(dom 3, dom 4)]"
        apply(rule dom_first)
        apply(auto)
        apply(rule codom_first)
        apply(auto)
        apply(rule dom_tuple)
        apply(auto)
        done

inductive_cases codom_list[elim!]: "(valid S1 S2 [(codom m, codom n)]) "
inductive_cases dom_list[elim!]:  "(valid S1 S2 [(dom m, dom n)]) " 
inductive_cases codom_dom[elim!]: "valid S1 S2 ((codom m,codom n)#x#xs)"
inductive_cases dom_codom[elim!]: "valid S1 S2 ((dom m,dom n)#x#xs)"
inductive_cases one_element[elim!]: "valid S1 S2 (x#xs)"
inductive_cases more_than_one_element[elim!]: "valid S1 S2 (x#y#xs)"        


lemma codom_tuple_invert: "valid S1 S2 [(codom m, codom n)] \<Longrightarrow>(codom m, codom n) \<in> S2"
   apply clarify
   done

        
lemma dom_tuple_invert: "valid S1 S2 [(dom m, dom n)] \<Longrightarrow>(dom m, dom n) \<in> S1"
   apply clarify
   done 

lemma codom_dom_tuple_invert: "valid S1 S2 ([x])\<and> ((str_number (fst x) = m)\<and>(str_number (snd x) = n)) 
                                  \<Longrightarrow> ((x = (codom m, codom n))\<and>(x \<in> S2))
                                       \<or>((x = (dom m, dom n))\<and>(x \<in> S1))"
 apply clarify
 apply (rule one_element)
 apply simp
 apply auto
 apply (metis endpt.distinct(1) endpt.inject(1) endpt_reconstruction)  
 apply (metis endpt.distinct(1) endpt.inject(1) endpt_reconstruction)
 apply (metis endpt.distinct(1) endpt.inject(2) endpt_reconstruction)
 apply (metis endpt.distinct(1) endpt.inject(2) endpt_reconstruction)
 done

lemma codom_dom_list: "valid S1 S2 (x#y#xs)\<and> ((str_number (fst x) = m)\<and>(str_number (snd x) = n)) 
                                  \<Longrightarrow> ((x = (codom m, codom n))\<and>(x \<in> S2))
                                       \<or>((x = (dom m, dom n))\<and>(x \<in> S1))"
   apply clarify
   apply (rule more_than_one_element)
   apply simp
   apply (metis Diff_iff codom_dom_tuple_invert dom_tuple)
   by (metis codom_dom_tuple_invert codom_tuple)


lemma hd_valid_list:"valid S1 S2 (x#xs)\<and> ((str_number (fst x) = m)\<and>(str_number (snd x) = n)) 
                                  \<Longrightarrow> ((x = (codom m, codom n))\<and>(x \<in> S2))
                                       \<or>((x = (dom m, dom n))\<and>(x \<in> S1))"
          apply(case_tac xs)
          apply(simp add:codom_dom_tuple_invert)  
          apply clarify  
          by (metis codom_dom_list)

lemma codom_tuple_list_invert: "valid S1 S2 ((codom m, codom n)#xs) \<longrightarrow>(codom m, codom n) \<in> S2 "
   apply (induct_tac xs)
   apply (auto)
   done    

lemma dom_tuple_list_invert:"valid S1 S2 ((dom m, dom n)#xs) \<longrightarrow>(dom m, dom n) \<in> S1 "         
   apply (induct_tac xs)
   apply (auto)
   done  

lemma dom_invert:"valid S1 S2 ((dom m, dom n)#y#xs) \<longrightarrow>(dom m, dom n) \<in> S1 
                    \<and> (y = (codom n,codom (str_number (snd y))))\<and>(y \<in> S2)"         
   apply (induct_tac xs)
   apply clarify
    apply (simp)
   apply (metis endpt.distinct(1) endpt.inject(2) endpt_reconstruction)
    by (metis dom_codom endpt.distinct(1) fst_eqD hd_valid_list)


lemma codom_invert:"valid S1 S2 ((codom m, codom n)#y#xs) \<longrightarrow>(codom m, codom n) \<in> S2 
                    \<and> (y = (dom n,dom (str_number (snd y)))) \<and> (y \<in> S1)"         
   apply (induct_tac xs)
   apply clarify
   apply (simp)
   apply (metis endpt.distinct(1) endpt.inject(1) endpt_reconstruction)
   by (metis codom_dom endpt.distinct(1) fst_eqD hd_valid_list)

lemma valid_reduce_list:"valid S1 S2 (x#xs) \<longrightarrow> (valid S1 S2 xs)"
  apply(case_tac xs) 
  apply (simp add: valid.Nil)  
  apply clarify
  apply (auto simp add:codom_dom_list)
  done


lemma valid_append_list:"valid S1 S2 (xs@ys) \<longrightarrow> (valid S1 S2 ys)"
  apply(induct_tac xs) 
  apply (simp add: valid.Nil)  
  apply clarify
  apply (auto simp add: valid_reduce_list)
  done


lemma codom_first_append:
 "(valid S1 S2 (xs@[(codom m, codom n)])) \<and> (valid S1 S2 ((dom n, dom k)#ys)) 
           \<Longrightarrow> (valid S1 S2 ((xs@[(codom m, codom n)])@((dom n, dom k)#ys)))"
proof(induction xs)            
 case Nil
     have "valid S1 S2 [(codom m, codom n)]"                                        
                 using Nil valid_append_list by auto
     then have "(codom m, codom n) \<in> S2"
                 by auto
     moreover have "(dom n, dom k) \<in> S1"
                 using Nil dom_tuple_list_invert by auto
     moreover have "valid S1 S2 ((dom n,dom k)#ys)"
                 using Nil by auto 
     ultimately show ?case using valid.codom_first by auto
 next
 case (Cons x xs)
     have Con_1:"valid S1 S2 ((x#xs)@[(codom m, codom n)])"
               using Cons by auto
     then have "valid S1 S2 ([x]@(xs@[(codom m, codom n)]))"
                    using append_Cons by auto
     then have "valid S1 S2 (xs@[(codom m, codom n)])"
                     using Cons valid_append_list by metis
     moreover  have Cons_2:"valid S1 S2 ((xs@[(codom m, codom n)])@((dom n,dom k)#ys))"
                           using Cons  by (metis calculation)
    then  show ?case
           proof(cases "xs")
           case Nil
             have 01:"valid S1 S2 (x#[(codom m, codom n)])"
                        using Nil Con_1 by auto
             then have "(x = (dom (str_number (fst x)), dom (str_number (snd x))))
                                  \<or>(x = (codom (str_number (fst x)), codom (str_number (snd x))))"
                       using hd_valid_list by metis
             then have "x = (dom (str_number (fst x)), dom m)"
                          using 01 by auto
             moreover have "x \<in> S1"
                              using 01 by auto
             moreover have "(codom m, codom n) \<in> S2"
                              using 01 by auto
             ultimately have "valid S1 S2 (x#((codom m, codom n)#((dom n, dom k)#ys)))"
                       using Cons_2 append_Cons  by (metis Nil append_Nil dom_first)   
             then  show ?thesis by (metis Cons_eq_appendI Nil eq_Nil_appendI)
           next
           case (Cons a xs)
             let ?j = "str_number (fst x)"
             let ?l = "str_number (snd x)"
             have a_1:"valid S1 S2 ((x#a#xs)@[(codom m, codom n)])" 
                              using Cons by (metis Con_1)
             then have a_2:"(x = (dom ?j, dom ?l))\<or>(x = (codom ?j, codom ?l))"
                          using hd_valid_list by (metis Cons_eq_appendI)
             then show ?thesis
                    proof(cases "x =  (dom ?j, dom ?l) ")
                      case True
                      have T_1:"valid S1 S2 ((dom ?j, dom ?l)#a#(xs@[(codom m, codom n)]))"
                                   using a_1 True by auto
                      then have T_2:"((dom ?j, dom ?l) \<in> S1)
                                 \<and>(a = (codom ?l, codom (str_number (snd a))))
                                 \<and>(a \<in> S2)  "
                           using dom_invert by auto     
                      then have T_3: " (codom ?l, codom (str_number (snd a))) \<in> S2"
                                            by auto
                      moreover have T_4:"valid S1 S2 ((codom ?l, codom (str_number (snd a)))#(xs@[(codom m, codom n)]@((dom n, dom k)#ys)))"
                                 using Cons_2 Cons T_2 by auto
                      ultimately have "valid S1 S2 ((dom ?j, dom ?l)#(codom ?l, codom (str_number (snd a)))
                                  #(xs@[(codom m, codom n)]@((dom n, dom k)#ys)))"
                                   using dom_first by (metis T_2)  
                      then have "valid S1 S2 (x#(a#(xs@[(codom m, codom n)]@((dom n, dom k)#ys))))"
                                            using T_2 True by auto
                      then show ?thesis using append_Cons by (metis (mono_tags) Cons append_assoc)                          
                    next
                    case False
                      have F_1:"x= (codom ?j, codom ?l)"
                                using False a_2 by auto
                      then have F_2:"valid S1 S2 ((codom  ?j, codom  ?l)#a#(xs@[(codom   m, codom   n)]))"
                                   using a_1 by auto
                      then have T_2:"((codom  ?j, codom  ?l) \<in> S2)
                                 \<and>(a = (dom   ?l, dom   (str_number (snd a))))
                                 \<and>(a \<in> S1)  "
                           using codom_invert by auto     
                      then have T_3: " (dom ?l, dom (str_number (snd a))) \<in> S1"
                                            by auto
                      moreover have T_4:"valid S1 S2 ((dom   ?l, dom   (str_number (snd a)))
                                #(xs@[(codom m,codom n)]@((dom  n, dom  k)#ys)))"
                                 using Cons_2 Cons T_2 by auto
                      ultimately have "valid S1 S2 ((codom  ?j, codom  ?l)#(dom ?l, dom (str_number (snd a)))
                                  #(xs@[(codom m,codom n)]@((dom n,dom k)#ys)))"
                                   using codom_first by (metis T_2)  
                      then have "valid S1 S2 (x#(a#(xs@[(codom m, codom n)]@((dom n, dom k)#ys))))"
                                         by (metis F_1 T_2)
                      then show ?thesis using append_Cons by (metis (mono_tags) Cons append_assoc)  
                    qed
            qed
 qed


lemma dom_first_append:
 "(valid S1 S2 (xs@[(dom m, dom n)])) \<and> (valid S1 S2 ((codom n, codom k)#ys)) 
           \<Longrightarrow> (valid S1 S2 ((xs@[(dom m, dom n)])@((codom n, codom k)#ys)))"
proof(induction xs)            
 case Nil
     have "valid S1 S2 [(dom m, dom n)]"                                        
                 using Nil valid_append_list by auto
     then have "(dom m, dom n) \<in> S1"
                 by auto
     moreover have "(codom n, codom k) \<in> S2"
                 using Nil codom_tuple_list_invert by auto
     moreover have "valid S1 S2 ((codom n,codom k)#ys)"
                 using Nil by auto 
     ultimately show ?case using valid.dom_first by auto
 next
 case (Cons x xs)
     have Con_1:"valid S1 S2 ((x#xs)@[(dom m, dom n)])"
               using Cons by auto
     then have "valid S1 S2 ([x]@(xs@[(dom m, dom n)]))"
                    using append_Cons by auto
     then have "valid S1 S2 (xs@[(dom m, dom n)])"
                     using Cons valid_append_list by metis
     moreover  have Cons_2:"valid S1 S2 ((xs@[(dom m, dom n)])@((codom n,codom k)#ys))"
                           using Cons  by (metis calculation)
    then  show ?case
           proof(cases "xs")
           case Nil
             have 01:"valid S1 S2 (x#[(dom m, dom n)])"
                        using Nil Con_1 by auto
             then have "(x = (codom (str_number (fst x)), codom (str_number (snd x))))
                                  \<or>(x = (dom (str_number (fst x)), dom (str_number (snd x))))"
                       using hd_valid_list by metis
             then have "x = (codom (str_number (fst x)), codom m)"
                          using 01 by auto
             moreover have "x \<in> S2"
                              using 01 by auto
             moreover have "(dom m, dom n) \<in> S1"
                              using 01 by auto
             ultimately have "valid S1 S2 (x#((dom m, dom n)#((codom n, codom k)#ys)))"
                       using Cons_2 append_Cons  by (metis Nil append_Nil codom_first)   
             then  show ?thesis by (metis Cons_eq_appendI Nil eq_Nil_appendI)
           next
           case (Cons a xs)
             let ?j = "str_number (fst x)"
             let ?l = "str_number (snd x)"
             have a_1:"valid S1 S2 ((x#a#xs)@[(dom m, dom n)])" 
                              using Cons by (metis Con_1)
             then have a_2:"(x = (codom ?j, codom ?l))\<or>(x = (dom ?j, dom ?l))"
                          using hd_valid_list by (metis Cons_eq_appendI)
             then show ?thesis
                    proof(cases "x =  (codom ?j, codom ?l) ")
                      case True
                      have T_1:"valid S1 S2 ((codom ?j, codom ?l)#a#(xs@[(dom m, dom n)]))"
                                   using a_1 True by auto
                      then have T_2:"((codom ?j, codom ?l) \<in> S2)
                                 \<and>(a = (dom ?l, dom (str_number (snd a))))
                                 \<and>(a \<in> S1)  "
                           using codom_invert by auto     
                      then have T_3: " (dom ?l, dom (str_number (snd a))) \<in> S1"
                                            by auto
                      moreover have T_4:"valid S1 S2 ((dom ?l, dom (str_number (snd a)))#(xs@[(dom m, dom n)]@((codom n, codom k)#ys)))"
                                 using Cons_2 Cons T_2 by auto
                      ultimately have "valid S1 S2 ((codom ?j, codom ?l)#(dom ?l, dom (str_number (snd a)))
                                  #(xs@[(dom m, dom n)]@((codom n, codom k)#ys)))"
                                   using codom_first by (metis T_2)  
                      then have "valid S1 S2 (x#(a#(xs@[(dom m, dom n)]@((codom n, codom k)#ys))))"
                                            using T_2 True by auto
                      then show ?thesis using append_Cons by (metis (mono_tags) Cons append_assoc)                          
                    next
                    case False
                      have F_1:"x= (dom ?j, dom ?l)"
                                using False a_2 by auto
                      then have F_2:"valid S1 S2 ((dom  ?j, dom  ?l)#a#(xs@[(dom   m, dom   n)]))"
                                   using a_1 by auto
                      then have T_2:"((dom  ?j, dom  ?l) \<in> S1)
                                 \<and>(a = (codom   ?l, codom   (str_number (snd a))))
                                 \<and>(a \<in> S2)  "
                           using dom_invert by auto     
                      then have T_3: " (codom ?l, codom (str_number (snd a))) \<in> S2"
                                            by auto
                      moreover have T_4:"valid S1 S2 ((codom   ?l, codom   (str_number (snd a)))
                                #(xs@[(dom m,dom n)]@((codom  n, codom  k)#ys)))"
                                 using Cons_2 Cons T_2 by auto
                      ultimately have "valid S1 S2 ((dom  ?j, dom  ?l)#(codom ?l, codom (str_number (snd a)))
                                  #(xs@[(dom m,dom n)]@((codom n,codom k)#ys)))"
                                   using dom_first by (metis T_2)  
                      then have "valid S1 S2 (x#(a#(xs@[(dom m, dom n)]@((codom n, codom k)#ys))))"
                                         by (metis F_1 T_2)
                      then show ?thesis using append_Cons by (metis (mono_tags) Cons append_assoc)  
                    qed
            qed
 qed


primrec rev_tuple::"(endpt \<times> endpt) list  \<Rightarrow> (endpt \<times> endpt) list"
where
"rev_tuple [] = []"
|"rev_tuple (x#xs) = (snd x, fst x)#(rev_tuple xs)"



definition rev_list::"(endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"rev_list ls = (rev (rev_tuple ls))" 


lemma rev_tuple_append:"rev_tuple (xs@ys) \<equiv> (rev_tuple xs)@(rev_tuple ys)"
       apply(induction  xs)
       apply(auto simp add:rev_tuple_def)
       done   

lemma rev_append:"rev (xs@ys) = (rev ys)@(rev xs)"
            by (metis rev_append) 

lemma rev_list_append:"rev_list (xs@ys) = (rev_list ys)@(rev_list xs)"
          apply (simp add:rev_list_def rev_tuple_append)
          done

lemma valid_rev_list: assumes "symmetric S1" and "symmetric S2"
shows "valid S1 S2 ls \<Longrightarrow> valid S1 S2 (rev_list ls)"
proof(induction ls)
 case Nil
      show ?case using Nil rev_list_def rev_def valid.Nil by auto
 next
 case (Cons l ls)
  let ?m = "str_number (fst l)"
  let ?n = "str_number (snd l)"
  have Cons_1:"valid S1 S2 (l#ls)"
           using Cons by auto
  then have Cons_2:"((l = (codom ?m, codom ?n))\<and>(l \<in> S2))\<or>((l = (dom ?m, dom ?n))\<and>(l \<in> S1)) "
          using hd_valid_list by metis
  also have Cons_3:"valid S1 S2 ls"
                    using Cons_1 valid_reduce_list by auto 
  then have Cons_4:"valid S1 S2 (rev_list ls)"
                   using  Cons.IH by auto 
  then show ?case
       proof(cases ls)
        case Nil
            have "rev_list [l] = [(snd l, fst l)]"
                     using rev_list_def rev_tuple.simps by auto
            then have "(l = (codom ?m, codom ?n)) \<Longrightarrow> (snd l, fst l) \<in> S2"
                          using Cons_2 assms(2) symmetric_def 
                   by (metis endpt.distinct(1) fst_conv pair_collapse)             
            moreover then  have "l = (dom ?m, dom ?n) \<Longrightarrow> (snd l, fst l) \<in> S1"
                                        using Cons_2 assms(2) symmetric_def
                  by (metis assms(1) endpt.distinct(1) fst_conv pair_collapse)
            ultimately show ?thesis using Nil  codom_tuple dom_tuple Cons_2  by (metis `rev_list [l] = [(snd l, fst l)]` fst_eqD snd_eqD)
        next
        case (Cons l1 ls1)
           show ?thesis
             proof(cases "l =  (codom ?m, codom ?n)")
             case True
                 have T_1:"l \<in> S2"
                       using Cons_2 True by (metis endpt.distinct(1) fst_conv) 
                 moreover have T_2:"valid S1 S2 (l#l1#ls1)"
                                using Cons_1  Cons by auto 
                 then have T_3:"valid S1 S2 ((codom ?m, codom ?n)#l1#ls1)"
                                  using True by auto
                 then have T_4:"l1 = (dom ?n, dom (str_number (snd l1)))\<and> l1 \<in> S1"
                       using  codom_invert True by metis      
                 then have T_5:"(l1#ls1) = [l1]@ls1 "
                                     using rev.simps by auto 
                 then have T_6:"rev_list ([l1]@ls1) = (rev_list ls1)@(rev_list [l1])"
                                 using rev_list_append by metis
                 moreover have "rev_tuple [l1] =[(dom (str_number (snd l1)) ,dom ?n)]"
                                       using rev_tuple.simps snd_conv fst_conv 
                                        T_4 by metis
                 moreover have "rev_list [l1] = [(dom (str_number (snd l1)) ,dom ?n)]"
                                        using rev_list_def rev.simps  singleton_rev_conv
                                        by (metis calculation(3))
                 then have "rev_list ([l1]@ls1) = 
                              (rev_list ls1)@[(dom (str_number (snd l1)) ,dom ?n)] "
                                 using T_6 by auto  
                 then have T_7:"rev_list (l1#ls1) = (rev_list ls1)@[(dom (str_number (snd l1)) ,dom ?n)]"
                                       by auto
                 have "valid S1 S2 (rev_list (l1#ls1))"
                                       using Cons_4 Cons by auto
                 then have T_8:"valid S1 S2 ((rev_list ls1)@[(dom (str_number (snd l1)) ,dom ?n)])" 
                                 using T_7 by auto
                  have "(codom ?n, codom ?m) \<in> S2"
                               using symmetric_def assms(2) by (metis T_1 True)   
                  moreover have "valid S1 S2 ((codom ?n, codom ?m)#[])"
                                          using codom_tuple by (metis calculation(4))
                  then have T_9:"valid S1 S2
                               (((rev_list ls1)@[(dom (str_number (snd l1)) ,dom ?n)])
                                   @[(codom ?n, codom ?m)])"
                                        using dom_first_append T_8 by auto 
                  have "rev_list [(codom ?m, codom ?n)] =  [(codom ?n, codom ?m)]"
                             using rev_list_def rev_tuple.simps by auto
                  moreover have "l#l1#ls1 = [l]@[l1]@ls1"
                                    using append_Cons by auto
                  moreover have "rev_list ([l]@[l1]@ls1) = (rev_list ([l1]@ls1))@(rev_list [l])"
                                     using rev_list_append by metis
                  ultimately have "rev_list (l#l1#ls1) = (((rev_list ls1)@[(dom (str_number (snd l1)) ,dom ?n)])
                                   @[(codom ?n, codom ?m)])" 
                                     using T_7 by (metis True `rev_list [l1] = [(endpt.dom (str_number (snd l1)), endpt.dom (str_number (snd l)))]`)
                  then have "valid S1 S2 (rev_list (l#l1#ls1))"
                                  using T_9 by auto
                  then show ?thesis using Cons by auto
                 next
                 case False
                      have F_1:"l = (dom ?m, dom ?n) \<and> l \<in> S1"
                              using False Cons_2 by auto 
                       moreover have F_2:"valid S1 S2 (l#l1#ls1)"
                                using Cons_1  Cons by auto 
                 then have F_3:"valid S1 S2 ((dom ?m, dom ?n)#l1#ls1)"
                                  using F_1 by auto
                 then have F_4:"l1 = (codom ?n, codom (str_number (snd l1)))\<and> l1 \<in> S2"
                       using  dom_invert F_1 by metis      
                 then have F_5:"(l1#ls1) = [l1]@ls1 "
                                     using rev.simps by auto 
                 then have F_6:"rev_list ([l1]@ls1) = (rev_list ls1)@(rev_list [l1])"
                                 using rev_list_append by metis
                 moreover have "rev_tuple [l1] =[(codom (str_number (snd l1)) ,codom ?n)]"
                                       using rev_tuple.simps snd_conv fst_conv 
                                        F_4 by metis
                 moreover have "rev_list [l1] = [(codom (str_number (snd l1)) ,codom ?n)]"
                                        using rev_list_def rev.simps  singleton_rev_conv
                                        by (metis calculation(3))
                 then have "rev_list ([l1]@ls1) = 
                              (rev_list ls1)@[(codom (str_number (snd l1)) ,codom ?n)] "
                                 using F_6 by auto  
                 then have F_7:"rev_list (l1#ls1) = (rev_list ls1)@[(codom (str_number (snd l1)) ,codom ?n)]"
                                       by auto
                 have "valid S1 S2 (rev_list (l1#ls1))"
                                       using Cons_4 Cons by auto
                 then have F_8:"valid S1 S2 ((rev_list ls1)@[(codom (str_number (snd l1)) ,codom ?n)])" 
                                 using F_7 by auto
                  have "(dom ?n, dom ?m) \<in> S1"
                               using symmetric_def assms(2) by (metis F_1 assms(1))   
                  moreover have "valid S1 S2 ((dom ?n, dom ?m)#[])"
                                          using dom_tuple by (metis calculation(4))
                  then have F_9:"valid S1 S2
                               (((rev_list ls1)@[(codom (str_number (snd l1)) ,codom ?n)])
                                   @[(dom ?n, dom ?m)])"
                                        using codom_first_append F_8 by auto 
                  have "rev_list [(dom ?m, dom ?n)] =  [(dom ?n, dom ?m)]"
                             using rev_list_def rev_tuple.simps by auto
                  moreover have "l#l1#ls1 = [l]@[l1]@ls1"
                                    using append_Cons by auto
                  moreover have "rev_list ([l]@[l1]@ls1) = (rev_list ([l1]@ls1))@(rev_list [l])"
                                     using rev_list_append by metis
                  ultimately have "rev_list (l#l1#ls1) = (((rev_list ls1)@[(codom (str_number (snd l1)) ,codom ?n)])
                                   @[(dom ?n, dom ?m)])" 
                                     using F_7 by (metis F_1 `rev_list [l1] = [(endpt.codom (str_number (snd l1)), endpt.codom (str_number (snd l)))]`)
                  then have "valid S1 S2 (rev_list (l#l1#ls1))"
                                  using F_9 by auto
                  then show ?thesis using Cons by auto     
                qed
             qed     
 qed


inductive compose_strands::"(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) \<Rightarrow> bool"
where
1:"(codom m, codom n) \<in> S1 \<Longrightarrow>(compose_strands S1 S2  (codom m, codom n))"
|2:"(dom m, dom n) \<in> S2  \<Longrightarrow>  (compose_strands S1 S2 (dom m, dom n) )"
|3:" ((codom m, dom k1) \<in> S1) \<and>((dom k4, codom n) \<in> S1)
                                  \<and>(valid S1 S2 ((codom k1,codom k2)#ls@[(codom k3, codom k4)]))
                          \<Longrightarrow> (compose_strands S1 S2 (codom m, codom n))"
|4:" ((dom m, codom k1) \<in> S2) \<and>((codom k4, dom n) \<in> S2)
                                  \<and>(valid S1 S2 ((dom k1,dom k2)#ls@[(dom k3, dom k4)]))
                          \<Longrightarrow> (compose_strands S1 S2 (dom m, dom n))"
|5:" ((codom m, dom k1) \<in> S1) \<and>((codom k4, dom n) \<in> S2)
                                  \<and>(valid S1 S2 ((codom k1,codom k2)#ls@[(dom k3, dom k4)]))
                          \<Longrightarrow> (compose_strands S1 S2 (codom m, dom n))"
|6:" ((codom n, dom k1) \<in> S1)\<and>((codom k4, dom m) \<in> S2)
                      \<and>(valid S1 S2 ((codom k1,codom k2)#ls@[(dom k3, dom k4)]))
                          \<Longrightarrow> (compose_strands S1 S2 (dom m, codom n))"
|7:"(((codom m, dom k) \<in> S1) \<and>((codom k, dom n) \<in> S2))\<Longrightarrow> (compose_strands S1 S2 (codom m, dom n))"
|8:" (((codom m, dom k) \<in> S1) \<and>((codom k, dom n) \<in> S2))\<Longrightarrow> (compose_strands S1 S2 (dom n, codom m))"               
  

definition strand_composition::"(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set"
where
"strand_composition S1 S2 \<equiv> {x. (compose_strands S1 S2 x)}"



lemma co_in: assumes "symmetric S1"
shows "(codom m, codom n) \<in> S1 \<Longrightarrow> (compose_strands S1 S2 (codom n, codom m))"
using 1 assms symmetric_def by metis

lemma do_in: assumes "symmetric S2"
shows "(dom m, dom n) \<in> S2 \<Longrightarrow> (compose_strands S1 S2 (dom n, dom m))"
using 2 assms symmetric_def by metis

lemma codom_tuple_connected_symmetric:
 assumes "symmetric S1" and "symmetric S2"
shows " ((codom m, dom k1) \<in> S1) \<and>((dom k4, codom n) \<in> S1)
                                  \<and>(valid S1 S2 ((codom k1,codom k2)#ls@[(codom k3, codom k4)])) 
                \<Longrightarrow> (compose_strands S1 S2 (codom n, codom m))"
proof-
 assume 0:"((codom m, dom k1) \<in> S1) \<and>((dom k4, codom n) \<in> S1)
                                  \<and>(valid S1 S2 ((codom k1,codom k2)#ls@[(codom k3, codom k4)])) "
 have "rev_list [(codom k3, codom k4)] = [(codom k4, codom k3)]"
                using rev_list_def rev_tuple.simps fst_conv snd_conv by auto
 then have "rev_list ((codom k1,codom k2)#ls@[(codom k3, codom k4)])
                 = [(codom k4, codom k3)]@(rev_list ((codom k1, codom k2)#ls))"
               using rev_list_append  append_Cons by (metis)
 then have "... = [(codom k4, codom k3)]@(rev_list ([(codom k1, codom k2)]@ls))"
               using append_Cons by auto
 then have "... = [(codom k4, codom k3)]@((rev_list ls)@(rev_list [(codom k1, codom k2)]))"
                       using rev_list_append append_Cons by metis
 then have "... = [(codom k4, codom k3)]@((rev_list ls)@[(codom k2, codom k1)])"
                           using rev_list_def rev_tuple.simps fst_conv snd_conv by auto
 then have 1:"... = (codom k4, codom k3)#((rev_list ls)@[(codom k2, codom k1)])"
                  using append_Cons by auto
 then  have 2:"valid S1 S2 (...)"
             using 0 valid_rev_list assms by (metis Cons_eq_appendI `[(codom k4, codom k3)] @ rev_list ([(codom k1, codom k2)] @ ls) = [(codom k4, codom k3)] @ rev_list ls @ rev_list [(codom k1, codom k2)]` `[(codom k4, codom k3)] @ rev_list ls @ rev_list [(codom k1, codom k2)] = [(codom k4, codom k3)] @ rev_list ls @ [(codom k2, codom k1)]` `rev_list ((codom k1, codom k2) # ls @ [(codom k3, codom k4)]) = [(codom k4, codom k3)] @ rev_list ((codom k1, codom k2) # ls)` eq_Nil_appendI)
 moreover have "((codom n, dom k4) \<in> S1) \<and>((dom k1, codom m) \<in> S1)"
                    using 0 assms symmetric_def by metis
 then have "compose_strands S1 S2 (codom n, codom m)"
                 using 3 by (metis calculation)           
 then show ?thesis using 0 by auto
qed

lemma dom_tuple_connected_symmetric:
 assumes "symmetric S1" and "symmetric S2"
shows " ((dom m, codom k1) \<in> S2) \<and>((codom k4, dom n) \<in> S2)
                                  \<and>(valid S1 S2 ((dom k1,dom k2)#ls@[(dom k3, dom k4)])) 
                \<Longrightarrow> (compose_strands S1 S2 (dom n, dom m))"
proof-
 assume 0:"((dom m, codom k1) \<in> S2) \<and>((codom k4, dom n) \<in> S2)
                                  \<and>(valid S1 S2 ((dom k1,dom k2)#ls@[(dom k3, dom k4)])) "
 have "rev_list [(dom k3, dom k4)] = [(dom k4, dom k3)]"
                using rev_list_def rev_tuple.simps fst_conv snd_conv by auto
 then have "rev_list ((dom k1,dom k2)#ls@[(dom k3, dom k4)])
                 = [(dom k4, dom k3)]@(rev_list ((dom k1, dom k2)#ls))"
               using rev_list_append  append_Cons by (metis)
 then have "... = [(dom k4, dom k3)]@(rev_list ([(dom k1, dom k2)]@ls))"
               using append_Cons by auto
 then have "... = [(dom k4, dom k3)]@((rev_list ls)@(rev_list [(dom k1, dom k2)]))"
                       using rev_list_append append_Cons by metis
 then have "... = [(dom k4, dom k3)]@((rev_list ls)@[(dom k2, dom k1)])"
                           using rev_list_def rev_tuple.simps fst_conv snd_conv by auto
 then have 1:"... = (dom k4, dom k3)#((rev_list ls)@[(dom k2, dom k1)])"
                  using append_Cons by auto
 then  have 2:"valid S1 S2 (...)"
             using 0 valid_rev_list assms by (metis Cons_eq_appendI `[(dom k4, dom k3)] @ rev_list ([(dom k1, dom k2)] @ ls) = [(dom k4, dom k3)] @ rev_list ls @ rev_list [(dom k1, dom k2)]` `[(dom k4, dom k3)] @ rev_list ls @ rev_list [(dom k1, dom k2)] = [(dom k4, dom k3)] @ rev_list ls @ [(dom k2, dom k1)]` `rev_list ((dom k1, dom k2) # ls @ [(dom k3, dom k4)]) = [(dom k4, dom k3)] @ rev_list ((dom k1, dom k2) # ls)` eq_Nil_appendI)
 moreover have "((dom n, codom k4) \<in> S2) \<and>((codom k1, dom m) \<in> S2)"
                    using 0 assms symmetric_def by metis
 ultimately have "compose_strands S1 S2 (dom n, dom m)"
                using 4 by metis 
 then show ?thesis using 0 by auto
qed

lemma codom_dom_connected_symmetric:
 assumes "symmetric S1" and "symmetric S2"
shows " ((codom m, dom k1) \<in> S1) \<and>((codom k4, dom n) \<in> S2)
                                  \<and>(valid S1 S2 ((codom k1,codom k2)#ls@[(dom k3, dom k4)])) 
                \<Longrightarrow> (compose_strands S1 S2 (dom n, codom m))"
       using 6 by metis


lemma dom_codom_connected_symmetric:
 assumes "symmetric S1" and "symmetric S2"
shows " ((codom m, dom k1) \<in> S1) \<and>((codom k4, dom n) \<in> S2)
                                  \<and>(valid S1 S2 ((codom k1,codom k2)#ls@[(dom k3, dom k4)])) 
                \<Longrightarrow> (compose_strands S1 S2 (codom m, dom n))"
       using 5 by metis


lemma symmetric_compose_strands:
assumes "symmetric S1" and "symmetric S2"
shows
 "compose_strands S1 S2 (x,y) \<Longrightarrow> compose_strands S1 S2 (y, x)"
 proof(induction rule:compose_strands.cases)
 case 1
   show ?thesis using 1 co_in assms by auto
 next
 case 2
  show ?thesis using 2 do_in assms by auto
 next
 case 3
  show ?thesis using 3 codom_tuple_connected_symmetric assms by auto
 next
 case 4
  show ?thesis using 4 dom_tuple_connected_symmetric assms by auto
 next
 case 5
  show ?thesis using 5 codom_dom_connected_symmetric assms by auto
 next
 case 6
  show ?thesis using 6 dom_codom_connected_symmetric assms by auto
 next
 case 7
  show ?thesis using 7 8 by auto
 next
 case 8
  show ?thesis using 7 8 by auto
 qed        

theorem assumes "symmetric S1" and "symmetric S2"
   shows "symmetric (strand_composition S1 S2)"
       using strand_composition_def assms symmetric_compose_strands  mem_Collect_eq symmetric_def
           by (metis)


theorem assumes "symmetric S1" and "symmetric S2"
          shows "symmetric (endpt_act S1 S2)"


(*now to prove other properties *)





(*
lemma codom_tuple_endpt_act:"(codom m , codom n) \<in> endpt_act xs ys \<and> (codom m, codom n) \<notin> xs 
                       \<Longrightarrow> (\<exists>k1 k2 ls. (((codom m, dom k1) \<in> xs)
                                            \<and>(fst (hd ls) = (codom k1)) 
                                            \<and>(snd (last ls) = (codom k2)) 
                                            \<and>((dom k2, codom n) \<in> xs))
                                            \<and>(alt_list xs ys ls)
                                            \<and>(ascending_list ls))"
                 using endpt_act_def by auto
*)
lemma "A \<subset> B \<and>(finite B) \<Longrightarrow> (finite A)"
       using  rev_finite_subset by auto
(*
lemma "finite xs \<Longrightarrow> finite ( {(codom m, codom n) | m n.(codom m, codom n) \<in> xs} )"
           using rev_finite_subset by auto
lemma "finite xs \<Longrightarrow> finite ( {(dom m, dom n) | m n.(dom m, dom n) \<in> xs} )"
           using rev_finite_subset by auto

lemma "finite S \<Longrightarrow> finite {x. ((x,y) \<in> S)\<or>((y,x)\<in>S)}"
 proof(induction rule:finite.induct) 
    have "finite {}" by auto        
    then show "finite {x. (x,y) \<in> {}\<or>((y,x)\<in>{})}" using finite.simps by auto       
 next 
  fix a and A

assume IH:"finite A \<Longrightarrow> finite {x. ((x,y) \<in> A)\<or>((y,x)\<in>A)}"
 and prems:"finite A"
then have " finite {x. ((x,y) \<in> (insert a A))\<or>((y,x)\<in>(insert a A))}"
     proof-
     have " {x. ((x,y) \<in> (insert a A))\<or>((y,x)\<in>(insert a A))} 
                  =  {x. ((x,y) \<in> A)\<or>((y,x)\<in>A)} \<union> {fst a, snd a}"
         proof-
                using insert_def fst_conv snd_conv sledgehammer
    
*)


(*this will be used to prove properties of the ls obtained by choice operator*)
(*

definition connecting_list::"(endpt \<times> endpt) \<Rightarrow>(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set 
                                            \<Rightarrow>(endpt \<times> endpt) list \<Rightarrow> bool"
where
"connecting_list a xs ys ls \<equiv>  (\<exists>k1 k2.((((fst a), dom k1) \<in> xs)
                                            \<and>(fst (hd ls) = (codom k1)) 
                                            \<and>(snd (last ls) = (codom k2)) 
                                            \<and>((dom k2, (snd a)) \<in> xs)
                                            \<and>(alt_list xs ys ls)
                                            \<and>(ascending_list ls)\<and>(ls \<noteq>[])))"

lemma connecting_list_implies_belongs_to:
 "(connecting_list a xs ys ls) \<and> (codom_tuple a) \<Longrightarrow> a \<in> endpt_act xs ys"
proof-
 assume 0:"(connecting_list a xs ys ls) \<and> (codom_tuple a)"
 have "\<exists>m n.(a = (codom m, codom n))"
            using codom_tuple_def type_def  0 
            by (metis (mono_tags) endpt.distinct(1) endpt.exhaust endpt_reconstruction 
                endtype.distinct(1) fst_conv pair_collapse prod_case_beta snd_conv split_Pair 
                str_number_def)
 then obtain m n where "a = (codom m, codom n)" by auto 
 then have " \<exists>k1 k2.((((codom m), dom k1) \<in> xs)
                                            \<and>(fst (hd ls) = (codom k1)) 
                                            \<and>(snd (last ls) = (codom k2)) 
                                            \<and>((dom k2, (codom n)) \<in> xs)
                                            \<and>(alt_list xs ys ls)
                                            \<and>(ascending_list ls)\<and>(ls \<noteq> [])) "
             using fst_conv snd_conv 0 unfolding connecting_list_def  
             by (metis (full_types))
 then have "(codom m, codom n) \<in> (endpt_act xs ys)"
             using endpt_act_def by auto
 then show ?thesis using 0 `a = (codom m, codom n)` 
             by auto 
qed

lemma existence_of_connecting_list:
 "(codom_tuple a)\<and>(a \<in> (endpt_act xs ys))\<and>( a \<notin> xs) \<Longrightarrow> \<exists>ls.(connecting_list a xs ys ls)"
 proof-
 assume 0:"(codom_tuple a)\<and>(a \<in> (endpt_act xs ys))\<and>( a \<notin> xs)"
  have "\<exists>m n.(a = (codom m, codom n))"
            using codom_tuple_def type_def  0 
            by (metis (mono_tags) endpt.distinct(1) endpt.exhaust endpt_reconstruction 
                endtype.distinct(1) fst_conv pair_collapse prod_case_beta snd_conv split_Pair 
                str_number_def)
 then obtain m n where "a = (codom m, codom n)" by auto 
 then have " \<exists>ls k1 k2.((((codom m), dom k1) \<in> xs)
                                            \<and>(fst (hd ls) = (codom k1)) 
                                            \<and>(snd (last ls) = (codom k2)) 
                                            \<and>((dom k2, (codom n)) \<in> xs)
                                            \<and>(alt_list xs ys ls)
                                            \<and>(ascending_list ls)\<and>(ls \<noteq> [])) "
             using fst_conv snd_conv 0 unfolding endpt_act_def by auto
 then obtain ls where "\<exists>k1 k2.((((codom m), dom k1) \<in> xs)
                                            \<and>(fst (hd ls) = (codom k1)) 
                                            \<and>(snd (last ls) = (codom k2)) 
                                            \<and>((dom k2, (codom n)) \<in> xs)
                                            \<and>(alt_list xs ys ls)
                                            \<and>(ascending_list ls)\<and>(ls \<noteq> [])) "
                      by auto
 then have "connecting_list a xs ys ls"
                 unfolding connecting_list_def by (metis `a = (codom m, codom n)` fst_conv snd_conv)
 then show ?thesis using 0 by auto
qed

(* we obtain a list associated to a given codom_tuple *)
definition assign_list::"(endpt \<times> endpt) \<Rightarrow> (endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set 
                            \<Rightarrow> (endpt \<times> endpt) list "
where
"assign_list a xs ys \<equiv> 
 ( if ((codom_tuple a)\<and>(a \<in> (endpt_act xs ys))\<and>( a \<notin> xs)) 
              then (SOME (ls::(endpt \<times> endpt) list).(connecting_list a xs ys ls)) 
              else [])"


(*lemma about assign_list*)
lemma assign_list_not_empty:"((codom_tuple a)\<and>(a \<in> (endpt_act xs ys))\<and>( a \<notin> xs)) 
             \<Longrightarrow> (assign_list a xs ys) \<noteq> []" 
    using assign_list_def existence_of_connecting_list connecting_list_def someI
                  by (metis (full_types))

lemma assign_list_empty_cond:"((codom_tuple a)\<and>(a \<in> (endpt_act xs ys))\<and>(assign_list a xs ys = []) 
                                       \<Longrightarrow>( a \<in> xs))"
        using assign_list_not_empty by blast

(*assigning end points of a component*)

primrec check_start_block::"(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set 
                                    \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> bool"
where
"check_start_block xs ys [] = True"
|"check_start_block xs ys (l#ls) = (if (check_start_block xs ys ls = False) 
                                 then False
                                 else (assign_list l xs ys = []))"


primrec reduce::"(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set 
                                    \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where 
"reduce S1 S2 [] = []"
|"reduce S1 S2 (l#ls) = (if (check_start_block S1 S2 (l#ls) = False) 
                        then (reduce S1 S2 ls)
                         else (l#ls))"

(*It would be better to chuck this approach*)
(*
primrec assign_start_list::"(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set 
                             \<Rightarrow>(endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"assign_start_list S1 S2 [] = []"
|"assign_start_list S1 S2 (l#ls) = (if (assign_list l ls \<noteq> []) 
  *)                                     
definition assign_end_points::"(endpt \<times> endpt) \<Rightarrow> (endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set
                 \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt)"
where
"assign_end_points a xs ys ls  \<equiv> (SOME x.((((fst a), fst x) \<in> xs)
                                            \<and>(dom_tuple x)
                                            \<and>(fst (hd ls) = (codom (str_number (fst x)))) 
                                            \<and>(snd (last ls) = (codom (str_number (snd x)))) 
                                            \<and>(snd x, (snd a)) \<in> xs))"


primrec list_transfer::"(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set
                 \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow>  (endpt \<times> endpt) list"
where
"list_transfer   S1 S2 []= []"
|"list_transfer  S1 S2 (x#xs) = (if (assign_list x S1 S2 \<noteq> [])
                                  then (assign_list x S1 S2)@
                                       ((dom (str_number (snd (last (assign_list x S1 S2))))
                                        ,dom (str_number (fst (hd (list_transfer S1 S2 xs))))) 
                                        #(list_transfer S1 S2 xs))
                                    else (list_transfer S1 S2 xs))"





lemma assign_list_ascending:"ascending_list (assign_list a xs ys)"
 proof(cases "((codom_tuple a)\<and>(a \<in> (endpt_act xs ys))\<and>( a \<notin> xs))")
 case False
   have "(assign_list a xs ys) = []"
                  using False assign_list_def by auto
   then show ?thesis by auto
 next
 case True
   have "(assign_list a xs ys) \<noteq> []"
                   using True assign_list_not_empty by auto 
   then have "connecting_list a xs ys (assign_list a xs ys)"
                using someI by (metis (full_types) assign_list_def existence_of_connecting_list)
   then show ?thesis unfolding connecting_list_def by auto
qed 

lemma ascending_list_recursion:"ascending_list (l#ls) \<longrightarrow> ascending_list ls"
     apply(induct_tac ls)
     apply(auto)
     done

lemma ascending_list_transfer:
 "ascending_list ls \<Longrightarrow> ascending_list (list_transfer S1 S2 ls)"
proof(induction ls)
 case Nil
   show ?case using ascending_list_def by auto
 next
 case (Cons l ls)
  let ?l1 = "dom (str_number (snd (last (assign_list l S1 S2))))"
  let ?l2 = "dom (str_number (fst (hd (list_transfer S1 S2 ls))))"
  have "ascending_list (l#ls)"
                using Cons by auto
  then have "ascending_list ls"
               using ascending_list_recursion by blast
  then have 1:"ascending_list (list_transfer S1 S2 ls)"
               using Cons  by auto
 show ?case
   proof(cases "assign_list l S1 S2 = []")
   case True
     have "(list_transfer S1 S2 (l#ls)) = (list_transfer S1 S2 ls)"
                   using list_transfer.simps(2) True by auto
     then show ?thesis using 1 by auto
  next
  case False
     have "str_number ?l2 = str_number (fst (hd (list_transfer S1 S2 ls)))"
                 using str_number_def type_def by auto
     then have False_1:"ascending_list ((?l1, ?l2)#(list_transfer S1 S2 ls))"
                     using ascending_list.simps(2) 1 by auto
      moreover have "ascending_list (assign_list l S1 S2)"
                      using assign_list_ascending by auto
      moreover have "(str_number ?l1) = str_number (snd (last (assign_list l S1 S2)))"
                       using str_number_def type_def by auto
      ultimately have "ascending_list ((assign_list l S1 S2)@((?l1, ?l2)#(list_transfer S1 S2 ls)))"
                         using ascending_list_append by auto
      then show ?thesis using ascending_list.simps list_transfer.simps(2) False
                     by auto
      qed
     qed

lemma assumes "x \<in> {a| b. P(a,b)}"
       shows "\<exists>y.(P(x,y))"
      using assms by auto

lemma "x \<in> {a. P(a)} \<union> {b. Q(b)} \<Longrightarrow> (P(x)\<or>Q(x))"
           by auto

*)
primrec set_assign_to_wall::"wall \<Rightarrow> (endpt \<times> endpt) set"
where
"set_assign_to_wall (basic b) = (block_act b)"
|"set_assign_to_wall (b*bs) = endact (block_act b) (set_assign_to_wall bs)"
(*
lemma finite_set_assign_to_wall: "finite (set_assign_to_wall w)"
    apply(induct_tac w)
    apply(auto)
    apply(simp add:finite_block_act)
    apply(simp add:endpt_act_def)
    apply(auto)      
       *)
lemma codom_tuple_condn:"(codom m, codom n) \<in> endpt_act S1 S2 \<Longrightarrow> (codom m, codom n) \<in> S1 \<or> 
(\<exists>k1 k2 ls. (((codom m, dom k1) \<in> S1)\<and>(fst (hd ls) = (codom k1)) 
 \<and>(snd (last ls) = (codom k2))  \<and>((dom k2, codom n) \<in> S1))
                                            \<and>(alt_list S1 S2 ls)
                                            \<and>(ascending_list ls)\<and>(ls \<noteq> []))"
 using endpt_act_def by auto
(*
theorem "endpt_act S1 (endpt_act S2 S3) = endpt_act (endpt_act S1 S2) S3"
proof-
 have "(x,y) \<in> endpt_act S1 (endpt_act S2 S3) \<Longrightarrow> (x,y) \<in> endpt_act (endpt_act S1 S2) S3"
   proof-   
   assume 0:"(x,y) \<in> endpt_act S1 (endpt_act S2 S3)"
   then have ?thesis  
       proof
       have "\<exists>m n.(((x,y) = (codom m, codom n))\<or> ((x,y) = (codom m, dom n)))\<or>((x,y) = (dom m, dom n))
                       \<or>((x,y) = (dom m, codom n))"
                           using 0 endpt.exhaust by metis
       then obtain m n where "(((x,y) = (codom m, codom n))\<or> ((x,y) = (codom m, dom n)))
                                         \<or>((x,y) = (dom m, dom n))
                       \<or>((x,y) = (dom m, codom n))"
                           by auto
       have "(x,y) = (codom m, codom n) \<Longrightarrow>  (x, y) \<in> endpt_act (endpt_act S1 S2) S3"
       proof-
        assume 1: "(x,y) = (codom m, codom n)"
        then have 11:"(codom m, codom n) \<in> (endpt_act S1 (endpt_act S2 S3))"
                     using 0 by auto   
        then have 12:" (codom m, codom n) \<in> S1 \<or> 
            (\<exists>k1 k2 ls. (((codom m, dom k1) \<in> S1)\<and>(fst (hd ls) = (codom k1)) 
           \<and>(snd (last ls) = (codom k2))  \<and>((dom k2, codom n) \<in> S1))
                                            \<and>(alt_list S1 (endpt_act S2 S3) ls)
                                            \<and>(ascending_list ls)\<and>(ls \<noteq> []))"
                            using codom_tuple_condn by auto 
        then have ?thesis
           proof(cases " (codom m, codom n) \<in> S1")
           case True
             have "(x,y) \<in> S1" 
                     using True 1 by auto
             then have "(x,y) \<in> (endpt_act S1 S2)"
                           using 1 endpt_act_def by auto
             then have "(x,y) \<in> (endpt_act (endpt_act S1 S2) S3)"
                            using endpt_act_def 1 by auto
             then show ?thesis using 1 by auto
           next
           case False
           have "(\<exists>k1 k2 ls. (((codom m, dom k1) \<in> S1)\<and>(fst (hd ls) = (codom k1)) 
                              \<and>(snd (last ls) = (codom k2))  \<and>((dom k2, codom n) \<in> S1))
                                            \<and>(alt_list S1 (endpt_act S2 S3) ls)
                                            \<and>(ascending_list ls))"
                        using  12 1 False by auto
          then obtain k1 k2 ls where  " (((codom m, dom k1) \<in> S1)\<and>(fst (hd ls) = (codom k1)) 
                              \<and>(snd (last ls) = (codom k2))  \<and>((dom k2, codom n) \<in> S1))
                                            \<and>(alt_list S1 (endpt_act S2 S3) ls)
                                            \<and>(ascending_list ls)"
                              by metis
          then have 111:"(((codom m, dom k1) \<in> S1)\<and>(fst (hd ls) = (codom k1)) 
                              \<and>(snd (last ls) = (codom k2))  \<and>((dom k2, codom n) \<in> S1))
                                            \<and>(alt_list S1 (endpt_act S2 S3) ls)
                                            \<and>(ascending_list ls)"
                            by auto
          then have "(alt_list S1 (endpt_act S2 S3)) ls"
                            using alt_list_def by auto
          then have "
  *)          
(*
|(codom m , dom n)  \<Rightarrow> 
          (if (belongs_to_list (codom n) (linearize xs))
                  then (replace_in (codom n) (codom m) xs)
                  else (codom m, dom n)#xs)
|(dom m, codom n)  \<Rightarrow>  (if (belongs_to_list (codom m) (linearize xs))
                  then (replace_in (codom m) (codom n) xs)
                  else ((dom m, codom n)#xs))
|(dom m, dom n)  \<Rightarrow>  if (find_both (codom m) (codom n) xs)
                         then ((other_end_list (codom m) xs, other_end_list (codom n) xs)
                              #(delete_containing (codom m) (delete_containing (codom n) xs)))
                         else xs)"
(* ((other_end (codom m) xs, other_end (codom n) xs)
                              #(delete_containing (codom m) (delete_containing (codom n) xs)))
                         else xs*)
primrec endlist_act::"(endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"endlist_act [] ys = ys" 
|"endlist_act (x#xs) ys = (endpt_act x (endlist_act xs ys))"
(*
lemma "endlist_act xs (endlist_act ys zs) = (endlist_act (endlist_act xs ys) zs)"       
proof(induction xs)
case Nil
 show ?case by auto
next
case (Cons x xs)
 have "endlist_act xs (endlist_act ys zs) = (endlist_act (endlist_act xs ys) zs)"
                 using Cons by auto
 then have "endlist_act (x#xs) (endlist_act ys zs) 
                      = endpt_act x (endlist_act xs (endlist_act ys zs))"
                     using endlist_act.simps(2) by auto
 then have "endlist_act (x#xs) (endlist_act ys zs) 
                            = endpt_act x (endlist_act (endlist_act xs ys) zs)"
                          using Cons by auto
 then have "endlist_act (x#xs) (endlist_act ys zs)
                            = endlist_act (x#(endlist_act xs ys)) zs"
                           by auto
 then have ?case sledgehammer 
          apply(induct_tac xs)
          apply(auto)
          sledgehammer
           apply(simp add:endlist_act_def)
           apply(auto) *)

primrec wall_act::"wall \<Rightarrow> (endpt \<times> endpt) list"
where
"wall_act (basic bs) = (block_act bs)"
|"wall_act (b*bs) = (endlist_act (block_act b) (wall_act bs))" 

lemma "(wall_act (w1 \<circ> w2)) = (endlist_act (wall_act w1) (wall_act w2))"
proof(induction w1)
case (basic b)
 show ?case using basic by auto
next
case (prod b bs)
 have "wall_act (b*(bs \<circ> w2)) = (endlist_act (block_act b) (wall_act (bs \<circ> w2)))"
         by auto      
 then have "(endlist_act (block_act b) (wall_act (bs \<circ> w2))
                       = (endlist_act (block_act b) (endlist_act (wall_act bs) (wall_act w2))))"
                          using prod by auto
 then have "(endlist_act (block_act b) (endlist_act (wall_act bs) (wall_act w2)))
               = (endlist_act (wall_act (b*bs)) (wall_act w2))"
                    using endlist_act.simps wall_act.simps sledgehammer
 then show ?case using prod  sledgehammer      

value "endpt_act (dom 1, codom 1) [(dom 2, codom 3)]"

value "Max {}" *)
(*
lemma "block_act [vert] = {(codom 1, dom 1)}"
     proof-
 have "block_act [vert] = {(codom ((max_codom {})+1), dom (max_dom  {}+1)), 
                                 (dom ((max_dom {})+1), codom (max_codom  {}+1))}
                        \<union>{}"
                  using block_act.simps by auto
 then have "block_act [vert] = {(codom ((max_codom {})+1), dom (max_dom  {}+1))}"
                    by auto
 moreover have  "(codom_set_filter {}) ={}"
                   using max_codom_def codom_set_filter_def by auto 
 moreover have  "(dom_set_filter {}) ={}"
                     using dom_set_filter_def by auto
 ultimately have "(max_codom {} = 0)\<and>(max_dom {}) = 0 "
                          using max_codom_def max_dom_def by auto
 then have "block_act [vert] = {(codom 1, dom 1)}" 
                          by auto  
 then show ?thesis by simp
qed
*)

 
        
(*{(codom ((max_codom (block_act xs))+1), dom (max_dom (block_act xs)+1)),
               (dom (max_dom (block_act xs)+1),codom ((max_codom (block_act xs))+1))}
                        \<union>(block_act xs)     *)

(*
inductive_set
  connect :: "(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set"  
  for xs :: "(endpt \<times> endpt) set" and ys :: "(endpt \<times> endpt) set"
where
  intro1[intro]: "((dom n, dom m) \<in> xs)  
                         \<Longrightarrow>(dom n, dom m) \<in> (connect xs ys)"
  |intro2:"((codom n, codom m) \<in> ys)  
                         \<Longrightarrow>(codom n, codom m) \<in> (connect xs ys)"
  |"((dom m, dom n) \<in> (connect xs ys))\<and>((codom n, codom k) \<in> (connect xs ys)) 
                         \<Longrightarrow> (dom m, codom k) \<in> (connect xs ys)"
  |"((dom m, codom n) \<in> (connect xs ys))\<and>((dom n, dom k) \<in> (connect xs ys)) 
                         \<Longrightarrow> (dom m, dom k) \<in> (connect xs ys)"
  |"((codom n, dom m) \<in> (connect xs ys))\<and>((codom m, codom k) \<in> (connect xs ys)) 
                         \<Longrightarrow> (codom n, codom k) \<in> (connect xs ys)"
  |"((x,y) \<in> (connect xs ys)) \<Longrightarrow> (y,x) \<in> (connect xs ys)" 

*)
(*
lemma "(dom 1, codom 3) \<in> connect {(dom 1, dom 2)} {(codom 2, codom 3)}"
proof-
let ?X = "{(dom 1, dom 2)}"
let ?Y = " {(codom 2, codom 3)}" 
have "(codom 2, codom 3) \<in> connect ?X ?Y"
            using intro2 by auto
then have "(dom 1, dom 2) \<in> connect ?X ?Y"
           using intro1 by auto
then have "(dom 1, codom 3) \<in> connect ?X ?Y"
              using connect.induct by (metis `(codom 2, codom 3) \<in> connect {(endpt.dom 1, endpt.dom 2)} {(codom 2, codom 3)}` connect.intros(3))
then show ?thesis by auto
qed
*)

(*
lemma "(codom 3, dom 1) 
\<in> endpt_act {(codom 1, codom 2),(codom 3, dom 3),(dom 2, dom 1)}
               {(dom 1, dom 2),(codom 3, codom 2),(codom 1, dom 1)}"
proof-
let ?xs = "{(codom 1, codom 2),(codom 3, dom 3),(dom 2, dom 1)}"
let ?ys = "{(dom 1, dom 2),(codom 3, codom 2),(codom 1, dom 1)}"
have "(codom 3, dom 3) \<in> ?xs"
             by auto
moreover have "alt_list ?xs ?ys [(codom 3, codom 2), (dom 2, dom 1)]" 
           using alt_list.simps by eval
moreover have "ascending_list [(codom 3, codom 2), (dom 2, dom 1)]"
            using ascending_list.simps by eval
moreover have "(codom 1, dom 1) \<in> ?ys"
            by auto
ultimately have "\<exists>m n k1 k2 ls. (((codom m, dom k1) \<in> ?xs)
                                            \<and>(fst (hd ls) = (dom k1)) 
                                            \<and>(snd (last ls) = (codom k2)) 
                                            \<and>((codom k2, dom n) \<in> ?ys))
                                            \<and>(alt_list ?xs ?ys ls)
                                            \<and>(ascending_list ls)"
                        using exI
*)
end
