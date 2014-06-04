theory comp_preserves
imports assoc
begin


(*
definition endpt_act::"(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set"
where
"endpt_act xs ys \<equiv> {(codom m, codom n) | m n.(codom m, codom n) \<in> xs} 
                    \<union>{(dom m, dom n) | m n. (dom m, dom n) \<in> ys} 
                    \<union>{(codom m, codom n) | m n k1 k2 ls. (((codom m, dom k1) \<in> xs)
                                            \<and>(fst (hd ls) = (codom k1)) 
                                            \<and>(snd (last ls) = (codom k2)) 
                                            \<and>((dom k2, codom n) \<in> xs))
                                            \<and>(alt_list xs ys ls)
                                            \<and>(ascending_list ls)\<and>(ls \<noteq> [])  }
                    \<union>{(dom m, dom n) | m n k1 k2 ls. (((dom m, codom k1) \<in> ys)
                                            \<and>(fst (hd ls) = (dom k1)) 
                                            \<and>(snd (last ls) = (dom k2)) 
                                            \<and>((codom k2, dom n) \<in> ys))
                                            \<and>(alt_list xs ys ls)
                                            \<and>(ascending_list ls)  }
                    \<union>{(codom m, dom n) | m n k1 k2 ls. (((codom m, dom k1) \<in> xs)
                                            \<and>(fst (hd ls) = (dom k1)) 
                                            \<and>(snd (last ls) = (codom k2)) 
                                            \<and>((codom k2, dom n) \<in> ys))
                                            \<and>(alt_list xs ys ls)
                                            \<and>(ascending_list ls)}
                     \<union>{(dom m, codom n) | m n k1 k2 ls. (((codom n, dom k1) \<in> xs)
                                            \<and>(fst (hd ls) = (dom k1)) 
                                            \<and>(snd (last ls) = (codom k2)) 
                                            \<and>((codom k2, dom m) \<in> ys))
                                            \<and>(alt_list xs ys ls)
                                            \<and>(ascending_list ls)}
                      \<union>{(dom m, codom n) | m n k. (((codom n, dom k) \<in> xs)
                                                          \<and>((codom k, dom m) \<in> ys)) }
                      \<union>{(codom m, dom n) | m n k. (((codom m, dom k) \<in> xs)
                                        \<and>((codom k, dom n) \<in> ys))}"*)

(*
definition symmetric::"('a \<times> 'a) set \<Rightarrow> bool"
 where
"symmetric S \<equiv> \<forall>x.\<forall>y.((x,y) \<in> S) \<longrightarrow> ((y,x) \<in> S)"  
*)

primrec rev_list::"(endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"rev_list [] = []"
|"rev_list (x#xs) = (snd x, fst x)#(rev_list xs)"

lemma rev_list_non_Nil:"xs \<noteq> [] \<longrightarrow> (rev_list xs \<noteq> [])"
      apply(induct_tac xs)
      apply(auto)
      done
definition rev_rev_list::"(endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"rev_rev_list xs = (rev (rev_list xs))"
value "rev [(1::nat),2,3,4]"
value "rev_rev_list [(codom 1, dom 2), (dom 3, dom 4)]" 

lemma rev_non_Nil:"(xs \<noteq>[]) = (rev xs \<noteq> [])"
  using Nil_is_rev_conv by auto

lemma rev_rev_list_non_Nil:"(xs \<noteq>[]) = (rev_rev_list xs \<noteq> [])"
    using rev_non_Nil rev_list_non_Nil rev_rev_list_def by auto

value "rev_list [(dom 1, codom 2), (dom 2, codom 3)]"

lemma ascending_list_Cons:"ascending_list (x#xs) \<Longrightarrow> ascending_list xs"
          using ascending_list.simps by metis

lemma rev_rev_list_induct: "rev_rev_list (x#xs) = (rev_rev_list xs)@(rev_rev_list [x])"
            using rev_rev_list_def rev_def rev_list_def by auto


lemma last_rev:"xs \<noteq> [] \<Longrightarrow> (last (rev xs) = hd xs)"
         using last_rev by auto

lemma last_rev_list:"xs \<noteq> [] \<Longrightarrow> (snd (hd (rev_list xs))) = (fst (hd xs))"
          using rev_list.simps by (metis hd.simps list.exhaust snd_eqD)

lemma last_rev_rev_list:"xs \<noteq> [] \<Longrightarrow> (snd (last (rev_rev_list xs))) = (fst (hd xs))"
       using last_rev_list last_rev rev_rev_list_def  rev_list_non_Nil 
                    by (metis)   
lemma ascending_list_append:
 "(ascending_list xs)\<and>(ascending_list ys)\<and>(str_number (snd (last xs)) = str_number (fst (hd ys)))
                         \<Longrightarrow> (ascending_list (xs@ys))"
proof(induction xs)
 case Nil
  show ?case using append_Nil Nil ascending_list.simps by auto
 next
 case (Cons x xs)
    have 1:"ascending_list (x#xs)"
          using Cons by auto
    then have 2:"ascending_list xs"
         using ascending_list_Cons by metis
    then have 3:"ascending_list (xs@ys)"
         using Cons by (metis last_ConsR self_append_conv2)  
    then show ?case
        proof(cases "ys")
        case Nil
              show ?thesis using 1 by (metis Nil append_Nil2)
        next
        case (Cons y yss)
               have "xs = [] \<Longrightarrow> (x#xs) = [x]"
                       by auto
               then have "xs = [] \<Longrightarrow>(str_number (fst (last (x#xs)))) 
                                     = (str_number (fst x))"
                                by auto
               then have "xs = [] \<Longrightarrow> (str_number (snd x) = str_number (fst (hd ys)))"
                                    using Cons by (metis Cons.prems last_ConsL) 
               then have "xs = [] \<Longrightarrow> ascending_list (x#ys)"
                                  using ascending_list.simps by (metis Cons.prems)
               moreover have "xs = [] \<Longrightarrow> (x#ys) = (x#xs)@ys"
                                      using append_Cons by auto
               ultimately have 11:"xs = [] \<Longrightarrow> ascending_list ((x#xs)@ys)"
                               by metis
                have "xs \<noteq> [] \<Longrightarrow> (str_number (snd x)) = (str_number (fst (hd xs)))"  
                              using 1 ascending_list.simps by auto
                then have "xs \<noteq> [] \<Longrightarrow> ascending_list (x#(xs@ys))"
                                 using 3 ascending_list.simps by auto
                with 11 show ?thesis using append.simps by metis
           qed
qed

find_theorems "alt_list"

lemma ascending_rev_rev_list:
 "ascending_list xs \<Longrightarrow> ascending_list (rev_rev_list xs)"
 proof(induction xs)
 case Nil
    show ?case using ascending_list.simps rev_rev_list_def rev_list.simps rev_def by auto
 next
 case (Cons x xs)
     have 1:"rev_rev_list (x#xs) = (rev_rev_list xs)@[(snd x, fst x)]"
                 using rev_list_def rev_def rev_rev_list_def snd_conv fst_conv by auto
     then have 2:"xs = [] \<Longrightarrow> ascending_list (rev_rev_list (x#xs))"
                 using rev_rev_list_def by auto
     have 3:"ascending_list (x#xs)"
                 using Cons by auto
     then have 4:"ascending_list xs"
                  using ascending_list_Cons by metis
     then have 5:"ascending_list (rev_rev_list xs)"
                  using Cons by auto
     from 3 have 6:"xs \<noteq> [] \<Longrightarrow> str_number (snd x) = str_number (fst (hd xs))"
                   using ascending_list.simps by auto
     moreover have "xs \<noteq> [] \<Longrightarrow> str_number (snd x) = str_number (fst (hd [(snd x, fst x)]))"
                             by auto
     moreover have " xs \<noteq> [] \<Longrightarrow>  str_number (fst (hd xs)) 
                  = (str_number (snd (last (rev_rev_list xs))))"
                     using last_rev_rev_list by auto 
     ultimately have "xs \<noteq> [] \<Longrightarrow>(str_number (snd (last (rev_rev_list xs))))
                                       = str_number (fst (hd [(snd x, fst x)]))"
                         by metis
     moreover have "ascending_list [(snd x, fst x)]"
                           by auto
     ultimately have "xs \<noteq> [] \<Longrightarrow> (ascending_list (rev_rev_list (x#xs)))"
                             using 5 1 ascending_list_append  by auto  
     then show ?case using 2 by auto
qed



lemma alt_list_cons:"alt_list S1 S2 (x#xs) \<longrightarrow>(alt_list S1 S2 xs)"
        apply(induct_tac xs)
        apply (metis alt_list.simps(1))
        apply (case_tac "dom_tuple x")
        apply(auto)
        done
                   

lemma "alt_list S1 S2 xs \<and> alt_list S1 S2 ys \<and> (hd ys \<in> S1)\<and>(dom_tuple (hd ys))\<and>
                (last xs \<in> S2)\<and>(codom_tuple (last xs))
          \<Longrightarrow> alt_list S1 S2 (xs@ys)"
proof(induction xs)
 case Nil
  show ?case using Nil append_Nil by auto
 next
 case (Cons x xs)
    have 1:"ys = [] \<Longrightarrow> alt_list S1 S2 (x#xs@ys)"
                 using append_Nil2 Cons by auto
    have "alt_list S1 S2 (x#xs)"
              using Cons by auto
    moreover then have "alt_list S1 S2 (xs)"
               using alt_list_cons by metis
    moreover then have "alt_list S1 S2 (xs@ys)"
                   using Cons by (metis last.simps self_append_conv2)
   ultimately have "alt_list S1 S2 (x#xs@ys)"
             proof(cases "dom_tuple x")
             case True
                have 1:"dom_tuple x"
                        using True by auto
                show ?thesis using Cons True sledgehammer by auto
                   proof(cases "xs = []")
                   case True
                    have "(last (x#xs) \<in> S2)"
                               using Cons by auto
                    then have "x \<in> S2"
                             using True by auto   
                    then have "codom_tuple (hd ys)"
                             using Cons     
then have "(dom_tuple x) \<and>(xs \<noteq> []) \<Longrightarrow> alt_list S1 S2 (x # xs) =   
                          (x \<in> S1 \<and> hd xs \<in> S2 \<and> codom_tuple (hd xs) \<and> alt_list S1 S2 xs)"
                    using alt_list.simps sledgehammer





theorem "nice_set S1 \<and> nice_set S2 
        \<and> (max_codom S1 = max_codom S2) \<Longrightarrow> nice_set (endpt_act S1 S2)"
proof-
assume assm_0:"nice_set S1 \<and> nice_set S2 
                \<and> (max_codom S1 = max_codom S2) "
have "symmetric (endpt_act S1 S2)"
   proof-
   fix x y
   assume assm_00:"(x, y) \<in> (endpt_act S1 S2)"
   have "\<exists>m n.(((x,y) = (codom m, codom n))\<or> ((x,y) =(dom m, dom n))
              \<or>((x,y) = (codom m, dom n))\<or>((x,y) = (dom m, codom n)))"
              using assm_00 endpt.exhaust by metis
  then obtain m n where 
          "(((x,y) = (codom m, codom n))\<or> ((x,y) =(dom m, dom n))
              \<or>((x,y) = (codom m, dom n))\<or>((x,y) = (dom m, codom n)))"
         by auto
 then have "((x,y) = (codom m, codom n)) \<Longrightarrow> (codom n, codom m) \<in> (endpt_act S1 S2)"
         proof-
         assume assm_000: "(x,y) = (codom m, codom n)"
         have "(x,y)\<in> S1 \<Longrightarrow> (y, x) \<in> S1"
                using assm_0 nice_set_def symmetric_def 
                by metis
         then have 1:"(x, y) \<in> S1 \<Longrightarrow> (y,x) \<in>(endpt_act S1 S2)"
               using endpt_act_def assm_000 fst_conv snd_conv by auto  
          then have 2:"(x, y) \<in> S1 \<Longrightarrow>  (codom m, codom n) \<in> S1 \<or> 
            (\<exists>k1 k2 ls. (((codom m, dom k1) \<in> S1)\<and>(fst (hd ls) = (codom k1)) 
           \<and>(snd (last ls) = (codom k2))  \<and>((dom k2, codom n) \<in> S1))
                                            \<and>(alt_list S1 (endpt_act S2 S3) ls)
                                            \<and>(ascending_list ls)\<and>(ls \<noteq> []))"
                            using codom_tuple_condn  assm_000 by auto
           then have "((x, y) \<in> S1)  \<and>  ((codom m, codom n) \<notin> S1) \<Longrightarrow> 
            (\<exists>k1 k2 ls. (((codom m, dom k1) \<in> S1)\<and>(fst (hd ls) = (codom k1)) 
           \<and>(snd (last ls) = (codom k2))  \<and>((dom k2, codom n) \<in> S1))
                                            \<and>(alt_list S1 S2 ls)
                                            \<and>(ascending_list ls)\<and>(ls \<noteq> []))"
                            using assm_000 by auto
            then obtain k1 k2 ls where "((x, y) \<in> S1)  \<and>  ((codom m, codom n) \<notin> S1) \<Longrightarrow> 
             (((codom m, dom k1) \<in> S1)\<and>(fst (hd ls) = (codom k1)) 
           \<and>(snd (last ls) = (codom k2))  \<and>((dom k2, codom n) \<in> S1))
                                            \<and>(alt_list S1 S2 ls)
                                            \<and>(ascending_list ls)\<and>(ls \<noteq> [])"
                                by auto
             then have  2:"((x, y) \<in> S1)\<and>((codom m, codom n) \<notin> S1) \<Longrightarrow> 
             (((codom m, dom k1) \<in> S1)\<and>(fst (hd ls) = (codom k1)) 
              \<and>(snd (last ls) = (codom k2))  \<and>((dom k2, codom n) \<in> S1))
                                            \<and>(alt_list S1 S2 ls)
                                            \<and>(ascending_list ls)\<and>(ls \<noteq> [])"
                                by auto                       
             let ?rev_ls = "rev_rev_list ls"
             have 3:"((x, y) \<in> S1)\<and>((codom m, codom n) \<notin> S1) \<Longrightarrow> ascending_list ?rev_ls"
                     using 2 ascending_rev_rev_list by auto
             then have "
end

