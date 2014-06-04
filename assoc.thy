theory assoc
imports Comp
begin


(*new definitions*)


definition codom_tuple_filter::"(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set"
where
"codom_tuple_filter xs \<equiv> {(codom m, codom n) |m n. ((codom m, codom n) \<in> xs)}"


lemma "codom_tuple_filter {(codom 1, codom 3), (codom 4, dom 5)}
                  = {(codom 1, codom 3)}"
      using codom_tuple_filter_def by auto


definition dom_tuple_filter::"(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set"
where
"dom_tuple_filter xs \<equiv> {(dom m, dom n) |m n. ((dom m, dom n) \<in> xs)}"


lemma "dom_tuple_filter {(codom 1, codom 3), (dom 4, dom 5)}
                  = {(dom 4, dom 5)}"
      using dom_tuple_filter_def by auto

primrec ascending_list::"(endpt \<times> endpt) list \<Rightarrow> bool"
where
"ascending_list [] = True"
|"ascending_list (x#xs) = (if (xs = []) 
                           then True 
                           else (str_number (snd x)=str_number (fst (hd xs)))\<and>(ascending_list xs))"

lemma ascending_list_append:
 "(ascending_list xs)\<and>(ascending_list ys)\<and>(str_number (snd (last xs)) = str_number (fst (hd ys)))
                     \<longrightarrow> ascending_list (xs@ys)"
    apply(induct_tac xs)
    apply(auto)
    done  

value "ascending_list [(codom 1, codom 2),(dom 2, codom 3)]" 

value "codom_tuple (hd [])"

primrec alt_list::"(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set \<Rightarrow>(endpt \<times> endpt) list \<Rightarrow> bool"
where
"alt_list xs ys [] = True"
|"alt_list xs ys (z#zs) = (case (dom_tuple z) of 
                       True \<Rightarrow> (if (zs = []) 
                                    then (z \<in> xs)
                                    else (z \<in> xs)
                                         \<and>(hd zs) \<in> ys)
                                         \<and>(codom_tuple (hd zs))
                                         \<and>(alt_list xs ys zs)
             |False \<Rightarrow>(if (zs = []) 
                                    then (z \<in> ys)\<and>(codom_tuple z) 
                                    else (z \<in>  ys)\<and>(codom_tuple z)
                                        \<and>((hd zs) \<in> xs)\<and>(dom_tuple (hd zs))
                                        \<and>(alt_list xs ys zs)
                                      ))" 

lemma "ls \<noteq> [] \<Longrightarrow> ls = (hd ls)#(tl ls)"
        unfolding hd_def tl_def  by (metis (lifting) list.exhaust list.simps(7))
(*
lemma "(fst (hd ls) = codom k)\<and>(hd ls \<in> S2)\<and>(alt_list S1 S2 ls) \<Longrightarrow> \<exists>l.(hd ls = (codom k, codom l))"
     proof-
    have "(ls \<noteq> []) \<Longrightarrow> (ls = (hd ls)#(tl ls))"
                using hd.simps tl.simps by auto  
     have "((fst (hd ls)) = codom k) \<Longrightarrow> (\<not>(dom_tuple (hd ls)))"
              using dom_tuple_def type_def by auto
    then have "(alt_list S1 S2 ls)\<and>(ls \<noteq> [])\<and>(\<not>(dom_tuple (hd ls))) \<Longrightarrow> (codom_tuple (hd ls))"
                     using alt_list.simps sledgehammer *)
value "alt_list {(codom 1, codom 3),(dom 1, dom 2)} {(codom 2, codom 5), (codom 6, codom 7),(dom 1, dom 3)} 
                        [(codom 1,codom 3),(dom 1, dom 3)]"

(*warning-over riders prohibited*)
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
                                        \<and>((codom k, dom n) \<in> ys))}"

function endact::"(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set "
where
"endact {} S = S"
|"endact S {} = S"
|"endact (insert s1 S1) (insert s2 S2) = endpt_act (insert s1 S1) (insert s2 S2)"
   apply (metis nonempty_iff prod.exhaust)
   apply (metis prod.inject)
   apply (metis prod.inject)
   apply (metis insert_not_empty prod.inject)
   apply (metis prod.inject)
   apply (metis insert_not_empty prod.inject)
   apply (auto)
   done

lemma codom_tuple_endpt_act:"(codom m , codom n) \<in> endpt_act xs ys \<and> (codom m, codom n) \<notin> xs 
                       \<Longrightarrow> (\<exists>k1 k2 ls. (((codom m, dom k1) \<in> xs)
                                            \<and>(fst (hd ls) = (codom k1)) 
                                            \<and>(snd (last ls) = (codom k2)) 
                                            \<and>((dom k2, codom n) \<in> xs))
                                            \<and>(alt_list xs ys ls)
                                            \<and>(ascending_list ls))"
                 using endpt_act_def by auto

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
