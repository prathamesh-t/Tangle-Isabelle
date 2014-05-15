theory Comp
imports Link_Algebra
begin



(*we begin by defining two different types of an end of a strand, domain refers to the fact the 
other end of a strand lies in the domain of the wall and codomain refers to the fact that other end
of a strand lies in the codomain*) 
datatype endtype = domain | codomain 


(*endpoint of a strand is given by the type of the end point and a natural number which refers
to the  position of the other end of the strand*)  

datatype endpt = dom nat|codom nat

(*the function type tells us the endtype of an endpt*)
definition type::"endpt \<Rightarrow> endtype"
where
"type x = (case x of dom n \<Rightarrow> domain|codom n \<Rightarrow> codomain)"

lemma type_uniqueness:"type x \<noteq> type y \<Longrightarrow> x \<noteq> y"
     using type_def by auto

(*the function str_number tells us the strand number of an endpt*)
definition str_number::"endpt \<Rightarrow> nat"
where
"str_number x = (case x of dom n \<Rightarrow> n|codom n \<Rightarrow> n)"

(*lemmas about str_number*)

lemma str_number_uniqueness:"str_number x \<noteq> str_number y \<Longrightarrow> (x \<noteq> y)"
       using str_number_def by auto

(*the following function tells us the maximum strand number in a list which is of the type dom*)
primrec dom_Max_list::"endpt list \<Rightarrow> nat"
where
"dom_Max_list [] = 0"|
"dom_Max_list (Cons x xs) = (case (type x) of 
                                             domain \<Rightarrow> (max (str_number x) (dom_Max_list xs))
                                             |codomain\<Rightarrow> (dom_Max_list xs))"
lemma dom_cons:"(dom_Max_list ((dom n)#xs)) \<ge> n"
      using dom_Max_list.simps type_def max_def
       by (metis endpt.simps(5) endtype.simps(3) eq_iff str_number_def)

lemma dom_Max_list_cons: "dom_Max_list (x#xs) \<ge> dom_Max_list xs"
     unfolding dom_Max_list.simps max_def type_def str_number_def 
   by (metis (mono_tags) dom_Max_list.simps(2) endtype.exhaust endtype.simps(3)
   endtype.simps(4) eq_iff max_def min_max.le_sup_iff min_max.sup.commute 
  min_max.sup.idem nat_le_linear order_refl str_number_def type_def)

lemma dom_Max_list_append: "dom_Max_list (ys@xs) \<ge> (dom_Max_list xs)"
        apply(induct_tac ys)
        apply(auto)
        by (metis dom_Max_list.simps(2) dom_Max_list_cons order_trans)    

(*the following function gives us n such that n is the maximum number assigned to an end of 
a type codomain*)
primrec codom_Max_list::"endpt list \<Rightarrow> nat"
where
"codom_Max_list [] = 0"|
"codom_Max_list (Cons x xs) = (case (type x) of 
                            codomain \<Rightarrow> (max (str_number x) (codom_Max_list xs))
                                              |domain\<Rightarrow> (codom_Max_list xs))"

(*
definition max_in_set::"endpt set \<Rightarrow> nat"
where
"max_in_set xs \<equiv> ((Max  {n.(codom n) \<in> xs}))"

*)

   
lemma codom_cons:"(codom_Max_list ((codom n)#xs)) \<ge> n"
      using codom_Max_list.simps type_def max_def
      by (metis endpt.simps(6) endtype.simps(4) eq_iff str_number_def)


lemma codom_Max_list_cons: "codom_Max_list (x#xs) \<ge> codom_Max_list xs"
     unfolding codom_Max_list.simps max_def type_def str_number_def 
   by (metis (mono_tags) codom_Max_list.simps(2) endtype.exhaust endtype.simps(3)
   endtype.simps(4) eq_iff max_def min_max.le_sup_iff min_max.sup.commute 
  min_max.sup.idem nat_le_linear order_refl str_number_def type_def)

lemma codom_Max_list_append:"codom_Max_list (ys@xs) \<ge> (codom_Max_list xs)"
        apply(induct_tac ys)
        apply(auto)
        by (metis codom_Max_list.simps(2) codom_Max_list_cons order_trans)
    
lemma "(codom_Max_list xs > 0) \<Longrightarrow> (xs \<noteq> [])"
         using codom_Max_list.simps(1) by auto


lemma "(codom_Max_list xs > 0) \<Longrightarrow> \<exists>x.\<exists>zs.(xs =(x#zs))"
       using codom_Max_list.simps  list.exhaust neq0_conv unfolding codom_Max_list_def 
       by (metis (lifting))

lemma "(codom_Max_list xs > 0) \<Longrightarrow> \<exists>ys.\<exists>y.\<exists>zs.((xs = (ys@(y#zs)))\<and>(y=codom (codom_Max_list xs)))"
proof(induction xs)
 case Nil
    show ?case using Nil.prems by auto
 next
 case (Cons x xss)
   have "codom_Max_list (x#xss) =  (case (type x) of 
                            codomain \<Rightarrow> (max (str_number x) (codom_Max_list xss))
                                              |domain\<Rightarrow> (codom_Max_list xss))"
           using codom_Max_list.simps(2) by auto
   then have ?case
         proof(cases "type x")
         case domain
           have 0:"codom_Max_list (x#xss) = codom_Max_list (xss)"
                               using domain by auto
           then have 1:"\<exists>yss.\<exists>y.\<exists>zss.((xss = (yss@(y#zss)))
                   \<and>(codom (codom_Max_list xss) = y))"
                      using Cons.prems Cons.IH by auto
           then have "\<exists>yss.\<exists>y.\<exists>zss.(((x#xss) = (yss@(y#zss)))
                   \<and>(codom (codom_Max_list xss) = y))"
                        using exI  append_Cons  by metis
           then show ?thesis  using 0 by auto
           next   
           case codomain
           have 0: "codom_Max_list (x#xss) = (max (str_number x) (codom_Max_list xss))"
                  using codomain codom_Max_list.simps by auto
           have ?thesis 
                proof(cases "(max (str_number x) (codom_Max_list xss)) = str_number x")
                case True
                      have "codom (str_number x) = x"
                                    using str_number_def codomain type_def  
                                    endpt.exhaust endpt.simps(5) 
                                    endpt.simps(6) endtype.distinct(1) 
                                    by (metis (lifting))
               
                      then have "(((x#xss) = ([]@(x#xss)))
                                          \<and>(x=codom (codom_Max_list ([]@(x#xss)))))"
                                using append.simps True 0
                                   by auto
                      then show ?thesis using exI by auto
                      next
                      case "False"
                      have 1:"codom_Max_list (x#xss) = codom_Max_list xss"
                               using 0 False by auto
                      then have 2:"\<exists>yss.\<exists>y.\<exists>zss.((xss = (yss@(y#zss)))
                                    \<and>(codom (codom_Max_list xss) = y))"
                      using Cons.prems Cons.IH by auto
                      then have "\<exists>yss.\<exists>y.\<exists>zss.(((x#xss) = (yss@(y#zss)))
                                    \<and>(codom (codom_Max_list xss) = y))"
                                   using exI  append_Cons  by metis
                       then show ?thesis  using 1  by auto
                       qed
                  then show ?thesis by simp
                  qed
 then show ?case by auto
 qed
(*       let ?yss = "SOME yss.\<exists>y.\<exists>zss.((xss = (yss@(y#zss)))\<and>(codom (codom_Max_list xss) = y))"
           have "(\<exists>yss.\<exists>y.\<exists>zss.((xss = (yss@(y#zss)))
                   \<and>(codom (codom_Max_list xss) = y)))  
         \<Longrightarrow> (\<exists>y.\<exists>zss.((xss = (?yss@(y#zss))) \<and>(codom (codom_Max_list xss) = y)))"
                  
        using 1 some_equality exI exE_some unfolding exI someI exE_some 
                                    appl

let ?y = "SOME y.\<exists>y.\<exists>zss.(xss = (?yss@(y#zss)))"
           let ?zss = "SOME zss.\<exists>zss.(xss = (?yss@(?y#zss)))"
      have "xss = (?yss@(?y#(?zss)))"
                   using 1 exI some_equality sledgehammer
*)

value "(codom_Max_list [codom 1, codom 2, codom 0])"



(*we define functions related to shifting of the codomain and domain by 1/2 strands to left*)
definition codom_left_shift::"(endpt \<Rightarrow> bool) \<Rightarrow> endpt \<Rightarrow> endpt"
where
"codom_left_shift P x \<equiv>(if ((type x = codomain)\<and> (P x)) then (codom (str_number x +1)) else x)"

definition codom_double_left_shift::"(endpt\<Rightarrow> bool) \<Rightarrow> endpt \<Rightarrow> endpt"
where
"codom_double_left_shift P x \<equiv>(if ((type x = codomain)\<and> (P x)) then (codom (str_number x +2)) else x)"

definition codom_double_left_shift_tuple::"(endpt\<Rightarrow>bool)\<Rightarrow> (endpt \<times> endpt) \<Rightarrow> (endpt \<times> endpt)"
where
"codom_double_left_shift_tuple P x \<equiv>
    (codom_double_left_shift P (fst x),codom_double_left_shift P (snd x))  "
   
primrec split_codom_double_left_shift::"(endpt \<Rightarrow> bool) \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
 where
"split_codom_double_left_shift P [] = []"
|"split_codom_double_left_shift P (x#xs) = (codom_double_left_shift_tuple P x)#(split_codom_double_left_shift P xs)"

(*we define the inverse of the above function *)

lemma endpt_reconstruction: "(x = (if ((type x)= domain) then dom (str_number x) else codom (str_number x)))"
      unfolding type_def str_number_def 
      using  endpt.exhaust endpt.simps(5) endpt.simps(6) endtype.distinct(1) by (metis)

lemma codom_double_left_shift_preserves_type:
"\<forall>x.\<forall>y.((x = (codom_double_left_shift  P y)) \<longrightarrow> ((type x) = (type y)))"
   unfolding type_def codom_double_left_shift_def  by auto

(*
lemma codom_double_left_shift_inverse:
assumes "(x = (codom_double_left_shift P y))"
shows "(y = x)\<or>(y = codom ((str_number x)- 2))"
proof(cases "((type x) = codomain)\<and>(P y)")
case False
  have "((type x) = (type y))" using assms codom_double_left_shift_preserves_type by auto
    then have "(codom_double_left_shift P y) = y"
             using codom_double_left_shift_def assms False by metis
  then show ?thesis using assms by auto
next
case True
 have 1:"x = (codom ((str_number y)+2))" 
                     using codom_double_left_shift_def True assms by auto 
 then have 2:"str_number x = (str_number y)+2" 
              using str_number_def by auto
 moreover have "str_number y \<ge> 0"
              using str_number_def by auto
 ultimately have "str_number x \<ge> 2"
              by auto
 then have 3:"str_number y = (str_number x) - 2"
              using 1 2 by auto
 moreover have "type y = codomain"
                using True codom_double_left_shift_preserves_type assms by auto
 then have "(y = (codom ((str_number x) - 2)))"
                  using 3 endpt_reconstruction by (metis endtype.distinct(1))  
 then show ?thesis using assms by auto
qed

lemma codom_double_left_shift_tuple_inverse:
assumes "(x = (codom_double_left_shift_tuple P y))"
shows "(y = x)\<or>((fst y) = codom ((str_number (fst x))- 2))\<or>((snd y) = codom ((str_number (snd x))- 2))"
 using codom_double_left_shift_inverse 
by (metis assms codom_double_left_shift_tuple_def fst_conv pair_collapse snd_conv)

lemma "split_codom_double_left_shift P xs = y#ys \<Longrightarrow>
(\<exists>z.\<exists>zs.((xs = z#zs)\<and>(codom_double_left_shift_tuple P z = y)
\<and>(split_codom_double_left_shift P zs = ys)))"
proof(induction xs)
 case Nil
  show ?case using Nil by auto
 next
 case (Cons l ls)
  have "ex
 apply(induct_tac xs)
 apply(simp add:codom_double_left_shift_tuple_inverse)
 sledgehammer
 using exI codom_double_left_shift_tuple_inverse sledgehammer  
*)
(*we define functions equivalent to above for right shift*)
definition codom_right_shift::"(endpt \<Rightarrow> bool) \<Rightarrow> endpt \<Rightarrow> endpt"
where
"codom_right_shift P x \<equiv>(if ((type x = codomain)\<and> (P x)) then (codom (str_number x- 1)) else x)"

abbreviation codom_double_right_shift::"(endpt\<Rightarrow> bool) \<Rightarrow> endpt \<Rightarrow> endpt"
where
"codom_double_right_shift P x \<equiv>(if ((type x = codomain)\<and> (P x)) then (codom (str_number x- 2)) else x)"

definition codom_double_right_shift_tuple::"(endpt\<Rightarrow>bool)\<Rightarrow> (endpt \<times> endpt) \<Rightarrow> (endpt \<times> endpt)"
where
"codom_double_right_shift_tuple P x \<equiv>
    (codom_double_right_shift P (fst x),codom_double_right_shift P (snd x))"   

primrec split_codom_double_right_shift::"(endpt \<Rightarrow> bool) \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
 where
"split_codom_double_right_shift P [] = []"
|"split_codom_double_right_shift P (x#xs) = (codom_double_right_shift_tuple P x)
                                                       #(split_codom_double_right_shift P xs)"

value 
"codom_double_right_shift_tuple  (\<lambda>x.(str_number x>2)) (codom 5, codom 6)"

(*If one of the two elements of a tuple is i then it replaces is with j*)
definition swap_with::"endpt \<Rightarrow> endpt \<Rightarrow> endpt \<Rightarrow> endpt"
where
"swap_with x i j  \<equiv> (if (x = i) then j else if (x = j) then i else x)"

lemma "swap_with i i j = j"
      using swap_with_def by auto
lemma swap_with_reflection:"\<forall>i.\<forall>j.(swap_with (swap_with x i j) i j= x)"
          using swap_with_def by auto
  
primrec swap_in::"endpt \<Rightarrow> endpt \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"swap_in i j []=  []"|
"swap_in i j (x#xs) =  (swap_with (fst x) i j,swap_with (snd x) i j)#(swap_in i j xs)"

lemma swap_in_reflection:"\<forall>i.\<forall>j.(swap_in i j  (swap_in i j xs)= xs)"
        apply(induct_tac xs)
        apply(auto)
        apply(simp add:swap_with_reflection)
        apply(simp add:swap_with_reflection)
        done

(*we check if a given element belongs to a given list of 2-tuples of endpts*)
primrec find::"endpt \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> bool"
where
"find x [] = False"|
"find x (y#ys) = (if (find x ys) then True else (((fst y) = x)\<or>((snd  y) = x)))"

(* we check if two given elements belong to the list*)
definition find_both::"endpt \<Rightarrow> endpt \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> bool"
where
"find_both x y zs \<equiv> (if (find x zs) then (find y zs) else False)"

lemma find_both_implies_find_and:"(find_both x y zs) \<longrightarrow> ((find x zs)\<and>(find y zs))"
    unfolding find_both_def by metis

lemma find_and_implies_find_both:"((find x zs)\<and>(find y zs)) \<longrightarrow> find_both x y zs"
    unfolding find_both_def by metis

lemma equality:assumes "a\<longrightarrow>b" and "b\<longrightarrow>a"
       shows "a = b"
     using assms 
 by metis
lemma find_both_equals_find_and:"((find x zs)\<and>(find y zs)) = (find_both x y zs)"
             using find_both_implies_find_and find_and_implies_find_both equality
               by metis

(*It checks if either of the two given elements belong to the list*)
definition find_either::"endpt \<Rightarrow> endpt \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> bool"
where
"find_either x y zs \<equiv> ((find x zs)\<or>(find y zs))"

(*it conversts a list of 2-tuples of endpts to a list of endpts which contains all the constituent
endpts of the former*)
primrec linearize::"(endpt \<times> endpt) list \<Rightarrow> endpt list"
where
"linearize [] = []" 
|"linearize (x#xs) = (fst x)#(snd x)#(linearize xs)"

(*filters out all the elements with endtype domain*)
definition domain_filter::"endpt list \<Rightarrow> endpt list"
where
"domain_filter xs \<equiv> [x<- xs. ((type x)=domain)]"

(*filters out all the elements with endtype codomain*)
definition codomain_filter::"endpt list \<Rightarrow> endpt list"
where
"codomain_filter xs \<equiv> [x<- xs. ((type x)=codomain)]"

(* The following function defines vertical action*)
definition vert_act::"nat \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"vert_act n xs \<equiv> 
 (if (find (codom n) xs) 
    then xs 
    else  (codom (codom_Max_list (linearize xs) + 1), dom (dom_Max_list (linearize xs) +1))#
         (dom (dom_Max_list (linearize xs) + 1), codom (codom_Max_list (linearize xs) +1))#xs)"
 
definition swap_act::"nat \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"swap_act n xs \<equiv>
 (if (find_both (codom n) (codom (n+1)) xs)
      then (swap_in (codom n) (codom (n+1)) xs)
           else if (find (codom n) xs)
              then ((dom ((dom_Max_list (linearize xs))+1), codom n)
#(codom n,dom ((dom_Max_list (linearize xs))+1))
#swap_in (codom n) (codom (n+1)) xs)
                  else 
([(dom (dom_Max_list (linearize xs)+2),
                codom (codom_Max_list (linearize xs)+1)),
  ((dom (dom_Max_list (linearize xs)+1)
               ,codom (codom_Max_list (linearize xs)+2)))
 ,(codom (codom_Max_list (linearize xs)+1)
               , dom (dom_Max_list (linearize xs)+2)),
  (codom (codom_Max_list (linearize xs)+2),
               (dom (dom_Max_list (linearize xs)+1)))]@xs))" 


definition str_number_geq_n::"nat \<Rightarrow> endpt \<times> endpt  \<Rightarrow> bool"
where
"str_number_geq_n n x \<equiv> (str_number (fst x) \<ge> n)"   

abbreviation  codom_geq_n::"nat \<Rightarrow> endpt \<Rightarrow> bool"
where
"codom_geq_n n \<equiv> (\<lambda>x.(type x=codomain)\<and>(str_number x \<ge> n))"

definition cap_act::"nat \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"cap_act n xs \<equiv> 
[(codom (n+1), codom n) ,(codom n, codom (n+1))]@(split_codom_double_left_shift (codom_geq_n n) xs)"

value "set [1,122,a,7,5,33,8,6,4,111,19] = set [a,19,33,122,111,4,7,6,1,5,8]"
(*
definition cap_act::"nat \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"cap_act n xs \<equiv> 
(takeWhile  ((str_number_geq_n n))  
(split_codom_double_left_shift (\<lambda>x.(type x=codomain)\<and>(str_number x \<ge> n)) xs))
@[(codom (n+1), codom n) ,(codom n, codom (n+1))]
@
(dropWhile ((str_number_geq_n n)) 
(split_codom_double_left_shift (\<lambda>x.(type x=codomain)\<and>(str_number x \<ge> n)) xs))"
*)
value "cap_act 3 [(codom 1, codom 2),(codom 2, codom 1)]"
primrec belongs_to_list::"'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
"belongs_to_list a [] = False"
|"belongs_to_list a (x#xs) = ((belongs_to_list a xs) \<or>(x=a))"

lemma find_equals_belongs_to_list:"(find a xs)=(belongs_to_list a (linearize xs))"
  apply(induct_tac xs)
  apply(auto)
  done

lemma find_both_equals_belongs_to_list:
"(find_both a b xs)=((belongs_to_list a (linearize xs))\<and> (belongs_to_list b (linearize xs)))"
   using find_both_equals_find_and find_equals_belongs_to_list by auto 
 

lemma belongs_to_append_of_lists:
 "belongs_to_list a (xs@ys) = (belongs_to_list a xs)\<or>(belongs_to_list a ys)"
   apply(induct_tac xs)
   apply(auto)
   done

lemma belongs_to_symmetric_list:
 "(belongs_to_list x [a,b,b,a]) \<Longrightarrow> (x = a) \<or>(x=b)"
          using belongs_to_list.simps by auto    

lemma belongs_to_list_implies_non_empty:"(belongs_to_list x xs) \<longrightarrow> (xs \<noteq> [])"
       using belongs_to_list.simps(1) by auto

lemma str_number_belongs_to_dom_Max_list: 
 "(belongs_to_list x xs)\<and>(type x = domain) \<Longrightarrow>
                 (dom_Max_list xs) \<ge>(str_number x)"
proof(induction xs)
 case Nil
    show ?case using belongs_to_list_implies_non_empty Nil by auto
 next
 case (Cons y ys)
     have 1:"(belongs_to_list x (y#ys)) \<Longrightarrow> (x=y) \<or> (belongs_to_list x ys)"
        using belongs_to_list.simps(2) by auto
     moreover have 2:"(x = y) \<Longrightarrow> dom_Max_list (y#ys) \<ge> (str_number x)"
             using dom_Max_list_def Cons by auto
     moreover have 3:"(dom_Max_list (y#ys)) \<ge> (dom_Max_list ys)"
             using dom_Max_list_cons by auto
     moreover have "(belongs_to_list x ys)\<Longrightarrow> (dom_Max_list (y#ys)) \<ge> (str_number x)"
             using Cons.IH  Cons.prems dom_Max_list_cons le_trans  by metis
     ultimately show ?case using Cons by auto
qed                  


lemma str_number_belongs_to_codom_Max_list: 
 "(belongs_to_list x xs)\<and>(type x = codomain) \<Longrightarrow>
                 (codom_Max_list xs) \<ge>(str_number x)"
proof(induction xs)
 case Nil
    show ?case using belongs_to_list_implies_non_empty Nil by auto
 next
 case (Cons y ys)
     have 1:"(belongs_to_list x (y#ys)) \<Longrightarrow> (x=y) \<or> (belongs_to_list x ys)"
        using belongs_to_list.simps(2) by auto
     moreover have 2:"(x = y) \<Longrightarrow> codom_Max_list (y#ys) \<ge> (str_number x)"
             using codom_Max_list_def Cons by auto
     moreover have 3:"(codom_Max_list (y#ys)) \<ge> (codom_Max_list ys)"
             using codom_Max_list_cons by auto
     moreover have "(belongs_to_list x ys)\<Longrightarrow> (codom_Max_list (y#ys)) \<ge> (str_number x)"
             using Cons.IH  Cons.prems codom_Max_list_cons le_trans  by metis
     ultimately show ?case using Cons by auto
qed                  


lemma domain_belongs_to_list: "(belongs_to_list x xs)\<and>(type x = domain) \<Longrightarrow> (x \<noteq> (dom ((dom_Max_list xs)+1)))"
    using str_number_belongs_to_dom_Max_list str_number_def str_number_uniqueness
       by (metis Zero_not_Suc add_0_iff add_eq_if 
       comm_monoid_add_class.add.left_neutral diff_self_eq_0 dom_Max_list.simps(2) 
       dom_cons endpt.distinct(1) endpt.exhaust endpt.inject(1) endtype.simps(3) 
       max_def min_max.sup_commute nat_add_assoc nat_add_commute nat_add_left_commute
         nat_minus_add_max zero_neq_one)

lemma codomain_belongs_to_list:"(belongs_to_list x xs)\<and>(type x = codomain) 
          \<Longrightarrow> (x \<noteq> (codom ((codom_Max_list xs)+1)))"
    using str_number_belongs_to_codom_Max_list str_number_def str_number_uniqueness
     by (metis add_eq_if codom_Max_list.simps(2) codom_Max_list_cons codom_cons 
     diff_self_eq_0 endtype.simps(4) min_max.le_iff_sup nat_add_commute not_less_eq_eq 
     zero_neq_one)                        
    
value "belongs_to_list (codom 1) ([codom 2,dom 3,codom 4,dom 5, dom 1])"

definition belongs_to::"'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
"belongs_to a xs \<equiv> a \<in> set xs"

value "belongs_to (1::nat) ([2,3,4,5])"

primrec delete_from_list::"'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
"delete_from_list a [] = []"|
"delete_from_list a (x#xs) = (if (x=a) then (delete_from_list a xs) else (x#(delete_from_list a xs)))"

(*if a is one of the two elements, then the following gives the other element else it gives
the first element*) 
definition other_end::"endpt \<Rightarrow>  (endpt \<times> endpt) \<Rightarrow> endpt"
where
"other_end a x \<equiv> (if (fst x)= a then (snd x) else if (snd  x = a) then (fst x) else a)"

primrec prelim_other_end_list::"endpt \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> endpt"
where
"prelim_other_end_list a [] = a"
|"prelim_other_end_list a (x#xs) = 
           (if ((prelim_other_end_list a xs) \<noteq> a) 
             then (prelim_other_end_list a xs) 
                 else (other_end a x))"

definition other_end_list ::"endpt \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> endpt"
where
"other_end_list a xs \<equiv> (if (prelim_other_end_list a xs = a)
                         then (dom (dom_Max_list (linearize xs) + 1)) 
                                   else (prelim_other_end_list a xs))"  

definition readjust::"endpt \<times> endpt \<Rightarrow> endpt \<times> endpt"
where
"readjust x \<equiv> (if ((fst x)=(snd x)) then (fst x,(dom (str_number (fst x) + 1))) else x)"

primrec delete_containing::"endpt \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"delete_containing a [] = []"
|"delete_containing a (x#xs) = (if ((fst x = a)\<or>(snd x = a)) 
                                then (delete_containing a xs)
                                        else (x#(delete_containing a xs)))" 

definition cup_check::"nat \<Rightarrow> (endpt \<times> endpt) list  \<Rightarrow> (endpt \<times> endpt) list"
where
"cup_check n xs =
split_codom_double_right_shift (\<lambda>x.(type x=codomain)\<and>(str_number x >(n+1))) 
([ (readjust (other_end_list (codom (n+1)) xs, other_end_list (codom n) xs))
, (readjust (other_end_list (codom n) xs, other_end_list (codom (n+1)) xs))]
@(delete_containing (codom (n+1)) (delete_containing (codom n) xs)))"

value "cup_check 1 [(codom 1, codom 3), (codom 3, codom 1), (codom 2, codom 4), (codom 4, codom 2)]"

(*return a blank list if the some condition is not satisfied and finish the function*)
definition cup_act::"nat \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"cup_act n xs \<equiv>
 (if  
    (belongs_to_list  (codom n, codom (n+1)) xs)
  then 
    split_codom_double_right_shift 
      (\<lambda>x.(type x=codomain)\<and>(str_number x > (n+1))) 
              (delete_from_list  (codom n, codom (n+1)) (delete_from_list  (codom (n+1), codom n) xs)) 
   else cup_check n xs)"

value "cup_act 1 [(codom 1, codom 3), (codom 3, codom 1), (codom 4, codom 2), (codom 2, codom 4)]"

primrec block_action::"block \<Rightarrow> (endpt \<times> endpt)  list \<times> nat  \<Rightarrow>  (endpt \<times> endpt) list \<times> nat"
where
"block_action [] ls = ls"
|"block_action (x#xs) ls = 
   (case x of
     vert \<Rightarrow> ((vert_act (nat (domain_block xs)+1) (fst (block_action xs  ls))),(snd (block_action xs  ls)))
    |over \<Rightarrow> ((swap_act (nat (domain_block xs)+1)  (fst (block_action xs  ls)),(snd (block_action xs  ls))))
|under \<Rightarrow> ((swap_act (nat (domain_block xs)+1)  (fst (block_action xs ls))),(snd (block_action xs  ls)))
|cap \<Rightarrow>    ((cap_act (nat (domain_block xs)+1)  (fst (block_action xs  ls))),(snd (block_action xs  ls)))
|cup \<Rightarrow> 
 ((cup_act (nat (domain_block xs)+1)  (fst (block_action xs  ls))),
  (if  
  ((belongs_to (codom (nat (domain_block xs)+1), codom ((nat (domain_block xs))+2))  
                                        (fst (block_action xs  ls)))
\<or>(belongs_to (codom (nat (domain_block xs)+2), codom ((nat (domain_block xs))+1))  
                                        (fst (block_action xs  ls))))

  then ((snd (block_action xs  ls))+1) else (snd (block_action xs  ls)))))"

value "block_action [vert] ([],0)"   

primrec wall_action::"wall \<Rightarrow> (endpt \<times> endpt)  list \<times> nat  \<Rightarrow>  (endpt \<times> endpt) list \<times> nat"
where
"wall_action (basic x) ls = block_action x ls"
|"wall_action (w*ws) ls = block_action w (wall_action ws ls)"

definition component_number::"wall \<Rightarrow> nat"
where 
"(component_number w) \<equiv> snd (wall_action w ([],0))"

(*,antireflexive,linear,injective*)
(*
primrec symmetric::"('a \<times> 'a) list \<Rightarrow> bool"
where
"symmetric [] = True"
|"symmetric (x#xs) = (belongs_to (snd x,fst x) xs)"
*)
(*new definitions*)


definition codom_set_filter::"(endpt \<times> endpt) set \<Rightarrow> nat set"
where
"codom_set_filter xs \<equiv> {n. \<exists>x.((x,codom n) \<in> xs)\<or>((codom n, x) \<in> xs)}"


definition dom_set_filter::"(endpt \<times> endpt) set \<Rightarrow> nat set"
where
"dom_set_filter xs \<equiv> {n. \<exists>x.((x,dom n) \<in> xs)\<or>((dom n, x) \<in> xs)}"

lemma "codom_set_filter {(codom 1, dom 0), (codom 2, codom 3),(codom 5, codom 6)} = {1,2,3,5,6}"
 using codom_set_filter_def by auto  


lemma "dom_set_filter {(codom 1, dom 0), (codom 2, codom 3),(codom 5, dom 6)} = {0,6}"
 using dom_set_filter_def by auto  

definition max_codom::"(endpt \<times> endpt) set \<Rightarrow> nat"
where
"max_codom xs \<equiv> (if (xs = {}) then 0 else Max (codom_set_filter xs))"


definition max_dom::"(endpt \<times> endpt) set \<Rightarrow> nat"
where
"max_dom xs \<equiv>  (if (xs = {}) then 0 else Max (codom_set_filter xs))"

lemma "max_codom {(codom 1,codom 2), (codom 3, dom 4)} = 3"
proof-
     have 1:"codom_set_filter {(codom 1,codom 2), (codom 3, dom 4)} = {1,2,3}"
                using codom_set_filter_def by auto
     then show ?thesis using max_codom_def 1 by auto       
qed

definition replace_if_with::"endpt \<Rightarrow> endpt \<Rightarrow> endpt \<Rightarrow> endpt"
where
"replace_if_with x i j  \<equiv> (if (x = i) then j else  x)"

lemma "replace_if_with i i j = j"
      using replace_if_with_def by auto
  
primrec replace_in::"endpt \<Rightarrow> endpt \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"replace_in i j []=  []"|
"replace_in i j (x#xs) =  (replace_if_with (fst x) i j,replace_if_with (snd x) i j)
                                     #(replace_in i j xs)"

primrec block_act::"block \<Rightarrow> (endpt \<times> endpt)  set"
where
"block_act []  = {}"
|"block_act (x#xs) = 
   (case x of
     vert \<Rightarrow> {(codom ((max_codom (block_act xs))+1), dom (max_dom (block_act xs)+1))}
                        \<union>(block_act xs)
    |over \<Rightarrow> {(codom ((max_codom (block_act xs))+1), dom ((max_dom (block_act xs))+2))
               ,(codom ((max_codom (block_act xs))+2), dom ((max_dom (block_act xs))+1))}
               \<union>(block_act xs)
    |under \<Rightarrow> {(codom ((max_codom (block_act xs))+1), dom ((max_dom (block_act xs))+2))
               ,(codom ((max_codom (block_act xs))+2), dom ((max_dom (block_act xs))+1))}
               \<union>(block_act xs)
    |cup \<Rightarrow>  {(codom ((max_codom (block_act xs))+2),codom ((max_codom (block_act xs))+1))}
               \<union>(block_act xs) 
    |cap \<Rightarrow>  {(dom ((max_dom (block_act xs))+2), dom ((max_dom (block_act xs))+1))}
               \<union>(block_act xs))"

value "Max {}"
lemma "block_act [vert] = {(codom 1, dom 1)}"
     proof-
 have "block_act [vert] = {(codom ((max_codom {})+1), dom (max_dom  {}+1))}
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

definition endpt_act::"(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set"
where
"endpt_act xs ys \<equiv> {(codom m, codom n) | m n. (codom m, codom n) \<in> xs} 
                    \<union> {(dom m, dom n) | m n. (dom m, dom n) \<in> xs} 
                      \<union> {(codom m, codom n) | m n k1 k2. (((codom m, dom k1) \<in> connect xs ys)
                                            \<and> ((dom k1, dom k2) \<in> connect xs ys) \<and> 
                                              ((dom k2, codom n) \<in> connect xs ys))}  "
                       
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
 *)
end 
