theory Rec_Comp
imports Link_Algebra
begin


(*we begin by defining two different types of an end of a strand, domain refers to the fact the 
other end of a strand lies in the domain of the wall and codomain refers to the fact that other end
of a strand lies in the codomain*) 
datatype endtype = domain|codomain

(*endpoint of a strand is given by the type of the end point and a natural number which refers
to the  position of the other end of the strand*)  
type_synonym endpt = "endtype \<times> nat"

(*The following functions are used to abbreviate (domain, n) and (codomain, n) as (dom n) and 
(codom n). The reason behind introducing these functions is purely for the sake of 
comprehensibility of the code*)

definition dom::"nat \<Rightarrow> endpt"
where
"dom n \<equiv> (domain, n)"

definition codom::"nat \<Rightarrow> endpt"
where
"codom n \<equiv> (codomain, n)"

(*the function type tells us the endtype of an endpt*)
definition type::"endpt \<Rightarrow> endtype"
where
"type x = (fst x)"
(*the function str_number tells us the strand number of an endpt*)
definition str_number::"endpt \<Rightarrow> nat"
where
"str_number x = (snd x)"

primrec dom_Max_list::"endpt list \<Rightarrow> nat"
where
"dom_Max_list [] = 0"|
"dom_Max_list (Cons x xs) = (case (type x) of 
                                             domain \<Rightarrow> (max (snd x) (dom_Max_list xs))
                                             |codomain\<Rightarrow> (dom_Max_list xs))"
(*we define functions related to shifting of the codomain and domain*)
definition codom_left_shift::"(endpt \<Rightarrow> bool) \<Rightarrow> endpt \<Rightarrow> endpt"
where
"codom_left_shift P x \<equiv>(if ((type x = codomain)\<and> (P x)) then (codom (snd x +1)) else x)"


abbreviation codom_double_left_shift::"(endpt\<Rightarrow> bool) \<Rightarrow> endpt \<Rightarrow> endpt"
where
"codom_double_left_shift P x \<equiv>(if ((type x = codomain)\<and> (P x)) then (codom (snd x +2)) else x)"

definition codom_double_left_shift_tuple::"(endpt\<Rightarrow>bool)\<Rightarrow> (endpt \<times> endpt) \<Rightarrow> (endpt \<times> endpt)"
where
"codom_double_left_shift_tuple P x \<equiv>
    (codom_double_left_shift P (fst x),codom_double_left_shift P (snd x))  "
   

primrec split_codom_double_left_shift::"(endpt \<Rightarrow> bool) \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
 where
"split_codom_double_left_shift P [] = []"
|"split_codom_double_left_shift P (x#xs) = (codom_double_left_shift_tuple P x)#xs  "


(*right shift*)
definition codom_right_shift::"(endpt \<Rightarrow> bool) \<Rightarrow> endpt \<Rightarrow> endpt"
where
"codom_right_shift P x \<equiv>(if ((type x = codomain)\<and> (P x)) then (codom (snd x- 1)) else x)"


abbreviation codom_double_right_shift::"(endpt\<Rightarrow> bool) \<Rightarrow> endpt \<Rightarrow> endpt"
where
"codom_double_right_shift P x \<equiv>(if ((type x = codomain)\<and> (P x)) then (codom (snd x- 2)) else x)"

definition codom_double_right_shift_tuple::"(endpt\<Rightarrow>bool)\<Rightarrow> (endpt \<times> endpt) \<Rightarrow> (endpt \<times> endpt)"
where
"codom_double_right_shift_tuple P x \<equiv>
    (codom_double_right_shift P (fst x),codom_double_right_shift P (snd x))  "
   

primrec split_codom_double_right_shift::"(endpt \<Rightarrow> bool) \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
 where
"split_codom_double_right_shift P [] = []"
|"split_codom_double_right_shift P (x#xs) = (codom_double_right_shift_tuple P x)#xs  "
(*the following function gives us n such that n is the maximum number assigned to an end of 
a type codomain*)
primrec codom_Max_list::"endpt list \<Rightarrow> nat"
where
"codom_Max_list [] = 0"|
"codom_Max_list (Cons x xs) = (case (type x) of 
                                               codomain \<Rightarrow> (max (snd x) (codom_Max_list xs))
                                              |domain\<Rightarrow> (codom_Max_list xs))"

(*If one of the two elements of a tuple is i then it replaces is with j*)
definition swap_with::"endpt \<Rightarrow> endpt \<Rightarrow> endpt \<Rightarrow> endpt"
where
"swap_with x i j  \<equiv> (if (x = i) then j else if (x = j) then i else x)"

primrec swap_in::"endpt \<Rightarrow> endpt \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"swap_in i j []=  []"|
"swap_in i j (x#xs) =  (swap_with (fst x) i j,swap_with (snd x) i j)#(swap_in i j xs)"

(*we check if a given element belongs to a given list of 2-tuples of endpts*)
primrec find::"endpt \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> bool"
where
"find x [] = False"|
"find x (y#ys) = (if (find x ys) then True else (((fst y) = x)\<or>((snd  y) = x)))"

(* we check if two given elements belong to the list*)
definition find_both::"endpt \<Rightarrow> endpt \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> bool"
where
"find_both x y zs \<equiv> (if (find x zs) then (find y zs) else False)"

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
    else  (codom (codom_Max_list (linearize xs) +1 ), dom (dom_Max_list (linearize xs) + 1))#xs)"
 
definition swap_act::"nat \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"swap_act n xs \<equiv>
 (if (find_both (codom n) (codom (n+1)) xs)
      then (swap_in (codom n) (codom (n+1)) xs)
           else if (find (codom n) xs)
              then ((dom ((dom_Max_list (linearize xs))+1), codom n)#swap_in (codom n) (codom (n+1)) xs)
                  else 
[(dom (dom_Max_list (linearize xs)+2),codom n),((dom (dom_Max_list (linearize xs)+1),codom (n+1)))]
                          @xs)  " 
   
definition cup_act::"nat \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"cup_act n xs \<equiv> 
(codom n, codom (n+1))#(split_codom_double_left_shift (\<lambda>x.(type x=codomain)\<and>(snd x>n)) xs)"

definition belongs_to::"'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
"belongs_to a xs \<equiv> a \<in> set xs"

primrec delete_from_list::"'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
"delete_from_list a [] = []"|
"delete_from_list a (x#xs) = (if (x=a) then (delete_from_list a xs) else (x#(delete_from_list a xs)))"


(*it adds nat option to nat*)
primrec nat_option_add::"nat\<Rightarrow>nat option\<Rightarrow> nat option" (infixl "+" 67)
where
"nat_option_add n None = None"
|"nat_option_add n (Some m) = (Some (m+n))"

(*it gives us Some n if a accurs in the list at the nth position*)
primrec first_occurance::"endpt \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> nat option"
where
"first_occurance a [] = None"
|"first_occurance a (x#xs) = (if (((fst x)= a)\<or>((snd x)=a)) then Some 0 else  (1+first_occurance a xs))"
 
(*if a is one of the two elements, then the following gives the other coefficient of the tuple else it gives
the same element*) 
definition other_end::" endpt \<Rightarrow>  (endpt \<times> endpt) \<Rightarrow> endpt"
where
"other_end a x \<equiv> (if (fst x)= a then (snd x) else if (snd  x = a) then (fst x) else a)"


(*if a is one of the two elements, then the following gives other coefficient of the tuple in the first
occurance  else it returns the same element*) 
primrec other_end_list::"endpt \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> endpt"
where
"other_end_list a [] = a"
|"other_end_list a (x#xs) = 
           (if ((other_end_list a xs) \<noteq> a) then (other_end_list a xs) else (other_end a x))" 

(*It deletes every tuple in the list which contains the element as one of the constituent elements of
the tuple*)
primrec delete_containing::"endpt \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"delete_containing a [] = []"
|"delete_containing a (x#xs) = (if ((fst x = a)\<or>(snd x = a)) 
                                then (delete_containing a xs)
                                        else (x#(delete_containing a xs)))" 

definition cap_check::"nat \<Rightarrow> (endpt \<times> endpt) list  \<Rightarrow> (endpt \<times> endpt) list"
where
"cap_check n xs = (other_end_list (codom n) xs, other_end_list (codom (n+1)) xs)
                     #( split_codom_double_right_shift  (\<lambda>x.(type x=codomain)\<and>(snd x>(n+1))) (delete_containing (codom (n+1)) (delete_containing (codom n) xs)))"

(*return a blank list if the some condition is not satisfied and finish the function*)
definition cap_act::"nat \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"cap_act n xs \<equiv>
 (if  (belongs_to (codom n, codom (n+1)) xs)
  then  split_codom_double_right_shift  (\<lambda>x.(type x=codomain)\<and>(snd x>(n+1))) 
                         (delete_from_list (codom n, codom (n+1)) xs) 
   else cap_check n xs)"

primrec block_action::"block \<Rightarrow> (endpt \<times> endpt)  list \<times> nat  \<Rightarrow>  (endpt \<times> endpt) list \<times> nat"
where
"block_action [] ls = ([],snd ls)"
|"block_action (x#xs) ls = 
   (case x of
     vert \<Rightarrow> ((vert_act (nat (codomain_block xs)) (fst (block_action xs  ls))),(snd ls))
    |over \<Rightarrow> ((swap_act (nat (codomain_block xs))  (fst (block_action xs  ls)),(snd ls)))
|under \<Rightarrow> ((swap_act (nat (codomain_block xs))  (fst (block_action xs ls))),(snd ls))
|cup \<Rightarrow>    ((cup_act (nat (codomain_block xs))  (fst (block_action xs  ls))),(snd ls))
|cap \<Rightarrow>  ((cap_act (nat (codomain_block xs))  (fst (block_action xs  ls))),
 (if  (belongs_to (codom (nat (codomain_block xs)), codom ((nat (codomain_block xs))+1)) (fst ls))
  then ((snd ls)+1) else (snd ls))))"
   
primrec wall_action::"wall \<Rightarrow> (endpt \<times> endpt)  list \<times> nat  \<Rightarrow>  (endpt \<times> endpt) list \<times> nat"
where
"wall_action (basic x) ls = block_action x ls"
|"wall_action (w*ws) ls = block_action w (wall_action ws ls)"

definition component_number::"wall \<Rightarrow> nat"
where 
"(component_number w) \<equiv> snd (wall_action w ([],0))"
