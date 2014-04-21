theory Rec_Comp
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


(*the function str_number tells us the strand number of an endpt*)
definition str_number::"endpt \<Rightarrow> nat"
where
"str_number x = (case x of dom n \<Rightarrow> n|codom n \<Rightarrow> n)"

(*the following function tells us the maximum strand number in a list which is of the type dom*)
primrec dom_Max_list::"endpt list \<Rightarrow> nat"
where
"dom_Max_list [] = 0"|
"dom_Max_list (Cons x xs) = (case (type x) of 
                                             domain \<Rightarrow> (max (str_number x) (dom_Max_list xs))
                                             |codomain\<Rightarrow> (dom_Max_list xs))"
(*the following function gives us n such that n is the maximum number assigned to an end of 
a type codomain*)
primrec codom_Max_list::"endpt list \<Rightarrow> nat"
where
"codom_Max_list [] = 0"|
"codom_Max_list (Cons x xs) = (case (type x) of 
                                               codomain \<Rightarrow> (max (str_number x) (codom_Max_list xs))
                                              |domain\<Rightarrow> (codom_Max_list xs))"


(*we define functions related to shifting of the codomain and domain by 1/2 strands to left*)
definition codom_left_shift::"(endpt \<Rightarrow> bool) \<Rightarrow> endpt \<Rightarrow> endpt"
where
"codom_left_shift P x \<equiv>(if ((type x = codomain)\<and> (P x)) then (codom (str_number x +1)) else x)"


abbreviation codom_double_left_shift::"(endpt\<Rightarrow> bool) \<Rightarrow> endpt \<Rightarrow> endpt"
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
|"split_codom_double_right_shift P (x#xs) = (codom_double_right_shift_tuple P x)#
(split_codom_double_right_shift P xs)  "

value 
"codom_double_right_shift_tuple  (\<lambda>x.(str_number x>2)) (codom 5, codom 6)"

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
    else  (dom (dom_Max_list (linearize xs) + 1), codom (codom_Max_list (linearize xs) +1))#xs)"
 
definition swap_act::"nat \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"swap_act n xs \<equiv>
 (if (find_both (codom n) (codom (n+1)) xs)
      then (swap_in (codom n) (codom (n+1)) xs)
           else if (find (codom n) xs)
              then ((dom ((dom_Max_list (linearize xs))+1), codom n)#swap_in (codom n) (codom (n+1)) xs)
                  else 
[(dom (dom_Max_list (linearize xs)+2),codom n),((dom (dom_Max_list (linearize xs)+1),codom (n+1)))]
                          @xs)" 

definition str_number_geq_n::"nat \<Rightarrow> endpt \<times> endpt  \<Rightarrow> bool"
where
"str_number_geq_n n x \<equiv> (str_number (fst x) \<ge> n)"   

definition cap_act::"nat \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"cap_act n xs \<equiv> 
(takeWhile  ((str_number_geq_n n))  (split_codom_double_left_shift (\<lambda>x.(type x=codomain)\<and>(str_number x \<ge> n)) xs))
@ (codom n, codom (n+1))#(dropWhile ((str_number_geq_n n)) (split_codom_double_left_shift (\<lambda>x.(type x=codomain)\<and>(str_number x \<ge> n)) xs))"

definition belongs_to::"'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
"belongs_to a xs \<equiv> a \<in> set xs"

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
 (readjust (other_end_list (codom n) xs, other_end_list (codom (n+1)) xs)
#(delete_containing (codom (n+1)) (delete_containing (codom n) xs)))"

(*return a blank list if the some condition is not satisfied and finish the function*)
definition cup_act::"nat \<Rightarrow> (endpt \<times> endpt) list \<Rightarrow> (endpt \<times> endpt) list"
where
"cup_act n xs \<equiv>
 (if  
    ((belongs_to (codom n, codom (n+1)) xs)\<or>(belongs_to (codom (n+1), codom n) xs))
  then 
    split_codom_double_right_shift 
      (\<lambda>x.(type x=codomain)\<and>(str_number x > (n+1))) 
              (delete_from_list  (codom n, codom (n+1)) (delete_from_list  (codom (n+1), codom n) xs)) 
   else cup_check n xs)"

primrec block_action::"block \<Rightarrow> (endpt \<times> endpt)  list \<times> nat  \<Rightarrow>  (endpt \<times> endpt) list \<times> nat"
where
"block_action [] ls = ls"
|"block_action (x#xs) ls = 
   (case x of
     vert \<Rightarrow> ((vert_act (nat (domain_block xs)+1) (fst (block_action xs  ls))),(snd (block_action xs  ls)))
    |over \<Rightarrow> ((swap_act (nat (domain_block xs)+1)  (fst (block_action xs  ls)),(snd (block_action xs  ls))))
|under \<Rightarrow> ((swap_act (nat (domain_block xs)+1)  (fst (block_action xs ls))),(snd (block_action xs  ls)))
|cap \<Rightarrow>    ((cap_act (nat (domain_block xs)+1)  (fst (block_action xs  ls))),(snd (block_action xs  ls)))
|cup \<Rightarrow>  ((cup_act (nat (domain_block xs)+1)  (fst (block_action xs  ls))),
 (if  
((belongs_to (codom (nat (domain_block xs)+1), codom ((nat (domain_block xs))+2))  (fst (block_action xs  ls)))
\<or>(belongs_to (codom (nat (domain_block xs)+2), codom ((nat (domain_block xs))+1))  (fst (block_action xs  ls))))

  then ((snd (block_action xs  ls))+1) else (snd (block_action xs  ls)))))"
   
primrec wall_action::"wall \<Rightarrow> (endpt \<times> endpt)  list \<times> nat  \<Rightarrow>  (endpt \<times> endpt) list \<times> nat"
where
"wall_action (basic x) ls = block_action x ls"
|"wall_action (w*ws) ls = block_action w (wall_action ws ls)"

definition component_number::"wall \<Rightarrow> nat"
where 
"(component_number w) \<equiv> snd (wall_action w ([],0))"

(*
" left_over \<equiv> ((basic (cup#vert#[])) \<circ> (basic (vert#over#[]))
\<circ> (basic (cap#vert#[])))"*)
(*((basic (vert#cup#[])) \<circ> (basic (under#vert#[])) \<circ>  (basic (vert#cap#[]))) *)

value "cap_act 3 ([(codom 3, codom 4), (codom 1, codom 2)])"
(*
*)
value "wall_action  (basic (cup#[])) ([(endpt.dom 1, codom 2), (codom 1, codom 3)], 0)"
value "(dom 1, codom 1) = (codom 1, dom 1)"
value "wall_action right_over ([],0)  "
value "wall_action (basic (cup#vert#[])) ([(codom 1, codom 3), (endpt.dom 1, codom 2)], 0)"
value "cup_check 2 ([(codom 1, codom 3), (endpt.dom 1, codom 2)])"
value "(delete_containing (codom (3)) (delete_containing (codom 2)  ([(codom 1, codom 3), (endpt.dom 1, codom 2)]))) "
value "other_end_list (codom 3) [(codom 1, codom 3), (endpt.dom 1, codom 2)]"
value "prelim_other_end_list (codom 3) [(codom 1, codom 3), (endpt.dom 1, codom 2)]"


(*
" left_over \<equiv> ((basic (cup#vert#[])) \<circ> (basic (vert#over#[]))
\<circ> (basic (cap#vert#[])))"*)
(*((basic (vert#cup#[])) \<circ> (basic (under#vert#[])) \<circ>  (basic (vert#cap#[]))) *)

value "wall_action left_over ([(codom 3, codom 2)],0)"
value "wall_action ((basic (vert#over#[]))\<circ>(basic (cap#vert#[])))  ([(codom 3, codom 2)],0)"
value "wall_action right_over ([(codom 3, codom 2)],0)"
value "wall_action r_over_braid ([],0) = wall_action l_over_braid ([],0)"
value "wall_action ((basic (vert#cup#[]))\<circ>(basic (cap#vert#[]))) ([],0)"
value "wall_action ((basic (cup#vert#[]))\<circ>(basic (vert#cap#[]))) ([],0)"
(*figure 8 knot*)
value "wall_action ([cup,cup]*[vert,over,vert]*[vert,over,vert]*[under,over]*[vert,cap,vert]*
[vert,cup,vert]*[over,over]*[vert,cap,vert]*(basic [cap]))
([],0)"

value "wall_action (basic [cup]) ([(codom 2, codom 1)], 0)"
value "cup_check 1 [(dom 1, codom 1)]"
value "block_action [cup,cap,cup] ([],0)"
value "wall_action ([cap,cap,cap]*(basic [cup,cup,cup])) ([],0)"
value "wall_action ([cap,vert,vert]*(basic [cap,cap])) ([],0)"
(*imp examples for modifying cup-cap*)
value "wall_action (([cup,cap,vert,vert]*(basic [cap,cap]))) ([],0)"
value "wall_action (([cup,cup]*(basic [cup,vert,vert,cup,vert,vert]) )) ([],0)"

(*hopf link has two components*)
value "wall_action ([cup,cup]*[vert,over,vert]*[vert,over,vert]*(basic [cap,cap])) ([],0)"
(*unknot diagram with a cross1ing has a single component*)
value "wall_action ([cup,cup]*[vert,over,vert]*(basic [cap,cap])) ([],0)"
value "wall_action ([cup]*[cap,cap]*[cap,cap]*(basic [cap,cap])) ([],0)"

value "block_action [cup] ([(codom 5, codom 6), (codom 3, codom 4), (codom 1, codom 2)], 0)"
value "block_action [cup] ([(codom 3, codom 4), (codom 1, codom 2)],4)"
value " (belongs_to (codom (nat (domain_block [cup])+1), codom ((nat (domain_block [cup]))+2)) (fst ([(codom 1, codom 2)], 1)))"

(*"([(endpt.dom 5, codom 7), (endpt.dom 4, codom 5), (endpt.dom 3, codom 6), (endpt.dom 2, codom 3),
   (endpt.dom 1, codom 4), (codom 1, codom 2)],*)
value "(codom (nat (domain_block [cup])+1), codom ((nat (domain_block [cup]))+2))"
value "block_action ([vert,cup]) ([],0)"
value "block_action [cup] ([(codom 1, codom 2)], 1)"
value "block_action [vert] ([(codom 1, codom 2)], 0)"
value "block_action [cup] ([(codom 3, codom 4), (codom 1, codom 2)], 0)"
value "(find_both  (codom 1) (codom 2) [(endpt.dom 2, codom 1), (endpt.dom 1, codom 2)])"
value "(swap_act 1 (swap_act 1 []))"
value "swap_act 1 ([(endpt.dom 2, codom 1), (endpt.dom 1, codom 2)])"
value "cup_act 0 [(codom 2, codom 3), (codom 0, codom 1)]"
value "block_action  [cup] ([(codom 2, codom 3), (codom 0, codom 1)], 0)"

value "(delete_from_list (codom 1, codom 0) [(codom 2, codom 3), (codom 0, codom 1)])" 

locale swap= assumes
swap:"(x::endpt \<times> endpt) = (snd x, fst x)"
begin

value "wall_action left_over ([],0)"
lemma "wall_action left_over ([],0)  = wall_action right_over ([],0) "
proof-
 have " wall_action left_over ([],0) = ([(endpt.dom 1, codom 1)], 0)"
       by eval
 moreover have "wall_action right_over ([],0)  = ([(endpt.codom 1, dom 1)], 0)"
       by eval
 moreover have "(endpt.dom 1, codom 1) = (endpt.codom 1, dom 1)"
       using swap by (metis (full_types) fst_conv snd_conv)  
 ultimately show ?thesis by auto
qed
end
