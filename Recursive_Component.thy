theory Recursive_Component
imports Link_Algebra
begin


datatype endtype = domain|codomain

type_synonym endpt = "endtype \<times> nat"
(*
primrec nat_count::"nat \<Rightarrow> nat list \<Rightarrow> nat"
where
"nat_count n [] = 0"|
"nat_count n (x#xs) = (if (n=x) then 1 else 0) + (nat_count n xs)"
*)

definition dom::"nat \<Rightarrow> endpt"
where
"dom n \<equiv> (domain, n)"


definition codom::"nat \<Rightarrow> endpt"
where
"codom n \<equiv> (codomain, n)"

definition type::"endpt \<Rightarrow> endtype"
where
"type x = (fst x)"

definition str_number::"endpt \<Rightarrow> nat"
where
"str_number x = (snd x)"

primrec codomain_split_readjust::"endpt list \<Rightarrow>nat \<Rightarrow> endpt list"
where
"codomain_split_readjust [] n = []"
|"codomain_split_readjust (x#xs) n = 
    (case (type x) of codomain \<Rightarrow> (codom ((snd x)+2))#(codomain_split_readjust xs n)
              |domain \<Rightarrow> (x#(codomain_split_readjust xs n)))"


primrec codomain_split_decrease::"endpt list \<Rightarrow>nat \<Rightarrow> endpt list"
where
"codomain_split_decrease [] n = []"
|"codomain_split_decrease (x#xs) n = 
    (case (type x) of codomain \<Rightarrow> (codom ((snd x)- 2))#(codomain_split_readjust xs n)
              |domain \<Rightarrow> (x#(codomain_split_readjust xs n)))"

primrec Max_list::"endpt list \<Rightarrow> nat"
where
"Max_list [] = 0"|
"Max_list (Cons x xs) = (case (type x) of domain \<Rightarrow> (max (snd x) (Max_list xs))|codomain\<Rightarrow> (Max_list xs))"

primrec Min_list::"endpt list \<Rightarrow> nat"
where
"Min_list [] = 0"|
"Min_list (Cons x xs) 
   = (case (type x) of domain \<Rightarrow> (min (snd x) (Min_list xs))|codomain\<Rightarrow> (Min_list xs))"

primrec replace::"endpt \<Rightarrow> endpt \<Rightarrow> endpt list \<Rightarrow> endpt list"
where
"replace i j []=  []"|
"replace i j (x#xs) =  (if (x = j) then i else x)#(replace i j xs)"


primrec swap::"endpt \<Rightarrow> endpt \<Rightarrow> endpt list \<Rightarrow> endpt list"
where
"swap i j []=  []"|
"swap i j (x#xs) =  (if (x = j) then i else if (x=i) then j else x)#(swap i j xs)"


definition vert_act::"int \<Rightarrow>endpt list \<Rightarrow> endpt list"
where
"vert_act n xs \<equiv> (if ((length xs)>nat n) then
 (dom (Max_list xs))#(xs) 
 else (xs))"

lemma "take 1 (3#(1#[])) =[3] "
 by auto

definition swap_act::"int \<Rightarrow> endpt list \<Rightarrow> endpt list"
where
"swap_act n xs \<equiv>  
 (if ((nat n) \<ge> (length xs) )
                 then 
([(dom (Max_list (xs) + 1)),(dom (Max_list (xs) + 2))]@xs)
             else
(if (1+ (nat n)) = (length xs) 
                            then  [(xs)!0,(dom (Max_list (xs) + 1))]
                                   @(replace (xs!0) (dom (Max_list (xs) + 1)) (drop 1 (xs)))
                else 
(swap ((drop ((length xs)-(nat n) - 2) xs)!1) ((drop ((length xs)-(nat n) - 2) xs)!0)  
(take ((length xs) - (nat n) - 2) xs))
@[(drop ((length xs)-(nat n) - 2) xs)!1,(drop ((length xs)-(nat n) - 2) xs)!0]
@ (swap ((drop ((length xs)-(nat n) - 2) xs)!1) ((drop ((length xs)-(nat n) - 2) xs)!0)  
(drop ((length xs)-(nat n)) xs))))"


(*insert list- it inserts a list at nth position to the right*)
definition insert_list::"nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
 where
 "insert_list n xs ys \<equiv> (take n xs)@(ys@(drop n xs))"

(*create a list to factor codoms, then create a list to add two to it*)
(*cup action is given by adding two new strands if the input list contains lesser number of elements 
than a given integer n else it adds two new strands in the middle of the list*)
definition cup_act::"int \<Rightarrow> endpt list \<Rightarrow> endpt list"
where
"cup_act n xs \<equiv>  (insert_list 
       ((length xs) - (nat n)) 
     (codomain_split_readjust  xs (nat n)) 
[codom (Max_list (drop ((length xs)- (nat n)) xs)+1),codom (Max_list (drop ((length xs)-(nat n)) xs)+1)])"

definition cap_act::"int\<Rightarrow> endpt list\<Rightarrow> endpt list"
where
"cap_act n xs \<equiv> 
 (if ((length xs) \<le> nat n) 
         then xs
            else 
                (if ((length xs)= ((nat n)+1))
                       then (drop 1 xs)
                         else 
(codomain_split_decrease ((replace (codom ((length xs) - (nat n) - 2)) (xs!((length xs)- (nat n) - 2)) 
  ((take ((length xs)- (nat n) - 2) xs)@(drop ((length xs) - (nat n)) xs)))) (nat n))))"

definition adjacency::"endpt \<Rightarrow> endpt \<Rightarrow> endpt list \<Rightarrow> bool"
where
"adjacency a b xs \<equiv> (if (\<exists>n.((xs!n)=a) \<longrightarrow> ((xs!(n+1) = b)\<or>((xs!(n+1)) = b))) 
                        then True
                          else False)"

(*the over strand checks if the number of incoming strands are more than the codomain of the adjacent
block and then subsequently either morphs, adds or permutes the strands*)
primrec block_action::"block \<Rightarrow> (endpt  list) \<times> nat  \<Rightarrow>  (endpt list) \<times> nat"
where
"block_action [] ls = ([],snd ls)"
|"block_action (x#xs) ls = 
   (case x of
     vert \<Rightarrow> ((vert_act  (codomain_block xs) (fst (block_action xs  ls))),(snd ls))
    |over \<Rightarrow> ((swap_act (codomain_block xs)  (fst (block_action xs  ls)),(snd ls)))
|under \<Rightarrow> ((swap_act (codomain_block xs)  (fst (block_action xs ls))),(snd ls))
|cup \<Rightarrow>    ((cup_act (codomain_block xs)  (fst (block_action xs  ls))),(snd ls))
|cap \<Rightarrow>  ((cap_act  (codomain_block xs)  (fst (block_action xs  ls))), 
 if (adjacency (codom (nat (codomain_block xs))) (codom (nat ((codomain_block xs))+1)) (fst (block_action xs  ls)))
       then ((snd ls)+1) else (snd ls)))"
   
primrec wall_action::"wall \<Rightarrow> (endpt)  list \<times> nat  \<Rightarrow>  (endpt) list \<times> nat"
where
"wall_action (basic x) ls = block_action x ls"
|"wall_action (w*ws) ls = block_action w (wall_action ws ls)"

definition component_number::"wall \<Rightarrow> nat"
where 
"(component_number w) \<equiv> snd (wall_action w ([],0))"
   
end
