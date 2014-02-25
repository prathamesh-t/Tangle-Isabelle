theory Components
imports Tangles
begin

primrec Max_list::"nat list \<Rightarrow> nat"
where
"Max_list [] = 0"|
"Max_list (Cons x xs) = (max x (Max_list xs))"

primrec Min_list::"nat list \<Rightarrow> nat"
where
"Min_list [] = 0"|
"Min_list (Cons x xs) = (min x (Max_list xs))"

primrec replace_in_list::"nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list"
where
"replace_in_list i j []=  []"|
"replace_in_list i j (x#xs) =  (if (x = j) then i else x)#(replace_in_list i j xs)"

definition cup_detect::"brick \<Rightarrow> int"
where 
" cup_detect x = (if (x = cup) then 1 else 0)"

primrec cup_count::"block \<Rightarrow> int"
where
"cup_count (cement x) = cup_detect x"|
"cup_count (cons x xs) = (cup_detect x)+(cup_count xs)"

primrec strand_path::"brick \<Rightarrow> nat \<Rightarrow> nat list \<times> nat list  \<Rightarrow> nat list \<times> nat list "
where
"strand_path vert n x = x "|
"strand_path cap n x = ((take n (fst x)@[(Max_list (fst x)) + 1, (Max_list (fst x)) + 1] 
@(drop n (fst x))),snd x)" |
"strand_path under n x=  ((take n (fst x))@[((fst x)!(n+2)),((fst x)!(n+1))]@(drop (n+2) (fst x)),
(snd x)) "|
"strand_path over n x=  ((take n (fst x))@[((fst x)!(n+2)),((fst x)!(n+1))]@(drop (n+2) (fst x))
, (snd x))"|
"strand_path cup n x=  
((replace_in_list (min ((fst x)!n) ((fst x)!n+1)) (max ((fst x)!n) 
((fst x)!n+1)) ((take n (fst x))@(drop (n+2) (fst x)))), 
(min ((fst x)!n) ((fst x)!n+1))#(replace_in_list (min ((fst x)!n) ((fst x)!n+1)) (max ((fst x)!n) ((fst x)!n+1)) 
(snd x))) "


primrec strand_block_path::"block \<Rightarrow> nat list \<times> nat list \<Rightarrow> nat list \<times> nat list"
where
"strand_block_path (cement y) x =  (strand_path y 0 x)"|
"strand_block_path (cons y ys) x = (strand_path y (nat ((fst (count ys))- 2*(cup_count ys)))
  (strand_block_path ys x))" 

primrec strand_wall_path::"walls \<Rightarrow> nat list \<times> nat list \<Rightarrow> nat list \<times> nat list"
where
"strand_wall_path (basic z) x = (strand_block_path z x)"|
"strand_wall_path (prod z zs) xs = (strand_block_path z ((strand_wall_path zs xs)))"
 
definition component_number::"walls \<Rightarrow> nat"
where
"component_number L = card (set (snd (strand_wall_path L ([],[]))))"

theorem  example1:"strand_wall_path ((cons cup (cement cup))*((cons vert (cons over (cement vert)))
*(basic (cons cap (cement cap))))) ([],[]) = ([],[1,1])"
proof-
have "strand_block_path (cement cap) ([],[]) =  (strand_path cap  0 ([],[]))"
by auto
have "(strand_path cap  0 ([],[])) = ([1,1],[])" by auto
have "strand_block_path (cons cap (cement cap)) ([],[]) 
= (strand_path cap (nat ((fst (count (cement cap))) - 2*(cap_detec (strand_path cap  0 ([],[])))"

