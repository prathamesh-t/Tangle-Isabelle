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


lemma endpt_reconstruction: "(x = (if ((type x)= domain) then dom (str_number x) else codom (str_number x)))"
      unfolding type_def str_number_def 
      using  endpt.exhaust endpt.simps(5) endpt.simps(6) endtype.distinct(1) by (metis)


(*codom tuple and dom tuple*)
definition codom_tuple::"(endpt \<times> endpt)  \<Rightarrow> bool"
where
"codom_tuple x \<equiv> (type (fst x) = codomain)\<and>(type (snd x) = codomain)"

definition dom_tuple::"(endpt \<times> endpt)  \<Rightarrow> bool"
where
"dom_tuple x \<equiv> (type (fst x) = domain)\<and>(type (snd x) = domain)"

(*defining maximum of codom elements and dom elements *)
definition codom_set_filter::"(endpt \<times> endpt) set \<Rightarrow> nat set"
where
"codom_set_filter xs \<equiv> {n. \<exists>x.((x,codom n) \<in> xs)\<or>((codom n, x) \<in> xs)}"

definition dom_set_filter::"(endpt \<times> endpt) set \<Rightarrow> nat set"
where
"dom_set_filter xs \<equiv> {n. \<exists>x.((x,dom n) \<in> xs)\<or>((dom n, x) \<in> xs)}"


lemma "codom_set_filter {(codom 1, dom 0), (codom 2, codom 3),(codom 5, codom 6)} = {1,2,3,5,6}"
 using codom_set_filter_def by auto  

lemma empty_set_codom_set_filter: "codom_set_filter {}  = {}"
     using codom_set_filter_def by auto

lemma empty_set_dom_set_filter: "dom_set_filter {}  = {}"
     using dom_set_filter_def by auto

lemma "dom_set_filter {(codom 1, dom 0), (codom 2, codom 3),(codom 5, dom 6)} = {0,6}"
 using dom_set_filter_def by auto  

lemma Max_S:fixes  x and S assumes "x \<in> S" and "finite S" shows "Max S \<ge> x"
      using assms by auto

definition max_codom::"(endpt \<times> endpt) set \<Rightarrow> nat"
where
"max_codom S \<equiv> (if ((codom_set_filter S) = {}) then 0 else Max (codom_set_filter S))"

lemma "(type x = domain) \<Longrightarrow> \<exists>m. x = dom m"
           using type_def by (metis endpt_reconstruction)

definition max_dom::"(endpt \<times> endpt) set \<Rightarrow> nat"
where
"max_dom S \<equiv>  (if (dom_set_filter S = {}) then 0 else Max (dom_set_filter S))"

 

lemma "max_codom {(codom 1,codom 2), (codom 3, dom 4)} = 3"
proof-
     have 1:"codom_set_filter {(codom 1,codom 2), (codom 3, dom 4)} = {1,2,3}"
                using codom_set_filter_def by auto
     then show ?thesis using max_codom_def 1 by auto       
qed



(*codom_set_filter associated lemmas*)

lemma finite_codom_set_filter:"finite S \<Longrightarrow> finite (codom_set_filter S)"
proof(induct rule:finite_induct)
   show "finite (codom_set_filter {})" using empty_set_codom_set_filter by auto
 next
 fix x S
  show "finite S \<Longrightarrow> x \<notin> S \<Longrightarrow> finite (codom_set_filter S) \<Longrightarrow> finite (codom_set_filter (insert x S))"
     proof-
     assume prems: "finite S"
     assume notin:"x \<notin> S"
     assume IH:"finite (codom_set_filter S)"
     show "finite (codom_set_filter (insert x S))"
     proof-
      have 0:"finite S"
                using prems by auto
      then have "finite (codom_set_filter S)"
                 using IH by auto
      then have "(insert x S) = {x} \<union> S"
             by auto
      then have "codom_set_filter (insert x S) = 
                          {n.(\<exists>y.((codom n,y) \<in> (insert x S)) \<or>((y, codom n)\<in> (insert x S)))}"
                        using codom_set_filter_def by auto
      then have "codom_set_filter (insert x S) = 
                          {n.(\<exists>y.(((codom n,y) \<in> S)\<or>(codom n, y) = x) \<or>((y, codom n)\<in> (insert x S)))}" 
                           using insert_def by auto
      then have "codom_set_filter (insert x S) = 
             {n.(\<exists>y.(((codom n,y) \<in> S)\<or>(codom n, y) = x) \<or>(((y, codom n)\<in>  S)\<or> (y, codom n) = x))}" 
                           using insert_def by auto
      then have "codom_set_filter (insert x S) = 
             {n.(\<exists>y.((codom n,y) \<in> S)\<or>((y, codom n)\<in>  S)\<or>((codom n, y) = x) \<or> (y, codom n) = x)}" 
                         by auto
      then have 1:"codom_set_filter (insert x S) = 
                     {n.(\<exists>y.((codom n,y) \<in> S)\<or>((y, codom n)\<in>  S))}
                      \<union>{n.(\<exists>y.((codom n, y) = x) \<or> (y, codom n) = x)}" 
                         by auto
      then have 2:"codom_set_filter S = {n.(\<exists>y.((codom n,y) \<in> S)\<or>((y, codom n)\<in>  S))}"
                          using codom_set_filter_def by auto
      then have 3:"codom_set_filter (insert x S) = 
                   (codom_set_filter S)
                      \<union>{n.(\<exists>y.((codom n, y) = x) \<or> (y, codom n) = x)}" 
                       using 1  by auto
      then have "finite {n.(\<exists>y.((codom n, y) = x) \<or> (y, codom n) = x)}"
                  proof(cases "codom_tuple x")
                  case True
                   have "\<exists>m1 m2.(x = (codom m1, codom m2))"
                              using codom_tuple_def type_def by (metis True endpt_reconstruction endtype.distinct(1) pair_collapse)      using finite_def sledgehammer
                   then obtain m1 m2 where "(x = (codom m1, codom m2))"
                          by auto     
                   then have "{n.(\<exists>y.((codom n, y) = x) \<or> (y, codom n) = x)} = {m1,m2}"
                              by auto
                   then show ?thesis by auto
                 next
                 case False
                    have 1:"(type (fst x) = domain)\<or>(type (snd x) = domain)"
                                          using False codom_tuple_def type_def
                                            by (metis endtype.exhaust)
                   show ?thesis
                       proof(cases "type (fst x)")
                       case domain
                         have "\<exists>m y. (x = (dom m, y))"
                                using domain endpt_reconstruction pair_collapse by metis
                         then obtain m1 y where "x = (dom m1, y)" by auto
                         then have 11:"x = (dom m1, y)" by auto
                          then show ?thesis
                                proof(cases "type y")
                                case domain
                                   have "\<exists>m2. (x = (dom m1, dom m2))"
                                        using domain 11 type_def endpt_reconstruction pair_collapse
                                        by metis
                                   then obtain m2 where "x = (dom m1, dom m2)" by auto
                                   then have "{n.(\<exists>y.((codom n, y) = x) \<or> (y, codom n) = x)} 
                                                = {}"
                                                by auto
                                   then show ?thesis by auto
                                 next
                                 case codomain
                                    have "\<exists>m2. (x = (dom m1, codom m2))"
                                      using codomain 11 type_def endpt_reconstruction pair_collapse
                                      by (metis endtype.distinct(1))
                                    then obtain m2 where "x = (dom m1, codom m2)"
                                          by auto
                                     then have "{n.(\<exists>y.((codom n, y) = x) \<or> (y, codom n) = x)} 
                                                = {m2}"
                                               by auto
                                     then show ?thesis by auto
                                  qed
                                 next
                                 case codomain
                                   have "\<exists>m y. (x = (codom m, y))"
                                     using codomain endpt_reconstruction pair_collapse 
                                     by (metis endtype.distinct(1))
                                   then obtain m1 y where "x = (codom m1, y)" by auto
                                   then have 11:"x = (codom m1, y)" by auto
                                   then have "type y = domain"
                                              using False type_def codom_tuple_def by (metis "1" codomain endtype.distinct(1) snd_conv)
                                   then have "\<exists>m2.(x = (codom m1, dom m2))"            
                                              using endpt_reconstruction pair_collapse
                                              by (metis "11") 
                                   then obtain m2 where "x = (codom m1, dom m2)"
                                              by auto
                                   then have "{n.(\<exists>y.((codom n, y) = x) \<or> (y, codom n) = x)} 
                                                = {m1}"  
                                              by auto
                                    then show ?thesis by auto
                               qed
                         qed
      then show ?thesis using 1 2 3 IH prems 0 by auto
      qed    
     qed 
 qed

lemma max_codom_set_filter:"(finite S)\<and>(n \<in> (codom_set_filter S)) \<Longrightarrow> max_codom S \<ge> n"
proof-
 assume 0: "(finite S)\<and>(n \<in> (codom_set_filter S))"
 have "n \<in> (codom_set_filter S) 
               \<Longrightarrow>  (codom_set_filter S) \<noteq> {}"  
                 by auto
 then have "(codom_set_filter S) \<noteq> {} \<Longrightarrow> S \<noteq> {}"
                  using empty_set_codom_set_filter by auto
 then have 1:"max_codom S = Max (codom_set_filter S)"
                  using max_codom_def 0 by auto
 then have " (Max (codom_set_filter S)\<ge> n)"
               using 0 Max_def finite_codom_set_filter Max_S by auto 
 then show ?thesis using 1 by auto
qed 
      
theorem fst_max_codom_does_not_belong:
 fixes i S
 assumes "finite S" and "i \<ge> 1"
 shows "\<forall>x.(codom ((max_codom S)+i) , x) \<notin> S"
proof(rule ccontr)
 assume 1: "\<not>(\<forall>x.(codom ((max_codom S)+i) , x) \<notin> S)"
 have "\<exists>x.(codom ((max_codom S)+i) , x) \<in> S"
        using 1 by auto
 then obtain x where "(codom ((max_codom S)+i) , x) \<in> S"
                by auto
 then have "(max_codom S)+i \<in> codom_set_filter S"
            using codom_set_filter_def by auto
 then have 2:"(max_codom S) \<ge> (max_codom S) +i "
              using max_codom_set_filter assms by auto
 moreover have "(max_codom S) + i > (max_codom S)"
               using assms by auto  
 then show False using 2 by auto
qed 

theorem snd_max_codom_does_not_belong:
 assumes "finite S" and "i \<ge> 1"
 shows "\<forall>x.( x,codom ((max_codom S)+i)) \<notin> S"
proof(rule ccontr)
 assume 1: "\<not>(\<forall>x.( x, codom ((max_codom S)+i)) \<notin> S)"
 have "\<exists>x.( x, codom ((max_codom S)+i)) \<in> S"
        using 1 by auto
 then obtain x where "( x, codom ((max_codom S)+i)) \<in> S"
                by auto
 then have "(max_codom S)+i \<in> codom_set_filter S"
            using codom_set_filter_def by auto
 then have 2:"(max_codom S) \<ge> (max_codom S) +i "
              using max_codom_set_filter assms by auto
 then have "(max_codom S) + i > max_codom S"
               using assms by auto
 then show False using 2 by auto
qed


theorem max_codom_does_not_belong:
 assumes "finite S" and "i \<ge> 1"
 shows "\<forall>x.((( x,codom ((max_codom S)+i)) \<notin> S)\<and>(codom ((max_codom S) + i), x) \<notin> S)"
  using fst_max_codom_does_not_belong snd_max_codom_does_not_belong assms by auto
  
(*max dom associated lemmas*)

lemma finite_dom_set_filter:"finite S \<Longrightarrow> finite (dom_set_filter S)"
proof(induct rule:finite_induct)
   show "finite (dom_set_filter {})" using empty_set_dom_set_filter by auto
next
 fix x S
  show "finite S \<Longrightarrow> x \<notin> S \<Longrightarrow> finite (dom_set_filter S) \<Longrightarrow> finite (dom_set_filter (insert x S))"
     proof-
     assume prems: "finite S"
     assume notin:"x \<notin> S"
     assume IH:"finite (dom_set_filter S)"
     show "finite (dom_set_filter (insert x S))"
     proof-
      have 0:"finite S"
                using prems by auto
      then have "finite (dom_set_filter S)"
                 using IH by auto
      then have "(insert x S) = {x} \<union> S"
             by auto
      then have "dom_set_filter (insert x S) = 
                          {n.(\<exists>y.((dom n,y) \<in> (insert x S)) \<or>((y, dom n)\<in> (insert x S)))}"
                        using dom_set_filter_def by auto
      then have "dom_set_filter (insert x S) = 
                          {n.(\<exists>y.(((dom n,y) \<in> S)\<or>(dom n, y) = x) \<or>((y, dom n)\<in> (insert x S)))}" 
                           using insert_def by auto
      then have "dom_set_filter (insert x S) = 
             {n.(\<exists>y.(((dom n,y) \<in> S)\<or>(dom n, y) = x) \<or>(((y, dom n)\<in>  S)\<or> (y, dom n) = x))}" 
                           using insert_def by auto
      then have "dom_set_filter (insert x S) = 
             {n.(\<exists>y.((dom n,y) \<in> S)\<or>((y, dom n)\<in>  S)\<or>((dom n, y) = x) \<or> (y, dom n) = x)}" 
                         by auto
      then have 1:"dom_set_filter (insert x S) = 
                     {n.(\<exists>y.((dom n,y) \<in> S)\<or>((y, dom n)\<in>  S))}
                      \<union>{n.(\<exists>y.((dom n, y) = x) \<or> (y, dom n) = x)}" 
                         by auto
      then have 2:"dom_set_filter S = {n.(\<exists>y.((dom n,y) \<in> S)\<or>((y, dom n)\<in>  S))}"
                          using dom_set_filter_def by auto
      then have 3:"dom_set_filter (insert x S) = 
                   (dom_set_filter S)
                      \<union>{n.(\<exists>y.((dom n, y) = x) \<or> (y, dom n) = x)}" 
                       using 1  by auto
      then have "finite {n.(\<exists>y.((dom n, y) = x) \<or> (y, dom n) = x)}     "
                  proof(cases "dom_tuple x")
                  case True
                   have "\<exists>m1 m2.(x = (dom m1, dom m2))"
                              using dom_tuple_def type_def by (metis True endpt_reconstruction endtype.distinct(1) pair_collapse)      using finite_def sledgehammer
                   then obtain m1 m2 where "(x = (dom m1, dom m2))"
                          by auto     
                   then have "{n.(\<exists>y.((dom n, y) = x) \<or> (y, dom n) = x)} = {m1,m2}"
                              by auto
                   then show ?thesis by auto
                 next
                 case False
                    have 1:"(type (fst x) = codomain)\<or>(type (snd x) = codomain)"
                                          using False dom_tuple_def type_def
                                            by (metis endtype.exhaust)
                   show ?thesis
                       proof(cases "type (fst x)")
                       case codomain
                         have "\<exists>m y. (x = (codom m, y))"
                                using codomain endpt_reconstruction pair_collapse by (metis endtype.distinct(1))
                         then obtain m1 y where "x = (codom m1, y)" by auto
                         then have 11:"x = (codom m1, y)" 
                                          by auto
                          then show ?thesis
                                proof(cases "type y")
                                case codomain
                                   have "\<exists>m2. (x = (codom m1, codom m2))"
                                        using codomain 11 type_def endpt_reconstruction pair_collapse
                                        by (metis endtype.distinct(1))
                                   then obtain m2 where "x = (codom m1, codom m2)" by auto
                                   then have "{n.(\<exists>y.((dom n, y) = x) \<or> (y, dom n) = x)} 
                                                = {}"
                                                by auto
                                   then show ?thesis by auto
                                 next
                                 case domain
                                    have "\<exists>m2. (x = (codom m1, dom m2))"
                                      using domain 11 type_def endpt_reconstruction pair_collapse
                                      by (metis endtype.distinct(1))
                                    then obtain m2 where "x = (codom m1, dom m2)"
                                          by auto
                                     then have "{n.(\<exists>y.((dom n, y) = x) \<or> (y, dom n) = x)} 
                                                = {m2}"
                                               by auto
                                     then show ?thesis by auto
                                  qed
                        next
                        case domain
                         have "\<exists>m y. (x = (dom m, y))"
                                     using domain endpt_reconstruction pair_collapse 
                                     by (metis endtype.distinct(1))
                                   then obtain m1 y where "x = (dom m1, y)" by auto
                                   then have 11:"x = (dom m1, y)" by auto
                                   then have "type y = codomain"
                                              using False type_def dom_tuple_def by (metis "1" domain endtype.distinct(1) snd_conv)
                                   then have "\<exists>m2.(x = (dom m1, codom m2))"            
                                              using endpt_reconstruction pair_collapse
                                              by (metis "11" endtype.distinct(1))
                                   then obtain m2 where "x = (dom m1, codom m2)"
                                              by auto
                                   then have "{n.(\<exists>y.((dom n, y) = x) \<or> (y, dom n) = x)} 
                                                = {m1}"  
                                              by auto
                                    then show ?thesis by auto
                               qed
                         qed
      then show ?thesis using 1 2 3 IH prems 0 by auto
      qed    
     qed 
 qed

lemma max_dom_set_filter:"(finite S)\<and>(n \<in> (dom_set_filter S)) \<Longrightarrow> max_dom S \<ge> n"
proof-
 assume 0: "(finite S)\<and>(n \<in> (dom_set_filter S))"
 have "n \<in> (dom_set_filter S) 
               \<Longrightarrow>  (dom_set_filter S) \<noteq> {}"  
                 by auto
 then have "(dom_set_filter S) \<noteq> {} \<Longrightarrow> S \<noteq> {}"
                  using empty_set_dom_set_filter by auto
 then have 1:"max_dom S = Max (dom_set_filter S)"
                  using max_dom_def 0  by auto
 then have " (Max (dom_set_filter S)\<ge> n)"
               using 0 Max_def finite_dom_set_filter Max_S by auto 
 then show ?thesis using 1 by auto
qed 
      
theorem fst_max_dom_does_not_belong:
 fixes i S
 assumes "finite S" and "i \<ge> 1"
 shows "\<forall>x.(dom ((max_dom S)+i) , x) \<notin> S"
proof(rule ccontr)
 assume 1: "\<not>(\<forall>x.(dom ((max_dom S)+i) , x) \<notin> S)"
 have "\<exists>x.(dom ((max_dom S)+i) , x) \<in> S"
        using 1 by auto
 then obtain x where "(dom ((max_dom S)+i) , x) \<in> S"
                by auto
 then have "(max_dom S)+i \<in> dom_set_filter S"
            using dom_set_filter_def by auto
 then have 2:"(max_dom S) \<ge> (max_dom S) +i "
              using max_dom_set_filter assms by auto
 moreover have "(max_dom S) + i > (max_dom S)"
               using assms by auto  
 then show False using 2 by auto
qed 

theorem snd_max_dom_does_not_belong:
 assumes "finite S" and "i \<ge> 1"
 shows "\<forall>x.( x,dom ((max_dom S)+i)) \<notin> S"
proof(rule ccontr)
 assume 1: "\<not>(\<forall>x.( x, dom ((max_dom S)+i)) \<notin> S)"
 have "\<exists>x.( x, dom ((max_dom S)+i)) \<in> S"
        using 1 by auto
 then obtain x where "( x, dom ((max_dom S)+i)) \<in> S"
                by auto
 then have "(max_dom S)+i \<in> dom_set_filter S"
            using dom_set_filter_def by auto
 then have 2:"(max_dom S) \<ge> (max_dom S) +i "
              using max_dom_set_filter assms by auto
 then have "(max_dom S) + i > max_dom S"
               using assms by auto
 then show False using 2 by auto
qed


theorem max_dom_does_not_belong:
 assumes "finite S" and "i \<ge> 1"
 shows "\<forall>x.((( x,dom ((max_dom S)+i)) \<notin> S)\<and>(dom ((max_dom S) + i), x) \<notin> S)"
  using fst_max_dom_does_not_belong snd_max_dom_does_not_belong assms by auto
        
(*end max_dom based lemmas*)
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

definition swap_act::"(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set"
where
"swap_act S \<equiv>  {(codom ((max_codom S)+1), dom ((max_dom S)+2))
               ,(codom ((max_codom S)+2), dom ((max_dom S)+1))
               ,(dom ((max_dom S)+2),codom ((max_codom S)+1))
               ,(dom ((max_dom S)+1),codom ((max_codom S)+2))}
               \<union> S"

lemma finite_swap_act:"finite S \<Longrightarrow> (finite (swap_act S))"
        using swap_act_def by auto
   
primrec block_act::"block \<Rightarrow> (endpt \<times> endpt)  set"
where
"block_act []  = {}"
|"block_act (x#xs) = 
   (case x of
      vert  \<Rightarrow> {(codom ((max_codom (block_act xs))+1), dom ((max_dom (block_act xs))+1)),
              (dom ((max_dom (block_act xs))+1), codom ((max_codom (block_act xs))+1))}
                   \<union> (block_act xs)
     |over  \<Rightarrow> swap_act (block_act xs)
     |under \<Rightarrow> swap_act (block_act xs)
     |cup   \<Rightarrow> {(codom ((max_codom (block_act xs))+2),codom ((max_codom (block_act xs))+1)),
               (codom ((max_codom (block_act xs))+1), codom ((max_codom (block_act xs))+2))}
               \<union>(block_act xs) 
     |cap   \<Rightarrow> {(dom ((max_dom (block_act xs))+2), dom ((max_dom (block_act xs))+1)),
              ( dom ((max_dom (block_act xs))+1),dom ((max_dom (block_act xs))+2))}
               \<union>(block_act xs))"

lemma finite_block_act:"finite (block_act xs)"
       apply(induct_tac xs)
       apply(auto)
       apply(case_tac a)
       apply(simp)
       apply(auto)
       apply(simp add:finite_swap_act)
       by (metis finite_swap_act)

    

theorem card_block_act: 
      "card (block_act xs) = nat (domain_block xs) + nat (codomain_block xs)"
 proof(induction xs)
 case Nil
     show ?case using block_act.simps card_def by auto
 next
 case (Cons x xs)
   show ?case
      proof(cases x)
      case vert
        have geq_1:"(1::nat) \<ge> 1"
                by (metis le_numeral_extra(4))
        have "card (block_act (xs)) = nat (domain_block (xs)) + nat (codomain_block (xs))"
                using Cons by auto
        then have vert_1:"block_act (x#xs) =  {(codom ((max_codom (block_act xs))+1),
                                                  dom ((max_dom (block_act xs))+1)),
              (dom ((max_dom (block_act xs))+1), codom ((max_codom (block_act xs))+1))}
                   \<union> (block_act xs)"
                       using vert by auto 
        moreover have "(codom ((max_codom (block_act xs))+1),
                                                  dom ((max_dom (block_act xs))+1))
                                   \<notin> (block_act xs)"
                             using fst_max_codom_does_not_belong finite_block_act geq_1
                            by metis   
        moreover have "(dom ((max_dom (block_act xs))+1), codom ((max_codom (block_act xs))+1))
                                \<notin> (block_act xs)"
                                using snd_max_codom_does_not_belong finite_block_act geq_1 by metis
        ultimately have vert_2:"{(codom ((max_codom (block_act xs))+1),
                                                  dom ((max_dom (block_act xs))+1)),
              (dom ((max_dom (block_act xs))+1), codom ((max_codom (block_act xs))+1))}
                     \<inter> (block_act xs) = {}"
                      by auto
        moreover have "finite {(codom ((max_codom (block_act xs))+1),
                                                  dom ((max_dom (block_act xs))+1)),
              (dom ((max_dom (block_act xs))+1), codom ((max_codom (block_act xs))+1))}"
                              by auto 
        then have vert_3:"card (block_act (x#xs)) = card ({(codom ((max_codom (block_act xs))+1),
                                                  dom ((max_dom (block_act xs))+1)),
              (dom ((max_dom (block_act xs))+1), codom ((max_codom (block_act xs))+1))})
                           + card (block_act xs)"
                         using vert_1 vert_2 card.union_disjoint finite_block_act by auto
         have "card  ({(codom ((max_codom (block_act xs))+1),
                                                  dom ((max_dom (block_act xs))+1)),
              (dom ((max_dom (block_act xs))+1), codom ((max_codom (block_act xs))+1))})
                           = 2"
                  by auto
          then have vert_4:"card (block_act (x#xs)) = 2 + card (block_act xs)"
                                using vert_3 by auto
         moreover have "(nat (domain_block (x#xs))) + (nat (codomain_block (x#xs))) 
                                          = 2 + (nat (domain_block xs))
                                              + (nat (codomain_block xs))"
                                 using vert domain_block.simps codomain_block.simps 
                                         by (metis Suc_1 Suc_eq_plus1_left Suc_nat_eq_nat_zadd1 
                                            add_Suc_shift codomain.simps(1) 
                                            codomain_block_nonnegative domain.simps(1) 
                                            domain_block_nonnegative)
          then have "nat (domain_block (x#xs)) + nat(codomain_block (x#xs)) = 2 + card (block_act xs)"
                              using Cons by auto
          with vert_4 have "card (block_act (x#xs)) = nat (domain_block (x#xs)) 
                                                    + nat(codomain_block (x#xs)) "
                             by auto
          then show ?thesis by auto
       next
       case cup
        have geq_1:"(1::nat) \<ge> 1" by (metis le_numeral_extra(4)) 
        let ?ys = "{(codom ((max_codom (block_act xs))+2),codom ((max_codom (block_act xs))+1))
                     ,(codom ((max_codom (block_act xs))+1), codom ((max_codom (block_act xs))+2))}"
        have cup_1:"block_act (x#xs) = ?ys \<union> (block_act xs)"
                   using cup block_act.simps by auto
        then have "(codom ((max_codom (block_act xs))+2),codom ((max_codom (block_act xs))+1))
                      \<notin> (block_act xs)"
                  using snd_max_codom_does_not_belong finite_block_act geq_1 by metis  
        moreover have "(codom ((max_codom (block_act xs))+1), codom ((max_codom (block_act xs))+2))
                      \<notin> (block_act xs)"
                     using fst_max_codom_does_not_belong finite_block_act geq_1 by metis  
       ultimately have "?ys \<inter> (block_act xs) = {}"
                         by auto
       moreover have"finite ?ys"
                    by auto
      ultimately have "card (block_act (x#xs)) = (card ?ys) + (card (block_act xs))"
                    using finite_block_act cup_1 card.union_disjoint by auto
      then have cup_2:"card (block_act (x#xs)) = 2 + (card (block_act xs))"
                              by auto
      moreover have "(nat (domain_block (x#xs))) + (nat (codomain_block (x#xs)))
                             =  (nat (domain_block xs)) +  (nat (2+ codomain_block xs))"
                               using domain_block.simps codomain_block.simps domain.simps 
                               codomain.simps cup by auto
     then have "(nat (domain_block (x#xs))) + (nat (codomain_block (x#xs)))
                             = 2 +  (nat (domain_block xs)) +  (nat (codomain_block xs))"
                               by (metis Nat_Transfer.transfer_nat_int_function_closures(7) 
                                  Suc_eq_plus1_left ab_semigroup_add_class.add_ac(1) add_Suc_right 
                                   codomain_block_nonnegative nat_add_distrib nat_numeral one_add_one)
     then have "(nat (domain_block (x#xs))) + (nat (codomain_block (x#xs)))
                               =  2 + (card (block_act xs)) "
                               using Cons by auto
     then have "card (block_act (x#xs)) = (nat (domain_block (x#xs))) + (nat (codomain_block (x#xs)))"
                     using cup_2 by auto
     then show ?thesis by auto
   next
   case over
    let ?S = "block_act xs"
    let ?Q = "{(codom ((max_codom ?S)+1), dom ((max_dom ?S)+2))
                                   ,(codom ((max_codom ?S)+2), dom ((max_dom ?S)+1))
                                   ,(dom ((max_dom ?S)+2),codom ((max_codom ?S)+1))
                                   ,(dom ((max_dom ?S)+1),codom ((max_codom ?S)+2))}"
    have geq_1:"(1::nat) \<ge> 1" by auto
    have geq_2:"(2::nat) \<ge> 1" by auto
    have over_1:"(block_act (x#xs)) = (swap_act (block_act xs))"
                             using over 
                             by auto
    then have over_2:
         "swap_act (block_act xs) = ?Q \<union> ?S"
                   using swap_act_def by auto
    then have "(codom ((max_codom ?S)+1), dom ((max_dom ?S)+2)) \<notin> ?S"
                    using fst_max_codom_does_not_belong finite_block_act geq_1 by metis
    moreover have "(codom ((max_codom ?S)+2), dom ((max_dom ?S)+1)) \<notin> ?S"
                    using fst_max_codom_does_not_belong finite_block_act geq_2 by metis
    moreover have "(dom ((max_dom ?S)+2),codom ((max_codom ?S)+1)) \<notin> ?S"
                    using snd_max_codom_does_not_belong finite_block_act geq_1 by metis
    moreover have "(dom ((max_dom ?S)+1),codom ((max_codom ?S)+2)) \<notin> ?S"
                    using snd_max_codom_does_not_belong finite_block_act geq_2 by metis
   ultimately have over_3:"?Q \<inter> ?S = {}"
                by auto
   have "finite ?Q"
               by auto
   then have "card (swap_act ?S) = card ?Q + card ?S"
                using over_2 over_3 card.union_disjoint finite_block_act by auto
   then have over_4:"card (swap_act ?S) = 4 + card ?S" 
                           by auto
   have "(nat (domain_block (x#xs))) + (nat (codomain_block (x#xs)))
                      = (nat (2+(domain_block xs)))+(nat (2+(codomain_block xs)))"
                using over domain_block.simps codomain_block.simps by auto
   moreover have "(nat (2+(domain_block xs))) = 2 + nat (domain_block xs)"
                         by (metis Suc_nat_eq_nat_zadd1 ab_semigroup_add_class.add_ac(1) add_2_eq_Suc add_nonneg_nonneg domain_block_non_negative one_add_one zero_le_one)
   moreover have "(nat (2+(codomain_block xs))) = 2 + nat (codomain_block xs)"
                                 by (metis Nat_Transfer.transfer_nat_int_function_closures(7) codomain_block_nonnegative nat_add_distrib nat_numeral)
   ultimately have "(nat (domain_block (x#xs))) + (nat (codomain_block (x#xs)))
                  = 4 + (nat (domain_block (xs))) +  (nat (codomain_block (xs)))"  
                     by auto
    then have "(nat (domain_block (x#xs))) + (nat (codomain_block (x#xs))) = 4 + card (block_act xs)"
                     by (metis Cons.IH nat_add_commute nat_add_left_commute)
    then have "card (swap_act ?S) = (nat (domain_block (x#xs))) + (nat (codomain_block (x#xs))) "
                      using over_4 by auto
    then show ?thesis using over_1 by auto
   next
   case under
     let ?S = "block_act xs"
     let ?Q = "{(codom ((max_codom ?S)+1), dom ((max_dom ?S)+2))
                                   ,(codom ((max_codom ?S)+2), dom ((max_dom ?S)+1))
                                   ,(dom ((max_dom ?S)+2),codom ((max_codom ?S)+1))
                                   ,(dom ((max_dom ?S)+1),codom ((max_codom ?S)+2))}"
     have geq_1:"(1::nat) \<ge> 1" by auto
     have geq_2:"(2::nat) \<ge> 1" by auto
     have under_1:"(block_act (x#xs)) = (swap_act (block_act xs))"
                             using under 
                             by auto
     then have under_2:
         "swap_act (block_act xs) = ?Q \<union> ?S"
                   using swap_act_def by auto
     then have "(codom ((max_codom ?S)+1), dom ((max_dom ?S)+2)) \<notin> ?S"
                    using fst_max_codom_does_not_belong finite_block_act geq_1 by metis
     moreover have "(codom ((max_codom ?S)+2), dom ((max_dom ?S)+1)) \<notin> ?S"
                    using fst_max_codom_does_not_belong finite_block_act geq_2 by metis
     moreover have "(dom ((max_dom ?S)+2),codom ((max_codom ?S)+1)) \<notin> ?S"
                    using snd_max_codom_does_not_belong finite_block_act geq_1 by metis
     moreover have "(dom ((max_dom ?S)+1),codom ((max_codom ?S)+2)) \<notin> ?S"
                    using snd_max_codom_does_not_belong finite_block_act geq_2 by metis
     ultimately have under_3:"?Q \<inter> ?S = {}"
                by auto
     have "finite ?Q"
               by auto
     then have "card (swap_act ?S) = card ?Q + card ?S"
                using under_2 under_3 card.union_disjoint finite_block_act by auto
     then have under_4:"card (swap_act ?S) = 4 + card ?S" 
                           by auto
     have "(nat (domain_block (x#xs))) + (nat (codomain_block (x#xs)))
                      = (nat (2+(domain_block xs)))+(nat (2+(codomain_block xs)))"
                using under domain_block.simps codomain_block.simps by auto
     moreover have "(nat (2+(domain_block xs))) = 2 + nat (domain_block xs)"
                         by (metis Suc_nat_eq_nat_zadd1 ab_semigroup_add_class.add_ac(1) 
                            add_2_eq_Suc add_nonneg_nonneg domain_block_non_negative one_add_one 
                            zero_le_one)
     moreover have "(nat (2+(codomain_block xs))) = 2 + nat (codomain_block xs)"
                                 by (metis Nat_Transfer.transfer_nat_int_function_closures(7) 
                                     codomain_block_nonnegative nat_add_distrib nat_numeral)
     ultimately have "(nat (domain_block (x#xs))) + (nat (codomain_block (x#xs)))
                  = 4 + (nat (domain_block (xs))) +  (nat (codomain_block (xs)))"  
                     by auto
     then have "(nat (domain_block (x#xs))) + (nat (codomain_block (x#xs))) = 4 + card (block_act xs)"
                     by (metis Cons.IH nat_add_commute nat_add_left_commute)
     then have "card (swap_act ?S) = (nat (domain_block (x#xs))) + (nat (codomain_block (x#xs))) "
                      using under_4 by auto
     then show ?thesis using under_1 by auto
   next
   case cap
     have geq_1:"(1::nat) \<ge> 1" by (metis le_numeral_extra(4)) 
     let ?ys = "{(dom ((max_dom (block_act xs))+2),dom ((max_dom (block_act xs))+1))
                     ,(dom ((max_dom (block_act xs))+1), dom ((max_dom (block_act xs))+2))}"
     have cup_1:"block_act (x#xs) = ?ys \<union> (block_act xs)"
                   using cap block_act.simps by auto
     then have "(dom ((max_dom (block_act xs))+2),dom ((max_dom (block_act xs))+1))
                      \<notin> (block_act xs)"
                  using snd_max_dom_does_not_belong finite_block_act geq_1 by metis  
     moreover have "(dom ((max_dom (block_act xs))+1), dom ((max_dom (block_act xs))+2))
                      \<notin> (block_act xs)"
                     using fst_max_dom_does_not_belong finite_block_act geq_1 by metis  
     ultimately have "?ys \<inter> (block_act xs) = {}"
                         by auto
     moreover have"finite ?ys"
                    by auto
     ultimately have "card (block_act (x#xs)) = (card ?ys) + (card (block_act xs))"
                    using finite_block_act cup_1 card.union_disjoint by auto
     then have cup_2:"card (block_act (x#xs)) = 2 + (card (block_act xs))"
                              by auto
     moreover have "(nat (domain_block (x#xs))) + (nat (codomain_block (x#xs)))
                             =  (nat (2+domain_block xs)) +  (nat (codomain_block xs))"
                               using domain_block.simps codomain_block.simps domain.simps 
                               codomain.simps cap by auto
     then have "(nat (domain_block (x#xs))) + (nat (codomain_block (x#xs)))
                             = 2 +  (nat (domain_block xs)) +  (nat (codomain_block xs))"
                               by (metis Nat_Transfer.transfer_nat_int_function_closures(7) 
                                  Suc_eq_plus1_left ab_semigroup_add_class.add_ac(1) add_Suc_right 
                                   domain_block_nonnegative nat_add_distrib nat_numeral one_add_one)
     then have "(nat (domain_block (x#xs))) + (nat (codomain_block (x#xs)))
                               =  2 + (card (block_act xs)) "
                               using Cons by auto
     then have "card (block_act (x#xs)) = (nat (domain_block (x#xs))) + (nat (codomain_block (x#xs)))"
                     using cup_2 by auto
     then show ?thesis by auto
qed
qed

(*symmetry related properties *)
definition symmetric::"('a \<times> 'a) set \<Rightarrow> bool"
 where
"symmetric S \<equiv> \<forall>x.\<forall>y.((x,y) \<in> S) \<longrightarrow> ((y,x) \<in> S)"  

lemma symmetric_union:
  assumes "symmetric A" and "symmetric B"
  shows "symmetric (A \<union> B)"
     using assms unfolding symmetric_def by auto

theorem symmetric_block_act: "symmetric (block_act xs)"
 proof(induction xs)
 case Nil
    show ?case using Nil by (metis block_act.simps(1) empty_iff symmetric_def)
 next
 case (Cons x xs)
    show ?case
      proof(cases x)
      case vert
        let ?ys = "{(codom ((max_codom (block_act xs))+1), dom ((max_dom (block_act xs))+1)),
              (dom ((max_dom (block_act xs))+1), codom ((max_codom (block_act xs))+1))}"
        have vert_1:"(block_act (x#xs)) = ?ys \<union> (block_act xs)"
                     using vert by auto
        have "symmetric ?ys"
               unfolding symmetric_def by auto
        moreover have "symmetric (block_act xs)"
                      using Cons by auto
        then show ?thesis using symmetric_union vert_1 by (metis calculation) 
       next
       case cup
        let ?ys = "{(codom ((max_codom (block_act xs))+2),codom ((max_codom (block_act xs))+1)),
               (codom ((max_codom (block_act xs))+1), codom ((max_codom (block_act xs))+2))}"
        have cup_1:"(block_act (x#xs)) = ?ys \<union> (block_act xs)"
                     using cup by auto
        have "symmetric ?ys"
               unfolding symmetric_def by auto
        moreover have "symmetric (block_act xs)"
                      using Cons by auto
        then show ?thesis using symmetric_union cup_1 by (metis calculation) 
       next       
        case cap
        let ?ys = "{(dom ((max_dom (block_act xs))+2),dom ((max_dom (block_act xs))+1)),
               (dom ((max_dom (block_act xs))+1), dom ((max_dom (block_act xs))+2))}"
        have cap_1:"(block_act (x#xs)) = ?ys \<union> (block_act xs)"
                     using cap by auto
        have "symmetric ?ys"
               unfolding symmetric_def by auto
        moreover have "symmetric (block_act xs)"
                      using Cons by auto
        then show ?thesis using symmetric_union cap_1 by (metis calculation) 
       next
       case over
        let ?S = " block_act xs"
        let ?Q = " {(codom ((max_codom ?S)+1), dom ((max_dom ?S)+2))
               ,(codom ((max_codom ?S)+2), dom ((max_dom ?S)+1))
               ,(dom ((max_dom ?S)+2),codom ((max_codom ?S)+1))
               ,(dom ((max_dom ?S)+1),codom ((max_codom ?S)+2))}"
        have "block_act (x#xs) = ?Q \<union> ?S"
                  using over swap_act_def by auto
        moreover have "symmetric ?Q"  
                  using symmetric_def by auto
        moreover have "symmetric ?S"
                  using Cons by auto
        ultimately show ?thesis using symmetric_union by metis 
  next
  case under
      let ?S = " block_act xs"
        let ?Q = " {(codom ((max_codom ?S)+1), dom ((max_dom ?S)+2))
               ,(codom ((max_codom ?S)+2), dom ((max_dom ?S)+1))
               ,(dom ((max_dom ?S)+2),codom ((max_codom ?S)+1))
               ,(dom ((max_dom ?S)+1),codom ((max_codom ?S)+2))}"
        have "block_act (x#xs) = ?Q \<union> ?S"
                  using under swap_act_def by auto
        moreover have "symmetric ?Q"  
                  using symmetric_def by auto
        moreover have "symmetric ?S"
                  using Cons by auto
        ultimately show ?thesis using symmetric_union by metis 
  qed
qed

(*defining injectivity*)
definition element_set::"endpt \<Rightarrow> (endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set"
where
"element_set a S \<equiv> {(x,y). ((x,y) \<in> S)\<and>((x=a)\<or>(y=a))}"

lemma a_implies_b:"\<not>(A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> \<not>B)"
         by auto

lemma element_set_empty:"(\<forall>x.(((x,a) \<notin> S)\<and>((a,x) \<notin> S))) \<longrightarrow> element_set a S = {}"
 proof(rule ccontr)
 assume 0:"\<not>((\<forall>x.(((x,a) \<notin> S)\<and>((a,x) \<notin> S))) \<longrightarrow> element_set a S = {})"
 have "(\<forall>x.(((x,a) \<notin> S)\<and>((a,x) \<notin> S))) \<longrightarrow> element_set a S \<noteq> {}"
           using 0 a_implies_b by auto 
 then have "(\<forall>x.(((x,a) \<notin> S)\<and>((a,x) \<notin> S))) \<longrightarrow> (\<exists>x y.((x,y) \<in> (element_set a S)))"
              by auto
 then obtain x y where "(\<forall>x.(((x,a) \<notin> S)\<and>((a,x) \<notin> S))) \<longrightarrow> ((x,y) \<in> (element_set a S))"
                     by auto

 then have "(\<forall>x.(((x,a) \<notin> S)\<and>((a,x) \<notin> S))) \<longrightarrow> ( ((x,y)\<in> S)\<and>((x=a)\<or>(y=a)))"
                  using element_set_def by auto
 moreover have "( ((x,y)\<in> S)\<and>((x=a)\<or>(y=a))) \<longrightarrow> (a,y) \<in> S \<or> (x,a) \<in> S"
              by auto
 ultimately have  "(\<forall>x.(((x,a) \<notin> S)\<and>((a,x) \<notin> S))) \<longrightarrow> (a,y) \<in> S \<or> (x,a) \<in> S"
                   by auto
 then show False by (metis "0")
qed

lemma subset_element_set:"element_set a S \<subseteq> S"
      unfolding element_set_def by auto

lemma finite_element_set:"finite S \<Longrightarrow> finite (element_set a S)"
      using subset_element_set rev_finite_subset  by metis
 
lemma empty_intersection_cond:"\<forall>x.((x \<in> S) \<longrightarrow> (x \<notin> R)) \<Longrightarrow> S \<inter> R = {}"
         by auto



definition count_element::"endpt \<Rightarrow> (endpt \<times> endpt) set \<Rightarrow> nat"
where
"count_element a S \<equiv> card (element_set a S)"

definition found_in::"endpt \<Rightarrow> (endpt \<times> endpt) set \<Rightarrow> bool"
where
"found_in a S \<equiv> (\<exists>x.((x,a) \<in> S)\<or>((a,x)\<in> S))"

lemma found_in_element_set:"found_in a S = (element_set a S \<noteq> {})"
           using found_in_def element_set_def by auto

lemma found_in_union:"\<forall>x.(found_in x (A \<union> B)) 
                         \<longrightarrow> (found_in x A) \<or> (found_in x B)" 
        using found_in_def by auto

lemma str_number_max_dom:
 fixes x S
       assumes "found_in x S" and "type x = domain" and "finite S"
       shows "str_number x \<le> (max_dom S)"
proof-
 have "\<exists>y.((x,y) \<in> S)\<or>(y,x) \<in> S"
         using found_in_def assms  by auto 
 then obtain y where "((x,y) \<in> S)\<or>(y,x) \<in> S" by auto
 have "x = dom (str_number x)"
             using assms(2) type_def str_number_def endpt_reconstruction by metis
 then have "((dom (str_number x),y) \<in> S)\<or>(y,(dom (str_number x))) \<in> S"
             by (metis `(x, y) \<in> S \<or> (y, x) \<in> S`)
 then have "str_number x \<in> dom_set_filter S"
           unfolding dom_set_filter_def by auto 
 moreover then have "dom_set_filter S \<noteq> {}"
                   by auto
 ultimately show ?thesis
         using max_dom_def Max_def assms(3) by (metis max_dom_set_filter) 
qed 

lemma str_number_max_codom:
 fixes x S
       assumes "found_in x S" and "type x = codomain" and "finite S"
       shows "str_number x \<le> (max_codom S)"
proof-
 have "\<exists>y.((x,y) \<in> S)\<or>(y,x) \<in> S"
         using found_in_def assms  by auto 
 then obtain y where "((x,y) \<in> S)\<or>(y,x) \<in> S" by auto
 have "x =  codom (str_number x)"
             using assms(2) type_def str_number_def endpt_reconstruction by (metis endtype.distinct(1))
 then have "((codom (str_number x),y) \<in> S)\<or>(y,(codom (str_number x))) \<in> S"
             by (metis `(x, y) \<in> S \<or> (y, x) \<in> S`)
 then have "str_number x \<in> codom_set_filter S"
           unfolding codom_set_filter_def by auto 
 moreover then have "codom_set_filter S \<noteq> {}"
                   by auto
 ultimately show ?thesis
         using max_codom_def Max_def assms(3) by (metis max_codom_set_filter) 
qed 




definition injective::"(endpt \<times> endpt) set \<Rightarrow> bool"
where
"injective S \<equiv> \<forall>x.(found_in x S \<longrightarrow> count_element x S = 2)"

lemma subset_intersection:"A \<subseteq> B \<and> C \<subseteq> D \<and> B \<inter> D = {} \<Longrightarrow> A \<inter> C = {}"
           by auto

(*block_act is symmetric*)

theorem injective_block_act:"injective (block_act xs)"
proof(induction xs)
 case Nil
  show ?case using Nil injective_def found_in_def by auto 
 next 
 case (Cons y ys)
  show ?case 
   proof(cases y)
    case vert
     fix a
     let ?Q = "{(codom ((max_codom (block_act ys))+1), dom ((max_dom (block_act ys))+1)),
              (dom ((max_dom (block_act ys))+1), codom ((max_codom (block_act ys))+1))}"
     have vert_0:"finite ?Q \<and> (finite (block_act ys))"
                   using finite_block_act   by auto
     have vert_1:"(block_act (y#ys)) = ?Q \<union> (block_act ys)"
                     using vert by auto
     then have vert_2:"\<forall>a.(element_set a (block_act (y#ys)) = element_set a ?Q 
                                     \<union> element_set a (block_act ys))"  
                            using element_set_def by auto
     have "\<forall>x.(x \<in> ?Q \<longrightarrow> x \<notin> (block_act ys))"
               using max_codom_does_not_belong max_dom_does_not_belong vert_0
                     by (metis (hide_lams, full_types) empty_iff finite_block_act insert_compr insert_iff le_refl nat_add_commute snd_max_codom_does_not_belong snd_max_dom_does_not_belong)
     then have "?Q \<inter> (block_act ys) = {}"
               by auto
     moreover have "\<forall>a.(element_set a ?Q \<subseteq> ?Q)"
                 using subset_element_set by auto 
     moreover have "\<forall>a.(element_set a (block_act ys) \<subseteq> (block_act ys))"
                 using subset_element_set by auto 
     ultimately have vert_12:"\<forall>a.(element_set a ?Q \<inter> element_set a (block_act ys) = {})"
                  using subset_intersection by auto 
     then have vert_3:"\<forall>a.(
                 count_element a  (block_act (y#ys)) = count_element a ?Q 
                                     + count_element a (block_act ys))"  
                           unfolding count_element_def using  card.union_disjoint 
                            vert_0 vert_2 by (metis finite_element_set)
     then have vert_4:"\<forall>x.(found_in x (block_act (y#ys)) 
                         \<longrightarrow> (found_in x (?Q))\<or>(found_in x (block_act ys)))" 
                       using vert_1 found_in_union by auto  
     then have "\<forall>x.((found_in x (?Q))
                        =  
       (x \<in>{codom ((max_codom (block_act ys))+1), dom ((max_dom (block_act ys))+1)}))"    
               using found_in_def by auto
     then have vert_5:
         "\<forall>x.((found_in x (?Q))
                        =  ((x= codom ((max_codom (block_act ys))+1))
                          \<or>(x= dom ((max_dom (block_act ys))+1))))"
                    by auto
         let ?x1 = " codom ((max_codom (block_act ys))+1)"
         let ?x2 = " dom ((max_dom (block_act ys))+1)"
    have "element_set ?x1 (block_act ys) = {} "
                     using element_set_def fst_max_codom_does_not_belong
                           snd_max_codom_does_not_belong element_set_empty by (metis (hide_lams, no_types) finite_block_act order_refl)      
    then have vert_6:"count_element ?x1 (block_act ys) = 0"
                   using count_element_def by auto
    have "element_set ?x2 (block_act ys) = {} "
                     using element_set_def max_dom_does_not_belong element_set_empty 
                     by (metis (hide_lams, no_types) finite_block_act order_refl)      
    then have vert_7:"count_element ?x2 (block_act ys) = 0"
                 using count_element_def by auto
    with vert_6 vert_5 have vert_8:"\<forall>x.((found_in x (?Q))
                           \<longrightarrow> (count_element x (block_act ys)) = 0)"
                              by metis 
    have "element_set ?x1 ?Q = ?Q"
                   unfolding element_set_def by auto 
    then have vert_9:"count_element ?x1 ?Q = 2"
                    using count_element_def by auto
    have "element_set ?x2 ?Q = ?Q"
                   unfolding element_set_def by auto 
    then have vert_10:"count_element ?x2 ?Q = 2"
                    using count_element_def by auto     
    then have vert_11:"\<forall>x.((found_in x (?Q))
                           \<longrightarrow> (count_element x ?Q) = 2)"
                     using vert_9 vert_5 by auto
   then have vert_12:"\<forall>x.((count_element x(block_act (y#ys))) = 
                                   (count_element x ?Q)+ (count_element x (block_act ys)))"
                            using vert_3 by auto   
   then have vert_13:"\<forall>x.((found_in x (?Q))
                           \<longrightarrow> (count_element x (block_act (y#ys))) = 2)"
                            using vert_8 vert_11 by auto 
   have vert_14:"\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (count_element x (block_act ys)) = 2)"
                       using Cons injective_def by auto 
   have vert_15:"\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         (str_number x < max_dom (block_act ys) + 1))"
                                 using str_number_max_dom 
                                 by (metis add_strict_increasing finite_block_act 
                                 nat_add_commute zero_less_one)
    have vert_16:"\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) = {})"
            proof(rule ccontr)
            assume 0:"\<not>(\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) = {}))"
            have "\<exists>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                          using 0 by auto
             then obtain x where "((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                            by auto
             then have "\<exists>y.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         y \<in> element_set x (?Q))"
                            by auto
             then obtain z where "((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         z \<in> element_set x (?Q))"
                             by auto
              then have 1:"(found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((fst z = x)\<or>(snd z = x))"
                              using element_set_def by auto
              then have "(found_in x (block_act ys)) \<and>(type x = domain) \<and> (fst z = x) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((str_number x < max_dom (block_act ys)+1))"
                              using vert_15 by auto
              moreover have "(z \<in> ?Q) \<and>(fst z = x)\<and>(type x = domain) 
                              \<longrightarrow> x = ?x1"
                           using type_def endpt_reconstruction    by (metis "0" `element_set (endpt.dom (max_dom (block_act ys) + 1)) (block_act ys) = {}` endpt.distinct(1) found_in_element_set vert_5)
              moreover have "(z \<in> ?Q) \<and>(fst z = x)\<and>(type x = domain) 
                                 \<longrightarrow> str_number x = max_dom (block_act ys) + 1"
                                  using str_number_def type_def by auto
              ultimately have 2:"(found_in x (block_act ys)) \<and>(type x = domain) \<and> (fst z = x) \<longrightarrow>
                                    False"
                                  by auto 
              then have "(found_in x (block_act ys)) \<and>(type x = domain) \<and> (snd z = x) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((str_number x < max_dom (block_act ys)+1))"
                              using 1 vert_15 by auto
              moreover have "(z \<in> ?Q) \<and>(snd z = x)\<and>(type x = domain) 
                              \<longrightarrow> x = ?x1"
                           using type_def endpt_reconstruction    by (metis "0" `element_set (endpt.dom (max_dom (block_act ys) + 1)) (block_act ys) = {}` endpt.distinct(1) found_in_element_set vert_5)
              moreover have "(z \<in> ?Q) \<and>(snd z = x)\<and>(type x = domain) 
                                 \<longrightarrow> str_number x = max_dom (block_act ys) + 1"
                                  using str_number_def type_def by auto
              ultimately have 2:"(found_in x (block_act ys)) \<and>(type x = domain) \<and> (snd z = x) \<longrightarrow>
                                    False"
                                  by auto
             then have "(found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow>
                                   False"
                                       using 1 2 by (metis `found_in x (block_act ys) \<and> type x = endtype.domain \<and> fst z = x \<longrightarrow> z \<in> {(codom (max_codom (block_act ys) + 1), endpt.dom (max_dom (block_act ys) + 1)), (endpt.dom (max_dom (block_act ys) + 1), codom (max_codom (block_act ys) + 1))} \<and> str_number x < max_dom (block_act ys) + 1` `z \<in> {(codom (max_codom (block_act ys) + 1), endpt.dom (max_dom (block_act ys) + 1)), (endpt.dom (max_dom (block_act ys) + 1), codom (max_codom (block_act ys) + 1))} \<and> fst z = x \<and> type x = endtype.domain \<longrightarrow> str_number x = max_dom (block_act ys) + 1` less_not_refl3)
             then show False using 0 by (metis `element_set (codom (max_codom (block_act ys) + 1)) (block_act ys) = {}` `element_set (endpt.dom (max_dom (block_act ys) + 1)) (block_act ys) = {}` found_in_element_set vert_5)
            qed        
 
     have vert_17:"\<forall>x.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         (str_number x < max_codom (block_act ys) + 1))"
                                 using str_number_max_codom 
                                 by (metis add_strict_increasing finite_block_act 
                                 nat_add_commute zero_less_one)
      have "\<forall>x.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         element_set x (?Q) = {})"
            proof(rule ccontr)
            assume 0:"\<not>(\<forall>x.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         element_set x (?Q) = {}))"
            have "\<exists>x.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                          using 0 by auto
             then obtain x where "((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                            by auto
             then have "\<exists>y.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         y \<in> element_set x (?Q))"
                            by auto
             then obtain z where "((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         z \<in> element_set x (?Q))"
                             by auto
             then have 1:"(found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((fst z = x)\<or>(snd z = x))"
                              using element_set_def by auto
             then have "(found_in x (block_act ys)) \<and>(type x = codomain) \<and> (fst z = x) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((str_number x < max_codom (block_act ys)+1))"
                              using vert_17 by auto
             moreover have "(z \<in> ?Q) \<and>(fst z = x)\<and>(type x = codomain) 
                              \<longrightarrow> x = ?x1"
                           using type_def endpt_reconstruction  by (metis (hide_lams, no_types) "0" endpt.distinct(1) endpt.inject(2) endtype.distinct(1) found_in_element_set less_not_refl vert_17 vert_5)
             moreover have "(z \<in> ?Q) \<and>(fst z = x)\<and>(type x = codomain) 
                                 \<longrightarrow> str_number x = max_codom (block_act ys) + 1"
                                  using str_number_def type_def by auto
             ultimately have 2:"(found_in x (block_act ys)) \<and>(type x = codomain) \<and> (fst z = x) \<longrightarrow>
                                    False"
                                  by auto 
             then have "(found_in x (block_act ys)) \<and>(type x = codomain) \<and> (snd z = x) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((str_number x < max_codom (block_act ys)+1))"
                              using 1 vert_17 by auto
             moreover have "(z \<in> ?Q) \<and>(snd z = x)\<and>(type x = codomain) 
                              \<longrightarrow> x = ?x1"
                           using type_def endpt_reconstruction  
                                by (metis (hide_lams, no_types) "0" endpt.distinct(1) endpt.inject(2) endtype.distinct(1) found_in_element_set less_not_refl vert_17 vert_5)
             moreover have "(z \<in> ?Q) \<and>(snd z = x)\<and>(type x = codomain) 
                                 \<longrightarrow> str_number x = max_codom (block_act ys) + 1"
                                  using str_number_def type_def by auto
             ultimately have 2:"(found_in x (block_act ys)) \<and>(type x = codomain) \<and> (snd z = x) \<longrightarrow>
                                    False"
                                  by auto
             then have "(found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow>
                                   False"
                                       using 1 2 by (metis `found_in x (block_act ys) \<and> type x = endtype.codomain \<and> fst z = x \<longrightarrow> z \<in> {(codom (max_codom (block_act ys) + 1), endpt.dom (max_dom (block_act ys) + 1)), (endpt.dom (max_dom (block_act ys) + 1), codom (max_codom (block_act ys) + 1))} \<and> str_number x < max_codom (block_act ys) + 1` `z \<in> {(codom (max_codom (block_act ys) + 1), endpt.dom (max_dom (block_act ys) + 1)), (endpt.dom (max_dom (block_act ys) + 1), codom (max_codom (block_act ys) + 1))} \<and> fst z = x \<and> type x = endtype.codomain \<longrightarrow> str_number x = max_codom (block_act ys) + 1` less_not_refl3)
             then show False using 0 by (metis `element_set (codom (max_codom (block_act ys) + 1)) (block_act ys) = {}` `element_set (endpt.dom (max_dom (block_act ys) + 1)) (block_act ys) = {}` found_in_element_set vert_5)
            qed
      then have "\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (element_set x ?Q = {}))"
                    using vert_16 endpt.exhaust  by (metis (full_types) endtype.exhaust)
      then have "\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (count_element x ?Q = 0))"
                                     using count_element_def by auto
      then have "\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (count_element x (block_act (y#ys)) = 2))"
                                      using vert_14 vert_3 by auto
      then have "\<forall>x.((found_in x (block_act (y#ys)) \<longrightarrow> (count_element x (block_act (y#ys)) = 2)))"
                      using vert_4 vert_13 by auto
      then show ?thesis  using injective_def by auto
    next
     case cup
     fix a
     let ?Q = "{(codom ((max_codom (block_act ys))+1), codom ((max_codom (block_act ys))+2)),
              (codom ((max_codom (block_act ys))+2), codom ((max_codom (block_act ys))+1))}"
     have cup_0:"finite ?Q \<and> (finite (block_act ys))"
                   using finite_block_act   by auto
     have cup_1:"(block_act (y#ys)) = ?Q \<union> (block_act ys)"
                     using cup by auto
     then have cup_2:"\<forall>a.(element_set a (block_act (y#ys)) = element_set a ?Q 
                                     \<union> element_set a (block_act ys))"  
                            using element_set_def by auto
     have "\<forall>x.(x \<in> ?Q \<longrightarrow> x \<notin> (block_act ys))"
               using max_codom_does_not_belong max_dom_does_not_belong cup_0
                     by (metis (hide_lams, full_types) empty_iff finite_block_act insert_compr insert_iff le_refl nat_add_commute snd_max_codom_does_not_belong snd_max_dom_does_not_belong)
     then have "?Q \<inter> (block_act ys) = {}"
               by auto
     moreover have "\<forall>a.(element_set a ?Q \<subseteq> ?Q)"
                 using subset_element_set by auto 
     moreover have "\<forall>a.(element_set a (block_act ys) \<subseteq> (block_act ys))"
                 using subset_element_set by auto 
     ultimately have cup_12:"\<forall>a.(element_set a ?Q \<inter> element_set a (block_act ys) = {})"
                  using subset_intersection by auto 
     then have cup_3:"\<forall>a.(
                 count_element a  (block_act (y#ys)) = count_element a ?Q 
                                     + count_element a (block_act ys))"  
                           unfolding count_element_def using  card.union_disjoint 
                            cup_0 cup_2 by (metis finite_element_set)
     then have cup_4:"\<forall>x.(found_in x (block_act (y#ys)) 
                         \<longrightarrow> (found_in x (?Q))\<or>(found_in x (block_act ys)))" 
                       using cup_1 found_in_union by auto  
     then have "\<forall>x.((found_in x (?Q))
                        =  
       (x \<in>{codom ((max_codom (block_act ys))+1), codom ((max_codom (block_act ys))+2)}))"    
               using found_in_def by auto
     then have cup_5:
         "\<forall>x.((found_in x (?Q))
                        =  ((x= codom ((max_codom (block_act ys))+1))
                          \<or>(x= codom ((max_codom (block_act ys))+2))))"
                    by auto
         let ?x1 = " codom ((max_codom (block_act ys))+1)"
         let ?x2 = " codom ((max_codom (block_act ys))+2)"
    have "element_set ?x1 (block_act ys) = {} "
                     using element_set_def fst_max_codom_does_not_belong
                           snd_max_codom_does_not_belong element_set_empty by (metis (hide_lams, no_types) finite_block_act order_refl)      
    then have cup_6:"count_element ?x1 (block_act ys) = 0"
                   using count_element_def by auto
    have "element_set ?x2 (block_act ys) = {} "
                     using element_set_def max_dom_does_not_belong element_set_empty 
                               by (metis (full_types) cup_0 max_codom_does_not_belong one_le_numeral)
    then have cup_7:"count_element ?x2 (block_act ys) = 0"
                 using count_element_def by auto
    with cup_6 cup_5 have cup_8:"\<forall>x.((found_in x (?Q))
                           \<longrightarrow> (count_element x (block_act ys)) = 0)"
                              by metis 
    have "element_set ?x1 ?Q = ?Q"
                   unfolding element_set_def by auto 
    then have cup_9:"count_element ?x1 ?Q = 2"
                    using count_element_def by auto
    have "element_set ?x2 ?Q = ?Q"
                   unfolding element_set_def by auto 
    then have cup_10:"count_element ?x2 ?Q = 2"
                    using count_element_def by auto     
    then have cup_11:"\<forall>x.((found_in x (?Q))
                           \<longrightarrow> (count_element x ?Q) = 2)"
                     using cup_9 cup_5 by auto
   then have cup_12:"\<forall>x.((count_element x(block_act (y#ys))) = 
                                   (count_element x ?Q)+ (count_element x (block_act ys)))"
                            using cup_3 by auto   
   then have cup_13:"\<forall>x.((found_in x (?Q))
                           \<longrightarrow> (count_element x (block_act (y#ys))) = 2)"
                            using cup_8 cup_11 by auto 
   have cup_14:"\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (count_element x (block_act ys)) = 2)"
                       using Cons injective_def by auto 
   have cup_15:"\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         (str_number x < max_dom (block_act ys) + 1))"
                                 using str_number_max_dom 
                                 by (metis add_strict_increasing finite_block_act 
                                 nat_add_commute zero_less_one)
    have cup_16:"\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) = {})"
            proof(rule ccontr)
            assume 0:"\<not>(\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) = {}))"
            have "\<exists>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                          using 0 by auto
             then obtain x where "((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                            by auto
             then have "\<exists>y.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         y \<in> element_set x (?Q))"
                            by auto
             then obtain z where "((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         z \<in> element_set x (?Q))"
                             by auto
              then have 1:"(found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((fst z = x)\<or>(snd z = x))"
                              using element_set_def by auto
              then have "(found_in x (block_act ys)) \<and>(type x = domain) \<and> (fst z = x) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((str_number x < max_dom (block_act ys)+1))"
                              using cup_15 by auto
              moreover have "(z \<in> ?Q) \<and>(fst z = x) 
                              \<longrightarrow> type x = codomain"
                           using type_def endpt_reconstruction by (metis "0" cup_14 cup_8 found_in_element_set zero_neq_numeral)
              ultimately have 2:"(found_in x (block_act ys)) \<and>(type x = domain) \<and> (fst z = x) \<longrightarrow>
                                    False"
                                  by auto 
              then have "(found_in x (block_act ys)) \<and>(snd z = x)\<and>(z \<in> ?Q) \<longrightarrow>
                                type x = codomain"
                              using 1 cup_15 by (metis "0" cup_14 cup_8 found_in_element_set zero_neq_numeral)
              
              then have 2:"(found_in x (block_act ys)) \<and>(type x = domain) \<and> (snd z = x) \<longrightarrow>
                                    False"
                                   by (metis `found_in x (block_act ys) \<and> type x = endtype.domain \<longrightarrow> element_set x {(codom (max_codom (block_act ys) + 1), codom (max_codom (block_act ys) + 2)), (codom (max_codom (block_act ys) + 2), codom (max_codom (block_act ys) + 1))} \<noteq> {}` cup_5 endpt.distinct(1) endpt_reconstruction found_in_element_set)
             then have "(found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow>
                                   False"
                                       using 1 2 by (metis `z \<in> {(codom (max_codom (block_act ys) + 1), codom (max_codom (block_act ys) + 2)), (codom (max_codom (block_act ys) + 2), codom (max_codom (block_act ys) + 1))} \<and> fst z = x \<longrightarrow> type x = endtype.codomain` endtype.distinct(1))
             then show False using 0 by (metis `element_set (codom (max_codom (block_act ys) + 1)) (block_act ys) = {}` `element_set (codom (max_codom (block_act ys) + 2)) (block_act ys) = {}` cup_5 found_in_element_set)
           qed
     have cup_17:"\<forall>x.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         (str_number x < max_codom (block_act ys) + 1))"
                                 using str_number_max_codom 
                                 by (metis add_strict_increasing finite_block_act 
                                 nat_add_commute zero_less_one)
   have "\<forall>x.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         element_set x (?Q) = {})"
            proof(rule ccontr)
            assume 0:"\<not>(\<forall>x.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         element_set x (?Q) = {}))"
            have "\<exists>x.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                          using 0 by auto
             then obtain x where "((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                            by auto
             then have "\<exists>y.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         y \<in> element_set x (?Q))"
                            by auto
             then obtain z where "((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         z \<in> element_set x (?Q))"
                             by auto
             then have 1:"(found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((fst z = x)\<or>(snd z = x))"
                              using element_set_def by auto
             then have "(found_in x (block_act ys)) \<and>(type x = codomain) \<and> (fst z = x) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((str_number x < max_codom (block_act ys)+1))"
                              using cup_17 by auto
             moreover have "(z \<in> ?Q) \<and>(fst z = x)\<and>(type x = codomain) 
                              \<longrightarrow> x = ?x1 \<or> x = ?x2"
                        by (metis "0" cup_14 cup_8 found_in_element_set zero_neq_numeral)
              moreover have "(z \<in> ?Q) \<and>(fst z = x)\<and>(type x = codomain) 
                                 \<longrightarrow> (str_number x = max_codom (block_act ys) + 2)
                                     \<or>(str_number x = max_codom (block_act ys) + 1)"
                                  using str_number_def type_def by auto
              ultimately have 2:"(found_in x (block_act ys)) \<and>(type x = codomain) \<and> (fst z = x) \<longrightarrow>
                                    False"
                                  by auto 
              then have "(found_in x (block_act ys)) \<and>(type x = codomain) \<and> (snd z = x) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((str_number x < max_codom (block_act ys)+1))"
                              using 1 cup_17 by auto
              moreover have "(z \<in> ?Q) \<and>(snd z = x)\<and>(type x = codomain) 
                              \<longrightarrow> x = ?x1 \<or> x = ?x2"
                           using type_def endpt_reconstruction  
                          by (metis "0" `element_set (codom (max_codom (block_act ys) + 1)) (block_act ys) = {}` `element_set (codom (max_codom (block_act ys) + 2)) (block_act ys) = {}` cup_5 found_in_element_set)   
            moreover have "(z \<in> ?Q) \<and>(snd z = x)\<and>(type x = codomain) 
                                 \<longrightarrow> str_number x = max_codom (block_act ys) + 1
                                     \<or> str_number x = max_codom (block_act ys) + 2"
                                  using str_number_def type_def by auto
              ultimately have 3:"(found_in x (block_act ys)) \<and>(type x = codomain) \<and> (snd z = x) \<longrightarrow>
                                    False"
                                  by auto
             then have "(found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow>
                                   False"
                                       using 1 2 
                          by metis
            then show False using 0 by (metis `element_set (codom (max_codom (block_act ys) + 1)) (block_act ys) = {}` `element_set (codom (max_codom (block_act ys) + 2)) (block_act ys) = {}` cup_5 found_in_element_set)
           qed
      then have "\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (element_set x ?Q = {}))"
                    using cup_16 endpt.exhaust  by (metis (full_types) endtype.exhaust)
      then have "\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (count_element x ?Q = 0))"
                                     using count_element_def by auto
      then have "\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (count_element x (block_act (y#ys)) = 2))"
                                      using cup_14 cup_3 by auto
      then have "\<forall>x.((found_in x (block_act (y#ys)) \<longrightarrow> (count_element x (block_act (y#ys)) = 2)))"
                      using cup_4 cup_13 by auto
      then show ?thesis  using injective_def by auto
    next       
    case cap
     fix a
     let ?Q = "{(dom ((max_dom (block_act ys))+1), dom ((max_dom (block_act ys))+2)),
              (dom ((max_dom (block_act ys))+2), dom ((max_dom (block_act ys))+1))}"
     have cap_0:"finite ?Q \<and> (finite (block_act ys))"
                   using finite_block_act   by auto
     have cap_1:"(block_act (y#ys)) = ?Q \<union> (block_act ys)"
                     using cap by auto
     then have cap_2:"\<forall>a.(element_set a (block_act (y#ys)) = element_set a ?Q 
                                     \<union> element_set a (block_act ys))"  
                            using element_set_def by auto
     have "\<forall>x.(x \<in> ?Q \<longrightarrow> x \<notin> (block_act ys))"
               using max_dom_does_not_belong cap_0
                     by (metis (hide_lams, full_types) empty_iff finite_block_act insert_compr insert_iff le_refl nat_add_commute snd_max_codom_does_not_belong snd_max_dom_does_not_belong)
     then have "?Q \<inter> (block_act ys) = {}"
               by auto
     moreover have "\<forall>a.(element_set a ?Q \<subseteq> ?Q)"
                 using subset_element_set by auto 
     moreover have "\<forall>a.(element_set a (block_act ys) \<subseteq> (block_act ys))"
                 using subset_element_set by auto 
     ultimately have cap_12:"\<forall>a.(element_set a ?Q \<inter> element_set a (block_act ys) = {})"
                  using subset_intersection by auto 
     then have cap_3:"\<forall>a.(
                 count_element a  (block_act (y#ys)) = count_element a ?Q 
                                     + count_element a (block_act ys))"  
                           unfolding count_element_def using  card.union_disjoint 
                            cap_0 cap_2 by (metis finite_element_set)
     then have cap_4:"\<forall>x.(found_in x (block_act (y#ys)) 
                         \<longrightarrow> (found_in x (?Q))\<or>(found_in x (block_act ys)))" 
                       using cap_1 found_in_union by auto  
     then have "\<forall>x.((found_in x (?Q))
                        =  
       (x \<in>{dom ((max_dom (block_act ys))+1), dom ((max_dom (block_act ys))+2)}))"    
               using found_in_def by auto
     then have cap_5:
         "\<forall>x.((found_in x (?Q))
                        =  ((x= dom ((max_dom (block_act ys))+1))
                          \<or>(x= dom ((max_dom (block_act ys))+2))))"
                    by auto
         let ?x1 = " dom ((max_dom (block_act ys))+1)"
         let ?x2 = " dom ((max_dom (block_act ys))+2)"
    have "element_set ?x1 (block_act ys) = {} "
                     using element_set_def fst_max_dom_does_not_belong
                           snd_max_dom_does_not_belong element_set_empty by (metis (hide_lams, no_types) finite_block_act order_refl)      
    then have cap_6:"count_element ?x1 (block_act ys) = 0"
                   using count_element_def by auto
    have "element_set ?x2 (block_act ys) = {} "
                     using element_set_def max_codom_does_not_belong element_set_empty 
                      by (metis (full_types) cap_0 le_add2 max_dom_does_not_belong one_add_one)
    then have cap_7:"count_element ?x2 (block_act ys) = 0"
                 using count_element_def by auto
    with cap_6 cap_5 have cap_8:"\<forall>x.((found_in x (?Q))
                           \<longrightarrow> (count_element x (block_act ys)) = 0)"
                              by metis 
    have "element_set ?x1 ?Q = ?Q"
                   unfolding element_set_def by auto 
    then have cap_9:"count_element ?x1 ?Q = 2"
                    using count_element_def by auto
    have "element_set ?x2 ?Q = ?Q"
                   unfolding element_set_def by auto 
    then have cap_10:"count_element ?x2 ?Q = 2"
                    using count_element_def by auto     
    then have cap_11:"\<forall>x.((found_in x (?Q))
                           \<longrightarrow> (count_element x ?Q) = 2)"
                     using cap_9 cap_5 by auto
   then have cap_12:"\<forall>x.((count_element x(block_act (y#ys))) = 
                                   (count_element x ?Q)+ (count_element x (block_act ys)))"
                            using cap_3 by auto   
   then have cap_13:"\<forall>x.((found_in x (?Q))
                           \<longrightarrow> (count_element x (block_act (y#ys))) = 2)"
                            using cap_8 cap_11 by auto 
   have cap_14:"\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (count_element x (block_act ys)) = 2)"
                       using Cons injective_def by auto 
   have cap_15:"\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         (str_number x < max_dom (block_act ys) + 1))"
                                 using str_number_max_dom 
                                 by (metis add_strict_increasing finite_block_act 
                                 nat_add_commute zero_less_one)
    have cap_16:"\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) = {})"
            proof(rule ccontr)
            assume 0:"\<not>(\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) = {}))"
            have "\<exists>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                          using 0 by auto
             then obtain x where "((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                            by auto
             then have "\<exists>y.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         y \<in> element_set x (?Q))"
                            by auto
             then obtain z where "((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         z \<in> element_set x (?Q))"
                             by auto
              then have 1:"(found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((fst z = x)\<or>(snd z = x))"
                              using element_set_def by auto
              then have "(found_in x (block_act ys)) \<and>(type x = domain) \<and> (fst z = x) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((str_number x < max_dom (block_act ys)+1))"
                              using cap_15 by auto
              moreover have "(z \<in> ?Q) \<and>(fst z = x) 
                              \<longrightarrow> type x = codomain"
                           using type_def endpt_reconstruction by (metis "0" cap_14 cap_8 found_in_element_set zero_neq_numeral)
              ultimately have 2:"(found_in x (block_act ys)) \<and>(type x = domain) \<and> (fst z = x) \<longrightarrow>
                                    False"
                                  by auto 
              then have "(found_in x (block_act ys)) \<and>(snd z = x)\<and>(z \<in> ?Q) \<longrightarrow>
                                type x = codomain"
                              using 1 by (metis "0" cap_14 cap_8 found_in_element_set zero_neq_numeral)
              then have 2:"(found_in x (block_act ys)) \<and>(type x = domain) \<and> (snd z = x) \<longrightarrow>
                                    False"
                                    by (metis "1" `found_in x (block_act ys) \<and> snd z = x \<and> z \<in> {(endpt.dom (max_dom (block_act ys) + 1), endpt.dom (max_dom (block_act ys) + 2)), (endpt.dom (max_dom (block_act ys) + 2), endpt.dom (max_dom (block_act ys) + 1))} \<longrightarrow> type x = endtype.codomain` endtype.distinct(1))
              then have "(found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow>
                                   False"
                                       using 1 2 by (metis `z \<in> {(endpt.dom (max_dom (block_act ys) + 1), endpt.dom (max_dom (block_act ys) + 2)), (endpt.dom (max_dom (block_act ys) + 2), endpt.dom (max_dom (block_act ys) + 1))} \<and> fst z = x \<longrightarrow> type x = endtype.codomain` endtype.distinct(1))
          then show False using 0 
          by (metis `element_set (endpt.dom (max_dom (block_act ys) + 1)) (block_act ys) = {}` `element_set (endpt.dom (max_dom (block_act ys) + 2)) (block_act ys) = {}` cap_5 found_in_element_set)
          qed
     have cap_17:"\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         (str_number x < max_dom (block_act ys) + 1))"
                                 using str_number_max_dom 
                                 by (metis add_strict_increasing finite_block_act 
                                 nat_add_commute zero_less_one)
   have "\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) = {})"
            proof(rule ccontr)
            assume 0:"\<not>(\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) = {}))"
            have "\<exists>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                          using 0 by auto
             then obtain x where "((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                            by auto
             then have "\<exists>y.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         y \<in> element_set x (?Q))"
                            by auto
             then obtain z where "((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         z \<in> element_set x (?Q))"
                             by auto
             then have 1:"(found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((fst z = x)\<or>(snd z = x))"
                              using element_set_def by auto
             then have "(found_in x (block_act ys)) \<and>(type x = domain) \<and> (fst z = x) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((str_number x < max_dom (block_act ys)+1))"
                              using cap_17 by auto
             moreover have "(z \<in> ?Q) \<and>(fst z = x)\<and>(type x = domain) 
                              \<longrightarrow> x = ?x1 \<or> x = ?x2"
                        by (metis "0" cap_14 cap_8 found_in_element_set zero_neq_numeral)
              moreover have "(z \<in> ?Q) \<and>(fst z = x)\<and>(type x = domain) 
                                 \<longrightarrow> (str_number x = max_dom (block_act ys) + 2)
                                     \<or>(str_number x = max_dom (block_act ys) + 1)"
                                  using str_number_def type_def by auto
              ultimately have 2:"(found_in x (block_act ys)) \<and>(type x = domain) \<and> (fst z = x) \<longrightarrow>
                                    False"
                                  by auto 
              then have "(found_in x (block_act ys)) \<and>(type x = domain) \<and> (snd z = x) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((str_number x < max_dom (block_act ys)+1))"
                              using 1 cap_17 by auto
              moreover have "(z \<in> ?Q) \<and>(snd z = x)\<and>(type x = domain) 
                              \<longrightarrow> x = ?x1 \<or> x = ?x2"
                           using type_def endpt_reconstruction  
                        by (metis "0" cap_16)     
            moreover have "(z \<in> ?Q) \<and>(snd z = x)\<and>(type x = domain) 
                                 \<longrightarrow> str_number x = max_dom (block_act ys) + 1
                                     \<or> str_number x = max_dom (block_act ys) + 2"
                                  using str_number_def type_def by auto
              ultimately have 3:"(found_in x (block_act ys)) \<and>(type x = domain) \<and> (snd z = x) \<longrightarrow>
                                    False"
                                  by auto
             then have "(found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow>
                                   False"
                                       using 1 2 
                          by metis
            then show False using 0 
                      by (metis cap_16)
         qed
      then have "\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (element_set x ?Q = {}))"
                    using cap_16 endpt.exhaust 
                     by (metis (hide_lams, no_types) cap_14 cap_8 found_in_element_set zero_neq_numeral)
      then have "\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (count_element x ?Q = 0))"
                                     using count_element_def by auto
      then have "\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (count_element x (block_act (y#ys)) = 2))"
                                      using cap_14 cap_3 by auto
      then have "\<forall>x.((found_in x (block_act (y#ys)) \<longrightarrow> (count_element x (block_act (y#ys)) = 2)))"
                      using cap_4 cap_13 by auto
      then show ?thesis  using injective_def by auto
    next       
     case over
     fix a
     let ?Q = "{(dom ((max_dom (block_act ys))+1), codom ((max_codom (block_act ys))+2)),
              (codom ((max_codom (block_act ys))+2), dom ((max_dom (block_act ys))+1)),
               (dom ((max_dom (block_act ys))+2), codom ((max_codom (block_act ys))+1)),
              (codom ((max_codom (block_act ys))+1), dom ((max_dom (block_act ys))+2))
                  }"
     have geq_2:"(2::nat) \<ge> 1"
                    by auto
     have over_0:"finite ?Q \<and> (finite (block_act ys))"
                   using finite_block_act   by auto
     have over_1:"(block_act (y#ys)) = ?Q \<union> (block_act ys)"
                     using over swap_act_def   by auto
     then have over_2:"\<forall>a.(element_set a (block_act (y#ys)) = element_set a ?Q 
                                     \<union> element_set a (block_act ys))"  
                            using element_set_def by auto
         let ?x1 = " codom ((max_codom (block_act ys))+1)"
         let ?x2 = " codom ((max_codom (block_act ys))+2)"  
         let ?y1 = " dom ((max_dom (block_act ys))+1)"
         let ?y2 = " dom ((max_dom (block_act ys))+2)" 
     have "\<forall>x.(x \<in> ?Q \<longrightarrow> x \<notin> (block_act ys))"
          proof-
          have "(dom ((max_dom (block_act ys))+1), codom ((max_codom (block_act ys))+2)) 
                                \<notin> (block_act ys)"          
                        using max_codom_does_not_belong max_dom_does_not_belong over_0
                        by (metis one_le_numeral)     
          moreover have 
                "(codom ((max_codom (block_act ys))+2), dom ((max_codom (block_act ys))+1)) 
                                \<notin> (block_act ys)" 
                           using max_codom_does_not_belong geq_2
                            finite_block_act by metis
          moreover have 
                 "(dom ((max_dom (block_act ys))+2), codom ((max_codom (block_act ys))+1)) 
                                \<notin> (block_act ys)"  
                             using max_dom_does_not_belong geq_2 finite_block_act
                               by metis
          moreover have 
                "(codom ((max_codom (block_act ys))+1), dom ((max_codom (block_act ys))+2)) 
                                \<notin> (block_act ys)" 
                           using max_codom_does_not_belong finite_block_act 
                                by (metis eq_imp_le)
          moreover have "\<forall>x.(x \<in> ?Q 
                               \<longrightarrow>
                              (x = (?x1, ?y2))\<or>(x= (?x2, ?y1)) \<or>(x =(?y2, ?x1)) \<or> (x =(?y1, ?x2)))"
                                by auto
          ultimately show ?thesis using allI  by (metis finite_block_act le_numeral_extra(4) max_codom_does_not_belong one_le_numeral)
         qed  
     then have "?Q \<inter> (block_act ys) = {}"
               by auto
     moreover have "\<forall>a.(element_set a ?Q \<subseteq> ?Q)"
                 using subset_element_set by auto 
     moreover have "\<forall>a.(element_set a (block_act ys) \<subseteq> (block_act ys))"
                 using subset_element_set by auto 
     ultimately have over_12:"\<forall>a.(element_set a ?Q \<inter> element_set a (block_act ys) = {})"
                  using subset_intersection by auto 
     then have over_3:"\<forall>a.(
                 count_element a  (block_act (y#ys)) = count_element a ?Q 
                                     + count_element a (block_act ys))"  
                           unfolding count_element_def using  card.union_disjoint 
                            over_0 over_2 by (metis finite_element_set)
     then have over_4:"\<forall>x.(found_in x (block_act (y#ys)) 
                         \<longrightarrow> (found_in x (?Q))\<or>(found_in x (block_act ys)))" 
                       using over_1 found_in_union by auto  
     then have "\<forall>x.((found_in x (?Q))
                        =  
       (x \<in>{codom ((max_codom (block_act ys))+1), codom ((max_codom (block_act ys))+2)
            ,dom ((max_dom (block_act ys))+1), dom ((max_dom (block_act ys))+2)}))"    
               using found_in_def by auto
     then have over_5:
         "\<forall>x.((found_in x (?Q))
                        =  ((x= codom ((max_codom (block_act ys))+1))
                          \<or>(x= codom ((max_codom (block_act ys))+2)))
                          \<or>(x = dom ((max_dom (block_act ys))+1))
                          \<or>(x = dom ((max_dom (block_act ys))+2)))"
                    by auto
     have "element_set ?x1 (block_act ys) = {} "
                     using element_set_def fst_max_codom_does_not_belong
                           snd_max_codom_does_not_belong element_set_empty by (metis (hide_lams, no_types) finite_block_act order_refl)      
    then have over_6:"count_element ?x1 (block_act ys) = 0"
                   using count_element_def by auto
    have "element_set ?x2 (block_act ys) = {} "
                     using element_set_def max_codom_does_not_belong element_set_empty geq_2 
                      finite_block_act
                     by (metis one_add_one)
    then have over_7:"count_element ?x2 (block_act ys) = 0"
                 using count_element_def by auto
     have "element_set ?y1 (block_act ys) = {} "
                     using element_set_def fst_max_dom_does_not_belong
                           snd_max_dom_does_not_belong element_set_empty 
                           by (metis (hide_lams, no_types) finite_block_act order_refl)      
    then have over_8:"count_element ?y1 (block_act ys) = 0"
                   using count_element_def by auto
    have "element_set ?y2 (block_act ys) = {} "
                     using element_set_def max_dom_does_not_belong element_set_empty geq_2 
                      finite_block_act
                     by (metis one_add_one)
    then have over_9:"count_element ?y2 (block_act ys) = 0"
                 using count_element_def by auto
    with over_6 over_5 over_8  over_7 have over_10:"\<forall>x.((found_in x (?Q))
                           \<longrightarrow> (count_element x (block_act ys)) = 0)"
                              by metis 
    have "element_set ?x1 ?Q = {(?x1,?y2),(?y2,?x1)}"
                   unfolding element_set_def by auto 
    then have over_11:"count_element ?x1 ?Q = 2"
                    using count_element_def by auto
    have "element_set ?x2 ?Q =  {(?x2,?y1),(?y1,?x2)}"
                   unfolding element_set_def by auto 
    then have over_12:"count_element ?x2 ?Q = 2"
                    using count_element_def by auto     
     have "element_set ?y1 ?Q = {(?y1,?x2),(?x2,?y1)}"
                   unfolding element_set_def by auto 
    then have over_13:"count_element ?y1 ?Q = 2"
                    using count_element_def by auto
    have "element_set ?y2 ?Q =  {(?y2,?x1),(?x1,?y2)}"
                   unfolding element_set_def by auto 
    then have over_14:"count_element ?y2 ?Q = 2"
                    using count_element_def by auto     
    then have over_15:"\<forall>x.((found_in x (?Q))
                           \<longrightarrow> (count_element x ?Q) = 2)"
                     using over_11 over_12 over_13 over_5 by metis
   then have over_16:"\<forall>x.((count_element x(block_act (y#ys))) = 
                                   (count_element x ?Q)+ (count_element x (block_act ys)))"
                            using over_3 by auto   
   then have over_17:"\<forall>x.((found_in x (?Q))
                           \<longrightarrow> (count_element x (block_act (y#ys))) = 2)"
                            using over_10 over_15 by auto 
   have over_18:"\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (count_element x (block_act ys)) = 2)"
                       using Cons injective_def by auto 
   have over_19:"\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         (str_number x < max_dom (block_act ys) + 1))"
                                 using str_number_max_dom 
                                 by (metis add_strict_increasing finite_block_act 
                                 nat_add_commute zero_less_one)
    have over_20:"\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) = {})"
            proof(rule ccontr)
            assume 0:"\<not>(\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) = {}))"
            have "\<exists>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                          using 0 by auto
             then obtain x where "((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                            by auto
             then have "\<exists>y.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         y \<in> element_set x (?Q))"
                            by auto
             then obtain z where "((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         z \<in> element_set x (?Q))"
                             by auto
              then have 1:"(found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((fst z = x)\<or>(snd z = x))"
                              using element_set_def by auto
              then have "(found_in x (block_act ys)) \<and>(type x = domain) \<and> (fst z = x) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((str_number x < max_dom (block_act ys)+1))"
                              using over_19 by auto
              moreover have "(z \<in> ?Q) \<and>(fst z = x) 
                              \<longrightarrow> type x = codomain"
                           using type_def endpt_reconstruction 
                             by (metis "0" `element_set (endpt.dom (max_dom (block_act ys) + 1)) (block_act ys) = {}` `element_set (endpt.dom (max_dom (block_act ys) + 2)) (block_act ys) = {}` endpt.distinct(1) found_in_element_set over_5)
             ultimately have 2:"(found_in x (block_act ys)) \<and>(type x = domain) \<and> (fst z = x) \<longrightarrow>
                                    False"
                                  by auto 
              then have "(found_in x (block_act ys)) \<and>(snd z = x)\<and>(z \<in> ?Q) \<longrightarrow>
                                type x = codomain"
                              using 1 over_19
                             by (metis "0" found_in_element_set over_10 over_18 zero_neq_numeral)              
              then have 3:"(found_in x (block_act ys)) \<and>(type x = domain) \<and> (snd z = x) \<longrightarrow>
                                    False"
                       by (metis "1" `found_in x (block_act ys) \<and> snd z = x \<and> z \<in> {(endpt.dom (max_dom (block_act ys) + 1), codom (max_codom (block_act ys) + 2)), (codom (max_codom (block_act ys) + 2), endpt.dom (max_dom (block_act ys) + 1)), (endpt.dom (max_dom (block_act ys) + 2), codom (max_codom (block_act ys) + 1)), (codom (max_codom (block_act ys) + 1), endpt.dom (max_dom (block_act ys) + 2))} \<longrightarrow> type x = endtype.codomain` endtype.distinct(1))         
             then have "(found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow>
                                   False"
                                       using 1 2 by metis
            then show False using 0 by (metis `element_set (codom (max_codom (block_act ys) + 1)) (block_act ys) = {}` `element_set (codom (max_codom (block_act ys) + 2)) (block_act ys) = {}` `element_set (endpt.dom (max_dom (block_act ys) + 1)) (block_act ys) = {}` `element_set (endpt.dom (max_dom (block_act ys) + 2)) (block_act ys) = {}` found_in_element_set over_5)
           qed
     have over_21:"\<forall>x.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         (str_number x < max_codom (block_act ys) + 1))"
                                 using str_number_max_codom 
                                 by (metis add_strict_increasing finite_block_act 
                                 nat_add_commute zero_less_one)
   have "\<forall>x.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         element_set x (?Q) = {})"
            proof(rule ccontr)
            assume 0:"\<not>(\<forall>x.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         element_set x (?Q) = {}))"
            have "\<exists>x.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                          using 0 by auto
             then obtain x where "((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                            by auto
             then have "\<exists>y.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         y \<in> element_set x (?Q))"
                            by auto
             then obtain z where "((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         z \<in> element_set x (?Q))"
                             by auto
             then have 1:"(found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((fst z = x)\<or>(snd z = x))"
                              using element_set_def by auto
             then have "(found_in x (block_act ys)) \<and>(type x = codomain) \<and> (fst z = x) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((str_number x < max_codom (block_act ys)+1))"
                              using over_21 by auto
             moreover have "(z \<in> ?Q) \<and>(fst z = x)\<and>(type x = codomain) 
                              \<longrightarrow> x = ?x1 \<or> x = ?x2"
                        by (metis "0" over_18 over_10 found_in_element_set zero_neq_numeral)
              moreover have "(z \<in> ?Q) \<and>(fst z = x)\<and>(type x = codomain) 
                                 \<longrightarrow> (str_number x = max_codom (block_act ys) + 2)
                                     \<or>(str_number x = max_codom (block_act ys) + 1)"
                                  using str_number_def type_def by auto
              ultimately have 2:"(found_in x (block_act ys)) \<and>(type x = codomain) \<and> (fst z = x) \<longrightarrow>
                                    False"
                                  by auto 
              then have "(found_in x (block_act ys)) \<and>(type x = codomain) \<and> (snd z = x) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((str_number x < max_codom (block_act ys)+1))"
                              using 1 over_21 by auto
              moreover have "(z \<in> ?Q) \<and>(snd z = x)\<and>(type x = codomain) 
                              \<longrightarrow> x = ?x1 \<or> x = ?x2"
                           using type_def endpt_reconstruction  
                                    by (metis "0" `element_set (codom (max_codom (block_act ys) + 1)) (block_act ys) = {}` `element_set (codom (max_codom (block_act ys) + 2)) (block_act ys) = {}` endpt.distinct(1) endtype.distinct(1) found_in_element_set over_5)
              moreover have "(z \<in> ?Q) \<and>(snd z = x)\<and>(type x = codomain) 
                                 \<longrightarrow> str_number x = max_codom (block_act ys) + 1
                                     \<or> str_number x = max_codom (block_act ys) + 2"
                                  using str_number_def type_def by auto
              ultimately have 3:"(found_in x (block_act ys)) \<and>(type x = codomain) \<and> (snd z = x) \<longrightarrow>
                                    False"
                                  by auto
              then have "(found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow>
                                   False"
                                       using 1 2 
                          by metis
            then show False using 0 by (metis `element_set (codom (max_codom (block_act ys) + 1)) (block_act ys) = {}` `element_set (codom (max_codom (block_act ys) + 2)) (block_act ys) = {}` `element_set (endpt.dom (max_dom (block_act ys) + 1)) (block_act ys) = {}` `element_set (endpt.dom (max_dom (block_act ys) + 2)) (block_act ys) = {}` found_in_element_set over_5)
       qed
      then have "\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (element_set x ?Q = {}))"
                    using over_20 endpt.exhaust  by (metis (full_types) endtype.exhaust)
      then have "\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (count_element x ?Q = 0))"
                                     using count_element_def by auto
      then have "\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (count_element x (block_act (y#ys)) = 2))"
                                      using over_18 over_3 by auto
      then have "\<forall>x.((found_in x (block_act (y#ys)) \<longrightarrow> (count_element x (block_act (y#ys)) = 2)))"
                      using over_4 over_17 by auto
      then show ?thesis  using injective_def by auto
    next       
    case under
     let ?Q = "{(dom ((max_dom (block_act ys))+1), codom ((max_codom (block_act ys))+2)),
              (codom ((max_codom (block_act ys))+2), dom ((max_dom (block_act ys))+1)),
               (dom ((max_dom (block_act ys))+2), codom ((max_codom (block_act ys))+1)),
              (codom ((max_codom (block_act ys))+1), dom ((max_dom (block_act ys))+2))
                  }"
     have geq_2:"(2::nat) \<ge> 1"
                    by auto
     have under_0:"finite ?Q \<and> (finite (block_act ys))"
                   using finite_block_act   by auto
     have under_1:"(block_act (y#ys)) = ?Q \<union> (block_act ys)"
                     using under swap_act_def by auto  
     then have under_2:"\<forall>a.(element_set a (block_act (y#ys)) = element_set a ?Q 
                                     \<union> element_set a (block_act ys))"  
                            using element_set_def by auto
         let ?x1 = " codom ((max_codom (block_act ys))+1)"
         let ?x2 = " codom ((max_codom (block_act ys))+2)"  
         let ?y1 = " dom ((max_dom (block_act ys))+1)"
         let ?y2 = " dom ((max_dom (block_act ys))+2)" 
     have "\<forall>x.(x \<in> ?Q \<longrightarrow> x \<notin> (block_act ys))"
          proof-
          have "(dom ((max_dom (block_act ys))+1), codom ((max_codom (block_act ys))+2)) 
                                \<notin> (block_act ys)"          
                        using max_codom_does_not_belong max_dom_does_not_belong under_0
                        by (metis one_le_numeral)     
          moreover have 
                "(codom ((max_codom (block_act ys))+2), dom ((max_codom (block_act ys))+1)) 
                                \<notin> (block_act ys)" 
                           using max_codom_does_not_belong geq_2
                            finite_block_act by metis
          moreover have 
                 "(dom ((max_dom (block_act ys))+2), codom ((max_codom (block_act ys))+1)) 
                                \<notin> (block_act ys)"  
                             using max_dom_does_not_belong geq_2 finite_block_act
                               by metis
          moreover have 
                "(codom ((max_codom (block_act ys))+1), dom ((max_codom (block_act ys))+2)) 
                                \<notin> (block_act ys)" 
                           using max_codom_does_not_belong finite_block_act 
                                by (metis eq_imp_le)
          moreover have "\<forall>x.(x \<in> ?Q 
                               \<longrightarrow>
                              (x = (?x1, ?y2))\<or>(x= (?x2, ?y1)) \<or>(x =(?y2, ?x1)) \<or> (x =(?y1, ?x2)))"
                                by auto
          ultimately show ?thesis by (metis finite_block_act le_numeral_extra(4) max_codom_does_not_belong one_le_numeral)
         qed  
     then have "?Q \<inter> (block_act ys) = {}"
               by auto
     moreover have "\<forall>a.(element_set a ?Q \<subseteq> ?Q)"
                 using subset_element_set by auto 
     moreover have "\<forall>a.(element_set a (block_act ys) \<subseteq> (block_act ys))"
                 using subset_element_set by auto 
     ultimately have under_12:"\<forall>a.(element_set a ?Q \<inter> element_set a (block_act ys) = {})"
                  using subset_intersection by auto 
     then have under_3:"\<forall>a.(
                 count_element a  (block_act (y#ys)) = count_element a ?Q 
                                     + count_element a (block_act ys))"  
                           unfolding count_element_def using  card.union_disjoint 
                            under_0 under_2 by (metis finite_element_set)
     then have under_4:"\<forall>x.(found_in x (block_act (y#ys)) 
                         \<longrightarrow> (found_in x (?Q))\<or>(found_in x (block_act ys)))" 
                       using under_1 found_in_union by auto  
     then have "\<forall>x.((found_in x (?Q))
                        =  
       (x \<in>{codom ((max_codom (block_act ys))+1), codom ((max_codom (block_act ys))+2)
            ,dom ((max_dom (block_act ys))+1), dom ((max_dom (block_act ys))+2)}))"    
               using found_in_def by auto
     then have under_5:
         "\<forall>x.((found_in x (?Q))
                        =  ((x= codom ((max_codom (block_act ys))+1))
                          \<or>(x= codom ((max_codom (block_act ys))+2)))
                          \<or>(x = dom ((max_dom (block_act ys))+1))
                          \<or>(x = dom ((max_dom (block_act ys))+2)))"
                    by auto
     have "element_set ?x1 (block_act ys) = {} "
                     using element_set_def fst_max_codom_does_not_belong
                           snd_max_codom_does_not_belong element_set_empty by (metis (hide_lams, no_types) finite_block_act order_refl)      
    then have under_6:"count_element ?x1 (block_act ys) = 0"
                   using count_element_def by auto
    have "element_set ?x2 (block_act ys) = {} "
                     using element_set_def max_codom_does_not_belong element_set_empty geq_2 
                      finite_block_act
                     by (metis one_add_one)
    then have under_7:"count_element ?x2 (block_act ys) = 0"
                 using count_element_def by auto
     have "element_set ?y1 (block_act ys) = {} "
                     using element_set_def fst_max_dom_does_not_belong
                           snd_max_dom_does_not_belong element_set_empty 
                           by (metis (hide_lams, no_types) finite_block_act order_refl)      
    then have under_8:"count_element ?y1 (block_act ys) = 0"
                   using count_element_def by auto
    have "element_set ?y2 (block_act ys) = {} "
                     using element_set_def max_dom_does_not_belong element_set_empty geq_2 
                      finite_block_act
                     by (metis one_add_one)
    then have under_9:"count_element ?y2 (block_act ys) = 0"
                 using count_element_def by auto
    with under_6 under_5 under_8  under_7 have under_10:"\<forall>x.((found_in x (?Q))
                           \<longrightarrow> (count_element x (block_act ys)) = 0)"
                              by metis 
    have "element_set ?x1 ?Q = {(?x1,?y2),(?y2,?x1)}"
                   unfolding element_set_def by auto 
    then have under_11:"count_element ?x1 ?Q = 2"
                    using count_element_def by auto
    have "element_set ?x2 ?Q =  {(?x2,?y1),(?y1,?x2)}"
                   unfolding element_set_def by auto 
    then have under_12:"count_element ?x2 ?Q = 2"
                    using count_element_def by auto     
     have "element_set ?y1 ?Q = {(?y1,?x2),(?x2,?y1)}"
                   unfolding element_set_def by auto 
    then have under_13:"count_element ?y1 ?Q = 2"
                    using count_element_def by auto
    have "element_set ?y2 ?Q =  {(?y2,?x1),(?x1,?y2)}"
                   unfolding element_set_def by auto 
    then have under_14:"count_element ?y2 ?Q = 2"
                    using count_element_def by auto     
    then have under_15:"\<forall>x.((found_in x (?Q))
                           \<longrightarrow> (count_element x ?Q) = 2)"
                     using under_11 under_12 under_13 under_5 by metis
   then have under_16:"\<forall>x.((count_element x(block_act (y#ys))) = 
                                   (count_element x ?Q)+ (count_element x (block_act ys)))"
                            using under_3 by auto   
   then have under_17:"\<forall>x.((found_in x (?Q))
                           \<longrightarrow> (count_element x (block_act (y#ys))) = 2)"
                            using under_10 under_15 by auto 
   have under_18:"\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (count_element x (block_act ys)) = 2)"
                       using Cons injective_def by auto 
   have under_19:"\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         (str_number x < max_dom (block_act ys) + 1))"
                                 using str_number_max_dom 
                                 by (metis add_strict_increasing finite_block_act 
                                 nat_add_commute zero_less_one)
    have under_20:"\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) = {})"
            proof(rule ccontr)
            assume 0:"\<not>(\<forall>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) = {}))"
            have "\<exists>x.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                          using 0 by auto
             then obtain x where "((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                            by auto
             then have "\<exists>y.((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         y \<in> element_set x (?Q))"
                            by auto
             then obtain z where "((found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow> 
                         z \<in> element_set x (?Q))"
                             by auto
              then have 1:"(found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((fst z = x)\<or>(snd z = x))"
                              using element_set_def by auto
              then have "(found_in x (block_act ys)) \<and>(type x = domain) \<and> (fst z = x) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((str_number x < max_dom (block_act ys)+1))"
                              using under_19 by auto
              moreover have "(z \<in> ?Q) \<and>(fst z = x) 
                              \<longrightarrow> type x = codomain"
                           using type_def endpt_reconstruction 
                             by (metis "0" `element_set (endpt.dom (max_dom (block_act ys) + 1)) (block_act ys) = {}` `element_set (endpt.dom (max_dom (block_act ys) + 2)) (block_act ys) = {}` endpt.distinct(1) found_in_element_set under_5)
             ultimately have 2:"(found_in x (block_act ys)) \<and>(type x = domain) \<and> (fst z = x) \<longrightarrow>
                                    False"
                                  by auto 
              then have "(found_in x (block_act ys)) \<and>(snd z = x)\<and>(z \<in> ?Q) \<longrightarrow>
                                type x = codomain"
                              using 1 under_19
                             by (metis "0" found_in_element_set under_10 under_18 zero_neq_numeral)              
              then have 3:"(found_in x (block_act ys)) \<and>(type x = domain) \<and> (snd z = x) \<longrightarrow>
                                    False"
                           by (metis "1" `found_in x (block_act ys) \<and> snd z = x \<and> z \<in> {(endpt.dom (max_dom (block_act ys) + 1), codom (max_codom (block_act ys) + 2)), (codom (max_codom (block_act ys) + 2), endpt.dom (max_dom (block_act ys) + 1)), (endpt.dom (max_dom (block_act ys) + 2), codom (max_codom (block_act ys) + 1)), (codom (max_codom (block_act ys) + 1), endpt.dom (max_dom (block_act ys) + 2))} \<longrightarrow> type x = endtype.codomain` endtype.distinct(1))
              then have "(found_in x (block_act ys)) \<and>(type x = domain) \<longrightarrow>
                                   False"
                                       using 1 2 by metis
            then show False using 0 by (metis `element_set (codom (max_codom (block_act ys) + 1)) (block_act ys) = {}` `element_set (codom (max_codom (block_act ys) + 2)) (block_act ys) = {}` `element_set (endpt.dom (max_dom (block_act ys) + 1)) (block_act ys) = {}` `element_set (endpt.dom (max_dom (block_act ys) + 2)) (block_act ys) = {}` found_in_element_set under_5)
           qed
     have under_21:"\<forall>x.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         (str_number x < max_codom (block_act ys) + 1))"
                                 using str_number_max_codom 
                                 by (metis add_strict_increasing finite_block_act 
                                 nat_add_commute zero_less_one)
   have "\<forall>x.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         element_set x (?Q) = {})"
            proof(rule ccontr)
            assume 0:"\<not>(\<forall>x.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         element_set x (?Q) = {}))"
            have "\<exists>x.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                          using 0 by auto
             then obtain x where "((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         element_set x (?Q) \<noteq> {})"
                            by auto
             then have "\<exists>y.((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         y \<in> element_set x (?Q))"
                            by auto
             then obtain z where "((found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow> 
                         z \<in> element_set x (?Q))"
                             by auto
             then have 1:"(found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((fst z = x)\<or>(snd z = x))"
                              using element_set_def by auto
             then have "(found_in x (block_act ys)) \<and>(type x = codomain) \<and> (fst z = x) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((str_number x < max_codom (block_act ys)+1))"
                              using under_21 by auto
             moreover have "(z \<in> ?Q) \<and>(fst z = x)\<and>(type x = codomain) 
                              \<longrightarrow> x = ?x1 \<or> x = ?x2"
                        by (metis "0" under_18 under_10 found_in_element_set zero_neq_numeral)
              moreover have "(z \<in> ?Q) \<and>(fst z = x)\<and>(type x = codomain) 
                                 \<longrightarrow> (str_number x = max_codom (block_act ys) + 2)
                                     \<or>(str_number x = max_codom (block_act ys) + 1)"
                                  using str_number_def type_def by auto
              ultimately have 2:"(found_in x (block_act ys)) \<and>(type x = codomain) \<and> (fst z = x) \<longrightarrow>
                                    False"
                                  by auto 
              then have "(found_in x (block_act ys)) \<and>(type x = codomain) \<and> (snd z = x) \<longrightarrow>
                                    (z \<in> ?Q) \<and> ((str_number x < max_codom (block_act ys)+1))"
                              using 1 under_21 by auto
              moreover have "(z \<in> ?Q) \<and>(snd z = x)\<and>(type x = codomain) 
                              \<longrightarrow> x = ?x1 \<or> x = ?x2"
                           using type_def endpt_reconstruction  
                                    by (metis "0" `element_set (codom (max_codom (block_act ys) + 1)) (block_act ys) = {}` `element_set (codom (max_codom (block_act ys) + 2)) (block_act ys) = {}` endpt.distinct(1) endtype.distinct(1) found_in_element_set under_5)
            moreover have "(z \<in> ?Q) \<and>(snd z = x)\<and>(type x = codomain) 
                                 \<longrightarrow> str_number x = max_codom (block_act ys) + 1
                                     \<or> str_number x = max_codom (block_act ys) + 2"
                                  using str_number_def type_def by auto
              ultimately have 3:"(found_in x (block_act ys)) \<and>(type x = codomain) \<and> (snd z = x) \<longrightarrow>
                                    False"
                                  by auto
             then have "(found_in x (block_act ys)) \<and>(type x = codomain) \<longrightarrow>
                                   False"
                                       using 1 2 
                          by metis
            then show False using 0 by (metis `element_set (codom (max_codom (block_act ys) + 1)) (block_act ys) = {}` `element_set (codom (max_codom (block_act ys) + 2)) (block_act ys) = {}` `element_set (endpt.dom (max_dom (block_act ys) + 1)) (block_act ys) = {}` `element_set (endpt.dom (max_dom (block_act ys) + 2)) (block_act ys) = {}` found_in_element_set under_5)
       qed
      then have "\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (element_set x ?Q = {}))"
                    using under_20 endpt.exhaust  by (metis (full_types) endtype.exhaust)
      then have "\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (count_element x ?Q = 0))"
                                     using count_element_def by auto
      then have "\<forall>x.((found_in x (block_act ys)) \<longrightarrow> (count_element x (block_act (y#ys)) = 2))"
                                      using under_18 under_3 by auto
      then have "\<forall>x.((found_in x (block_act (y#ys)) \<longrightarrow> (count_element x (block_act (y#ys)) = 2)))"
                      using under_4 under_17 by auto
      then show ?thesis  using injective_def by auto
 qed
qed

definition antireflexive ::"('a \<times> 'a) set \<Rightarrow> bool"
where
"antireflexive S \<equiv> \<forall>x.((x \<in> S) \<longrightarrow> (fst x \<noteq> snd x))"
 
lemma antireflexive_union:assumes "antireflexive S1" and "antireflexive S2"
         shows "antireflexive (S1 \<union> S2)"
         using assms antireflexive_def by auto

theorem antireflexive_block_act:"antireflexive (block_act xs)"
 proof(induction xs)
 case Nil
    show ?case using Nil antireflexive_def by auto
 next
 case (Cons y ys)
    show ?case
      proof(cases y)
        case vert
           let ?Q = "{(codom ((max_codom (block_act ys))+1), dom ((max_dom (block_act ys))+1)),
              (dom ((max_dom (block_act ys))+1), codom ((max_codom (block_act ys))+1))}"
           have "block_act (y#ys) = ?Q \<union> (block_act ys)"
                     using block_act.simps vert by auto
           moreover have "antireflexive ?Q"
                        unfolding antireflexive_def by auto
           moreover have "antireflexive (block_act ys)"
                     using Cons by auto
           ultimately show ?thesis using antireflexive_union by metis
       next
       case cup
            let ?Q = "{(codom ((max_codom (block_act ys))+1), codom ((max_codom (block_act ys))+2)),
              (codom ((max_codom (block_act ys))+2), codom ((max_codom (block_act ys))+1))}"
           have "block_act (y#ys) = ?Q \<union> (block_act ys)"
                     using block_act.simps cup  by auto
           moreover have "antireflexive ?Q"
                        unfolding antireflexive_def by auto
           moreover have "antireflexive (block_act ys)"
                     using Cons by auto
           ultimately show ?thesis using antireflexive_union by metis
       next
       case cap
           let ?Q = "{(dom ((max_dom (block_act ys))+1), dom ((max_dom (block_act ys))+2)),
              (dom ((max_dom (block_act ys))+2), dom ((max_dom (block_act ys))+1))}"
           have "block_act (y#ys) = ?Q \<union> (block_act ys)"
                     using block_act.simps cap  by auto
           moreover have "antireflexive ?Q"
                        unfolding antireflexive_def by auto
           moreover have "antireflexive (block_act ys)"
                     using Cons by auto
           ultimately show ?thesis using antireflexive_union by metis
       next
       case over
          let ?Q = "{(dom ((max_dom (block_act ys))+1), codom ((max_codom (block_act ys))+2)),
              (codom ((max_codom (block_act ys))+2), dom ((max_dom (block_act ys))+1)),
              (dom ((max_dom (block_act ys))+2), codom ((max_codom (block_act ys))+1)),
              (codom ((max_codom (block_act ys))+1), dom ((max_dom (block_act ys))+2)) }"
           have "block_act (y#ys) = ?Q \<union> (block_act ys)"
                     using block_act.simps over swap_act_def  by auto
           moreover have "antireflexive ?Q"
                        unfolding antireflexive_def by auto
           moreover have "antireflexive (block_act ys)"
                     using Cons by auto
           ultimately show ?thesis using antireflexive_union by metis
      next
      case under  
           let ?Q = "{(dom ((max_dom (block_act ys))+1), codom ((max_codom (block_act ys))+2)),
              (codom ((max_codom (block_act ys))+2), dom ((max_dom (block_act ys))+1)),
              (dom ((max_dom (block_act ys))+2), codom ((max_codom (block_act ys))+1)),
              (codom ((max_codom (block_act ys))+1), dom ((max_dom (block_act ys))+2)) }"
           have "block_act (y#ys) = ?Q \<union> (block_act ys)"
                     using block_act.simps under swap_act_def  by auto
           moreover have "antireflexive ?Q"
                        unfolding antireflexive_def by auto
           moreover have "antireflexive (block_act ys)"
                     using Cons by auto
           ultimately show ?thesis using antireflexive_union by metis
         qed
 qed

lemma Max_belongs_to_set: "(finite S)\<and>(S \<noteq> {}) \<Longrightarrow> Max S \<in> S"
             using Max_def by auto

lemma find_codom_max:
 "(S \<noteq> {} \<and> (finite S)) \<Longrightarrow> (found_in (codom (max_codom S)) S) \<or> (max_codom S = 0)"
 proof-
 assume 0:"(S \<noteq> {} \<and> (finite S))"
 let ?x = "max_codom S"
 have "codom_set_filter S \<noteq> {} \<Longrightarrow> ?x = Max (codom_set_filter S)"
           using 0  by (metis max_codom_def)
 then have "codom_set_filter S \<noteq> {} \<Longrightarrow> ?x \<in> (codom_set_filter S)"
           using Max_belongs_to_set 0 finite_codom_set_filter by auto
 then have "codom_set_filter S \<noteq> {} \<Longrightarrow> (\<exists>y. ((codom ?x,y) \<in> S \<or> (y, codom ?x) \<in> S))"
                            using codom_set_filter_def by auto
 then have "codom_set_filter S \<noteq> {} \<Longrightarrow> found_in (codom ?x) S"
                  using found_in_def by auto
 then show ?thesis using max_codom_def by auto
qed


lemma find_dom_max:
 "(S \<noteq> {} \<and> (finite S)) \<Longrightarrow> (found_in (dom (max_dom S)) S) \<or> (max_dom S = 0)"
 proof-
 assume 0:"(S \<noteq> {} \<and> (finite S))"
 let ?x = "max_dom S"
 have "dom_set_filter S \<noteq> {} \<Longrightarrow> ?x = Max (dom_set_filter S)"
           using 0  by (metis max_dom_def)
 then have "dom_set_filter S \<noteq> {} \<Longrightarrow> ?x \<in> (dom_set_filter S)"
           using Max_belongs_to_set 0 finite_dom_set_filter by auto
 then have "dom_set_filter S \<noteq> {} \<Longrightarrow> (\<exists>y. ((dom ?x,y) \<in> S \<or> (y, dom ?x) \<in> S))"
                            using dom_set_filter_def by auto
 then have "dom_set_filter S \<noteq> {} \<Longrightarrow> found_in (dom ?x) S"
                  using found_in_def by auto
 then show ?thesis using max_dom_def by auto
qed

definition one_less::"endpt \<Rightarrow> endpt"
where
"one_less x \<equiv> (case (type x) of domain \<Rightarrow> if (str_number x > 1) 
                                           then (dom (str_number x - 1))
                                            else x 
                        |codomain \<Rightarrow> 
                                       if (str_number x > 1) 
                                           then (codom (str_number x - 1))
                                            else x )"
   
definition linear::"(endpt \<times> endpt) set \<Rightarrow> bool"
where
"linear S \<equiv> (\<forall>x.(found_in x S) \<longrightarrow> (found_in (one_less x) S))"

theorem linear_block_act:"linear (block_act xs)"
 proof(induction xs)
 case Nil
     show ?case using Nil linear_def block_act.simps(1) empty_iff found_in_def by auto 
 next
 case (Cons y ys)
    show ?case
      proof(cases "y")
      case vert
          let ?Q = "{(codom ((max_codom (block_act ys))+1), dom ((max_dom (block_act ys))+1)),
              (dom ((max_dom (block_act ys))+1), codom ((max_codom (block_act ys))+1))}"
          have vert_1:"block_act (y#ys) = ?Q \<union> (block_act ys)"
                     using block_act.simps vert by auto
          then have vert_2:"\<forall>x.(found_in x (block_act (y#ys)) \<longrightarrow> (found_in x (block_act ys))
                                                                  \<or>(found_in x ?Q))"
                               using found_in_def by auto
          then have vert_3:"\<forall>x.(found_in x (block_act ys) 
                                 \<longrightarrow> (found_in (one_less x) (block_act ys)))"
                              using Cons linear_def by auto
          have vert_4: "\<forall>x.(found_in x ?Q) 
                                 \<longrightarrow> x \<in> {codom ((max_codom (block_act ys))+1)
                                          , dom ((max_dom (block_act ys))+1)
                                           } "
                                using found_in_def by auto
           
          have "\<forall>x.(found_in x ?Q) 
                                 \<longrightarrow>  (found_in (one_less x) (block_act (y#ys)))"
               proof-
               have 0:"max_codom (block_act ys) \<ge> 0"
                            by auto
               have "one_less (codom 1) = codom 1"
                                    unfolding one_less_def type_def endpt.exhaust str_number_def
                                        by auto         
               then have 
                  " max_codom (block_act ys) = 0 \<Longrightarrow> 
                          one_less (codom ((max_codom (block_act ys))+1)) 
                                        = (codom ((max_codom (block_act ys))+1))"
                                       by auto
                then have a:"max_codom (block_act ys) = 0
                                  \<Longrightarrow> found_in (one_less (codom ((max_codom (block_act ys))+1))) 
                                                 (block_act (y#ys))"
                                       using found_in_def vert_1 by auto 
                have b:"max_codom (block_act ys) > 0 
                            \<Longrightarrow> (found_in (codom (max_codom (block_act ys)))(block_act ys))"
                                using find_codom_max by (metis empty_set_codom_set_filter finite_block_act gr_implies_not0 max_codom_def)
                then have "max_codom (block_act ys) > 0 
                            \<Longrightarrow> one_less (codom (max_codom (block_act ys)+1) ) 
                                              = codom (max_codom (block_act ys))"
                                    unfolding one_less_def type_def endpt.exhaust str_number_def
                                        by auto
                 with b have 
                  "max_codom (block_act ys) > 0 
                      \<Longrightarrow> (found_in (one_less (codom (max_codom (block_act ys)+1))) (block_act ys))"
                          by auto
                  then have
                  "max_codom (block_act ys) > 0 
                    \<Longrightarrow> 
                     (found_in (one_less (codom (max_codom (block_act ys)+1))) (block_act (y#ys)))"
                            using vert_1  found_in_def by auto 
                    with 0 a have c:
                    "(found_in (one_less (codom (max_codom (block_act ys)+1))) (block_act (y#ys)))"
                              using neq0_conv by (metis)
                     have 1:"max_dom (block_act ys) \<ge> 0"
                            by auto
                     have "one_less (dom 1) = dom 1"
                                    unfolding one_less_def type_def endpt.exhaust str_number_def
                                        by auto         
                      then have 
                       "max_dom (block_act ys) = 0 \<Longrightarrow> 
                           one_less (dom ((max_dom (block_act ys))+1)) 
                                        = (dom ((max_dom (block_act ys))+1))"
                                       by auto
                      then have d:"max_dom (block_act ys) = 0
                                  \<Longrightarrow> found_in (one_less (dom ((max_dom (block_act ys))+1))) 
                                                 (block_act (y#ys))"
                                       using found_in_def vert_1 by auto 
                       have e:"max_dom (block_act ys) > 0 
                            \<Longrightarrow> (found_in (dom (max_dom (block_act ys)))(block_act ys))"
                                using find_dom_max by (metis empty_set_dom_set_filter finite_block_act gr_implies_not0 max_dom_def)
                       then have "max_dom (block_act ys) > 0 
                            \<Longrightarrow> one_less (dom (max_dom (block_act ys)+1) ) 
                                              = dom (max_dom (block_act ys))"
                                    unfolding one_less_def type_def endpt.exhaust str_number_def
                                        by auto
                        with e have 
                         "max_dom (block_act ys) > 0 
                              \<Longrightarrow> 
                              (found_in (one_less (dom (max_dom (block_act ys)+1))) (block_act ys))"
                                   by auto
                         then have
                          "max_dom (block_act ys) > 0 
                             \<Longrightarrow> 
                          (found_in (one_less (dom (max_dom (block_act ys)+1))) (block_act (y#ys)))"
                            using vert_1  found_in_def by auto 
                          with 0 d have f:
                          "(found_in (one_less (dom (max_dom (block_act ys)+1))) (block_act (y#ys)))"
                              using neq0_conv by (metis)
                           then show ?thesis using c f vert_4 by auto
                         qed
               then show ?thesis using vert_2 vert_3 unfolding linear_def 
                  by (metis Un_insert_left found_in_def insertCI insert_is_Un vert_1)
              next
              case cup
              let ?Q = "{(codom ((max_codom (block_act ys))+1), codom ((max_codom (block_act ys))+2)),
              (codom ((max_codom (block_act ys))+2), codom ((max_codom (block_act ys))+1))}"
              have cup_1:"block_act (y#ys) = ?Q \<union> (block_act ys)"
                     using block_act.simps cup by auto
               then have cup_2:"\<forall>x.(found_in x (block_act (y#ys)) \<longrightarrow> (found_in x (block_act ys))
                                                                  \<or>(found_in x ?Q))"
                               using found_in_def by auto
               then have cup_3:"\<forall>x.(found_in x (block_act ys) 
                                 \<longrightarrow> (found_in (one_less x) (block_act ys)))"
                              using Cons linear_def by auto
               have cup_4: "\<forall>x.(found_in x ?Q) 
                                 \<longrightarrow> x \<in> {codom ((max_codom (block_act ys))+1)
                                          , codom ((max_codom (block_act ys))+2)} "
                                using found_in_def by auto           
               have "\<forall>x.(found_in x ?Q) 
                                 \<longrightarrow>  (found_in (one_less x) (block_act (y#ys)))"
                proof-
                have 0:"max_codom (block_act ys) \<ge> 0"
                            by auto
                have "one_less (codom 1) = codom 1"
                                    unfolding one_less_def type_def endpt.exhaust str_number_def
                                        by auto         
                then have 
                  " max_codom (block_act ys) = 0 \<Longrightarrow> 
                          one_less (codom ((max_codom (block_act ys))+1)) 
                                        = (codom ((max_codom (block_act ys))+1))"
                                       by auto
                then have a:"max_codom (block_act ys) = 0
                                  \<Longrightarrow> found_in (one_less (codom ((max_codom (block_act ys))+1))) 
                                                 (block_act (y#ys))"
                                       using found_in_def cup_1 by auto 
                have b:"max_codom (block_act ys) > 0 
                            \<Longrightarrow> (found_in (codom (max_codom (block_act ys)))(block_act ys))"
                                using find_codom_max by (metis empty_set_codom_set_filter finite_block_act gr_implies_not0 max_codom_def)
                then have "max_codom (block_act ys) > 0 
                            \<Longrightarrow> one_less (codom (max_codom (block_act ys)+1) ) 
                                              = codom (max_codom (block_act ys))"
                                    unfolding one_less_def type_def endpt.exhaust str_number_def
                                        by auto
                with b have 
                  "max_codom (block_act ys) > 0 
                      \<Longrightarrow> (found_in (one_less (codom (max_codom (block_act ys)+1))) (block_act ys))"
                          by auto
                then have
                  "max_codom (block_act ys) > 0 
                    \<Longrightarrow> 
                     (found_in (one_less (codom (max_codom (block_act ys)+1))) (block_act (y#ys)))"
                            using cup_1  found_in_def by auto 
                with 0 a have c:
                    "(found_in (one_less (codom (max_codom (block_act ys)+1))) (block_act (y#ys)))"
                              using neq0_conv by (metis)
                have "one_less (codom (max_codom (block_act ys)+2)) 
                                = (codom (max_codom (block_act ys)+1))"
                                  using one_less_def type_def str_number_def by auto
                then have 
                  "(found_in (one_less (codom (max_codom (block_act ys)+2))) (block_act (y#ys)))"
                                   using cup_1 found_in_def by auto
                with c show ?thesis using cup_4 by auto
                qed
               then show ?thesis using cup_2 cup_1 cup_3 unfolding linear_def 
                 by (metis UnCI found_in_def)
             next
                      case cap
              let ?Q = "{(dom ((max_dom (block_act ys))+1), dom ((max_dom (block_act ys))+2)),
              (dom ((max_dom (block_act ys))+2), dom ((max_dom (block_act ys))+1))}"
              have cap_1:"block_act (y#ys) = ?Q \<union> (block_act ys)"
                     using block_act.simps cap by auto
               then have cap_2:"\<forall>x.(found_in x (block_act (y#ys)) \<longrightarrow> (found_in x (block_act ys))
                                                                  \<or>(found_in x ?Q))"
                               using found_in_def by auto
               then have cap_3:"\<forall>x.(found_in x (block_act ys) 
                                 \<longrightarrow> (found_in (one_less x) (block_act ys)))"
                              using Cons linear_def by auto
               have cap_4: "\<forall>x.(found_in x ?Q) 
                                 \<longrightarrow> x \<in> {dom ((max_dom (block_act ys))+1)
                                          , dom ((max_dom (block_act ys))+2)} "
                                using found_in_def by auto           
               have "\<forall>x.(found_in x ?Q) 
                                 \<longrightarrow>  (found_in (one_less x) (block_act (y#ys)))"
                proof-
                have 0:"max_dom (block_act ys) \<ge> 0"
                            by auto
                have "one_less (dom 1) = dom 1"
                                    unfolding one_less_def type_def endpt.exhaust str_number_def
                                        by auto         
                then have 
                  " max_dom (block_act ys) = 0 \<Longrightarrow> 
                          one_less (dom ((max_dom (block_act ys))+1)) 
                                        = (dom ((max_dom (block_act ys))+1))"
                                       by auto
                then have a:"max_dom (block_act ys) = 0
                                  \<Longrightarrow> found_in (one_less (dom ((max_dom (block_act ys))+1))) 
                                                 (block_act (y#ys))"
                                       using found_in_def cap_1 by auto 
                have b:"max_dom (block_act ys) > 0 
                            \<Longrightarrow> (found_in (dom (max_dom (block_act ys)))(block_act ys))"
                                using find_dom_max by (metis empty_set_dom_set_filter finite_block_act gr_implies_not0 max_dom_def)
                then have "max_dom (block_act ys) > 0 
                            \<Longrightarrow> one_less (dom (max_dom (block_act ys)+1) ) 
                                              = dom (max_dom (block_act ys))"
                                    unfolding one_less_def type_def endpt.exhaust str_number_def
                                        by auto
                with b have 
                  "max_dom (block_act ys) > 0 
                      \<Longrightarrow> (found_in (one_less (dom (max_dom (block_act ys)+1))) (block_act ys))"
                          by auto
                then have
                  "max_dom (block_act ys) > 0 
                    \<Longrightarrow> 
                     (found_in (one_less (dom (max_dom (block_act ys)+1))) (block_act (y#ys)))"
                            using cap_1  found_in_def by auto 
                with 0 a have c:
                    "(found_in (one_less (dom (max_dom (block_act ys)+1))) (block_act (y#ys)))"
                              using neq0_conv by (metis)
                have "one_less (dom (max_dom (block_act ys)+2)) 
                                = (dom (max_dom (block_act ys)+1))"
                                  using one_less_def type_def str_number_def by auto
                then have 
                  "(found_in (one_less (dom (max_dom (block_act ys)+2))) (block_act (y#ys)))"
                                   using cap_1 found_in_def by auto
                with c show ?thesis using cap_4 by auto
                qed
               then show ?thesis using cap_2 cap_1 cap_3 unfolding linear_def 
                 by (metis UnCI found_in_def)
              next
              case over
              let ?Q = "{(dom ((max_dom (block_act ys))+1), codom ((max_codom (block_act ys))+2)),
              (codom ((max_codom (block_act ys))+2), dom ((max_dom (block_act ys))+1)),
              (dom ((max_dom (block_act ys))+2), codom ((max_codom (block_act ys))+1)),
              (codom ((max_codom (block_act ys))+1), dom ((max_dom (block_act ys))+2)) }"
              have over_1:"block_act (y#ys) = ?Q \<union> (block_act ys)"
                     using block_act.simps over swap_act_def by auto 
               then have over_2:"\<forall>x.(found_in x (block_act (y#ys)) \<longrightarrow> (found_in x (block_act ys))
                                                                  \<or>(found_in x ?Q))"
                               using found_in_def by auto
               then have over_3:"\<forall>x.(found_in x (block_act ys) 
                                 \<longrightarrow> (found_in (one_less x) (block_act ys)))"
                              using Cons linear_def by auto
               have over_4: "\<forall>x.(found_in x ?Q) 
                                 \<longrightarrow> x \<in> {dom ((max_dom (block_act ys))+1)
                                          , dom ((max_dom (block_act ys))+2)
                                          , codom ((max_codom (block_act ys))+1)
                                          , codom ((max_codom (block_act ys))+2)  } "
                                using found_in_def by auto           
               have "\<forall>x.(found_in x ?Q) 
                                 \<longrightarrow>  (found_in (one_less x) (block_act (y#ys)))"
                proof-
                have 0:"max_dom (block_act ys) \<ge> 0"
                            by auto
                have "one_less (dom 1) = dom 1"
                                    unfolding one_less_def type_def endpt.exhaust str_number_def
                                        by auto         
                then have 
                  " max_dom (block_act ys) = 0 \<Longrightarrow> 
                          one_less (dom ((max_dom (block_act ys))+1)) 
                                        = (dom ((max_dom (block_act ys))+1))"
                                       by auto
                then have a:"max_dom (block_act ys) = 0
                                  \<Longrightarrow> found_in (one_less (dom ((max_dom (block_act ys))+1))) 
                                                 (block_act (y#ys))"
                                       using found_in_def over_1 by auto 
                have b:"max_dom (block_act ys) > 0 
                            \<Longrightarrow> (found_in (dom (max_dom (block_act ys)))(block_act ys))"
                                using find_dom_max by (metis empty_set_dom_set_filter finite_block_act gr_implies_not0 max_dom_def)
                then have "max_dom (block_act ys) > 0 
                            \<Longrightarrow> one_less (dom (max_dom (block_act ys)+1) ) 
                                              = dom (max_dom (block_act ys))"
                                    unfolding one_less_def type_def endpt.exhaust str_number_def
                                        by auto
                with b have 
                  "max_dom (block_act ys) > 0 
                      \<Longrightarrow> (found_in (one_less (dom (max_dom (block_act ys)+1))) (block_act ys))"
                          by auto
                then have
                  "max_dom (block_act ys) > 0 
                    \<Longrightarrow> 
                     (found_in (one_less (dom (max_dom (block_act ys)+1))) (block_act (y#ys)))"
                            using over_1  found_in_def by auto 
                with 0 a have c:
                    "(found_in (one_less (dom (max_dom (block_act ys)+1))) (block_act (y#ys)))"
                              using neq0_conv by (metis)

               have 1:"max_codom (block_act ys) \<ge> 0"
                            by auto
                have "one_less (codom 1) = codom 1"
                                    unfolding one_less_def type_def endpt.exhaust str_number_def
                                        by auto         
                then have 
                  " max_codom (block_act ys) = 0 \<Longrightarrow> 
                          one_less (codom ((max_codom (block_act ys))+1)) 
                                        = (codom ((max_codom (block_act ys))+1))"
                                       by auto
                then have d:"max_codom (block_act ys) = 0
                                  \<Longrightarrow> found_in (one_less (codom ((max_codom (block_act ys))+1))) 
                                                 (block_act (y#ys))"
                                       using found_in_def over_1 by auto 
                have e:"max_codom (block_act ys) > 0 
                            \<Longrightarrow> (found_in (codom (max_codom (block_act ys)))(block_act ys))"
                                using find_codom_max by (metis empty_set_codom_set_filter finite_block_act gr_implies_not0 max_codom_def)
                then have "max_codom (block_act ys) > 0 
                            \<Longrightarrow> one_less (codom (max_codom (block_act ys)+1) ) 
                                              = codom (max_codom (block_act ys))"
                                    unfolding one_less_def type_def endpt.exhaust str_number_def
                                        by auto
                with e have 
                  "max_codom (block_act ys) > 0 
                      \<Longrightarrow> (found_in (one_less (codom (max_codom (block_act ys)+1))) (block_act ys))"
                          by auto
                 then have
                  "max_codom (block_act ys) > 0 
                    \<Longrightarrow> 
                     (found_in (one_less (codom (max_codom (block_act ys)+1))) (block_act (y#ys)))"
                            using over_1  found_in_def by auto 
                with 0 d have f:
                    "(found_in (one_less (codom (max_codom (block_act ys)+1))) (block_act (y#ys)))"
                              using neq0_conv by (metis)
                have "one_less (dom (max_dom (block_act ys)+2)) 
                                = (dom (max_dom (block_act ys)+1))"
                                  using one_less_def type_def str_number_def by auto
                then have g:
                  "(found_in (one_less (dom (max_dom (block_act ys)+2))) (block_act (y#ys)))"
                                   using over_1 found_in_def by auto
                have "one_less (codom (max_codom (block_act ys)+2)) 
                                = (codom (max_codom (block_act ys)+1))"
                                  using one_less_def type_def str_number_def by auto
                then have 
                  "(found_in (one_less (codom (max_codom (block_act ys)+2))) (block_act (y#ys)))"
                                   using over_1 found_in_def by auto
                with c f g show ?thesis using over_4 by auto
                qed
                 then show ?thesis using over_2 over_1 over_3 unfolding linear_def 
                 by (metis UnCI found_in_def)
               next
               case under
                      let ?Q = "{(dom ((max_dom (block_act ys))+1), codom ((max_codom (block_act ys))+2)),
              (codom ((max_codom (block_act ys))+2), dom ((max_dom (block_act ys))+1)),
              (dom ((max_dom (block_act ys))+2), codom ((max_codom (block_act ys))+1)),
              (codom ((max_codom (block_act ys))+1), dom ((max_dom (block_act ys))+2)) }"
              have under_1:"block_act (y#ys) = ?Q \<union> (block_act ys)"
                     using block_act.simps under swap_act_def by auto 
               then have under_2:"\<forall>x.(found_in x (block_act (y#ys)) \<longrightarrow> (found_in x (block_act ys))
                                                                  \<or>(found_in x ?Q))"
                               using found_in_def by auto
               then have under_3:"\<forall>x.(found_in x (block_act ys) 
                                 \<longrightarrow> (found_in (one_less x) (block_act ys)))"
                              using Cons linear_def by auto
               have under_4: "\<forall>x.(found_in x ?Q) 
                                 \<longrightarrow> x \<in> {dom ((max_dom (block_act ys))+1)
                                          , dom ((max_dom (block_act ys))+2)
                                          , codom ((max_codom (block_act ys))+1)
                                          , codom ((max_codom (block_act ys))+2)  } "
                                using found_in_def by auto           
               have "\<forall>x.(found_in x ?Q) 
                                 \<longrightarrow>  (found_in (one_less x) (block_act (y#ys)))"
                proof-
                have 0:"max_dom (block_act ys) \<ge> 0"
                            by auto
                have "one_less (dom 1) = dom 1"
                                    unfolding one_less_def type_def endpt.exhaust str_number_def
                                        by auto         
                then have 
                  " max_dom (block_act ys) = 0 \<Longrightarrow> 
                          one_less (dom ((max_dom (block_act ys))+1)) 
                                        = (dom ((max_dom (block_act ys))+1))"
                                       by auto
                then have a:"max_dom (block_act ys) = 0
                                  \<Longrightarrow> found_in (one_less (dom ((max_dom (block_act ys))+1))) 
                                                 (block_act (y#ys))"
                                       using found_in_def under_1 by auto 
                have b:"max_dom (block_act ys) > 0 
                            \<Longrightarrow> (found_in (dom (max_dom (block_act ys)))(block_act ys))"
                                using find_dom_max by (metis empty_set_dom_set_filter 
                                 finite_block_act gr_implies_not0 max_dom_def)
                then have "max_dom (block_act ys) > 0 
                            \<Longrightarrow> one_less (dom (max_dom (block_act ys)+1) ) 
                                              = dom (max_dom (block_act ys))"
                                    unfolding one_less_def type_def endpt.exhaust str_number_def
                                        by auto
                with b have 
                  "max_dom (block_act ys) > 0 
                      \<Longrightarrow> (found_in (one_less (dom (max_dom (block_act ys)+1))) (block_act ys))"
                          by auto
                then have
                  "max_dom (block_act ys) > 0 
                    \<Longrightarrow> 
                     (found_in (one_less (dom (max_dom (block_act ys)+1))) (block_act (y#ys)))"
                            using under_1  found_in_def by auto 
                with 0 a have c:
                    "(found_in (one_less (dom (max_dom (block_act ys)+1))) (block_act (y#ys)))"
                              using neq0_conv by (metis)

               have 1:"max_codom (block_act ys) \<ge> 0"
                            by auto
                have "one_less (codom 1) = codom 1"
                                    unfolding one_less_def type_def endpt.exhaust str_number_def
                                        by auto         
                then have 
                  " max_codom (block_act ys) = 0 \<Longrightarrow> 
                          one_less (codom ((max_codom (block_act ys))+1)) 
                                        = (codom ((max_codom (block_act ys))+1))"
                                       by auto
                then have d:"max_codom (block_act ys) = 0
                                  \<Longrightarrow> found_in (one_less (codom ((max_codom (block_act ys))+1))) 
                                                 (block_act (y#ys))"
                                       using found_in_def under_1 by auto 
                have e:"max_codom (block_act ys) > 0 
                            \<Longrightarrow> (found_in (codom (max_codom (block_act ys)))(block_act ys))"
                                using find_codom_max by (metis empty_set_codom_set_filter finite_block_act gr_implies_not0 max_codom_def)
                then have "max_codom (block_act ys) > 0 
                            \<Longrightarrow> one_less (codom (max_codom (block_act ys)+1) ) 
                                              = codom (max_codom (block_act ys))"
                                    unfolding one_less_def type_def endpt.exhaust str_number_def
                                        by auto
                with e have 
                  "max_codom (block_act ys) > 0 
                      \<Longrightarrow> (found_in (one_less (codom (max_codom (block_act ys)+1))) (block_act ys))"
                          by auto
                 then have
                  "max_codom (block_act ys) > 0 
                    \<Longrightarrow> 
                     (found_in (one_less (codom (max_codom (block_act ys)+1))) (block_act (y#ys)))"
                            using under_1  found_in_def by auto 
                with 0 d have f:
                    "(found_in (one_less (codom (max_codom (block_act ys)+1))) (block_act (y#ys)))"
                              using neq0_conv by (metis)
                have "one_less (dom (max_dom (block_act ys)+2)) 
                                = (dom (max_dom (block_act ys)+1))"
                                  using one_less_def type_def str_number_def by auto
                then have g:
                  "(found_in (one_less (dom (max_dom (block_act ys)+2))) (block_act (y#ys)))"
                                   using under_1 found_in_def by auto
                have "one_less (codom (max_codom (block_act ys)+2)) 
                                = (codom (max_codom (block_act ys)+1))"
                                  using one_less_def type_def str_number_def by auto
                then have 
                  "(found_in (one_less (codom (max_codom (block_act ys)+2))) (block_act (y#ys)))"
                                   using under_1 found_in_def by auto
                with c f g show ?thesis using under_4 by auto
                qed
                 then show ?thesis using under_2 under_1 under_3 unfolding linear_def 
                 by (metis UnCI found_in_def)
               qed
qed

definition nice_set::"(endpt \<times> endpt) set \<Rightarrow> bool"
 where
 "nice_set S \<equiv> (symmetric S)\<and> (antireflexive S)\<and>(linear S)\<and>(injective S)"
 
theorem nice_set_block_act:"nice_set (block_act xs)"
   unfolding nice_set_def using antireflexive_block_act linear_block_act symmetric_block_act
     injective_block_act by auto 
 

(*theorem to prove - str_number is greater than or equal to 1 in block_act 
.ie. found_in (codom n) (block_act ys) \<equiv> n \<ge> 1*)
(*
lemma assumes "A \<subseteq> B"  and "finite A" and "finite B" shows "Max A \<le> Max B"
      proof-
      have "\<forall>x.(x \<in> A \<longrightarrow> x \<in> B)"
          using assms by auto
      moreover have "\<forall>x.(x \<in> B \<longrightarrow> x \<le> Max B)"
         using Max_def assms by auto  
      ultimately have "\<forall>x.(x \<in> A \<longrightarrow>  x \<le> Max B)"
               by auto
      then have "Max A \<le> Max B"
               using Max_def assms sledgehammer
*)

lemma max_union:assumes "finite S1" and "finite S2" and "S2 \<noteq> {}" and "S1 \<noteq> {}" and "S1 \<union> S2 \<noteq> {}"
    shows "Max (S1 \<union> S2) = Max {Max S1, Max S2}"
    proof-
    have "Max (S1 \<union> S2) \<in> S1 \<union> S2"
          using assms by (metis Max_belongs_to_set finite_Un)
   then have 1:"Max (S1 \<union> S2) \<in> S1 \<or> Max (S1 \<union> S2) \<in> S2"
                   by auto
   show ?thesis
         proof(cases "Max (S1 \<union> S2) \<in> S1")
         case True
          have "Max (S1 \<union> S2) \<ge> Max S1"
                 using assms unfolding Max_def by (metis Max_def Max_mono True Un_upper1 equals0D finite_Un)
          moreover have "Max (S1 \<union> S2) \<le> Max S1"
                     using True Max_def assms by auto
          ultimately have "Max (S1 \<union> S2) = Max S1"
                      by auto
          moreover have "Max (S1 \<union> S2) \<ge> Max S2"
                      using assms Max_def  by (metis Collect_mem_eq Diff_empty Max.union_idem True 
                                             Un_empty_left `Max (S1 \<union> S2) = Max S1` equals0D max_def 
                                              min_max.sup.commute min_max.sup.idem order_refl) 
          ultimately have "Max (S1 \<union> S2) = Max {Max S1, Max S2}"
                          using assms by (metis Max.insert_idem Max.union_idem Max_singleton True equals0D finite.emptyI finite_insert) 
          then show ?thesis  by auto
         next
         case False
           have F_1:"Max (S1 \<union> S2) \<in> S2"
                 using False 1 by auto
           have "Max (S1 \<union> S2) \<ge> Max S2"
                 using assms unfolding Max_def by (metis Max_def Max_mono Un_upper2 finite_Un)
           moreover have "Max (S1 \<union> S2) \<le> Max S2"
                     using F_1 Max_def assms by auto 
          ultimately have "Max (S1 \<union> S2) = Max S2"
                      by auto
          moreover have "Max (S1 \<union> S2) \<ge> Max S1"
                      using assms Max_def by (metis Max.union_idem calculation max_def order_refl) 
          ultimately have "Max (S1 \<union> S2) = Max {Max S1, Max S2}"
                          using assms by (metis Collect_mem_eq Max.insert_idem Max.union_idem Max_singleton Min_singleton finite.emptyI finite_insert insert_commute insert_compr insert_not_empty sup_commute the_elem_eq) 
           then show ?thesis  by auto     
        qed
qed

lemma codom_set_filter_union:  "codom_set_filter (S1 \<union> S2) = (codom_set_filter S1) \<union> (codom_set_filter S2)"
      unfolding codom_set_filter_def by auto
 
lemma "max_codom S \<ge> 0"
           using max_codom_def by auto

lemma Max_two_elements:"(a \<ge> b) \<Longrightarrow> Max {a, b} = a"
   unfolding Max_def by (metis (hide_lams, no_types) finite.emptyI finite_insert
                         min_max.Sup_fin.insert_idem min_max.Sup_fin.singleton min_max.Sup_fin_def 
                         min_max.sup_absorb2 min_max.sup_commute)

               (*codom_set_filter and then max_codom*)
lemma assumes "finite S1" and "finite S2" 
    shows"max_codom (S1 \<union> S2) = Max {max_codom S1, max_codom S2}"
      using codom_set_filter_union max_union max_codom_def 
proof-
 have 1:"codom_set_filter (S1 \<union> S2) = {} \<Longrightarrow> (codom_set_filter (S1) = {} )
                                          \<and> (codom_set_filter (S2) = {} )"
        using codom_set_filter_union by auto             
 moreover have "codom_set_filter (S1 \<union> S2) = {} \<Longrightarrow> max_codom (S1 \<union> S2) = 0"
            using max_codom_def by auto
 moreover have "codom_set_filter (S1 \<union> S2) = {} \<Longrightarrow> (max_codom S1 = 0)\<and>(max_codom S2 = 0)"
                  using 1 max_codom_def by auto
 ultimately have 2:"codom_set_filter (S1 \<union> S2) = {} \<Longrightarrow> 
                            max_codom (S1 \<union> S2) = Max {max_codom S1, max_codom S2}"
                     by auto
 have 3:"codom_set_filter (S1 \<union> S2) \<noteq> {} \<Longrightarrow> (codom_set_filter (S1) \<noteq> {} )
                                          \<or> (codom_set_filter (S2) \<noteq> {} )"
              using codom_set_filter_union by auto
 then have 4:"  (codom_set_filter (S1) \<noteq> {} )
                                          \<or> (codom_set_filter (S2) \<noteq> {} ) \<Longrightarrow>
                      ((codom_set_filter (S1) \<noteq> {} ) \<and> (codom_set_filter (S2) \<noteq> {} ))
                      \<or> ((codom_set_filter (S1) \<noteq> {} ) \<and> (codom_set_filter (S2) = {} ))
                      \<or> ((codom_set_filter (S1) = {} ) \<and> (codom_set_filter (S2) \<noteq> {} )) "
                         by auto
 then have 5:"(codom_set_filter (S1) \<noteq> {} ) \<and> (codom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> max_codom S1 = Max (codom_set_filter S1)
                   \<and> max_codom S2 = Max (codom_set_filter S2)"
    using max_codom_def assms by auto 
 then have "(codom_set_filter (S1) \<noteq> {} ) \<and> (codom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow>(codom_set_filter (S1 \<union> S2) \<noteq> {} )"
                    using codom_set_filter_union by auto
 then have "(codom_set_filter (S1) \<noteq> {} ) \<and> (codom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> max_codom (S1 \<union> S2) = Max (codom_set_filter (S1 \<union> S2))"
                using max_codom_def by auto                                                                             
 then have "(codom_set_filter (S1) \<noteq> {} ) \<and> (codom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> Max (codom_set_filter (S1 \<union> S2)) 
                            = Max {Max (codom_set_filter S1), Max (codom_set_filter S2)}"               
                          using finite_codom_set_filter codom_set_filter_union assms
                                  by (metis Un_empty max_union)
 then have 6:"(codom_set_filter (S1) \<noteq> {} ) \<and> (codom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> max_codom (S1 \<union> S2) = Max {max_codom S1, max_codom S2}"
                 using max_codom_def by (metis `codom_set_filter S1 \<noteq> {} \<and> codom_set_filter S2 \<noteq> {} \<Longrightarrow> max_codom (S1 \<union> S2) = Max (codom_set_filter (S1 \<union> S2))`)      

 have "(codom_set_filter (S1) =  {} ) \<and> (codom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> codom_set_filter (S1 \<union> S2) = codom_set_filter S2"
             using codom_set_filter_union    by auto
 then have "(codom_set_filter (S1) =  {} ) \<and> (codom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> Max (codom_set_filter (S1 \<union> S2)) = Max (codom_set_filter S2)"
               by auto
 moreover have "(codom_set_filter (S1) =  {} ) \<and> (codom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> Max {0, Max (codom_set_filter S2)} 
                            =  Max (codom_set_filter S2)"
                          using Max_two_elements by auto
 moreover have "(codom_set_filter (S1) =  {} ) \<and> (codom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> Max {max_codom S1, max_codom S2} 
                            = max_codom S2"
                              using max_codom_def by auto
 ultimately have "(codom_set_filter (S1) =  {} ) \<and> (codom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> Max (codom_set_filter (S1 \<union> S2)) = Max {max_codom S1, max_codom S2}"
            using max_codom_def   by auto
 then have 7:"(codom_set_filter (S1) =  {} ) \<and> (codom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> max_codom (S1 \<union> S2)= Max {max_codom S1, max_codom S2}"
             using max_codom_def by (metis `codom_set_filter S1 = {} \<and> codom_set_filter S2 \<noteq> {} \<Longrightarrow> codom_set_filter (S1 \<union> S2) = codom_set_filter S2`)
 
  have "(codom_set_filter (S2) =  {} ) \<and> (codom_set_filter (S1) \<noteq> {} )
                \<Longrightarrow> codom_set_filter (S1 \<union> S2) = codom_set_filter S1"
             using codom_set_filter_union    by auto
 then have "(codom_set_filter (S2) =  {} ) \<and> (codom_set_filter (S1) \<noteq> {} )
                \<Longrightarrow> Max (codom_set_filter (S1 \<union> S2)) = Max (codom_set_filter S1)"
               by auto
 moreover have "(codom_set_filter (S2) =  {} ) \<and> (codom_set_filter (S1) \<noteq> {} )
                \<Longrightarrow> Max {0, Max (codom_set_filter S1)} 
                            =  Max (codom_set_filter S1)"
                          using Max_two_elements by auto
 moreover have "(codom_set_filter (S2) =  {} ) \<and> (codom_set_filter (S1) \<noteq> {} )
                \<Longrightarrow> Max {max_codom S1, max_codom S2} 
                            = max_codom S1"
                              using max_codom_def by auto
 ultimately have "(codom_set_filter (S2) =  {} ) \<and> (codom_set_filter (S1) \<noteq> {} )
                \<Longrightarrow> Max (codom_set_filter (S1 \<union> S2)) = Max {max_codom S1, max_codom S2}"
            using max_codom_def   by auto
 then have 8:"(codom_set_filter (S2) =  {} ) \<and> (codom_set_filter (S1) \<noteq> {} )
                \<Longrightarrow> max_codom (S1 \<union> S2)= Max {max_codom S1, max_codom S2}"
             using max_codom_def by (metis `codom_set_filter S2 = {} \<and> codom_set_filter S1 \<noteq> {} \<Longrightarrow> codom_set_filter (S1 \<union> S2) = codom_set_filter S1`)
 from 2 3 6 7 8 show ?thesis by auto
qed


lemma dom_set_filter_union:  "dom_set_filter (S1 \<union> S2) = (dom_set_filter S1) \<union> (dom_set_filter S2)"
      unfolding dom_set_filter_def by auto
 
lemma "max_dom S \<ge> 0"
           using max_dom_def by auto
               (*dom_set_filter and then max_dom*)
lemma assumes "finite S1" and "finite S2" 
    shows"max_dom (S1 \<union> S2) = Max {max_dom S1, max_dom S2}"
      using dom_set_filter_union max_union max_dom_def 
proof-
 have 1:"dom_set_filter (S1 \<union> S2) = {} \<Longrightarrow> (dom_set_filter (S1) = {} )
                                          \<and> (dom_set_filter (S2) = {} )"
        using dom_set_filter_union by auto             
 moreover have "dom_set_filter (S1 \<union> S2) = {} \<Longrightarrow> max_dom (S1 \<union> S2) = 0"
            using max_dom_def by auto
 moreover have "dom_set_filter (S1 \<union> S2) = {} \<Longrightarrow> (max_dom S1 = 0)\<and>(max_dom S2 = 0)"
                  using 1 max_dom_def by auto
 ultimately have 2:"dom_set_filter (S1 \<union> S2) = {} \<Longrightarrow> 
                            max_dom (S1 \<union> S2) = Max {max_dom S1, max_dom S2}"
                     by auto
 have 3:"dom_set_filter (S1 \<union> S2) \<noteq> {} \<Longrightarrow> (dom_set_filter (S1) \<noteq> {} )
                                          \<or> (dom_set_filter (S2) \<noteq> {} )"
              using dom_set_filter_union by auto
 then have 4:"  (dom_set_filter (S1) \<noteq> {} )
                                          \<or> (dom_set_filter (S2) \<noteq> {} ) \<Longrightarrow>
                      ((dom_set_filter (S1) \<noteq> {} ) \<and> (dom_set_filter (S2) \<noteq> {} ))
                      \<or> ((dom_set_filter (S1) \<noteq> {} ) \<and> (dom_set_filter (S2) = {} ))
                      \<or> ((dom_set_filter (S1) = {} ) \<and> (dom_set_filter (S2) \<noteq> {} )) "
                         by auto
 then have 5:"(dom_set_filter (S1) \<noteq> {} ) \<and> (dom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> max_dom S1 = Max (dom_set_filter S1)
                   \<and> max_dom S2 = Max (dom_set_filter S2)"
    using max_dom_def assms by auto 
 then have "(dom_set_filter (S1) \<noteq> {} ) \<and> (dom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow>(dom_set_filter (S1 \<union> S2) \<noteq> {} )"
                    using dom_set_filter_union by auto
 then have "(dom_set_filter (S1) \<noteq> {} ) \<and> (dom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> max_dom (S1 \<union> S2) = Max (dom_set_filter (S1 \<union> S2))"
                using max_dom_def by auto                                                                             
 then have "(dom_set_filter (S1) \<noteq> {} ) \<and> (dom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> Max (dom_set_filter (S1 \<union> S2)) 
                            = Max {Max (dom_set_filter S1), Max (dom_set_filter S2)}"               
                          using finite_dom_set_filter dom_set_filter_union assms
                                  by (metis Un_empty max_union)
 then have 6:"(dom_set_filter (S1) \<noteq> {} ) \<and> (dom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> max_dom (S1 \<union> S2) = Max {max_dom S1, max_dom S2}"
                 using max_dom_def by (metis `dom_set_filter S1 \<noteq> {} \<and> dom_set_filter S2 \<noteq> {} \<Longrightarrow> max_dom (S1 \<union> S2) = Max (dom_set_filter (S1 \<union> S2))`)      

 have "(dom_set_filter (S1) =  {} ) \<and> (dom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> dom_set_filter (S1 \<union> S2) = dom_set_filter S2"
             using dom_set_filter_union    by auto
 then have "(dom_set_filter (S1) =  {} ) \<and> (dom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> Max (dom_set_filter (S1 \<union> S2)) = Max (dom_set_filter S2)"
               by auto
 moreover have "(dom_set_filter (S1) =  {} ) \<and> (dom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> Max {0, Max (dom_set_filter S2)} 
                            =  Max (dom_set_filter S2)"
                          using Max_two_elements by auto
 moreover have "(dom_set_filter (S1) =  {} ) \<and> (dom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> Max {max_dom S1, max_dom S2} 
                            = max_dom S2"
                              using max_dom_def by auto
 ultimately have "(dom_set_filter (S1) =  {} ) \<and> (dom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> Max (dom_set_filter (S1 \<union> S2)) = Max {max_dom S1, max_dom S2}"
            using max_dom_def   by auto
 then have 7:"(dom_set_filter (S1) =  {} ) \<and> (dom_set_filter (S2) \<noteq> {} )
                \<Longrightarrow> max_dom (S1 \<union> S2)= Max {max_dom S1, max_dom S2}"
             using max_dom_def by (metis `dom_set_filter S1 = {} \<and> dom_set_filter S2 \<noteq> {} \<Longrightarrow> dom_set_filter (S1 \<union> S2) = dom_set_filter S2`)
 
  have "(dom_set_filter (S2) =  {} ) \<and> (dom_set_filter (S1) \<noteq> {} )
                \<Longrightarrow> dom_set_filter (S1 \<union> S2) = dom_set_filter S1"
             using dom_set_filter_union    by auto
 then have "(dom_set_filter (S2) =  {} ) \<and> (dom_set_filter (S1) \<noteq> {} )
                \<Longrightarrow> Max (dom_set_filter (S1 \<union> S2)) = Max (dom_set_filter S1)"
               by auto
 moreover have "(dom_set_filter (S2) =  {} ) \<and> (dom_set_filter (S1) \<noteq> {} )
                \<Longrightarrow> Max {0, Max (dom_set_filter S1)} 
                            =  Max (dom_set_filter S1)"
                          using Max_two_elements by auto
 moreover have "(dom_set_filter (S2) =  {} ) \<and> (dom_set_filter (S1) \<noteq> {} )
                \<Longrightarrow> Max {max_dom S1, max_dom S2} 
                            = max_dom S1"
                              using max_dom_def by auto
 ultimately have "(dom_set_filter (S2) =  {} ) \<and> (dom_set_filter (S1) \<noteq> {} )
                \<Longrightarrow> Max (dom_set_filter (S1 \<union> S2)) = Max {max_dom S1, max_dom S2}"
            using max_dom_def   by auto
 then have 8:"(dom_set_filter (S2) =  {} ) \<and> (dom_set_filter (S1) \<noteq> {} )
                \<Longrightarrow> max_dom (S1 \<union> S2)= Max {max_dom S1, max_dom S2}"
             using max_dom_def by (metis `dom_set_filter S2 = {} \<and> dom_set_filter S1 \<noteq> {} \<Longrightarrow> dom_set_filter (S1 \<union> S2) = dom_set_filter S1`)
 from 2 3 6 7 8 show ?thesis by auto
qed



(*codom_max_set equals codomain_block - To be proved in a bit*)
 

end 
