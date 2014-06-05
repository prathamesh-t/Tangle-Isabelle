theory Component
imports Link_Algebra 
begin


(*we begin by defining two different types of an end of a strand, domain refers to the fact the 
other end of a strand lies in the domain of the wall and codomain refers to the fact that other end
of a strand lies in the codomain*) 

(*endpoint of a strand is given by the type of the end point and a natural number which refers
to the  position of the other end of the strand*)  
(*ADD 1 to max_codom and max_dom*)
datatype endpt = dom nat|codom nat


(*the function str_number tells us the strand number of an endpt*)
definition str_number::"endpt \<Rightarrow> nat"
where
"str_number x = (case x of dom n \<Rightarrow> n|codom n \<Rightarrow> n)"

(*lemmas about str_number*)

lemma str_number_uniqueness:"str_number x \<noteq> str_number y \<Longrightarrow> (x \<noteq> y)"
       using str_number_def by auto

definition shift::" nat \<Rightarrow> nat \<Rightarrow> endpt \<Rightarrow> endpt"
where
"shift  m n x \<equiv> (case x of 
                  dom k \<Rightarrow> dom (k+m)
                 |codom k \<Rightarrow> codom (k+n))"


(*
lemma "finite S \<Longrightarrow> finite (index S)"
     sledgehammer
*)


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

definition max_dom::"(endpt \<times> endpt) set \<Rightarrow> nat"
where
"max_dom S \<equiv>  (if (dom_set_filter S = {}) then 0 else Max (dom_set_filter S))"

 
definition shift_tuple::"nat \<Rightarrow> nat \<Rightarrow> endpt \<times> endpt \<Rightarrow> endpt \<times> endpt"
where
"shift_tuple m n x \<equiv> (shift m n (fst x), shift m n (snd x))"

value "shift_tuple 1 2 (codom 2, codom 1)"

definition endpt_set_shift::" (endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set \<Rightarrow> 
                                        (endpt \<times> endpt) set"
where
"endpt_set_shift S1 S \<equiv> (shift_tuple (max_dom S1+1) (max_codom S1+1))`S"
(*replace above with workable definitions of codom_max and dom_max*)

definition set_addition::"(endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set \<Rightarrow> (endpt \<times> endpt) set"
                                      (infixl "\<oplus>" 65)
where
"set_addition S1 S2 \<equiv> (endpt_set_shift S1 S2) \<union> S1"

(*lemmas about set addition*)

lemma endpt_set_shift_empty:"endpt_set_shift S1 {} = {}"
         using endpt_set_shift_def by auto

(*block_action*)

primrec brick_to_endpt_set::"brick \<Rightarrow> (endpt \<times> endpt) set"
where 
"brick_to_endpt_set vert = {(codom 0, dom 0),(dom 0, codom 0)}"
|"brick_to_endpt_set cup = {(codom 0, codom 1),(codom 1, codom 0)}"
|"brick_to_endpt_set cap = {(dom 0, dom 1),(dom 1, dom 0)}"
|"brick_to_endpt_set over = {(codom 0, dom 1),(dom 1, codom 0)}"
|"brick_to_endpt_set under = {(codom 0, dom 1),(dom 1, codom 0)}"

primrec block_to_endpt_set::"block \<Rightarrow> (endpt \<times> endpt) set"
where 
"block_to_endpt_set [] = {}"
|"block_to_endpt_set (x#xs) = (brick_to_endpt_set x)\<oplus>(block_to_endpt_set xs)"

(*rewrite some stuff to make it compatible*) 
(*To prove- 
 Set_addition takes injective sets to injective set
 Set_addition takes symmetric sets to symmetric sets
 antireflexive
 complete-linear(hardest one) et al*)

(*symmetric properties*)
definition symmetric::"('a \<times> 'a) set \<Rightarrow> bool"
 where
"symmetric S \<equiv> \<forall>x.\<forall>y.((x,y) \<in> S) \<longrightarrow> ((y,x) \<in> S)"  

lemma symmetric_union:
  assumes "symmetric A" and "symmetric B"
  shows "symmetric (A \<union> B)"
     using assms unfolding symmetric_def by auto

lemma symmetric_pre_condn:fixes x y assumes "symmetric S" and "(x,y) \<in> (endpt_set_shift S1 S)"
      shows "(y,x) \<in> (endpt_set_shift S1 S)"
    proof-
    have "(x,y) \<in> (endpt_set_shift S1 S)"
                  by (metis assms(2))
    then have "\<exists>a b. (x,y) = (shift_tuple (max_dom S1+1) (max_codom S1+1) (a,b))\<and>((a,b) \<in> S)"
                      unfolding endpt_set_shift_def image_iff prod.exhaust by auto
    then obtain a b where "(x,y) = (shift_tuple  (max_dom S1+1) (max_codom S1+1) (a,b))\<and>((a,b) \<in> S)"
                      by auto
    then have 1:"(x,y) = (shift_tuple  (max_dom S1+1) (max_codom S1+1) (a,b))\<and>((a,b) \<in> S)"
                  by auto
    then have "(b,a) \<in> S"
                  by (metis assms(1) symmetric_def)
    then have 2:"shift_tuple  (max_dom S1+1) (max_codom S1+1) (b,a) \<in> (endpt_set_shift S1 S)"
                        using endpt_set_shift_def image_def by auto
    then have "shift_tuple  (max_dom S1+1) (max_codom S1+1) (b,a) = (y,x)"
                  using shift_tuple_def shift_def 1 fst_conv snd_conv by auto
    then show ?thesis using 2 by auto 
qed

lemma symmetric_endpt_set_shift:"symmetric S \<Longrightarrow> (symmetric (endpt_set_shift S1 S))"
          using symmetric_def symmetric_pre_condn by metis

lemma symmetric_set_addition:assumes "symmetric S1" and "symmetric S2"
           shows "symmetric (set_addition S1 S2)"
                     using set_addition_def assms symmetric_endpt_set_shift symmetric_union 
                       by metis

lemma symmetric_brick_map: fixes x 
                          shows "symmetric (brick_to_endpt_set x)"
proof(cases "x")
 case vert
  show ?thesis
           unfolding symmetric_def brick_to_endpt_set_def vert by auto
 next
 case cup
   show ?thesis
           unfolding symmetric_def brick_to_endpt_set_def cup by auto  
 next
 case cap
   show ?thesis
           unfolding symmetric_def brick_to_endpt_set_def cap by auto 
 next
 case over
   show ?thesis
           unfolding symmetric_def brick_to_endpt_set_def over by auto   
 next
 case under
   show ?thesis
           unfolding symmetric_def brick_to_endpt_set_def under by auto     
qed            

theorem symmetric_block_to_endpt_set: "symmetric (block_to_endpt_set xs)"
 apply(induct_tac xs)
 apply(auto)   
 apply(simp add:symmetric_def)
  by (metis symmetric_brick_map symmetric_set_addition)

(*antireflexive*)


definition antireflexive ::"('a \<times> 'a) set \<Rightarrow> bool"
where
"antireflexive S \<equiv> \<forall>x.((x \<in> S) \<longrightarrow> (fst x \<noteq> snd x))"
 
lemma antireflexive_union:assumes "antireflexive S1" and "antireflexive S2"
         shows "antireflexive (S1 \<union> S2)"
         using assms antireflexive_def by auto

lemma shift_injectivity:"(shift m n a) = (shift m n b) \<Longrightarrow> a = b"
        apply(case_tac a)
        apply(case_tac b)
        apply(auto)
        apply (metis endpt.simps(5) nat_add_commute nat_add_left_cancel shift_def)
        apply (metis endpt.distinct(1) endpt.simps(5) endpt.simps(6) shift_def)
        apply(case_tac b)
        apply(auto)
        apply (metis (lifting) endpt.distinct(1) endpt.simps(5) endpt.simps(6) shift_def) 
        apply (metis endpt.simps(6) nat_add_commute nat_add_left_cancel shift_def)
        done
lemma shift_tuple_injective:"(shift_tuple m n (a,b)) = (x,x) \<Longrightarrow> a = b"
           using shift_injectivity fst_conv snd_conv shift_tuple_def   by metis

lemma antireflexive_pre_condn:fixes x  assumes "antireflexive S" 
      shows "(x,x) \<notin> (endpt_set_shift S1 S)"
proof(rule ccontr)
 assume 0:"\<not>((x,x) \<notin> (endpt_set_shift S1 S))"
 then have "(x,x) \<in> (endpt_set_shift S1 S)"
           by auto
 then have "\<exists>a b.((x,x) = shift_tuple (max_dom S1+1) (max_codom S1+1) (a,b)) \<and> (a,b) \<in> S"
           using endpt_set_shift_def by (metis image_iff prod.exhaust)
 then obtain a b where "(x,x) = shift_tuple (max_dom S1+1) (max_codom S1+1) (a,b)  \<and> (a,b) \<in> S"
                   by auto
 then have 1:"((x,x) = shift_tuple (max_dom S1+1) (max_codom S1+1) (a,b))  \<and> (a,b) \<in> S"
                by auto
 then have "a = b"        
               using shift_tuple_injective by metis   
 then have "(a,a) \<in> S" 
               using 1 by auto
 then show False using 0 assms unfolding antireflexive_def by auto
qed

lemma endpt_set_shift_antireflexive: "antireflexive S \<Longrightarrow> (antireflexive (endpt_set_shift S1 S))"
                 using antireflexive_pre_condn antireflexive_def fst_conv snd_conv pair_collapse
                     by (metis )

theorem antireflexive_set_addition:
        assumes "antireflexive S1" and "antireflexive S2"
            shows "antireflexive (S1 \<oplus> S2)"
            using set_addition_def endpt_set_shift_antireflexive assms antireflexive_union
            by metis

lemma antireflexive_brick_map: fixes x 
                          shows "antireflexive (brick_to_endpt_set x)"
proof(cases "x")
 case vert
  show ?thesis
           unfolding antireflexive_def brick_to_endpt_set_def vert by auto
 next
 case cup
   show ?thesis
           unfolding antireflexive_def brick_to_endpt_set_def cup by auto  
 next
 case cap
   show ?thesis
           unfolding antireflexive_def brick_to_endpt_set_def cap by auto 
 next
 case over
   show ?thesis
           unfolding antireflexive_def brick_to_endpt_set_def over by auto   
 next
 case under
   show ?thesis
           unfolding antireflexive_def brick_to_endpt_set_def under by auto     
qed            

theorem antireflexive_block_to_endpt_set: "antireflexive (block_to_endpt_set xs)"
 apply(induct_tac xs)
 apply(auto)   
 apply(simp add:antireflexive_def)
  by (metis antireflexive_brick_map antireflexive_set_addition)


(*Proving Injectivity*)
