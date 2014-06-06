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




(*defining maximum of codom elements and dom elements *)

definition codom_set_filter::"(endpt \<times> endpt) set \<Rightarrow> nat set"
where
"codom_set_filter xs \<equiv> {n. \<exists>x.((codom n,x) \<in> xs)}"

definition dom_set_filter::"(endpt \<times> endpt) set \<Rightarrow> nat set"
where
"dom_set_filter xs \<equiv> {n. \<exists>x.((dom n,x) \<in> xs)}"

definition coordinate::"(endpt \<times> endpt) \<Rightarrow> nat"
where
"coordinate x \<equiv> (case x of (dom n,y) \<Rightarrow> n|(codom n,y) \<Rightarrow> n)"

definition str_number_set::"(endpt \<times> endpt) set \<Rightarrow> nat set"
where
"str_number_set S \<equiv> (coordinate)`S"


lemma empty_set_codom_set_filter: "codom_set_filter {}  = {}"
     using codom_set_filter_def by auto

lemma empty_set_dom_set_filter: "dom_set_filter {}  = {}"
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
|"brick_to_endpt_set cup = {(codom 1, codom 0),(codom 0, codom 1)}"
|"brick_to_endpt_set cap = {(dom 1, dom 0),(dom 0, dom 1)}"
|"brick_to_endpt_set over = {(codom 1, dom 0),(dom 0, codom 1),(codom 0, dom 1),(dom 1, codom 0)}"
|"brick_to_endpt_set under = {(codom 1, dom 0),(dom 0, codom 1),(codom 0, dom 1),(dom 1, codom 0)}"

primrec block_to_endpt_set::"block \<Rightarrow> (endpt \<times> endpt) set"
where 
"block_to_endpt_set [] = {}"
|"block_to_endpt_set (x#xs) = (brick_to_endpt_set x)\<oplus>(block_to_endpt_set xs)"

(*rewrite some stuff to make it compatible*)
(*Finite-ness*)

lemma finite_endpt_set_shift:"finite S \<Longrightarrow> finite (endpt_set_shift S1 S)"
      using endpt_set_shift_def by auto

lemma finite_set_addition_def: "finite S1 \<and> finite S2 \<Longrightarrow> finite (S1 \<oplus> S2)"
       using finite_endpt_set_shift set_addition_def by auto

lemma finite_brick_to_endpt_set:"finite (brick_to_endpt_set x)"
                apply(case_tac x)
                apply(auto)
                done

lemma finite_block_to_endpt_set:"finite (block_to_endpt_set xs)"
               apply(induct_tac xs)
               apply(auto)
               by (metis (full_types) finite_brick_to_endpt_set finite_set_addition_def)

lemma assumes "\<forall>x.((x \<in> A) \<longrightarrow> (x \<in> B))"
      shows "A \<subseteq> B"
         using subset_eq assms subsetI by (metis (full_types) )     
lemma codom_set_filter_subset:"codom_set_filter S \<subseteq> str_number_set S"
 proof-
      have "\<forall>n.(n \<in> codom_set_filter S  \<longrightarrow> (n \<in> str_number_set S))"
       proof-
       have "\<forall>n.(n \<in> codom_set_filter S  \<longrightarrow> (\<exists>x.(codom n, x) \<in> S))"
           using codom_set_filter_def  by auto 
       then have "\<forall>n.(n \<in> codom_set_filter S  \<longrightarrow> n \<in> str_number_set S)"
           using codom_set_filter_def str_number_set_def coordinate_def 
           by (metis (mono_tags) endpt.simps(6) image_eqI split_conv)  
       then show ?thesis by auto
       qed
 then show ?thesis using subset_eq by auto
 qed

lemma dom_set_filter_subset:"dom_set_filter S \<subseteq> str_number_set S"
 proof-
      have "\<forall>n.(n \<in> dom_set_filter S  \<longrightarrow> (n \<in> str_number_set S))"
       proof-
       have "\<forall>n.(n \<in> dom_set_filter S  \<longrightarrow> (\<exists>x.(dom n, x) \<in> S))"
           using dom_set_filter_def  by auto 
       then have "\<forall>n.(n \<in> dom_set_filter S  \<longrightarrow> n \<in> str_number_set S)"
           using dom_set_filter_def str_number_set_def coordinate_def 
                      by (metis (mono_tags) endpt.simps(5) image_eqI split_conv)
       then show ?thesis by auto
       qed
 then show ?thesis using subset_eq by auto
 qed     

lemma finite_str_number_set:"finite S \<Longrightarrow> finite (str_number_set S)"
             using str_number_set_def by auto

lemma finite_dom_set_filter:"finite S \<Longrightarrow> finite (dom_set_filter S)"
               using dom_set_filter_subset finite_str_number_set rev_finite_subset
                by (metis (full_types) )

lemma finite_codom_set_filter:"finite S \<Longrightarrow> finite (codom_set_filter S)"
               using codom_set_filter_subset finite_str_number_set rev_finite_subset
                by (metis (full_types) )

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
               using 0 Max_def Max_S  finite_dom_set_filter by auto
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

lemma symmetric_cross:"symmetric {(codom 1, dom 2),(dom 2, codom 1),(codom 2, dom 1),(dom 1, codom 2)}"
                unfolding symmetric_def by auto
lemma symmetric_brick_map:  "symmetric (brick_to_endpt_set x)"
              apply(case_tac x)
             unfolding symmetric_def using symmetric_cross by auto

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


lemma antireflexive_brick_map: "antireflexive (brick_to_endpt_set x)"
            apply(case_tac x)
            unfolding antireflexive_def by auto

theorem antireflexive_block_to_endpt_set: "antireflexive (block_to_endpt_set xs)"
 apply(induct_tac xs)
 apply(auto)   
 apply(simp add:antireflexive_def)
  by (metis antireflexive_brick_map antireflexive_set_addition)


(*Proving Injectivity*)

definition injective::"(endpt \<times> endpt) set \<Rightarrow> bool"
where
"injective S \<equiv> \<forall>x y z.((x,y) \<in> S \<and> (x,z) \<in> S \<longrightarrow> y = z)"
   

definition found_in::"endpt \<Rightarrow> (endpt \<times> endpt) set \<Rightarrow> bool"
where
"found_in a S \<equiv> (\<exists>x.((a,x) \<in> S))"


lemma found_in_union:"\<forall>x.(found_in x (A \<union> B)) 
                         \<longrightarrow> (found_in x A) \<or> (found_in x B)" 
        using found_in_def by auto

             


lemma endpt_set_shift_found_in:
 fixes x
 assumes "finite S1" and "(found_in x S1) "
 shows "\<not>(found_in x (endpt_set_shift S1 S))"
 proof (rule ccontr)
 assume 0:"\<not>(\<not>(found_in x (endpt_set_shift S1 S)))"
 then have 1:"found_in x (endpt_set_shift S1 S)" 
           by auto
 then show False
     proof-
      have "(\<exists>a b.((x, a) \<in> S1)\<and> (x,b) \<in> (endpt_set_shift S1 S))"
             using found_in_def assms(2) 1 by (metis )
      then obtain a b where "((x, a) \<in> S1)\<and> (x,b) \<in> (endpt_set_shift S1 S)"
              by auto
      then have 1:" ((x, a) \<in> S1)\<and> (x,b) \<in> (endpt_set_shift S1 S)"
                    by auto
       then have 11:"((x, a) \<in> S1)\<and> (x,b) \<in> (endpt_set_shift S1 S)"
                      using 1  by auto
       then have "\<exists>y c.(x,b) = (shift_tuple ((max_dom S1+1)) ((max_codom S1+1)) (y,c))" 
                  using endpt_set_shift_def by auto
       then obtain y c where "(x,b) = (shift_tuple ((max_dom S1+1)) ((max_codom S1+1)) (y,c))" 
                              by auto
       then have 12:"x = shift ((max_dom S1+1)) ((max_codom S1+1)) y"
                           using shift_tuple_def by auto
       then show ?thesis
                  proof(cases "y")
                  case (dom n)
                   have "x = dom ((max_dom S1)+n+1)"
                                using dom 12 shift_def by auto
                   then have dom_1:"((max_dom S1)+n+1) \<in> dom_set_filter S1"
                                  using 11 dom_set_filter_def by auto
                   then have dom_2:"dom_set_filter S1 \<noteq> {}"
                                         by auto
                   then have "max_dom S1 = Max (dom_set_filter S1)"
                               using max_dom_def by auto
                   then have " ((max_dom S1)+n+1)  \<le> max_dom S1"
                                  using max_dom_set_filter assms by (metis dom_1)
                   moreover have "(max_dom S1)+n +1> (max_dom S1)"
                                    by auto
                   ultimately show False by auto
                  next
                  case (codom n)
                       have "x = codom ((max_codom S1)+1+n)"
                                using codom 12 shift_def by auto
                   then have codom_1:"((max_codom S1)+1+n) \<in> codom_set_filter S1"
                                  using 11 codom_set_filter_def by auto
                   then have codom_2:"codom_set_filter S1 \<noteq> {}"
                                         by auto
                   then have "max_codom S1 = Max (codom_set_filter S1)"
                               using max_codom_def by auto
                   then have " ((max_codom S1)+1+n)  \<le> max_codom S1"
                                  using max_codom_set_filter assms by (metis codom_1)
                   moreover have "(max_codom S1)+1+n > (max_codom S1)"
                                    by auto
                   ultimately show False by auto
                  qed  
                 qed
   qed

lemma injective_endpt_set_shift:
      assumes "injective S2"
     shows "injective (endpt_set_shift S1 S2)"
  proof(rule ccontr)
  assume 0:"\<not>injective (endpt_set_shift S1 S2)"
  then have "\<exists>x y z.((x,y) \<in> (endpt_set_shift S1 S2) \<and> (x,z) \<in> (endpt_set_shift S1 S2) 
                     \<and>(y \<noteq> z))"
                 using injective_def by auto
  then obtain x y z where "((x,y) \<in> (endpt_set_shift S1 S2) \<and> (x,z) \<in> (endpt_set_shift S1 S2) 
                     \<and>(y \<noteq> z))"
                  by auto
  then have 1:"((x,y) \<in> (endpt_set_shift S1 S2) \<and> (x,z) \<in> (endpt_set_shift S1 S2) 
                     \<and>(y \<noteq> z))"
                  by auto
  then have "\<exists>a b.((x,y) = shift_tuple ((max_dom S1)+1) ((max_codom S1)+1)
                                              (a,b))\<and>(a,b)\<in> S2"
                        using endpt_set_shift_def by auto
  then obtain a b where "((x,y) = shift_tuple ((max_dom S1)+1) ((max_codom S1)+1)
                                              (a,b))\<and>(a,b)\<in> S2"
                        using endpt_set_shift_def by auto
  moreover have "\<exists>c d.((x,z) = shift_tuple ((max_dom S1)+1) ((max_codom S1)+1)
                                              (c,d)\<and>(c,d)\<in> S2)"
                        using endpt_set_shift_def 1 by auto 
  moreover then obtain c d where "((x,z) = shift_tuple ((max_dom S1)+1) ((max_codom S1)+1)
                                              (c,d))\<and>(c,d)\<in> S2"
                        using endpt_set_shift_def by auto
  ultimately have "shift ((max_dom S1)+1) ((max_codom S1)+1) c 
                            = shift ((max_dom S1)+1) ((max_codom S1)+1) a"
                             using shift_tuple_def fst_conv by metis
  then have 2:"a = c"
                 using shift_injectivity by auto
  then have "(a,b) \<in> S2 \<and> (a,d) \<in> S2"
                by (metis `(x, y) = shift_tuple (max_dom S1 + 1) (max_codom S1 + 1) (a, b) \<and> (a, b) \<in> S2` `(x, z) = shift_tuple (max_dom S1 + 1) (max_codom S1 + 1) (c, d) \<and> (c, d) \<in> S2`)
  then have "b = d"
            using assms(1) injective_def by auto
  then have "y = z"
           using 2   by (metis  `(x, y) = shift_tuple (max_dom S1 + 1) (max_codom S1 + 1) (a, b) \<and> (a, b) \<in> S2` `(x, z) = shift_tuple (max_dom S1 + 1) (max_codom S1 + 1) (c, d) \<and> (c, d) \<in> S2` prod.inject)
  then show False using 1 by auto
qed
 
lemma assumes "finite S1" shows "\<forall>x.((found_in x  S1) \<longrightarrow> (\<not>(found_in x (endpt_set_shift S1 S))))"
                using assms endpt_set_shift_found_in by auto

lemma not_found_in: "\<not>(found_in x S) \<longrightarrow> (\<forall>y.(x,y) \<notin> S)"
         using found_in_def by auto

theorem injective_set_addition: assumes "finite S1" and "injective S1" and "injective S2"
       shows "injective (S1 \<oplus> S2)"
proof(rule ccontr)
 assume contr:"\<not>(injective (S1 \<oplus> S2))"
 then have "\<exists>x y z.((x,y) \<in> (S1 \<oplus> S2) \<and> (x,z) \<in> (S1 \<oplus> S2) \<and> (y \<noteq> z))"
                  using injective_def by auto
 then obtain x y z where "((x,y) \<in> (S1 \<oplus> S2) \<and> (x,z) \<in> (S1 \<oplus> S2)) \<and> (y \<noteq> z)"
                   by auto
 then have 1:"((x,y) \<in> (S1 \<oplus> S2) \<and> (x,z) \<in> (S1 \<oplus> S2)) \<and> (y \<noteq> z)"
                by auto
 then have 2:"((x,y) \<in> S1 \<union> (endpt_set_shift S1 S2))\<and> ((x,z) \<in> S1 \<union> (endpt_set_shift S1 S2)) "
              using set_addition_def by auto
 then show False
     proof(cases "(x,y) \<in> S1")
     case True
        then have 11:"(x,z) \<notin> S1"
                using assms(2) 1 injective_def by auto
        moreover have 12:"found_in x S1"
                     using found_in_def True by auto
        then  have "\<not>(found_in x (endpt_set_shift S1 S2))"
                       using endpt_set_shift_found_in assms(2) by (metis assms(1))
        then have 13:"(x,z) \<notin> (endpt_set_shift S1 S2)"
                  using not_found_in by auto
        then show ?thesis using 2 11 by auto
     next
     case False
        then have 11:"(x,y) \<in> (endpt_set_shift S1 S2)"
                   using 2 by auto
        then have "(x,z) \<notin> (endpt_set_shift S1 S2)"
                     using injective_endpt_set_shift "1" assms(3) injective_def  by (metis )
        then have "(x,z) \<in> S1"
                   using 2 by auto
        moreover have "found_in x S1"
                     using found_in_def by (metis calculation)
        moreover then have "\<not>(found_in x (endpt_set_shift S1 S2))"
                       using endpt_set_shift_found_in assms(2) by (metis assms(1))
        then have 13:"(x,y) \<notin> (endpt_set_shift S1 S2)"
                  using not_found_in by auto
        then show ?thesis using 2 11 by auto
     qed
qed         

lemma injective_brick_to_endpt_set:"injective (brick_to_endpt_set x)"
                   apply(case_tac x)
                   apply(auto)
                   unfolding injective_def by auto   

lemma injective_block_to_endpt_set:"injective (block_to_endpt_set xs)"
                 apply(induct_tac xs)
                 apply(auto)
                 apply(simp add:injective_def)
                 by (metis finite_brick_to_endpt_set injective_brick_to_endpt_set 
                injective_set_addition)    

(*proving linearity*) 

definition shift_nat::"nat \<Rightarrow> nat \<Rightarrow> nat"
where
"shift_nat k n = (n+k)"
 
definition shift_nat_set::"nat \<Rightarrow> nat set \<Rightarrow> nat set"
where
"shift_nat_set k S \<equiv> (shift_nat k)`S"

value "shift_nat_set 3 {1,6,2,4,5}"
(*
lemma "(finite S)\<and>(S \<noteq> {}) \<Longrightarrow> Max (shift_nat_set k S) = Max S + k"
         apply(induct rule:finite.induct)
         apply(simp add:Max_def)
  *)

lemma "(finite S)\<and>(S \<noteq> {}) \<Longrightarrow> (max_codom (endpt_set_shift S1 S)) = (max_codom S)+(max_codom S1)+1"
        
