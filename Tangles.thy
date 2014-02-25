theory Tangles 
imports Preliminaries
begin


(* Time to split the file: Links and Tangles in another file*)

text{*well_defined walls as a type called diagram. The morphisms Abs_diagram maps a well defined wall to 
its diagram type and Rep_diagram maps the diagram back to the wall *}

typedef Tangle = "{(x::walls). well_defined_tangle x}"
 apply (rule_tac x = "prod (cement cup) (basic (cement cap))" in exI)
 apply(auto)
 apply(simp add:abs_def well_defined_tangle_def)
 done

typedef diagram = "{(x::walls). well_defined x}"
 apply (rule_tac x = "prod (cement cup) (basic (cement cap))" in exI)
 apply(auto)
 apply(simp add:abs_def well_defined_def)
 done

text{*The next few lemmas list the properties of well defined diagrams*}

text{*For a well defined diagram, the morphism Rep_diagram acts as an inverse of Abs_diagram- 
the morphism which maps a well defined wall to its representative in the type- diagram*}

lemma Abs_Rep_well_defined: assumes " well_defined x" shows "Rep_diagram (Abs_diagram x) = x"
using Rep_diagram Abs_diagram_inverse assms mem_Collect_eq  by auto

text{*The map Abs_diagram is injective*}
lemma Rep_Abs_well_defined: assumes " well_defined x"  and "well_defined y" 
and  "(Abs_diagram x) = (Abs_diagram y)"
shows "x = y"
using Rep_diagram Abs_diagram_inverse assms mem_Collect_eq  by metis

text{* restating the property of well_defined walls in terms of diagram*}
lemma well_defined_composition: 
"((list_sum (domain_codomain_list (Rep_diagram z))+(abs (domain_wall (Rep_diagram z)))
+ (abs (codomain_wall (Rep_diagram z)))) = 0)"
   using Rep_diagram mem_Collect_eq well_defined_def by auto

lemma diagram_list_sum: 
"((list_sum (domain_codomain_list (Rep_diagram z))) = 0)"
   using well_defined_composition abs_non_negative_sum list_sum_non_negative
   abs_non_negative add_increasing add_nonneg_eq_0_iff
   by metis

lemma diagram_fst_wall_count: 
"(abs (domain_wall (Rep_diagram z)) = 0)"
   using well_defined_composition abs_non_negative_sum list_sum_non_negative
   abs_non_negative add_increasing add_nonneg_eq_0_iff
   by metis

 
text{* In order to locally defined moves, it helps to prove that if composition of two walls is a 
well defined wall then the number of outgoing strands of the wall below are equal to the number of 
incoming strands of the wall above. The following lemmas prove that for a well defined wall, t
he number of incoming and outgoing strands are zero*}

(* All this should become cleaner with pattern matching *)

lemma well_defined_fst_wall_count: 
assumes "well_defined x"
shows "(abs (domain_wall x) = 0)"
   using well_defined_composition abs_non_negative_sum list_sum_non_negative
         abs_non_negative add_increasing add_nonneg_eq_0_iff assms well_defined_def by metis


lemma is_link_fst_wall_count: 
assumes "is_link x"
shows "(abs (domain_wall x) = 0)"
  using abs_non_negative_sum(1) assms is_link_def by metis

lemma diagram_snd_wall_count: 
"(abs (domain_wall (Rep_diagram z)) = 0)"
   using well_defined_composition abs_non_negative_sum list_sum_non_negative
         abs_non_negative add_increasing add_nonneg_eq_0_iff 
   by metis


lemma well_defined_snd_wall_count: 
assumes "well_defined x"
shows "(abs (codomain_wall x) = 0)"
    using well_defined_composition abs_non_negative_sum list_sum_non_negative
          abs_non_negative add_increasing add_nonneg_eq_0_iff 
          assms well_defined_def
    by (metis)


lemma is_link_snd_wall_count: 
assumes "is_link x"
shows "(abs (codomain_wall x) = 0)"
   using assms comm_monoid_add_class.add.left_neutral is_link_def is_link_fst_wall_count by (metis)

lemma domain_codomain_list_sum_non_negative:
"(list_sum (domain_codomain_list x)) \<ge> 0"
     apply(induct_tac x) 
     apply(auto)
     apply (simp add: abs_non_negative add_increasing)
     done

lemma wall_count_list_list_sum_abs:
"(list_sum (domain_codomain_list x)) = abs (list_sum (domain_codomain_list x))"
     using domain_codomain_list_sum_non_negative abs_def 
     by auto


lemma wall_count_list_list_sum_zero_add:
assumes "(list_sum (domain_codomain_list x)) + (list_sum (domain_codomain_list y)) = 0"
shows "(list_sum (domain_codomain_list x)) = 0" and "(list_sum (domain_codomain_list y)) = 0"
       using abs_non_negative_sum wall_count_list_list_sum_abs assms 
       apply metis 
       using add_nonneg_eq_0_iff assms domain_codomain_list_sum_non_negative 
       by (auto)

lemma list_sum_concatenates:
"list_sum (x@y) = (list_sum x) + (list_sum y)"
       apply(induct_tac x)
       apply(auto)
       done

lemma domain_codomain_list_sum_compose:
"(list_sum (domain_codomain_list (x \<circ> y))) = 
(list_sum (domain_codomain_list x)) + ((abs ((domain_wall y) - (codomain_wall x)))) + 
(list_sum (domain_codomain_list y))"
  using domain_codomain_list_compose list_sum_def concatenate_def list_sum_concatenates
  by (metis ab_semigroup_add_class.add_ac(1) list_sum.simps(2))
(*
lemma is_tangle_compose: assumes "is_tangle (x \<circ> y)"
shows "is_tangle x" 
unfolding is_tangle_def sledgehammer
proof (induct_tac x)
fix x y z
 have "is_tangle (basic x)" using is_tangle.simps(1)  by auto
then show thesis
*)
lemma list_sum_compose: assumes "list_sum (domain_codomain_list x) = 0" 
       and "list_sum (domain_codomain_list y) = 0"
and "(codomain_wall x)= (domain_wall y)"
shows  "list_sum (domain_codomain_list (x\<circ>y)) = 0"
proof-
 from  domain_codomain_list_sum_compose and assms and abs_def 
  have "list_sum (domain_codomain_list (x\<circ>y)) 
           = (list_sum (domain_codomain_list x))+(list_sum (domain_codomain_list y))"
       by auto
 from this and assms have "list_sum (domain_codomain_list (x\<circ>y)) = 0" by auto 
 from this show ?thesis by auto
qed

lemma diagram_domain_codomain_list:
assumes "abs ((domain_wall y) - (codomain_wall x))>0"
shows "(list_sum (domain_codomain_list (x\<circ>y)) > 0)"
proof-
 have "(list_sum (domain_codomain_list x) \<ge>0)" and "(list_sum (domain_codomain_list y)\<ge>  0)"  
      using domain_codomain_list_sum_non_negative by auto
 moreover have  "abs ((domain_wall y) - (codomain_wall x))>0" 
      using assms by auto
 ultimately have "
  ( 
  (list_sum (domain_codomain_list x)) 
        + (abs ( (domain_wall y) - (codomain_wall x)))  
        + (list_sum (domain_codomain_list y))
           ) 
             > 0"
      using  add_le_less_mono add_less_le_mono double_zero_sym by auto
 moreover then have "(list_sum (domain_codomain_list (x \<circ> y)))  
             =  ((list_sum (domain_codomain_list x)) 
                + (abs ( (domain_wall y) - (codomain_wall x)))  
               + (list_sum (domain_codomain_list y)))" 
       using domain_codomain_list_sum_compose by auto
 ultimately show ?thesis by simp
qed

lemma diagram_wall_count_list_zero:
assumes "(list_sum (domain_codomain_list (x\<circ>y)) = 0)"
shows " abs ( (domain_wall y) - (codomain_wall x))=0"
  using diagram_domain_codomain_list list_sum_non_negative abs_non_negative assms less_le
  by (metis)



lemma diagram_list_sum_zero:
 assumes "well_defined x"
shows "list_sum (domain_codomain_list x) = 0" 
proof-
 have 1:"list_sum (domain_codomain_list(Rep_diagram (Abs_diagram x))) = 0" 
        using diagram_list_sum by metis
 then have "Rep_diagram (Abs_diagram x) = x" 
        using Abs_diagram_inverse assms mem_Collect_eq by (auto)
 then show ?thesis using 1 by metis
qed


lemma diagram_compose:
assumes "well_defined (x\<circ>y)"
shows " (abs ( (domain_wall y) - (codomain_wall x)))=0"
      using diagram_list_sum_zero diagram_wall_count_list_zero assms 
      by auto

lemma diagram_fst_equals_snd:
assumes "well_defined (x\<circ>y)"
shows " (domain_wall y) = (codomain_wall x)"
     using diagram_compose abs_zero_equality assms  
     by auto


text{*if composition of two walls is a well defined wall then the two walls are well defined tangles
*}
lemma diagram_list_sum_subsequence:
assumes "well_defined (x\<circ>y)"
shows "(list_sum (domain_codomain_list x) = 0)\<and>(list_sum (domain_codomain_list y) = 0)"
proof-
  have "abs (( domain_wall y) - (codomain_wall x)) = 0" 
       using diagram_compose assms by auto
  then have "(list_sum (domain_codomain_list x)) + (list_sum (domain_codomain_list y)) = 0"
       using diagram_list_sum_zero domain_codomain_list_sum_compose assms plus_int_code(1) 
       by metis
  then have goal1: "(list_sum (domain_codomain_list x)) = 0" 
        and goal2:"(list_sum (domain_codomain_list y)) = 0" 
      using wall_count_list_list_sum_zero_add by auto
  then  have "(list_sum (domain_codomain_list x) = 0)\<and>(list_sum (domain_codomain_list y) = 0)" 
      by auto
  from this show ?thesis by simp
qed

lemma assumes "(well_defined_tangle x)" 
          and "(well_defined_tangle y)" 
          and "(domain_wall y) = (codomain_wall x)"
      shows   "well_defined_tangle (x \<circ> y)"
proof-
 have "(list_sum (domain_codomain_list (x \<circ> y))) = 
                     (list_sum (domain_codomain_list x)) 
                    + ((abs ((domain_wall y) - (codomain_wall x))))  
                    + (list_sum (domain_codomain_list y))" 
   unfolding  domain_codomain_list_sum_compose by auto
 moreover have "((abs ((domain_wall y) - (codomain_wall x))))  = 0" 
          using assms abs_def by auto
 moreover have "list_sum (domain_codomain_list x) = 0" 
              using well_defined_tangle_def assms(1) by auto
 moreover have  "list_sum (domain_codomain_list y) = 0" 
              using well_defined_tangle_def assms(2) by auto
 ultimately have "(list_sum (domain_codomain_list (x \<circ> y))) = 0" by auto
 then show ?thesis using well_defined_tangle_def by auto
qed 

(*defining compose for diagrams*)
definition compose_Tangle::"Tangle \<Rightarrow> Tangle \<Rightarrow> Tangle" (infixl "\<circ>" 65)
 where
"compose_Tangle x y = Abs_Tangle ((Rep_Tangle x) \<circ> (Rep_Tangle y))"

theorem well_defined_compose: assumes "well_defined_tangle x" and "well_defined_tangle y"
and "domain_wall x = codomain_wall y"
shows "(Abs_Tangle x) \<circ> (Abs_Tangle y) = (Abs_Tangle (x \<circ> y))"
by (metis Abs_Tangle_inverse assms(1) assms(2) compose_Tangle_def mem_Collect_eq)

(*defining domain and co-domain of tangles*)
definition domain_Tangle::"Tangle \<Rightarrow> int"
where
"domain_Tangle x = domain_wall(Rep_Tangle x)"

definition codomain_Tangle::"Tangle \<Rightarrow> int"
where
"codomain_Tangle x = codomain_wall(Rep_Tangle x)"
end
