theory Tangles 
imports Preliminaries
begin


(* Time to split the file: Links and Tangles in another file*)

text{*well_defined wall as a type called diagram. The morphisms Abs_diagram maps a well defined wall to 
its diagram type and Rep_diagram maps the diagram back to the wall *}

typedef Tangle_Diagram = "{(x::wall). is_tangle_diagram x}"
 apply (rule_tac x = "prod (cup#[]) (basic (cap#[]))" in exI)
 apply(auto)
 done

typedef Link_Diagram = "{(x::wall). is_link_diagram x}"
 apply (rule_tac x = "prod (cup#[]) (basic (cap#[]))" in exI)
 apply(auto)
 apply(simp add:is_link_diagram_def abs_def)
 done

text{*The next few lemmas list the properties of well defined diagrams*}

text{*For a well defined diagram, the morphism Rep_diagram acts as an inverse of Abs_diagram- 
the morphism which maps a well defined wall to its representative in the type- diagram*}

lemma Abs_Rep_well_defined: 
        assumes " is_tangle_diagram x" 
        shows "Rep_Tangle_Diagram (Abs_Tangle_Diagram x) = x"
            using Rep_Tangle_Diagram Abs_Tangle_Diagram_inverse assms mem_Collect_eq  by auto

text{*The map Abs_diagram is injective*}
lemma Rep_Abs_well_defined: 
  assumes "is_tangle_diagram x"  
      and "is_tangle_diagram y" 
      and  "(Abs_Tangle_Diagram x) = (Abs_Tangle_Diagram y)"
  shows "x = y"
     using Rep_Tangle_Diagram Abs_Tangle_Diagram_inverse assms mem_Collect_eq  
     by metis

text{* restating the property of well_defined wall in terms of diagram*}
(*
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

*) 
text{* In order to locally defined moves, it helps to prove that if composition of two wall is a 
well defined wall then the number of outgoing strands of the wall below are equal to the number of 
incoming strands of the wall above. The following lemmas prove that for a well defined wall, t
he number of incoming and outgoing strands are zero*}

(* All this should become cleaner with pattern matching *)
(*
lemma well_defined_fst_wall_count: 
assumes "well_defined x"
shows "(abs (domain_wall x) = 0)"
   using well_defined_composition abs_non_negative_sum list_sum_non_negative
         abs_non_negative add_increasing add_nonneg_eq_0_iff assms well_defined_def by metis


lemma is_link_fst_wall_count: 
assumes "is_link_diagram x"
shows "(abs (domain_wall x) = 0)"
  using abs_non_negative_sum(1) assms is_link_diagram_def by metis

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
assumes "is_link_diagram x"
shows "(abs (codomain_wall x) = 0)"
   using assms comm_monoid_add_class.add.left_neutral is_link_diagram_def is_link_fst_wall_count by (metis)

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
*)
(*is_tangle_compose*)
lemma is_tangle_left_compose: 
 "is_tangle_diagram (x \<circ> y) \<Longrightarrow> is_tangle_diagram x" 
proof (induct x)
 case (basic z)
   have "is_tangle_diagram (basic z)" using is_tangle_diagram.simps(1)  by auto
   then show ?case using basic by auto
 next
 case (prod z zs)
   have "(z*zs)\<circ>y = (z*(zs \<circ> y))" by auto
   then have " is_tangle_diagram (z*(zs\<circ>y))" using assms prod by auto
   moreover then have 1: "is_tangle_diagram zs" 
        using is_tangle_diagram.simps(2) prod.hyps prod.prems  by metis
  ultimately have "domain_wall (zs \<circ> y) = codomain_block z"
         by (metis is_tangle_diagram.simps(2))  
  moreover have "domain_wall (zs \<circ> y) = domain_wall zs" 
         using domain_wall_def domain_wall_compose by auto
  ultimately have "domain_wall zs = codomain_block z" by auto
  then have "is_tangle_diagram (z*zs)" 
    by (metis "1" is_tangle_diagram.simps(2))
  then show ?case by auto
 qed

lemma is_tangle_right_compose: 
 "is_tangle_diagram (x \<circ> y) \<Longrightarrow> is_tangle_diagram y"
proof (induct x)
 case (basic z)
  have "(basic z) \<circ> y = (z*y) " using basic  by auto
  then have "is_tangle_diagram y" 
         unfolding is_tangle_diagram.simps(2) using basic.prems by (metis is_tangle_diagram.simps(2))
  then show ?case using basic.prems by auto 
 next
 case (prod z zs)
  have "((z*zs) \<circ> y) = (z *(zs \<circ> y))" by auto
  then have " is_tangle_diagram (z*(zs \<circ> y))" using assms prod by auto
  then have "is_tangle_diagram (zs \<circ> y)" using is_tangle_diagram.simps(2) by metis
  then have "is_tangle_diagram y"  using prod.hyps by auto 
  then show ?case by auto
 qed


(*
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


text{*if composition of two wall is a well defined wall then the two wall are well defined tangles
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
*)
(*tangle diagrams using composition*)
lemma comp_of_tangle_dgms: assumes"is_tangle_diagram y" 
shows "((is_tangle_diagram x)\<and>(codomain_wall x = domain_wall y)) \<Longrightarrow> is_tangle_diagram (x \<circ> y)"
proof(induct x)
 case (basic z)
   have "codomain_block z = codomain_wall (basic z)" 
      using domain_wall_def by auto
   moreover have "(basic z)\<circ>y= z*y" 
      using compose_def by auto
   ultimately have "codomain_block z = domain_wall y" 
      using basic.prems by auto 
    moreover have "is_tangle_diagram y" 
      using assms by auto
    ultimately have "is_tangle_diagram (z*y)" 
      unfolding is_tangle_diagram_def by auto
     then show ?case by auto
 next
 case (prod z zs)
   have "is_tangle_diagram (z*zs)" 
       using prod.prems by metis 
   then have "codomain_block z = domain_wall zs" 
      using is_tangle_diagram.simps(2) prod.prems  by metis
   then have "codomain_block z = domain_wall (zs \<circ> y)" 
      using domain_wall.simps domain_wall_compose by auto 
   moreover have "is_tangle_diagram (zs \<circ> y)" 
      using prod.hyps by (metis codomain_wall.simps(2) is_tangle_diagram.simps(2) prod.prems)
   ultimately have "is_tangle_diagram (z*(zs \<circ> y))" 
     unfolding is_tangle_diagram_def by auto 
   then show ?case by auto
 qed

lemma composition_of_tangle_diagrams:assumes "is_tangle_diagram x" and "is_tangle_diagram y"
     and "(domain_wall y = codomain_wall x)" shows "is_tangle_diagram (x \<circ> y)"
    using comp_of_tangle_dgms using assms by auto
    

lemma converse_composition_of_tangle_diagrams:
  "is_tangle_diagram (x \<circ> y) \<Longrightarrow> (domain_wall y) = (codomain_wall x)"
 proof(induct x)
 case (basic z)
   have "(basic z) \<circ> y = z * y" 
      using compose_def basic by auto 
   then have 
    "is_tangle_diagram ((basic z) \<circ> y) \<Longrightarrow> 
              (is_tangle_diagram y)\<and> (codomain_block z = domain_wall y)"
     using is_tangle_diagram.simps(2)  by (metis)
   then have "(codomain_block z) = (domain_wall y)" 
      using basic.prems by auto
   moreover have "codomain_wall (basic z) = codomain_block z"
      using domain_wall_compose by auto
   ultimately have "(codomain_wall (basic z)) = (domain_wall y)" 
      by auto
   then show ?case by simp
 next
 case (prod z zs)
    have "codomain_wall zs = domain_wall y" 
          using prod.hyps prod.prems 
          by (metis compose_Nil compose_leftassociativity is_tangle_right_compose)
    moreover have "codomain_wall zs = codomain_wall (z*zs)"
          using domain_wall_compose by auto
    ultimately show ?case by metis
 qed
(*
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
*)
(*defining compose for diagrams*)
definition compose_Tangle::"Tangle_Diagram \<Rightarrow> Tangle_Diagram \<Rightarrow> Tangle_Diagram" (infixl "\<circ>" 65)
 where
"compose_Tangle x y = Abs_Tangle_Diagram ((Rep_Tangle_Diagram x) \<circ> (Rep_Tangle_Diagram y))"

theorem well_defined_compose: 
 assumes "is_tangle_diagram x" 
     and "is_tangle_diagram y"
     and "domain_wall x = codomain_wall y"
 shows "(Abs_Tangle_Diagram x) \<circ> (Abs_Tangle_Diagram y) = (Abs_Tangle_Diagram (x \<circ> y))"
     using  Abs_Tangle_Diagram_inverse assms(1) assms(2) compose_Tangle_def mem_Collect_eq 
     by auto

(*defining domain and co-domain of tangles*)
definition domain_Tangle::"Tangle_Diagram \<Rightarrow> int"
where
"domain_Tangle x = domain_wall(Rep_Tangle_Diagram x)"

definition codomain_Tangle::"Tangle_Diagram \<Rightarrow> int"
where
"codomain_Tangle x = codomain_wall(Rep_Tangle_Diagram x)"

end
