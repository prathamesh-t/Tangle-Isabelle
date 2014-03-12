theory Component_def
imports Tangles
begin

(*strand types are defined - vertical, left/right over, left/right under, left/right cap, left/ right cup*)
 (*convention - left over is the over going strand from right to left*)

datatype strand = str_vert|str_lover|str_lunder|str_rover|str_runder|str_lcap|str_rcap|str_lcup|str_rcup


(*Each of the basic tangles are assigned the strand types which they are composed of*)
primrec strand_list::"brick \<Rightarrow> strand list"
where
"strand_list vert = [str_vert]"
|"strand_list over = [str_rover, str_lunder]"
|"strand_list under = [str_runder, str_lover]"
|"strand_list cap = [str_rcap,str_lcap]"
|"strand_list cup = [str_rcup,str_lcup]"


(*Each of the blocks are assigned a list of strand types*)
primrec block_to_strand::"block \<Rightarrow> strand list"
where
"block_to_strand [] = []"
|"block_to_strand (x#xs) = (strand_list x)@(block_to_strand xs)"

(*Each wall is assigned a list of list of strands - this definition automatically gives us
a way to allot positions to strand types in the wall*)
primrec strand_list_list ::"wall \<Rightarrow> strand list list"
where
"strand_list_list (basic x) = [(block_to_strand x)]"
|"strand_list_list (prod x xs) = (block_to_strand x)#(strand_list_list xs)"

(*Given an 2-tuple of natural number (i,j) which can be used to denote the position of a strand in a
wall , the following functions gives the set of strand types to its
right in the block, while filtering out the strand types which are used in the caps and cups. This is important
to ensure alignment of strand types *)
(*cap-filter-out*)

definition filter_out_cap_prop::"strand \<Rightarrow> bool"
where
"filter_out_cap_prop x \<equiv> ((x =  str_vert) \<or> (x = str_lover)\<or> (x = str_lunder)\<or> (x = str_rover)
\<or>(x= str_runder)\<or>(x= str_lcup)\<or>(x= str_rcup))"

definition list_filter_out_cap::"strand list \<Rightarrow> strand list"
where
"list_filter_out_cap x = (filter (filter_out_cap_prop)  x)"

definition filter_out_cap::"wall \<Rightarrow> nat \<times> nat \<Rightarrow> strand list"
where
"filter_out_cap w x \<equiv> list_filter_out_cap (drop ((fst x)+1) ((strand_list_list w)!(snd x)))"

definition cap_minus_count::"wall \<Rightarrow> nat \<times> nat \<Rightarrow> nat"
where
"cap_minus_count w x = size (filter_out_cap w x)"

(*cup-filter- equivalent of filter_out_cap for cups*)

definition filter_out_cup_prop::"strand \<Rightarrow> bool"
where
"filter_out_cup_prop x \<equiv> ((x =  str_vert) \<or> (x = str_lover)\<or> (x = str_lunder)\<or> (x = str_rover)
\<or>(x= str_runder)\<or>(x= str_lcap)\<or>(x= str_rcap))"

definition list_filter_out_cup::"strand list \<Rightarrow> strand list"
where
"list_filter_out_cup x = (filter (filter_out_cup_prop) x)"

definition filter_out_cup::"wall \<Rightarrow> nat \<times> nat \<Rightarrow> strand list"
where
"filter_out_cup w x \<equiv> list_filter_out_cup (drop ((fst x)+1) ((strand_list_list w)!(snd x)))"

definition cup_minus_count::"wall \<Rightarrow> nat \<times> nat \<Rightarrow> nat"
where
"cup_minus_count w x = size (filter_out_cup w x)"

(*returns true if x=(s,i,j) for a given wall w such that s represents the strand in the position 
(i,j) of the strand array of w *)
definition well_defined_strand::"wall \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow>  bool"
where
"well_defined_strand w x \<equiv> ((strand_list_list w)!(snd (snd x))!(fst (snd x)) = (fst x))"


(*returns true if x=(s',i,j) for a given wall w such that s represents the strand in the position 
(i,j) of the strand array of w  and s = s'*)
definition strand_check::"wall \<Rightarrow> strand \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> bool"
where
"strand_check w s x \<equiv> (((strand_list_list w)!(snd (snd x))!(fst (snd x))) = s)
\<and>((fst x)= s)"

(*relates vertical strand to the one below it by checking the following - 
(1) if x (=(s1,i1,j1)) represents the strand s1 such that in the strand array of the given wall w, 
w!i1!j1 is s1. 
(2) s1 is the vertical strand (str_vert). 
(3) if y (=(s2,i2,j2)) represents the strand s2 such that in the strand array of the given wall w, 
w!i2!j2 is s2.
(4) end points of the strands match *)
definition relation_vert::"wall \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> bool"
where
"relation_vert w x y \<equiv> (strand_check w str_vert x) \<and> (well_defined_strand w y)
\<and> ((snd (snd y))+ 1= snd (snd x)) \<and> (cap_minus_count w (snd y) = cup_minus_count w (snd x))
\<and> (filter_out_cap_prop (fst y))"


(*returns true if  x =(s1,i1,j1) and  y = (s2, i2,j2) represent the adjacent strands 
-left cap and right cap respectively, *)
definition relation_lcap_rcap::"wall \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> bool"
where
"relation_lcap_rcap w x y \<equiv>(strand_check w str_lcap x)\<and> (strand_check w str_rcap y)
\<and>((snd (snd y)) = (snd (snd x))) \<and> ((fst (snd y) +1 = fst (snd x)))"

(*relates the left cap strand to the one below it by checking the following - 
(1) if x (=(s1,i1,j1)) represents the strand s1 such that in the strand array of the given wall w, 
w!i1!j1 is s1. 
(2) s1 is str_lcap. 
(3) if y (=(s2,i2,j2)) represents the strand s2 such that in the strand array of the given wall w, 
w!i2!j2 is s2.
(4) end points of the strands match *)
definition relation_lcap_below::"wall \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> bool"
where
"relation_lcap_below w x y \<equiv>(strand_check w str_lcap x)\<and>
(well_defined_strand w y)
\<and>((snd (snd y)) + 1= (snd (snd x))) \<and> ((cap_minus_count w (snd y) = cup_minus_count w (snd x)))
\<and> (filter_out_cap_prop (strand_list_list w!(snd (snd y))!(fst (snd y))))"


(*relates the right cap strand to the one below it by checking the following - 
(1) if x (=(s1,i1,j1)) represents the strand s1 such that in the strand array of the given wall w, 
w!i1!j1 is s1. 
(2) s1 is the right cap - str_rcap. 
(3) if y (=(s2,i2,j2)) represents the strand s2 such that in the strand array of the given wall w, 
w!i2!j2 is s2.
(4) end points of the strands match *)

definition relation_rcap_below::"wall \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> bool"
where
"relation_rcap_below w x y \<equiv>(strand_check w str_rcap x)\<and>
(well_defined_strand w y)
\<and>((snd (snd y)) + 1= (snd (snd x))) \<and> ((cap_minus_count w (snd y) = cup_minus_count w (snd x)))
\<and>  (filter_out_cap_prop (fst y))"


(*returns true  if  x =(s1,i1,j1) and  y = (s2, i2,j2) represent the adjacent strands 
-left cap and right cap respectively, *)
definition relation_lcup_rcup::"wall \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> bool"
where
"relation_lcup_rcup w x y \<equiv>(strand_check w str_lcup x)\<and> (strand_check w str_rcup y)
\<and>((snd (snd y)) = (snd (snd x))) \<and> ((fst (snd y) +1 = fst (snd x)))"

(*over-under-relations*)


(*relates the right over strand to the one diagonally across below the strand by checking the 
following - 
(1) if x (=(s1,i1,j1)) represents the strand s1 such that in the strand array of the given wall w, 
w!i1!j1 is s1. 
(2) s1 is the right rover - str_rover. 
(3) if y (=(s2,i2,j2)) represents the strand s2 such that in the strand array of the given wall w, 
w!i2!j2 is s2.
(4) end points of the strands match *)
definition relation_rover::"wall \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> bool"
where
"relation_rover w x y \<equiv> (strand_check w str_rover x)\<and> (well_defined_strand w y)
\<and>(snd (snd y)) + 1= (snd (snd x)) \<and> (cap_minus_count w (snd y) = cup_minus_count w (snd x) + 1)
\<and>  (filter_out_cap_prop (fst y)) "



(*relates the right under strand to the one diagonally across below the strand by checking the 
following - 
(1) if x (=(s1,i1,j1)) represents the strand s1 such that in the strand array of the given wall w, 
w!i1!j1 is s1. 
(2) s1 is the right rover - str_runder. 
(3) if y (=(s2,i2,j2)) represents the strand s2 such that in the strand array of the given wall w, 
w!i2!j2 is s2.
(4) end points of the strands match *)
definition relation_runder::"wall \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> bool"
where
"relation_runder w x y \<equiv> (strand_check w str_runder x)\<and> (well_defined_strand w y)
\<and>(snd (snd y)) + 1= (snd (snd x)) \<and> (cap_minus_count w (snd y) = cup_minus_count w (snd x) + 1)
\<and>  (filter_out_cap_prop (fst y)) "


(*relates the left over strand to the one diagonally across below the strand by checking the 
following - 
(1) if x (=(s1,i1,j1)) represents the strand s1 such that in the strand array of the given wall w, 
w!i1!j1 is s1. 
(2) s1 is the right rover - str_lover. 
(3) if y (=(s2,i2,j2)) represents the strand s2 such that in the strand array of the given wall w, 
w!i2!j2 is s2.
(4) end points of the strands match *)
definition relation_lover::"wall \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> bool"
where
"relation_lover w x y \<equiv> 
(strand_check w str_lover x)\<and> (well_defined_strand w y)\<and>
 (snd (snd y)) + 1= (snd (snd x)) \<and> ((cap_minus_count w (snd y)) + 1 = cup_minus_count w (snd x))
\<and>  (filter_out_cap_prop (fst y))"


(*relates the left under strand to the one diagonally across below the strand by checking the 
following - 
(1) if x (=(s1,i1,j1)) represents the strand s1 such that in the strand array of the given wall w, 
w!i1!j1 is s1. 
(2) s1 is the right rover - str_lunder. 
(3) if y (=(s2,i2,j2)) represents the strand s2 such that in the strand array of the given wall w, 
w!i2!j2 is s2.
(4) end points of the strands match *)
definition relation_lunder::"wall \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> bool"
where
"relation_lunder w x y \<equiv> (strand_check w str_lunder x)\<and> (well_defined_strand w y)\<and>
(snd (snd y)) + 1= (snd (snd x)) \<and> (cap_minus_count w (snd y) + 1 = cup_minus_count w (snd x))
\<and>  (filter_out_cap_prop (fst y))"


(*Returns true if two strands are related by any of the above relations*)
definition strand_rel::"wall \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> bool"
where
"strand_rel w x y \<equiv> ((relation_lcap_rcap w x y)
\<or>(relation_lcup_rcup w x y) \<or> (relation_vert w x y) \<or>(relation_lcap_below w x y)
\<or>(relation_rcap_below w x y)\<or> (relation_lover w x y) \<or> (relation_lunder w x y)
\<or>(relation_rover w x y) \<or> (relation_runder w x y)) "

(*given a relation, we obtain the symmetric closure of the relation*)
definition symmetrize::"('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"
where
"symmetrize r \<equiv> \<lambda> x y.(r x y)\<or>(r y x)"


(*symmetric variant of the strand relation*)
definition relation::"wall \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> bool"
where
"relation w \<equiv> (symmetrize (strand_rel w))"


(*Reflexive transitive closure of the above relation*)
definition strand_equivalence::"wall \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow> bool"
where
"strand_equivalence w \<equiv> (relation w)^**"


(*orbit of a given element of (strand \<times> nat \<times> nat), which is the set of elements which are related 
to it *)
definition orbit::"wall \<Rightarrow> strand \<times> nat \<times> nat \<Rightarrow>(strand \<times> nat \<times> nat) set"
where
"orbit w x = {y. strand_equivalence w x y = True}"

(*orbit space- the set of components - it is obtained by taking the orbit of all the 
well defined strands for a give wall w*)
definition orbit_space::"wall \<Rightarrow> (strand \<times> nat \<times> nat) set set"
where
"orbit_space w \<equiv> {(orbit w x)| x. well_defined_strand w x }"

(*the cardinality of orbit space gives the component_number of the wall*)
definition component_number::"wall \<Rightarrow> nat"
where
"component_number w \<equiv> card (orbit_space w)"

(*is a knot diagram only if the number of components are 1*)
definition is_Knot_diagram::"Link_Diagram \<Rightarrow> bool"
where
"is_Knot_diagram K \<equiv> (component_number (Rep_Link_Diagram K) = 1)"


(*

primrec strand_count::"strand  \<Rightarrow> nat \<times> nat"
where
"strand_count str_vert = (1,1)"
|"strand_count str_rover = (1,1)"
|"strand_count str_runder = (1,1)"
|"strand_count str_lover = (1,1)"
|"strand_count str_lunder = (1,1)"
|"strand_count str_rcap = (1,0)"
|"strand_count str_lcap = (1,0)"
|"strand_count str_rcup = (0,1)"
|"strand_count str_lcup = (0,1)"

lemma "component_number ((basic (cement cup)) \<circ> (basic (cement cap))) = 1"
proof-
have "strand_array ((basic (cement cup)) \<circ> (basic (cement cap))) = 
[[str_rcup,str_lcup],[str_rcap,str_lcap]]" by auto
let ?w = "(basic (cement cup)) \<circ> (basic (cement cap))"
have rel:"relation_lcap_rcap ?w (str_lcap,1,1) (str_rcap,0,1) " 
  proof-
   have "(strand_array ?w)!1!1 = str_lcap" by auto
   moreover have "(strand_array ?w)!1!0 = str_rcap" by auto 
   moreover have "fst (str_lcap,1,1) = str_lcap" by auto
   moreover have "fst (str_rcap,0,1) = str_rcap" by auto 
   moreover have "fst (snd (str_rcap,0,1)) + (1::nat) = fst(snd (str_lcap,1,1))"  by auto
   moreover have "snd (snd (str_rcap,0,1)) = snd (snd (str_lcap,0,1))" by auto
   ultimately show ?thesis unfolding relation_lcap_rcap_def by auto
   qed
then have rel2:"relation ?w (str_rcap,0,1) (str_lcap,1,1) " unfolding relation_def symmetrize_def 
strand_rel_def
by auto
then have 1:"strand_equivalence ?w (str_lcap,1,1) (str_rcap,0,1)" unfolding strand_equivalence_def
   relation_def symmetrize_def strand_rel_def by auto
have "relation_lcap_below ?w (str_lcap, 1, 1) (str_lcup, 1, 0)"  
   proof-
   have "(strand_array ?w)!1!1 = str_lcap" by auto
   moreover have "(strand_array ?w)!0!1 = str_lcup" by auto 
   moreover have "fst (str_lcap,1,1) = str_lcap" by auto
   moreover have "fst (str_lcup,1,0) = str_lcup" by auto 
   moreover have "snd (snd (str_lcup,1,0)) + (1::nat) = snd (snd (str_lcap,1,1)) " by auto
   moreover have "cup_count ?w (snd  (str_lcap,1,1)) = cap_count ?w (snd (str_lcup,1,0))"
      proof-
      have "cap_count ?w (snd (str_lcup,1,0)) = 0" unfolding cap_count_def cap_filter_def
      list_cap_filter_def by auto
      moreover have "cup_count ?w (snd  (str_lcap,1,1)) = 0"  unfolding cup_count_def cup_filter_def
      list_cup_filter_def by auto
      ultimately show ?thesis by auto
      qed
  ultimately show ?thesis unfolding relation_lcap_below_def by auto
  qed
then have 2:"strand_equivalence ?w (str_lcap, 1, 1) (str_lcup, 1, 0)" unfolding strand_equivalence_def
   relation_def symmetrize_def strand_rel_def by auto
have "relation_lcup_rcup ?w (str_lcup,1,0) (str_rcup,0,0) " 
  proof-
   have "(strand_array ?w)!0!1 = str_lcup" by auto
   moreover have "(strand_array ?w)!0!0 = str_rcup" by auto 
   moreover have "fst (str_lcup,1,0) = str_lcup" by auto
   moreover have "fst (str_rcup,0,0) = str_rcup" by auto 
   moreover have "fst (snd (str_rcup,0,0)) + (1::nat) = fst(snd (str_lcup,1,0))"  by auto
   moreover have "snd (snd (str_rcup,0,0)) = snd (snd (str_lcup,0,0))" by auto
   ultimately show ?thesis unfolding relation_lcup_rcup_def by auto
   qed

then have 3:"strand_equivalence ?w (str_lcup, 1, 0) (str_rcup, 0, 0)" unfolding strand_equivalence_def
   relation_def symmetrize_def strand_rel_def by auto   
then have 4:"strand_equivalence ?w (str_lcap, 1, 1) (str_rcup, 0, 0)" using strand_equivalence_def
2 rtranclp_trans by auto
then have 5:"strand_equivalence ?w (str_rcap, 0, 1) (str_rcup, 0, 0)" using strand_equivalence_def
1 rtranclp_trans symmetrize_def rel2  by auto
have 6: " strand_equivalence ?w (str_rcap, 0, 1) (str_lcup, 1 , 0)" using rel2 2 rtranclp_trans 
strand_equivalence_def by auto
have "orbit ?w  (str_rcup,0,0) = {(str_rcup,0,0),(str_lcup,1,0),(str_rcap,0,1),(str_lcap,1,1)}" 
 proof-
 have "{y. strand_equivalence ?w (str_rcup, 0, 0) y = True} =
    {(str_rcup, 0, 0), (str_lcup, 1, 0), (str_rcap, 0, 1), (str_lcap, 1, 1)}"
   proof-
   have  "(strand_equivalence ?w (str_rcup,0,0) (x,y,z) = True) \<longrightarrow> (y=0)\<or>(y=1)" 
    proof-
    assume "y>1"
    
*)

