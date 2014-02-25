theory etc
imports Links
begin

text{*swing begins*}

abbreviation r_over_braid::"walls"
where
"r_over_braid  \<equiv>  ((basic ((cement over)\<otimes>(cement vert))\<circ>(basic ((cement vert)\<otimes>(cement over)))
                 \<circ>(basic ((cement over)\<otimes>(cement vert)))))"



abbreviation l_over_braid::"walls"
where
"l_over_braid  \<equiv>   (basic ((cement vert)\<otimes>(cement over))\<circ>(basic ((cement over)\<otimes>(cement vert)))
                    \<circ>(basic ((cement vert)\<otimes>(cement over))))"


abbreviation r_under_braid::"walls"
where
"r_under_braid  \<equiv>  ((basic ((cement under)\<otimes>(cement vert))\<circ>(basic ((cement vert)\<otimes>(cement under)))
                 \<circ>(basic ((cement under)\<otimes>(cement vert)))))"

abbreviation l_under_braid::"walls"
where
"l_under_braid  \<equiv>   (basic ((cement vert)\<otimes>(cement under))\<circ>(basic ((cement under)\<otimes>(cement vert)))
                    \<circ>(basic ((cement vert)\<otimes>(cement under))))"

definition swing_pos::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"swing_pos x y \<equiv> (x = r_over_braid)\<and>(y = l_over_braid)"

definition swing_neg::"walls \<Rightarrow> walls \<Rightarrow> bool"
where
"swing_neg x y \<equiv>(x = r_under_braid)\<and>(y=l_under_braid)"

definition swing::relation
where
"swing x y \<equiv> (swing_pos x y)\<or>(swing_neg x y)"

text{*swing definition*}
type_synonym relation = "walls \<Rightarrow> walls \<Rightarrow> bool" 

abbreviation right_over::"walls"
where
"right_over \<equiv> ((basic ((cement vert)\<otimes>(cement cup))) \<circ> (basic ((cement over)\<otimes>(cement vert)))
\<circ> (basic ((cement vert)\<otimes> (cement cap))))"

abbreviation left_over::"walls"
where
" left_over \<equiv> ((basic ((cement cup)\<otimes>(cement vert))) \<circ> (basic ((cement vert)\<otimes>(cement over)))
\<circ> (basic ((cement cap)\<otimes> (cement vert))))"

abbreviation right_under::"walls"
where
"right_under \<equiv>  ((basic ((cement vert)\<otimes>(cement cup))) \<circ> (basic ((cement under)\<otimes>(cement vert)))
\<circ> (basic ((cement vert)\<otimes> (cement cap))))"

abbreviation left_under::"walls"
where
"left_under \<equiv>  ((basic ((cement cup)\<otimes>(cement vert))) \<circ> (basic ((cement vert)\<otimes>(cement under)))
\<circ> (basic ((cement cap)\<otimes> (cement vert))))"

abbreviation straight_line::"walls"
where
"straight_line \<equiv> (basic (cement vert)) \<circ> (basic (cement vert)) \<circ> (basic (cement vert))"

definition positive_flip::relation
where
"positive_flip x y \<equiv> ((x = right_over)\<and>(y =  left_over))"

definition positive_straighten::relation
where
"positive_straighten x y \<equiv> ((x = right_over)\<and>(y = straight_line))"

definition negative_flip::relation
where
"negative_flip x y \<equiv> ((x = right_under)\<and>(y =  left_under))"


definition negative_straighten::relation
where
"negative_straighten x y \<equiv> ((x = right_over)\<and>(y = straight_line))"
