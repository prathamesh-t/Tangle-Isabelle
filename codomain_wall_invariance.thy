theory codomain_wall_invariance
imports Link_Algebra 
begin

theorem linkrel_codomain_invariance: " linkrel a b \<Longrightarrow> codomain_wall a = codomain_wall b"
proof-
assume 0: "linkrel a b"
have 1:"uncross a b \<Longrightarrow> codomain_wall a = codomain_wall b" 
 proof-
  assume 1:"uncross a b"
  have " codomain_wall right_over = codomain_wall straight_line" by auto 
  then
   have "uncross_positive_straighten a b \<Longrightarrow> codomain_wall a = codomain_wall b" 
   unfolding uncross_positive_straighten_def by metis 
  moreover have "codomain_wall right_over = codomain_wall left_over" using codomain_wall.simps by auto
  then have "uncross_positive_flip a b \<Longrightarrow> codomain_wall a = codomain_wall b"
   unfolding uncross_positive_flip_def by auto
  moreover have "uncross_negative_straighten a b \<Longrightarrow> codomain_wall a = codomain_wall b" 
   unfolding uncross_negative_straighten_def by auto
  moreover have "uncross_negative_flip a b \<Longrightarrow> codomain_wall a = codomain_wall b"
   unfolding uncross_negative_flip_def by auto
  ultimately have "uncross a b \<Longrightarrow> codomain_wall a = codomain_wall b"
  unfolding uncross_def by auto
  then show ?thesis using 1 by auto
  qed
have 2:"pull a b \<Longrightarrow> codomain_wall a = codomain_wall b"
proof- 
 assume 1:"pull a b"
 have "pull_negpos a b \<Longrightarrow> codomain_wall a = codomain_wall b"
  using pull_negpos_def by auto 
 moreover have "pull_posneg a b \<Longrightarrow> codomain_wall a = codomain_wall b"
 using pull_posneg_def by auto
 ultimately show ?thesis  using 1 pull_def by auto
 qed
have 3:"straighten a b \<Longrightarrow> codomain_wall a = codomain_wall b"
  using straighten_def straighten_topdown_def straighten_downtop_def codomain_wall.simps
          by (metis codomain.simps(3) codomain_block.simps(2) comm_monoid_add_class.add.left_neutral compose_Nil)
have 4:"rotate a b \<Longrightarrow> codomain_wall a = codomain_wall b"
proof-
assume 1:"rotate a b"
 have "rotate_toppos a b \<Longrightarrow> codomain_wall a = codomain_wall b"
  using rotate_toppos_def codomain.simps
  by auto
 moreover have "rotate_topneg a b \<Longrightarrow> codomain_wall a = codomain_wall b"
  using rotate_topneg_def codomain.simps
  by auto
  moreover have "rotate_downneg a b \<Longrightarrow> codomain_wall a = codomain_wall b"
  using rotate_downneg_def codomain.simps
  by auto
  moreover have "rotate_downpos a b \<Longrightarrow> codomain_wall a = codomain_wall b"
  using rotate_downpos_def codomain.simps
  by auto
  ultimately show ?thesis using 1 rotate_def by auto
 qed
have 5:"swing a b \<Longrightarrow> codomain_wall a = codomain_wall b"
 using swing_def swing_pos_def swing_neg_def codomain_wall.simps 
     proof-
       assume 0: "swing a b"
       have "swing_pos a b \<Longrightarrow> codomain_wall a = codomain_wall b"
              using swing_pos_def codomain_wall.simps    by auto
       moreover have "swing_neg a b \<Longrightarrow> codomain_wall a = codomain_wall b"
              using swing_neg_def codomain_wall.simps    by auto
       ultimately have "swing_pos a b \<or> swing_neg a b \<Longrightarrow> codomain_wall a = codomain_wall b"
                       by auto
       then show ?thesis  using swing_def 0 by auto 
     qed
have 6:"compress a b \<Longrightarrow> codomain_wall a = codomain_wall b"
 proof-
  assume 1: "compress a b"
  have "compress_top a b \<Longrightarrow> codomain_wall a = codomain_wall b"
     using compress_top_def codomain_wall_def codomain_block.simps(1) codomain_wall.simps(1) 
     codomain_wall_compose by (metis ) 
  moreover have "compress_bottom a b \<Longrightarrow> codomain_wall a = codomain_wall b"
     using compress_bottom_def codomain_wall.simps 
     proof-
     assume 1: "compress_bottom a b"
     have " \<exists>B. ((a = B \<circ> basic (make_vert_block (nat (codomain_wall B)))) \<and>
               (b = basic [] \<circ> B) \<and> domain_wall B = 0)"
                 using compress_bottom_def 1 by auto
     then obtain B where " ((a = B \<circ> basic (make_vert_block (nat (codomain_wall B)))) \<and>
               (b = basic [] \<circ> B) \<and> domain_wall B = 0)"
                 by auto
     have "codomain_block (make_vert_block (nat (codomain_wall B))) = codomain_wall B"
          proof-
           have "codomain_block (make_vert_block n)
                         = int n"
                       using codomain_block_def make_vert_block_def codomain_make_vert  by (metis )
           moreover have "(codomain_wall B \<ge> 0)"
                        apply(induct_tac B) 
                        apply(auto)
                        using codomain_block_nonnegative by (metis )
           moreover then have "int (nat (codomain_wall B)) = codomain_wall B"
                      by auto
           ultimately show ?thesis by (metis codomain_make_vert)       
          qed 
    then have " codomain_wall (B \<circ>basic (make_vert_block (nat (codomain_wall B)))) 
                    = codomain_wall ((basic []) \<circ>B)"
                    using codomain_wall.simps codomain_wall_compose make_vert_block.simps(1) nat_0 
                      by (metis)  
    then have "codomain_wall a = codomain_wall b"
            using exI by (metis `a = B \<circ> basic (make_vert_block (nat (codomain_wall B))) \<and> b = basic [] \<circ> B \<and> domain_wall B = 0`)
     then show ?thesis using 1 by auto
    qed
  ultimately show ?thesis using 1 compress_def by auto
 qed
have 7:"slide a b \<Longrightarrow> codomain_wall a = codomain_wall b"
 using slide_def
   proof-
   assume 1: "slide a b"
   have "codomain_block (make_vert_block (nat (codomain_wall B))) = codomain_wall B"
         proof-
          have "codomain_block (make_vert_block n)
                         = int n"
                       using codomain_block_def make_vert_block_def codomain_make_vert  by (metis )
          moreover have "(codomain_wall B \<ge> 0)"
                        apply(induct_tac B) 
                        apply(auto)
                        using codomain_block_nonnegative by (metis )
          moreover then have "int (nat (codomain_wall B)) = codomain_wall B"
                      by auto
          ultimately show ?thesis by (metis codomain_make_vert)       
        qed    
   then have "
  (\<exists>B. (x = basic (make_vert_block (nat (codomain_block B))) \<circ> basic B \<and>
       y = basic B \<circ> basic (make_vert_block (nat (codomain_block B)))) \<and>
      codomain_block B \<noteq> 0) \<Longrightarrow> (codomain_wall x = codomain_wall y)"
       using exI codomain_wall.simps by (metis codomain_block_nonnegative codomain_make_vert codomain_wall_compose int_nat_eq)
  then have "slide a b \<Longrightarrow> codomain_wall a  = codomain_wall b"
          unfolding slide_def by (metis codomain_block_nonnegative codomain_make_vert codomain_wall.simps(1) codomain_wall_compose int_nat_eq)
  then show ?thesis using 1 by auto 
 qed
 then have "linkrel a b \<Longrightarrow> codomain_wall a = codomain_wall b"
            using 1 2 3 4 5 6 7 linkrel_def by auto
 then show ?thesis using 0 by auto
qed

theorem "x ~ y \<Longrightarrow> codomain_wall x = codomain_wall y"
proof(induction rule:Tangle_Equivalence.induct)
 case refl
     show ?case by simp
 next
 case codomain_compose   
      show ?case using codomain_compose by (metis codomain_block.simps(1) codomain_wall.simps(1) codomain_wall_compose)
 next
 case domain_compose
      show ?case using codomain_wall.simps  codomain_wall_compose by auto 
 next
 case compose_eq
      show ?case  using codomain_wall_compose compose_eq.IH by auto
 next
 case sym
      show ?case using sym.IH by auto
 next
 case trans
      show ?case using trans.IH by auto
 next
 case tensor_eq
     show ?case using tensor_codomain_wall_additivity tensor_eq.IH by auto 
 next 
 case equality
     show ?case using linkrel_codomain_invariance equality.hyps by auto
 
 qed

end
