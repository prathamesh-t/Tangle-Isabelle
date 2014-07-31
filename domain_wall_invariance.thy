theory domain_wall_invariance
imports Link_Algebra
begin

theorem linkrel_domain_invariance: " linkrel a b \<Longrightarrow> domain_wall a = domain_wall b"
proof-
assume 0: "linkrel a b"
have 1:"uncross a b \<Longrightarrow> domain_wall a = domain_wall b" 
 proof-
  assume 1:"uncross a b"
  have " domain_wall right_over = domain_wall straight_line" by auto 
  then
   have "uncross_positive_straighten a b \<Longrightarrow> domain_wall a = domain_wall b" 
   unfolding uncross_positive_straighten_def by metis 
  moreover have "domain_wall right_over = domain_wall left_over" using domain_wall.simps by auto
  then have "uncross_positive_flip a b \<Longrightarrow> domain_wall a = domain_wall b"
   unfolding uncross_positive_flip_def by auto
  moreover have "uncross_negative_straighten a b \<Longrightarrow> domain_wall a = domain_wall b" 
   unfolding uncross_negative_straighten_def by auto
  moreover have "uncross_negative_flip a b \<Longrightarrow> domain_wall a = domain_wall b"
   unfolding uncross_negative_flip_def by auto
  ultimately have "uncross a b \<Longrightarrow> domain_wall a = domain_wall b"
  unfolding uncross_def by auto
  then show ?thesis using 1 by auto
  qed
have 2:"pull a b \<Longrightarrow> domain_wall a = domain_wall b"
proof- 
 assume 1:"pull a b"
 have "pull_negpos a b \<Longrightarrow> domain_wall a = domain_wall b"
  using pull_negpos_def by auto 
 moreover have "pull_posneg a b \<Longrightarrow> domain_wall a = domain_wall b"
 using pull_posneg_def by auto
 ultimately show ?thesis  using 1 pull_def by auto
 qed
have 3:"straighten a b \<Longrightarrow> domain_wall a = domain_wall b"
  using straighten_def straighten_topdown_def straighten_downtop_def domain_wall.simps by (metis comm_semiring_1_class.normalizing_semiring_rules(5) compose_Nil domain.simps(2) domain_block.simps(2))

have 4:"rotate a b \<Longrightarrow> domain_wall a = domain_wall b"
proof-
assume 1:"rotate a b"
 have "rotate_toppos a b \<Longrightarrow> domain_wall a = domain_wall b"
  using rotate_toppos_def domain.simps
  by auto
 moreover have "rotate_topneg a b \<Longrightarrow> domain_wall a = domain_wall b"
  using rotate_topneg_def domain.simps
  by auto
  moreover have "rotate_downneg a b \<Longrightarrow> domain_wall a = domain_wall b"
  using rotate_downneg_def domain.simps
  by auto
  moreover have "rotate_downpos a b \<Longrightarrow> domain_wall a = domain_wall b"
  using rotate_downpos_def domain.simps
  by auto
  ultimately show ?thesis using 1 rotate_def by auto
 qed
have 5:"swing a b \<Longrightarrow> domain_wall a = domain_wall b"
 using swing_def swing_pos_def swing_neg_def domain_wall.simps 
by (metis 
ab_semigroup_add_class.add_ac(1) codomain_wall.cases comm_semiring_1_class.normalizing_semiring_rules(22) 
comm_semiring_1_class.normalizing_semiring_rules(23) comm_semiring_1_class.normalizing_semiring_rules(24) 
comm_semiring_1_class.normalizing_semiring_rules(5) comm_semiring_1_class.normalizing_semiring_rules(6) 
compose_Nil domain_block.simps(1) domain_block.simps(2) wall.distinct(1) wall.size(1) wall.size(2) 
wall.size(3) wall.size(4))
have 6:"compress a b \<Longrightarrow> domain_wall a = domain_wall b"
 proof-
 assume 1: "compress a b"
 have "compress_top a b \<Longrightarrow> domain_wall a = domain_wall b"
 using compress_top_def
 proof-
  assume 1: "compress_top a b"
  have "domain_block (make_vert_block (nat (domain_wall B))) = domain_wall B"
     using make_vert_block_def domain_block.simps 
      by (metis (full_types) domain_block_nonnegative domain_make_vert domain_wall.simps(1) domain_wall.simps(2) int_nat_eq wall.exhaust)
  then have "domain_wall (basic (make_vert_block (nat (domain_wall B))::block) \<circ> B) 
                    = domain_wall (B \<circ> (basic []))"
          by (metis domain_wall.simps(1) domain_wall_compose)
  then have "(\<exists>B. (x = basic (make_vert_block (nat (domain_wall B))) \<circ> B) \<and> (y= B \<circ> basic [] \<and> codomain_wall B = 0))
            \<Longrightarrow> domain_wall x = domain_wall y"
            using exI by (metis (full_types) codomain_wall.cases compose_Nil compose_leftassociativity domain_block_nonnegative domain_make_vert domain_wall.simps(1) domain_wall_compose int_nat_eq wall.distinct(1) wall.exhaust wall.inject(2))
  then have  "(\<exists>B. (x = basic (make_vert_block (nat (domain_wall B))) \<circ> B) \<and> (y= B \<circ> basic [] \<and> codomain_wall B = 0)
         \<and> (codomain_wall B = 0)) \<Longrightarrow> domain_wall x = domain_wall y" 
              by auto
  then have "compress_top a b \<Longrightarrow> domain_wall a = domain_wall b"
       using compress_top_def exI
               by (metis codomain_wall.cases compose_Nil domain_block_nonnegative domain_make_vert domain_wall.simps(1) domain_wall_compose int_nat_eq)
  then show ?thesis using 1 by auto
  qed
 moreover have "compress_bottom a b \<Longrightarrow> domain_wall a = domain_wall b"
  using compress_bottom_def domain_wall.simps by (metis domain_block.simps(1) domain_wall_compose)
 ultimately show ?thesis using 1 compress_def by auto
 qed
have 7:"slide a b \<Longrightarrow> domain_wall a = domain_wall b"
 using slide_def
   proof-
   assume 1: "slide a b"
   have "domain_block (make_vert_block (nat (domain_wall B))) = domain_wall B"
        by (metis (full_types) domain_block_nonnegative domain_make_vert domain_wall.simps(1) 
         domain_wall.simps(2) int_nat_eq wall.exhaust)
   then have "
  (\<exists>B. (x = basic (make_vert_block (nat (domain_block B))) \<circ> basic B \<and>
       y = basic B \<circ> basic (make_vert_block (nat (codomain_block B)))) \<and>
      domain_block B \<noteq> 0) \<Longrightarrow> (domain_wall x = domain_wall y)"
       using exI domain_wall.simps by (metis domain_block_nonnegative domain_make_vert domain_wall_compose int_nat_eq)
  then have "slide a b \<Longrightarrow> domain_wall a  = domain_wall b"
          unfolding slide_def by (metis domain_block_nonnegative domain_make_vert domain_wall.simps(1) domain_wall_compose int_nat_eq)
  then show ?thesis using 1 by auto 
 qed
 then have "linkrel a b \<Longrightarrow> domain_wall a = domain_wall b"
            using 1 2 3 4 5 6 7 linkrel_def by auto
 then show ?thesis using 0 by auto
qed

theorem "x ~ y \<Longrightarrow> domain_wall x = domain_wall y"
proof(induction rule:Tangle_Equivalence.induct)
 case refl
     show ?case by simp
 next
 case equality
     show ?case using linkrel_domain_invariance equality.hyps by auto
 next
 case domain_compose   
      show ?case using domain_compose by auto
 next
 case codomain_compose
      show ?case using domain_wall.simps  domain_wall_compose by auto 
 next
 case compose_eq
      show ?case  using domain_wall_compose compose_eq.IH by auto
 next
 case sym
      show ?case using sym.IH by auto
 next
 case trans
      show ?case using trans.IH by auto
 next
 case tensor_eq
     show ?case using tensor_domain_wall_additivity tensor_eq.IH by auto 
 qed

end
