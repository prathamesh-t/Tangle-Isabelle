theory Tangle_Algebra
imports Tangles
begin

(*the following definition enables construction of a block*)
primrec make_vert_block:: "nat \<Rightarrow> block"
where
"make_vert_block 0 = cement empty"
|"make_vert_block (Suc n) = vert#(make_vert_block n)"


lemma domain_make_vert:"domain_block (make_vert_block n) = int n"
   apply(induct_tac n)
   apply(auto)
   done

lemma codomain_make_vert:"codomain_block (make_vert_block n) = int n"
   apply(induct_tac n)
   apply(auto)
   done
  
(*we defined the tensor of walls as described in the standard tangle algebra*)
fun tensor::"walls => walls => walls" (infixr "\<otimes>" 65)
where
1:"tensor (basic x) (basic y) = (basic (x \<otimes> y))"
|2:"tensor (x*xs) (basic y) = (
                  if (codomain_block y = 0)
                    then (x \<otimes> y)*xs 
                    else (x \<otimes> y)*(xs\<otimes>(basic (make_vert_block (nat (codomain_block y)))))
                              )"
|3:"tensor (basic x) (y*ys) = (
                  if (codomain_block x = 0) 
                     then (x \<otimes> y)*ys 
                     else (x \<otimes> y)*((basic (make_vert_block (nat (codomain_block x))))\<otimes> ys)
                              )"
|4:"tensor (x*xs) (y*ys) = (x \<otimes> y)* (xs \<otimes> ys)"

(*extending the definition of tensors to diagrams*)
definition tensor_Tangle ::"Tangle \<Rightarrow> Tangle \<Rightarrow> Tangle" (infixl "\<otimes>" 65)
where
"tensor_Tangle x y = Abs_Tangle ((Rep_Tangle x) \<otimes> (Rep_Tangle y))" 

(*some lemmas*)
lemma "tensor (basic (cement vert)) (basic (cement vert)) = (basic ((cement vert) \<otimes> (cement vert)))"
by simp

lemma tensor_domain_wall_additivity:
 "domain_wall (xs \<otimes> ys) = domain_wall xs + domain_wall ys"
 proof(cases xs)
 fix x
 assume A:"xs = basic x"
 then have "domain_wall (xs \<otimes> ys) = domain_wall xs + domain_wall ys"
   proof(cases ys)
   fix y
   assume B:"ys = basic y"
     have "domain_block (x \<otimes> y) = domain_block x + domain_block y"
       using domain_additive by auto
     then have "domain_wall (xs \<otimes> ys) = domain_wall xs + domain_wall ys"
       using tensor.simps(1) A B by auto
     thus ?thesis by auto
  next
  fix z zs 
  assume C:"ys = (z*zs)"
    have "domain_wall (xs \<otimes> ys) = domain_wall xs + domain_wall ys"
     proof(case_tac "(codomain_block x) = 0")  
      assume "codomain_block x = 0"
       then have "(xs \<otimes> ys) = (x \<otimes> z)*zs" 
          using A C tensor.simps(4) by auto
       then have "domain_wall (xs \<otimes> ys) = domain_block (x \<otimes> z)" 
          by auto
       moreover have "domain_wall ys = domain_block z"
          unfolding domain_wall_def C by auto
       moreover have "domain_wall xs = domain_block x"
          unfolding domain_wall_def A by auto
       moreover have "domain_block (x \<otimes> z) = domain_block x + domain_block z" 
          using domain_additive by auto
       ultimately show ?thesis by auto
     next
     assume "codomain_block x \<noteq> 0"
     have "(xs \<otimes> ys) = (x \<otimes> z)*((basic (make_vert_block (nat (codomain_block x))))\<otimes> zs)"
          using tensor.simps(3) A C `codomain_block x \<noteq> 0`  by auto
     then have "domain_wall (xs \<otimes> ys) = domain_block (x \<otimes> z)"
          by auto   
        moreover have "domain_wall ys = domain_block z"
          unfolding domain_wall_def C by auto
       moreover have "domain_wall xs = domain_block x"
          unfolding domain_wall_def A by auto
       moreover have "domain_block (x \<otimes> z) = domain_block x + domain_block z" 
          using domain_additive by auto
       ultimately show ?thesis by auto
      qed
      then show ?thesis by auto
   qed
 then show ?thesis by auto
 next
 fix z zs
 assume D:"xs = z * zs"
 then have "domain_wall (xs \<otimes> ys) = domain_wall xs + domain_wall ys"
    proof(cases ys)
     fix y
     assume E:"ys = basic y"
     then have "domain_wall (xs \<otimes> ys) = domain_wall xs + domain_wall ys"
         proof(cases "codomain_block y = 0")
         assume "codomain_block y = 0"
         have "(xs \<otimes> ys) = (z \<otimes> y)*zs"  
            using tensor.simps(2)  D E `codomain_block y = 0` by auto 
       then have "domain_wall (xs \<otimes> ys) = domain_block (z \<otimes> y)" 
          by auto
       moreover have "domain_wall xs = domain_block z"
          unfolding domain_wall_def D by auto
       moreover have "domain_wall ys = domain_block y"
          unfolding domain_wall_def E by auto
       moreover have "domain_block (z \<otimes> y) = domain_block z + domain_block y" 
          using domain_additive by auto
       ultimately show ?thesis by auto
     next
     assume "codomain_block y \<noteq> 0"
     have "(xs \<otimes> ys) = (z \<otimes> y)*(zs\<otimes>(basic (make_vert_block (nat (codomain_block y)))))"
          using tensor.simps(3) D E `codomain_block y \<noteq> 0`  by auto
     then have "domain_wall (xs \<otimes> ys) = domain_block (z \<otimes> y)"
          by auto   
        moreover have "domain_wall ys = domain_block y"
          unfolding domain_wall_def E by auto
       moreover have "domain_wall xs = domain_block z"
          unfolding domain_wall_def D by auto
       moreover have "domain_block (z \<otimes> y) = domain_block z + domain_block y" 
          using domain_additive by auto
       ultimately show ?thesis by auto
      qed
      then show ?thesis by auto
     next
     fix w ws
     assume F:"ys = w*ws"  
     have "(xs \<otimes> ys) = (z \<otimes> w) * (zs \<otimes> ws)" 
          using D F by auto
     then have "domain_wall (xs \<otimes> ys) = domain_block (z \<otimes> w)" 
          by auto 
     moreover have "domain_wall ys = domain_block w"
          unfolding domain_wall_def F by auto
    moreover have "domain_wall xs = domain_block z"
          unfolding domain_wall_def D by auto
    moreover have "domain_block (z \<otimes> w) = domain_block z + domain_block w" 
          using domain_additive by auto
    ultimately show ?thesis by auto
    qed
    then show ?thesis by auto
  qed


(*
theorem well_definedness:
 assumes "well_defined_tangle x" 
    and "well_defined_tangle y" 
 shows"well_defined_tangle (tensor x y)"
proof(induct_tac x y rule: tensor.induct)
 fix x y                 
 let ?case = " well_defined_tangle (basic x \<otimes> basic y)"
    have "domain_codomain_list (basic x \<otimes> basic y) = []" 
        by auto
    from this have "list_sum (domain_codomain_list (basic x \<otimes> basic y)) = 0" 
       by auto   
    from this show ?case unfolding well_defined_tangle_def by auto
 next
 fix x y xs
 assume A:"codomain_block y \<noteq> 0"
 assume B:"well_defined_tangle (xs \<otimes> basic (make_vert_block (nat (codomain_block y - 1))))"
 assume C:"well_defined_tangle (x*xs)" 
 let ?case = "well_defined_tangle (x * xs \<otimes> basic y)"
   have 1:"(x*xs) \<otimes> (basic y) =  (x \<otimes> y)*(xs\<otimes>(basic (make_vert_block (nat (codomain_block y- 1)))))"
    using tensor.simps(2) A by auto
  moreover have "list_sum (domain_codomain_list (x*xs)) = 0" 
    using well_defined_tangle_def C by auto
  moreover then have "codomain_block x = domain_wall xs" 
    using well_defined_tangle_def C domain_codomain_list_def
              abs_zero_equality calculation(2) codomain_wall.simps(1) compose_Nil 
              diagram_wall_count_list_zero  
    by metis
 moreover have "domain_wall (xs \<otimes> (basic (make_vert_block (nat (codomain_block y- 1)))))
                  = domain_wall xs + domain_block  (make_vert_block (nat (codomain_block y- 1)))"
           using tensor.simps  domain_wall.simps(1) tensor_domain_wall_additivity by auto
 moreover have " domain_block  (make_vert_block (nat (codomain_block y- 1))) = 
                             codomain_block y" 
      using domain_make_vert int_def 
      by (metis A add_eq_if codomain_block_nonnegative 
          comm_semiring_1_class.normalizing_semiring_rules(24) 
         int_nat_eq nat_diff_distrib' of_nat_0 of_nat_Suc transfer_nat_int_numerals(2) zero_le_one)
 ultimately have "domain_wall (xs \<otimes> (basic (make_vert_block (nat (codomain_block y- 1)))))
                      = codomain_block x + codomain_block y"
               by auto
 then have 2:"domain_wall (xs \<otimes> (basic (make_vert_block (nat (codomain_block y- 1))))) 
                      = codomain_block (x \<otimes> y)"
       using  codomain_additive by (metis)
 moreover have "list_sum (domain_codomain_list (xs \<otimes> (basic (make_vert_block (nat (codomain_block y- 1)))))) 
              = 0"
            using well_defined_tangle_def B by auto
 moreover have "list_sum (domain_codomain_list ((x*xs) \<otimes> (basic y))) = 
list_sum (domain_codomain_list (xs \<otimes> (basic (make_vert_block (nat (codomain_block y- 1)))))) 
+ abs( domain_wall (xs \<otimes> (basic (make_vert_block (nat (codomain_block y- 1))))) - codomain_wall(basic (x \<otimes> y)))"
  using list_sum_def 2 
by (metis "1" codomain_wall.simps(1) comm_semiring_1_class.normalizing_semiring_rules(24) domain_codomain_list.simps(2) list_sum.simps(2))
 ultimately have "list_sum (domain_codomain_list ((x*xs) \<otimes> (basic y))) = 0"
           by (metis codomain_wall.simps(1) comm_monoid_add_class.add.left_neutral diff_self wall_count_list_list_sum_abs)
*)
end
