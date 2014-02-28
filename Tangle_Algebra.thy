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
  
(*we defined the tensor of wall as described in the standard tangle algebra*)
fun tensor::"wall => wall => wall" (infixr "\<otimes>" 65)
where
1:"tensor (basic x) (basic y) = (basic (x \<otimes> y))"
|evss:"tensor (x*xs) (basic y) = (
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
definition tensor_Tangle ::"Tangle_Diagram \<Rightarrow> Tangle_Diagram \<Rightarrow> Tangle_Diagram" (infixl "\<otimes>" 65)
where
"tensor_Tangle x y = Abs_Tangle_Diagram ((Rep_Tangle_Diagram x) \<otimes> (Rep_Tangle_Diagram y))" 

(*some lemmas*)
lemma "tensor (basic (cement vert)) (basic (cement vert)) = (basic ((cement vert) \<otimes> (cement vert)))"
by simp

(*domain_wall of a tensor product of two walls is the sum of the domain_wall of each of the tensor
 products*)
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

(*the following theorem tells us that given a tensor product of a tangle diagram with a vertical
   strand, it gives a tangle diagram*)
theorem is_tangle_make_vert_right:
 "(is_tangle_diagram xs) \<Longrightarrow> is_tangle_diagram (xs \<otimes> (basic (make_vert_block n)))"
proof(induct xs)
 case (basic xs)
  show ?case using tensor_def by auto
 next
 case (prod x xs)
  have ?case 
   proof(cases n)
    case 0
     have 
        "codomain_block (x \<otimes> (make_vert_block 0)) 
               = (codomain_block x) + codomain_block(make_vert_block 0)"
            using  codomain_additive by auto
     moreover have "codomain_block (make_vert_block 0) = 0" 
            by auto
     ultimately have "codomain_block (x \<otimes> (make_vert_block 0)) = codomain_block (x)"
            by auto
     moreover have "is_tangle_diagram xs" 
          using prod.prems by (metis is_tangle_diagram.simps(2))
     then have "is_tangle_diagram ((x \<otimes> (make_vert_block 0))*xs)" 
          using is_tangle_diagram.simps(2) by (metis calculation prod.prems)
     then  have "is_tangle_diagram ((x*xs) \<otimes> (basic (make_vert_block 0)))" 
          by auto
     then show ?thesis using  "0" by (metis)
    next
    case (Suc k)
     have "codomain_block (make_vert_block (k+1)) = int (k+1)" 
         using codomain_make_vert  by auto
     then have "(nat (codomain_block (make_vert_block (k+1)))) = k+1" 
         by auto
     then have "make_vert_block (nat (codomain_block (make_vert_block (k+1)))) 
                             = make_vert_block (k+1)"
          by auto
     moreover have "codomain_wall (basic (make_vert_block (k+1)))>0" 
       using make_vert_block.simps codomain_wall.simps  Suc_eq_plus1 
       codomain_make_vert of_nat_0_less_iff zero_less_Suc
       by metis
     ultimately have 1: "(x*xs) \<otimes> (basic (make_vert_block (k+1))) 
             =  (x\<otimes>(make_vert_block (k+1)))*(xs\<otimes>(basic (make_vert_block (k+1))))" 
        using tensor.simps(2)  by (metis codomain_wall.simps(1) int_0 of_nat_less_0_iff)
     have "domain_wall (xs\<otimes>(basic (make_vert_block (k+1)))) 
                 = domain_wall xs + domain_wall (basic (make_vert_block (k+1)))"
            using tensor_domain_wall_additivity by auto
     then have 2: 
          "domain_wall (xs\<otimes>(basic (make_vert_block (k+1)))) 
                  = (domain_wall xs) + int (k+1)"
             using domain_make_vert domain_wall.simps(1) by auto 
     moreover have 3: "codomain_block (x \<otimes> (make_vert_block (k+1))) 
                 = codomain_block x + int (k+1)"
             using  codomain_additive codomain_make_vert by (metis)
     have "is_tangle_diagram (x*xs)"
            using prod.prems by auto
     then have 4:"codomain_block x = domain_wall xs"
            using is_tangle_diagram.simps(2) by metis
     from 2 3 4 have 
       "domain_wall (xs\<otimes>(basic (make_vert_block (k+1)))) 
               = codomain_block (x \<otimes> (make_vert_block (k+1))) "
            by auto
     moreover have "is_tangle_diagram (xs\<otimes>(basic (make_vert_block (k+1))))"
            using prod.hyps prod.prems by (metis Suc Suc_eq_plus1 is_tangle_diagram.simps(2))
     ultimately have "is_tangle_diagram ((x*xs) \<otimes> (basic (make_vert_block (k+1))))"
                using 1 by auto
      then show ?thesis using  Suc Suc_eq_plus1 by metis
    qed
   then show ?case by auto
 qed

(*the following theorem tells us that given a tensor product of a vertical strand block with a 
tangle diagram, it gives a tangle diagram. If the above result can be treated as right product, 
this can be treated as the left product*)

theorem is_tangle_make_vert_left:
 "(is_tangle_diagram xs) \<Longrightarrow> is_tangle_diagram ((basic (make_vert_block n)) \<otimes> xs)"
proof(induct xs)
 case (basic xs)
  show ?case using tensor_def by auto
 next
 case (prod x xs)
  have ?case 
   proof(cases n)
    case 0
     have 
        "codomain_block ( (make_vert_block 0) \<otimes> x) 
               = (codomain_block x) + codomain_block(make_vert_block 0)"
            using  codomain_additive by auto
     moreover have "codomain_block (make_vert_block 0) = 0" 
            by auto
     ultimately have "codomain_block ( (make_vert_block 0) \<otimes> x) = codomain_block (x)"
            by auto
     moreover have "is_tangle_diagram xs" 
          using prod.prems by (metis is_tangle_diagram.simps(2))
     then have "is_tangle_diagram (( (make_vert_block 0) \<otimes> x)*xs)" 
          using is_tangle_diagram.simps(2) by (metis calculation prod.prems)
     then  have "is_tangle_diagram ((basic (make_vert_block 0)) \<otimes> (x*xs) )" 
          by auto
     then show ?thesis using  "0" by (metis)
    next
    case (Suc k)
     have "codomain_block (make_vert_block (k+1)) = int (k+1)" 
         using codomain_make_vert  by auto
     then have "(nat (codomain_block (make_vert_block (k+1)))) = k+1" 
         by auto
     then have "make_vert_block (nat (codomain_block (make_vert_block (k+1)))) 
                             = make_vert_block (k+1)"
          by auto
     moreover have "codomain_wall (basic (make_vert_block (k+1)))>0" 
       using make_vert_block.simps codomain_wall.simps  Suc_eq_plus1 
       codomain_make_vert of_nat_0_less_iff zero_less_Suc
       by metis
     ultimately have 1: "  (basic (make_vert_block (k+1))) \<otimes> (x*xs)
             =  ((make_vert_block (k+1)) \<otimes> x)*((basic (make_vert_block (k+1))) \<otimes> xs)" 
        using tensor.simps(3)  by (metis codomain_wall.simps(1) int_0 of_nat_less_0_iff)
     have "domain_wall ((basic (make_vert_block (k+1))) \<otimes> xs) 
                 = domain_wall xs + domain_wall (basic (make_vert_block (k+1)))"
            using tensor_domain_wall_additivity by auto
     then have 2: 
          "domain_wall ((basic (make_vert_block (k+1))) \<otimes> xs) 
                  = (domain_wall xs) + int (k+1)"
             using domain_make_vert domain_wall.simps(1) by auto 
     moreover have 3: "codomain_block ( (make_vert_block (k+1)) \<otimes> x) 
                 = codomain_block x + int (k+1)"
             using  codomain_additive codomain_make_vert
              comm_semiring_1_class.normalizing_semiring_rules(24) 
             by metis
     have "is_tangle_diagram (x*xs)"
            using prod.prems by auto
     then have 4:"codomain_block x = domain_wall xs"
            using is_tangle_diagram.simps(2) by metis
     from 2 3 4 have 
       "domain_wall ((basic (make_vert_block (k+1))) \<otimes> xs) 
               = codomain_block ((make_vert_block (k+1)) \<otimes> x)"
             by auto
     moreover have "is_tangle_diagram ((basic (make_vert_block (k+1))) \<otimes> xs)"
            using prod.hyps prod.prems by (metis Suc Suc_eq_plus1 is_tangle_diagram.simps(2))
     ultimately have "is_tangle_diagram ((basic (make_vert_block (k+1))) \<otimes> (x*xs))"
                using 1 by auto
      then show ?thesis using  Suc Suc_eq_plus1 by metis
    qed
   then show ?case by auto
 qed
(*
(*tensor product of two tangle diagrams is a tangle diagram*)
theorem is_tangle_diagramness:
 shows"(is_tangle_diagram x)\<and>(is_tangle_diagram y)\<longrightarrow>is_tangle_diagram (tensor x y)"
 proof(induct_tac x y  rule:tensor.induct)
 fix z w
 let ?case = "(is_tangle_diagram (basic z))\<and>(is_tangle_diagram (basic w))
                  \<longrightarrow>is_tangle_diagram ((basic z) \<otimes> (basic w))"
  show ?case by auto
 next
 fix z zs w 
   assume a: "codomain_block w \<noteq> 0 "
   assume b: "(is_tangle_diagram zs)
               \<and>(is_tangle_diagram (basic (make_vert_block (nat (codomain_block w))))) 
    \<longrightarrow> is_tangle_diagram (zs \<otimes> basic (make_vert_block (nat (codomain_block w))))"
   let ?case = 
 "is_tangle_diagram (z * zs) \<and> is_tangle_diagram (basic w) \<longrightarrow> is_tangle_diagram (z * zs \<otimes> basic w)"
  have "is_tangle_diagram (z * zs) \<and> is_tangle_diagram (basic w) \<longrightarrow>
               is_tangle_diagram ((z*zs) \<otimes> (basic w))"
  proof-
  have " is_tangle_diagram (z * zs) \<and> is_tangle_diagram (basic w) \<longrightarrow> is_tangle_diagram zs"
        by (metis is_tangle_diagram.simps(2))
  moreover have "(is_tangle_diagram (basic (make_vert_block (nat (codomain_block w))))) "
              using is_tangle_diagram.simps(1) by auto
  ultimately have "is_tangle_diagram (z * zs) \<and> is_tangle_diagram (basic w) \<longrightarrow>
                is_tangle_diagram (zs \<otimes> basic (make_vert_block (nat (codomain_block w))))"
         using b by auto
  moreover have 1:"codomain_block w = domain_wall (basic (make_vert_block (nat (codomain_block w))))"
        using codomain_block_nonnegative domain_make_vert domain_wall.simps(1) int_nat_eq by auto
  moreover have 2:"is_tangle_diagram (z * zs) \<and> is_tangle_diagram (basic w) \<longrightarrow>
                 codomain_block z = domain_wall zs"
       using is_tangle_diagram.simps(2) by metis
 moreover have "codomain_block (z \<otimes> w) = codomain_block z +codomain_block w"
       using codomain_additive by auto
 moreover have "domain_wall (zs \<otimes> (basic (make_vert_block (nat (codomain_block w)))))
                 = domain_wall zs + domain_wall (basic (make_vert_block (nat (codomain_block w))))"
          using tensor_domain_wall_additivity by auto
 moreover then have " is_tangle_diagram (z * zs) \<and> is_tangle_diagram (basic w) \<longrightarrow>
          domain_wall (zs \<otimes> (basic (make_vert_block (nat (codomain_block w)))))
                   = codomain_block (z \<otimes> w)"
             by (metis "1" "2" calculation(4))
 ultimately have 
        "is_tangle_diagram (z * zs) \<and> is_tangle_diagram (basic w) \<longrightarrow>
         is_tangle_diagram ((z \<otimes> w)* (zs \<otimes> (basic (make_vert_block (nat (codomain_block w))))))"
          using is_tangle_diagram.simps(2)  by auto
 then have "is_tangle_diagram (z * zs) \<and> is_tangle_diagram (basic w) \<longrightarrow>
               is_tangle_diagram ((z*zs) \<otimes> (basic w))"
               using a by auto
 then show ?thesis by auto
 qed
 then have ?case by auto
 then have " (codomain_block w \<noteq> 0 \<Longrightarrow>
        is_tangle_diagram zs \<and> is_tangle_diagram (basic (make_vert_block (nat (codomain_block w)))) \<longrightarrow>
        is_tangle_diagram (zs \<otimes> basic (make_vert_block (nat (codomain_block w))))) \<Longrightarrow>
       is_tangle_diagram (z * zs) \<and> is_tangle_diagram (basic w) \<longrightarrow> is_tangle_diagram (z * zs \<otimes> basic w)"
        by auto
 *)
  

(*
proof(cases x)
case (basic z)
 have "(is_tangle_diagram (basic z))\<and>(is_tangle_diagram y)\<Longrightarrow>is_tangle_diagram ((basic z) \<otimes> y)"
  proof(cases y)
  case (basic w)
    show ?thesis using basic by auto
  next
  case (prod w ws)
    have "(is_tangle_diagram (basic z))\<and>(is_tangle_diagram (w*ws))
                \<Longrightarrow>is_tangle_diagram ((basic z)\<otimes>(w*ws))"
        proof-
        assume A: "(is_tangle_diagram (basic z))\<and>(is_tangle_diagram (w*ws))"
        have 1:"codomain_block w = domain_wall ws"
                  using A by (metis is_tangle_diagram.simps(2))
        have "(codomain_block z) = 0 \<Longrightarrow> (basic z)\<otimes>(w*ws) = (z \<otimes> w)*ws"
             using tensor.simps by auto
        moreover have "(codomain_block z) = 0 \<Longrightarrow> codomain_block (z \<otimes> w) = codomain_block w"
                      using codomain_additive by auto
        moreover have 2:"domain_wall ws = codomain_block w"
                       using A is_tangle_diagram.simps(2) by metis
        moreover have 3: "is_tangle_diagram ws" 
                      using  A is_tangle_diagram.simps(2) by metis
        ultimately have 4: "(codomain_block z) = 0 \<Longrightarrow> is_tangle_diagram ((basic z)\<otimes>(w*ws))"
                     by auto
*)        
 
        
      

(*
  fix x y                 
  let ?case = "is_tangle_diagram (basic x \<otimes> basic y)"
    show ?case by auto 
 next 
  fix x y xs
  assume A:"codomain_block y \<noteq> 0"
  assume B:"is_tangle_diagram (xs \<otimes>  basic (make_vert_block (nat (codomain_block y))))"
  assume C: "(is_tangle_diagram (x*xs))\<and>(is_tangle_diagram (basic y)) "
  let ?case = "is_tangle_diagram ((x * xs) \<otimes> basic y)"
   have 1:"(x*xs) \<otimes> (basic y) =  (x \<otimes> y)*(xs\<otimes>(basic (make_vert_block (nat (codomain_block y)))))"
    using tensor.simps(2) A by auto
   have "codomain_block (x \<otimes> y) = codomain_block x + codomain_block y"
        using codomain_additive by auto
   moreover have "domain_wall (xs\<otimes>(basic (make_vert_block (nat (codomain_block y)))))
                = domain_wall xs + domain_wall (basic (make_vert_block (nat (codomain_block y))))"
         using tensor_domain_wall_additivity by auto
  moreover have "domain_wall (basic (make_vert_block (nat (codomain_block y))))
                         = codomain_block y"
             using codomain_block_nonnegative domain_make_vert domain_wall.simps(1) int_nat_eq 
             by auto
   moreover have "is_tangle_diagram (x*xs) \<Longrightarrow> domain_wall xs = codomain_block x"
           using  is_tangle_diagram.simps(2) by metis
   ultimately have "is_tangle_diagram (x*xs) 
                        \<Longrightarrow> (domain_wall (xs\<otimes>(basic (make_vert_block (nat (codomain_block y)))))
                               = codomain_block (x \<otimes> y))"   
                   by auto
   then have "is_tangle_diagram (x*xs) 
                        \<Longrightarrow> is_tangle_diagram ((x*xs) \<otimes> (basic y))" 
                  by (metis "1" is_tangle_diagram.simps(2) is_tangle_make_vert_right)
   then have "is_tangle_diagram ((x*xs) \<otimes> (basic y))" 
               using C by auto
   
*)        
end
