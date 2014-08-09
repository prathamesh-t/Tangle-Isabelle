theory Kauffman_Invariance
imports  Link_Algebra Linkrel_kauffman
begin

theorem kauffman_invariance:"(w1::wall) ~f w2 \<Longrightarrow> kauff_mat w1 = kauff_mat w2"
proof(induction rule:Framed_Tangle_Equivalence.induct)
case refl
  show ?case using refl by auto
next
case sym
 show ?case using sym by auto
next
case trans
 show ?case using trans by auto
  next
case compose_eq
  show ?case using compose_eq tangle_compose_matrix by auto
next
case codomain_compose
  show ?case using codomain_compose left_mat_compose by auto
next
case domain_compose
  show ?case using domain_compose right_mat_compose by auto
next
case tensor_eq
  show ?case using  tensor_eq.IH Tensor_Invariance by (metis)
next
case equality
  show ?case using framed_linkrel_inv equality by auto
qed

definition tangle_diagram_kauffman::"Tangle_Diagram \<Rightarrow> rat_poly mat"
where
"tangle_diagram_kauffman T \<equiv> kauff_mat (Rep_Tangle_Diagram T)"


lemma "rat_poly_times A B = 1"
      using inverse1  by (metis )

lemma "kauff_mat ([cup]*(basic [cap])) = [[-(A^2) - (B^2)]]"
       apply(simp add:mat_multI_def)
       apply(simp add:matT_vec_multI_def)
       apply(auto simp add:replicate_def rat_poly.row_length_def)
       apply(auto simp add:scalar_prod)
       by (metis comm_ring_1_class.normalizing_ring_rules(2) power2_eq_square)

lemma unlink_computation:
 "rat_poly_plus (rat_poly_times (rat_poly_times A A) (rat_poly_times A A))
     (rat_poly_plus
       (rat_poly_times 2 (rat_poly_times A (rat_poly_times A (rat_poly_times B B))))
       (rat_poly_times (rat_poly_times B B) (rat_poly_times B B))) =
             ((A^4)+(B^4)+2)"
  proof-
  have "(rat_poly_times (rat_poly_times A A) (rat_poly_times A A)) = A^4"
             by (metis comm_semiring_1_class.normalizing_semiring_rules(18) comm_semiring_1_class.normalizing_semiring_rules(31) numeral_times_numeral power2_eq_square semiring_norm(12) semiring_norm(13))
  moreover have "(rat_poly_times (rat_poly_times B B) (rat_poly_times B B))
             = B^4"
             by (metis comm_semiring_1_class.normalizing_semiring_rules(18) comm_semiring_1_class.normalizing_semiring_rules(31) numeral_times_numeral power2_eq_square semiring_norm(12) semiring_norm(13))
  moreover have "(rat_poly_times 2 (rat_poly_times A (rat_poly_times A (rat_poly_times B B))))
               = 2"
       using inverse1  by (metis mult_2_right one_add_one rat_poly.assoc rat_poly.comm)
   ultimately show ?thesis by auto
qed
lemma "kauff_mat ([cup,cup]*(basic [cap,cap]))= [[((A^4)+(B^4)) + 2]]"
       apply(simp add:mat_multI_def)
       apply(simp add:matT_vec_multI_def)
       apply(auto simp add:replicate_def rat_poly.row_length_def)
       apply(auto simp add:scalar_prod)
       apply(auto simp add:unlink_computation)
       done

definition trefoil_polynomial::"rat_poly"
where
"trefoil_polynomial \<equiv>
rat_poly_plus
     (rat_poly_times (rat_poly_times A A)
       (rat_poly_plus
         (rat_poly_times B
           (rat_poly_times B
             (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
               (rat_poly_times A A))))
         (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
           (rat_poly_plus (rat_poly_times B (rat_poly_times B (rat_poly_times A A)))
             (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
               (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
                 (rat_poly_times A A)))))))
     (rat_poly_plus
       (rat_poly_times 2
         (rat_poly_times A
           (rat_poly_times A
             (rat_poly_times A
               (rat_poly_times A (rat_poly_times A (rat_poly_times B B)))))))
       (rat_poly_times (rat_poly_times B B)
         (rat_poly_times B
           (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
             (rat_poly_times B (rat_poly_times B B))))))"

lemma trefoil:
"kauff_mat ([cup,cup]*[vert,over,vert]*[vert,over,vert]*[vert,over,vert]
              *(basic [cap,cap]))
          = [[trefoil_polynomial]]"
    apply(simp add:mat_multI_def)
    apply(simp add:matT_vec_multI_def)
    apply(auto simp add:replicate_def rat_poly.row_length_def)
    apply(auto simp add:scalar_prod)
    apply(simp add:trefoil_polynomial_def)
    done
(*lemma "
rat_poly_plus
     (rat_poly_times (rat_poly_times A A)
       (rat_poly_plus (rat_poly_times B (rat_poly_times B (rat_poly_times A A)))
         (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
           (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
             (rat_poly_times A A)))))
     (rat_poly_plus
       (rat_poly_times 2
         (rat_poly_times A
           (rat_poly_times A
             (rat_poly_times A (rat_poly_times A (rat_poly_times B B))))))
       (rat_poly_times (rat_poly_times B B)
         (rat_poly_times B (rat_poly_times B (rat_poly_times B B)))))
  = (A^6) + (A^2) + (B^2) + (B^6)"
*)(*
lemma "kauff_mat ([cup,cup]*[vert,over,vert]*[vert,over,vert]*(basic [cap,cap]))
          = [[(A^6) + (A^2) + (B^2) + (B^6)]]" 
  apply(simp add:mat_multI_def)
  apply(simp add:matT_vec_multI_def)
  apply(auto simp add:replicate_def rat_poly.row_length_def)
  apply(auto simp add:scalar_prod)
*)
(*
lemma "kauff_mat ([cup,cup]*[vert,over,vert]*[vert,over,vert]*(basic [cap,cap]))
          = [[(A^6) + (A^2) + (B^2) + (B^6)]]" 
  apply(simp add:mat_multI_def)
  apply(simp add:matT_vec_multI_def)
  apply(auto simp add:replicate_def rat_poly.row_length_def)
  apply(auto simp add:scalar_prod)
*)
(*
lemma 
"kauff_mat ([cup,cup,cup]*[vert,over,over,vert]*[vert,vert,cap,vert,vert]
*[vert,over,vert]*(basic [cap, cap]))
          = [[-(A^3) - (A^2) - A- (B^2) - (B^4)]]"
 apply(simp add:mat_multI_def)
  apply(simp add:matT_vec_multI_def)
  apply(auto simp add:replicate_def rat_poly.row_length_def)
  apply(auto simp add:scalar_prod)*)

(*
definition trefoil_polynomial::"rat_poly"
where
"trefoil_polynomial \<equiv>
rat_poly_plus
     (rat_poly_times (rat_poly_times A A)
       (rat_poly_plus
         (rat_poly_times B
           (rat_poly_times B
             (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
               (rat_poly_times A A))))
         (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
           (rat_poly_plus (rat_poly_times B (rat_poly_times B (rat_poly_times A A)))
             (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
               (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
                 (rat_poly_times A A)))))))
     (rat_poly_plus
       (rat_poly_times 2
         (rat_poly_times A
           (rat_poly_times A
             (rat_poly_times A
               (rat_poly_times A (rat_poly_times A (rat_poly_times B B)))))))
       (rat_poly_times (rat_poly_times B B)
         (rat_poly_times B
           (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
             (rat_poly_times B (rat_poly_times B B))))))"*)


(*
definition test::"rat_poly"
where

lemma trefoil:
"kauff_mat ([cup,cup]*[vert,over,vert]*[vert,over,vert]*[vert,over,vert]
              *(basic [cap,cap]))
          = [[trefoil_polynomial]]"
    apply(simp add:mat_multI_def)
    apply(simp add:matT_vec_multI_def)
    apply(auto simp add:replicate_def rat_poly.row_length_def)
    apply(auto simp add:scalar_prod)
    apply(simp add:trefoil_polynomial_def)
    done*)
end
