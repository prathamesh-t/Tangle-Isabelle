(*  Title:       Executable Matrix Operations on Matrices of Arbitrary Dimensions
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)

(*
Copyright 2010 Christian Sternagel, René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

header {* Basic Operations on Matrices *}

theory Matrix_Tensor
imports
  Utility 
begin

text {*
  This theory provides the operations of matrix addition, multiplication,
  and transposition as executable functions. 
  Most properties are proven via pointwise equality of matrices. 
*}


subsection {* types and well-formedness of vectors / matrices *}

type_synonym 'a vec = "'a list"
type_synonym 'a mat = "'a vec list" (* list of column-vectors *)


(* vector of given length *)
definition vec :: "nat \<Rightarrow> 'x vec \<Rightarrow> bool"
 where "vec n x = (length x = n)"

(* matrix of given number of rows and columns *)
definition mat :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> bool" where
 "mat nr nc m = (length m = nc \<and> Ball (set m) (vec nr))"

subsection {* definitions / algorithms *}

text {* note that these algorithms are generic in all basic definitions / operations 
like 0 (ze) 1 (on) addition (pl) multiplication (ti) and in the dimension(s) of the matrix/vector.
Hence, many of these algorithms require these definitions/operations/sizes as arguments.
All indices start from 0.
*}

(* the 0 vector *)
definition vec0I :: "'a \<Rightarrow> nat \<Rightarrow> 'a vec" where 
 "vec0I ze n = replicate n ze"

(* the 0 matrix *)
definition mat0I :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "mat0I ze nr nc = replicate nc (vec0I ze nr)"

(* the i-th unit vector of size n *) 
definition vec1I :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a vec"
  where "vec1I ze on n i \<equiv> replicate i ze @ on # replicate (n - 1 - i) ze"

(* the 1 matrix *)
definition mat1I :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a mat"
  where "mat1I ze on n \<equiv> map (vec1I ze on n) [0 ..< n]"


(* vector addition *)
definition vec_plusI :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec" where 
 "vec_plusI pl v w = map (\<lambda> xy. pl (fst xy) (snd xy)) (zip v w)"

(* matrix addition *)
definition mat_plusI :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
 where "mat_plusI pl m1 m2 = map (\<lambda> uv. vec_plusI pl (fst uv) (snd uv)) (zip m1 m2)"

(* scalar product *)
definition scalar_prodI :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a" where
 "scalar_prodI ze pl ti v w = foldr (\<lambda> (x,y) s. pl (ti x y) s) (zip v w) ze"

(* the m-th row of a matrix *)
definition row :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a vec"
where "row m i \<equiv> map (\<lambda> w. w ! i) m"

(* the m-th column of a matrix *)
definition col :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a vec"
where "col m i \<equiv> m ! i"

(* transposition of a matrix (number of rows of matrix has to be given since otherwise one 
   could not compute transpose [] which might be [] or [[]] or [[], []], or ...) *)
fun transpose :: "nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
 where "transpose nr [] = replicate nr []"
     | "transpose nr (v # m) = map (\<lambda> (vi,mi). (vi # mi)) (zip v (transpose nr m))"

(* matrix-vector multiplication, assumes the transposed matrix is given *)
definition matT_vec_multI :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a mat \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
 where "matT_vec_multI ze pl ti m v = map (\<lambda> w. scalar_prodI ze pl ti w v) m"

(* matrix-matrix multiplication, number of rows of left matrix has to be given (as transpose is used) *)
definition mat_multI :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" 
where "mat_multI ze pl ti nr m1 m2 \<equiv> map (matT_vec_multI ze pl ti (transpose nr m1)) m2"

(* power of a square matrix *)
fun mat_powI :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> 'a mat"
  where "mat_powI ze on pl ti n m 0 = mat1I ze on n"
      | "mat_powI ze on pl ti n m (Suc i) = mat_multI ze pl ti n (mat_powI ze on pl ti n m i) m"

definition sub_vec :: "nat \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
where "sub_vec = take"

(* taking only the upper left sub matrix *)
definition sub_mat :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
where "sub_mat nr nc m = map (sub_vec nr) (take nc m)"


(* map on vectors *)
definition vec_map :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
  where "vec_map = map"

(* map on matrices *)
definition mat_map :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
  where "mat_map f = map (vec_map f)"

subsection {* algorithms preserve dimensions *}

lemma vec0[simp]: "vec nr (vec0I ze nr)"
  by (simp add: vec_def vec0I_def)

lemma replicate_prop:
  assumes "P x"
  shows "\<forall>y\<in>set (replicate n x). P y"
  using assms by (induct n) simp_all

lemma mat0[simp]: "mat nr nc (mat0I ze nr nc)"
unfolding mat_def mat0I_def
using replicate_prop[of "vec nr" "vec0I ze nr" "nc"] by simp

lemma vec1: assumes "i < nr" shows "vec nr (vec1I ze on nr i)"
unfolding vec_def vec1I_def using assms by auto

lemma mat1: "mat nr nr (mat1I ze on nr)"
unfolding mat_def mat1I_def using vec1 by auto

lemma vec_plus: "\<lbrakk>vec nr u; vec nr v\<rbrakk> \<Longrightarrow> vec nr (vec_plusI pl u v)"
using assms 
unfolding vec_plusI_def vec_def
by auto

lemma mat_plus: assumes "mat nr nc m1" and "mat nr nc m2" shows "mat nr nc (mat_plusI pl m1 m2)"
using assms
unfolding mat_def mat_plusI_def
proof (simp, induct nc arbitrary: m1 m2, simp)
  case (Suc nn)
  show ?case 
  proof (cases m1)
    case Nil with Suc show ?thesis by auto
  next
    case (Cons v1 mm1) note oCons = this
    with Suc have l1: "length mm1 = nn" by auto
    show ?thesis
    proof (cases m2)
      case Nil with Suc show ?thesis by auto
    next
      case (Cons v2 mm2)
      with Suc have l2: "length mm2 = nn" by auto
      show ?thesis by (simp add: Cons oCons, intro conjI[OF vec_plus], (simp add: Cons oCons Suc)+, rule Suc, auto simp: Cons oCons Suc l1 l2)
    qed
  qed
qed

lemma vec_map: "vec nr u \<Longrightarrow> vec nr (vec_map f u)"
using assms 
unfolding vec_map_def vec_def
by auto

lemma mat_map: "mat nr nc m \<Longrightarrow> mat nr nc (mat_map f m)"
using assms vec_map
unfolding mat_map_def mat_def 
by auto

fun vec_fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a vec \<Rightarrow> 'b \<Rightarrow> 'b"
  where [code_unfold]: "vec_fold f = foldr f"

fun mat_fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a mat \<Rightarrow> 'b \<Rightarrow> 'b"
  where [code_unfold]: "mat_fold f = foldr (vec_fold f)"


lemma concat_mat: "mat nr nc m \<Longrightarrow>
  concat m = [ m ! i ! j. i \<leftarrow> [0 ..< nc], j \<leftarrow> [0 ..< nr] ]"
proof (induct m arbitrary: nc)
  case Nil
  thus ?case unfolding mat_def by auto
next
  case (Cons v m snc)
  from Cons(2) obtain nc where snc: "snc = Suc nc" and mat: "mat nr nc m" and v: "vec nr v"
    unfolding mat_def by (cases snc, auto)
  from v have nr: "nr = length v" unfolding vec_def by auto
  have v: "map (\<lambda> i. v ! i) [0 ..< nr] = v" unfolding nr map_nth by simp
  note IH = Cons(1)[OF mat]
  show ?case 
    unfolding snc 
    unfolding map_upt_Suc
    unfolding nth.simps nat.simps concat.simps
    unfolding IH v ..
qed


lemma row: assumes "mat nr nc m"
  and "i < nr"
  shows "vec nc (row m i)"
  using assms
  unfolding vec_def row_def mat_def
  by (auto simp: vec_def) 

lemma col: assumes "mat nr nc m"
  and "i < nc"
  shows "vec nr (col m i)"
  using assms
  unfolding vec_def col_def mat_def
  by (auto simp: vec_def) 

lemma transpose: assumes "mat nr nc m"
  shows "mat nc nr (transpose nr m)"
using assms 
proof (induct m arbitrary: nc)
  case (Cons v m)
  from `mat nr nc (v # m)` obtain ncc where nc: "nc = Suc ncc" by (cases nc, auto simp: mat_def) 
  with Cons have wfRec: "mat ncc nr (transpose nr m)" unfolding mat_def by auto
  have "min nr (length (transpose nr m)) = nr" using wfRec unfolding mat_def by auto
  moreover have "Ball (set (transpose nr (v # m))) (vec nc)"
  proof -
    {
      fix a b
      assume mem: "(a,b) \<in> set (zip v (transpose nr m))"
      from mem have "b \<in> set (transpose nr m)" by (rule set_zip_rightD)
      with wfRec have "length b = ncc" unfolding mat_def using vec_def[of ncc] by auto
      hence "length (split op # (a,b)) = Suc ncc" by auto
    }
    thus ?thesis
      by (auto simp: vec_def nc)
  qed
  moreover from `mat nr nc (v # m)` have wfV: "length v = nr" unfolding mat_def by (simp add: vec_def)
  ultimately
  show ?case unfolding mat_def
    by (intro conjI, auto simp: wfV wfRec mat_def vec_def)
qed (simp add: mat_def vec_def set_replicate_conv_if)


lemma matT_vec_multI: assumes "mat nr nc m"
  shows "vec nc (matT_vec_multI ze pl ti m v)"
  unfolding matT_vec_multI_def
  using assms
  unfolding mat_def
  by (simp add: vec_def)

lemma mat_mult: assumes wf1: "mat nr n m1"
  and wf2: "mat n nc m2"
  shows "mat nr nc (mat_multI ze pl ti nr m1 m2)"
using assms
unfolding mat_def mat_multI_def by (auto simp: matT_vec_multI[OF transpose[OF wf1]])

lemma mat_pow: assumes "mat n n m"
  shows "mat n n (mat_powI ze on pl ti n m i)"
proof (induct i)
  case 0
  show ?case unfolding mat_powI.simps by (rule mat1)
next
  case (Suc i)
  show ?case unfolding mat_powI.simps
    by (rule mat_mult[OF Suc assms])
qed

lemma sub_vec: assumes "vec nr v" and "sd \<le> nr" 
  shows "vec sd (sub_vec sd v)"
using assms unfolding vec_def sub_vec_def by auto

lemma sub_mat: assumes wf: "mat nr nc m" and sr: "sr \<le> nr" and sc: "sc \<le> nc"
  shows "mat sr sc (sub_mat sr sc m)"
using assms in_set_takeD[of _ sc m] sub_vec[OF _ sr] unfolding mat_def sub_mat_def by auto


subsection {* properties of algorithms which do not depend on properties of type of matrix *}

lemma mat0_index: assumes "i < nc" and "j < nr"
  shows "mat0I ze nr nc ! i ! j = ze"
unfolding mat0I_def vec0I_def using assms by auto

lemma mat0_row: assumes "i < nr"
  shows "row (mat0I ze nr nc) i = vec0I ze nc"
unfolding row_def mat0I_def vec0I_def
using assms by auto


lemma mat0_col: assumes "i < nc"
  shows "col (mat0I ze nr nc) i = vec0I ze nr"
unfolding mat0I_def col_def
using assms by auto

lemma vec1_index: assumes j: "j < n"
  shows "vec1I ze on n i ! j = (if i = j then on else ze)" (is "_ = ?r")
unfolding vec1I_def
proof -
  let ?l = "replicate i ze @ on # replicate (n - 1 - i) ze"
  have len: "length ?l > i" by auto
  have len2: "length (replicate i ze @ on # []) > i" by auto
  show "?l ! j = ?r"
  proof (cases "j = i")
    case True
    thus ?thesis by (simp add: nth_append)
  next
    case False
    show ?thesis 
    proof (cases "j < i")
      case True
      thus ?thesis by (simp add: nth_append)
    next
      case False
      with `j \<noteq> i` have gt: "j > i" by auto
      from this have "\<exists> k. j = i + Suc k" by arith
      from this obtain k where k: "j = i + Suc k" by auto
      with j show ?thesis by (simp add: nth_append)
    qed
  qed
qed


lemma col_transpose_is_row: 
  assumes wf: "mat nr nc m"
  and i: "i < nr"
  shows "col (transpose nr m) i = row m i"
using wf 
proof (induct m arbitrary: nc)
  case (Cons v m)
  from `mat nr nc (v # m)` obtain ncc where nc: "nc = Suc ncc" and wf: "mat nr ncc m"  by (cases nc, auto simp: mat_def)
  from `mat nr nc (v # m)` nc have lengths: "(\<forall> w \<in> set m. length w = nr) \<and> length v = nr \<and> length m = ncc" unfolding mat_def by (auto simp: vec_def)
  from wf Cons have colRec: "col (transpose nr m) i = row m i" by auto
  hence simpme: "transpose nr m ! i = row m i" unfolding col_def by auto
  from wf have trans: "mat ncc nr (transpose nr m)" by (rule transpose)
  hence lengths2: "(\<forall> w \<in> set (transpose nr m). length w = ncc) \<and> length (transpose nr m) = nr" unfolding mat_def by (auto simp: vec_def)
  {
    fix j
    assume "j < length (col (transpose nr (v # m)) i)"
    hence "j < Suc ncc" by (simp add: col_def lengths2 lengths i) 
    hence "col (transpose nr (v # m)) i ! j = row (v # m) i ! j"
      by (cases j, simp add: row_def col_def i lengths lengths2, simp add: row_def col_def i lengths lengths2 simpme)
  } note simpme = this
  show ?case by (rule nth_equalityI, simp add: col_def row_def lengths lengths2 i, intro allI impI, rule simpme)
qed (simp add: col_def row_def mat_def i)

lemma mat_col_eq:
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  shows "(\<forall> i < nc. col m1 i = col m2 i) = (m1 = m2)" (is "?l = ?r")
proof
  assume ?r thus ?l by auto
next
  assume ?l show ?r 
  proof (rule nth_equalityI)
    show "length m1 = length m2" using wf1 wf2 unfolding mat_def by auto
  next
    from `?l` show "\<forall> i < length m1. m1 ! i = m2 ! i" using wf1 unfolding col_def mat_def by auto
  qed
qed

lemma mat_eq_index:
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  shows "(m1 = m2) = (\<forall> i < nc. \<forall> j < nr. m1 ! i ! j = m2 ! i ! j)" (is "?l = ?r")
proof 
  assume ?l thus ?r by auto
next
  assume ?r show ?l
  proof (simp only: mat_col_eq[OF wf1 wf2,symmetric], unfold col_def, intro allI impI)
    fix i
    assume i: "i < nc"
    show "m1 ! i = m2 ! i"
    proof (rule nth_equalityI)      
      show "length (m1 ! i)  = length (m2 ! i)" using wf1 wf2 i unfolding mat_def by (auto simp: vec_def)
    next
      from `?r` i show "\<forall> j < length (m1 ! i). m1 ! i ! j = m2 ! i ! j" using wf1 wf2 unfolding mat_def by (auto simp: vec_def)
    qed
  qed
qed

lemma vec_index_eq: 
  assumes wf1: "vec n v1"
  and wf2: "vec n v2"
  shows "(v1 = v2) = (\<forall> i < n. v1 ! i = v2 ! i)" (is "?l = ?r")
proof
  assume ?l thus ?r by auto
next
  assume ?r show ?l 
  proof (rule nth_equalityI)
    from wf1 wf2 show "length v1 = length v2" unfolding vec_def by simp
  next
    from `?r` wf1 show "\<forall> i < length v1. v1 ! i = v2 ! i" unfolding vec_def by simp
  qed
qed


lemma row_col: assumes "mat nr nc m"  
  and "i < nr" and "j < nc"
  shows "row m i ! j = col m j ! i"
using assms unfolding mat_def row_def col_def
  by auto

lemma col_index: assumes m: "mat nr nc m"
  and i: "i < nc"
  shows "col m i = map (\<lambda> j. m ! i ! j) [0 ..< nr]"
proof -
  from m[unfolded mat_def] i
  have nr: "nr = length (m ! i)" by (auto simp: vec_def)
  show ?thesis unfolding nr col_def 
    by (rule map_nth[symmetric])
qed

lemma row_index: assumes m: "mat nr nc m"
  and i: "i < nr"
  shows "row m i = map (\<lambda> j. m ! j ! i) [0 ..< nc]"
proof -
  note rc = row_col[OF m i]
  from row[OF m i] have id: "length (row m i) = nc" unfolding vec_def by simp
  from map_nth[of "row m i"]
  have "row m i = map (\<lambda> j. row m i ! j) [0 ..< nc]" unfolding id by simp
  also have "... = map (\<lambda> j. m ! j ! i) [0 ..< nc]" using rc[unfolded col_def] by auto
  finally show ?thesis .
qed


lemma mat_row_eq: 
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  shows "(m1 = m2) = (\<forall> i < nr. row m1 i = row m2 i)" (is "?l = ?r")
proof 
  assume ?l thus ?r by auto
next
  assume ?r show ?l
  proof (rule nth_equalityI)
    show "length m1 = length m2" using wf1 wf2 unfolding mat_def by auto
  next
    show "\<forall> i < length m1. m1 ! i = m2 ! i"
    proof (intro allI impI)
      fix i
      assume i: "i < length m1"
      show "m1 ! i = m2 ! i"
      proof (rule nth_equalityI)
        show "length (m1 ! i) = length (m2 ! i)" using wf1 wf2 i unfolding mat_def by (auto simp: vec_def)
      next
        show "\<forall> j < length (m1 ! i). m1 ! i ! j = m2 ! i ! j" 
        proof (intro allI impI)
          fix j
          assume j: "j < length (m1 ! i)"
          from i j wf1 have i1: "i < nc" and j1: "j < nr" unfolding mat_def by (auto simp: vec_def)
          from `?r` j1 have "col m1 i ! j = col m2 i ! j"
            by (simp add: row_col[OF wf1 j1 i1, symmetric] row_col[OF wf2 j1 i1, symmetric])
          thus "m1 ! i ! j = m2 ! i ! j" unfolding col_def .
        qed
      qed
    qed
  qed
qed

lemma row_transpose_is_col:   assumes wf: "mat nr nc m"
  and i: "i < nc"
  shows "row (transpose nr m) i = col m i"
proof -
  have len: "length (row (transpose nr m) i) = length (col m i)"
    using transpose[OF wf]  wf i  unfolding row_def col_def mat_def by (auto simp: vec_def)
  show ?thesis 
  proof (rule nth_equalityI[OF len], intro allI impI)
    fix j
    assume "j < length (row (transpose nr m) i)"
    hence j: "j < nr" using transpose[OF wf] wf i unfolding row_def col_def mat_def by (auto simp: vec_def)
    show "row (transpose nr m) i ! j = col m i ! j"
      by (simp only: row_col[OF transpose[OF wf] i j],
        simp only: col_transpose_is_row[OF wf j],
        simp only: row_col[OF wf j i])
  qed
qed


lemma matT_vec_mult_to_scalar: 
  assumes "mat nr nc m"
  and "vec nr v"
  and "i < nc"
  shows "matT_vec_multI ze pl ti m v ! i = scalar_prodI ze pl ti (col m i) v"
unfolding matT_vec_multI_def using assms unfolding mat_def col_def by (auto simp: vec_def)

lemma mat_vec_mult_index: 
  assumes wf: "mat nr nc m"
  and wfV: "vec nc v"
  and i: "i < nr"
  shows "matT_vec_multI ze pl ti (transpose nr m) v ! i = scalar_prodI ze pl ti (row m i) v"
by (simp only:matT_vec_mult_to_scalar[OF transpose[OF wf] wfV i],
  simp only: col_transpose_is_row[OF wf i])

lemma mat_mult_index :
  assumes wf1: "mat nr n m1"
  and wf2: "mat n nc m2"
  and i: "i < nr"
  and j: "j < nc"
  shows "mat_multI ze pl ti nr m1 m2 ! j ! i = scalar_prodI ze pl ti (row m1 i) (col m2 j)"
proof -
  have jlen: "j < length m2" using wf2 j unfolding mat_def by auto
  have wfj: "vec n (m2 ! j)" using jlen j wf2 unfolding mat_def by auto
  show ?thesis 
    unfolding mat_multI_def
    by (simp add: jlen, simp only: mat_vec_mult_index[OF wf1 wfj i], unfold col_def, simp)
qed

lemma col_mat_mult_index :
  assumes wf1: "mat nr n m1"
  and wf2: "mat n nc m2"
  and j: "j < nc"
  shows "col (mat_multI ze pl ti nr m1 m2) j = map (\<lambda> i. scalar_prodI ze pl ti (row m1 i) (col m2 j)) [0 ..< nr]" (is "col ?l j = ?r")
proof - 
  have wf12: "mat nr nc ?l" by (rule mat_mult[OF wf1 wf2])
  have len: "length (col ?l j) = length ?r" and nr: "length (col ?l j) = nr" using wf1 wf2 wf12 j unfolding mat_def col_def by (auto simp: vec_def) 
  show ?thesis by (rule nth_equalityI[OF len], simp add: j nr, intro allI impI, unfold col_def, simp only:
    mat_mult_index[OF wf1 wf2 _ j], simp add: col_def)
qed

lemma row_mat_mult_index :
  assumes wf1: "mat nr n m1"
  and wf2: "mat n nc m2"
  and i: "i < nr"
  shows "row (mat_multI ze pl ti nr m1 m2) i = map (\<lambda> j. scalar_prodI ze pl ti (row m1 i) (col m2 j)) [0 ..< nc]" (is "row ?l i = ?r")
proof - 
  have wf12: "mat nr nc ?l" by (rule mat_mult[OF wf1 wf2])
  hence lenL: "length ?l = nc" unfolding mat_def by simp
  have len: "length (row ?l i) = length ?r" and nc: "length (row ?l i) = nc" using wf1 wf2 wf12 i unfolding mat_def row_def by (auto simp: vec_def) 
  show ?thesis by (rule nth_equalityI[OF len], simp add: i nc, intro allI impI, unfold row_def, simp add: lenL, simp only: 
    mat_mult_index[OF wf1 wf2 i], simp add: row_def)
qed

lemma scalar_prod_cons: 
  "scalar_prodI ze pl ti (a # as) (b # bs) = pl (ti a b) (scalar_prodI ze pl ti as bs)"
unfolding scalar_prodI_def by auto


lemma vec_plus_index: 
  assumes wf1: "vec nr v1"
  and wf2: "vec nr v2"
  and i: "i < nr"
  shows "vec_plusI pl v1 v2 ! i = pl (v1 ! i)  (v2 ! i)"
using wf1 wf2 i
unfolding vec_def vec_plusI_def
proof (induct v1 arbitrary: i v2 nr, simp)
  case (Cons a v11)
  from Cons obtain b v22 where v2: "v2 = b # v22" by (cases v2, auto)
  from v2 Cons obtain nrr where nr: "nr = Suc nrr" by (force)
  from Cons show ?case
    by (cases i, simp add: v2, auto simp: v2 nr)
qed

lemma mat_map_index: assumes wf: "mat nr nc m" and i: "i < nc" and j: "j < nr" 
  shows "mat_map f m ! i ! j = f (m ! i ! j)"
proof -
  from wf i have i: "i < length m" unfolding mat_def by auto
  with wf j have j: "j < length (m ! i)" unfolding mat_def by (auto simp: vec_def)
  have "mat_map f m ! i ! j = map (map f) m ! i ! j" unfolding mat_map_def vec_map_def by auto
  also have "\<dots> = map f (m ! i) ! j" using i by auto
  also have "\<dots> = f (m ! i ! j)" using j by auto
  finally show ?thesis .
qed


lemma mat_plus_index: 
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  and i: "i < nc"
  and j: "j < nr"
  shows "mat_plusI pl m1 m2 ! i ! j = pl (m1 ! i ! j) (m2 ! i ! j)"
using wf1 wf2 i
unfolding mat_plusI_def mat_def 
proof (simp, induct m1 arbitrary: m2 i nc, simp)
  case (Cons v1 m11)
  from Cons obtain v2 m22 where m2: "m2 = v2 # m22" by (cases m2, auto)
  from m2 Cons obtain ncc where nc: "nc = Suc ncc" by force
  show ?case
  proof (cases i, simp add: m2, rule vec_plus_index[where nr = nr], (auto simp: Cons j m2)[3])
    case (Suc ii)
    with Cons show ?thesis using m2 nc by auto
  qed
qed

lemma col_mat_plus: assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  and i: "i < nc"
  shows "col (mat_plusI pl m1 m2) i = vec_plusI pl (col m1 i) (col m2 i)"
using assms
unfolding mat_plusI_def col_def mat_def
proof (induct m1 arbitrary: m2 nc i, simp)
  case (Cons v m1)
  from Cons obtain v2 m22 where m2: "m2 = v2 # m22" by (cases m2, auto)
  from m2 Cons obtain ncc where nc: "nc = Suc ncc" by force
  show ?case
  proof (cases i, simp add: m2)
    case (Suc ii)
    with Cons show ?thesis using m2 nc by auto
  qed
qed

lemma transpose_index: assumes wf: "mat nr nc m"
  and i: "i < nr"
  and j: "j < nc"
  shows "transpose nr m ! i ! j = m ! j ! i"
proof -
  have "transpose nr m ! i ! j = col (transpose nr m) i ! j" unfolding col_def by simp
  also have "\<dots> = row m i ! j" using col_transpose_is_row[OF wf i] by simp
  also have "\<dots> = m ! j ! i" unfolding row_def using wf j unfolding mat_def by (auto simp: vec_def)
  finally show ?thesis . 
qed

lemma transpose_mat_plus: assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  shows "transpose nr (mat_plusI pl m1 m2) = mat_plusI pl (transpose nr m1) (transpose nr m2)"
proof - 
  let ?m12 = "mat_plusI pl m1 m2"
  let ?t1 = "transpose nr m1"
  let ?t2 = "transpose nr m2"
  from mat_plus[OF wf1 wf2] have wf12: "mat nr nc ?m12" .
  from transpose[OF wf1] have wft1: "mat nc nr ?t1" .
  from transpose[OF wf2] have wft2: "mat nc nr ?t2" .
  show ?thesis 
  proof (simp only: mat_eq_index[OF transpose[OF wf12] mat_plus[OF wft1 wft2]], intro allI impI)
    fix i j
    assume i: "i < nr" and j: "j < nc"
    show "transpose nr ?m12 ! i ! j = mat_plusI pl ?t1 ?t2 ! i ! j"      
      by (simp only: transpose_index[OF wf12 i j],
        simp only: mat_plus_index[OF wft1 wft2 i j],
        simp only: mat_plus_index[OF wf1 wf2 j i],
        simp only: transpose_index[OF wf1 i j],
        simp only: transpose_index[OF wf2 i j])
  qed
qed
      

lemma row_mat_plus: assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  and i: "i < nr"
  shows "row (mat_plusI pl m1 m2) i = vec_plusI pl (row m1 i) (row m2 i)"
  by (
    simp only: col_transpose_is_row[OF mat_plus[OF wf1 wf2] i, symmetric], 
    simp only: transpose_mat_plus[OF wf1 wf2],
    simp only: col_mat_plus[OF transpose[OF wf1] transpose[OF wf2] i],
    simp only: col_transpose_is_row[OF wf1 i],
    simp only: col_transpose_is_row[OF wf2 i])


lemma col_mat1: assumes "i < nr"
  shows "col (mat1I ze on nr) i = vec1I ze on nr i"
unfolding mat1I_def col_def using assms by auto


lemma mat1_index: assumes i: "i < n" and j: "j < n"
  shows "mat1I ze on n ! i ! j = (if i = j then on else ze)"
  by (simp add: col_mat1[OF i, simplified col_def] vec1_index[OF j])

lemma transpose_mat1: "transpose nr (mat1I ze on nr) = (mat1I ze on nr)"
proof (simp only: mat_eq_index[OF transpose[OF mat1] mat1], intro impI allI)
  fix i j
  assume i: "i < nr" and j: "j < nr"
  let ?I = "mat1I ze on nr"
  show "transpose nr ?I ! i ! j = ?I ! i ! j"
    by  (simp only: col_def[symmetric], 
      simp only: col_mat1[OF i],
      simp only: row_col[OF transpose[OF mat1] j i,symmetric],
      simp only: row_transpose_is_col[OF mat1 j],
      simp only: col_mat1[OF j],
      simp only: vec1_index[OF j],
      simp only: vec1_index[OF i], simp)
qed

lemma row_mat1: assumes i: "i < nr"
  shows "row (mat1I ze on nr) i = vec1I ze on nr i"
by (simp only: col_transpose_is_row[OF mat1 i, symmetric],
  simp only: transpose_mat1,
  simp only: col_mat1[OF i])

lemma sub_mat_index:
  assumes wf: "mat nr nc m"
  and sr: "sr \<le> nr"
  and sc: "sc \<le> nc"
  and j: "j < sr"
  and i: "i < sc"
  shows "sub_mat sr sc m ! i ! j = m ! i ! j"
proof -
  from assms have im: "i < length m" unfolding mat_def by auto
  from assms have jm: "j < length (m ! i)" unfolding mat_def by (auto simp: vec_def)
  have "sub_mat sr sc m ! i ! j = map (take sr) (take sc m) ! i ! j"
    unfolding sub_mat_def sub_vec_def by auto
  also have "\<dots> = take sr (m ! i) ! j" using i im by auto
  also have "\<dots> = m ! i ! j" using j jm by auto
  finally show ?thesis .
qed

subsection {* lemmas requiring properties of plus, times, ... *}

context plus
begin

abbreviation vec_plus :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
where "vec_plus \<equiv> vec_plusI plus"

abbreviation mat_plus :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
where "mat_plus \<equiv> mat_plusI plus"
end

context semigroup_add
begin
lemma vec_plus_assoc: assumes u: "vec nr u" and v: "vec nr v" and w: "vec nr w"
 shows "vec_plus u (vec_plus v w) = vec_plus (vec_plus u v) w" (is "?l = ?r")
proof -
  from v w have vw: "vec nr (vec_plus v w)" by (simp add: vec_plus)
  from u v have uv: "vec nr (vec_plus u v)" by (simp add: vec_plus)
  from assms have l: "vec nr ?l" by (simp add: vec_plus)
  from assms have r: "vec nr ?r" by (simp add: vec_plus)
  show ?thesis by (simp only: vec_index_eq[OF l r], intro allI impI,
    simp only: vec_plus_index[OF u vw],
    simp only: vec_plus_index[OF v w],
    simp only: vec_plus_index[OF uv w],
    simp only: vec_plus_index[OF u v],
    simp only: add_assoc)
qed

lemma mat_plus_assoc: assumes wf_1: "mat nr nc m1" and wf_2: "mat nr nc m2" and wf_3: "mat nr nc m3"
  shows "mat_plus m1 (mat_plus m2 m3) = mat_plus (mat_plus m1 m2) m3" (is "?l = ?r")
proof -
  from wf_2 wf_3 have wf_23: "mat nr nc (mat_plus m2 m3)" by (simp add: mat_plus)
  from wf_1 wf_2 have wf_12: "mat nr nc (mat_plus m1 m2)" by (simp add: mat_plus)
  from assms have wf_l: "mat nr nc ?l" by (simp add: mat_plus)
  from assms have wf_r: "mat nr nc ?r" by (simp add: mat_plus)
  show ?thesis by (simp only: mat_eq_index[OF wf_l wf_r], intro allI impI,
    simp only: mat_plus_index[OF wf_1 wf_23],
    simp only: mat_plus_index[OF wf_2 wf_3],
    simp only: mat_plus_index[OF wf_12 wf_3],
    simp only: mat_plus_index[OF wf_1 wf_2],
    simp only: add_assoc)
qed
end

context ab_semigroup_add
begin
lemma vec_plus_comm: "vec_plus x y = vec_plus y x"
unfolding vec_plusI_def
proof (induct x arbitrary: y)
  case (Cons a x)
  thus ?case 
    by (cases y, auto simp: add_commute) 
qed simp


lemma mat_plus_comm: "mat_plus m1 m2 = mat_plus m2 m1"
unfolding mat_plusI_def
proof (induct m1 arbitrary: m2)
  case (Cons v m1) note oCons = this
  thus ?case
  proof (cases m2)
    case (Cons w m2a)
    hence "mat_plus (v # m1) m2 = vec_plus v w # mat_plus m1 m2a" by (auto simp: mat_plusI_def)
    also have "\<dots> = vec_plus w v # mat_plus m1 m2a" using vec_plus_comm by auto
    finally show ?thesis using Cons oCons by (auto simp: mat_plusI_def)
  qed simp
qed simp
end

context zero
begin
abbreviation vec0 :: "nat \<Rightarrow> 'a vec"
where "vec0 \<equiv> vec0I zero"

abbreviation mat0 :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat"
where "mat0 \<equiv> mat0I zero"
end

context monoid_add
begin
lemma vec0_plus[simp]: assumes "vec nr u" shows "vec_plus (vec0 nr) u = u"
using assms
unfolding vec_def vec_plusI_def vec0I_def
proof (induct nr arbitrary: u)
 case (Suc nn) thus ?case by (cases u, auto)
qed simp

lemma plus_vec0[simp]: assumes "vec nr u" shows "vec_plus u (vec0 nr) = u"
using assms
unfolding vec_def vec_plusI_def vec0I_def
proof (induct nr arbitrary: u)
 case (Suc nn) thus ?case by (cases u, auto)
qed simp

lemma plus_mat0[simp]: assumes "mat nr nc m" shows "mat_plus m (mat0 nr nc) = m"
using assms 
unfolding mat_def 
proof (induct nc arbitrary: m)
  case (Suc nn) 
  thus ?case 
  proof (cases m)
    case (Cons v mm)
    with Suc have wf: "vec nr v" by auto
    from Cons Suc have "mat_plus m (mat0 nr (Suc nn)) = vec_plus v (vec0 nr) # mat_plus mm (mat0 nr nn)" by (auto simp: mat_plusI_def mat0I_def)
    also have "\<dots> = vec_plus v (vec0 nr) # mm" using Suc Cons by auto
    also have "\<dots> = v # mm" by (simp only: plus_vec0 wf)
    finally show ?thesis using Cons by auto
  qed simp
qed (simp add: mat_plusI_def mat0I_def)
end

context semiring_0
begin
abbreviation scalar_prod :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a"
where "scalar_prod \<equiv> scalar_prodI zero plus times"

abbreviation mat_mult :: "nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
where "mat_mult \<equiv> mat_multI zero plus times"

lemma scalar_prod: "scalar_prod v1 v2 = listsum (map (\<lambda>(x,y). x * y) (zip v1 v2))" 
proof -
  obtain z where z: "zip v1 v2 = z" by auto
  show ?thesis unfolding scalar_prodI_def listsum_def z 
    by (induct z, auto)
qed

lemma scalar_prod_last: assumes "length v1 = length v2" 
  shows "scalar_prod (v1 @ [x1]) (v2 @ [x2]) = x1 * x2 + scalar_prod v1 v2"
using assms 
proof (induct v1 arbitrary: v2)
  case (Cons y1 w1)
  from Cons(2) obtain y2 w2 where v2: "v2 = Cons y2 w2" and len: "length w1 = length w2" by (cases v2, auto)
  from Cons(1)[OF len] have rec: "scalar_prod (w1 @ [x1]) (w2 @ [x2]) = x1 * x2 + scalar_prod w1 w2" .
  have "scalar_prod ((y1 # w1) @ [x1]) (v2 @ [x2]) = 
    (y1 * y2 + x1 * x2) + scalar_prod w1 w2" by (simp add: scalar_prod_cons v2 rec add_assoc)
  also have "\<dots> = (x1 * x2 + y1 * y2) + scalar_prod w1 w2" using add_commute[of "x1 * x2"] by simp
  also have "\<dots> = x1 * x2 + (scalar_prod (y1 # w1) v2)" by (simp add: add_assoc scalar_prod_cons v2)
  finally show ?case .
qed (simp add: scalar_prodI_def)

lemma scalar_product_assoc: 
  assumes wfm: "mat nr nc m"
  and wfr: "vec nr r"
  and wfc: "vec nc c"
  shows "scalar_prod (map (\<lambda>k. scalar_prod r (col m k)) [0..<nc]) c = scalar_prod r (map (\<lambda>k. scalar_prod (row m k) c) [0..<nr])"
using wfm wfc
unfolding col_def 
proof (induct m arbitrary: nc c)
  case Nil
  hence nc: "nc = 0" unfolding mat_def by (auto)
  from wfr have nr: "nr = length r" unfolding vec_def by auto
  let ?term = "\<lambda> r :: 'a vec. zip r (map (\<lambda> k. zero) [0..<length r])"
  let ?fun = "\<lambda> (x,y). plus (times x y)"
  have "foldr ?fun (?term r) zero = zero" 
  proof (induct r, simp)
    case (Cons d r)
    have "foldr ?fun (?term (d # r)) zero = foldr ?fun ( (d,zero) # ?term r) zero" by (simp only: map_replicate_trivial, simp)
    also have "\<dots> = zero" using Cons by simp
    finally show ?case .
  qed
  hence "zero = foldr ?fun (zip r (map (\<lambda> k. zero) [0..<nr])) zero" by (simp add: nr)
  with Nil nc show ?case 
    by (simp add: scalar_prodI_def row_def)
next
  case (Cons v m)
  from this obtain ncc where nc: "nc = Suc ncc" and wf: "mat nr ncc m" unfolding mat_def by (auto simp: vec_def)
  from nc `vec nc c` obtain a cc where c: "c = a # cc" and wfc: "vec ncc cc" unfolding vec_def by (cases c, auto)
  have rec: "scalar_prod (map (\<lambda> k. scalar_prod r (m ! k)) [0..<ncc]) cc = scalar_prod r (map (\<lambda> k. scalar_prod (row m k) cc) [0..<nr])"
    by (rule Cons, rule wf, rule wfc)
  have id: "map (\<lambda>k. scalar_prod r ((v # m) ! k)) [0..<Suc ncc] = scalar_prod r v # map (\<lambda> k. scalar_prod r (m ! k)) [0..<ncc]" by (induct ncc, auto)    
  from wfr have nr: "nr = length r" unfolding vec_def by auto
  with Cons have v: "length v = length r" unfolding mat_def by (auto simp: vec_def)
  have "\<forall> i < nr. vec ncc (row m i)" by (intro allI impI, rule row[OF wf], simp)
  obtain tm where tm: "tm = transpose nr m" by auto
  hence idk: "\<forall> k < length r. row m k = tm ! k" using col_transpose_is_row[OF wf] unfolding col_def by (auto simp: nr)
  hence idtm1: "map (\<lambda>k. scalar_prod (row m k) cc) [0..<length r] = map (\<lambda>k. scalar_prod (tm ! k) cc) [0..<length r]" 
    and idtm2: "map (\<lambda>k. plus (times (v ! k) a) (scalar_prod (row m k) cc)) [0..<length r] = map (\<lambda>k. plus (times (v ! k) a) (scalar_prod (tm ! k) cc)) [0..<length r]" by auto
  from tm transpose[OF wf] have "mat ncc nr tm" by simp
  with nr have "length tm = length r" and  "(\<forall> i < length r. length (tm ! i) = ncc)" unfolding mat_def by (auto simp: vec_def) 
  with v have main: "plus (times (scalar_prod r v) a) (scalar_prod r (map (\<lambda>k. scalar_prod (tm ! k) cc) [0..<length r])) =
    scalar_prod r (map (\<lambda>k. plus (times (v ! k) a) (scalar_prod (tm ! k) cc)) [0..<length r])" 
  proof (induct r arbitrary: v tm)
    case Nil
    thus ?case by (auto simp: scalar_prodI_def row_def)
  next
    case (Cons b r)
    from this obtain c vv where v: "v = c # vv" and vvlen: "length vv = length r" by (cases v, auto)
    from Cons obtain u mm where tm: "tm = u # mm" and mmlen: "length mm = length r"  by (cases tm, auto)
    from Cons tm have argLen: "\<forall> i < length r. length (mm ! i) = ncc" by auto
    have rec: "plus (times (scalar_prod r vv) a) (scalar_prod r (map (\<lambda>k. scalar_prod (mm ! k) cc) [0..<length r])) =
     scalar_prod r (map (\<lambda>k. plus (times (vv ! k) a) (scalar_prod (mm ! k) cc)) [0..<length r])" 
      (is "plus (times ?rv a) ?recl = ?recr")
      by (rule Cons, auto simp: vvlen mmlen argLen)
    have id: "map (\<lambda>k. scalar_prod ((u # mm) ! k) cc) [0..<length (b # r)] = scalar_prod u cc # map (\<lambda>k. scalar_prod (mm ! k) cc) [0..<length r]" 
      by (simp, induct r, auto)
    have id2: "map (\<lambda>k. plus (times ((c # vv) ! k) a) (scalar_prod ((u # mm) ! k) cc)) [0..<length (b # r)] = 
               (plus (times c a) (scalar_prod u cc)) #
               map (\<lambda>k. plus (times (vv ! k) a) (scalar_prod (mm ! k) cc)) [0..<length r]" 
      by (simp, induct r, auto)
    show ?case proof (simp only: v tm, simp only: id, simp only: id2, simp only: scalar_prod_cons)
      let ?uc = "scalar_prod u cc"
      let ?bca = "times (times b c) a"
      have "plus (times (plus (times b c) ?rv) a) (plus (times b ?uc) ?recl) = plus (plus ?bca (times ?rv a)) (plus (times b ?uc) ?recl)" 
        by (simp add: distrib_right)
      also have "\<dots> = plus (plus ?bca (times ?rv a)) (plus ?recl (times b ?uc))" by (simp add: add_commute)
      also have "\<dots> = plus ?bca (plus (plus (times ?rv a) ?recl) (times b ?uc))" by (simp add: add_assoc)
      also have "\<dots> = plus ?bca (plus ?recr (times b ?uc))" by (simp only: rec)
      also have "\<dots> = plus ?bca (plus (times b ?uc) ?recr)" by (simp add: add_commute)
      also have "\<dots> = plus (times b (plus (times c a) ?uc)) ?recr" by (simp add: distrib_left mult_assoc add_assoc)
      finally show "plus (times (plus (times b c) ?rv) a) (plus (times b ?uc) ?recl) = plus (times b (plus (times c a) ?uc)) ?recr" .
    qed
  qed
  show ?case 
    by (simp only: c scalar_prod_cons, simp only: nc, simp only: id, simp only: scalar_prod_cons, simp only: rec, simp only: nr, simp only: idtm1 idtm2, simp only: main, simp only: idtm2[symmetric], simp add: row_def scalar_prod_cons)
qed


lemma mat_mult_assoc: 
  assumes wf1: "mat nr n1 m1"
  and wf2: "mat n1 n2 m2"
  and wf3: "mat n2 nc m3"
  shows "mat_mult nr (mat_mult nr m1 m2) m3 = mat_mult nr m1 (mat_mult n1 m2 m3)" (is "?m12_3 = ?m1_23")
proof -
  let ?m12 = "mat_mult nr m1 m2"
  let ?m23 = "mat_mult n1 m2 m3"
  from wf1 wf2 have wf12: "mat nr n2 ?m12" by (rule mat_mult)
  from wf2 wf3 have wf23: "mat n1 nc ?m23" by (rule mat_mult)
  from wf1 wf23 have wf1_23: "mat nr nc ?m1_23" by (rule mat_mult)
  from wf12 wf3 have wf12_3: "mat nr nc ?m12_3" by (rule mat_mult)
  show ?thesis
  proof (simp only: mat_col_eq[OF wf12_3 wf1_23, symmetric], unfold col_def, intro allI impI)
    fix i
    assume i: "i < nc"
    with wf1_23 wf12_3 wf3 have len: "length (?m12_3 ! i) = length (?m1_23 ! i)" and ilen: "i < length m3" unfolding mat_def by (auto simp: vec_def)
    show "?m12_3 ! i = ?m1_23 ! i"
    proof (rule nth_equalityI[OF len], intro allI impI)
      fix j
      assume jlen: "j < length (?m12_3 ! i)"
      with wf12_3 i have j: "j < nr" unfolding mat_def by (auto simp: vec_def)      
      show "?m12_3 ! i ! j = ?m1_23 ! i ! j"
        by (simp only: mat_mult_index[OF wf12 wf3 j i],
             simp only: mat_mult_index[OF wf1 wf23 j i], 
             simp only: row_mat_mult_index[OF wf1 wf2 j],
             simp only: col_mat_mult_index[OF wf2 wf3 i], 
             simp only: scalar_product_assoc[OF wf2 row[OF wf1 j] col[OF wf3 i]])
    qed
  qed
qed

lemma mat_mult_assoc_n:  
  assumes wf1: "mat n n m1"
  and wf2: "mat n n m2"
  and wf3: "mat n n m3"
  shows "mat_mult n (mat_mult n m1 m2) m3 = mat_mult n m1 (mat_mult n m2 m3)"
using assms
 by (rule mat_mult_assoc)


lemma scalar_left_zero: "scalar_prod (vec0 nn) v = zero"
  unfolding vec0I_def scalar_prodI_def
proof (induct nn arbitrary: v)
  case (Suc m)
  thus ?case by (cases v, auto)
qed simp

lemma scalar_right_zero: "scalar_prod v (vec0 nn) = zero"
  unfolding vec0I_def scalar_prodI_def
proof (induct v arbitrary: nn)
  case (Cons a vv)
  thus ?case by (cases nn, auto)
qed simp

lemma mat0_mult_left: assumes wf: "mat nc ncc m"
  shows "mat_mult nr (mat0 nr nc) m = (mat0 nr ncc)"
proof (simp only: mat_eq_index[OF mat_mult[OF mat0 wf] mat0], intro allI impI)
  fix i j
  assume i: "i < ncc" and j: "j < nr"
  show "mat_mult nr (mat0 nr nc) m ! i ! j = mat0 nr ncc ! i ! j"
  by (simp only: mat_mult_index[OF mat0 wf j i], 
         simp only: mat0_index[OF i j], 
         simp only: mat0_row[OF j],
         simp only: scalar_left_zero)
qed


lemma mat0_mult_right: assumes wf: "mat nr nc m"
  shows "mat_mult nr m (mat0 nc ncc) = (mat0 nr ncc)"
proof (simp only: mat_eq_index[OF mat_mult[OF wf mat0] mat0], intro allI impI)
  fix i j
  assume i: "i < ncc" and j: "j < nr"
  show "mat_mult nr m (mat0 nc ncc) ! i ! j = mat0 nr ncc ! i ! j"
    by (simp only: mat_mult_index[OF wf mat0 j i],
         simp only: mat0_index[OF i j],
         simp only: mat0_col[OF i],
         simp only: scalar_right_zero)
qed

lemma scalar_vec_plus_distrib_right: 
  assumes wf1: "vec nr u"
  assumes wf2: "vec nr v"
  assumes wf3: "vec nr w"
  shows "scalar_prod u (vec_plus v w) = plus (scalar_prod u v) (scalar_prod u w)"
using assms
unfolding vec_def scalar_prodI_def vec_plusI_def
proof (induct nr arbitrary: u v w)
  case (Suc n)
  from Suc obtain a uu where u: "u = a # uu" by (cases u, auto)
  from Suc obtain b vv where v: "v = b # vv" by (cases v, auto)
  from Suc obtain c ww where w: "w = c # ww" by (cases w, auto)
  from Suc u v w have lu: "length uu = n" and lv: "length vv = n" and lw: "length ww = n" by auto
  show ?case by (simp only: u v w, simp, simp only: Suc(1)[OF lu lv lw], simp add: add_commute[of _ "times a c"] distrib_left add_assoc[symmetric])
qed simp

lemma scalar_vec_plus_distrib_left: 
  assumes wf1: "vec nr u"
  assumes wf2: "vec nr v"
  assumes wf3: "vec nr w"
  shows "scalar_prod (vec_plus u v) w = plus (scalar_prod u w) (scalar_prod v w)"
using assms
unfolding vec_def scalar_prodI_def vec_plusI_def
proof (induct nr arbitrary: u v w)
  case (Suc n)
  from Suc obtain a uu where u: "u = a # uu" by (cases u, auto)
  from Suc obtain b vv where v: "v = b # vv" by (cases v, auto)
  from Suc obtain c ww where w: "w = c # ww" by (cases w, auto)
  from Suc u v w have lu: "length uu = n" and lv: "length vv = n" and lw: "length ww = n" by auto
  show ?case by (simp only: u v w, simp, simp only: Suc(1)[OF lu lv lw], simp add: add_commute[of _ "times b c"] distrib_right add_assoc[symmetric])
qed simp

lemma mat_mult_plus_distrib_right: 
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nc ncc m2"
  and wf3: "mat nc ncc m3"
  shows "mat_mult nr m1 (mat_plus m2 m3) = mat_plus (mat_mult nr m1 m2) (mat_mult nr m1 m3)" (is "mat_mult nr m1 ?m23 = mat_plus ?m12 ?m13")
proof -
  let ?m1_23 = "mat_mult nr m1 ?m23"
  let ?m12_13 = "mat_plus ?m12 ?m13"
  from mat_plus[OF wf2 wf3] have wf23: "mat nc ncc ?m23" .
  from mat_mult[OF wf1 wf2] have wf12: "mat nr ncc ?m12" .
  from mat_mult[OF wf1 wf3] have wf13: "mat nr ncc ?m13" .
  from mat_mult[OF wf1 wf23] have wf1_23: "mat nr ncc ?m1_23" .
  from mat_plus[OF wf12 wf13] have wf12_13: "mat nr ncc ?m12_13" .
  show ?thesis 
  proof (simp only: mat_eq_index[OF wf1_23 wf12_13], intro impI allI)
    fix i j
    assume i: "i < ncc" and j: "j < nr"
    show "?m1_23 ! i ! j = ?m12_13 ! i ! j"
      by (simp only: mat_mult_index[OF wf1 wf23 j i],
           simp only: mat_plus_index[OF wf12 wf13 i j],
           simp only: mat_mult_index[OF wf1 wf2 j i],
           simp only: mat_mult_index[OF wf1 wf3 j i],
           simp only: col_mat_plus[OF wf2 wf3 i],
        rule scalar_vec_plus_distrib_right[OF row[OF wf1 j] col[OF wf2 i] col[OF wf3 i]])
  qed
qed

lemma mat_mult_plus_distrib_left: 
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  and wf3: "mat nc ncc m3"
  shows "mat_mult nr (mat_plus m1 m2) m3 = mat_plus (mat_mult nr m1 m3) (mat_mult nr m2 m3)" (is "mat_mult nr ?m12 _ = mat_plus ?m13 ?m23")
proof -
  let ?m12_3 = "mat_mult nr ?m12 m3"
  let ?m13_23 = "mat_plus ?m13 ?m23"
  from mat_plus[OF wf1 wf2] have wf12: "mat nr nc ?m12" .
  from mat_mult[OF wf1 wf3] have wf13: "mat nr ncc ?m13" .
  from mat_mult[OF wf2 wf3] have wf23: "mat nr ncc ?m23" .
  from mat_mult[OF wf12 wf3] have wf12_3: "mat nr ncc ?m12_3" .
  from mat_plus[OF wf13 wf23] have wf13_23: "mat nr ncc ?m13_23" .
  show ?thesis 
  proof (simp only: mat_eq_index[OF wf12_3 wf13_23], intro impI allI)
    fix i j
    assume i: "i < ncc" and j: "j < nr"
    show "?m12_3 ! i ! j = ?m13_23 ! i ! j"
      by (simp only: mat_mult_index[OF wf12 wf3 j i],
           simp only: mat_plus_index[OF wf13 wf23 i j],
           simp only: mat_mult_index[OF wf1 wf3 j i],
           simp only: mat_mult_index[OF wf2 wf3 j i],
           simp only: row_mat_plus[OF wf1 wf2 j],
           rule scalar_vec_plus_distrib_left[OF row[OF wf1 j] row[OF wf2 j] col[OF wf3 i]])
  qed
qed
end

context semiring_1
begin
abbreviation vec1 :: "nat \<Rightarrow> nat \<Rightarrow> 'a vec"
where "vec1 \<equiv> vec1I zero one"

abbreviation mat1 :: "nat \<Rightarrow> 'a mat"
where "mat1 \<equiv> mat1I zero one"

abbreviation mat_pow where "mat_pow \<equiv> mat_powI (0 :: 'a) 1 (op +) (op *)"


lemma scalar_left_one: assumes wf: "vec nn v"
  and i: "i < nn"
  shows "scalar_prod (vec1 nn i) v = v ! i"
  using assms 
  unfolding vec1I_def vec_def 
proof (induct nn arbitrary: v i)
  case (Suc n) note oSuc = this
  from this obtain a vv where v: "v = a # vv" and lvv: "length vv = n" by (cases v, auto)
  show ?case 
  proof (cases i)
    case 0
    thus ?thesis using scalar_left_zero unfolding vec0I_def by (simp add: v scalar_prod_cons add_commute)
  next
    case (Suc ii)
    thus ?thesis using oSuc lvv v by (auto simp: scalar_prod_cons)
  qed
qed blast


lemma scalar_right_one: assumes wf: "vec nn v"
  and i: "i < nn"
  shows "scalar_prod v (vec1 nn i) = v ! i"
  using assms 
  unfolding vec1I_def vec_def 
proof (induct nn arbitrary: v i)
  case (Suc n) note oSuc = this
  from this obtain a vv where v: "v = a # vv" and lvv: "length vv = n" by (cases v, auto)
  show ?case 
  proof (cases i)
    case 0
    thus ?thesis using scalar_right_zero unfolding vec0I_def by (simp add: v scalar_prod_cons add_commute)
  next
    case (Suc ii)
    thus ?thesis using oSuc lvv v by (auto simp: scalar_prod_cons)
  qed
qed blast


lemma mat1_mult_right: assumes wf: "mat nr nc m"
  shows "mat_mult nr m (mat1 nc) = m"
proof (simp only: mat_eq_index[OF mat_mult[OF wf mat1] wf], intro allI impI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  show "mat_mult nr m (mat1 nc) ! i ! j = m ! i ! j"
    by (simp only: mat_mult_index[OF wf mat1 j i],
    simp only: col_mat1[OF i],
    simp only: scalar_right_one[OF row[OF wf j] i],
    simp only: row_col[OF wf j i],
    unfold col_def, simp)
qed


lemma mat1_mult_left: assumes wf: "mat nr nc m"
  shows "mat_mult nr (mat1 nr) m = m"
proof (simp only: mat_eq_index[OF mat_mult[OF mat1 wf] wf], intro allI impI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  show "mat_mult nr (mat1 nr) m ! i ! j = m ! i ! j"
    by (simp only: mat_mult_index[OF mat1 wf j i],
      simp only: row_mat1[OF j],
      simp only: scalar_left_one[OF col[OF wf i] j], unfold col_def, simp)
qed
end


declare vec0[simp del] mat0[simp del] vec0_plus[simp del] plus_vec0[simp del] plus_mat0[simp del]
(*Matrix Tensor begins*)

locale mult = 
 fixes f::" 'a \<Rightarrow> 'a \<Rightarrow> 'a " (infixl "*" 60)
 assumes comm:" f a  b = f b  a "
 assumes assoc:" (f (f a b) c) = (f a (f b c))"
context mult
begin   
 
primrec times:: "'a \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
where
"times n [] = []"|
"times n (y#ys) = (f n y)#(times n ys)"

lemma preserving_length: "length (times n y) = (length y)"
apply(induct_tac y)
apply(auto)
done

primrec product:: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
where
"product [] ys = []"|
"product (x#xs) ys = (times x ys)@(product xs ys)"

theorem product_length : 
 "(length(product x y)) = (length x)*(length y)"
apply(induct_tac x)
apply(auto)
apply(simp add: preserving_length)
done

theorem vec_length: assumes "vec m x" and "vec n y"
shows "vec (m*n) (product x y)"
apply(simp add:vec_def)
apply(simp add:product_length)
apply (metis assms(1) assms(2) vec_def)
done

primrec list_tensor::"'a vec \<Rightarrow> 'a mat \<Rightarrow>'a mat"
where
"list_tensor xs []  = []"|
"list_tensor xs (ys#yss) = (product xs ys)#(list_tensor xs yss)"


theorem list_tensor_length : 
 "(length(list_tensor xs ys)) = (length ys)"
apply(induct_tac ys)
apply(auto)
done

theorem length_matrix: assumes "mat nr nc (y#ys)" and "length v = k"
and "(list_tensor v (y#ys) = x#xs)" 
 shows "(vec (nr*k) x)" 
proof-
have "list_tensor v (y#ys) = (product v y)#(list_tensor v ys)"  using list_tensor_def assms by auto
also have "(product v y) = x" using assms by auto
also have "length y = nr" using assms mat_def by (metis in_set_member member_rec(1) vec_def)
from this
 have "length (product v y) = nr*k" using assms product_length nat_mult_commute by auto
from this have "length x = nr*k" by (simp add: `product v y = x`)
from this have "vec (nr*k) x" using vec_def by auto
from this show ?thesis by auto
qed

lemma matrix_set_list: assumes "mat nr nc M" and "length v = k"
and " x \<in> set M" 
 shows "\<exists>ys.\<exists>zs.(ys@x#zs = M)" using assms set_def in_set_conv_decomp by metis

primrec reduct :: "'a mat \<Rightarrow> 'a mat"
where
"reduct [] = []"
|"reduct (x#xs) = xs"

lemma length_reduct: assumes "m \<noteq> []"
shows "length (reduct m) +1  = (length m)"
apply(auto)
by (metis One_nat_def Suc_eq_plus1 assms list.size(4) neq_Nil_conv reduct.simps(2))

lemma mat_empty_column_length: assumes "mat nr nc M" and "M = []"
shows "nc = 0" 
proof-
have "(length M = nc)" using mat_def assms by metis
from this have "nc = 0" using assms by auto
from this show ?thesis by simp
qed

lemma vec_uniqueness: assumes "vec m v" and "vec n v" shows 
"m = n"
using vec_def assms(1) assms(2)  by metis

lemma mat_uniqueness: assumes "mat nr1 nc M" and "mat nr2 nc M" and "z = hd M" and "M \<noteq> []"
shows "(\<forall>x\<in>(set M).(nr1 = nr2))" 
proof-
 have A:"z \<in> set M" using assms(1) assms(3) assms(4) set_def mat_def by (metis hd_in_set)
 have "Ball (set M) (vec nr1)" using mat_def assms(1) by auto 
  from this have step1: "((x \<in> (set M)) \<longrightarrow> (vec nr1 x))" using Ball_def assms by auto
  have "Ball (set M) (vec nr2)" using mat_def assms(2) by auto
  from this have step2: "((x \<in> (set M)) \<longrightarrow> (vec nr2 x))" using Ball_def assms by auto
  from step1 and step2 have step3:"\<forall>x.((x \<in> (set M))\<longrightarrow> ((vec nr1 x)\<and> (vec nr2 x)))"
  by (metis `Ball (set M) (vec nr1)` `Ball (set M) (vec nr2)`)
  have "((vec nr1 x)\<and> (vec nr2 x)) \<longrightarrow> (nr1 = nr2)" using vec_uniqueness by auto
  from this and step3  have "(\<forall>x.((x \<in> (set M)) \<longrightarrow>((nr1 = nr2))))" by 
 (metis vec_uniqueness) 
 from this have "(\<forall>x\<in>(set M).(nr1 = nr2))" by auto 
 from this show ?thesis by auto
qed

 
lemma mat_empty_row_length: assumes "mat nr nc M" and "M = []"
shows "mat 0 nc M" 
proof-
have "set M = {}" using mat_def assms  empty_set  by auto
from this have "Ball (set M) (vec 0)" using Ball_def by auto
from this have "mat 0 nc M" using mat_def assms(1) assms(2) gen_length_code(1) length_code
 by (metis (full_types) )
from this show ?thesis by auto
qed

abbreviation null_matrix::"'a list list"
where
"null_matrix \<equiv> [Nil] "

lemma zero_matrix:" mat 0 0 []" using mat_def in_set_insert insert_Nil list.size(3) not_Cons_self2
 by (metis (full_types))

definition row_length:: "'a mat \<Rightarrow> nat"
where
"row_length xs \<equiv> if (xs = []) then 0 else (length (hd xs))"

lemma row_length_Nil: "row_length [] =0" using row_length_def by (metis )

lemma row_length_vect_mat: " row_length (list_tensor v m) = length v*(row_length m)"
proof(induct m)
 case Nil
  have "row_length [] = 0" using row_length_Nil by simp
  moreover have "list_tensor v [] = []" using list_tensor.simps(1) by auto 
  ultimately have " row_length (list_tensor v []) = length v*(row_length [])" using mult_0_right by (metis )
  from this show ?case by metis
 next  
  fix a m
  assume A:"row_length (list_tensor v m) = length v * row_length m"
  let ?case = "row_length (list_tensor v (a#m)) = (length v)*(row_length (a#m))" 
  have A:"row_length (a # m) = length a" using row_length_def by (metis hd.simps list.distinct(1))
  have "(list_tensor v  (a#m)) = (product v a)#(list_tensor v m)" using list_tensor_def list_tensor.simps(2)
  by auto
  from this have "row_length (list_tensor v (a#m)) = length (product v a)" using row_length_def  hd.simps
  by (metis list.distinct(1) list_tensor.simps(2))
  from this and product_length have "row_length (list_tensor v (a#m)) = (length v)*(length a)" by auto
  from this and A  have "row_length (list_tensor v (a#m)) = (length v)*(row_length (a#m))"
  by auto
  from this show ?case by auto
qed

primrec tensor::" 'a mat \<Rightarrow> 'a mat \<Rightarrow>'a mat" (infixl "\<otimes>" 63)
where
"tensor [] xs = []"|
"tensor (x#xs) ys = (list_tensor x ys)@(tensor xs ys)"

lemma tensor_null: "xs \<otimes>[] = []" 
apply(induct_tac xs)
apply(auto)
done

lemma hd_append:  assumes "xs \<noteq> []" shows "hd (xs@ys) = hd xs" using hd_def hd_append2 append_def 
apply(induct_tac ys)
apply(auto)
by (metis assms hd_append2)

lemma row_length_mat: "(row_length (m1\<otimes>m2)) = (row_length m1)*(row_length m2)"
proof(induct m1)
 case Nil
   have "row_length ([]\<otimes>m2) = 0" using tensor.simps(1) row_length_def by metis
   from this have "row_length ([]\<otimes>m2) = (row_length [])*(row_length m2)"  
        by (metis comm_semiring_1_class.normalizing_semiring_rules(9) row_length_Nil)
   then show ?case by metis
 next
 fix a m1 
 assume "row_length (m1 \<otimes> m2) = row_length m1 * row_length m2"
 let ?case = "row_length ((a # m1) \<otimes> m2) = row_length (a # m1) * row_length m2"
 have B: "row_length (a#m1) = length a" using row_length_def by (metis hd.simps list.distinct(1))
 have "row_length ((a # m1) \<otimes> m2) = row_length (a # m1) * row_length m2"
   proof(induct m2)
   case Nil
    show ?case using tensor_null row_length_def by (metis mult_0_right)
   next
    fix aa m2
    assume "row_length (a # m1 \<otimes> m2) = row_length (a # m1) * row_length m2"
    let ?case= " row_length (a # m1 \<otimes> aa # m2) = row_length (a # m1) * row_length (aa # m2)"
    have "aa#m2 \<noteq> []" by auto
    from this have "(list_tensor a (aa#m2)) \<noteq> []" using list_tensor_def by auto
    from this have "hd ((list_tensor a (aa#m2))@(m1\<otimes>m2))= hd (list_tensor a (aa#m2)) " by auto

    from this have "hd ((a#m1)\<otimes>(aa#m2)) = hd (list_tensor a (aa#m2))" using tensor.simps(2) by auto
    from this have s1: "row_length ((a#m1)\<otimes>(aa#m2)) = row_length (list_tensor a (aa#m2))" 
           using row_length_def by (metis Nil_is_append_conv `list_tensor a (aa # m2) \<noteq> []` tensor.simps(2))
    have "row_length (list_tensor a (aa#m2)) = (length a)*row_length(aa#m2)" using row_length_vect_mat
    by metis   
    from this and s1  
     have "row_length (list_tensor a (aa#m2)) = (length a)*row_length(aa#m2)"
         by auto
   from this and B have "row_length (list_tensor a (aa#m2)) = (row_length (a#m1))*row_length(aa#m2)"    
        by auto
   from this  and s1 show ?case  by (auto)
   qed
  from this show ?case by auto
 qed

lemma hd_set:assumes "x \<in> set (a#M)" shows "(x = a) \<or> (x\<in>(set M))"
             using set_def assms set_ConsD  by auto


theorem matrix_row_length: assumes "mat nr nc M" 
shows "mat (row_length M) (length M) M"
proof(cases M)
case Nil
 have "row_length M= 0 " using row_length_def by (metis Nil)
 moreover have "length M = 0" by (metis Nil list.size(3))
 moreover  have "mat 0 0 M" using zero_matrix Nil by auto 
 ultimately show ?thesis  using mat_empty_row_length row_length_def mat_def  by metis
next
case (Cons a N) 
 have 1: "mat nr nc (a#N)" using assms Cons by auto
 from this have "(x \<in> set (a #N)) \<longrightarrow> (x = a) \<or> (x \<in> (set N))" using hd_set by auto
 from this and 1 have 2:"vec nr a" using  mat_def by (metis Ball_set_list_all list_all_simps(1))
 have "row_length (a#N) = length a" using row_length_def Cons hd.simps list.distinct(1) by metis
 from this have " vec (row_length (a#N)) a" using vec_def by auto
 from this and 2 have 3:"(row_length M)  = nr" using vec_uniqueness Cons by auto
 have  " nc = (length M)" using 1 and mat_def and assms by metis
 from this and 3 have "mat (row_length M) (length M) M" using assms by auto 
 from this show ?thesis by auto
qed

lemma reduct_matrix: assumes "mat (row_length (a#M)) (length (a#M)) (a#M)"
shows "mat (row_length M) (length M) M"
proof(cases M)
 case Nil
   show ?thesis using row_length_def zero_matrix Nil by (metis list.size(3))
 next   
 case (Cons b N)
  have 1: "b \<in> (set M)" using set_def  Cons ListMem_iff elem  by auto
  have "mat (row_length (a#M)) (length (a#M)) (a#M)" using assms by auto
  from this have "(x \<in> (set (a#M))) \<longrightarrow> ((x = a) \<or> (x \<in> set M))" by auto
  from this have " (x \<in> (set (a#M))) \<longrightarrow> (vec (row_length (a#M)) x)" using mat_def Ball_def assms 
      by metis
  from this have "(x \<in> (set (a#M))) \<longrightarrow> (vec (length a) x)" using row_length_def 
      by (metis hd.simps list.distinct(1))
  from this have 2:"x \<in> (set M) \<longrightarrow> (vec (length a) x)" by auto
  from this and 1 have 3:"(vec (length a) b)" by (metis assms in_set_member mat_def member_rec(1) vec_def) 
  have 5: "(vec (length b) b)" using vec_def by auto
  from this and 3 have "(length a) = (length b)" using vec_uniqueness by auto
  from this and 2 have 4: "x \<in> (set M) \<longrightarrow> (vec (length b) x)" by auto
  have 6:"row_length M = (length b)" using row_length_def hd.simps by (metis Cons list.distinct(1))
  from this and 4 have "x \<in> (set M) \<longrightarrow> (vec (row_length M) x)" by auto
  from this have "(\<forall>x. (x \<in> (set M) \<longrightarrow> (vec (row_length M) x)))" by (metis Cons 5 6
   assms in_set_member mat_def member_rec(1) vec_uniqueness)
  from this have "Ball (set M) (vec (row_length M))" using Ball_def by auto
  from this have "(mat (row_length M) (length M) M)" using mat_def by auto
  from this show ?thesis by auto
  qed 

theorem well_defined_list_tensor:
"(mat (row_length M) (length M) M) \<Longrightarrow>(mat ((row_length M)*(length v)) (length M) (list_tensor v M))"
proof(induct M) 
 case Nil
  have "(list_tensor v []) = []" using list_tensor.simps(1) Nil  by simp
  moreover have "(row_length [] = 0)"  using row_length_def Nil by metis
  moreover have "(length []) = 0" using Nil by simp
  ultimately have "mat ((row_length [])*(length v)) (length []) (list_tensor v [])" using zero_matrix by (metis mult_zero_left)
  from this show ?case by simp
 next
 fix a M
 assume hyp :"(mat (row_length M) (length M) M \<Longrightarrow> mat (row_length M * length v) (length M) (list_tensor v M))"
               " mat (row_length (a#M)) (length (a#M)) (a#M)"                      
  let ?case = "mat (row_length (a#M) * length v) (length (a#M)) (list_tensor v (a#M))"
  have step1: "mat (row_length M) (length M) M" using hyp(2) reduct_matrix by auto
  from this have step2:"mat (row_length M * length v) (length M) (list_tensor v M)" using hyp(1) by auto 
  have "mat (row_length (a#M) * length v) (length (a#M)) (list_tensor v (a#M))" 
    proof (cases M)
         case Nil 
     have 1:"(list_tensor v (a#M)) = [product v a]" using list_tensor.simps Nil by auto
     have   "(x \<in> (set [product v a])) \<longrightarrow>  x = (product v a)" using set_def by auto
     from this have 2:" (x \<in> (set [product v a])) \<longrightarrow> (vec (length (product v a)) x)" using vec_def by metis 
     have "length (product v a) = (length v)*(length a)" using product_length by auto 
     from this have "length (product v a) = (length v)*(row_length (a#M))" using row_length_def hd.simps
     list.distinct(1) by metis
     from this and 2 have "(x \<in> (set [product v a])) \<longrightarrow> (vec ((length v)*(row_length (a#M))) x)" by auto
     from this and 1 have 3:"(x \<in> set (list_tensor v (a#M))) \<longrightarrow> vec ((length v)*(row_length (a#M))) x" 
     by auto
     have 4: "length (list_tensor v (a#M)) = (length (a#M))" using list_tensor_length by auto
     from this have "mat (row_length (a#M) * length v) (length (list_tensor v (a#M))) (list_tensor v (a#M))"
     using mat_def Ball_def by (metis (hide_lams, no_types) 
    "1" `length (product v a) = length v * row_length (a # M)` `length (product v a) = length v * length a` 
    hd_set in_set_insert insert_Nil length_code nat_mult_commute not_Cons_self2 product_length vec_def)
     from this show ?thesis using 4 by auto
     next 
     case (Cons b L)
      have 1:"x \<in> (set (a#M)) \<longrightarrow> ((x=a) \<or> (x \<in> (set M)))" using hd_set by auto
      have "mat (row_length (a#M)) (length (a#M)) (a#M)" using hyp by auto
      from this have "x\<in> (set (a#M)) \<longrightarrow> (vec (row_length (a#M)) x)" using mat_def Ball_def by metis
      from this have "x\<in> (set (a#M))\<longrightarrow> (vec (length a) x)" using row_length_def hd.simps list.distinct(1)
      by (metis ) 
      from this and 1 have "x\<in> (set M)\<longrightarrow> (vec (length a) x)" by auto
      moreover have " b \<in> (set M)" using Cons by auto
      ultimately have "vec (length a) b" by (metis hyp(2) in_set_member mat_def member_rec(1) vec_def) 
      from this have "(length b) = (length a)" using vec_def vec_uniqueness by auto
      from this have 2:"row_length M = (length a)" using row_length_def hd.simps by (metis Cons list.distinct(1)) 
      
      have "  mat (row_length M * length v) (length M) (list_tensor v M)" using step2 by auto 
      from this have " Ball (set (list_tensor v M)) (vec ((row_length M)*(length v)))" using mat_def by auto
      from this have "(x \<in> set (list_tensor v M)) \<longrightarrow> (vec ((row_length M)*(length v)) x)" using mat_def Ball_def
      by auto
      from this have 3:" (x \<in> set (list_tensor v M)) \<longrightarrow> (vec ((length a)*(length v)) x)" using 2 by auto
  
      have "length (product v a) = (length a)*(length v)" by (metis nat_mult_commute product_length)  
      from this  have 4:" vec ((length a)*(length v)) (product v a)" using product_length vec_def 
             by (metis (full_types))

      have 5:"(length a) = (row_length (a#M))" using row_length_def hd.simps  list.distinct(1)  by (metis) 
 
      have "list_tensor v (a#M) = (product v a)#(list_tensor v M)" using list_tensor.simps(2) by auto
      from this have "(x \<in> set (list_tensor v (a#M)))\<longrightarrow> ((x = (product v a)) \<or> (x \<in> (set (list_tensor v M)))) "
      using hd.simps hd_set by auto
      from this 3 4 have "(x \<in> set (list_tensor v (a#M)))\<longrightarrow>  vec ((length a)*(length v)) x" by auto
      from this 5 have "(x \<in> set (list_tensor v (a#M)))\<longrightarrow>  vec ((row_length (a#M))*(length v)) x" by auto
      from this have "\<forall>x.((x \<in> set (list_tensor v (a#M)))\<longrightarrow>  vec ((row_length (a#M))*(length v)) x)"
       by (metis "2" "4" "5" `Ball (set (list_tensor v M)) (vec (row_length M * length v))` 
      hd_set list_tensor.simps(2))
      from this have 6: "Ball (set (list_tensor v (a#M))) (vec ((row_length (a#M))*(length v)))" using Ball_def by 
      auto
      have 7:"length (list_tensor v (a#M)) = length (a#M)" using list_tensor_length by auto
    
      from 6 and 7 have "mat ((row_length (a#M))*(length v)) (length (a#M)) (list_tensor v (a#M))"
        using mat_def
        by (metis (hide_lams, no_types) "5" `length (product v a) = length a * length v` length_code)
     from this show ?thesis by auto
     qed
    from hyp this show ?case by auto  
qed


lemma length_tensor:" (length (M1\<otimes>M2)) = (length M1)*(length M2)"
proof(induct M1)
 case Nil
  show ?case by auto
 next
 case (Cons a M1)
 have "((a # M1) \<otimes> M2) = (list_tensor a M2)@(M1 \<otimes> M2)" using tensor.simps(2) by auto
 from this have 1:"length ((a # M1) \<otimes> M2) = length ((list_tensor a M2)@(M1 \<otimes> M2))" by auto
 have 2:"length ((list_tensor a M2)@(M1 \<otimes> M2)) = length (list_tensor a M2)+ length (M1 \<otimes> M2)" using append_def
 by auto
 have 3:"(length (list_tensor a M2)) = length M2" using list_tensor_length by (auto)
 have 4:"length (M1 \<otimes> M2) = (length M1)*(length M2)" using  Cons.hyps by auto
 from this 2 3 have  "length ((list_tensor a M2)@(M1 \<otimes> M2)) =  (length M2) + (length M1)*(length M2)"
 by auto
 from this have 5:"length ((list_tensor a M2)@(M1 \<otimes> M2)) =  (1 + (length M1))*(length M2)" by auto
 have "length (a#M1) = 1+(length M1)" by auto
 from this have "((length (a # M1)) * (length M2)) = (1 + (length M1))*(length M2)" by auto 
 from 1 5 this have "length ((a # M1) \<otimes> M2) = ((length (a # M1)) * (length M2))" by auto
 from this show ?case by auto
qed


lemma append_reduct_matrix: 
"(mat (row_length (M1@M2)) (length (M1@M2)) (M1@M2))
\<Longrightarrow>(mat (row_length M2) (length M2) M2)"
proof(induct M1)
case Nil
 show ?thesis using Nil append.simps(1) by auto
next
case (Cons a M1)
 have "mat (row_length (M1 @ M2)) (length (M1 @ M2)) (M1 @ M2)" using reduct_matrix Cons.prems 
   append_Cons by metis
 from this have "(mat (row_length M2) (length M2) M2)" using Cons.hyps by auto
 from this show?thesis by simp
qed
(*proves that tensor product takes well defined matrices to well defined matrices*)
theorem well_defined_tensor:
"(mat (row_length M1) (length M1) M1) \<and> (mat (row_length M2) (length M2) M2)
\<Longrightarrow>(mat ((row_length M1)*(row_length M2)) ((length M1)*(length M2)) (M1\<otimes>M2))"
proof(induct M1)
 case Nil
  have "(row_length []) * (row_length M2) = 0" using row_length_def  mult_zero_left  by (metis)
  moreover have "(length []) * (length M2) = 0" using  mult_zero_left list.size(3) by auto 
  moreover have "[] \<otimes> M2 = []" using tensor.simps(1) by auto
  ultimately have "mat (row_length [] * row_length M2) (length [] * length M2) ([] \<otimes> M2)"
     using zero_matrix by metis
  from this show ?case by simp
 next
 case (Cons a M1)
 have step1: "mat (row_length (a # M1)) (length (a # M1)) (a # M1)" using Cons.prems by auto
 then have "mat (row_length (M1)) (length (M1)) (M1)" using reduct_matrix by auto
 moreover have "mat (row_length (M2)) (length (M2)) (M2)" using Cons.prems by auto
 ultimately have step2:"mat (row_length M1 * row_length M2) (length M1 * length M2) (M1 \<otimes> M2)"
 using Cons.hyps by auto
 have 0:"row_length (a#M1) = length a" using row_length_def hd.simps list.distinct(1)  
      by metis
 have "mat (row_length (a # M1) * row_length M2) (length (a # M1) * length M2) (a # M1 \<otimes> M2)"
  proof(cases M1)
   case Nil 
    have "(mat ((row_length M2)*(length a)) (length M2) (list_tensor a M2))" using Cons.prems 
    well_defined_list_tensor by auto
    moreover have "(length (a # M1)) * (length M2) = length M2" using Nil by auto
    moreover have "(a#M1)\<otimes>M2 = (list_tensor a M2)" using Nil tensor.simps append.simps(1) by auto
    ultimately have "(mat ((row_length M2)*(row_length (a#M1))) ((length (a # M1)) * (length M2))
               ((a#M1)\<otimes>M2))" using 0
             by auto
    from this show ?thesis using nat_mult_commute by metis
  next
  case (Cons b N1)
     have 1:"x \<in> (set (a#M1)) \<longrightarrow> ((x=a) \<or> (x \<in> (set M1)))" using hd_set by auto
     have "mat (row_length (a#M1)) (length (a#M1)) (a#M1)" using Cons.prems by auto
     from this have "x\<in> (set (a#M1)) \<longrightarrow> (vec (row_length (a#M1)) x)" using mat_def Ball_def by metis
      from this have "x\<in> (set (a#M1))\<longrightarrow> (vec (length a) x)" using row_length_def hd.simps list.distinct(1)
      by (metis ) 
      from this and 1 have "x\<in> (set M1)\<longrightarrow> (vec (length a) x)" by auto
      moreover have " b \<in> (set M1)" using Cons by auto
      ultimately have "vec (length a) b" by (metis Cons.prems in_set_member mat_def member_rec(1) vec_def)
      from this have "(length b) = (length a)" using vec_def vec_uniqueness by auto
      from this have 2:"row_length M1 = (length a)" using row_length_def hd.simps by (metis Cons list.distinct(1)) 
      from this have "mat ((length a) * row_length M2) (length M1 * length M2) (M1 \<otimes> M2)" using step2
      by auto
      from this have "Ball (set (M1\<otimes>M2)) (vec ((length a)*(row_length M2))) " using mat_def by auto     
      from this have 3:"\<forall>x. x \<in> (set (M1 \<otimes> M2)) \<longrightarrow> (vec ((length a)*(row_length M2)) x)" using Ball_def by auto
    
    
      have "(mat ((row_length M2)*(length a)) (length M2) (list_tensor a M2))" using well_defined_list_tensor
       Cons.prems by auto
      from this have "Ball (set (list_tensor a M2)) (vec ((row_length M2)*(length a)))" using mat_def
         by auto
      from this have 4:"\<forall>x. x \<in> (set (list_tensor a M2)) \<longrightarrow> (vec ((length a)*(row_length M2)) x)"
           using  nat_mult_commute by metis
      from this and 3 have 5: "\<forall>x. (x \<in> (set (list_tensor a M2)))\<or>(x \<in> (set (M1 \<otimes> M2))) 
                         \<longrightarrow> (vec ((length a)*(row_length M2)) x)"     by auto  

       have 6:"(a # M1 \<otimes> M2) = (list_tensor a M2)@(M1 \<otimes>M2)" using tensor.simps(2) by auto 
       from this have "x \<in> (set (a # M1 \<otimes> M2)) 
        \<longrightarrow> (x \<in> (set (list_tensor a M2)))\<or>(x \<in> (set (M1 \<otimes> M2)))"
           using set_def append_def by auto
       from this and 5 have "\<forall>x. (x \<in>  (set (a # M1 \<otimes> M2)))
                         \<longrightarrow> (vec ((length a)*(row_length M2)) x)" by auto
       from this have 7:"Ball (set (a # M1 \<otimes> M2)) (vec ((row_length (a#M1))*(row_length M2)))" 
       using Ball_def 0 by auto
   
       have "(length ((a#M1)\<otimes>M2)) = (length (a#M1))*(length M2)" using length_tensor by metis
       from this and 7 
           have "mat (row_length (a # M1) * row_length M2) (length (a # M1) * length M2) (a # M1 \<otimes> M2)"
             using mat_def by (metis "0" `\<forall>x. x \<in> set (a # M1 \<otimes> M2) \<longrightarrow> vec (length a * row_length M2) x` length_tensor)
       from this show ?thesis by auto
       qed
     from this show ?case by auto
   qed


theorem effective_well_defined_tensor:
assumes "(mat (row_length M1) (length M1) M1)" and "(mat (row_length M2) (length M2) M2)"
shows "(mat ((row_length M1)*(row_length M2)) ((length M1)*(length M2)) (M1\<otimes>M2))"
using well_defined_tensor assms by auto

definition natmod::"nat \<Rightarrow> nat \<Rightarrow> nat" (infixl "nmod" 50)
where
 "natmod x y = nat ((int x) mod (int y))"

theorem times_elements:
"\<forall>i.((i<(length v)) \<longrightarrow> (times a v)!i = f a (v!i))"
apply(rule allI)
proof(induct v)
case Nil
have "(length [] = 0)" by auto
from this have "i <(length []) \<Longrightarrow> False" by auto
moreover have "(times a []) = []" using times.simps(1) by auto 
ultimately have "(i<(length [])) \<longrightarrow> (times a [])!i = f a ([]!i)" by auto
from this have "\<forall>i. ((i<(length [])) \<longrightarrow> (times a [])!i = f a ([]!i))" by auto
from this show ?case  by auto
next
case (Cons x xs)
have "\<forall>i.((x#xs)!(i+1) = (xs)!i)" by auto

have 0:"((i<length (x#xs))\<longrightarrow> ((i<(length xs)) \<or> (i = (length xs))))" by auto
have 1:" ((i<length xs) \<longrightarrow>((times a xs)!i = f a (xs!i)))" by (metis Cons.hyps)
have "\<forall>i.((x#xs)!(i+1) = (xs)!i)" by auto
have "((i <length (x#xs)) \<longrightarrow>(times a (x#xs))!i = f a ((x#xs)!i))"  
 proof(cases i)
   case 0
    have "((times a (x#xs))!i) = f a x" using 0 times.simps(2) by auto
    from this have "(times a (x#xs))!i = f a ((x#xs)!i)" using 0 by auto
    from this show ?thesis by auto
    next
  case (Suc j)
    have 1:" (times a (x#xs))!i = ((f a x)#(times a xs))!i" using times.simps(2) by auto 
    have 2:"((f a x)#(times a xs))!i = (times a xs)!j" using Suc by auto
    have 3:"(i <length (x#xs)) \<longrightarrow> (j<length xs)" using One_nat_def Suc Suc_eq_plus1 list.size(4) not_less_eq 
    by metis
    have 4:"(j<length xs) \<longrightarrow> ((times a xs)!j = (f a (xs!j)))" using 1 by (metis Cons.hyps)
    have 5:"(x#xs)!i = (xs!j)" using Suc by (metis nth_Cons_Suc)
    from 1 2 4 5 have " (j<length xs) \<longrightarrow> ((times a (x#xs))!i = (f a ((x#xs)!i)))" by auto
    from 3 and this have "(i <length (x#xs)) \<longrightarrow> ((times a (x#xs))!i = (f a ((x#xs)!i)))" by auto
    from this show ?thesis  by auto
   qed
from this show ?case by auto
qed

lemma simpl_times_elements:assumes "(i<length xs)" shows "((i<(length v)) \<longrightarrow> (times a v)!i = f a (v!i))"
using times_elements by auto

(*preparatory lemmas*)
lemma append_simpl: "i<(length xs) \<longrightarrow> (xs@ys)!i = (xs!i)" 
using nth_append  by metis

lemma append_simpl2: "i \<ge>(length xs) \<longrightarrow> (xs@ys)!i = (ys!(i- (length xs)))" 
using nth_append less_asym  leD  by metis

lemma append_simpl3: 
assumes "i > (length y)"
shows " ((i <((length (z#zs))*(length y)))) \<longrightarrow> ((i - (length y))< (length zs)*(length y))"
proof-
have "length (z#zs) = (length zs)+1" by auto
from this have "(i <((length (z#zs))*(length y))) \<longrightarrow> (i <(((length zs)+1)*(length y)))"
by auto
from this have 1: "(i <((length (z#zs))*(length y))) \<longrightarrow> (i <((length zs)*(length y)+ (length y)))" by auto
have " (i <((length zs)*(length y)+ (length y))) = ((i - (length y)) <((length zs)*(length y)))"
using assms by auto
from this have "(i <((length (z#zs))*(length y))) \<longrightarrow> ((i - (length y)) <((length zs)*(length y)))"
by auto
from this show ?thesis by auto
qed

lemma append_simpl4: "
(i > (length y))
\<longrightarrow> ((i <((length (z#zs))*(length y)))) \<longrightarrow> ((i - (length y))< (length zs)*(length y))"
using append_simpl3 by auto

lemma product_simpl: "i<(length y) \<longrightarrow> (product (z#zs) y)!i = (times z y)!i" 
proof-
have a: "product (z#zs) y = (times z y)@(product zs y)" by auto
from this have b: "length (times z y) = (length y)" using preserving_length by auto
from this have "i<(length (times z y)) \<longrightarrow> ((times z y)@(product zs y))!i = (times z y)!i" using append_simpl
by metis
from this b have "i<(length y) \<longrightarrow> ((times z y)@(product zs y))!i = (times z y)!i" by auto
from this a have "i<(length y) \<longrightarrow> (product (z#zs) y)!i = (times z y)!i" by auto
from this show ?thesis by auto
qed


lemma product_simpl2: "(i \<ge> (length y)) \<longrightarrow> ((product (z#zs) y)!i = (product zs y)!(i- (length y)))" 
using product.simps(2) append_simpl2  preserving_length by metis

lemma division_product: 
assumes "(b::int)>0"
and "a>b"
shows " (a div b) = ((a - b) div b) + 1"
proof-
have " a -b > 0" using assms(2) by auto
have 1: "a - b = a + (-1)*b" by auto
have "(b \<noteq> 0) \<longrightarrow> ((a + b * c) div b = c + a div b)" using div_mult_self2 by auto
have "(b \<noteq> 0) \<longrightarrow> ((a + b * (-1)) div b = (-1) + a div b)" using div_mult_self2 by metis
from this 1 assms(1) have "((a - b) div b) = (-1) + a div b" using  
comm_semiring_1_class.normalizing_semiring_rules(7) less_int_code(1)
by metis
from this have "(a div b) = ((a - b) div b) + 1" by auto
from this show ?thesis by auto
qed

lemma int_nat_div: " (int a) div (int b) = int ((a::nat) div b)"
by (metis zdiv_int)

lemma int_nat_eq: assumes "int (a::nat) = int b"
shows "a = b" by (metis assms of_nat_eq_iff)

lemma nat_div: assumes "(b::nat) > 0" and "a>b"
shows "(a div b) = ((a - b) div b) + 1"
proof-
have 1:"(int b)>0" using assms(1) division_product by auto
moreover have "(int a)>(int b)" using assms(2) by auto
from this 1 have 2: " ((int a) div (int b)) = (((int a) - (int b)) div (int b)) + 1" using division_product
by auto
from int_nat_div have 3: "((int a) div (int b)) = int ( a div b)" by auto
from int_nat_div  assms(2) have 4: "(((int a) - (int b)) div (int b)) = int ((a - b) div b)" by (metis (full_types) less_asym not_less of_nat_diff)
have " (int x) + 1 = int (x +1)" by auto
from this 2 3 4 have "int (a div b) = int (((a - b) div b) + 1)" by auto
from this int_nat_eq have "(a div b) = ((a - b) div b) + 1" by auto
from this show ?thesis by auto
qed

lemma mod_eq:" (m::int) mod n = (m + (-1)*n) mod n"
using mod_mult_self1 by metis

lemma nat_mod_eq: "(int (m::nat)) mod (int n) = int ( m mod n)"
using Divides.transfer_int_nat_functions(2) by auto 

lemma nat_mod: assumes  "(m::nat) > n"
shows "(m::nat) mod n = (m -n) mod n"
using assms mod_if not_less_iff_gr_or_eq by auto 

lemma logic: assumes "A \<longrightarrow> B" and "\<not>A \<longrightarrow> B" shows "B" using assms(1) assms(2) by auto

theorem product_elements:
assumes " (y \<noteq> [])"
shows 
"\<forall>i.((i<((length x)*(length y)))
\<longrightarrow> ((product x y)!i) = f (x!(i div (length y))) (y!(i mod (length y))))"
 apply(rule allI)
 proof(induct x)
 case Nil
 have "(length [] = 0)" by auto
 also have "length (product [] y) = 0" using product.simps(1) by auto
 from this have "i <(length (product [] y)) \<Longrightarrow> False" by auto
 moreover have "(product [] y) = []" by auto 
 moreover have "(i<(length (product [] y))) \<longrightarrow> 
 ((product x y)!i) = f (x!(i div (length y))) (y!(i mod (length y)))"  
 by auto
 from this show ?case  by auto
 next
 case (Cons z zs)
 have 1:"product (z#zs) y = (times z y)@(product zs y)" by auto
 have 2:"i<(length y)\<longrightarrow>((times z y)!i = f z (y!i))" using times_elements by auto
 moreover have 3:"i<(length y) \<longrightarrow> (product (z#zs) y)!i = (times z y)!i" using product_simpl by auto
 moreover  have "i<(length y) \<longrightarrow> (product (z#zs) y)!i = f z (y!i)" by (metis calculation(1) calculation(2))
 have "(y \<noteq> []) \<longrightarrow> (length y) >0 " by auto 
 have "(i <(length y)) \<longrightarrow>  ((i div (length y)) = 0)" by auto
 from this have  6:"(i <(length y)) \<longrightarrow> (z#zs)!(i div (length y)) = z" using nth_Cons_0 by auto
 from this have 7:"(i <(length y)) \<longrightarrow> (i mod (length y)) = i" by auto
 from 2 6 7 have "(i < (length y)) \<longrightarrow> (times z y)!i = f  ((z#zs)!(i div (length y))) (y! (i mod (length y)))
 " by auto 
 from this 3 have step1:"((i < (length y)) \<longrightarrow> 
  ((i<((length x)*(length y)) \<longrightarrow> ((product (z#zs) y)!i 
  =  f  ((z#zs)!(i div (length y))) (y! (i mod (length y)))))))"
 by auto
 have "((length y) \<le> i) \<longrightarrow> (i - (length y)) \<ge> 0" by auto
 have step2:" ((length y) < i) \<longrightarrow>
  ((i < (length (z#zs)*(length y)))\<longrightarrow>((product (z#zs) y)!i) 
   = f ((z#zs)!(i div (length y))) (y!(i mod (length y))))"
  proof-
  have "(length y)>0" using assms by auto
  from this have 1: "(i > (length y))\<longrightarrow>(i div (length y)) = ((i-(length y)) div (length y)) + 1" using nat_div 
    by auto
  have "zs!j = (z#zs)!(j+1)" by auto
  from this have " (zs!((i - (length y)) div (length y))) = (z#zs)!(((i - (length y)) div (length y))+1)"
  by auto
  from this 1  have 2: "(i > (length y))\<longrightarrow> (zs!((i - (length y)) div (length y)) = (z#zs)!(i div (length y)))"
  by auto
   have "(i > (length y))\<longrightarrow>((i mod (length y)) = ((i - (length y)) mod (length y)))" using nat_mod 
  by auto
  from this have 3:"(i > (length y))\<longrightarrow>((y! (i mod (length y))) = (y! ((i - (length y)) mod (length y))))" 
  by auto
  have 4:" (i > (length y))\<longrightarrow>(product (z#zs) y)!i =  (product zs y)!(i- (length y))" using product_simpl2 
  by auto
  have 5: " (i > (length y))\<longrightarrow>((i <((length (z#zs))*(length y)))) = ((i - (length y))< (length zs)*(length y))"
   by auto
  from this have 6:"\<forall>i.((i<((length zs)*(length y)))
  \<longrightarrow> ((product zs y)!i) = f (zs!(i div (length y))) (y!(i mod (length y))))" using Cons.hyps by auto
  from this 5 have "(i > (length y))\<longrightarrow>((i<((length (z#zs))*(length y)))
  \<longrightarrow> ((product zs y)!(i -(length y))) = f (zs!((i -(length y)) div (length y))) (y!((i -(length y)) 
   mod (length y))))
   = ((i<((length zs)*(length y)))
  \<longrightarrow> ((product zs y)!i) = f (zs!(i div (length y))) (y!(i mod (length y))))
    " by auto
   from this 6 have "(i > (length y))\<longrightarrow>((i<((length (z#zs))*(length y)))
  \<longrightarrow> ((product zs y)!(i -(length y))) = f (zs!((i -(length y)) div (length y))) (y!((i -(length y)) 
   mod (length y))))" by auto
   from this 2 3 4 have  "(i > (length y))\<longrightarrow>((i<((length (z#zs))*(length y)))
  \<longrightarrow> ((product (z#zs) y)!i) = f ((z#zs)!(i div (length y))) (y!(i mod (length y))))"
  by auto
  from this show ?thesis  by auto
  qed
 have "((length y) = i) \<longrightarrow>
 ((i < (length (z#zs)*(length y)))\<longrightarrow>((product (z#zs) y)!i) 
   = f ((z#zs)!(i div (length y))) (y!(i mod (length y))))"
  proof-
  have 1:"(i = (length y)) \<longrightarrow> ((product (z#zs) y)!i) = (product zs y)!0" using product_simpl2
   by auto
  have 2:"(i = length y) \<longrightarrow> (i mod (length y)) = 0" by auto
  have 3:"(i = length y) \<longrightarrow> (i div (length y)) = 1" 
    by (metis `y \<noteq> [] \<longrightarrow> 0 < length y` assms div_self less_numeral_extra(3))
  have 4: "(i = length y) \<longrightarrow> ((i < (length (z#zs))*(length y)) = (0 < (length zs)*(length y)))" by auto
  have " (z#zs)!1 = (zs!0)" by auto
  from this 3 have 5:" (i = length y) \<longrightarrow> ((z#zs)!(i div (length y))) = (zs!0)" by auto 
  have " \<forall>i.((i < (length zs)*(length y))\<longrightarrow>((product (zs) y)!i) 
    = f ((zs)!(i div (length y))) (y!(i mod (length y))))" using Cons.hyps by auto  
  from this 4 have 6:"(i = length y) \<longrightarrow>((0 < ((length zs)*(length y)))\<longrightarrow> (((product (zs) y)!0) 
    = f ((zs)!0) (y!0))) = ((i < ((length zs)*(length y)))\<longrightarrow>(((product zs y)!i) 
    = f ((zs)!(i div (length y))) (y!(i mod (length y)))))" by auto
  have 7: " (0 div (length y)) = 0" by auto
  have 8: " (0 mod (length y)) = 0" by auto
  have 9: "(0 < ((length zs)*(length y))) \<longrightarrow> ((product zs y)!0) 
    = f (zs!0) (y!0)" using 7 8 Cons.hyps by auto
  from this 4 5 8 have "(i = length y) \<longrightarrow> ((i < (length (z#zs))*(length y)) \<longrightarrow> (((product (zs) y)!0) 
    = f ((zs)!0) (y!0)))" 
  by auto
  from this 1 2 5 have "(i = length y) \<longrightarrow> ((i < (length (z#zs))*(length y)) \<longrightarrow> (((product ((z#zs)) y)!i) 
    = f ((z#zs)!(i div (length y))) (y!(i mod (length y)))))" by auto
  from this show ?thesis by auto
  qed
 from this step2 have step4: " (i \<ge> (length y)) \<longrightarrow>  ((i < (length (z#zs))*(length y)) \<longrightarrow> (((product ((z#zs)) y)!i) 
   = f ((z#zs)!(i div (length y))) (y!(i mod (length y)))))" by auto
 have "(i < (length y)) \<or> (i \<ge> (length y))" by auto
 from this step1 step4 have " ((i < (length (z#zs))*(length y)) \<longrightarrow> (((product ((z#zs)) y)!i) 
   = f ((z#zs)!(i div (length y))) (y!(i mod (length y)))))" using logic by (metis "6" "7" 
  `i < length y \<longrightarrow> product (z # zs) y ! i = z * y ! i`) 
 from this show ?case by auto
 qed
(*list_tensor elements*)

lemma nat_int:  "nat (int x + int y) = x + y"
using nat_int of_nat_add by auto

lemma int_nat_equiv: "(x > 0) \<longrightarrow> (nat ((int x) + -1)+1) = x"
proof-
have "1 = nat (int 1)" by auto
have "-1 = -int 1" by auto
from this have 1:"(nat ((int x) + -1)+1) = (nat ((int x) + -1) + (nat (int 1)))" by auto
from this have 2:"  (x > 0) \<longrightarrow> nat ((int x) + -1 ) + (nat (int 1)) =  (nat (((int x)  + -1) + (int 1)))" 
using of_nat_add nat_int by auto
 have "  (nat (((int x)  + -1) + (int 1))) = (nat ((int x) + -1 + (int 1)))" by auto
from this have "  (nat (((int x)  + -1) + (int 1))) = (nat ((int x)))" by auto
from this have "(nat (((int x)  + -1) + (int 1))) = x" by auto
from this 1 2 have " (x > 0) \<longrightarrow> nat ((int x) + -1 ) + 1 = x" by auto
from this show ?thesis by auto
qed 

lemma list_int_nat: "(k>0) \<longrightarrow> ((x#xs)!k = xs!(nat ((int k)+-1)))"  
  proof-
  have " ((x#xs)!(k+1) = xs!k)" by auto
  have "j = (k+1) \<longrightarrow> (nat ((int j)+-1)) = k" by auto
  moreover have "(nat ((int j)+-1)) = k \<longrightarrow> ((nat ((int j)+-1)) + 1) = (k +1)" by auto
  moreover have "(j>0)\<longrightarrow>(((nat ((int j)+-1)) + 1) = j)" using  int_nat_equiv by (auto)
  moreover have "(k>0) \<longrightarrow> ((x#xs)!k = xs!(nat ((int k)+-1)))" 
  by (metis Suc_eq_plus1 int_nat_equiv nth_Cons_Suc)
  from this show ?thesis by auto
  qed

theorem list_tensor_elements: 
"\<forall>i.\<forall>j.(((i<((length v)*(row_length M)))\<and>(j < (length M)))\<and>(mat (row_length M) (length M) M)
\<longrightarrow> ((list_tensor v M)!j!i) = f (v!(i div (row_length M))) (M!j!(i mod (row_length M))))"
 apply(rule allI)
 apply(rule allI)
 proof(induct M)
 case Nil
 have "row_length [] = 0" using row_length_def by auto
 from this have "(length v)*(row_length []) = 0" by auto
 from this have "((i<((length v)*(row_length [])))\<and>(j < (length []))) \<longrightarrow> False" by auto
 moreover have "list_tensor v [] = []" by auto 
 moreover have "(((i<((length v)*(row_length [])))\<and>(j < (length [])))
\<longrightarrow> ((list_tensor v [])!j!i) = f (v!(i div (row_length []))) ([]!j!(i mod (row_length []))))"
 by auto
 from this show ?case by auto
 next
 case (Cons a M)
 have "(((i<((length v)*(row_length (a#M))))\<and>(j < (length (a#M))))\<and>(mat (row_length (a#M)) 
 (length (a#M)) (a#M))
\<longrightarrow> ((list_tensor v (a#M))!j!i) = f (v!(i div (row_length (a#M)))) ((a#M)!j!(i mod (row_length (a#M)))))"
  proof(cases a)
  case Nil
  have "row_length ([]#M) = 0" using row_length_def by auto
  from this have "(length v)*(row_length ([]#M)) = 0" by auto
  from this have "((i<((length v)*(row_length ([]#M))))\<and>(j < (length ([]#M)))) \<longrightarrow> False" by auto
  moreover have "(((i<((length v)*(row_length ([]#M))))\<and>(j < (length ([]#M))))
  \<longrightarrow> ((list_tensor v ([]#M))!j!i) = f (v!(i div (row_length ([]#M)))) ([]!j!(i mod (row_length ([]#M)))))"
  by (metis calculation)
  from this show ?thesis by (metis Nil `length v * row_length ([] # M) = 0` less_nat_zero_code)
  next
  case (Cons x xs)
  have 1:"(a#M)!(j+1) = M!j" by auto
  have " (((i<((length v)*(row_length M)))\<and>(j < (length M)))\<and> (mat (row_length M) (length M) M)
  \<longrightarrow> ((list_tensor v M)!j!i) = f (v!(i div (row_length M))) (M!j!(i mod (row_length M))))" 
  using Cons.hyps by auto
  have 2: "(row_length (a#M)) = (length a)" using row_length_def by auto
  from this have 3:"(i< (row_length (a#M))*(length v)) = (i < (length a)*(length v))" by auto
  have "a \<noteq> []" using Cons by auto
  from this have 4:" \<forall>i.((i < (length a)*(length v)) \<longrightarrow>  
    ((product v a)!i) = f (v!(i div (length a))) (a!(i mod (length a))))" using product_elements Cons.hyps
  using nat_mult_commute by auto
  have "(list_tensor v (a#M))!0 = (product v a)" using list_tensor.simps(2) by auto
  from this 2 4 have 5: " \<forall>i.((i < (row_length (a#M))*(length v)) \<longrightarrow>  
    ((list_tensor v (a#M))!0!i) = f (v!(i div (row_length (a#M)))) ((a#M)!0!(i mod (row_length (a#M)))))" 
  by auto 
  have "length (a#M)>0" by auto
  from this 5 have 6: "(j = 0)\<longrightarrow>
   ((((i < (row_length (a#M))*(length v)) \<and>(j < (length (a#M))))
   \<and> (mat (row_length (a#M)) (length (a#M)) (a#M))   \<longrightarrow>  
   ((list_tensor v (a#M))!j!i) = f (v!(i div (row_length (a#M)))) ((a#M)!j!(i mod (row_length (a#M))))))" 
   by auto 
  have " (((i < (row_length (a#M))*(length v)) \<and>(j < (length (a#M))))
   \<and> (mat (row_length (a#M)) (length (a#M)) (a#M))   \<longrightarrow>  
  ((list_tensor v (a#M))!j!i) = f (v!(i div (row_length (a#M)))) ((a#M)!j!(i mod (row_length (a#M)))))" 
   proof(cases M)
   case Nil
   have "(length (a#[])) = 1" by auto
   from this have "(j<(length (a#[]))) = (j = 0)" by auto
   from this have " ( (((i < (row_length (a#[]))*(length v)) \<and>(j < (length (a#[]))))
   \<and> (mat (row_length (a#[])) (length (a#[])) (a#[]))   \<longrightarrow>  
   ((list_tensor v (a#[]))!j!i) = f (v!(i div (row_length (a#[])))) ((a#[])!j!(i mod (row_length (a#[]))))))" 
   using 6 Nil by auto
   from this show ?thesis using Nil by auto 
   next
   case (Cons b N)
   have 7:"(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) \<longrightarrow> 
    (row_length (a#b#N) = (row_length (b#N)))" 
     proof-
     have "(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) \<longrightarrow> (b \<in> set (a#b#M))" by auto
     moreover have "(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) 
          \<longrightarrow> (Ball (set (a#b#N)) (vec (row_length (a#b#N))))"
          using mat_def by metis
     moreover have "(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) \<longrightarrow> (b \<in> (set (a#b#N)))\<longrightarrow> 
                        (vec (row_length (a#b#N)) b)"  by (metis calculation(2))
     from this have "(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) 
       \<longrightarrow> (length b) = (row_length (a#b#N))" using vec_def by auto
     from this have "(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) 
          \<longrightarrow> (row_length (b#N)) = (row_length (a#b#N))" using row_length_def by auto
     then show ?thesis by auto
     qed
   have 8: "(j>0) \<longrightarrow> ((list_tensor v (b#N))!(nat ((int j)+-1))) = (list_tensor v (a#b#N))!j"
    using list_tensor.simps(2) using list_int_nat by metis
   have 9: "(j>0) \<longrightarrow> (((i < (row_length (b#N))*(length v)) \<and>((nat ((int j)+-1)) < (length (b#N))))
           \<and> (mat (row_length (b#N)) (length (b#N)) (b#N))   \<longrightarrow>  
           ((list_tensor v (b#N))!(nat ((int j)+-1))!i) = f (v!(i div (row_length (b#N)))) 
           ((b#N)!(nat ((int j)+-1))!(i mod (row_length (b#N)))))"
           using Cons.hyps Cons nat_mult_commute by metis
   have "(j>0) \<longrightarrow> ((nat ((int j) + -1)) < (length (b#N))) \<longrightarrow> ((nat ((int j) + -1) + 1) < length (a#b#N))"
    by auto
   from this have "(j>0) \<longrightarrow> ((nat ((int j) + -1)) < (length (b#N))) = (j < length (a#b#N))"
     by auto
   from this have  "(j>0) \<longrightarrow> (((i < (row_length (b#N))*(length v)) \<and> (j < length (a#b#N)))
     \<and> (mat (row_length (b#N)) (length (b#N)) (b#N))   \<longrightarrow>  
     ((list_tensor v (b#N))!(nat ((int j)+-1))!i) = f (v!(i div (row_length (b#N)))) ((b#N)!(nat ((int j)+-1))!(i mod (row_length (b#N)))))"
      using Cons.hyps Cons nat_mult_commute by metis
   from this 8 have "(j>0) \<longrightarrow> (((i < (row_length (b#N))*(length v)) \<and> (j < length (a#b#N)))
     \<and> (mat (row_length (b#N)) (length (b#N)) (b#N))   \<longrightarrow>  
     ((list_tensor v (a#b#N))!j!i) = f (v!(i div (row_length (b#N)))) ((b#N)!(nat ((int j)+-1))!(i mod (row_length (b#N)))))"
     by auto
   moreover have "(j>0) \<longrightarrow> (b#N)!(nat ((int j)+-1)) = (a#b#N)!j" using list_int_nat by metis
   moreover have " (j>0) \<longrightarrow> (((i < (row_length (b#N))*(length v)) \<and> (j < length (a#b#N)))
     \<and> (mat (row_length (b#N)) (length (b#N)) (b#N))   \<longrightarrow>  
     ((list_tensor v (a#b#N))!j!i) = f (v!(i div (row_length (b#N)))) ((a#b#N)!j!(i mod (row_length (b#N)))))"
     by (metis calculation(1) calculation(2))
   from this have  " (j>0) \<longrightarrow> (((i < (row_length (b#N))*(length v)) \<and> (j < length (a#b#N)))
      \<and> (mat (row_length (a#b#N)) (length (a#b#N)) (a#b#N))   \<longrightarrow>  
      ((list_tensor v (a#b#N))!j!i) = f (v!(i div (row_length (b#N)))) ((a#b#N)!j!(i mod (row_length (b#N)))))"
      using  reduct_matrix by (metis)
   moreover  have "(mat (row_length (a#b#N)) (length (a#b#N)) (a#b#N))
   \<longrightarrow>(row_length (b#N)) = (row_length (a#b#N))" by (metis "7" Cons)
   moreover have 10:"  (j>0) \<longrightarrow> (((i < (row_length (a#b#N))*(length v)) \<and> (j < length (a#b#N)))
      \<and> (mat (row_length (a#b#N)) (length (a#b#N)) (a#b#N))   \<longrightarrow>  
      ((list_tensor v (a#b#N))!j!i) = f (v!(i div (row_length (a#b#N)))) ((a#b#N)!j!(i mod (row_length (a#b#N)))))"
     by (metis calculation(3) calculation(4))
   have "(j = 0) \<or> (j > 0)" by auto
    from this 6 10 logic have "(((i < (row_length (a#b#N))*(length v)) \<and> (j < length (a#b#N)))
      \<and> (mat (row_length (a#b#N)) (length (a#b#N)) (a#b#N))   \<longrightarrow>  
     ((list_tensor v (a#b#N))!j!i) = f (v!(i div (row_length (a#b#N)))) ((a#b#N)!j!(i mod (row_length (a#b#N)))))"
     using  Cons by metis
     from this show ?thesis by (metis Cons)
   qed
  from this show ?thesis by (metis nat_mult_commute)
  qed
  from this show ?case by auto
  qed
(*Matrix_Tensor_Elements*)
(*
primrec tensor::" 'a mat \<Rightarrow> 'a mat \<Rightarrow>'a mat" (infixl "\<otimes>" 63)
where
"tensor [] xs = []"|
"tensor (x#xs) ys = (list_tensor x ys)#(tensor xs ys)"
*)

theorem matrix_tensor_elements: 
"\<forall>i.\<forall>j.(((i<((row_length M1)*(row_length M2)))\<and>(j < (length M1)*(length M2)))
\<and>(mat (row_length M1) (length M1) M1)\<and>(mat (row_length M2) (length M2) M2)
\<longrightarrow> ((M1 \<otimes> M2)!j!i) = f (M1!(j div (row_length M1))!(i div (row_length M2))) 
(M2!(j mod row_length M1)!(i mod (row_length M2))))"
 apply(rule allI)
 apply(rule allI)
 proof(induct M1)
 case Nil
  have "(row_length []) = 0" using row_length_def by auto
  from this have "(i< ((row_length [])*(row_length M2))) \<longrightarrow> False" by auto
  from this have "((i<((row_length [])*(row_length M2)))\<and>(j < (length [])*(length M2)))
  \<and>(mat (row_length []) (length []) [])\<and>(mat (row_length M2) (length M2) M2) \<longrightarrow> False" by auto
  moreover have "([] \<otimes> M2) = []" by auto
  moreover have "((i<((row_length [])*(row_length M2)))\<and>(j < (length [])*(length M2)))
  \<and>(mat (row_length []) (length []) [])\<and>(mat (row_length M2) (length M2) M2) 
  \<longrightarrow> (([] \<otimes> M2)!j!i) = f ([]!(j div (row_length []))!(i div (row_length M2))) 
      (M2!(j mod row_length [])!(i mod (row_length M2)))" by auto
  from this show ?case by auto
 next
 case (Cons a M)
 have "(a#M) \<otimes> M2 = (list_tensor a M2)@(tensor M M2)" by auto
 from this have "(j<(length M2)) \<longrightarrow> ( ((a#M) \<otimes> M2)!j = (list_tensor a M2)!j)" 
   using append_simpl list_tensor_length by metis
 have "
 (list_tensor a M2)!j
(*To Prove-
That Tensors Commute with products*)
(*theorem multiplicative_distributivity:  mat k1 l1 M1 mat k2 l2 N1 mat l1 j1 M2 mat l2 j2 N2 shows 
( ((M1\<otimes>N1)\<circ>(M2\<otimes>N2)) = (M1\<circ>M2)\<otimes>(M2\<circ>N2)*)
  
end

 

      

