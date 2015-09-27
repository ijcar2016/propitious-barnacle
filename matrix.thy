theory matrix
imports
    "Complex"
begin

type_synonym 'a vec = "int list"
type_synonym 'a mat = "'a vec list" (* list of column-vectors *)
type_synonym 'a Utary="'a mat"
type_synonym  Mat="'a mat"

(* vector of given length *)
definition vec :: "nat \<Rightarrow> 'x vec \<Rightarrow> bool"
 where "vec n x = (length x = n)"

(* matrix of given number of rows and columns *)
definition mat :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> bool" where
 "mat nr nc m = (length m = nc \<and> Ball(set m) (vec nr))"

subsection {* definitions / algorithms *}



(* the 0 vector *)
definition vec0I :: "nat \<Rightarrow> nat \<Rightarrow> 'a vec" where 
 "vec0I ze n = replicate n ze"


definition vec10_def:
   "l0=(replicate 1 1)#replicate 1 (replicate 1 0) "(*<0|*)
definition vec1_0_def: 
   "r0=  replicate 1 (1#(replicate 1 0))"(*|0>*)
definition vec01_def:
   "l1=(replicate 1 0)#replicate 1 (replicate 1 1) "(*<1|*)
definition vec0_1_def:
   "r1= replicate 1 (0#(replicate 1 1))"(*|1>*)

(* the 0 matrix *)
definition mat0I :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "mat0I ze nr nc = replicate nc (vec0I ze nr)"


definition right_n::"nat\<Rightarrow>nat\<Rightarrow>'a mat" where
    "right_n n i=replicate 1 (replicate i 0 @ 1 #replicate (n - 1 - i) 0)"
definition left_n::"nat\<Rightarrow>nat\<Rightarrow>'a mat"where
    "left_n n i = replicate i (replicate 1 0)@ (replicate 1 1)#replicate (n- 1-i)  (replicate 1 0)"
(* the i-th unit vector of size n *) 
definition vec1I ::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a vec"
  where "vec1I ze on n i \<equiv> replicate i ze @ on # replicate (n - 1 - i) ze"

(* the 1 matrix *)    (*unit matrix*)
definition mat1I :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat"
  where "mat1I ze on n \<equiv> map (vec1I ze on n) [0 ..< n]"

definition matI::"nat\<Rightarrow>'a mat"
where "matI nr \<equiv> map (vec1I 0 1 nr) [0 ..<nr]"


(* vector addition *)
definition vec_plusI :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> 'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec" where 
 "vec_plusI pl v w = map (\<lambda> xy. pl (fst xy) (snd xy)) (zip v w)"
(*vector substract*)
definition vec_sub::"'a vec\<Rightarrow>'a vec\<Rightarrow>'a vec" where
 "vec_sub v w=map (\<lambda> xy. (fst xy)-(snd xy)) (zip v w)"
(* matrix addition *)
definition mat_plusI :: "( int \<Rightarrow>  int \<Rightarrow> int) \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
 where "mat_plusI pl m1 m2 = map (\<lambda> uv. vec_plusI pl (fst uv) (snd uv)) (zip m1 m2)"

definition adjoint::"'a Utary\<Rightarrow>'a Utary"
  where "adjoint m=m"

(* scalar product *)
definition scalar_prodI :: " nat \<Rightarrow> ( int \<Rightarrow>  int \<Rightarrow>  int) \<Rightarrow> ( int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> 'a vec \<Rightarrow> 'a vec \<Rightarrow> int" where
 "scalar_prodI ze pl ti v w = foldr (\<lambda> (x,y) s. pl (ti x y) s) (zip v w) ze"

(* the m-th row of a matrix *)
definition row :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a vec"
where "row m i \<equiv> map (\<lambda> w. w ! i) m"

(* the m-th column of a matrix *)
definition col :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a vec"
where "col m i \<equiv> m ! i"

definition vec_com_mult::"nat=>'a vec=>'a vec" where
     "vec_com_mult b v= map (\<lambda>x. x*b) v"

definition  mat_com_mult::"nat=>'a mat=>'a mat"
    where " mat_com_mult b m=map (\<lambda> x. vec_com_mult b x) m"

(* transposition of a matrix (number of rows of matrix has to be given since otherwise one 
   could not compute transpose [] which might be [] or [[]] or [[], []], or ...) *)
fun transpose ::"'a mat \<Rightarrow> 'a mat"
 where "transpose  [] =replicate 0 []"
     | "transpose  (v # m) = map (\<lambda> (vi,mi). (vi # mi)) (zip v (transpose  m))"

(* matrix-vector multiplication, assumes the transposed matrix is given *)
definition matT_vec_multI :: " nat \<Rightarrow> ( int \<Rightarrow>  int \<Rightarrow>  int) \<Rightarrow> ( int \<Rightarrow>  int \<Rightarrow>  int) \<Rightarrow> 'a mat \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
 where "matT_vec_multI ze pl ti m v = map (\<lambda> w. scalar_prodI ze pl ti w v) m"

(* matrix-matrix multiplication, number of rows of left matrix has to be given (as transpose is used) *)
definition mat_multI :: "nat\<Rightarrow> ( int \<Rightarrow>  int \<Rightarrow>  int) \<Rightarrow> (  int \<Rightarrow>  int \<Rightarrow>  int) \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" 
where "mat_multI ze pl ti m1 m2 \<equiv> map (matT_vec_multI ze pl ti (transpose  m1)) m2"

definition tensor_product::"'a mat\<Rightarrow>'a mat\<Rightarrow>'a mat"
 where "tensor_product m1 m2 =m1"
definition pow::" 'a mat\<Rightarrow>nat\<Rightarrow>'a mat"
where "pow m n=m"
definition matsum::"nat\<Rightarrow>'a mat\<Rightarrow>'a mat"
where "matsum  n P=P"

definition matUtrans::"'a mat\<Rightarrow>nat\<Rightarrow>'a mat\<Rightarrow>'a mat"
where "matUtrans U n P=P"

definition order::"'a mat\<Rightarrow>'a mat\<Rightarrow>bool"
where "order a b=(a=b)"

abbreviation vec_plus :: "nat vec \<Rightarrow> nat vec \<Rightarrow> nat vec"
where "vec_plus \<equiv> vec_plusI  plus"

abbreviation mat_plus :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
where "mat_plus \<equiv> mat_plusI plus"

abbreviation vec0 :: "nat \<Rightarrow> 'nat vec"
where "vec0 \<equiv> vec0I 0"

abbreviation mat0 :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat"
where "mat0 \<equiv> mat0I 0"

abbreviation mat_mult :: " 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
where "mat_mult \<equiv> mat_multI 0 plus times"

definition A_def:
"A=mat_mult  l0 r1"
definition B_def:
"B=mat_mult l1 r0 "
definition Z_def:
"Z=mat_mult l1 r0 "
definition Mat0_def:
"Mat0=mat0 1 1"

abbreviation vec1 :: "nat \<Rightarrow> nat \<Rightarrow> nat vec"
where "vec1 \<equiv> vec1I 0 1"

abbreviation mat1 :: "nat \<Rightarrow> 'a mat"
where "mat1 \<equiv> mat1I 0 1"


end
                                       


