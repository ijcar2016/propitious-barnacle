theory basic
imports Main Complex
begin
(*to do: explain the constans.*)
typedecl Mat
type_synonym number=nat
type_synonym measurement="Mat list"
type_synonym nT="nat\<Rightarrow>Mat"
(* \<infinity> *)
consts  infinity::"nat"
(*   the trace of matrix  *)
consts Tr::"Mat\<Rightarrow>real"
(*multiplication of matrix*)
consts mat_mult::"Mat\<Rightarrow>Mat\<Rightarrow>Mat"
(*   addition of matrix  *)
consts mat_add::"Mat\<Rightarrow>Mat\<Rightarrow>Mat"
(*   subtration of matrix    *)
consts mat_sub::"Mat\<Rightarrow>Mat\<Rightarrow>Mat"
(*    all 0 matrix   *)
consts zero::"Mat"
(*    M\<dagger>   *)
consts dag::"Mat\<Rightarrow>Mat"
(*    |0><n|  *)
consts f::"nat\<Rightarrow>Mat"
(*    |n><0|  *)
consts g::"nat\<Rightarrow>Mat"
(*   identity matrix *)
consts I::"Mat"
(*   a\<sqsubseteq>b      *)
consts less::"Mat\<Rightarrow>Mat\<Rightarrow>bool"
(*  fixpoint    *)
consts fixPoint::"Mat"
consts fixPoint_wlp::"Mat"
(*  a^n   a is type of matrix,b is type of int *)
consts pow::"Mat\<Rightarrow>nat\<Rightarrow>Mat"

(*to do: define subtypes of Mat*)
axiomatization where
(* Tr a*b= Tr b*a *)
exchange:"Tr (mat_mult a b) =Tr (mat_mult b a)"and
(*  (m1*m2)*m3=m1*(m2*m3)   *)
mult_asso:"mat_mult (mat_mult m1 m2) m3=mat_mult m1 (mat_mult m2 m3)"and
(*zero*)
zero_mult:"mat_mult a zero=zero"and
zero_tr: "Tr zero = 0" and
zero_rel:"\<forall> \<rho>. less zero  \<rho>" and
(*(a+b)*c=ac+bc*)
mult_dist:"mat_mult (mat_add a b) c=mat_add (mat_mult a c)  (mat_mult b c)" and
(* (a-b)*c=a*c-b*c    *)
mult_sub_allo1:"mat_mult (mat_sub a b) c=mat_sub (mat_mult a c) (mat_mult b c)" and
(*  c(a+b) =ca+cb       *)
mult_dist_l:"mat_mult c (mat_add a b) =mat_add (mat_mult c a )  (mat_mult c b)"and
(* Tr (a+b) =Tr a+Tr b  *)
tr_allo:"Tr (mat_add a b) =Tr a+Tr b"and
(*Tr (a-b) =Tr a - Tr b*)
tr_allo1:"Tr (mat_sub a b) =Tr a -Tr b"and
(*dag U * U=I*)
U_dag:"mat_mult (dag U) U=I"and
(*I*a=a*)
I_mult:"mat_mult I a=a"and
(* less a b \<Rightarrow> less (a+c) (b+c)*)
less1:"less a b\<Longrightarrow>less (mat_add c a) (mat_add c b )"and
(*  a\<sqsubseteq>b\<Longrightarrow>tr ap\<le>tr bp  *)
less2:"less a b\<Longrightarrow>\<forall> \<rho>. tr (mat_mult a \<rho>) \<le>tr (mat_mult b \<rho>) "and
M_pt:"mat_add  (mat_mult m0 (dag m0)) (mat_mult m1 (dag m1)) =I"

lemma zero_mult_l:"mat_mult zero b=zero"
by (metis (poly_guards_query) U_dag zero_mult mult_asso)
lemma \<rho>_rel:"\<forall> \<rho>. 0 <=Tr \<rho>"
by (metis (full_types) I_mult U_dag zero_mult zero_mult_l zero_tr less_irrefl not_le)





end
