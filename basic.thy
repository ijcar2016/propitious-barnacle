theory basic
imports Main Complex
begin


(*The type for representing matrices, and three special sets of matrices*)
typedecl Mat
consts uMat :: "Mat set"
consts rhoMat :: "Mat set"
consts predMat::"Mat set"

type_synonym number=nat
type_synonym measurement="Mat list"
type_synonym nT="nat\<Rightarrow>Mat"

consts  infinity::"nat"
(*   the trace of matrix  *)
consts Tr::"Mat\<Rightarrow>real"
(*multiplication of matrix*)
consts mat_mult::"Mat\<Rightarrow>Mat\<Rightarrow>Mat"
(*   addition of matrix  *)
consts mat_add::"Mat\<Rightarrow>Mat\<Rightarrow>Mat"
(*   subtraction of matrix    *)
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

(*The axioms for matrices we assume. These are the basic axioms of matrices accepted by us for a long time. *)
axiomatization where
(* Tr a*b= Tr b*a *)
exchange:"Tr (mat_mult a b) =Tr (mat_mult b a)"and
(*  (m1*m2)*m3=m1*(m2*m3)   *)
mult_exchange:"mat_mult (mat_mult m1 m2) m3=mat_mult m1 (mat_mult m2 m3)"and
(*zero*)
zero_mult_r:"mat_mult a zero=zero"and
zero_mult_l:"mat_mult zero b=zero"and
zero_tr: "Tr zero = 0" and
rho_zero:"\<forall> a. a \<in> rhoMat \<longrightarrow> less zero  a" and
I_zero:"less zero I" and
pred:"\<forall> a. a\<in>predMat\<longrightarrow>less a I" and
(*(a+b)*c=ac+bc*)
mult_allo1:"mat_mult (mat_add a b) c=mat_add (mat_mult a c)  (mat_mult b c)" and
(* (a-b)*c=a*c-b*c    *)
mult_sub_allo1:"mat_mult (mat_sub a b) c=mat_sub (mat_mult a c) (mat_mult b c)" and
(*  c(a+b) =ca+cb       *)
mult_allo2:"mat_mult c (mat_add a b) =mat_add (mat_mult c a )  (mat_mult c b)"and
(* Tr (a+b) =Tr a+Tr b  *)
tr_allo:"Tr (mat_add a b) =Tr a+Tr b"and
(*Tr (a-b) =Tr a - Tr b*)
tr_allo1:"Tr (mat_sub a b) =Tr a -Tr b"and
(*dag U * U=I*)
U_dag:"\<forall> a. a \<in> uMat \<longrightarrow> mat_mult (dag a) a=I"and
(*I*a=a*)
Ident:"mat_mult I a=a"and
(* less a b \<Rightarrow> less (a+c) (b+c)*)
less1:"less a b\<Longrightarrow>less (mat_add c a) (mat_add c b )"and
(*  a\<sqsubseteq>b\<Longrightarrow>tr ac\<le>tr bc for all \<rho> mats  *)
less2:"less a b\<Longrightarrow>(\<forall> c. c \<in> rhoMat \<longrightarrow> tr (mat_mult a c) \<le>tr (mat_mult b c)) "and
(* a\<ge>0\<Longrightarrow>m*a*m.T\<ge>0  *)
less3:" less zero  a\<Longrightarrow>less zero (mat_mult (mat_mult b a) (dag b))"and
(*a>0 b>0\<Longrightarrow>Tr (ab)\<ge>0*)
less4:"less zero a\<Longrightarrow>less zero b\<Longrightarrow>Tr (mat_mult a b) \<ge>0"



lemma c:"\<forall> c. c \<in> rhoMat \<longrightarrow>  0 <=Tr c"
by (metis I_zero Ident less2 zero_mult_l zero_tr)






end
