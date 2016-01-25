theory quantum_hoare_logic
imports Main  basic
begin

(*The datatype for representing syntax of quantum programs*)
datatype
com=SKIP
|Init "nat list" "number"
|Utrans "Mat" "number"
|Seq "com" "com"          ("(_;/ _)"   [61,59] 60  )
|Cond "(Mat * com * Mat) list"  
|While "Mat" "Mat" "com" "Mat" 
|While_n "Mat" "Mat" "com" "Mat" "nat"

primrec M_sum::"(Mat*com*Mat) list\<Rightarrow>Mat"where
"M_sum [] =I"|
"M_sum (a#M) =mat_add (mat_mult (dag (fst a) ) (fst a)) (M_sum M )"
(*the conditions the comands should meet they are well-defined  *)
primrec wellDefined :: "com\<Rightarrow>bool" where
"wellDefined SKIP =True"|
"wellDefined (Utrans a n) = (a \<in> uMat)"|
"wellDefined (Init m n) =True"|
"wellDefined (s1;s2) = (wellDefined (s1) & wellDefined (s2))"|
"wellDefined (Cond mcl) = (M_sum mcl=I) "|
"wellDefined (While_n m0 m1 s Q n)= (mat_add (mat_mult (dag m0) m0)  (mat_mult (dag m1) m1) =I)" |
"wellDefined  (While  m0 m1 s Q )=(mat_add (mat_mult (dag m0) m0)  (mat_mult (dag m1) m1) =I)  "

primrec sum::"nat list\<Rightarrow>nT\<Rightarrow>Mat\<Rightarrow>nT\<Rightarrow>Mat" where
"sum [] f1 p g1=zero"|
"sum (b#nl) f1 p g1 = mat_add (mat_mult (mat_mult (f1 b) p) (g1 b)) (sum nl f1 p g1)"

primrec sum_1::"nat list\<Rightarrow>nT\<Rightarrow>nT\<Rightarrow>Mat" where
"sum_1 [] f1 g1=zero"|
"sum_1 (b#nl) f1 g1=mat_add (mat_mult (f1 b) (g1 b)) (sum_1 nl f1 g1)"
(*  f(1)*g(1)+f(2)*g(2)+..\<doteq>I the same as measurement matrix      *)
axiomatization where
fg:"sum_1 m g f=I"

(*u a b =ab(dag a) *)
definition u::"Mat\<Rightarrow>Mat\<Rightarrow>Mat"where
"u a b= mat_mult (mat_mult a b) (dag a)"
(*u a b =(dag a)ba *)
definition uu::"Mat\<Rightarrow>Mat\<Rightarrow>Mat"where
"uu a b= mat_mult (mat_mult (dag a) b)  a"
 (*the rank that defined for the command*)
fun rank :: "com\<Rightarrow>nat" where
"rank SKIP =1"|
"rank (Utrans U n) =1"|
"rank (Init m n) =1"|
"rank (s1;s2) =1+ rank s2 + (rank s1 )"|
"rank (Cond mcl) =  (case mcl of [] \<Rightarrow> 1
  | mc # mcr \<Rightarrow> 1+rank (fst (snd mc)) + rank (Cond mcr)) "|
"rank (While_n m0 m1 s Q n)=  1 + n * rank (s)" |
"rank  (While  m0 m1 s Q )= 1"

lemma rank_pos : " rank ss > 0" 
apply (induct ss, auto) 
by (smt2 One_nat_def Suc_less_eq le_imp_less_Suc list.case(1) list.case(2) list.exhaust monoid_add_class.add.left_neutral monoid_add_class.add.right_neutral not_le order_refl plus_nat.simps(2) rank.simps(5) trans_le_add1 trans_le_add2)
(*definition of fixpoint*)
definition fixpoint::"Mat\<Rightarrow>Mat\<Rightarrow>com\<Rightarrow>Mat\<Rightarrow>Mat\<Rightarrow>Mat"where
"fixpoint m0 m1 s Q p=fixPoint"
definition fixpoint_wlp::"Mat\<Rightarrow>Mat\<Rightarrow>com\<Rightarrow>Mat\<Rightarrow>Mat\<Rightarrow>Mat"where
"fixpoint_wlp  m0 m1 s Q p=fixPoint_wlp"

(*the denotational semantics of quantum programs  *)
function denoFun::"com\<Rightarrow>Mat\<Rightarrow>Mat" where
"denoFun SKIP p=p"|
"denoFun (Utrans U n) p=mat_mult (mat_mult U p) (dag U)"|
"denoFun (Init m n) p=sum m f p g"|
"denoFun (s1;s2) p= denoFun s2 (denoFun s1  p )"|
"denoFun (Cond mcl) p=  (case mcl of [] \<Rightarrow> zero
  | mc # mcr \<Rightarrow> mat_add (mat_mult (mat_mult (fst mc) (denoFun (fst (snd mc)) p))  (dag (fst mc)) ) (denoFun (Cond mcr) p)) "|
"denoFun (While_n m0 m1 s Q n) p= (case n of 0\<Rightarrow>zero
                               | Suc m\<Rightarrow>
mat_add (u m0 p)  (denoFun (While_n m0 m1 s Q m) ( denoFun s (u m1 p))   ) )"  
|"denoFun (While m0 m1 s Q) p= fixpoint  m0 m1 s Q  p"
by  pat_completeness auto 
termination 
 apply (relation "measure (\<lambda>(c,m).rank c)", auto )
by (metis rank_pos)
(*the ascending  order of denotational semantics of while_n *)
lemma ascend:"\<forall> \<rho> .less  (denoFun (While_n m0 m1 s Q n) \<rho>)   (denoFun (While_n m0 m1 s Q (Suc n) ) \<rho>)"
apply(induct n,auto)
apply (metis (poly_guards_query) Ident zero_mult_l I_zero fg sum_1.simps(1))
by (metis Nitpick.case_nat_unfold less1)

(*the definition of valid *)
definition valid::"Mat\<Rightarrow>com\<Rightarrow>Mat\<Rightarrow>bool" where
"  valid P S Q= (\<forall>\<rho>. \<rho> \<in> rhoMat\<longrightarrow> Tr (mat_mult P \<rho>)<= Tr (mat_mult Q (denoFun S \<rho>))+Tr \<rho>-Tr (denoFun S \<rho>)   )"
(*svalid is equal to valid ,just for simplication*)
definition svalid::"Mat\<Rightarrow>com\<Rightarrow>Mat\<Rightarrow>bool"where
"svalid P S Q=(\<forall> \<rho> .\<rho>\<in>rhoMat\<longrightarrow> Tr (mat_mult (mat_sub I Q) (denoFun S \<rho>)) <= Tr (mat_mult (mat_sub I P) \<rho>) )"
lemma eq_valid:"svalid P S Q  \<Longrightarrow>valid P S Q"
apply(simp add:valid_def)
apply(simp add:svalid_def)
apply(simp add:mult_sub_allo1)
apply(simp add:tr_allo1)
apply(simp add:Ident)
apply auto
done
lemma eq_valid2:"valid P S Q\<Longrightarrow>svalid P S Q"
apply(simp add:valid_def)
apply(simp add:svalid_def)
apply(simp add:mult_sub_allo1)
apply(simp add:tr_allo1)
apply(simp add:Ident)
apply auto
done
lemma b1:" (mat_mult (mat_mult (mat_mult a b) c) d) =mat_mult (mat_mult a b) (mat_mult c d)"
apply (simp add:mult_exchange)
done
lemma b2:" (mat_mult (mat_mult b d) (mat_mult a c)) =mat_mult (mat_mult (mat_mult b d) a) c"
apply (simp add:mult_exchange)
done
lemma b3:" Tr (mat_mult (mat_mult (mat_mult e  b) d) c)=Tr (mat_mult b (mat_mult (mat_mult d c) e ))"
apply(simp add:b1)
apply(simp add:exchange)
apply(simp add:b2)
apply(simp add:exchange)
done
lemma b4:"mat_mult (dag U) (mat_mult U \<rho>) =mat_mult(mat_mult (dag U) U) \<rho>"
apply(simp add:mult_exchange)
done

lemma hh:" Tr (mat_mult (f a) (mat_mult \<rho> (g a))) =Tr (mat_mult (mat_mult \<rho> (g a))   (f a))"
apply(simp add:exchange)
done
lemma temp:"Tr (sum m f \<rho> g) =Tr  (mat_mult \<rho> (sum_1 m g f) ) "
apply(induct m)
apply auto
apply(simp add:zero_mult_r)
apply(simp add:mult_allo2)
apply(simp add:tr_allo)
apply(simp add:mult_exchange)
apply(simp add:hh)
apply(simp add:mult_exchange)
done
lemma m_init:"Tr (sum m f \<rho> g) =Tr \<rho>"
apply(simp add:temp)
apply(simp add:fg)
apply(subgoal_tac " Tr (mat_mult \<rho> I) = Tr (mat_mult I \<rho> ) ")
apply(simp add:Ident)
apply(simp add:exchange)
done

lemma w3:"\<lbrakk>valid Q S (mat_add (uu m0 P) (uu m1 Q)) \<Longrightarrow>
svalid Q S  (mat_add (uu m0 P) (uu m1 Q)) ; svalid Q S  (mat_add (uu m0 P) (uu m1 Q)) \<Longrightarrow>
         \<forall>\<rho>. Tr (mat_mult (mat_sub I P)  (denoFun (While_n m0 m1 S Q n) \<rho>)  )
        \<le> Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) \<rho>)\<rbrakk>\<Longrightarrow>(valid Q S (mat_add (uu m0 P) (uu m1 Q)) \<Longrightarrow>
       \<forall>\<rho>. Tr (mat_mult (mat_sub I P)  (denoFun (While_n m0 m1 S Q n) \<rho>)  )
        \<le> Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) \<rho>) )"
apply auto
done

lemma While_n:"wellDefined (While_n m0 m1 S Q n) \<Longrightarrow>mat_add  (mat_mult m0 (dag m0)) (mat_mult m1 (dag m1)) =I\<Longrightarrow>
valid Q S (mat_add (uu m0 P) (uu m1 Q)) \<Longrightarrow> 
\<forall>\<rho>. Tr (mat_mult (mat_sub I P)  (denoFun (While_n m0 m1 S Q n) \<rho>))
        \<le> Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) \<rho>) "
apply(rule w3)
apply(simp add:eq_valid2)
prefer 2
apply auto
apply(induct n)
apply(simp add:zero_mult_r)
apply(simp add:zero_tr)
apply(simp add:svalid_def)
apply (metis (poly_guards_query) Ident zero_mult_l zero_tr fg less_irrefl not_le sum_1.simps(1))
by (metis (full_types) Ident zero_mult_r zero_mult_l zero_tr denoFun.simps(6) exchange fg monoid_add_class.add.right_neutral mult_exchange mult_sub_allo1 order_refl sum_1.simps(1) tr_allo u_def uu_def)
primrec sum1::"(Mat*com*Mat) list\<Rightarrow>Mat"where
"sum1 []  =zero"|
"sum1  (a#M)  =  (mat_add (uu (fst a ) (snd (snd a)))  (sum1 M  ))  "
primrec sum4::"(Mat*com) list\<Rightarrow>Mat"where
"sum4 [] =zero"|
"sum4 (a#M)  =mat_add (mat_mult (dag (fst a) ) (fst a)) (sum4 M )"

primrec validlist :: "(Mat * com * Mat) list \<Rightarrow> Mat \<Rightarrow> bool" where
"validlist [] Q = True "
| "validlist (a # mcml) Q = (valid (snd (snd a)) (fst (snd a)) Q)"

lemma w4:"\<lbrakk>valid Q S (mat_add (uu m0 P) (uu m1 Q)) \<Longrightarrow>svalid Q S (mat_add (uu m0 P) (uu m1 Q));svalid Q S (mat_add (uu m0 P) (uu m1 Q))
 \<Longrightarrow>svalid (mat_add (uu m0 P) (uu m1 Q)) (While m0 m1 S Q ) P\<rbrakk>\<Longrightarrow>valid Q S (mat_add (uu m0 P) (uu m1 Q))
 \<Longrightarrow>svalid (mat_add (uu m0 P) (uu m1 Q))  (While m0 m1 S Q ) P"
apply auto
done

lemma o1:" Tr (mat_mult P \<rho>) <=Tr (mat_mult P1 \<rho>)\<Longrightarrow>
           ( Tr (mat_mult P1 \<rho>) <= Tr (mat_mult Q (denoFun S \<rho>)) + Tr \<rho> - Tr (denoFun S \<rho>) \<Longrightarrow>
         Tr (mat_mult P \<rho>) <= Tr (mat_mult Q (denoFun S \<rho>)) + Tr \<rho> - Tr (denoFun S \<rho>) ) "
apply(auto)
done

(*   six rules         *)
lemma Skip:"valid P SKIP P"
apply (simp add:valid_def)
done
lemma Utrans:"wellDefined (Utrans U n) \<Longrightarrow>valid  (mat_mult (mat_mult (dag U) P) U)  (Utrans U n) P"
apply(simp add:valid_def)  
apply(simp add:b3)
apply(simp add:exchange)
apply(simp add:b4)
apply(simp add:U_dag)
apply(simp add:Ident)
done
lemma Init:"valid (sum m g P f)  (Init m n) P"
apply(simp add:valid_def, auto)
apply(simp add:m_init)
apply (induct m)
apply (simp add:valid_def, auto)
apply(simp  add:zero_mult_r)
apply(simp add:zero_mult_l)
apply(simp add:mult_allo1)
apply(simp add:mult_allo2)
apply(simp add:tr_allo)
apply(simp add:b3)
done
lemma Seq:"valid P s1 Q\<Longrightarrow>valid Q s2 R\<Longrightarrow>valid P (s1;s2) R"
apply(simp add:valid_def,auto)
apply(drule_tac x=" \<rho>" in spec)
apply(drule_tac x="denoFun s1 \<rho>" in spec)
apply auto
by (metis (full_types) Ident zero_mult_l fg sum_1.simps(1))

lemma Measure:"wellDefined (Cond M) \<Longrightarrow>validlist M Q \<Longrightarrow> valid (sum1 M) (Cond M ) Q" 
apply (induct M)
apply(simp add:valid_def,auto)
apply(simp add:zero_mult_r)
apply(simp add:zero_mult_l)
apply(simp add:zero_tr)
apply(simp add:c)
apply(simp add:valid_def uu_def,auto)
by (smt2 Ident zero_mult_l zero_tr fg sum_1.simps(1))

(* fixpoint theory  *)
axiomatization where
 fixpoint_lemma:"\<forall> n .less  (denoFun (While_n m0 m1 s Q n) \<rho>) (denoFun (While_n m0 m1 s Q (Suc n) ) \<rho>) \<Longrightarrow>
                 \<forall> n. Tr (mat_mult p (denoFun (While_n m0 m1 s Q n) \<rho>) ) \<le> x\<Longrightarrow>
                Tr (mat_mult p (fixpoint  m0 m1 s Q \<rho>) )\<le>x"


lemma While:"wellDefined (While m0 m1 S Q) \<Longrightarrow>valid Q S (mat_add (uu m0 P) (uu m1 Q)) \<Longrightarrow>valid (mat_add (uu m0 P) (uu m1 Q)) 
          (While m0 m1 S Q ) P"
apply(rule eq_valid)
apply(rule w4,auto)
apply(simp add:eq_valid2)
apply(simp add:svalid_def)
unfolding svalid_def
apply auto
apply(rule fixpoint_lemma,auto)
prefer 2
apply (metis (full_types) Ident zero_mult_l zero_tr denoFun.simps(6) exchange fg less_irrefl mult_exchange not_le sum_1.simps(1) u_def uu_def)
by (metis (mono_tags) Ident zero_mult_l rho_zero fg sum_1.simps(1))

lemma order:"\<lbrakk>less P Pa;valid Pa S Q\<rbrakk>\<Longrightarrow>valid P S Q"
apply(simp add:valid_def)
apply(auto)
apply(drule_tac x=" \<rho>" in spec)
apply(rule o1,auto)
apply(simp add:less2)
done
lemma Order:"\<lbrakk>less P Pa;valid Pa S Qa;less Qa Q\<rbrakk>\<Longrightarrow>valid P S Q"
apply(simp add:valid_def,auto)
apply(drule_tac x=" \<rho>" in spec)
apply(rule o1,auto)
by (metis (poly_guards_query) Ident zero_mult_l fg sum_1.simps(1))


(*     about wlp          *)
definition matsum::"nat list\<Rightarrow>nat\<Rightarrow>Mat\<Rightarrow>Mat" where
"matsum m n P=(sum m g P f)"
definition matUtrans::"Mat\<Rightarrow>nat\<Rightarrow>Mat\<Rightarrow>Mat"where
"matUtrans U n P =(mat_mult (mat_mult (dag U) P) U)"

function wlp::"Mat\<Rightarrow>com\<Rightarrow>Mat" where
"wlp P (SKIP) =P"|
"wlp P (Init m n) =matsum m n P"|
"wlp P (Utrans U n) =matUtrans U n P"|
"wlp P ( Seq c1 c2) =wlp (wlp P c2) c1"|
"wlp P (Cond mcl ) = (case mcl of [] \<Rightarrow> zero
  | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp P (fst (snd mc))))  (wlp P (Cond mcr)) ) "   |
"wlp P (While_n m0 m1 s Q n) = (case n of 0\<Rightarrow>I
                               | Suc m\<Rightarrow>
mat_add (uu m0 P)  (uu m1  (wlp (wlp P (While_n m0 m1 s Q m))  s) )     )"|
"wlp P (While m0 m1 s  Q ) = fixpoint_wlp m0 m1 s Q P"
by  pat_completeness auto 
termination 
 apply (relation "measure (\<lambda>(c,m).rank m)", auto )
by (metis rank_pos)

lemma ascent_wlp:"less (wlp P (While_n m0 m1 s Q n))  (wlp P (While_n m0 m1 s Q (Suc n)))"
apply(induct n,auto)
apply (metis (poly_guards_query) Ident zero_mult_l I_zero fg sum_1.simps(1))
by (metis (mono_tags) Ident zero_mult_l fg sum_1.simps(1))

axiomatization where
 fixpoint_wlp_lemma:"\<forall> n .less (wlp P (While_n m0 m1 s Q n))  (wlp P (While_n m0 m1 s Q (Suc n)))\<Longrightarrow>
                 \<forall> n. Tr (mat_mult  (wlp P (While_n m0 m1 s Q n)) p ) \<le> x\<Longrightarrow>
                Tr (mat_mult  (fixpoint_wlp  m0 m1 s Q P) p )\<le>x"
(* Skip   *)
lemma wlp_skip:"valid  (wlp P (SKIP)) SKIP P "
apply(simp add:Skip)
done
(*  Init       *)
lemma wlp_init:"valid (wlp P (Init m n)) (Init m n) P"
apply(simp add:matsum_def)
apply(simp add:Init)
done
(*    Utrans        *)
lemma wlp_utrans: "wellDefined (Utrans U n) \<Longrightarrow>valid (wlp P (Utrans U n)) (Utrans U n) P"
apply(simp add:matUtrans_def)
apply(simp add:Utrans)
done
(*     Cond Measure       *)
lemma wlp_cond: " wellDefined (Cond M) \<Longrightarrow> valid (wlp Q (Cond M )) (Cond M )  Q"
apply(simp add:valid_def uu_def)
by (metis (mono_tags, lifting) Ident zero_mult_l fg less_irrefl not_le sum_1.simps(1) tr_allo tr_allo1)
(*  While_n     *)
lemma wlp_while_n:"Q\<in>predMat\<Longrightarrow> wellDefined (While_n Mata Matb com Matc m) \<Longrightarrow> \<forall>Q. valid (wlp Q com) com Q \<Longrightarrow>
       valid (case num of 0 \<Rightarrow> I | Suc m \<Rightarrow> mat_add (uu Mata Q) (uu Matb (wlp (wlp Q (While_n Mata Matb com Matc m)) com))) (While_n Mata Matb com Matc num) Q"
apply(split nat.split,auto)
apply(simp add:valid_def,auto)
apply(simp add:Ident)
apply (metis zero_mult_r zero_tr diff_0_right order_refl)
apply(simp add:valid_def,auto)
by (metis (mono_tags, lifting) Ident zero_mult_l fg sum_1.simps(1) u_def)

(*While   *)
lemma wlp_while:" wellDefined (While Mata Matb com Matc ) \<Longrightarrow>\<forall>Q. valid (wlp Q com) com Q \<Longrightarrow>
       valid (fixpoint_wlp Mata Matb com Matc Q)  (While Mata Matb com Matc ) Q"
apply(simp add:valid_def,auto)
apply(rule fixpoint_wlp_lemma,auto)
apply (smt2 Ident ascend zero_mult_l fg sum_1.simps(1))
by (metis (full_types) Ident zero_mult_l fg sum_1.simps(1))

(*    Seq     *)
lemma wlp_seq: "\<forall>Q. valid (wlp Q coma) coma Q \<Longrightarrow> \<forall>Q. valid (wlp Q comb) comb Q 
   \<Longrightarrow> valid (wlp (wlp Q comb) coma) (coma; comb) Q"
apply (drule_tac x = "(wlp Q comb)" in  spec)
apply (drule_tac x = "Q" in  spec)
apply (rule Seq, auto)
done
lemma soundwp1: "wellDefined S \<Longrightarrow>\<forall> Q. valid (wlp Q S) S  Q"
apply (induct S,auto)
apply (cut_tac wlp_skip, auto)
apply (cut_tac wlp_init, auto)
apply (cut_tac wlp_utrans, auto)
apply (cut_tac Q = Q and  coma = "S1" and comb = "S2" in wlp_seq, auto)
apply (cut_tac wlp_cond, auto)
defer
apply (metis (poly_guards_query) Ident zero_mult_l eq_valid fg less_irrefl not_le sum_1.simps(1) svalid_def)
apply(cut_tac Mata="Mat1" and Matb="Mat2" and Matc="Mat3" and com="S" and Q="Q" in wlp_while,auto)
by (metis (poly_guards_query) Ident zero_mult_l fg order_refl sum_1.simps(1) tr_allo tr_allo1 valid_def)

lemma WLPsound:"Q\<in>predMat\<Longrightarrow>wellDefined S\<Longrightarrow>valid (wlp Q S) S Q"
apply(simp add: soundwp1)
done
lemma ord_wlp:"Q\<in>predMat\<Longrightarrow>P\<in>predMat\<Longrightarrow>wellDefined S\<Longrightarrow>less P (wlp Q S)\<Longrightarrow>valid P S Q"
apply(rule_tac Pa="wlp Q S" in order,auto)
apply(rule WLPsound)
apply auto
done
declare uu_def[simp]
ML_file "Quantum_Hoare_tac.ML"
method_setup vcg = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (quantum_hoare_tac ctxt (K all_tac))) *}
method_setup vcg_simp = {*
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (quantum_hoare_tac ctxt (asm_full_simp_tac ctxt))) *}
end








