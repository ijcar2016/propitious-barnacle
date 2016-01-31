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
"M_sum [] =zero"|
"M_sum (a#M) =mat_add (mat_mult (dag (fst a) ) (fst a)) (M_sum M )"
primrec sum::"nat list\<Rightarrow>nT\<Rightarrow>Mat\<Rightarrow>Mat" where
"sum [] f1 p=p"|
"sum (b#nl) f1 p = mat_add (mat_mult (mat_mult (f1 b) p) (dag (f1 b)) ) (sum nl f1 p )"
primrec sum_t::"nat list\<Rightarrow>nT\<Rightarrow>Mat\<Rightarrow>Mat"where
"sum_t [] f1 p=p"|
"sum_t (b#nl) f1 p = mat_add (mat_mult (mat_mult (dag (f1 b)) p)  (f1 b) ) (sum_t nl f1 p )"
primrec sum_1::"nat list\<Rightarrow>nT\<Rightarrow>Mat" where
"sum_1 [] f1 =I"|
"sum_1 (b#nl) f1 =mat_add (mat_mult (f1 b) (dag (f1 b))) (sum_1 nl f1)"
primrec sum_2::"nat list\<Rightarrow>nT\<Rightarrow>Mat" where
"sum_2 [] f1 =I"|
"sum_2 (b#nl) f1 =mat_add (mat_mult (dag (f1 b))  (f1 b)   ) (sum_2 nl f1)"

(*u a b =ab(dag a) *)
definition u::"Mat\<Rightarrow>Mat\<Rightarrow>Mat"where
"u a b= mat_mult (mat_mult a b) (dag a)"
(*u a b =(dag a)ba *)
definition uu::"Mat\<Rightarrow>Mat\<Rightarrow>Mat"where
"uu a b= mat_mult (mat_mult (dag a) b)  a"



 (*the rank function that defined for the denoFun*)
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
by (smt One_nat_def Suc_less_eq le_imp_less_Suc list.case(1) list.case(2) list.exhaust monoid_add_class.add.left_neutral monoid_add_class.add.right_neutral not_le order_refl plus_nat.simps(2) rank.simps(5) trans_le_add1 trans_le_add2)

(*definition of fixpoint*)
definition fixpoint::"Mat\<Rightarrow>Mat\<Rightarrow>com\<Rightarrow>Mat\<Rightarrow>Mat\<Rightarrow>Mat"where
"fixpoint m0 m1 s Q p=fixPoint"
definition fixpoint_wlp::"Mat\<Rightarrow>Mat\<Rightarrow>com\<Rightarrow>Mat\<Rightarrow>Mat\<Rightarrow>Mat"where
"fixpoint_wlp  m0 m1 s Q p=fixPoint_wlp"

(*the denotational semantics of quantum programs  *)
function denoFun::"com\<Rightarrow>Mat\<Rightarrow>Mat" where
"denoFun SKIP p=p"|
"denoFun (Utrans U n) p=mat_mult (mat_mult U p) (dag U)"|
"denoFun (Init m n) p=sum m f p "|
"denoFun (s1;s2) p= denoFun s2 (denoFun s1  p )"|
"denoFun (Cond mcl) p=  (case mcl of [] \<Rightarrow> zero
  | mc # mcr \<Rightarrow> mat_add (denoFun((fst (snd mc))) (u (fst mc) p) ) (denoFun (Cond mcr) p)) "|
"denoFun (While_n m0 m1 s Q n) p= (case n of 0\<Rightarrow>zero
                               | Suc m\<Rightarrow>
mat_add (u m0 p)  (denoFun (While_n m0 m1 s Q m) ( denoFun s (u m1 p))   ) )"  
|"denoFun (While m0 m1 s Q) p= fixpoint  m0 m1 s Q  p"
by  pat_completeness auto 
termination 
 apply (relation "measure (\<lambda>(c,m).rank c)", auto )
by (metis rank_pos)

lemma rho: "a\<in>rhoMat\<Longrightarrow>(u m a) \<in>rhoMat"
by (metis a less3 rho_zero u_def)

fun rankf :: "com\<Rightarrow>nat" where
"rankf SKIP =1"|
"rankf (Utrans U n) =1"|
"rankf (Init m n) =1"|
"rankf (s1;s2) =1+ rankf s2 + (rankf s1 )"|
"rankf (Cond mcl) =  (case mcl of [] \<Rightarrow> 1
  | mc # mcr \<Rightarrow> 1+rankf (fst (snd mc)) + rankf (Cond mcr)) "|
"rankf (While_n m0 m1 s Q n)=  1 + rankf (s)" |
"rankf  (While  m0 m1 s Q )= 1 + rankf s"

lemma wellDefined_aux: "(x, xa, xb) \<in> set mcl \<Longrightarrow>
       (xc, xd) \<in> Basic_BNFs.snds (x, xa, xb) \<Longrightarrow>
       xe \<in> Basic_BNFs.fsts (xc, xd) \<Longrightarrow> rankf xe < (case mcl of [] \<Rightarrow> 1 | mc # mcr \<Rightarrow> 1 + rankf (fst (snd mc)) + rankf (Cond mcr))"
apply (induct mcl, auto)
by (metis fst_conv fsts.cases not_add_less1 not_less_eq sndI snds.cases)


(*the conditions that the commands should meet iff they are well-defined  *)
function wellDefined :: "com\<Rightarrow>bool" where
"wellDefined SKIP =True"|
"wellDefined (Utrans a n) = (a \<in> uMat)"|
"wellDefined (Init m n) =((sum_1 m f =I)\<and>(sum_2 m f=I))"|
"wellDefined (s1;s2) = (wellDefined (s1) & wellDefined (s2))"|
"wellDefined (Cond mcl) = ((M_sum mcl=I) \<and> 
(\<forall>a aa b aaa ba xaaa. (a, aa, b) \<in> set mcl \<longrightarrow>
       (aaa, ba) \<in> Basic_BNFs.snds (a, aa, b) \<longrightarrow>
       xaaa \<in> Basic_BNFs.fsts (aaa, ba) \<longrightarrow> wellDefined xaaa))"|
"wellDefined (While_n m0 m1 s Q n)= ((mat_add (mat_mult (dag m0) m0)  (mat_mult (dag m1) m1) =I) \<and> (wellDefined s) )" |
"wellDefined  (While  m0 m1 s Q )=((mat_add (mat_mult (dag m0) m0)  (mat_mult (dag m1) m1) =I)  \<and> (wellDefined s)  )  "
by  pat_completeness auto
termination 
apply (relation "measure (\<lambda>(c).rankf c)", auto)
apply (rule wellDefined_aux, auto)
done

lemma au:" denoFun s1 a \<in> rhoMat \<Longrightarrow>\<forall>a. a \<in> rhoMat\<longrightarrow> denoFun s2 a \<in> rhoMat \<Longrightarrow> a \<in> rhoMat \<longrightarrow>denoFun s2 (denoFun s1 a) \<in> rhoMat"
apply auto
done

lemma init_rho: " a \<in> rhoMat \<Longrightarrow> sum list f a \<in> rhoMat"
apply(induct list,auto)
by (metis a less3 less6 rho_zero zero_add)

lemma while_rho:" \<forall>a. a \<in> rhoMat \<longrightarrow> denoFun s a \<in> rhoMat \<Longrightarrow>\<forall>a. a \<in> rhoMat\<longrightarrow>
    (case na of 0 \<Rightarrow> zero | Suc m \<Rightarrow> mat_add (u Mat1 a) (denoFun (While_n Mat1 Mat2 s Mat3 m) (denoFun s (u Mat2 a)))) \<in> rhoMat"
apply(induct na,auto)
apply (metis rho u_def zero_mult_l)
apply(subgoal_tac "(u Mat2 a)\<in>rhoMat")
prefer 2
apply (metis rho)
apply(subgoal_tac " (denoFun s (u Mat2 a))\<in>rhoMat")
prefer 2 
apply metis
apply(drule_tac x="(denoFun s (u Mat2 a))" in spec)
by (metis a less3 less6 rho_zero u_def zero_add)
lemma rho1_aux:"\<forall>a. a \<in> rhoMat \<longrightarrow>less zero (fixpoint x1 x2 s x4 a) \<Longrightarrow>\<forall>a. a \<in> rhoMat \<longrightarrow> fixpoint x1 x2 s x4 a \<in> rhoMat"
by (simp add: a)
lemma rho2_aux:" \<forall>a. a \<in> rhoMat \<longrightarrow> denoFun s a \<in> rhoMat  \<Longrightarrow>\<forall>a. a \<in> rhoMat\<longrightarrow>
           basic.less zero (case n of 0 \<Rightarrow> zero | Suc m \<Rightarrow> mat_add (u x1 a) 
         (denoFun (While_n x1 x2 s x4 m) (denoFun s (u x2 a))))"
apply(induct n,auto)
apply (metis I_zero less3 zero_mult_l)
apply(subgoal_tac "(u x2 a)\<in>rhoMat")
prefer 2
apply (metis rho)
apply(subgoal_tac " (denoFun s (u x2 a))\<in>rhoMat")
prefer 2 
apply metis
apply(drule_tac x="(denoFun s (u x2 a))" in spec)
by (metis denoFun.simps(6) old.nat.simps(5) rho_zero while_rho)


(*fixpoint theory   [while_n]\<le>[while_n+1] \<Longrightarrow>0\<le>[while_n] \<Longrightarrow>fixpoint\<ge>0                        *)
axiomatization where
fixpoint_rho_lemma:"a\<in>rhoMat\<Longrightarrow>\<forall>n. less (denoFun (While_n x1 x2 s x4 n) a) (denoFun (While_n x1 x2 s x4 n) a) \<Longrightarrow>
\<forall>n. less zero (denoFun (While_n x1 x2 s x4 n) a) \<Longrightarrow>less zero(fixpoint x1 x2 s x4 a)" and
(*  Tr p*[while_n] \<le>Tr p*[while_n+1] \<Longrightarrow> Tr p*[while_n] \<le>x\<Longrightarrow>Tr p*fixpoint\<le>x                  *)
 fixpoint_lemma:" \<rho>\<in>rhoMat\<Longrightarrow>\<forall>n. Tr (mat_mult p (denoFun (While_n m0 m1 s Q n) \<rho>)) \<le> Tr (mat_mult p (denoFun (While_n m0 m1 s Q (Suc n) ) \<rho>)) \<Longrightarrow>
                 \<forall> n.  Tr (mat_mult p (denoFun (While_n m0 m1 s Q n) \<rho>) ) \<le> x \<Longrightarrow>
             Tr (mat_mult p (fixpoint  m0 m1 s Q \<rho>) )\<le>x"

lemma while_rho1_aux:" \<forall>a. a \<in> rhoMat \<longrightarrow> denoFun s a \<in> rhoMat \<Longrightarrow>
        \<forall>a. a \<in> rhoMat \<longrightarrow> basic.less (denoFun (While_n x1 x2 s x4 n) a) (denoFun (While_n x1 x2 s x4 n) a)"
apply(induct n,auto)
apply (metis I_zero less3 zero_mult_l)
apply(rule less1)
by (simp add: rho)

lemma while_rho1:"\<forall>a. a \<in> rhoMat \<longrightarrow> denoFun s a \<in> rhoMat \<Longrightarrow>\<forall>a. a \<in> rhoMat \<longrightarrow> fixpoint x1 x2 s x4 a \<in> rhoMat"
apply(rule rho1_aux,auto)
apply(rule fixpoint_rho_lemma)
apply simp
apply(rule allI)
apply(cut_tac while_rho1_aux,auto)
apply(simp add:rho2_aux)
done

lemma cond_rho_aux1:"\<forall>ab. ab\<in>rhoMat\<longrightarrow> denoFun aa ab \<in> rhoMat
\<Longrightarrow>\<forall>ab. ab\<in>rhoMat\<longrightarrow> denoFun aa (u a ab) \<in> rhoMat"
apply auto
apply(subgoal_tac "(u a ab)\<in>rhoMat")
prefer 2
using rho apply auto[1]
apply(drule_tac x="u a ab" in spec)
apply auto
done

lemma cond_rho_aux:"(denoFun aa (u a ab))\<in>rhoMat \<Longrightarrow>
 (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (denoFun (fst (snd mc)) (u (fst mc) ab)) (denoFun (Cond mcr) ab)) \<in> rhoMat
 \<Longrightarrow>mat_add (denoFun aa (u a ab))
        (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (denoFun (fst (snd mc)) (u (fst mc) ab)) (denoFun (Cond mcr) ab))
       \<in> rhoMat"
by (metis (lifting) a less6 rho_zero zero_add)

lemma cond_rho:" (\<forall>a aa b aaa ba xaaa.
\<forall>a. a \<in> rhoMat \<longrightarrow> (a, aa, b) \<in> set x \<longrightarrow>  (aaa, ba) \<in> Basic_BNFs.snds (a, aa, b) \<longrightarrow>
               xaaa \<in> Basic_BNFs.fsts (aaa, ba) \<longrightarrow> denoFun xaaa a \<in> rhoMat) \<Longrightarrow> \<forall>a. a \<in> rhoMat \<longrightarrow>
           (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (denoFun (fst (snd mc)) (u (fst mc) a)) (denoFun (Cond mcr) a)) \<in> rhoMat"
apply(induct x,auto)
apply (metis Nitpick.case_nat_unfold denoFun.simps(1) while_rho)
apply(drule_tac x="ab"in spec,auto)
apply(rule cond_rho_aux,auto)
apply(cut_tac cond_rho_aux1,auto)
proof -
  fix a :: Mat and aa :: com and b :: Mat and xa :: "(Mat \<times> com \<times> Mat) list" and ab :: Mat and aba :: Mat
  assume "aba \<in> rhoMat"
  have f1: "\<forall>b ba. \<not> ba \<or> b \<or> \<not> ba \<le> b \<or> b"
    by simp
  have "\<forall>p. (p zero\<Colon>bool) \<le> p I"
    by (metis (no_types) I_zero Ident a less2 zero_mult_l)
  hence "I = zero"
    using f1 by (meson insertCI singletonD)
  thus "denoFun aa aba \<in> rhoMat"
    by (metis (full_types) I_zero Ident a zero_mult_l)
qed

(* a\<in>rhoMat\<Longrightarrow>denoFun s a \<in>rhoMat      *)
lemma bb:"\<forall>a. a\<in>rhoMat\<longrightarrow>(denoFun s a) \<in>rhoMat"
apply(induct s,auto)
apply(rule init_rho,auto)
apply (metis rho u_def)
prefer 3
apply(cut_tac while_rho,auto)
prefer 2
apply(cut_tac while_rho1,auto)
apply(cut_tac cond_rho,auto)
done

lemma b:"a\<in>rhoMat\<Longrightarrow>(denoFun s a) \<in>rhoMat"
apply(simp add:bb)
done

(*the ascending  order of denotational semantics of while_n *)
lemma ascend:"\<forall>\<rho>. \<rho>\<in>rhoMat\<longrightarrow> less  (denoFun (While_n m0 m1 s Q n) \<rho>)   (denoFun (While_n m0 m1 s Q (Suc n) ) \<rho>) "
apply(induct n,auto)
apply (metis less3 rho_zero u_def zero_add)
apply(rule less1)
by (metis Nitpick.case_nat_unfold b rho)

lemma ascend1:"less P I\<Longrightarrow>\<forall>\<rho>. \<rho>\<in>rhoMat\<longrightarrow>Tr (mat_mult (mat_sub I P) (denoFun (While_n m0 m1 s Q n) \<rho>)) \<le>
   Tr (mat_mult (mat_sub I P)  (denoFun (While_n m0 m1 s Q (Suc n) ) \<rho>))"
apply(induct n,auto)
apply (metis less4 less5 rho rho_zero sub_self zero_add zero_mult_r zero_tr)
apply(simp add:mult_allo2)
apply(simp add:tr_allo)
apply(subgoal_tac "(denoFun s (u m1 \<rho>))\<in>rhoMat")
prefer 2
apply (metis b rho)
apply(drule_tac x="(denoFun s (u m1 \<rho>))"in spec,auto)
done

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


lemma temp:"Tr (sum m f \<rho> ) =Tr  (mat_mult \<rho> (sum_2 m  f) ) "
apply(induct m)
apply auto
apply (metis Ident exchange)
by (metis exchange mult_allo2 mult_exchange tr_allo)

lemma m_init:"sum_1 m  f=I\<Longrightarrow>sum_2 m  f=I\<Longrightarrow>Tr (sum m f \<rho> ) =Tr \<rho>"
apply(simp add:temp)
apply(subgoal_tac " Tr (mat_mult \<rho> I) = Tr (mat_mult I \<rho> ) ")
apply(simp add:Ident)
apply(simp add:exchange)
done

lemma neq:"(b::real)\<le>(d::real)\<Longrightarrow>a+d\<le>(c::real)\<Longrightarrow>a+b\<le>c"
apply auto
done

lemma While_n:" mat_add (mat_mult (dag m0) m0) (mat_mult (dag m1) m1) = I \<Longrightarrow>
        less (mat_add (uu m0 P) (uu m1 Q)) I\<Longrightarrow>
         valid Q S (mat_add (uu m0 P) (uu m1 Q)) \<Longrightarrow>
    \<forall>\<rho>. \<rho> \<in> rhoMat \<longrightarrow> Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) (denoFun S \<rho>)) \<le> Tr (mat_mult (mat_sub I Q) \<rho>) \<Longrightarrow>
        \<forall>\<rho>. \<rho> \<in> rhoMat \<longrightarrow>
   Tr (mat_mult (mat_sub I P) (denoFun (While_n m0 m1 S Q n) \<rho>)) \<le> Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) \<rho>) "
apply(induct n,auto)
defer
apply(subgoal_tac "(denoFun S (u m1 \<rho>)) \<in>rhoMat")
prefer 2
apply (metis b rho)
apply(drule_tac x=" (denoFun S (u m1 \<rho>))" in spec)
apply(simp add:mult_allo2)
apply(simp add:tr_allo)
apply(cut_tac a="Tr (mat_mult (mat_sub I P) (u m0 \<rho>))" and c="Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) \<rho>)
"and b=" Tr (mat_mult (mat_sub I P)
                (case n of 0 \<Rightarrow> zero
                 | Suc m \<Rightarrow> mat_add (u m0 (denoFun S (u m1 \<rho>))) (denoFun (While_n m0 m1 S Q m) (denoFun S (u m1 (denoFun S (u m1 \<rho>)))))))" 
and d=" Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) (denoFun S (u m1 \<rho>))) " in neq)
apply auto
apply(subgoal_tac "(u m1 \<rho>) \<in>rhoMat")
prefer 2
apply (metis rho)
apply(drule_tac x=" (u m1 \<rho>)" in spec)
apply(cut_tac a=" Tr (mat_mult (mat_sub I P) (u m0 \<rho>))" and c="Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) \<rho>)"
and b=" Tr (mat_mult (mat_sub I (mat_add (uu m0 P) (uu m1 Q))) (denoFun S (u m1 \<rho>)))"
and d=" Tr (mat_mult (mat_sub I Q) (u m1 \<rho>))" in neq)
apply auto
apply (smt Ident b3 mult_allo1 mult_exchange mult_sub_allo1 tr_allo tr_allo1 u_def uu_def)
apply(simp add:zero_mult_r)
by (metis less4 less5 rho_zero sub_self zero_tr)

primrec sum1::"(Mat*com*Mat) list\<Rightarrow>Mat"where
"sum1 []  =zero"|
"sum1  (a#M)  =  (mat_add (uu (fst a ) (snd (snd a)))  (sum1 M  ))  "
primrec sum4::"(Mat*com) list\<Rightarrow>Mat"where
"sum4 [] =zero"|
"sum4 (a#M)  =mat_add (mat_mult (dag (fst a) ) (fst a)) (sum4 M )"

primrec validlist :: "(Mat * com * Mat) list \<Rightarrow> Mat \<Rightarrow> bool" where
"validlist [] Q = True "
| "validlist (a # mcml) Q = ( (valid (snd (snd a)) (fst (snd a)) Q) \<and> (validlist  mcml Q) )"

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
lemma Initfact: "\<rho> \<in> rhoMat \<Longrightarrow> Tr (mat_mult (sum_t m f P ) \<rho>) = Tr (mat_mult P (sum m f \<rho> ))"
apply (induct m,auto)
apply(simp add:mult_allo1)
apply(simp add:mult_allo2)
apply(simp add:tr_allo)
apply(simp add:b3)
done
lemma mea_\<rho>:"wellDefined (Cond M) \<Longrightarrow>\<forall>\<rho>. \<rho> \<in> rhoMat \<longrightarrow> Tr (mat_mult (sum1 M) \<rho>) \<le> Tr (mat_mult Q (denoFun (Cond M) \<rho>)) + Tr (mat_mult (M_sum M) \<rho>) - Tr (denoFun (Cond M) \<rho>)
\<Longrightarrow> \<forall>\<rho>. \<rho> \<in> rhoMat \<longrightarrow> Tr (mat_mult (sum1 M) \<rho>) \<le> Tr (mat_mult Q (denoFun (Cond M) \<rho>)) + Tr \<rho> - Tr (denoFun (Cond M) \<rho>)"
by (metis Ident wellDefined.simps(5))
lemma neq1:"(b::real)\<le>d\<Longrightarrow>a\<le>c\<Longrightarrow>(b+a)\<le>(d+c)"
apply auto
done

lemma neq3:"(a::real)\<le>b\<Longrightarrow>c\<le>a\<Longrightarrow>b\<le>d\<Longrightarrow>c\<le>d"
apply auto
done

lemma neq2:"(a::real)\<le>c\<Longrightarrow>c\<le>b\<Longrightarrow>a\<le>b"
by auto

lemma mea1:"validlist M Q \<Longrightarrow> \<forall>\<rho>. \<rho> \<in> rhoMat \<longrightarrow>
        Tr (mat_mult (sum1 M) \<rho>) \<le> Tr (mat_mult Q (denoFun (Cond M) \<rho>)) + Tr (mat_mult (M_sum M) \<rho>) - Tr (denoFun (Cond M) \<rho>)"
apply(induct M,auto)
apply (smt I_zero less4 rho_zero zero_mult_l zero_mult_r zero_tr)
apply(simp add:mult_allo1)
apply(simp add:tr_allo)
apply(simp add:mult_allo2)
apply(simp add:tr_allo)
apply(cut_tac b="Tr (mat_mult (sum1 M) \<rho>)" and d="Tr (mat_mult Q
                   (case M of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (denoFun (fst (snd mc)) (u (fst mc) \<rho>)) (denoFun (Cond mcr) \<rho>))) +
              Tr (mat_mult (M_sum M) \<rho>) -
              Tr (case M of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (denoFun (fst (snd mc)) (u (fst mc) \<rho>)) (denoFun (Cond mcr) \<rho>))"
and a=" Tr (mat_mult (uu a b) \<rho>)" and c=" Tr (mat_mult Q (denoFun aa (u a \<rho>)))+ (Tr (mat_mult (mat_mult (dag a) a) \<rho>))-Tr (denoFun aa (u a \<rho>))"
in neq1,auto)
apply(simp add:valid_def)
apply(subgoal_tac "\<rho>\<in>rhoMat\<Longrightarrow>(u a \<rho>)\<in>rhoMat")
prefer 2
apply (metis rho)
apply(drule_tac x="(u a \<rho>)"in spec)
apply(drule_tac x="(u a \<rho>)"in spec,auto)
by (metis exchange mult_exchange u_def uu_def)

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

lemma Init:"wellDefined (Init m n) \<Longrightarrow>valid (sum_t m f P)  (Init m n) P"
apply(simp add:valid_def, auto)
apply(simp add:m_init)
apply (simp add: Initfact)
done

lemma Seq:"valid P s1 Q\<Longrightarrow>valid Q s2 R\<Longrightarrow>valid P (s1;s2) R"
apply(simp add:valid_def,auto)
apply(drule_tac x=" \<rho>" in spec)
apply(subgoal_tac " \<rho> \<in> rhoMat\<Longrightarrow>denoFun s1 \<rho> \<in> rhoMat")
apply auto
by (metis b)

lemma Measure:"wellDefined (Cond M) \<Longrightarrow> validlist M Q \<Longrightarrow> valid (sum1 M) (Cond M ) Q" 
unfolding valid_def
apply(rule mea_\<rho>)
apply(simp)
apply(rule mea1,auto)
done

lemma While:"wellDefined (While m0 m1 S Q) \<Longrightarrow> less (mat_add (uu m0 P) (uu m1 Q)) I\<Longrightarrow>less P I\<Longrightarrow>valid Q S (mat_add (uu m0 P) (uu m1 Q)) \<Longrightarrow>valid (mat_add (uu m0 P) (uu m1 Q)) 
          (While m0 m1 S Q ) P"
apply(rule eq_valid)
apply(rule w4,auto)
apply(simp add:eq_valid2)
apply(simp add:svalid_def,auto)
apply (rule fixpoint_lemma)
apply(simp)
apply (metis ascend1)
apply (rule allI)
apply(subgoal_tac "less zero (mat_sub I P)")
prefer 2
apply (metis less5 sub_self)
apply(cut_tac While_n, auto)
done

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
apply(cut_tac a=" Tr (mat_mult Pa \<rho>)"and b="Tr (mat_mult Qa (denoFun S \<rho>)) + Tr \<rho> - Tr (denoFun S \<rho>)"
and c=" Tr (mat_mult P \<rho>)" and d="Tr (mat_mult Q (denoFun S \<rho>)) + Tr \<rho> - Tr (denoFun S \<rho>)"in neq3,auto)
apply (metis less2)
by (metis b less2)

(*     about wlp          *)
definition matsum::"nat list\<Rightarrow>nat\<Rightarrow>Mat\<Rightarrow>Mat" where
"matsum m n P=(sum_t m f P )"
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

lemma while_n_aux:" Tr (mat_mult (uu Matb  (wlp (case num of 0 \<Rightarrow> I | Suc m \<Rightarrow>
    mat_add (uu Mata Q) (uu Matb (wlp (wlp Q (While_n Mata Matb com Matc m)) com))) com)   ) \<rho>) =
Tr (mat_mult (wlp (case num of 0 \<Rightarrow> I | Suc m \<Rightarrow>
    mat_add (uu Mata Q) (uu Matb (wlp (wlp Q (While_n Mata Matb com Matc m)) com))) com) (u Matb \<rho>))  "
by (metis b3 u_def uu_def)
lemma while_n_aux2:"Tr (mat_mult (uu Mata Q) \<rho>) =Tr (mat_mult Q (u Mata \<rho>))"
apply (metis b3 u_def uu_def)
done
(*fixpoint \<forall>n.  Tr ((wlp Q [while_n])+(I-Q)*[while_n]) =x \<Longrightarrow>  Tr (fixpoint1+(I-Q)fixpoint2) = x      *)
axiomatization where
 fixpoint_wlp_lemma:" \<rho>\<in>rhoMat  \<Longrightarrow>
 \<forall> n. Tr (mat_add (mat_mult (wlp Q (While_n Mata Matb com Matc n) ) \<rho>) 
 (mat_mult (mat_sub I Q) (denoFun  (While_n Mata Matb com Matc n) \<rho>)) )  = x\<Longrightarrow>
      Tr (mat_add (mat_mult (fixpoint_wlp Mata Matb com Matc Q) \<rho>) (mat_mult (mat_sub I Q) (fixpoint Mata Matb com Matc \<rho>))) =x" 

lemma wlp_while_aux1:" \<forall>\<rho>. \<rho>\<in>rhoMat\<longrightarrow>Tr (mat_mult (wlp Q (While_n Mata Matb com Matc num) ) \<rho>) =Tr (mat_mult Q  (denoFun  (While_n Mata Matb com Matc num) \<rho>))
+Tr \<rho>-Tr  (denoFun  (While_n Mata Matb com Matc num) \<rho>) \<Longrightarrow> \<forall>\<rho>. \<rho>\<in>rhoMat\<longrightarrow>Tr (mat_mult (wlp Q (While_n Mata Matb com Matc num) ) \<rho>)+Tr (mat_mult (mat_sub I Q)
       (denoFun  (While_n Mata Matb com Matc num) \<rho>)) =Tr \<rho>"
by (smt Ident mult_sub_allo1 tr_allo1)

lemma wlp_while_aux:" wellDefined (While_n Mata Matb com Matc m) \<Longrightarrow>
 \<forall>Q \<rho>. \<rho> \<in> rhoMat \<longrightarrow> Tr (mat_mult (wlp Q com) \<rho>) = Tr (mat_mult Q (denoFun com \<rho>)) + Tr \<rho> - Tr (denoFun com \<rho>) \<Longrightarrow>
       \<forall>\<rho>. \<rho>\<in>rhoMat\<longrightarrow>Tr (mat_mult (wlp Q (While_n Mata Matb com Matc num) ) \<rho>)+Tr (mat_mult (mat_sub I Q)
       (denoFun  (While_n Mata Matb com Matc num) \<rho>)) =Tr \<rho>"
apply(rule wlp_while_aux1,simp)
apply(induct num,auto)
apply (smt Ident zero_mult_r)
apply(simp add:mult_allo1)
apply(simp add:tr_allo)
apply(simp add:while_n_aux)
apply(simp add:mult_allo2)
apply(simp add:tr_allo)
apply(subgoal_tac "(denoFun com (u Matb \<rho>))\<in>rhoMat")
prefer 2
apply (metis b rho)
apply(drule_tac x="(denoFun com (u Matb \<rho>))"in spec)
apply(drule_tac x="(case num of 0 \<Rightarrow> I | Suc m \<Rightarrow> mat_add (uu Mata Q) (uu Matb (wlp (wlp Q (While_n Mata Matb com Matc m)) com)))"in spec)
apply(subgoal_tac "(u Matb \<rho>)\<in>rhoMat")
prefer 2
apply (metis rho)
apply(drule_tac x="(u Matb \<rho>)"in spec)
apply(simp add:while_n_aux2)
apply(simp add:u_def)
apply(simp add:exchange)
by (smt Ident mult_allo1 mult_exchange tr_allo)

lemma aux:"Tr (mat_mult (fixpoint_wlp Mata Matb com Matc Q) \<rho>)+Tr (mat_mult (mat_sub I Q) (fixpoint Mata Matb com Matc \<rho>))
 =Tr \<rho>
\<Longrightarrow> Tr (mat_mult (fixpoint_wlp Mata Matb com Matc Q) \<rho>)
         =Tr (mat_mult Q (fixpoint Mata Matb com Matc \<rho>)) + Tr \<rho> - Tr (fixpoint Mata Matb com Matc \<rho>)"
by (smt Ident mult_sub_allo1 tr_allo1)

lemma aux1:"Tr (mat_add (mat_mult (fixpoint_wlp Mata Matb com Matc Q) \<rho>) (mat_mult (mat_sub I Q) (fixpoint Mata Matb com Matc \<rho>))) =Tr \<rho>
\<Longrightarrow>Tr (mat_mult (fixpoint_wlp Mata Matb com Matc Q) \<rho>) + Tr (mat_mult (mat_sub I Q) (fixpoint Mata Matb com Matc \<rho>)) = Tr \<rho>"
by (metis tr_allo)

(*wlp_init*)
lemma w_init:"\<rho>\<in>rhoMat\<Longrightarrow>wellDefined (Init m n) \<Longrightarrow>
\<forall>Q. Tr (mat_mult (wlp Q (Init m n)) \<rho>) =Tr (mat_mult Q (denoFun (Init m n) \<rho>)) +Tr \<rho>-Tr (denoFun (Init m n) \<rho>)"
apply(simp add:matsum_def)
apply(simp add:m_init)
apply(simp add:Initfact)
done

(*wlp_utrans*)
lemma w_utrans:"\<rho>\<in>rhoMat\<Longrightarrow>wellDefined (Utrans U n) \<Longrightarrow>
\<forall>Q. Tr (mat_mult (wlp Q (Utrans U n)) \<rho>) =Tr (mat_mult Q (denoFun (Utrans U n) \<rho>)) +Tr \<rho>-Tr (denoFun (Utrans U n) \<rho>)"
apply(simp add:matUtrans_def)
by (metis (no_types, hide_lams) Ident U_dag add.commute b3 diff_0 diff_add_cancel diff_diff_eq2 diff_minus_eq_add exchange minus_diff_eq mult_exchange mult_sub_allo1 tr_allo1 u_def uu_def)

(* wlp_seq *)
lemma w_seq:"\<rho>\<in>rhoMat\<Longrightarrow>wellDefined (Sa;Sb) \<Longrightarrow>
      \<forall>Q \<rho>. \<rho> \<in> rhoMat \<longrightarrow> Tr (mat_mult (wlp Q Sa) \<rho>) = Tr (mat_mult Q (denoFun Sa \<rho>)) + Tr \<rho> - Tr (denoFun Sa \<rho>) \<Longrightarrow>
       \<forall>Q \<rho>. \<rho> \<in> rhoMat \<longrightarrow> Tr (mat_mult (wlp Q Sb) \<rho>) = Tr (mat_mult Q (denoFun Sb \<rho>)) + Tr \<rho> - Tr (denoFun Sb \<rho>) \<Longrightarrow>
\<forall>Q. Tr (mat_mult (wlp Q (Sa;Sb)) \<rho>) =Tr (mat_mult Q (denoFun (Sa;Sb) \<rho>)) +Tr \<rho>-Tr (denoFun (Sa;Sb) \<rho>)"
apply auto
apply(drule_tac x="Q"in spec)
apply(drule_tac x="Q"in spec)
apply(drule_tac x="\<rho>"in spec)
apply(subgoal_tac "(denoFun Sa \<rho>)\<in>rhoMat")
prefer 2
apply (metis b)
apply(drule_tac x="(denoFun Sa \<rho>)"in spec,auto)
done

lemma cond_aux:" M_sum x = I \<Longrightarrow> \<forall>Q \<rho>. \<rho> \<in> rhoMat \<longrightarrow>
          Tr (mat_mult (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) \<rho>) =
          Tr (mat_mult Q (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (denoFun (fst (snd mc)) (u (fst mc) \<rho>)) (denoFun (Cond mcr) \<rho>))) +
          Tr (mat_mult (M_sum x) \<rho>) -
          Tr (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (denoFun (fst (snd mc)) (u (fst mc) \<rho>)) (denoFun (Cond mcr) \<rho>))\<Longrightarrow>
    \<forall>Q \<rho>. \<rho> \<in> rhoMat \<longrightarrow>
          Tr (mat_mult (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) \<rho>) =
          Tr (mat_mult Q (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (denoFun (fst (snd mc)) (u (fst mc) \<rho>)) (denoFun (Cond mcr) \<rho>))) +
          Tr \<rho> -
          Tr (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (denoFun (fst (snd mc)) (u (fst mc) \<rho>)) (denoFun (Cond mcr) \<rho>))"
by (simp add: Ident)
lemma cond_aux2:"\<forall>\<rho>. \<rho>\<in>rhoMat\<longrightarrow>  Tr (mat_mult (wlp Q aa) \<rho>) = Tr (mat_mult Q (denoFun aa \<rho>)) + Tr \<rho> - Tr (denoFun aa \<rho>) \<Longrightarrow>
 \<forall>\<rho>. \<rho>\<in>rhoMat\<longrightarrow> Tr (mat_mult (uu a (wlp Q aa)) \<rho>) = Tr (mat_mult Q (denoFun aa (u a \<rho>))) + (Tr (mat_mult (mat_mult (dag a) a) \<rho>) - Tr (denoFun aa (u a \<rho>)))"
apply auto
apply(subgoal_tac "(u a \<rho>)\<in>rhoMat")
prefer 2
apply (simp add: rho)
apply(drule_tac x="(u a \<rho>)"in spec)
apply(simp add:u_def)
apply(simp add:uu_def)
using b3 b4 exchange by auto

lemma cond_aux_1: "\<forall>a aa b aaa ba xaaa Q \<rho>. (a, aa, b) \<in> set x \<longrightarrow>
       (aaa, ba) \<in> Basic_BNFs.snds (a, aa, b) \<longrightarrow>
       xaaa \<in> Basic_BNFs.fsts (aaa, ba) \<longrightarrow> wellDefined xaaa \<longrightarrow>
       \<rho> \<in> rhoMat \<longrightarrow> Tr (mat_mult (wlp Q xaaa) \<rho>) = Tr (mat_mult Q (denoFun xaaa \<rho>)) + Tr \<rho> - Tr (denoFun xaaa \<rho>) \<Longrightarrow>
 \<forall>a aa b. (a, aa, b) \<in> set x \<longrightarrow> (\<forall>aaa ba. (aaa, ba) \<in> Basic_BNFs.snds (a, aa, b) \<longrightarrow> (\<forall>xaaa. xaaa \<in> Basic_BNFs.fsts (aaa, ba) \<longrightarrow> wellDefined xaaa)) \<Longrightarrow>
       \<forall>Q \<rho>. \<rho> \<in> rhoMat \<longrightarrow>
          Tr (mat_mult (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr))) \<rho>) =
          Tr (mat_mult Q (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (denoFun (fst (snd mc)) (u (fst mc) \<rho>)) (denoFun (Cond mcr) \<rho>))) + Tr (mat_mult (M_sum x) \<rho>) -
          Tr (case x of [] \<Rightarrow> zero | mc # mcr \<Rightarrow> mat_add (denoFun (fst (snd mc)) (u (fst mc) \<rho>)) (denoFun (Cond mcr) \<rho>))"
apply auto
apply (induct x, auto)
using zero_mult_r apply auto[1]
apply(simp add:mult_allo1)
apply(simp add:tr_allo)
apply(simp add:mult_allo2)
apply(simp add:tr_allo)
apply(cut_tac  cond_aux2,auto)
apply (drule_tac x="a" in spec)
apply (drule_tac x="aa" in spec)
apply (drule_tac x="b" in spec)
apply (drule_tac x="b" in spec)
apply (drule_tac x="aa" in spec)
apply (drule_tac x="b" in spec)
using fsts.intros snds.intros apply fastforce+
done

(*cond_wlp*)    
lemma w_cond:"\<forall>a aa b aaa ba xaaa Q \<rho>. (a, aa, b) \<in> set x \<longrightarrow> (aaa, ba) \<in> Basic_BNFs.snds (a, aa, b) \<longrightarrow>
              xaaa \<in> Basic_BNFs.fsts (aaa, ba) \<longrightarrow> wellDefined xaaa \<longrightarrow> \<rho> \<in> rhoMat \<longrightarrow>
     Tr (mat_mult (wlp Q xaaa) \<rho>) = Tr (mat_mult Q (denoFun xaaa \<rho>)) + Tr \<rho> - Tr (denoFun xaaa \<rho>) \<Longrightarrow>
     M_sum x = I \<Longrightarrow> \<forall>a aa b. (a, aa, b) \<in> set x \<longrightarrow> (\<forall>aaa ba. (aaa, ba) \<in> Basic_BNFs.snds (a, aa, b) \<longrightarrow>
   (\<forall>xaaa. xaaa \<in> Basic_BNFs.fsts (aaa, ba) \<longrightarrow> wellDefined xaaa)) \<Longrightarrow> \<forall>Q \<rho>.  \<rho> \<in> rhoMat \<longrightarrow> Tr (mat_mult (case x of [] \<Rightarrow> zero
      | mc # mcr \<Rightarrow> mat_add (uu (fst mc) (wlp Q (fst (snd mc)))) (wlp Q (Cond mcr)))  \<rho>) =
      Tr (mat_mult Q (case x of [] \<Rightarrow> zero  | mc # mcr \<Rightarrow> mat_add (denoFun (fst (snd mc)) (u (fst mc) \<rho>)) (denoFun (Cond mcr) \<rho>))) +
     Tr \<rho> - Tr (case x of [] \<Rightarrow> zero
        | mc # mcr \<Rightarrow> mat_add (denoFun (fst (snd mc)) (u (fst mc) \<rho>)) (denoFun (Cond mcr) \<rho>))"
apply(rule cond_aux)
apply simp
apply(cut_tac x=x in cond_aux_1,auto)
done

(*while_wlp *)
lemma w_while_n:" wellDefined (While_n Mata Matb com Matc m) \<Longrightarrow>  
 \<forall>Q.\<forall> \<rho>. \<rho> \<in> rhoMat \<longrightarrow> Tr (mat_mult (wlp Q com) \<rho>) = Tr (mat_mult Q (denoFun com \<rho>)) + Tr \<rho> - Tr (denoFun com \<rho>)  \<Longrightarrow>
 \<forall>\<rho>. \<rho> \<in> rhoMat \<longrightarrow>
       Tr (mat_mult (case num of 0 \<Rightarrow> I | Suc m \<Rightarrow> mat_add (uu Mata Q) (uu Matb (wlp (wlp Q (While_n Mata Matb com Matc m)) com))) \<rho>) =
       Tr (mat_mult Q
            (case num of 0 \<Rightarrow> zero | Suc m \<Rightarrow> mat_add (u Mata \<rho>) (denoFun (While_n Mata Matb com Matc m) (denoFun com (u Matb \<rho>))))) +
       Tr \<rho> -
       Tr (case num of 0 \<Rightarrow> zero | Suc m \<Rightarrow> mat_add (u Mata \<rho>) (denoFun (While_n Mata Matb com Matc m) (denoFun com (u Matb \<rho>))))"
apply(induct num,auto)
apply (smt Ident zero_mult_r)
apply(simp add:mult_allo1)
apply(simp add:tr_allo)
apply(simp add:while_n_aux)
apply(simp add:mult_allo2)
apply(simp add:tr_allo)
apply(subgoal_tac "(denoFun com (u Matb \<rho>))\<in>rhoMat")
prefer 2
apply (metis b rho)
apply(drule_tac x="(denoFun com (u Matb \<rho>))"in spec)
apply(drule_tac x="(case num of 0 \<Rightarrow> I | Suc m \<Rightarrow> mat_add (uu Mata Q) (uu Matb (wlp (wlp Q (While_n Mata Matb com Matc m)) com)))"in spec)
apply(subgoal_tac "(u Matb \<rho>)\<in>rhoMat")
prefer 2
apply (metis rho)
apply(drule_tac x="(u Matb \<rho>)"in spec)
apply(simp add:while_n_aux2)
apply(simp add:u_def)
apply(simp add:exchange)
by (smt Ident mult_allo1 mult_exchange tr_allo)

(*  while_wlp   *)
lemma w_while:" wellDefined (While Mata Matb com Matc ) \<Longrightarrow>
 \<forall>Q \<rho>. \<rho> \<in> rhoMat \<longrightarrow> Tr (mat_mult (wlp Q com) \<rho>) = Tr (mat_mult Q (denoFun com \<rho>)) + Tr \<rho> - Tr (denoFun com \<rho>) \<Longrightarrow>
    \<forall>\<rho>. \<rho> \<in> rhoMat \<longrightarrow> Tr (mat_mult (fixpoint_wlp Mata Matb com Matc Q) \<rho>)
      = Tr (mat_mult Q (fixpoint Mata Matb com Matc \<rho>)) + Tr \<rho> - Tr (fixpoint Mata Matb com Matc \<rho>)"
apply auto
apply(rule aux)
apply(rule aux1)
apply(rule fixpoint_wlp_lemma,auto)
apply(simp add:tr_allo)
apply(cut_tac wlp_while_aux,auto)
done

(*\<forall> \<rho>,Q\<longrightarrow>Tr (wlp Q S)*\<rho>=Tr Q*[S](\<rho>)+ Tr \<rho>-Tr [S](\<rho>)          *)
lemma eq:"wellDefined S\<Longrightarrow>\<forall>Q. \<forall>\<rho>. \<rho>\<in>rhoMat\<longrightarrow> Tr (mat_mult (wlp Q S) \<rho>) =Tr (mat_mult Q (denoFun S \<rho>)) +Tr \<rho>-Tr (denoFun S \<rho>)"
apply(induct S,auto)
apply(cut_tac w_init,auto)
apply(cut_tac w_utrans,auto)
apply(cut_tac Sa="S1"and Sb="S2" in w_seq,auto)
prefer 3
apply(cut_tac Mata="x1" and Matb="x2" and Matc="x4" and com="S" and Q="Q" in w_while_n,auto)
defer
apply(cut_tac w_while,auto)
apply(cut_tac w_cond,auto)
done


lemma soundwp1: "wellDefined S \<Longrightarrow>\<forall> Q. valid (wlp Q S) S  Q"
apply(simp add:valid_def)
apply(simp add:eq)
done

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











