(*  Title:      HOL/Hoare/Hoare_Quantum_Logic.thy
    Author:     Tao Liu
*)
theory Hoare_Quantum_Logic
imports Main  "matrix"   "lt"
begin

type_synonym 'a bexp = "'a mat list"
type_synonym 'a assn = "'a mat"
type_synonym 'a outcome= nat
type_synonym 'a type= nat
type_synonym 'a number= nat
type_synonym 'a measurement="'a mat list"

datatype
 'a com =Basic "'a mat=>'a mat"       
   | Init "'a mat "  "'a number"                  ("(INIT__ )")
   |Utrans "'a mat" "'a number"                     ("(UTRANS_ _)")
   | Seq "'a com" "'a com"               ("(_;/ _)"   [61,59] 60  )
   | Cond "'a measurement"  "('a com)list"     ("(1MEASURE _ / THEN _ FI)"  [0,0]62 )
   | While "'a bexp" "'a com" "'a mat"  ("(1WHILE _/DO _ _ /OD)"  [0,0,0]62 )

abbreviation annskip ("SKIP") where "SKIP == Basic id"
(*
abbreviation annskips ("SKIPs") where "SKIPs == Basic id"*)
type_synonym 'a sem = "'a => 'a => bool"


definition plus_mea::"'a mat list\<Rightarrow>nat\<Rightarrow>'a mat\<Rightarrow>'a mat" where
"plus_mea M n P= foldr   (\<lambda> m s .(mat_plus m s))  (map (\<lambda> i. mat_mult (mat_mult (adjoint (M!i)) P) (M!i)) [0..<n])   (mat0 (nrows P) (nrows P) ) "


axiomatization wlp::"'a mat\<Rightarrow>'a com\<Rightarrow>'a mat" where 
SkipRule:"wlp  P (SKIP) =P " and
InitRule:"wlp  P (INIT f n) = matsum  n P " and
UtransRule:"wlp  P (UTRANS U n) = matUtrans U n P "and
SeqRule:"wlp  P (c1;c2) =wlp (wlp P c2 ) c1"  and
MeasureRule:"wlp  P (MEASURE M THEN C FI) =foldr ( \<lambda> (x,y) s. (mat_plus (mat_mult (mat_mult(adjoint x) y) x)  s) )  (zip M (map (\<lambda> r. (wlp P r)) C) )      Mat0 " and
WhileRule:"wlp  P (WHILE M DO c Q OD)=mat_plus (mat_mult (mat_mult  (adjoint (M!0)) P) (M!0)) (mat_mult  (mat_mult  (adjoint (M!1)) Q) (M!1))  "

definition valid ::"'a mat=>'a com\<Rightarrow>'a mat\<Rightarrow>bool" where
    "valid  Pr  S P\<equiv> order (wlp P S )  Pr"

lemma Compl_Collect: "-(Collect b) = {x. ~(b x)}"
  by blast
lemma validdef:"valid Pr S P=order (wlp P S) Pr"
apply (simp add:valid_def)
done
syntax
 "_hoare_vars" :: "['a assn,'a com,'a assn] => bool"
                 (" _ // _ // _" [0,55,0] 50)
syntax ("" output)
 "_hoare"      :: "['a mat,'a com,'a mat] => bool"
                 ("_ // _ // _" [0,55,0] 50)
ML_file "Quantum_hoare_syntax.ML"
parse_translation {* [(@{syntax_const "_hoare_vars"}, K Hoare_Syntax.hoare_vars_tr)] *}
print_translation {* [(@{const_syntax valid}, K (Hoare_Syntax.spec_tr' @{syntax_const "_hoare"}))] *}


ML_file"Quantum_Hoare_tac.ML"
method_setup vcg = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (quantum_hoare_tac ctxt (K all_tac))) *}
  "verification condition generator"

method_setup vcg_simp = {*
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (quantum_hoare_tac ctxt (asm_full_simp_tac ctxt))) *}
  "verification condition generator plus simplification"



(*lemma grover:"valid I  ((((INIT q0 0);INIT q1 1;INIT q 2;INIT r 3;UTRANS Delta 2;UTRANS H 0;UTRANS H 1;UTRANS H 2)
          ;WHILE [M0,M1]  DO c Q OD); MEASURE [N0,N1,N2,N3] THEN [SKIP,SKIP,SKIP,SKIP] FI)  P"
apply vcg
apply(simp add:SkipRule)
apply quantum_oracle
done*)


lemma shor:"valid P   (((((((((((INIT q0 0;INIT q1 1);UTRANS H 1);UTRANS  R2 2);UTRANS U 2);UTRANS H 1);UTRANS (pow U 2) 2 ;
           UTRANS adjoint (pow U 2) 2);UTRANS (adjoint H) 1);UTRANS adjoint U 2);UTRANS adjoint R2 0);
           UTRANS adjoint H 0);MEASURE [M0,M1,M2,M3] THEN [SKIP,SKIP,SKIP,SKIP] FI )  Q"
apply vcg
apply(simp add:SkipRule)
apply quantum_oracle
done







end



