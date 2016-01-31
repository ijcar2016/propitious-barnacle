theory lt
imports Main   "basic"  "quantum_hoare_logic"
begin
definition Add::"int\<Rightarrow>int\<Rightarrow>int"where
"Add a b=a+b" 
ML
{*
fun translate t =
  let
    fun trans t =
      (case t of
      Free (n,@{typ Mat })=>
        Buffer.add n
      | _ =>Buffer.add "0")  (*error "inacceptable term ")*)
  in Buffer.content (trans t Buffer.empty) 
end;
 

fun translate1 t =
  let
    fun trans t =
      (case t of
       @{term "op = :: Mat\<Rightarrow>Mat\<Rightarrow>bool"} $ t $ u  =>
           Buffer.add "check_I#"#>
           trans t#>
           Buffer.add "@"
       | @{term " sum_1 :: nat list \<Rightarrow> nT \<Rightarrow> Mat"} $ t $ u  =>  
        Buffer.add "I" 
       | @{term " sum_2 :: nat list \<Rightarrow> nT \<Rightarrow> Mat"} $ t $ u  =>  
        Buffer.add "I" 
     | @{term " wellDefined ::com\<Rightarrow>bool"} $ t  =>  
        Buffer.add "0" 
      | @{term " mat_add :: Mat \<Rightarrow> Mat \<Rightarrow> Mat"} $ t $ u  =>  
        Buffer.add "#" #>(* ( *)
        trans t #>
        Buffer.add "+" #>
        trans u #>
        Buffer.add "@"(* ) *)
      | @{term " matsum::nat list\<Rightarrow>nat\<Rightarrow>Mat\<Rightarrow>Mat"}$t $u $ v =>
         Buffer.add "matsum#" #>
         trans u#>
         Buffer.add ","#>
         trans v#>
         Buffer.add"@"
      | @{term "matUtrans::Mat\<Rightarrow>nat\<Rightarrow>Mat\<Rightarrow>Mat"}$t $u $v=>
         Buffer.add "matUtrans#"#>
         trans t#>
         Buffer.add ","#>
         trans u#>
         Buffer.add ","#>
         trans v#>
         Buffer.add"@"
      | @{term "basic.less::Mat\<Rightarrow>Mat\<Rightarrow>bool"}$t $u=>
        Buffer.add "order#"#>
        trans u#>
         Buffer.add ","#>
        trans t#>
         Buffer.add "@"
      | @{term " mat_mult :: Mat \<Rightarrow> Mat \<Rightarrow> Mat"} $ t $ u  =>  
        trans t #>
        Buffer.add ".dot#" #>
        trans u #>
        Buffer.add "@"
      | @{term " dag :: Mat \<Rightarrow> Mat"} $ t  =>  
        Buffer.add "adjoint#" #>
        trans t #>
        Buffer.add "@"
     | @{term " pow :: Mat\<Rightarrow>nat \<Rightarrow> Mat"} $ t $u =>  
        Buffer.add "pow#" #>
        trans t #>
        Buffer.add "," #>
        trans u #>
        Buffer.add "@"
      | @{term  " fixpoint_wlp::Mat\<Rightarrow>Mat\<Rightarrow>com\<Rightarrow>Mat\<Rightarrow>Mat\<Rightarrow>Mat"} $a $b $c $d $e=>
        Buffer.add "fixpoint#" #>
        trans a#>
        Buffer.add "," #>
        trans b #>
        Buffer.add "," #>
        trans d #>
        Buffer.add "," #>
        trans e #>
        Buffer.add "@"
      | @{term " Suc :: nat \<Rightarrow>nat"} $ t  =>  
        Buffer.add "1" 
      | @{term " 0 :: nat"}  =>  
        Buffer.add "0"
      | @{term " 1 :: nat"}  =>  
        Buffer.add "1"
      | @{term " 2 :: nat"}  =>  
        Buffer.add "2"
      | @{term " 3 :: nat"}  =>  
        Buffer.add "3"
      | @{term " 4 :: nat"}  =>  
        Buffer.add "4"
      | @{term " 5 :: nat"}  =>  
        Buffer.add "5"
      | @{term " 6 :: nat"}  =>  
        Buffer.add "6"
      | @{term " 7 :: nat"}  =>  
        Buffer.add "7"
      | @{term " 8 :: nat"}  =>  
        Buffer.add "8"
      | @{term " 9 :: nat"}  =>  
        Buffer.add "9"
      | @{term " 10 :: nat"}  =>  
        Buffer.add "10"
      | @{term " zero :: Mat"}  =>  
        Buffer.add "mat0"
      | @{term " I:: Mat"}  =>  
        Buffer.add "I"
      |  @{term "op \<in> :: Mat\<Rightarrow>Mat set\<Rightarrow>bool"} $ t $ u  =>
           Buffer.add "check#"#>
           trans t#>
           Buffer.add ","#>
           trans u#>
           Buffer.add "@"
    | @{term " uMat :: Mat set"}  =>  
        Buffer.add "uMat"
    | @{term " rhoMat :: Mat set"}  =>  
        Buffer.add "rho"
    | @{term " predMat :: Mat set"}  =>  
        Buffer.add "pred"
      | Free (n,@{typ int})=>
        Buffer.add n
      | Free (n,@{typ nat})=>
        Buffer.add n
      | Free (n,@{typ string})=>
        Buffer.add n
      | Free (n,@{typ bool})=>
        Buffer.add n
      | Free (n,@{typ Mat })=>
        Buffer.add n
      | _ => error "inacceptable term tao")
  in Buffer.content (trans t Buffer.empty) 
end;
fun isTrue x = 
      if x="True\n" then true
      else false   
fun decide p = "~/quantum.py"^" "^p^""
    |> Isabelle_System.bash_output
    |>fst
    |> isTrue;

*}
oracle quantum_oracle = {* fn ct =>
  if decide (translate1 (HOLogic.dest_Trueprop (Thm.term_of ct)))
  then ct
  else error "Proof failed."*}

ML{*
(*decide (translate1 @{term "mat_add (mat_mult (dag M0) M0) (mat_mult (dag M1) M1) = I"});*)

 (* (translate1 @{term " basic.less P (matsum q0 0 (matUtrans H 0
      (matUtrans U (Suc 0)(matUtrans (dag U) (Suc 0)
      (matUtrans (dag H) 0 (mat_add (mat_mult (mat_mult (dag M0) Q) M0)
      (mat_add (mat_mult (mat_mult (dag M1) Q) M1) zero)))))))"});
*)



val quantum_oracle_tac =
  CSUBGOAL (fn (goal, i) =>
  (case try quantum_oracle goal of
    NONE => no_tac
  | SOME thm => rtac thm i))
*}
method_setup quantum_oracle = {*
  Scan.succeed (K (Method.SIMPLE_METHOD' quantum_oracle_tac))
*} 
end
