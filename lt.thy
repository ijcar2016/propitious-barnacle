theory lt
imports Main  "matrix"
begin
definition Add::"int\<Rightarrow>int\<Rightarrow>int"where
"Add a b=a+b" 
ML
{*
fun translate t =
  let
    fun trans t =
      (case t of
        @{term "op = :: bool\<Rightarrow>bool\<Rightarrow>bool"} $ t $ u  =>
        Buffer.add "(" #>
        trans t #>
        Buffer.add "\<Leftrightarrow>" #>
        trans u #>
        Buffer.add ")"
      | Free (n,@{typ bool})=>
        Buffer.add n
      | _ => error "inacceptable term ")
  in Buffer.content (trans t Buffer.empty) 
end;

fun translate1 t =
  let
    fun trans t =
      (case t of
        @{term " mat_plus :: Mat \<Rightarrow> Mat \<Rightarrow> Mat"} $ t $ u  =>  
        Buffer.add "#" #>
        trans t #>
        Buffer.add "+" #>
        trans u #>
        Buffer.add "@"
      | @{term " matsum::nat\<Rightarrow>Mat\<Rightarrow>Mat"} $u $ v =>
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
      | @{term "order::Mat\<Rightarrow>Mat\<Rightarrow>bool"}$t $u=>
        Buffer.add "order#"#>
        trans t#>
         Buffer.add ","#>
        trans u#>
         Buffer.add "@"
      | @{term "op = :: Mat\<Rightarrow>Mat\<Rightarrow>bool"} $ t $ u  =>   
        trans t #>
        Buffer.add "==" #>
        trans u 
      | @{term " mat_mult :: 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"} $ t $ u  =>  
        trans t #>
        Buffer.add "*" #>
        trans u 
      | @{term " adjoint :: 'a mat \<Rightarrow> 'a mat"} $ t  =>  
        Buffer.add "adjoint#" #>
        trans t #>
        Buffer.add "@"
     | @{term " pow :: 'a mat\<Rightarrow>nat \<Rightarrow> 'a mat"} $ t $u =>  
        Buffer.add "pow#" #>
        trans t #>
        Buffer.add "," #>
        trans u #>
        Buffer.add "@"
      | @{term " Suc :: nat \<Rightarrow>nat"} $ t  =>  
        Buffer.add "1" 
      
      | @{term " A :: 'a mat"}  =>  
        Buffer.add "A"
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
      | @{term " B :: 'a mat"}  =>  
        Buffer.add "B"
      | @{term " Z :: 'a mat"}  =>  
        Buffer.add "Z"
      | @{term " Mat0 :: 'a mat"}  =>  
        Buffer.add "mat0"
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




translate1 @{term  "order (matsum 0 (matsum (Suc 0) (matUtrans H (Suc 0) (matUtrans R2 2 (matUtrans U 2
       (matUtrans H (Suc 0) (matUtrans (pow U 2) 2 (matUtrans (adjoint (pow U 2)) 2
       (matUtrans (adjoint H) (Suc 0) (matUtrans (adjoint U) 2 (matUtrans (adjoint R2) 0
        (matUtrans (adjoint H) 0 (mat_plus (mat_mult (mat_mult (adjoint M0) Q) M0)
      (mat_plus (mat_mult (mat_mult (adjoint M1) Q) M1) (mat_plus (mat_mult (mat_mult (adjoint M2) Q) M2)
    (mat_plus (mat_mult (mat_mult (adjoint M3) Q) M3) Mat0)))))))))))))))) P"};



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

(*decide (translate1 @{term "order  (matsum  0 (matsum  1 (matsum 2 (matsum  3 (matUtrans Delta 2 (matUtrans H 0 (matUtrans H 1 (matUtrans H 2 (mat_plus
 (mat_mult (mat_mult (adjoint M0) (mat_plus (mat_mult (mat_mult (adjoint N0) P) N0) (mat_plus (mat_mult (mat_mult (adjoint N1) P) N1)
 (mat_plus (mat_mult (mat_mult (adjoint N2) P) N2) (mat_plus (mat_mult (mat_mult (adjoint N3) P) N3) Mat0)))))  M0) (mat_mult
  (mat_mult (adjoint M1)Q)  M1))))))))))  I"});*)

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
