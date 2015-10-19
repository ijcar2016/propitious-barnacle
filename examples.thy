theory examples
imports Main  "basic" "quantum_hoare_logic" "lt"
begin

lemma grover:"valid I  
               ((((Init q0 0);Init q1 1;Init q 2;Init r 3;
               Utrans Delta 2;Utrans H 0;Utrans H 1;Utrans H 2);
              While M0 M1 C Q);
          Cond [(N0,SKIP,p0),(N1,SKIP,p1),(N2,SKIP,p2),(N3,SKIP,p3)] )             
               P"
apply (vcg,auto)
apply quantum_oracle
done
lemma loop:"valid Q (Utrans Or (10);Utrans H 0;Utrans H 1;Utrans Ph 10;
         Utrans H 0; Utrans H 1) G"
apply(vcg,auto)
apply quantum_oracle
done
(*
lemma shor:"valid P  (Init q0 0;Utrans H 0;Utrans C_U 10;Utrans (dag C_U) 10;Utrans (dag H) 0;
                    Cond [(M0,SKIP,p0),(M1,SKIP,p1)])   Q"
apply(vcg,auto)
apply quantum_oracle
done*)

end
