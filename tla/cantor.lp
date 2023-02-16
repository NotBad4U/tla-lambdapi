
require open tla.predicatelogic;
require open tla.settheory;
require open tla.function;

// (declare-fun S () Idv)
symbol S : U;


// (declare-fun f_ () Idv)
symbol f_ : U;


// SMT-lib
// (assert
//  (Mem f_
//      (FunSet S (Subset S))))
//
// TLA+
// TAKE f \in [S -> SUBSET S]
constant symbol f_assert f:  Prf (f ∈ FuncSet S (subset S));  


// (declare-fun X () Idv)
symbol X : U;

// (assert (Mem X S))
constant symbol assert1: Prf (X ∈ S);

// equivalent to T
constant symbol T: U → U;

// (assume |Goal| (not (or (Mem X (T S)) (not (Mem X (T S))))))
opaque symbol Proofobligation#2: Prf (or  (X ∈  (T S)) (X ∉ (T S))) ≔
begin
    simplify;
    apply ccontr;
    assume Goal;
    // (step t2 (cl (= (or (∈ X (T S)) (not (∈ X (T S)))) true))
    // :rule or_simplify)
    have t2: Prf (or (X ∈ T S) (not (X ∈ T S)) = true) {
        apply or_simplify (X ∈ T S) (not (X ∈ T S)) true;
    };

    //(step t3 (cl (= (not (or (∈ X (T S)) (not (∈ X (T S))))) (not true))) 
    // :rule cong :premises (t2))
    have t3: Prf (not (or (X ∈ T S) (not (X ∈ T S))) = not true) {
        apply cong (or (X ∈ T S) (not (X ∈ T S))) (true) not t2 ;
    };
    
    // (step t4 (cl (= (not true) false)) :rule not_simplify)
    have t4: Prf(not true = false) {
        apply notTrue;
    };

    // (step t5 (cl (= (not (or (∈ X (T S)) (not (∈ X (T S))))) false)) 
    // :rule trans :premises (t3 t4))
    have t5: Prf ((not (or (X ∈ T S) (not (X ∈ T S))) = false)) {
        apply trans (not (or (X ∈ T S) (not (X ∈ T S)))) 
                    (not true)
                    (false) t3 t4;
    };
    // (step t6 (cl (not (= (not (or (∈ X (T S)) (not (∈ X (T S))))) false)) (not (not (or (∈ X (T S)) (not (∈ X (T S)))))) false)
    // :rule equiv_pos2)
    have t6: Prf ( 
        or 
            (or 
                (not (not (or (X ∈ T S) (not (X ∈ T S))) = false))
                (not (not (or (X ∈ T S) (not (X ∈ T S)))))
            ) 
            false
        ) {
            apply equiv_pos2 (not (or (X ∈ T S) (not (X ∈ T S)))) false;
    };
    //(step t7 (cl (not (not (not (or (∈ X (T S)) (not (∈ X (T S))))))) (or (∈ X (T S)) (not (∈ X (T S))))) :rule not_not)
    have t7: Prf (or 
                    (not (not (not (or (X ∈ T S) (not (X ∈ T S))))))
                    (or (X ∈ T S) (not (X ∈ T S)))
    ) {
        apply not_not (or (X ∈ T S) (not (X ∈ T S)));
    };
    //
    have t8: Prf (
        or 
            (or 
                (not (not (or (X ∈ T S) (not (X ∈ T S))) = false))
                (or (X ∈ T S) (not (X ∈ T S)))
            )
            false
    ) {
        have tmp: Prf (
            or
                (or 
                (or 
                    (not (not (or (X ∈ T S) (not (X ∈ T S))) = false))
                    (not (not (or (X ∈ T S) (not (X ∈ T S)))))
                ) 
                false)
                (or 
                    (not (not (not (or (X ∈ T S) (not (X ∈ T S))))))
                    (or (X ∈ T S) (not (X ∈ T S))))
        ) {
            apply orI2 
            (or 
                (or 
                    (not (not (or (X ∈ T S) (not (X ∈ T S))) = false))
                    (not (not (or (X ∈ T S) (not (X ∈ T S)))))
                ) 
                false)
                (or 
                    (not (not (not (or (X ∈ T S) (not (X ∈ T S))))))
                    (or (X ∈ T S) (not (X ∈ T S))))
                t7;
        };
        apply ssubst 
        (not (not (or (X ∈ T S) (not (X ∈ T S)))))
        (or (X ∈ T S) (not (X ∈ T S)))
        (λ z, or (or (not (not (or (X ∈ T S) (not (X ∈ T S))) = false)) z) false)
        (double_negation_elim  ((or (X ∈ T S) (not (X ∈ T S)))))
        t6
        ;
    };
    //apply subst (not (or (X ∈ T S) (not (X ∈ T S)))) false (λ z, z) t5;
    have tmp2: Prf (or (or (not (false = false)) (or (X ∈ T S) (not (X ∈ T S)))) false) {
        apply ssubst (not (or (X ∈ T S) (not (X ∈ T S)))) false (λ z, or (or (not (z = false)) (or (X ∈ T S) (not (X ∈ T S)))) false) t5 t8;
    };
    have tmp4: Prf (or (or false (or (X ∈ T S) (not (X ∈ T S)))) false) {
        apply ssubst (not true) false (λ z, or (or z (or (X ∈ T S) (not (X ∈ T S)))) false) (refl false) tmp2;
    };
    have tmp5: Prf (or false (or (X ∈ T S) (not (X ∈ T S)))) {
        apply identity_or_r ((or (not (false = false)) (or (X ∈ T S) (not (X ∈ T S))))) tmp4;
    };
    have goal2: Prf (or false (not (or (X ∈ T S) (not (X ∈ T S))))) {
        admit
    };
    have tmp6: Prf (or false false) {
        apply reduction_clause2 (or (X ∈ T S) (not (X ∈ T S))) false false tmp5 goal2;
    };
    have tmpf: Prf false {
        apply ssubst (or false false) false (λ z, z) (idempotence_or false) tmp6;
    };
    apply tmpf;
end;

// (assume |SetStDef T| (forall ((smt__a Idv) (smt__x Idv)) (= (∈ smt__x (T smt__a)) (and (∈ smt__x smt__a) (not (∈ smt__x (FunApp smt__CONSTANT_f_ smt__x)))))))
constant symbol SetStDef_T: Π a x, Prf ((x ∈ T a)  = (and (x ∈ a) (x ∉  (fapply f_ x))));

opaque symbol Proofobligation#1: Prf (X ∈ S) → Prf (((fapply f_ X) ≠ (T S))) ≔
begin
    simplify;
    assume H2;
    apply ccontr;
    assume Goal;

    //(step t5 (cl (not (not (not (smt__TLA__TrigEq_Idv (FunApp f X) (T))))) (smt__TLA__TrigEq_Idv (FunApp f X) (T))) :rule not_not)
    have t5: Prf (or (not (not (not (fapply f_ X = T S)))) (fapply f_ X = T S)) {
        apply not_not (fapply f_ X = (T S)) ;
    };
    //(step t6 (cl (smt__TLA__TrigEq_Idv (FunApp f X) (T))) :rule th_resolution :premises (t5 |Goal|))
    have t6: Prf (fapply f_ X = (T S) ) {
        admit;
    };
    have t7:  Prf ((`forall x, `forall y, ((x = y) = (x = y))) = (`forall veriT_vr52, `forall veriT_vr53, ((veriT_vr52 = veriT_vr53) = (veriT_vr52 = veriT_vr53)) )) {
        admit;
    };
    // (step t8 (cl (not (= (forall ((smt__x Idv) (smt__y Idv)) (= (smt__TLA__TrigEq_Idv smt__x smt__y) (= smt__x smt__y))) (forall ((veriT_vr52 Idv) (veriT_vr53 Idv)) (= (smt__TLA__TrigEq_Idv veriT_vr52 veriT_vr53) (= veriT_vr52 veriT_vr53))))) (not (forall ((smt__x Idv) (smt__y Idv)) (= (smt__TLA__TrigEq_Idv smt__x smt__y) (= smt__x smt__y)))) (forall ((veriT_vr52 Idv) (veriT_vr53 Idv)) (= (smt__TLA__TrigEq_Idv veriT_vr52 veriT_vr53) (= veriT_vr52 veriT_vr53)))) :rule equiv_pos2)


    admit; //TODO
end;