
require open tla.predicatelogic;
require open tla.settheory;
require open tla.function;
require open tla.smtlib;

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

// (declare-fun smt__TLA__TrigEq_Idv (Idv Idv) Bool)
// NOTE we shorter smt__TLA__TrigEq_Idv in TrigEq_Idv.
symbol TrigEq_Idv: U → U → U;

//;; Axiom: ExtTrigEqDef Idv
//(assert
//  (!
//    (forall ((smt__x Idv) (smt__y Idv))
//      (! (= (smt__TLA__TrigEq_Idv smt__x smt__y) (= smt__x smt__y))
//        :pattern ((smt__TLA__TrigEq_Idv smt__x smt__y))))
//    :named |ExtTrigEqDef Idv|))
constant symbol ExtTrigEqDef: Π x y, Prf ( TrigEq_Idv x y =  (x = y));


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

// (assume |SetStDef T| (forall ((smt__a Idv) (smt__x Idv)) (= (∈ smt__x (T smt__a)) (and (∈ smt__x smt__a) (not (∈ smt__x (FunApp f_ smt__x)))))))
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
        refine reduction_clause' (not (not (fapply f_ X = T S))) (fapply f_ X = T S) (orI1 (not (not (fapply f_ X = T S))) false Goal) t5;
    };
    have t7: Prf ((`forall x, `forall y, ((x = y) = (x = y))) = (`forall vr52, `forall vr53, ((vr52 = vr53) = (vr52 = vr53)) )) {
        admit;
    };
    // (step t8 (cl (not (= (forall ((smt__x Idv) (smt__y Idv)) (= (smt__TLA__TrigEq_Idv smt__x smt__y) (= smt__x smt__y))) (forall ((veriT_vr52 Idv) (veriT_vr53 Idv)) (= (smt__TLA__TrigEq_Idv veriT_vr52 veriT_vr53) (= veriT_vr52 veriT_vr53))))) (not (forall ((smt__x Idv) (smt__y Idv)) (= (smt__TLA__TrigEq_Idv smt__x smt__y) (= smt__x smt__y)))) (forall ((veriT_vr52 Idv) (veriT_vr53 Idv)) (= (smt__TLA__TrigEq_Idv veriT_vr52 veriT_vr53) (= veriT_vr52 veriT_vr53)))) :rule equiv_pos2)
    have t8: Prf (
        or 
            (or 
                (not ((`forall x, `forall y, ((x = y) = (x = y))) = (`forall vr52, `forall vr53, ((vr52 = vr53) = (vr52 = vr53)))))
                (not (`forall x, `forall y, ((x = y) = (x = y))))
            )
                (`forall vr52, `forall vr53, ((vr52 = vr53) = (vr52 = vr53)))
    ) {
        apply equiv_pos2 (`forall x, `forall y, ((x = y) = (x = y))) (`forall vr52, `forall vr53, ((vr52 = vr53) = (vr52 = vr53)))
    };
    // (step t9 (cl (forall ((vr52 Idv) (vr53 Idv)) (= (smt__TLA__TrigEq_Idv vr52 vr53) (= vr52 vr53)))) :rule th_resolution :premises (|ExtTrigEqDef Idv| t7 t8))
    have t9: Prf (`forall vr52, `forall vr53, ((vr52 = vr53) = (vr52 = vr53))) {
        admit
    };

    // (step t10 (cl (= (forall ((vr52 Idv) (vr53 Idv)) (= (smt__TLA__TrigEq_Idv vr52 vr53) (= vr52 vr53))) (forall ((vr54 Idv) (veriT_vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 veriT_vr55) (= vr54 veriT_vr55))))) :rule bind)
    have t10: Prf ((`forall vr52, `forall vr53, ((vr52 = vr53) = (vr52 = vr53))) = (`forall vr54, `forall vr55, ((vr54 = vr55) = (vr54 = vr55)) )) {
        admit;
    };

    //(step t11 (cl (not (= (forall ((vr52 Idv) (vr53 Idv)) (= (smt__TLA__TrigEq_Idv vr52 vr53) (= vr52 vr53))) (forall ((vr54 Idv) (veriT_vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 veriT_vr55) (= vr54 veriT_vr55))))) (not (forall ((vr52 Idv) (vr53 Idv)) (= (smt__TLA__TrigEq_Idv vr52 vr53) (= vr52 vr53)))) (forall ((vr54 Idv) (veriT_vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 veriT_vr55) (= vr54 veriT_vr55)))) :rule equiv_pos2)
    have t11:  Prf (
        or 
            (or 
                (not ((`forall vr52, `forall vr53, ((vr52 = vr53) = (vr52 = vr53))) = (`forall vr54, `forall vr55, ((vr54 = vr55) = (vr54 = vr55)))))
                (not (`forall vr52, `forall y, ((vr52 = y) = (vr52 = y))))
            )
                (`forall vr54, `forall vr55, ((vr54 = vr55) = (vr54 = vr55)))
        ) {
        apply equiv_pos2 (`forall vr52, `forall y, ((vr52 = y) = (vr52 = y))) (`forall vr54, `forall vr55, ((vr54 = vr55) = (vr54 = vr55)));
    };

    // (step t12 (cl (forall ((vr54 Idv) (veriT_vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 veriT_vr55) (= vr54 veriT_vr55)))) :rule th_resolution :premises (t9 t10 t11))
    have t12: Prf (`forall vr54, `forall vr55, ((vr54 = vr55) = (vr54 = vr55))) {
        admit;
    };

    //(step t13 (cl (= (forall ((smt__a Idv) (smt__x Idv)) (= (∈ smt__x (T smt__a)) (and (∈ smt__x smt__a) (not (∈ smt__x (FunApp f smt__x)))))) (forall ((veriT_vr56 Idv) (veriT_vr57 Idv)) (= (∈ veriT_vr57 (T veriT_vr56)) (and (∈ veriT_vr57 veriT_vr56) (not (∈ veriT_vr57 (FunApp f veriT_vr57)))))))) :rule bind)
    have t13: Prf (
            (`forall a, `forall x, (x ∈ T a) = and (x ∈ a) (x ∉  (fapply f_ x)))
            =
            (`forall vr56, `forall vr57, (vr57 ∈ T vr56) = and (vr57 ∈ vr56) (vr57 ∉  (fapply f_ vr57)))
        ) {
        admit;
    };

    // (step t14 (cl (not (= (forall ((smt__a Idv) (smt__x Idv)) (= (∈ smt__x (T smt__a)) (and (∈ smt__x smt__a) (not (∈ smt__x (FunApp f smt__x)))))) (forall ((veriT_vr56 Idv) (veriT_vr57 Idv)) (= (∈ veriT_vr57 (T veriT_vr56)) (and (∈ veriT_vr57 veriT_vr56) (not (∈ veriT_vr57 (FunApp f veriT_vr57)))))))) (not (forall ((smt__a Idv) (smt__x Idv)) (= (∈ smt__x (T smt__a)) (and (∈ smt__x smt__a) (not (∈ smt__x (FunApp f smt__x))))))) (forall ((veriT_vr56 Idv) (veriT_vr57 Idv)) (= (∈ veriT_vr57 (T veriT_vr56)) (and (∈ veriT_vr57 veriT_vr56) (not (∈ veriT_vr57 (FunApp f veriT_vr57))))))) :rule equiv_pos2)
    have t14: Prf (
        or 
            (or
                (¬ (((`forall a, `forall x, (x ∈ T a) = and (x ∈ a) (x ∉  (fapply f_ x))) = (`forall vr56, `forall vr57, (vr57 ∈ T vr56) = and (vr57 ∈ vr56) (vr57 ∉  (fapply f_ vr57))))))
                (¬ (`forall a, `forall x, (x ∈ T a) = and (x ∈ a) (x ∉  (fapply f_ x))))
            )
            (`forall vr56, `forall vr57, (vr57 ∈ T vr56) = and (vr57 ∈ vr56) (vr57 ∉  (fapply f_ vr57)))
    ) {
        apply equiv_pos2 (`forall a, `forall x, (x ∈ T a) = and (x ∈ a) (x ∉  (fapply f_ x)))             (`forall vr56, `forall vr57, (vr57 ∈ T vr56) = and (vr57 ∈ vr56) (vr57 ∉  (fapply f_ vr57)));
    };

    // (step t15 (cl (forall ((veriT_vr56 Idv) (veriT_vr57 Idv)) (= (∈ veriT_vr57 (T veriT_vr56)) (and (∈ veriT_vr57 veriT_vr56) (not (∈ veriT_vr57 (FunApp f veriT_vr57))))))) :rule th_resolution :premises (|SetStDef T| t13 t14))
    have t15: Prf (`forall vr56, `forall vr57,  (vr57 ∈ T vr56) = (and (vr57 ∈ vr56) (vr57 ∉ (fapply f_ vr57))) ) {
        admit;
    };
    //(step t16 (cl (= (forall ((veriT_vr56 Idv) (veriT_vr57 Idv)) (= (∈ veriT_vr57 (T veriT_vr56)) (and (∈ veriT_vr57 veriT_vr56) (not (∈ veriT_vr57 (FunApp f veriT_vr57)))))) (forall ((veriT_vr58 Idv) (veriT_vr59 Idv)) (= (∈ veriT_vr59 (T veriT_vr58)) (and (∈ veriT_vr59 veriT_vr58) (not (∈ veriT_vr59 (FunApp f veriT_vr59)))))))) :rule bind)
    have t16: Prf (`forall vr56, `forall vr57, (vr57 ∈ (T vr56)) = and (vr57 ∈ vr56) (vr57 ∉ (fapply f_ vr57))) {
        admit;
    };
    // (step t17 (cl (not (= (forall ((veriT_vr56 Idv) (veriT_vr57 Idv)) (= (∈ veriT_vr57 (T veriT_vr56)) (and (∈ veriT_vr57 veriT_vr56) (not (∈ veriT_vr57 (FunApp f veriT_vr57)))))) (forall ((veriT_vr58 Idv) (veriT_vr59 Idv)) (= (∈ veriT_vr59 (T veriT_vr58)) (and (∈ veriT_vr59 veriT_vr58) (not (∈ veriT_vr59 (FunApp f veriT_vr59)))))))) (not (forall ((veriT_vr56 Idv) (veriT_vr57 Idv)) (= (∈ veriT_vr57 (T veriT_vr56)) (and (∈ veriT_vr57 veriT_vr56) (not (∈ veriT_vr57 (FunApp f veriT_vr57))))))) (forall ((veriT_vr58 Idv) (veriT_vr59 Idv)) (= (∈ veriT_vr59 (T veriT_vr58)) (and (∈ veriT_vr59 veriT_vr58) (not (∈ veriT_vr59 (FunApp f veriT_vr59))))))) :rule equiv_pos2)
    have t17: Prf(
        or 
            (or 
                (¬ ( (`forall vr56, `forall vr57, (vr57 ∈ (T vr56)) = and (vr57 ∈ vr56) (vr57 ∉ (fapply f_ vr57))) = (`forall vr58, `forall vr59, (vr59 ∈ (T vr58)) = and (vr59 ∈ vr58) (vr59 ∉ (fapply f_ vr58)))))
                (¬ ((`forall vr56, `forall vr57, (vr57 ∈ (T vr56)) = and (vr57 ∈ vr56) (vr57 ∉ (fapply f_ vr57))))))
                (`forall vr58, `forall vr59, (vr59 ∈ (T vr58)) = and (vr59 ∈ vr58) (vr59 ∉ (fapply f_ vr58)))
    ) {
        apply equiv_pos2 (`forall vr56, `forall vr57, (vr57 ∈ (T vr56)) = and (vr57 ∈ vr56) (vr57 ∉ (fapply f_ vr57))) (`forall vr58, `forall vr59, (vr59 ∈ (T vr58)) = and (vr59 ∈ vr58) (vr59 ∉ (fapply f_ vr58)));
    };
    // (step t18 (cl (forall ((veriT_vr58 Idv) (veriT_vr59 Idv)) (= (∈ veriT_vr59 (T veriT_vr58)) (and (∈ veriT_vr59 veriT_vr58) (not (∈ veriT_vr59 (FunApp f veriT_vr59))))))) :rule th_resolution :premises (t15 t16 t17))
    have t18: Prf (`forall vr58, `forall vr59, (vr59 ∈ (T vr58)) = and (vr59 ∈ vr58) (vr59 ∉ (fapply f_ vr58))) {
        admit;
    };

    //(step t19 (cl (or (not (forall ((vr54 Idv) (veriT_vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 veriT_vr55) (= vr54 veriT_vr55)))) (forall ((vr54 Idv) (veriT_vr55 Idv)) (or (not (smt__TLA__TrigEq_Idv vr54 veriT_vr55)) (= vr54 veriT_vr55))))) :rule qnt_cnf)
    have t19: Prf (or (¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)) ) ((`forall vr54, `forall vr55, or (vr54 ≠ vr55) (vr54 = vr55)))  ) {
        //FIXME check how we can use qnt_cnf_2.
        //apply qnt_cnf_2 ((vr54 = vr55) = (vr54 = vr55)) ((`forall vr54, `forall vr55, or (vr54 ≠ vr55) (vr54 = vr55)));
        admit;
    };
    // 
    // (step t20 (cl 
    // (not (forall ((vr54 Idv) (veriT_vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 veriT_vr55) (= vr54 veriT_vr55)))) 
    // (forall ((vr54 Idv) (veriT_vr55 Idv)) (or (not (smt__TLA__TrigEq_Idv vr54 veriT_vr55)) (= vr54 veriT_vr55)))
    // ) :rule or :premises (t19))
    have t20: Prf (or (¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)) ) ((`forall vr54, `forall vr55, or (vr54 ≠ vr55) (vr54 = vr55)))  ) {
        apply t19;
        //NOTE the rule between or and qnt_cnf sound to enter in conflict in LambdaPi logic
    };
    
    // (step t32 (cl (= (T S_) (smt__TLA__FunApp f_ x_))) :rule resolution :premises (t30 t31))
    have t32: Prf ((T S) = (fapply f_ X)) {
        admit;
    };

    // (step t33 (cl (or (not (forall ((veriT_vr58 Idv) (veriT_vr59 Idv)) (= (∈ veriT_vr59 (T veriT_vr58)) (and (∈ veriT_vr59 veriT_vr58) (not (∈ veriT_vr59 (smt__TLA__FunApp f_ veriT_vr59))))))) (= (∈ x_ (T S_)) (and (∈ x_ S_) (not (∈ x_ (smt__TLA__FunApp smt__CONSTANT_f_ smt__CONSTANT_x_))))))) :rule forall_inst :args ((:= veriT_vr58 S_) (:= veriT_vr59 smt__CONSTANT_x_)))
    have t33: Prf (
        or (¬ (`forall vr58, `forall vr59, (vr59 ∈ T vr58) = (and (vr59 ∈ vr58) (vr59 ∉ fapply f_ vr59))))
            (X ∈ T S = (and (X ∈ S) (X ∉ (fapply f_ X))))
    ) {
        admit;
    };

    // (step t34 (cl (not (and (∈ x_ S_) (not (∈ x_ (smt__TLA__FunApp f_ x_))))) (not (∈ x_ (smt__TLA__FunApp f_ x_)))) :rule and_pos)
    have t34: Prf ( or (¬ (and (X ∈ S) (X ∉ (fapply f_ X)))) (X ∉ (fapply f_ X))) {
        apply and_pos (X ∈ S) (¬ (X ∈ (fapply f_ X))) (¬ (X ∈ (fapply f_ X))) ;
    };

    // (step t35 (cl (and (∈ _x_ _S_) (not (∈ _x_ (FunApp _f_ _x_)))) (not (∈ _x_ _S_)) (not (not (∈ _x_ (FunApp _f_ _x_))))) :rule and_neg)
    have t35: Prf (or (and (X ∈ S) (X ∉ fapply f_ X)) (or (X ∉ S) (¬ (X ∉ (fapply f_ X))))) {
        apply and_neg2 (X ∈ S) (X ∉ (fapply f_ X));
    };

    // (step t36 (cl (not (not (not (∈ _x_ (FunApp _f_ _x_))))) (∈ _x_ (FunApp _f_ _x_))) :rule not_not)
    have t36: Prf (or (¬ ¬ (X ∉ (fapply f_ X))) (X ∈ fapply f_ X)) {
        apply not_not (X ∈ fapply f_ X);
    };

    // (step t37 (cl (and (∈ _x_ _S_) (not (∈ _x_ (FunApp _f_ _x_)))) (not (∈ _x_ _S_)) (∈ _x_ (FunApp _f_ _x_))) :rule th_resolution :premises (t36 t35))
    have t37: Prf (or (and (X ∈ S) (X ∉ fapply f_ X)) (or (X ∉ S) (X ∈ fapply f_ X))) {
        have t35': Prf (or (or (and (X ∈ S) (X ∉ fapply f_ X)) (X ∉ S)) (¬ (X ∉ (fapply f_ X)))) {
            apply or_assoc_l (and (X ∈ S) (X ∉ fapply f_ X)) (X ∉ S) (¬ (X ∉ (fapply f_ X))) t35;
        };
        apply or_assoc_r 
        (and (X ∈ S) (X ∉ fapply f_ X))
        (X ∉ S)
        (X ∈ fapply f_ X)
        (reduction_clause2 
            (¬ (X ∉ (fapply f_ X)))
            (or (and (X ∈ S) (X ∉ fapply f_ X)) (X ∉ S))
            (X ∈ fapply f_ X)
            t35'
            (or_comm (¬ ¬ (X ∉ (fapply f_ X))) (X ∈ fapply f_ X) t36)
        );
    };
    // (step t38 (cl (not (= (∈ _x_ (T _S_)) (and (∈ _x_ _S_) (not (∈ _x_ (FunApp _f_ _x_)))))) (∈ _x_ (T _S_)) (not (and (∈ _x_ _S_) (not (∈ _x_ (FunApp _f_ _x_)))))) :rule equiv_pos1)
    have t38: Prf ( or  (or ((X ∈ T S) ≠ (and (X ∈ S) (X ∉ fapply f_ X))) (X ∈ T S)) ¬ (and (X ∈ S) (X ∉ fapply f_ X))) {
        apply equiv_pos1 (X ∈ T S) (and (X ∈ S) (X ∉ fapply f_ X));
    };
    // (step t39 (cl (not (= (∈ _x_ (T _S_)) (and (∈ _x_ _S_) (not (∈ _x_ (FunApp _f_ _x_)))))) (not (∈ _x_ (T _S_))) (and (∈ _x_ _S_) (not (∈ _x_ (FunApp _f_ _x_))))) :rule equiv_pos2)
    have t39: Prf ( or  (or ((X ∈ T S) ≠ (and (X ∈ S) (X ∉ fapply f_ X))) (X ∉ T S)) (and (X ∈ S) (X ∉ fapply f_ X))) {
        apply equiv_pos2 (X ∈ T S) (and (X ∈ S) (X ∉ fapply f_ X));
    };

    // FIXME: bug between t33 and t40 -- sounds to transform Or into cl
    //(step t40 (cl (not (forall ((vr58 Idv) (vr59 Idv)) (= (∈ vr59 (T vr58)) (and (∈ vr59 vr58) (not (∈ vr59 (FunApp _f_ vr59))))))) (= (∈ _x_ (T _S_)) (and (∈ _x_ _S_) (not (∈ _x_ (FunApp _f_ _x_)))))) :rule or :premises (t33))
    have t40: Prf (
        or (¬ (`forall vr58, `forall vr59, (vr59 ∈ T vr58) = (and (vr59 ∈ vr58) (vr59 ∉ fapply f_ vr59))))
            (X ∈ T S = (and (X ∈ S) (X ∉ (fapply f_ X))))
        ) {
        apply t33;
    };

    // (step t41 (cl (and (∈ _x_ _S_) (not (∈ _x_ (FunApp _f_ _x_)))) (∈ _x_ (FunApp _f_ _x_))) :rule resolution :premises (t37 h2))
    have t41: Prf (or (and (X ∈ S) (X ∉ fapply f_ X))  (X ∈ fapply f_ X)) {
        have t37': Prf (or (X ∉ S) (or  (and (X ∈ S) (X ∉ fapply f_ X)) (X ∈ fapply f_ X))) {
            admit;
            //TODO: assoc and comm
            //apply or_assoc_r (X ∉ S) (and (X ∈ S) (X ∉ fapply f_ X)) (X ∈ fapply f_ X);
        };
        apply 
            identity_or_l
            (or (and (X ∈ S) (X ∉ fapply f_ X)) (X ∈ fapply f_ X))
            (reduction_clause
            (X ∈ S)
            false
            (or  (and (X ∈ S) (X ∉ fapply f_ X)) (X ∈ fapply f_ X))
            (orI1 (X ∈ S) false H2)
            t37');
    };

    // (step t42 (cl (= (∈ _x_ (T _S_)) (and (∈ _x_ _S_) (not (∈ _x_ (FunApp _f_ _x_)))))) :rule resolution :premises (t40 t18))
    have t42: Prf ((X ∈ T S) = (and (X ∈ S) (X ∉ fapply f_ X))) {
        admit;
    };

    // (step t43 (cl (not (= _x_ _x_)) (not (= (T _S_) (FunApp _f_ _x_))) (not (∈ _x_ (T _S_))) (∈ _x_ (FunApp _f_ _x_))) :rule eq_congruent_pred)
    have t43: Prf (( X ≠ X ) ⟇ ((T S ≠ (fapply f_ X)) ⟇ ((X ∉ (T S)) ⟇ (X ∈ fapply f_ X)))) {
        apply eq_congruent_pred X X (T S) (fapply f_ X) (λ x y, x ∉ y) (λ x y, x ∈ y);
    };

    //(step t44 (cl (= _x_ _x_)) :rule eq_reflexive)
    have t44: Prf (X = X) {
        apply refl X;
    };

    // (step t45 (cl (not (= (T _S_) (FunApp _f_ _x_))) (not (∈ _x_ (T _S_))) (∈ _x_ (FunApp _f_ _x_))) :rule th_resolution :premises (t43 t44))
    have t45: Prf ( (T S ≠ (fapply f_ X)) ⟇ ((X ∉ (T S)) ⟇ (X ∈ fapply f_ X)) ) {
        apply 
            identity_or_l
            ((T S ≠ (fapply f_ X)) ⟇ ((X ∉ (T S)) ⟇ (X ∈ fapply f_ X)))
            (reduction_clause
                (X = X)
                false
                ((T S ≠ (fapply f_ X)) ⟇ ((X ∉ (T S)) ⟇ (X ∈ fapply f_ X)))
                (orI1 true false t44)
                t43
            )
    };

    // (step t46 (cl (not (∈ _x_ (T _S_))) (∈ _x_ (FunApp _f_ _x_))) :rule resolution :premises (t45 t32))
    have t46: Prf ((X ∉ T S)  ⟇ (X ∈ fapply f_ X)) {
        apply 
        identity_or_l
        (X ∉ T S  ⟇ X ∈ fapply f_ X)
        (reduction_clause
            (T S = fapply f_ X)
            false
            (X ∉ T S ⟇ X ∈ fapply f_ X)
            (orI1 (T S = fapply f_ X) false t32)
            t45
        )
    };

    // (step t47 (cl (∈ _x_ (FunApp _f_ _x_))) :rule resolution :premises (t46 t38 t41 t42))
    // NOTE: t38 is useless here because it reduce to True with t42 equality
    have t47: Prf (X ∈ fapply f_ X) {
        have t41': Prf (or (X ∈ T S) (X ∈ fapply f_ X)) {
            apply subst (X ∈ T S) (and (X ∈ S) (X ∉ fapply f_ X)) (λ z, or z (X ∈ fapply f_ X)) t42 t41
        };
        apply reduction_clause
            (X ∈ T S)
            (X ∈ fapply f_ X)
            (X ∈ fapply f_ X)
            t41'
            t46;
    };

    // (step t48 (cl (not (and (∈ _x_ _S_) (not (∈ _x_ (FunApp _f_ _x_)))))) :rule resolution :premises (t34 t47))
    have t48: Prf ( ¬ and (X ∈ S) (X ∉ fapply f_ X)) {
        apply identity_or_l
        ( ¬ and (X ∈ S) (X ∉ fapply f_ X))
        (reduction_clause2
            (X ∈ fapply f_ X)
            false
            ( ¬ and (X ∈ S) (X ∉ fapply f_ X))
            (orI2 false (X ∈ fapply f_ X)  t47)
            t34
        )
    };

    // (step t49 (cl (not (∈ _x_ (T _S_)))) :rule resolution :premises (t39 t48 t42))
    have t49: Prf (X ∉ T S) {
        admit;
    };

    // (step t50 (cl (not (= _x_ _x_)) (not (= (T _S_) (FunApp _f_ _x_))) (not (∈ _x_ (FunApp _f_ _x_))) (∈ _x_ (T _S_))) :rule eq_congruent_pred)
    have t50: Prf ((X ≠ X) ⟇ ((T S ≠  fapply f_ X) ⟇  ( (X ∈ T S) ⟇ (X ∉ fapply f_ X)))) {
        //NOTE bug in  eq_congruent_pred order
        apply eq_congruent_pred X X (T S) (fapply f_ X) (λ x1 x2, x1 ∈ x2) (λ y1 y2, y1 ∉ y2)
    };

    //(step t51 (cl (not (= (T _S_) (FunApp _f_ _x_))) (not (∈ _x_ (FunApp _f_ _x_))) (∈ _x_ (T _S_))) :rule th_resolution :premises (t50 t44))
    have t51: Prf ( ((T S ≠  fapply f_ X) ⟇  ( (X ∈ T S) ⟇ (X ∉ fapply f_ X)))) {
        apply 
        identity_or_l
        ((T S ≠  fapply f_ X) ⟇  ( (X ∈ T S) ⟇ (X ∉ fapply f_ X)))
        (reduction_clause
            (X = X)
            false
            ((T S ≠  fapply f_ X) ⟇  ( (X ∈ T S) ⟇ (X ∉ fapply f_ X)))
            (orI1 (X = X) false t44)
            t50
        )
    };

    // (step t52 (cl) :rule resolution :premises (t51 t32 t49 t47))

    admit; //TODO
end;