
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
constant symbol ExtTrigEqDef: Prf (`forall x, `forall y, (x = y) =  (x = y));

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
    // (step t8 (cl (not (= (not (or (∈ X (T S)) (not (∈ X (T S))))) false)) (or (∈ X (T S)) (not (∈ X (T S)))) false) :rule th_resolution :premises (t7 t6))
    have t8: Prf (
        or
            (or
                (not (not (or (X ∈ T S) (not (X ∈ T S))) = false))
                (or (X ∈ T S) (not (X ∈ T S)))
            )
            false
    ) {
        have t6': Prf (
        or
            (not (not (or (X ∈ T S) (not (X ∈ T S)))))
            (or
                false
                (not (not (or (X ∈ T S) (not (X ∈ T S))) = false))
            )
        )  {
            apply or_assoc_r (not (not (or (X ∈ T S) (not (X ∈ T S))))) false (not (not (or (X ∈ T S) (not (X ∈ T S))) = false));
            apply or_comm  (not (not (or (X ∈ T S) (not (X ∈ T S))) = false)) (or (not (not (or (X ∈ T S) (not (X ∈ T S))))) false) t6
        };
        have tmpt8: Prf (
            or
                (or false (not (not (or (X ∈ T S) (not (X ∈ T S))) = false)))
                (or (X ∈ T S) (not (X ∈ T S)))
        ) {
            apply reduction_clause
                (not (not (or (X ∈ T S) (not (X ∈ T S)))))
                (or false (not (not (or (X ∈ T S) (not (X ∈ T S))) = false)))
                (or (X ∈ T S) (not (X ∈ T S)))
                t6' t7
        };
        apply or_assoc_r (not (not (or (X ∈ T S) (not (X ∈ T S))) = false)) (or (X ∈ T S) (not (X ∈ T S))) false;
        apply or_comm  (or (not (not (or (X ∈ T S) (not (X ∈ T S))) = false)) (or (X ∈ T S) (not (X ∈ T S)))) false tmpt8;
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
        apply orI2 false (not (or (X ∈ T S) (not (X ∈ T S)))) Goal
    };
    have tmp6: Prf (or false false) {
        apply reduction_clause2 (or (X ∈ T S) (not (X ∈ T S))) false false tmp5 goal2;
    };
    have tmpf: Prf false {
        apply idempotence_or false tmp6;
    };
    apply tmpf;
end;

// (assume |SetStDef T| (forall ((smt__a Idv) (smt__x Idv)) (= (∈ smt__x (T smt__a)) (and (∈ smt__x smt__a) (not (∈ smt__x (FunApp f_ smt__x)))))))
//TODO: make a parallel with the settheory
constant symbol SetStDef t: Prf (`forall a, `forall x,  (x ∈ t a) = (and (x ∈ a) (x ∉  (fapply f_ x))));


/*
(anchor :step t7 :args ((:= (smt__x Idv) vr52) (:= (smt__y Idv) vr53)))
(step t7.t1 (cl (= smt__x vr52)) :rule refl)
(step t7.t2 (cl (= smt__y vr53)) :rule refl)
(step t7.t3 (cl (= (smt__TLA__TrigEq_Idv smt__x smt__y) (smt__TLA__TrigEq_Idv vr52 vr53))) :rule cong :premises (t7.t1 t7.t2))
(step t7.t4 (cl (= smt__x vr52)) :rule refl)
(step t7.t5 (cl (= smt__y vr53)) :rule refl)
(step t7.t6 (cl (= (= smt__x smt__y) (= vr52 vr53))) :rule cong :premises (t7.t4 t7.t5))
(step t7.t7 (cl (= (= (smt__TLA__TrigEq_Idv smt__x smt__y) (= smt__x smt__y)) (= (smt__TLA__TrigEq_Idv vr52 vr53) (= vr52 vr53)))) :rule cong :premises (t7.t3 t7.t6))
(step t7 (cl (= (forall ((smt__x Idv) (smt__y Idv)) (= (smt__TLA__TrigEq_Idv smt__x smt__y) (= smt__x smt__y))) (forall ((vr52 Idv) (vr53 Idv)) (= (smt__TLA__TrigEq_Idv vr52 vr53) (= vr52 vr53))))) :rule bind)
*/
opaque symbol thm_t7 : Prf ((`forall x, `forall y, ((x = y) = (x = y))) = (`forall vr52, `forall vr53, ((vr52 = vr53) = (vr52 = vr53)) )) ≔
begin
    apply bind2 (λ x y, ((x = y) = (x = y))) (λ vr52 vr53, ((vr52 = vr53) = (vr52 = vr53)));
    assume x y;
    simplify;
    apply trivial
end;

/*
(anchor :step t10 :args ((:= (vr52 Idv) vr54) (:= (vr53 Idv) vr55)))
(step t10.t1 (cl (= vr52 vr54)) :rule refl)
(step t10.t2 (cl (= vr53 vr55)) :rule refl)
(step t10.t3 (cl (= (smt__TLA__TrigEq_Idv vr52 vr53) (smt__TLA__TrigEq_Idv vr54 vr55))) :rule cong :premises (t10.t1 t10.t2))
(step t10.t4 (cl (= vr52 vr54)) :rule refl)
(step t10.t5 (cl (= vr53 vr55)) :rule refl)
(step t10.t6 (cl (= (= vr52 vr53) (= vr54 vr55))) :rule cong :premises (t10.t4 t10.t5))
(step t10.t7 (cl (= (= (smt__TLA__TrigEq_Idv vr52 vr53) (= vr52 vr53)) (= (smt__TLA__TrigEq_Idv vr54 vr55) (= vr54 vr55)))) :rule cong :premises (t10.t3 t10.t6))
(step t10 (cl (= (forall ((vr52 Idv) (vr53 Idv)) (= (smt__TLA__TrigEq_Idv vr52 vr53) (= vr52 vr53))) (forall ((vr54 Idv) (vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 vr55) (= vr54 vr55))))) :rule bind)
*/
opaque symbol thm_t10 : Prf ((`forall vr52, `forall vr53, ((vr52 = vr53) = (vr52 = vr53))) = (`forall vr54, `forall vr55, ((vr54 = vr55) = (vr54 = vr55)) )) ≔
begin
    apply bind2 (λ vr52 vr53, ((vr52 = vr53) = (vr52 = vr53))) (λ vr54 vr55, ((vr54 = vr55) = (vr54 = vr55))) ;
    assume vr52 vr53;
    simplify;
    apply trivial
end;

/*
(anchor :step t13 :args ((:= (smt__a Idv) vr56) (:= (smt__x Idv) vr57)))
(step t13.t1 (cl (= smt__x vr57)) :rule refl)
(step t13.t2 (cl (= smt__a vr56)) :rule refl)
(step t13.t3 (cl (= (T smt__a) (T vr56))) :rule cong :premises (t13.t2))
(step t13.t4 (cl (= (∈ smt__x (T smt__a)) (∈ vr57 (T vr56)))) :rule cong :premises (t13.t1 t13.t3))
(step t13.t5 (cl (= smt__x vr57)) :rule refl)
(step t13.t6 (cl (= smt__a vr56)) :rule refl)
(step t13.t7 (cl (= (∈ smt__x smt__a) (∈ vr57 vr56))) :rule cong :premises (t13.t5 t13.t6))
(step t13.t8 (cl (= smt__x vr57)) :rule refl)
(step t13.t9 (cl (= smt__x vr57)) :rule refl)
(step t13.t10 (cl (= (FunApp f_ smt__x) (FunApp f_ vr57))) :rule cong :premises (t13.t9))
(step t13.t11 (cl (= (∈ smt__x (FunApp f_ smt__x)) (∈ vr57 (FunApp f_ vr57)))) :rule cong :premises (t13.t8 t13.t10))
(step t13.t12 (cl (= (not (∈ smt__x (FunApp f_ smt__x))) (not (∈ vr57 (FunApp f_ vr57))))) :rule cong :premises (t13.t11))
(step t13.t13 (cl (= (and (∈ smt__x smt__a) (not (∈ smt__x (FunApp f_ smt__x)))) (and (∈ vr57 vr56) (not (∈ vr57 (FunApp f_ vr57)))))) :rule cong :premises (t13.t7 t13.t12))
(step t13.t14 (cl (= (= (∈ smt__x (T smt__a)) (and (∈ smt__x smt__a) (not (∈ smt__x (FunApp f_ smt__x))))) (= (∈ vr57 (T vr56)) (and (∈ vr57 vr56) (not (∈ vr57 (FunApp f_ vr57))))))) :rule cong :premises (t13.t4 t13.t13))
(step t13 (cl (
    =
        (forall ((smt__a Idv) (smt__x Idv)) (=
                                                (∈ smt__x (T smt__a))
                                                (and (∈ smt__x smt__a) (not (∈ smt__x (FunApp f_ smt__x))))))
        (forall ((vr56 Idv) (vr57 Idv)) (=
                                                (∈ vr57 (T vr56))
                                                (and (∈ vr57 vr56) (not (∈ vr57 (FunApp f_ vr57))))))))
:rule bind)
*/
opaque symbol thm_t13 : Prf (
    (`forall a, `forall x, (x ∈ T a) = and (x ∈ a) (x ∉  (fapply f_ x)))
    =
    (`forall vr56, `forall vr57, (vr57 ∈ T vr56) = and (vr57 ∈ vr56) (vr57 ∉  (fapply f_ vr57)))) ≔
begin
    apply bind2 (λ a x, ((x ∈ T a) = and (x ∈ a) (x ∉  (fapply f_ x)))) (λ vr56 vr57,  ((vr57 ∈ T vr56) = and (vr57 ∈ vr56) (vr57 ∉  (fapply f_ vr57))));
    assume a b ;
    simplify;
    apply trivial
end;

/*
(anchor :step t16 :args ((:= (vr56 Idv) vr58) (:= (vr57 Idv) vr59)))
(step t16.t1 (cl (= vr57 vr59)) :rule refl)
(step t16.t2 (cl (= vr56 vr58)) :rule refl)
(step t16.t3 (cl (= (T vr56) (T vr58))) :rule cong :premises (t16.t2))
(step t16.t4 (cl (= (∈ vr57 (T vr56)) (∈ vr59 (T vr58)))) :rule cong :premises (t16.t1 t16.t3))
(step t16.t5 (cl (= vr57 vr59)) :rule refl)
(step t16.t6 (cl (= vr56 vr58)) :rule refl)
(step t16.t7 (cl (= (∈ vr57 vr56) (∈ vr59 vr58))) :rule cong :premises (t16.t5 t16.t6))
(step t16.t8 (cl (= vr57 vr59)) :rule refl)
(step t16.t9 (cl (= vr57 vr59)) :rule refl)
(step t16.t10 (cl (= (FunApp f_ vr57) (FunApp f_ vr59))) :rule cong :premises (t16.t9))
(step t16.t11 (cl (= (∈ vr57 (FunApp f_ vr57)) (∈ vr59 (FunApp f_ vr59)))) :rule cong :premises (t16.t8 t16.t10))
(step t16.t12 (cl (= (not (∈ vr57 (FunApp f_ vr57))) (not (∈ vr59 (FunApp f_ vr59))))) :rule cong :premises (t16.t11))
(step t16.t13 (cl (= (and (∈ vr57 vr56) (not (∈ vr57 (FunApp f_ vr57)))) (and (∈ vr59 vr58) (not (∈ vr59 (FunApp f_ vr59)))))) :rule cong :premises (t16.t7 t16.t12))
(step t16.t14 (cl (= (= (∈ vr57 (T vr56)) (and (∈ vr57 vr56) (not (∈ vr57 (FunApp f_ vr57))))) (= (∈ vr59 (T vr58)) (and (∈ vr59 vr58) (not (∈ vr59 (FunApp f_ vr59))))))) :rule cong :premises (t16.t4 t16.t13))
(step t16 (cl (= (forall ((vr56 Idv) (vr57 Idv)) (= (∈ vr57 (T vr56)) (and (∈ vr57 vr56) (not (∈ vr57 (FunApp f_ vr57)))))) (forall ((vr58 Idv) (vr59 Idv)) (= (∈ vr59 (T vr58)) (and (∈ vr59 vr58) (not (∈ vr59 (FunApp f_ vr59)))))))) :rule bind)
*/
opaque symbol thm_t16 : Prf (
    (`forall vr56, `forall vr57, (vr57 ∈ (T vr56)) = and (vr57 ∈ vr56) (vr57 ∉ (fapply f_ vr57)))
    =
    (`forall vr58, `forall vr59, (vr59 ∈ (T vr58)) = and (vr59 ∈ vr58) (vr59 ∉ (fapply f_ vr59)))
) ≔
begin
    apply bind2 (λ vr56 vr57, ((vr57 ∈ (T vr56)) = and (vr57 ∈ vr56) (vr57 ∉ (fapply f_ vr57)))) (λ vr58 vr59, ((vr59 ∈ (T vr58)) = and (vr59 ∈ vr58) (vr59 ∉ (fapply f_ vr59))));
    assume vr56 vr57;
    simplify;
    apply trivial
end;

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
    /*
    (anchor :step t7 :args ((:= (smt__x Idv) vr52) (:= (smt__y Idv) vr53)))
    ...
    (step t7 (cl (= (forall ((smt__x Idv) (smt__y Idv)) (= (smt__TLA__TrigEq_Idv smt__x smt__y) (= smt__x smt__y))) (forall ((vr52 Idv) (vr53 Idv)) (= (smt__TLA__TrigEq_Idv vr52 vr53) (= vr52 vr53))))) :rule bind)
    */
    have t7: Prf ((`forall x, `forall y, ((x = y) = (x = y))) = (`forall vr52, `forall vr53, ((vr52 = vr53) = (vr52 = vr53)) )) {
        apply thm_t7
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
        have t8': Prf (
            or
                (not (`forall x, `forall y, ((x = y) = (x = y))))
                (`forall vr52, `forall vr53, ((vr52 = vr53) = (vr52 = vr53)))
            ) {
            apply ssubst
            (`forall x, `forall y, (x = y) = (x = y))
            (`forall vr52, `forall vr53, (vr52 = vr53) = (vr52 = vr53))
            (λ z, or
                    (not (`forall x, `forall y, ((x = y) = (x = y))))
                    (`forall vr52, `forall vr53, ((vr52 = vr53) = (vr52 = vr53)))
            )
            t7 t8
        };
        // We have t7 t8 that reduce to True, so to finish the Goal we need ExtTrigEqDef
        apply ExtTrigEqDef
    };

    /*
    (anchor :step t10 :args ((:= (vr52 Idv) vr54) (:= (vr53 Idv) vr55)))
    ...
    (step t10 (cl (= (forall ((vr52 Idv) (vr53 Idv)) (= (smt__TLA__TrigEq_Idv vr52 vr53) (= vr52 vr53))) (forall ((vr54 Idv) (vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 vr55) (= vr54 vr55))))) :rule bind)
    */
    have t10: Prf ((`forall vr52, `forall vr53, ((vr52 = vr53) = (vr52 = vr53))) = (`forall vr54, `forall vr55, ((vr54 = vr55) = (vr54 = vr55)) )) {
        apply thm_t10
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
        apply ssubst
            (`forall vr52, `forall vr53, (vr52 = vr53) = (vr52 = vr53))
            (`forall vr54, `forall vr55, ((vr54 = vr55) = (vr54 = vr55)))
            (λ z, z)
            t10 t9
    };

    //(step t13 (cl (= (forall ((smt__a Idv) (smt__x Idv)) (= (∈ smt__x (T smt__a)) (and (∈ smt__x smt__a) (not (∈ smt__x (FunApp f smt__x)))))) (forall ((veriT_vr56 Idv) (veriT_vr57 Idv)) (= (∈ veriT_vr57 (T veriT_vr56)) (and (∈ veriT_vr57 veriT_vr56) (not (∈ veriT_vr57 (FunApp f veriT_vr57)))))))) :rule bind)
    have t13: Prf (
            (`forall a, `forall x, (x ∈ T a) = and (x ∈ a) (x ∉  (fapply f_ x)))
            =
            (`forall vr56, `forall vr57, (vr57 ∈ T vr56) = and (vr57 ∈ vr56) (vr57 ∉  (fapply f_ vr57)))
        ) {
        apply thm_t13;
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
        apply SetStDef T
    };
    //(step t16 (cl (= (forall ((veriT_vr56 Idv) (veriT_vr57 Idv)) (= (∈ veriT_vr57 (T veriT_vr56)) (and (∈ veriT_vr57 veriT_vr56) (not (∈ veriT_vr57 (FunApp f veriT_vr57)))))) (forall ((veriT_vr58 Idv) (veriT_vr59 Idv)) (= (∈ veriT_vr59 (T veriT_vr58)) (and (∈ veriT_vr59 veriT_vr58) (not (∈ veriT_vr59 (FunApp f veriT_vr59)))))))) :rule bind)
    have t16: Prf (
        (`forall vr56, `forall vr57, (vr57 ∈ (T vr56)) = and (vr57 ∈ vr56) (vr57 ∉ (fapply f_ vr57)))
        =
        (`forall vr58, `forall vr59, (vr59 ∈ (T vr58)) = and (vr59 ∈ vr58) (vr59 ∉ (fapply f_ vr59)))
    ) {
        apply thm_t16
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
    have t18: Prf (`forall vr58, `forall vr59, (vr59 ∈ (T vr58)) = and (vr59 ∈ vr58) (vr59 ∉ (fapply f_ vr59))) {
        apply ssubst
            (`forall vr56, `forall vr57, (vr57 ∈ (T vr56)) = and (vr57 ∈ vr56) (vr57 ∉ (fapply f_ vr57)))
            (`forall vr58, `forall vr59, (vr59 ∈ (T vr58)) = and (vr59 ∈ vr58) (vr59 ∉ (fapply f_ vr59)))
            (λ z, z)
            t16 t15
    };

    //(step t19 (cl (or (not (forall ((vr54 Idv) (veriT_vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 veriT_vr55) (= vr54 veriT_vr55)))) (forall ((vr54 Idv) (veriT_vr55 Idv)) (or (not (smt__TLA__TrigEq_Idv vr54 veriT_vr55)) (= vr54 veriT_vr55))))) :rule qnt_cnf)
    have t19: Prf (or (¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55))) ((`forall vr54, `forall vr55, or (vr54 ≠ vr55) (vr54 = vr55)))  ) {
        apply cnf2 (λ vr54 vr55, (vr54 = vr55) = (vr54 = vr55)) (λ vr54 vr55, or (vr54 ≠ vr55) (vr54 = vr55));
        assume x y;
        simplify;
        apply or_comm  (x = y) (not (x = y));
        apply excluded_middle (x = y);
    };
    //
    // (step t20 (cl
    // (not (forall ((vr54 Idv) (veriT_vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 veriT_vr55) (= vr54 veriT_vr55))))
    // (forall ((vr54 Idv) (veriT_vr55 Idv)) (or (not (smt__TLA__TrigEq_Idv vr54 veriT_vr55)) (= vr54 veriT_vr55)))
    // ) :rule or :premises (t19))
    have t20: Prf (or (¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)) ) ((`forall vr54, `forall vr55, or (vr54 ≠ vr55) (vr54 = vr55)))  ) {
        apply t19;
    };

    // (step t21 (cl (or (not (forall ((vr54 Idv) (vr55 Idv)) (or (not (smt__TLA__TrigEq_Idv vr54 vr55)) (= vr54 vr55)))) (or (not (smt__TLA__TrigEq_Idv (FunApp f_ X) (T S))) (= (T S) (FunApp f_ X))))) :rule forall_inst :args ((:= vr54 (FunApp f_ X)) (:= vr55 (T S))))
    have t21: Prf (
        or ( not ( `forall vr54, `forall vr55, or (vr54 ≠ vr55) (vr54 = vr55)))
            (or (fapply f_ X  ≠ T S) ((fapply f_ X) = T S ))
    ) {
        apply forall_inst_2 (λ vr54 vr55, or (vr54 ≠ vr55) (vr54 = vr55)) (fapply f_ X) (T S);
        simplify;
    };

    // (step t22 (cl (not (forall ((vr54 Idv) (vr55 Idv)) (or (not (smt__TLA__TrigEq_Idv vr54 vr55)) (= vr54 vr55)))) (or (not (smt__TLA__TrigEq_Idv (FunApp f_ X) (T S))) (= (T S) (FunApp f_ X)))) :rule or :premises (t21))
    have t22: Prf (( not ( `forall vr54, `forall vr55, or (vr54 ≠ vr55) (vr54 = vr55))) ⟇ (or (fapply f_ X  ≠ T S) ((fapply f_ X) = T S ))
    ) {
        apply t21
    };

    //(step t23 (cl (or (not (forall ((vr54 Idv) (vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 vr55) (= vr54 vr55)))) (or (not (smt__TLA__TrigEq_Idv (FunApp f_ X) (T S))) (= (T S) (FunApp f_ X)))) (not (not (forall ((vr54 Idv) (vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 vr55) (= vr54 vr55)))))) :rule or_neg)
    have t23: Prf (
        (or (¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)))
            (or (fapply f_ X ≠ T S)
                (fapply f_ X =  T S))
        )
        ⟇
        (¬ ¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)))
    ) {
        apply or_neg (¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)))  (or (fapply f_ X ≠ T S) (fapply f_ X =  T S))
    };

    // (step t24 (cl (not (not (not (forall ((vr54 Idv) (vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 vr55) (= vr54 vr55)))))) (forall ((vr54 Idv) (vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 vr55) (= vr54 vr55)))) :rule not_not)
    have t24: Prf (
        (¬ ¬ ¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)))
        ⟇
        (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55))
    ) {
        apply not_not (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55))
    };

    // (step t25 (cl (or (not (forall ((vr54 Idv) (vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 vr55) (= vr54 vr55)))) (or (not (smt__TLA__TrigEq_Idv (FunApp f_ X) (T S))) (= (T S) (FunApp f_ X)))) (forall ((vr54 Idv) (vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 vr55) (= vr54 vr55)))) :rule th_resolution :premises (t24 t23))
    //HACK we need to use t6 to apply the symmetry of T S = fapply f_ X
    have t25: Prf (
        or (¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)))
            (or
                (fapply f_ X  ≠ T S)
                (T S = fapply f_ X)
            )
        ⟇
        (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55))
    ) {
        have t25': Prf (
            or (¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)))
            (or
                (fapply f_ X  ≠ T S)
                (fapply f_ X = T S)
            )
            ⟇
            (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55))
        ) {
                apply //or_comm (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)) (or (¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55))) (or (fapply f_ X ≠ T S) (fapply f_ X =  T S)))
                reduction_clause2
                    (¬ ¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)))
                    (or (¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)))  (or (fapply f_ X ≠ T S) (fapply f_ X =  T S)))
                    (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55))
                    t23
                    (or_comm (¬ ¬ ¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55))) (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)) t24)

        };
        have t25'': Prf (
            or (¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)))
            (or
                (fapply f_ X  ≠ T S)
                (T S = T S)
            )
            ⟇
            (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55))
        ) {
            apply ssubst (fapply f_ X) (T S)
                (λ z, or (or (not (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55))) (or (not (fapply f_ X = T S)) (z = T S))) (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)))
                t6 t25'

        };

        apply subst (fapply f_ X) (T S)
            (λ z, or (or (not (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55))) (or (not (fapply f_ X = T S)) (T S = z))) (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)))
            t6 t25''
    };

    // (step t26 (cl (or (not (forall ((vr54 Idv) (vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 vr55) (= vr54 vr55)))) (or (not (smt__TLA__TrigEq_Idv (FunApp f_ X) (T S))) (= (T S) (FunApp f_ X)))) (not (or (not (smt__TLA__TrigEq_Idv (FunApp f_ X) (T S))) (= (T S) (FunApp f_ X))))) :rule or_neg)
    have t26: Prf (
        (or
            (or (fapply f_ X  ≠ T S) (T S = fapply f_ X)))
            (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55))
        ⟇
        (¬ (or (fapply f_ X  ≠ T S) (T S = fapply f_ X)))
    ) {
        apply or_neg (or (fapply f_ X  ≠ T S) (T S = fapply f_ X)) (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55))
    };

    //(step t27 (cl (or (not (forall ((vr54 Idv) (vr55 Idv)) (= (smt__TLA__TrigEq_Idv vr54 vr55) (= vr54 vr55)))) (or (not (smt__TLA__TrigEq_Idv (FunApp f_ X) (T S))) (= (T S) (FunApp f_ X))))) :rule th_resolution :premises (t20 t22 t25 t26))
    have t27: Prf (
        or (¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)))
            (or (fapply f_ X  ≠ T S)(T S = fapply f_ X)
        )
    ) {
        have t22': Prf ((or (fapply f_ X  ≠ T S) ((fapply f_ X) = T S )) ⟇  ( not ( `forall vr54, `forall vr55, or (vr54 ≠ vr55) (vr54 = vr55)))) {
            apply or_comm (not ( `forall vr54, `forall vr55, or (vr54 ≠ vr55) (vr54 = vr55))) (or (fapply f_ X  ≠ T S) ((fapply f_ X) = T S ))  t22
        };
        have tmp: Prf (
            or (¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)))
            (or (fapply f_ X  ≠ T S)(fapply f_ X = T S))
        ) {
            apply reduction_clause2
                ( `forall vr54, `forall vr55, or (vr54 ≠ vr55) (vr54 = vr55))
                (¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)))
                (or (fapply f_ X ≠ T S) (fapply f_ X = T S))
                t20  t22'
        };
        //HACK with t6 due to the bug of veriT mentioned earlier (inversion in =).
        // Similar hack in t25.
        have tmp': Prf (
            or (¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)))
            (or (fapply f_ X  ≠ T S)(T S = T S))
        ) {
            apply ssubst (fapply f_ X) (T S)
            (λ z, or (not (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55))) (or (not (fapply f_ X = T S)) (z = T S)))
            t6 tmp
        };

        apply subst (fapply f_ X) (T S)
            (λ z, or (not (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55))) (or (not (fapply f_ X = T S)) (T S = z)))
            t6 tmp'
    };

    // (step t28 (cl (not (or (not (smt__TLA__TrigEq_Idv (FunApp f_ X) (T S))) (= (T S) (FunApp f_ X)))) (not (smt__TLA__TrigEq_Idv (FunApp f_ X) (T S))) (= (T S) (FunApp f_ X))) :rule or_pos)
    have t28: Prf (
        (¬ (or  (fapply f_ X  ≠ T S) (T S = fapply f_ X)))
        ⟇
        ((fapply f_ X  ≠ T S)
        ⟇
        (T S = fapply f_ X))
    ) {
        apply or_pos (fapply f_ X  ≠ T S) (T S = fapply f_ X)
    };

    have t29: Prf (
        or (¬ (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)))
        (or
            (fapply f_ X  ≠ T S)
            (T S = fapply f_ X)
        )
    ) {
        apply t27;
    };

    // (step t30 (cl (not (or (not (smt__TLA__TrigEq_Idv (FunApp f_ X) (T S))) (= (T S) (FunApp f_ X)))) (= (T S) (FunApp f_ X))) :rule resolution :premises (t28 t6))
    have t30: Prf ((¬ (or (fapply f_ X  ≠ T S) (T S = fapply f_ X))) ⟇ (T S = fapply f_ X)) {
        have t28': Prf (
            ((T S = fapply f_ X)
            ⟇
            (¬ (or  (fapply f_ X  ≠ T S) (T S = fapply f_ X))))
            ⟇
            (fapply f_ X  ≠ T S)
        ) {
            apply or_assoc_l (T S = fapply f_ X) (¬ (or  (fapply f_ X  ≠ T S) (T S = fapply f_ X))) (fapply f_ X  ≠ T S);
            apply or_comm (or (¬ (or (fapply f_ X ≠ T S) (T S = fapply f_ X))) (fapply f_ X ≠ T S)) (T S = fapply f_ X);
            apply or_assoc_l (¬ (or  (fapply f_ X  ≠ T S) (T S = fapply f_ X))) (fapply f_ X  ≠ T S) (T S = fapply f_ X);
            apply t28
        };

        apply or_comm (T S = fapply f_ X) (¬ (or  (fapply f_ X  ≠ T S) (T S = fapply f_ X)))
                (reduction_clause2
                    (fapply f_ X = T S)
                    false
                    ((T S = fapply f_ X) ⟇ (¬ (or  (fapply f_ X  ≠ T S) (T S = fapply f_ X))))
                    (orI2 false (fapply f_ X = T S) t6)
                    t28')
    };

    //(step t31 (cl (or (not (smt__TLA__TrigEq_Idv (FunApp f_ X) (T S))) (= (T S) (FunApp f_ X)))) :rule resolution :premises (t29 t12))
    have t31: Prf (or (fapply f_ X  ≠ T S) (T S = fapply f_ X)) {
        apply reduction_clause
                (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55))
                false
                (or (fapply f_ X  ≠ T S) (T S = fapply f_ X))
                (orI1 (`forall vr54, `forall vr55, (vr54 = vr55) = (vr54 = vr55)) false t12)
                t29

    };

    // (step t32 (cl (= (T S_) (smt__TLA__FunApp f_ x_))) :rule resolution :premises (t30 t31))
    have t32: Prf ((T S) = (fapply f_ X)) {
        apply reduction_clause
            (or (fapply f_ X  ≠ T S) (T S = fapply f_ X))
            false
            (T S = fapply f_ X)
            (orI1  (or (fapply f_ X  ≠ T S) (T S = fapply f_ X)) false t31)
            t30
    };

    // (step t33 (cl (or (not (forall ((veriT_vr58 Idv) (veriT_vr59 Idv)) (= (∈ veriT_vr59 (T veriT_vr58)) (and (∈ veriT_vr59 veriT_vr58) (not (∈ veriT_vr59 (smt__TLA__FunApp f_ veriT_vr59))))))) (= (∈ x_ (T S_)) (and (∈ x_ S_) (not (∈ x_ (smt__TLA__FunApp smt__CONSTANT_f_ X))))))) :rule forall_inst :args ((:= veriT_vr58 S_) (:= veriT_vr59 X)))
    have t33: Prf (
        or (¬ (`forall vr58, `forall vr59, (vr59 ∈ T vr58) = (and (vr59 ∈ vr58) (vr59 ∉ fapply f_ vr59))))
            (X ∈ T S = (and (X ∈ S) (X ∉ (fapply f_ X))))
    ) {
        apply forall_inst_2 (λ vr58 vr59,  (vr59 ∈ T vr58) = (and (vr59 ∈ vr58) (vr59 ∉ fapply f_ vr59))) S X
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

    //(step t40 (cl (not (forall ((vr58 Idv) (vr59 Idv)) (= (∈ vr59 (T vr58)) (and (∈ vr59 vr58) (not (∈ vr59 (FunApp _f_ vr59))))))) (= (∈ _x_ (T _S_)) (and (∈ _x_ _S_) (not (∈ _x_ (FunApp _f_ _x_)))))) :rule or :premises (t33))
    have t40: Prf (
        or (¬ (`forall vr58, `forall vr59, (vr59 ∈ T vr58) = (and (vr59 ∈ vr58) (vr59 ∉ fapply f_ vr59))))
            (X ∈ T S = (and (X ∈ S) (X ∉ (fapply f_ X))))
        ) {
        apply t33;
    };

    // (step t41 (cl (and (∈ _x_ _S_) (not (∈ _x_ (FunApp _f_ _x_)))) (∈ _x_ (FunApp _f_ _x_))) :rule resolution :premises (t37 h2))
    have t41: Prf (or (and (X ∈ S) (X ∉ fapply f_ X))  (X ∈ fapply f_ X)) {

        have t37': Prf (or (or (X ∈ fapply f_ X) (and (X ∈ S) (X ∉ fapply f_ X))) (X ∉ S)) {
            apply or_assoc_l (X ∈ fapply f_ X) (and (X ∈ S) (X ∉ fapply f_ X)) (X ∉ S);
            apply or_comm  (or (and (X ∈ S) (X ∉ fapply f_ X)) (X ∉ S)) (X ∈ fapply f_ X);
            apply or_assoc_l (and (X ∈ S) (X ∉ fapply f_ X)) (X ∉ S) (X ∈ fapply f_ X);
            apply t37
        };

        apply or_comm (X ∈ fapply f_ X) (and (X ∈ S) (X ∉ fapply f_ X))
            (reduction_clause2
                (X ∈ S)
                false
                (or (X ∈ fapply f_ X) (and (X ∈ S) (X ∉ fapply f_ X)))
                (orI2 false (X ∈ S)  H2)
                t37'
            )
    };

    // (step t42 (cl (= (∈ _x_ (T _S_)) (and (∈ _x_ _S_) (not (∈ _x_ (FunApp _f_ _x_)))))) :rule resolution :premises (t40 t18))
    have t42: Prf ((X ∈ T S) = (and (X ∈ S) (X ∉ fapply f_ X))) {
        apply reduction_clause
        (`forall vr58, `forall vr59, (vr59 ∈ T vr58) = and (vr59 ∈ vr58) (vr59 ∉ fapply f_ vr59))
        false
        ((X ∈ T S) = (and (X ∈ S) (X ∉ fapply f_ X)))
        (orI1 (`forall vr58, `forall vr59, (vr59 ∈ T vr58) = and (vr59 ∈ vr58) (vr59 ∉ fapply f_ vr59)) false t18)
        t40
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
        apply reduction_clause
                (X = X)
                false
                ((T S ≠ (fapply f_ X)) ⟇ ((X ∉ (T S)) ⟇ (X ∈ fapply f_ X)))
                (orI1 true false t44)
                t43
    };

    // (step t46 (cl (not (∈ _x_ (T _S_))) (∈ _x_ (FunApp _f_ _x_))) :rule resolution :premises (t45 t32))
    have t46: Prf ((X ∉ T S)  ⟇ (X ∈ fapply f_ X)) {
        apply reduction_clause
            (T S = fapply f_ X)
            false
            (X ∉ T S ⟇ X ∈ fapply f_ X)
            (orI1 (T S = fapply f_ X) false t32)
            t45
    };

    // (step t47 (cl (∈ _x_ (FunApp _f_ _x_))) :rule resolution :premises (t46 t38 t41 t42))
    have t47: Prf (X ∈ fapply f_ X) {
        have t41': Prf (or (X ∈ T S) (X ∈ fapply f_ X)) {
            apply subst (X ∈ T S) (and (X ∈ S) (X ∉ fapply f_ X)) (λ z, or z (X ∈ fapply f_ X)) t42 t41
        };
        // t38 is useless here because it reduce to True with t42 equality
        apply reduction_clause
            (X ∈ T S)
            (X ∈ fapply f_ X)
            (X ∈ fapply f_ X)
            t41'
            t46;
    };

    // (step t48 (cl (not (and (∈ _x_ _S_) (not (∈ _x_ (FunApp _f_ _x_)))))) :rule resolution :premises (t34 t47))
    have t48: Prf ( ¬ and (X ∈ S) (X ∉ fapply f_ X)) {
        apply reduction_clause2
            (X ∈ fapply f_ X)
            false
            ( ¬ and (X ∈ S) (X ∉ fapply f_ X))
            (orI2 false (X ∈ fapply f_ X)  t47)
            t34
    };

    // (step t49 (cl (not (∈ _x_ (T _S_)))) :rule resolution :premises (t39 t48 t42))
    have t49: Prf (X ∉ T S) {
        have t39' : Prf (or ((X ∈ T S) ≠ and (X ∈ S) (X ∉ fapply f_ X)) (X ∉ T S)) {
            apply reduction_clause2
                (and (X ∈ S) (X ∉ fapply f_ X))
                (or ((X ∈ T S) ≠ and (X ∈ S) (X ∉ fapply f_ X)) (X ∉ T S))
                false
                t39
                (orI2 false (¬ (and (X ∈ S) (X ∉ fapply f_ X))) t48)
        };
        have t39'': Prf (or ((X ∈ T S) ≠ (X ∈ T S)) (X ∉ T S)) {
            apply subst (X ∈ T S) (and (X ∈ S) (X ∉ fapply f_ X)) (λ z, or ((X ∈ T S) ≠ z) (X ∉ T S)) t42 t39'
        };
        have t39''': Prf (or false (X ∉ T S)) { apply t39''};
        apply t39'''
    };

    // (step t50 (cl (not (= _x_ _x_)) (not (= (T _S_) (FunApp _f_ _x_))) (not (∈ _x_ (FunApp _f_ _x_))) (∈ _x_ (T _S_))) :rule eq_congruent_pred)
    have t50: Prf ((X ≠ X) ⟇ ((T S ≠  fapply f_ X) ⟇  ( (X ∈ T S) ⟇ (X ∉ fapply f_ X)))) {
        //NOTE bug in eq_congruent_pred order
        apply eq_congruent_pred X X (T S) (fapply f_ X) (λ x1 x2, x1 ∈ x2) (λ y1 y2, y1 ∉ y2)
    };

    //(step t51 (cl (not (= (T _S_) (FunApp _f_ _x_))) (not (∈ _x_ (FunApp _f_ _x_))) (∈ _x_ (T _S_))) :rule th_resolution :premises (t50 t44))
    have t51: Prf ((T S ≠  fapply f_ X) ⟇  ( (X ∈ T S) ⟇ (X ∉ fapply f_ X))) {
        apply reduction_clause
                (X = X)
                false
                ((T S ≠  fapply f_ X) ⟇  ( (X ∈ T S) ⟇ (X ∉ fapply f_ X)))
                (orI1 (X = X) false t44)
                t50
    };

    // (step t52 (cl) :rule resolution :premises (t51 t32 t49 t47))
    have t52: Prf (((T S ≠  fapply f_ X) ⟇  (X ∈ T S)) ⟇ (X ∉ fapply f_ X)) {
        apply  or_assoc_l  (T S ≠  fapply f_ X) (X ∈ T S)  (X ∉ fapply f_ X) t51
    };

    // rule resolution :premises (t51 t47))
    have t52': Prf ((T S ≠  fapply f_ X) ⟇  X ∈ T S) {
        apply reduction_clause2
            (X ∈ fapply f_ X)
            false
            ((T S ≠ fapply f_ X) ⟇ (X ∈ T S))
            (orI2 false  (X ∈ fapply f_ X) t47)
            t52
    };

    // rule resolution :premises (t51 t49))
    have t52''': Prf ((T S ≠  fapply f_ X)) {
        apply reduction_clause2
                (X ∈ T S)
                (T S ≠ fapply f_ X)
                false
                t52'
                (orI2 false  (X ∉ T S) t49)

    };

    // rule resolution :premises (t51 t32))
    apply subst (T S) (fapply f_ X) (λ z, (T S) ≠ z) t32  t52'''
end;
