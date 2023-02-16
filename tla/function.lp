
require open tla.predicatelogic;
require open tla.settheory;

// Funtion constructor
symbol Func : U → (U → U) → U;

// Domain of a function
symbol DOMAIN: U → U;

// function application
symbol fapply : U → U → U;

// Axiomatizations
constant symbol DOMAIN-func S e: Prf (DOMAIN (Func S e) = S); 

constant symbol fapply-func S e x: Prf (x ∈ S) → Prf(fapply (Func S e) (x) = e x); 

// The predicate isAFunc characterizes functional values.
symbol isAFunc : U → U;

constant symbol funcIsAFunc S e: Prf (isAFunc(Func S e));

constant symbol isAFunc-def f : Prf ((isAFunc f) = (f = Func (DOMAIN f) (λ x, fapply f x)));

// Two functions are equal if they have the same domain and
//  agree on all arguments within the domain.
constant symbol funcEqual f g: Prf (isAFunc f) → Prf (isAFunc g) → Prf (DOMAIN f = DOMAIN g) → Prf (bforall (DOMAIN g) (λ x, (fapply f x) = (fapply g x)) ) →  Prf (f = g);


// FuncSet(S,T) represents the set of functions with domain S and co-domain
// T. It cannot be defined as a set comprehension because we do not have a
// bounding set for its elements.

symbol FuncSet:  U → U → U;
constant symbol FuncSetAx f S T: Prf (iff 
                                        (f ∈ (FuncSet S T))
                                        (and (isAFunc f)  (DOMAIN f = and S (bforall S   (λ x, (fapply f x) ∈ T))))
                                    );


symbol except: U → U → U → U;
constant symbol except-def f v e: Prf (except f v e = Func (DOMAIN f) (λ x, ite (x = v) e (fapply f x)));


// The following operators are useful for representing functions with finite domains by enumeration. They are not part of basic TLA+, but they are
// defined in the TLC module of the standard library.

symbol oneArg: U → U → U;
constant symbol oneArg-def x d e: Prf (Func (x ∈ singleton d) e);
notation oneArg infix 1;

//extend
symbol extend : U → U → U;
notation extend infix 2;
constant symbol extend-def f g : Prf ( Func ((DOMAIN f) ∪ (DOMAIN g))
                                        (λ x, ite (x ∈ f) (fapply f x) (fapply g x)
                                    ));

opaque symbol boolifyIsAFcn f: Prf (boolify(isAFunc(f)) = isAFunc(f)) ≔
begin
    assume f;
    apply subst (isAFunc f) (f = Func (DOMAIN f) (λ x, fapply f x)) (λ z, boolify z = z) (isAFunc-def f);
    apply boolifyEq (f) (Func (DOMAIN f) (λ x, fapply f x));
end;

opaque symbol exceptIsAFcn f v e : Prf (isAFunc (except f v e)) ≔
begin
    assume f v e;
    apply subst (except f v e) (Func (DOMAIN f) (λ x, ite (x = v) e (fapply f x))) (λ z, isAFunc z) (except-def f v e);
    apply funcIsAFunc (DOMAIN f) (λ x, ite (x = v) e (fapply f x));
end;

/*
We derive instances of axiom fcnEqual that help in automating proofs about
equality of functions.
*/
opaque symbol funcEqual2 f g :  Prf( isAFunc g )
                                → Prf( isAFunc f )
                                → Prf (DOMAIN f = DOMAIN g)
                                → Prf (bforall (DOMAIN g) (λ x, (fapply f x) = (fapply g x)))
                                → Prf (f = g)
                                ≔
begin
    
    assume f g HgIsFunc HfIsFunc  HDomEqual H;
    apply funcEqual f g HfIsFunc HgIsFunc HDomEqual H;
end;

opaque symbol funcEqualIff f g :  Prf( isAFunc f ) → Prf( isAFunc g ) → Prf (iff (f = g) (and (DOMAIN f = DOMAIN g) (bforall (DOMAIN g) (λ x, (fapply f x) = (fapply g x))))) ≔
begin
    assume f g HfIsFunc HgIsFunc;
    apply iffI (f = g) (and (DOMAIN f = DOMAIN g) (bforall (DOMAIN g) (λ x, fapply f x = fapply g x)))
    {
        assume HEqfg;
        apply andI (DOMAIN f = DOMAIN g) ((bforall (DOMAIN g) (λ x, fapply f x = fapply g x))) // split "and"
        // Case DOMAIN f = DOMAIN g
        { 
            apply ssubst f g (λ z, DOMAIN f = DOMAIN z) HEqfg;
            apply refl (DOMAIN f);
        }
        // Case (bforall (DOMAIN g) (λ x, fapply f x = fapply g x)))
        { 
            apply ssubst f g (λ z, bforall (DOMAIN g) (λ x, fapply f x = fapply z x)) HEqfg;
            apply ballI (DOMAIN g) (λ x, fapply f x = fapply f x);
            assume z H;
            apply refl (fapply f z);
        };
    }
    {
        assume H;
        have HDom: Prf (DOMAIN f = DOMAIN g) {
            apply andD1 (DOMAIN f = DOMAIN g) (bforall (DOMAIN g) (λ x, fapply f x = fapply g x)) H;
        };
        have Hfunc: Prf (bforall (DOMAIN g) (λ x, fapply f x = fapply g x)) {
            apply andD2 (DOMAIN f = DOMAIN g) (bforall (DOMAIN g) (λ x, fapply f x = fapply g x)) H;
        };
        apply funcEqual f g HfIsFunc HgIsFunc HDom Hfunc;
    };
end;

opaque symbol fcnCong S T e f : Prf (S = T)
                                → Prf (`forall x, imp (x ∈ T) (fapply e x = fapply f x))
                                → Prf (Func S (λ x, fapply e x) =  Func T (λ x, fapply f x)) ≔
begin
    assume S T e f  HSeqT H;
    apply funcEqual (Func S (λ x, fapply e x)) (Func T (λ x, fapply f x)) 
    { apply funcIsAFunc S (λ x, fapply e x) }
    { apply funcIsAFunc T (λ x, fapply f x) }
    { 
        apply subst (DOMAIN (Func S (λ x, fapply e x))) S (λ z, z = DOMAIN (Func T (λ x, fapply f x)))  (DOMAIN-func S (λ x, fapply e x));
        apply subst (DOMAIN (Func T (λ x, fapply f x))) T (λ z, S = z)  (DOMAIN-func T (λ x, fapply f x));
        apply HSeqT;
    }
    {
        apply ballI (DOMAIN (Func T (λ x, fapply f x))) (λ x, fapply (Func S (λ x, fapply e x)) x = fapply (Func T (λ x, fapply f x)) x);
        //assume z;
        //apply ssubst (DOMAIN (Func T (λ x, fapply f x))) (z ∈ T) (λ d, d) (DOMAIN-func T (λ x, fapply f x));
        assume z Htmp;
        have zInT : Prf (z ∈ T) {
            apply ssubst (DOMAIN (Func T (λ x, fapply f x))) T (λ d, z ∈ d) (DOMAIN-func T (λ x, fapply f x));
            apply Htmp;
        };
        have Himp: Prf (imp (z ∈ T) (fapply e z = fapply f z)) {
            apply allE (λ z, imp (z ∈ T) (fapply e z = fapply f z)) z H;
        };
        have Hfequal: Prf (fapply e z = fapply f z) {
            apply mp (z ∈ T) (fapply e z = fapply f z) Himp zInT;
        };
    };
    apply subst S T (λ d, fapply (Func d (λ x, fapply e x)) z = fapply (Func T (λ x, fapply f x)) z) HSeqT;

    apply subst 
    (fapply (Func T (λ x, fapply e x)) z)
    ((λ x, (fapply e x)) z)
    (λ a,  a =  fapply (Func T (λ x, fapply f x)) z)
    (fapply-func T (λ x, fapply e x) z zInT);
    apply subst 
    (fapply (Func T (λ x, fapply f x)) z)
    ((λ x, (fapply f x)) z)
    (λ a, (λ x, fapply e x) z  =  a)
    (fapply-func T (λ x, fapply f x) z zInT);
    simplify;
    apply Hfequal;
end;

opaque symbol domainExcept f v e: Prf (DOMAIN (except f v e) = DOMAIN f)  ≔
begin
    assume f v e;
    apply subst (except f v e) (Func (DOMAIN f) (λ x, ite (x = v) e (fapply f x))) (λ z, DOMAIN z = DOMAIN f) (except-def f v e);
    apply subst (DOMAIN (Func (DOMAIN f) (λ x, ite (x = v) e (fapply f x)))) (DOMAIN f) (λ z, z = DOMAIN f) (DOMAIN-func (DOMAIN f) (λ x, ite (x = v) e (fapply f x)));
    apply refl (DOMAIN f);
end;

opaque symbol applyExcept f v e w: Prf (w ∈ DOMAIN f) →  Prf ( (fapply (except f v e) w) = (ite (w = v) e (fapply f w))) ≔
begin
    assume f v e w HwInDomainf;
    apply subst (except f v e) (Func (DOMAIN f) (λ x, ite (x = v) e (fapply f x))) (λ z, fapply z w = ite (w = v) e (fapply f w)) (except-def f v e);
    // rewrite with the application function Axiom
    apply subst 
            (fapply (Func (DOMAIN f) (λ x, ite (x = v) e (fapply f x))) w)
            ((λ x, ite (x = v) e (fapply f x)) w)
            (λ z, z = ite (w = v) e (fapply f w))
            (fapply-func (DOMAIN f) (λ x, ite (x = v) e (fapply f x)) w HwInDomainf);
    simplify;
    apply trivial;
end;

opaque symbol exceptI f v e w p: Prf( w ∈ DOMAIN f ) → Prf (imp (v = w) (p e)) → Prf (imp (v ≠ w) (p (fapply f w))) → Prf( p (fapply (except f v e) w) ) ≔
begin
    simplify;
    assume f v e w p HwInDomF HImpVeqW HImpVNotEqW;
    apply subst (except f v e) (Func (DOMAIN f) (λ x, ite (x = v) e (fapply f x))) (λ z, p ((fapply z) w)) (except-def f v e);
    apply subst 
        (fapply (Func (DOMAIN f) (λ x, ite (x = v) e (fapply f x))) w)
        ((λ x, ite (x = v) e (fapply f x)) w)
        (λ z,  p z )
        (fapply-func (DOMAIN f) (λ x, ite (x = v) e (fapply f x)) w HwInDomF);
    simplify;
    apply iteI (w = v) e (fapply f w) (λ z, p z)
    { 
        assume Hw=v;
        apply mp (v = w) (p e) HImpVeqW (sym w v Hw=v);
    }
    {
        assume Hv≠w;
        have Hw≠v: Prf ((v = w) ) → Prf false {
            assume H;
            apply Hv≠w (sym v w H);
        };
        have notVeqW: Prf (not (v = w)) {
            apply notI (v = w) Hw≠v;
        };
        apply mp (v ≠ w) (p (fapply f w)) HImpVNotEqW notVeqW;
    };
end;

opaque symbol exceptTrivial f v e:  Prf( v ∉ (DOMAIN f) ) → Prf (isAFunc f) →  Prf ( except f v e = f) ≔
begin
    assume f v e HvNotIn HfIsFunc;
    apply funcEqual (except f v e) (f)
     { apply exceptIsAFcn f v e; }
     { apply HfIsFunc; }
     { apply domainExcept f v e;  }
     {  admit;  }; 
end;

opaque symbol exceptEqual f v e: Prf (isAFunc f) → Prf (iff (except f v e = f) (or (v ∉ DOMAIN f) (fapply f v = e))) ≔
begin
    assume f v e HisFunc;
    apply iffI (except f v e = f) (or (v ∉ DOMAIN f) (fapply f v = e))
    {  
        assume Hexcept;
        //TODO
        admit;
    }
    {
        assume H;
        apply orE (v ∉ DOMAIN f) (fapply f v = e) (except f v e = f) H 
        {
            assume HvNotInDomF;
            apply exceptTrivial f v e HvNotInDomF HisFunc;
        }
        {
            assume Happly;
            admit;
            //TODO
        };
    };
end;

opaque symbol funcConstruct p S: Prf (bforall S (λ x, `exists y, (p x y))) 
                                →  Prf (`exists f, and (and (isAFunc(f)) (DOMAIN f = S)) (bforall S (λ x, p x (fapply f x)))) ≔
begin
    admit;
end;


// Functions spaces

opaque symbol funcSetE f x S T p: Prf (f ∈ (FuncSet S T)) → Prf (x ∈ S) → ( Prf (isAFunc f) → Prf (DOMAIN f) → Prf (fapply f x ∈ T) → Prf p) → Prf p ≔
begin
    assume f x S T p HFuncSet HxInS H;
    //TODO: unfold FuncSet -- everything should be inside
    admit
end;

opaque symbol funcSetE' f x S T p: Prf (f ∈ (FuncSet S T)) → ( Prf (isAFunc f) → Prf (DOMAIN f) → Prf (`forall x, fapply f x ∈ T) → Prf p) → Prf p ≔
begin
    admit
end;