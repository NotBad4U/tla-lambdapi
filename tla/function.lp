
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
constant symbol funcEqual f g: Prf (isAFunc f) → Prf (isAFunc g) → Prf (DOMAIN f = DOMAIN g) → Prf (bforall (DOMAIN g) (λ x, imp ((fapply f x) = (fapply g x)) (f = g)));


// FuncSet(S,T) represents the set of functions with domain S and co-domain
// T. It cannot be defined as a set comprehension because we do not have a
// bounding set for its elements.

symbol FuncSet: U → U → U;
constant symbol FuncSetAx f S T: Prf (iff 
                                        (f ∈ (FuncSet S T))
                                        (and (isAFunc f)  (DOMAIN f = and S (bforall S   (λ x, (fapply f x) ∈ T))))
                                    );


symbol except: U → U → U → U;
constant symbol except-def f v e: Prf (except f v e = Func (DOMAIN f) (λ x, ite (x = v) e (fapply f x)));


// The following operators are useful for representing functions with finite domains by enumeration. They are not part of basic TLA+, but they are
// defined in the TLC module of the standard library.

symbol oneArg: U → U → U;
constant symbol oneArg-def x d e: Prf (Func (x ∈ d) e);

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
 
/*    apply subst (isAFunc ((Func (DOMAIN f) (λ x, ite (x = v) e (fapply f x)))))

    (f = Func (DOMAIN f) (λ x, ite (x = v) e (fapply f x)))

    (λ z, z)

    (isAFunc-def f);*/
    admit;
end;
 

/*
We derive instances of axiom fcnEqual that help in automating proofs about
equality of functions.
*/
opaque symbol funcEqual2 f g :  Prf( isAFunc g )
                                → Prf( isAFunc f )
                                → Prf (DOMAIN f = DOMAIN g)
                                → Prf (bforall (DOMAIN g) (λ x, imp ((fapply f x) = (fapply g x)) (f = g)))
                                ≔
begin
assume f g HgIsFunc HfIsFunc  HDomEqual;
apply funcEqual f g HfIsFunc HgIsFunc HDomEqual;
end;

opaque symbol funcEqualIf f g :  Prf( isAFunc g ) → Prf( isAFunc f ) → Prf (iff (f = g) (and (DOMAIN f = DOMAIN g) (bforall (DOMAIN g) (λ x, (fapply f x) = (fapply g x))))) ≔
begin
    assume f g HfIsFunc HgIsFunc;
    apply iffI (f = g) (and (DOMAIN f = DOMAIN g) (bforall (DOMAIN g) (λ x, fapply f x = fapply g x)))
    {
        assume HEqfg;
        admit;
    }
    {   
        assume H;
        //apply funcEqual f g HfIsFunc HgIsFunc
        //(andD1 _ _  H)
        //(andD2 _ _ H);
        admit;
    };
end;

opaque symbol fcnCong S T e f : Prf (S = T)
                                → Π x, Prf (imp (x ∈ T) (fapply e x = fapply f x))
                                → Prf (Func S (λ x, fapply e x) =  Func T (λ x, fapply f x)) ≔
begin
    assume S T e f  HSeqT x H;
    admit;
end;