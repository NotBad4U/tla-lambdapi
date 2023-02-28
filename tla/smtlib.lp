require open tla.predicatelogic;
require open tla.settheory;

symbol ⟇: U → U → U;
notation ⟇ infix 1;
rule $x ⟇ $y ↪ or ($x) ($y);

// SMT-lib solver
constant symbol or_simplify p q r : Prf ((p ⟇ q) = r);

constant symbol cong x y f: Prf (x = y) → Prf (f x = f y);

constant symbol not_not x: Prf ((not (not (not x))) ⟇ x);

constant symbol equiv_pos1 x y : Prf (((not (x = y)) ⟇ x) ⟇ ¬ y);

constant symbol equiv_pos2 x y : Prf (((x ≠ y) ⟇ ¬ x) ⟇ y);

constant symbol qnt_cnf_2 p q: Prf (or (¬ (`forall x1, `forall x2, p)) (`forall x1, `forall x2, q));

constant symbol forall_inst_2 p x1 x2: Prf (or (not (`forall a1, `forall a2, p a1 a2)) (p x1 x2));

constant symbol and_pos p q i: Prf ((¬ (and p q)) ⟇ i);

constant symbol and_neg2 p q: Prf (((and p q)) ⟇ ((¬ p) ⟇ (¬ q)));

//TODO verify the rule, in the documentation it is mentionned that there is only one P
constant symbol eq_congruent_pred t1 u1 t2 u2 p1 p2 : Prf (( t1 ≠ u1 ) ⟇ ((t2 ≠ u2) ⟇ ((p1 t1 t2) ⟇ (p2 u1 u2))));

constant symbol bind p q: Π x, Prf (p x = q x) → Prf ((forall p) = (forall q));

constant symbol bind2 p q: Π x y, Prf ((p x y) = (q x y)) → Prf ((`forall a, `forall b, p a b) = (`forall a, `forall b, q a b));

//FIXME: not sure we can prove this one but 
opaque symbol double_negation_elim x: Prf ((not (not x)) = x) ≔
begin
    admit
end;


opaque symbol univ_bounds_or x: Prf (or true x = true) ≔
begin
    assume x;
    simplify;
    apply (orI1 true x);
    apply trivial;  
end;

opaque symbol identity_or_l x: Prf (or false x) → Prf x ≔
begin
    assume x H;
    apply orE false x x H 
    { assume Hfalse; apply absurd x Hfalse; }
    { assume H2; apply H2 }
end;

opaque symbol identity_or_r x: Prf (or x false) → Prf x ≔
begin
    assume x H;
    apply orE x false x H 
    { assume H2; apply H2 }
    { assume Hfalse; apply absurd x Hfalse;} 
end;

rule or $x false ↪ $x;

rule or false $x ↪ $x;

opaque symbol reduction_clause x a b: Prf (or x a) → Prf (or (not x) b) → Prf (or a b) ≔
begin
    assume x a b Hl Hr; 
    apply orE x a (or a b) Hl
    {
        assume Hx;
        apply orE (¬ x) b (or a b) Hr 
        {
           assume Hnotx;
            admit; //TODO
        }
        {
            assume Hb;
            apply orI2 a b Hb
        }
    }
    {
        assume Ha;
        apply orI1 a b Ha
    };
end;

opaque symbol reduction_clause2 x a b: Prf (or a x) → Prf (or b (not x)) → Prf (or a b) ≔
begin
    assume x a b Hl Hr;
    apply orE a x (or a b) Hl
    {
        assume Ha;
        apply orI1 a b Ha
    }
    {
        assume Hx;
        apply orE  b (¬ x) (or a b) Hr
        {
            assume Hb;
            apply orI2 a b Hb
        }
        {
           assume Hnotx; //TODO
            admit;   
        }
    };
end;

opaque symbol reduction_clause' x b: Prf (or x false) → Prf (or (not x) b) → Prf (b) ≔
begin
    admit;
end;

opaque symbol idempotence_or x : Prf (or x x = x) ≔ 
begin
    admit;
end;