require open tla.predicatelogic;
require open tla.settheory;

// SMT-lib solver
constant symbol or_simplify p q r : Prf ((or p q) = r);

constant symbol cong x y f: Prf (x = y) → Prf (f x = f y);

constant symbol not_not x: Prf (or (not (not (not x))) x);

constant symbol equiv_pos1 x y : Prf (or (or (not (x = y)) x) (¬ y));

constant symbol equiv_pos2 x y : Prf (or (or (not (x = y)) (not x)) y);

constant symbol qnt_cnf_2 p q: Prf (or (¬ (`forall x1, `forall x2, p)) (`forall x1, `forall x2, q));

constant symbol forall_inst_2 p x1 x2: Prf (or (not (`forall a1, `forall a2, p a1 a2)) (p x1 x2));

constant symbol and_pos p q i: Prf (or (¬ (and p q)) i);

constant symbol and_neg2 p q: Prf (or ((and p q)) (or (¬ p) (¬ q)));

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

opaque symbol reduction_clause x a b: Prf (or x a) → Prf (or (not x) b) → Prf (or a b) ≔
begin
    assume x a b Hl Hr; 
    admit;
end;

opaque symbol reduction_clause2 x a b: Prf (or a x) → Prf (or b (not x)) → Prf (or a b) ≔
begin
    admit;
end;

opaque symbol reduction_clause' x b: Prf (or x false) → Prf (or (not x) b) → Prf (b) ≔
begin
    admit;
end;

opaque symbol idempotence_or x : Prf (or x x = x) ≔ 
begin
    admit;
end;

