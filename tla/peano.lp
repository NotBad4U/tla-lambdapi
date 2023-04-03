require open tla.predicatelogic;
require open tla.settheory;
require open tla.function;
require open tla.fixedpoints;


symbol ExtendedPeano: U → U → U → U → U → U;

constant symbol ExtendedPeano-def I N Z sc cp: Prf (
    (ExtendedPeano I N Z sc cp) =
    (Z ∈ N
    ∧ (sc ∈ FuncSet N N)
    ∧ (bforall N  (λ n,  fapply sc n ≠ Z))
    ∧  (bforall N (λ n,  bforall N (λ m, imp (fapply sc n = fapply sc m) (m = n))))
    ∧  (bforall (subset N) (λ S, imp  (Z ∈ S  ∧  (bforall S  (λ n, fapply sc n ∈ S ))) (N ⊆ S)))
    ∧ (cp ∈ FuncSet I I)
    ∧ I = N ∪ (setOfAll cp (λ n, n ∈ N))
    ∧ (fapply cp Z = Z)
    ∧ (bforall N  (λ k, imp (fapply cp k ∈ N) k = Z))
    ∧  (bforall I (λ k,  bforall I (λ l, imp (fapply cp k = fapply cp l) (k = l))))
    ∧ (bforall I  (λ k, fapply cp (fapply cp k) = k)))
);

symbol Succ: U;
constant symbol Succ-def: Prf( Succ = (`choose sc, `exists cp, `exists I, `exists N, `exists Z, ExtendedPeano I N Z sc cp));

symbol Nat: U;
constant symbol Nat-def: Prf (Nat = (DOMAIN Succ));

symbol zero: U;
constant symbol zero-def: Prf (zero = `choose Z, `exists cp, `exists I, ExtendedPeano I Nat Z Succ cp);

symbol intCplt: U;
constant symbol intCplt-def: Prf (intCplt = `choose cp, `exists I, ExtendedPeano I Nat zero Succ cp);


symbol Int: U;
constant symbol Int-def: Prf (Int = (DOMAIN intCplt));

symbol minus: U → U;

symbol -: U → U;
notation - prefix 2;
rule - $x ↪ minus $x;

symbol minus-def z : Prf (- z = (fapply intCplt z));