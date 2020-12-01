/-
If P and Q are arbitrary propositions, then to prove 
P ∨ Q, you need to prove either P or Q and then use
one of the or introduction rules to form a proof of
the disjunction. 
-/

-- Suppose P and Q are arbitrary propositions
axioms (P Q : Prop)

-- Suppose you have proofs of P and of Q
axioms (p : P) (q : Q)

-- You can now construct proofs of P ∨ Q

#check or.intro_left Q p
#check or.intro_right P q

/-
If the type of the disjunction for which a
proof is not provided can be inferred then
the shorthand form of these rules can be
used.
-/

example : P ∨ Q := or.inl p
example : P ∨ Q := or.inr q

/-
The elimination rule for using a proof of
a disjunction requires a case analysis. If
you have a proof of P ∨ Q, and you can show
that P → R and Q → R, then you've shown that
R is true *in either case* (whether P ∨ Q is
true because P is or because Q is).
-/

axioms Raining Sprinkler StreetsWet: Prop
axiom rw : Raining → StreetsWet

example : (Raining ∨ Sprinkler) → 
          (Raining → StreetsWet) → 
          (Sprinkler → StreetsWet) → 
          StreetsWet :=
λ (rors : Raining ∨ Sprinkler), -- if you assume R ∨ S
λ (rw : Raining → StreetsWet),   -- and you can prove R→W
λ (sw : Sprinkler → StreetsWet), -- and also S→W
   match rors with  -- then you can prove W "by case analysis"
    | or.inl r := rw r  -- if it's raining the streets are wet
    | or.inr s := sw s  -- if the sprinker's on, they're wet
   end                  -- so they're wet in either case QED.