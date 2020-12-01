/-
If you understand the introduction and elimination
rules for ∀, then you understand these rules for
proving, and using proofs of implications. Consider
an implication, P → Q. To construct a proof, pq, of 
P → Q, you simply *assume* you're given an arbitrary
but specific value/proof of P and in this context you
must show that you can construct and return a proof of
Q. What this shows is that *if* P is true (because
there is a proof of it) then so is Q. 

In other words, prove P → Q by showing that you can 
define a total function of type P → Q!

For an example, see the second step (after the ∀
introduction) in our proof of the commutativity of
∨. What's left to prove there is an implication,
P ∨ Q → Q ∨ P. The way it is proved is just the
way that the overall ∀ proposition is proved: by
assuming that we're given a proof/value, but now
of type P ∨ Q, and showing that in this context 
we can construct and return a value of Q ∨ P.

In fact, P ∨ Q is really just a shorthand in Lean
for ∀ (p : P), Q! You can see it clearly in the 
following code, where we first assume that P and 
Q are arbitrary propositions, and then check the
type of ∀ (p : P), Q. It's Prop, of course, as
∀ (p : P), Q is a proposition; but what is key
here is that Lean uses → notation to print out
this proposition! We can even prove that they're
exactly the same proposition.
-/

axioms P Q : Prop
#check ∀ (p : P), Q
example : (P → Q) = ∀ (p : P), Q := rfl 

/-
Of course it's now obvious that the elimination
rule for → is the same as it is for ∀: *apply* a 
proof of P → Q to a proof of P to obtain a proof
of Q.
-/

theorem modus_ponens: 
    (P → Q) →  
    P →                  
    Q :=
λ (pq : P → Q), -- suppose you have a proof of P → Q
λ (p : P),      -- and that you have a proof of P 
pq p            -- *apply* former to latter; QED.