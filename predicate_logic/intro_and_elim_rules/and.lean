/-
If P and Q are arbitrary propositions, then to prove 
P ∧ Q, you need to prove P and to prove Q and then to
form the pair of these proofs to construct a proof of
P ∧ Q. 
-/

-- Suppose P and Q are arbitrary propositions
axioms (P Q : Prop)

-- Suppose you have proofs of P and of Q
axioms (p : P) (q : Q)

-- You can now construct a proof of P ∧ Q

#check and.intro p q


/- 
Note: Lean provides a nice notation for
and.intro. Use backslash left and right
angle brackets. This notation emphasizes
that a proof of a conjunctions is formed
as a pair of proofs.
-/
lemma pq : P ∧ Q := ⟨ p, q ⟩ 

/-
The elimination rules for and allow you
to deduce from a proof of P ∧ Q that there
is a proof of P and a proof of Q.
-/

#check pq.left
#check pq.right