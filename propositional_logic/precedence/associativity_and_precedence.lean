import .propositional_logic_syntax_and_semantics

open pExp

-- left associative
-- associative
#check 2 + 3 + 4
#check (2 + 3) + 4
#check 2 + (3 + 4) 
#eval 2 + 3 + 4
#eval (2 + 3) + 4
#eval 2 + (3 + 4) 

-- - is left associative
-- - is not associative
#check 5 - 3 - 1
#check 5 - (3 - 1)
#check (5 - 3) - 1
#eval (5 - 3) - 1
#eval 5 - (3 - 1)

-- precedence, bind strenth
#check 3 * 4 + 5
#check (3 * 4) + 5
#check 3 * (4 + 5)
#eval (3 * 4) + 5
#eval 3 * (4 + 5)

/-
Motivation: Can't overlad →. First
attempt at a solution: overload >
to mean pImp, as follows.

notation e1 > e2 := pImp e1 e2 

Problem: > is a reserved notation
in Lean. We can overload it but we
cannot change either is precedence
or its associativity. The notation
is thus non-standard and confusing.
-/

def P := pVar (var.mk 0)
def Q := pVar (var.mk 1)
def R := pVar (var.mk 2)

-- associativity is wrong
-- left associative X
#check P > Q > R
#check P > (Q > R)
#check (P > Q) > R

#check nat → nat → nat
#check nat → (nat → nat)
#check (nat → nat) → nat

-- associativity is wrong
#check P ∧ Q > Q > R 
#check (P ∧ Q) > (Q > R) 
#check P ∧ (Q > Q) > R 

-- precedence is wrong, too
#check P ∨ Q > Q > R 
#check (P ∨ Q) > (Q > R)
#check P ∨ (Q > Q) > R 

#check P ∧ Q > Q > R 
#check (P ∧ Q) > (Q > R)
#check P ∧ (Q > Q) > R 

#check P > Q ↔ Q > P
#check (P > Q) ↔ (Q > P)


/-
Solution: Define our own infix operator
with appropriate precedence (also called)
binding strength.

First, let's see where the other reserved
operators that we're using (such as ∧ and 
∨) get their binding strengths: from one of
Lean's libraries. Here's what appears there
(some details omitted).

/-
/- Logical operations and relations -/

reserve prefix `¬`:40
reserve prefix `~`:40
reserve infixr ` ∧ `:35
reserve infixr ` /\ `:35
reserve infixr ` \/ `:30
reserve infixr ` ∨ `:30
reserve infix ` <-> `:20
reserve infix ` ↔ `:20
reserve infix ` = `:50
reserve infix ` == `:50
reserve infix ` ≠ `:50
reserve infix ` ≈ `:50
reserve infix ` ~ `:50
reserve infix ` ≡ `:50
reserve infixl ` ⬝ `:75
reserve infixr ` ▸ `:75
reserve infixr ` ▹ `:75

/- arithmetic operations -/

reserve infixl ` + `:65
reserve infixl ` - `:65
reserve infixl ` * `:70
reserve infixl ` / `:70
reserve infixl ` % `:70
reserve prefix `-`:100
reserve infixr ` ^ `:80

reserve infixr ` ∘ `:90                 -- input with \comp

reserve infix ` <= `:50
reserve infix ` ≤ `:50
reserve infix ` < `:50
reserve infix ` >= `:50
reserve infix ` ≥ `:50
reserve infix ` > `:50

/- boolean operations -/

reserve infixl ` && `:70
reserve infixl ` || `:65
-/
-/


-- Here's our new notation

infixr ` >> ` : 25 := pImp 

-- associativity is correct
#check P >> Q >> R
#check P >> (Q >> R)
#check (P >> Q) >> R

-- precedence is (almost) correct
#check P ∧ Q >> Q >> R 
#check (P ∧ Q >> Q) >> R 
#check (P ∧ Q) >> (Q >> R) 
#check P ∧ (Q >> Q) >> R 

#check P ∨ Q >> Q >> R 
#check P ∨ Q >> (Q >> R)
#check P ∨ (Q >> (Q >> R)) --uh oh, another bug!
#check (P ∨ Q) >> (Q >> R)

/-
What is wrong?
How to fix it?
-/

#check (P ∨ Q) >> (Q >> R)
#check (P ∨ Q) >> Q >> R

axioms X Y Z : Prop
#check X ∨ Y → Y → Z
#check X ∨ Y → (Y → Z)

#check (P ∨ Q) >> Q >> R
#check P ∨ (Q >> Q) >> R 

#check P ∧ Q >> Q >> R 
#check (P ∧ Q) >> (Q >> R)
#check P ∧ (Q >> Q) >> R 

#check P >> Q ↔ Q >> P
#check (P >> Q) ↔ (Q >> P)

