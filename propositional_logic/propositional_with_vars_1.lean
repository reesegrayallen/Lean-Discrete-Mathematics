

/-
Propositional logic.
-/

/-
Propositions.

P: Kevin Is at Home.
Q: It's warm outside.

If P and Q are propositions, then so are 

- not P
- P and Q
- P or Q
- P implies Q
-/

/-
Syntax -- defines set of well formed expressions.
We formalize syntax as an inductive data type.
Expressions are then just values of this type.
-/

inductive var : Type
| mk : ℕ → var

def V_0 := var.mk 0
def V_1 := var.mk 1
def V_2 := var.mk 2
-- variables indexed by natural numbers

open var

inductive pExp : Type
| pTrue : pExp
| pFalse : pExp
| pVar : var → pExp
| pNot : pExp → pExp
| pAnd : pExp → pExp → pExp
| pOr : pExp → pExp → pExp
| pImp : pExp → pExp → pExp

open pExp

/-
Semantics -- what does each such expression mean?
The semantics of propositional logic assigns a 
Boolean truth value to each well formed expression. 
Moreover, it does this in a "compositional" manner. 
What that means is that the meaning of a "larger"
expression is defined by "composing"", using Boolean
operators, the meaning(s) of the smaller expression(s)
from which it is constructed.  
-/

/-
Recall how we define Boolean operators.
-/

-- implies
def bimp : bool → bool → bool
| tt tt := tt
| tt ff := ff
| ff tt := tt
| ff ff := tt

/-
An interpretation is a mapping,
i.e., a function, from variables 
to Boolean "meanings" (values)
-/

def interp_all_false : var → bool
| _ := ff


/-
We formalize the "assignment" of a bool meaning
(value) to each well formed expression as a 
*function* from expressions (values of type pExp)
to bool. Here are the rules.
-/
def pEval : pExp → (var → bool) → bool
| pTrue _ := tt 
| pFalse _ := ff
| (pVar v) i := i v
| (pNot e) i := bnot (pEval e i)
| (pAnd e1 e2) i := band (pEval e1 i) (pEval e2 i) 
| (pOr e1 e2) i := bor (pEval e1 i) (pEval e2 i)
| (pImp e1 e2) i := bimp (pEval e1 i) (pEval e2 i)

-- P ↔ Q
-- iff, equivalent
-- tt tt tt
-- ff ff tt
--       ff


/-
Examples
-/
#eval pEval pTrue
#eval pEval pFalse
#eval pEval (pNot pTrue)
#eval pEval (pNot pFalse)

def p1 := pTrue
def p2 := pFalse
def p25 := pNot p2
def p3 := pAnd pTrue pFalse
def p4 := pOr p3 p2

#eval pEval p3
#eval pEval p4
#eval pEval (pImp p3 p4)

-- Variable expressions

def P := V_0
def Q := V_1
def R := V_2

def p5 := pVar P
def p6 := pOr (pVar P) (pVar Q)
def p7 := pAnd 
            (pOr (pVar P) (pVar Q)) 
            (pNot (pVar Q))
-- (P ∨ Q) ∧ (¬Q)

#eval pEval p7 interp_all_false

def interp_makes_p7_true : var → bool
| (var.mk 0) := ff       -- P
| (var.mk 1) := ff       -- Q
| (var.mk 2) := ff       -- R
| (var.mk _) := ff

#eval pEval p7 interp_makes_p7_true

-- Boolean satisfiability

-- Satisfiable: has some interpretation true

-- Unsatisfiable: no interpretation makes true
-- pFalse
-- P ∧ ¬ P

-- Valid: under every interpretation it's true
-- pTrue
-- P ∨ ¬ P

-- Satisfiable but not valid
-- P

/- 
Problem of Boolean satisfiability: Given
a proposition in propositional logic, or 
equivalently a Boolean expression, *find* 
an interpretation, if there is one, under
which that expression is true. 
-/

/-
Example:

(P ∧ Q) → (Q ∧ P)   -- VALID

¬ (P ∧ Q) → (¬ P) ∨ (¬ Q)   -- DeMorgan Laws
¬ (P ∨ Q) → (¬ P) ∧ (¬ Q)   -- DeMorgan Laws 

-/