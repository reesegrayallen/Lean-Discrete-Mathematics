

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

/-
inductive var : Type
| P
| Q
| R
-/

inductive var : Type
| mk : ℕ → var

def P_var := var.mk 0
def Q_var := var.mk 1
def R_var := var.mk 2
def V_3 := var.mk 4 --etc


inductive pExp : Type
| pTrue : pExp
| pFalse : pExp
| pVar : var → pExp
| pNot : pExp → pExp
| pAnd : pExp → pExp → pExp
| pOr : pExp → pExp → pExp
| pImp : pExp → pExp → pExp
| pIff : pExp → pExp → pExp

open pExp

-- Here are some variable expressions
--
def P := pVar P_var        -- pVar (var.mk 0) 
def Q := pVar Q_var        -- pVar Q_var
def R := pVar R_var        -- pVar R_var



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
We formalize the "assignment" of a bool meaning
(value) to each well formed expression as a 
*function* from expressions (values of type pExp)
to bool. We will then be able to evaluate a
propositional logic expression that includes
variables, as long as an interpretation (such a
function) is provided, so that we can determine
the Boolean meaning of each variable "under that
particular interpretation." We will thus have to
add an interpretation (pExp → bool) argument to
our pEval function.
-/

-- Here are a few different interpretations

def interp_all_false : var → bool
| _ := ff

def interp_all_true : var → bool
| _ := tt


-- Here's our extended semantic evaluator
def pEval : pExp → (var → bool) → bool
| pTrue _ := tt 
| pFalse _ := ff
| (pVar v) i := i v
| (pNot e) i := bnot (pEval e i)
| (pAnd e1 e2) i := band (pEval e1 i) (pEval e2 i) 
| (pOr e1 e2) i := bor (pEval e1 i) (pEval e2 i)
| (pImp e1 e2) i := bimp (pEval e1 i) (pEval e2 i)
| (pIff e1 e2) i := tt  --stubbed out


/-
Notation is just "syntactic sugar!"
-/
notation e1 ∧ e2 :=  pAnd e1 e2
notation e1 ∨ e2 :=  pOr e1 e2
notation ¬ e := pNot e
notation e1 > e2 := pImp e1 e2
notation e1 ↔ e2 := pIff e1 e2


#eval pEval P interp_all_false
#eval pEval P interp_all_true

#eval pEval Q
#eval pEval R

#eval pEval (pOr (pAnd P Q) R)    -- (P ∧ Q) ∨ R
#eval pEval (pAnd    
                (pOr 
                    P
                    Q
                )
                (pAnd
                    P 
                    Q
                )
            )
            interp_all_true


def lots_of_fun := pAnd (pOr P Q) (pNot P)

def sat : var → bool
| (var.mk 0) := ff       -- P_var
| (var.mk 1) := tt       -- Q_var
| (var.mk _) := ff       -- otherwise



#eval pEval lots_of_fun sat

-- We have found a *satisfying solution*
-- An interpretation that makes an expression true!

-- A problem that has a solution is said to be *satisfiable*
-- A problem that has no solution is said be *unsatisfiable*
-- A problem for which every interp is a solution is said to be *valid*
-- Satisfiable but not valid


-- pAnd P (pNot P)  -- P ∧ ¬ P      -- never true
-- pOr P (pNot P)   -- P ∨ ¬ P

/-
Proof by case analysis
- P=true: true ∨ false = true
- P=false: false ∨ true = true
-/


/- VALID RULES OF REASON

-- 
(P ∧ Q) → (Q ∧ P)
¬ (P ∧ Q) → (¬ P) ∨ (¬ Q)
¬ (P ∨ Q) → (¬ P ∧ ¬ Q)

-- not valid
(P → Q) → (Q → P)
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
