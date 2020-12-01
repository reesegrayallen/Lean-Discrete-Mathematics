

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

Here we formalize the syntax of propositional
logic except for variable expressions. That will
come next class.
-/

inductive pExp : Type
| pTrue : pExp
| pFalse : pExp
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
We formalize the "assignment" of a bool meaning
(value) to each well formed expression as a 
*function* from expressions (values of type pExp)
to bool. Here are the rules.
-/
def pEval : pExp → bool
| pTrue := tt 
| pFalse := ff
| (pNot e) := bnot (pEval e)
| (pAnd e1 e2) := band (pEval e1) (pEval e2) 
| (pOr e1 e2) := bor (pEval e1) (pEval e2)
| (pImp e1 e2) := bimp (pEval e1) (pEval e2)


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
