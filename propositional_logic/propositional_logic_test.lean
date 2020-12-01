import .propositional_logic_syntax_and_semantics

open pExp

-- some "variables" (of type var)
def P_var := var.mk 0
def Q_var := var.mk 1
def R_var := var.mk 2
#check P_var

-- some variable expressions (of type pExp)
def P := pVar P_var
def Q := pVar Q_var
def R := pVar R_var

-- confirming that we can build larger expresions
#check P
#check pAnd P Q         -- P ∧ Q
#check pOr Q (pNot R)   -- Q ∨ (¬ P)

-- confirming we can use our traditional notation!
#check P ∧ Q 
#check P ∨ Q
#check ¬ P
#check P > Q
#check P ↔ Q
#check P ⊕ Q 


-- all four possible interpretations for two variables
def interp_all_false : var → bool
| _ := ff

def interp_all_true : var → bool
| _ := tt

def tt_ff_interp : var → bool
| (var.mk 0) := tt      -- P_var
| (var.mk 1) := ff      -- Q_var
| _ := ff

def ff_tt_interp : var → bool
| (var.mk 0) := ff      -- P_var
| (var.mk 1) := tt      -- Q_var
| _ := ff


-- evaluating expressions written as abstract syntax trees
#eval pEval P interp_all_false
#eval pEval P interp_all_true
#eval pEval (pOr (pAnd P Q) R)    -- (P ∧ Q) ∨ R

-- but now we can write them using standard notation
#eval pEval ((P ∧ Q) ∨ R) interp_all_false
#eval pEval ((P ∧ Q) ∨ R) interp_all_true
#eval pEval ((P ∧ Q) ∨ R) interp_all_false

-- An expression from last class
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

-- rewritting using standard logical notation
#check ((P ∨ Q) ∧ (P ∧ Q))


-- Evaluated under all for possible interpretations

#eval pEval ((P ∨ Q) ∧ (P ∧ Q)) interp_all_true
#eval pEval ((P ∨ Q) ∧ (P ∧ Q)) tt_ff_interp
#eval pEval ((P ∨ Q) ∧ (P ∧ Q)) ff_tt_interp
#eval pEval ((P ∨ Q) ∧ (P ∧ Q)) interp_all_false

-- Yielding a truth table for this expression! 

-- P     Q     (P ∨ Q) ∧ (P ∧ Q)
-- tt    tt         tt
-- tt    ff         ff
-- ff    tt         ff
-- ff    ff         ff

/-
Each row of the truth table corresponds to an
interpretation, and the value in the last column 
of each row is the meaning of the given expression 
under the interpretation specified by that row. 
-/

/-
The best algorithms that we have today have to 
compute and search the entire truth table before
determining whether an expression is satisfiable
or not. If there are N variables, the number of
interpretations (rows in the corresponding truth
table) is 2^N.

It's easy to compute the value of an expression
under any particular interpretation, but in the
worst case, it's exponentially hard to *search*
for such a satisfying solution -- at least today.

The biggest open question in computer science is
whether there exists an algorithm with better 
than worst-case exponential time complexity for
deciding whether an arbitrary propositional logic
formula is satisfiable or not.

The question is usually posed by asking whether
two classes of problems, P and NP, are equal or
not. The question is thus usually phrased, does
P = NP? If you want to go down in history, solve
this problem. Many brilliant minds have tried to
no avail. 
-/
