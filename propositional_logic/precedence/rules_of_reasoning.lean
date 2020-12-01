--import .prop_logic 
import .propositional_logic_syntax_and_semantics


open pExp


/-
Here are three propositional variables,
P, Q, and R.
-/

def P := pVar (var.mk 0)
def Q := pVar (var.mk 1)
def R := pVar (var.mk 2)

/-
Below are 20+ formulae in propositional
logic. Your job is to classify each as
valid or not valid. To do this you will
produe a truth table for each one. It is
good that we have an automatic evaluator
as that makes the job easy. For each of
the formulae that is not valid, give an
English language counterexample: some 
scenario that shows that the formula is
not always true. 

To do this assignment, produce a truth table
for each formula and use the result to tell 
if a formula is valid or not. Remember that
each row of a truth table corresponds to one
interpretation and gives the value of such a
formula under that specific interpretation. 

Some of the formulae contain only one variable.
We will always use P in these cases. You will
need two interpretations in these cases. Call
them Pt and Pf. Some formula have two variables,
P and Q. You will need four interpretations in
these cases. Call them PtQt, PtQf, etc. Finally
some formula use three variables. Call the
interpretations for these cases PtQtRt, etc.

Define your interpretations, for formulae with
one, two, and three variables, respectively, here. 
-/

-- Answer


/-
Beneath each formula, below, evaluate it under 
each of its possible interpretations. Hint: use
pEval!

The results will tell you whether the formula
is valid or  not. It'll also tell you under 
which of the interpretations, if any, it is
not true.

From the results, you can then decide whether
each formula is valid or not. 
-/

def true_intro : pExp := pTrue

-- truth table here (some number of pEvals)
-- classification here (valid or not)

def false_elim := pFalse >> P
-- answer here

#eval pEval false_elim _
#eval pEval false_elim _

def true_imp := pTrue >> P
-- etc

def and_intro := P >> Q >> P ∧ Q

def and_elim_left := P ∧ Q >> P

def and_elim_right := P ∧ Q >> Q

def or_intro_left := P >> P ∨ Q

def or_intro_right := Q >> P ∨ Q

def or_elim := P ∨ Q >> (P >> R) >> (Q >> R) >> R

def iff_intro := (P >> Q) >> (Q >> P) >> (P ↔ Q)

def iff_intro' := (P >> Q) ∧ (Q >> P) >> (P ↔ Q)

def iff_elim_left := (P ↔ Q) >> (P >> Q)

def iff_elim_right := (P ↔ Q) >> (Q >> P)

def arrow_elim := (P >> Q) >> (P >> Q)

def resolution := (P ∨ Q) >> (¬ Q ∨ R) >> (P ∨ R)

def unit_resolution := (P ∨ Q) >> ((¬ Q) >> P)

def syllogism := (P >> Q) >> (Q >> R) >> (P >> R)

def modus_tollens := (P >> Q) >> (¬ Q >> ¬ P)

def neg_elim := (¬ ¬ P) >> P

def excluded_middle := P ∨ (¬ P)

def neg_intro := (P >> pFalse) >> (¬ P)

def affirm_consequence := (P >> Q) >> (Q >> P)
-- fallacy
/-
Counterexample. Just because I know that if it's raining the streets are wet,
I don't necessarily know that if the streets wet it's raining, because there
could be other causes for the street to be wet.
-/

def affirm_disjunct := (P ∨ Q) >> (P >> ¬ Q)

def deny_antecedent := (P >> Q) >> (¬ P >> ¬ Q)
axioms A B : Prop

#check A ∨ B ∧ B ∨ A
#check (A ∨ B) ∧ (B ∨ A)
#check A ∨ (B ∧ B) ∨ A

#check  A ∨ B → B ∨ A
#check  (A ∨ B) → (B ∨ A)
#check A ∨ (B → B) ∨ A

#check A → B ↔ B → A 
#check (A → B) ↔ (B → A) 
#check A → (B ↔ B) → A

#check  A ↔ B ∨ B ↔ A
#check  (A ↔ B) ∨ (B ↔ A)
#check  A ↔ (B ∨ B) ↔ A

#check A → B ∨ B → A
#check (A → B) ∨ (B → A)
#check A → (B ∨ B) → A


/-
Study the valid rules and learn their names. 
These rules, which, here, we are validating 
"semantically" (by the method of truth tables)
will become fundamental "rules of inference",
for reasoning "syntactically" when we get to 
predicate logic. There is not much memorizing
in this class, but this is one case where you
will find it important to learn the names and
definitions of these rules.
-/