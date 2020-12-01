/-
REESE ALLEN (rga2uz)
-/

import .satisfiability
import .rules_of_reasoning

/-
CS2102 Exam #2: Propositional Logic
-/

/-
#1. Define a predicate function, is_satisfiable: pExp → bool
that returns true iff the given proposition is satisfiable.
Hint: Model your answer on our definition of is_valid. You
may need to define one or more helper functions. You should
test your solution, but we will only grade your definition.
Please write test cases in a separate file. Do not submit
that file.
-/

-- both of these helper functions do the same thing
def contains_tt : list bool → bool
| [] := ff
| (list.cons tt l) := tt
| (list.cons b l) := contains_tt l

def foldr_or : list bool → bool
| [] := ff
| (list.cons h t) := bor h (foldr_or t)


def is_satisfiable (e : pExp) : bool :=
    let n := number_of_variables_in_expression e in 
    let is := interpretations_for_n_vars n in
    let rs := map_pEval_over_interps e is in 
    foldr_or rs


/-
#2. Clearly the propositions in rules_of_reasoning.lean that
are valid are also satisfiable. But what about the following?
Apply your satisfiability predicate function to decide whether
or not each of the following formulae is satisfiable or not.
Write an "#eval is_satisfiable e" command for each expression.

A. The "fallacies" in that file (the ones that aren't valid). 

B. The proposition, pFalse.

C. The following propositions:
1. P ∧ ¬ P
2. P ∨ ¬ P
3. (¬x1 ∨ x2) ∧ (¬x2 ∨ x3 ∨ ¬x4) ∧ (x1 ∨ x2 ∨ x3 ∨ ¬x4)

Note that for 3. you will have to define four new variables.
Call them x1, x2, x3, and x4.
-/

open pExp

-- A.
#eval is_satisfiable affirm_consequence -- tt
#eval is_satisfiable affirm_disjunct -- tt
#eval is_satisfiable deny_antecedent -- tt

-- B.
#eval is_satisfiable pFalse -- ff
def false_intro : pExp := pFalse
#eval is_satisfiable false_intro -- ff

-- C.
def x1 := pVar (var.mk 0)
def x2 := pVar (var.mk 1)
def x3 := pVar (var.mk 2)
def x4 := pVar (var.mk 3)

#eval is_satisfiable (P ∧ ¬ P) -- ff 
#eval is_satisfiable (P ∨ ¬ P) -- tt
#eval is_satisfiable ((¬x1 ∨ x2) ∧ (¬x2 ∨ x3 ∨ ¬x4) ∧ (x1 ∨ x2 ∨ x3 ∨ ¬x4)) -- tt


def e1 := P ∧ ¬ P
def e2 := P ∨ ¬ P
def e3 := (¬x1 ∨ x2) ∧ (¬x2 ∨ x3 ∨ ¬x4) ∧ (x1 ∨ x2 ∨ x3 ∨ ¬x4)

#eval is_satisfiable e1 -- ff
#eval is_satisfiable e2 -- tt
#eval is_satisfiable e3 -- tt


/-
3. In the previous problems, you defined a satisfiability
predicate function that returns true or false depending on
whether a given formula is satisfiable or not. Often we will
want to know not only whether there exists a solution but an
actual example of a solution, if there is one. 

Define a function
called sat_solver : pExp → option (var → bool) that returns a
satisfying interpretation (as "some interpretation") if there
is one, or "none" otherwise. Hint: Model your solution on our
validity checker. First compute the list of interpretations for
a given expression, e, then reduce that list to a value of type
option (var → bool). Evaluate e under each interpretation in 
the list until either (A) you find one, call it i, for which e
evaluates to true, or until you reach the empty list, empty
handed. 
-/

def sat_helper : pExp → list (var → bool) → option(var → bool)
| e [] := option.none 
| e (h::t) := match pEval e h with
            | tt := option.some h
            | ff := sat_helper e t
            end

def sat_solver (e : pExp) : option (var → bool) :=
    let n := number_of_variables_in_expression e in 
    let is := interpretations_for_n_vars n in
    sat_helper e is 


/-
4. Define a predicate function, is_unsatisfiable : pExp → bool,
that takes a propositional logic formula, e, and returns true
iff e is unsatisfiable. Hint: Easy. Build on what you have.
-/

def is_unsatisfiable (e : pExp) : bool :=
    let tf := is_satisfiable e in 
    (match tf with 
    | ff := tt
    | tt := ff
    end)
    
/-
5. Given a propositional logic expression, e, and an incorrect
claim that it's valid, we often want to produce a counter-example
to that claim. Such a counter example is an interpretation under
which the expression is not true. Equivalently, a counterexample
is an interpretation under which the *negation* of the expression
*is* true. 

Define a function, counterexample : pExp → option (var → bool),
that takes any expression e and returns either a counterexample
(as "some interpretation") or "none" if there isn't one. Hint:
given e, try to find a model for the expression, ¬ e.
-/

/- you can either 1. iterate over the list of interpretations for a given
expression until finding an interpretation i for which the expression is false 
and return option(i) otherwise none, OR 2. negate the expression and iterate 
over a list of intepretations until finding one i for which ¬ expression 
is true and return option(i) otherwise none  -- both of these should lead
to the same return value
-/

def counter_helper : pExp → list (var → bool) → option(var → bool)
| e [] := option.none 
| e (h::t) := match pEval e h with
            | ff := option.some h
            | tt := counter_helper e t
            end

def counterexample (e : pExp) : option (var → bool) :=
    let n := number_of_variables_in_expression e in 
    let is := interpretations_for_n_vars n in
    counter_helper e is 


/-
6. Give an English language example for every valid rule of
reasoning in rules_of_reasoning.lean, and also give an English
language counter-example for each fallacy.

For example, for the rule, P >> Q >> P ∧ Q, you could say,
"If the ball is red then if (in addition to that) the box
is blue, then (in this context) the ball is red AND the box
is blue." It will be easiest is you re-use the same words
for P, Q, and R, in all of your examples. E.g., P means "the
ball is red", Q means "the box is blue", etc.

Copy the contents of rules_of_reasoning.lean into this comment
block and under each rule give your English language sentence.


def true_intro : pExp := pTrue
One water molecule is composed of two hydrogen atoms and one oxygen atom.
-- statement that is objectively/ always true 

def false_elim := pFalse >> P
If it is true that his leg is broken, then we walks with a limp

def true_imp := pTrue >> P
If his leg is broken, then he walks with a limp.
-- If it is objectively/ always true that his leg is broken, and he 
walks with a limp, then the implication is true. If he does not walk with
a limp, then the implication is false.

def and_intro := P >> Q >> P ∧ Q
If we assume his leg is broken, then, in addition, we assume he walks with 
a limp, then, in this context, his leg is broken and he walks with a limp

def and_elim_left := P ∧ Q >> P
If we assume that his leg is broken and he walks with a limp, then it must
be true that his leg is broken.

def and_elim_right := P ∧ Q >> Q
If we assume that his leg is broken and he walks with a limp, then it must
be true that he walks with a limp.

def or_intro_left := P >> P ∨ Q
If we waasume that his leg is broken, then it it must be true that his leg
is broken or he walks with a limp

def or_intro_right := Q >> P ∨ Q
If we assume that he walks with a limp, then it must be true that his leg
is broken or we walks with a limp.

def or_elim := P ∨ Q >> (P >> R) >> (Q >> R) >> R
If we assume that it is true that he walks with a limp or his leg is broken,
then, in addition to that, we assume it is true that his leg being broken
means that he is in pain, then, in addition to that, we assume him 
walking with a limp means he is in pain, we can deduce that he is in pain.

def iff_intro := (P >> Q) >> (Q >> P) >> (P ↔ Q)
If his leg is broken, then he walks with a limp, and, in additon to that, if 
he walks with a limp his leg is broken, then we can deduce that his leg is 
broken if and only if he walks with a limp.

def iff_intro' := (P >> Q) ∧ (Q >> P) >> (P ↔ Q)
If we assume that his leg is broken, then he walks with a limp, and 
we assume that if he walks with a limp, then his leg is broken, it must be 
true that his leg is broken if and only if he walks with a limp.

def iff_elim_left := (P ↔ Q) >> (P >> Q)
If we assume that his leg is broken if and only if he walks with a limp, then
it must be true that, if we assume his leg is broken, he walks with a limp.

def iff_elim_right := (P ↔ Q) >> (Q >> P)
If we assume that his leg is broken if and only if he walks with a limp, then
it must be true that, if we assume he walks with a limp, his leg is broken

def arrow_elim := (P >> Q) >> (P >> Q)
If we assume that if his leg is broken, then he walks with a limp, then
it must be true that if we assume his leg is broken, he walks with a limp.

def resolution := (P ∨ Q) >> (¬ Q ∨ R) >> (P ∨ R)
If we assume that his leg is broken or he walks with a limp, and, in 
addition to that, if we assume that his leg s not broken or he is in pain, 
then it must be true that his leg is broken or he is in pain.

def unit_resolution := (P ∨ Q) >> ((¬ Q) >> P)
If we assume that his leg is broken or he he walks with a limp, then we can
deduce that, assuming his leg is not broken, it must be true he walks with a limp.

def syllogism := (P >> Q) >> (Q >> R) >> (P >> R)
If we assume his leg being broken means that he walks with a limp, and in 
addition to that we assume that him walking with a limp means he is in pain,
then it must be true that his leg being broken means he is in pain.

def modus_tollens := (P >> Q) >> (¬ Q >> ¬ P)
If his leg being broken means that he is in pain, then it must be true 
that him not being in pain means that his leg is not broken.

def neg_elim := (¬ ¬ P) >> P
If it is not true that his leg his not broken, then it must be true that
his leg is broken.

def excluded_middle := P ∨ (¬ P)
His leg is broken or his leg is not broken.

def neg_intro := (P >> pFalse) >> (¬ P)
If we assume that his leg being broken is false, then it must be true that
his leg is not broken.

def affirm_consequence := (P >> Q) >> (Q >> P)
If he walks with a limp, then his leg is broken; therefore, if his leg
is broken, he walks with a limp. F

def affirm_disjunct := (P ∨ Q) >> (P >> ¬ Q)
If we assume that his leg is broken or he walks with a limp, then it must 
be true that his leg being broken means he walks with a limp. F

def deny_antecedent := (P >> Q) >> (¬ P >> ¬ Q)
If we assume that his leg not being broken implies that he walks with a limp,
then it must be true that his leg being broken means he does not walk
with a limp. F

-/