import .propositional_logic_syntax_and_semantics

open pExp

/-
This file defines three propositional logic variables
and then defines a list of fundamental rules of logical
reasoning. Most of these rules are valid, but a few are
not. It is a homework assignment to use pEval to prove
that the ones that are valid really are valid, and to
find counter-examples for the ones that are not valid.

The names of all of these rules are important and are 
to be memorized. These rules, which we are to validate
"semantically" (by the method of truth tables) become
the fundamental "inference rules" for reasoning and
constructing proofs *syntactically* when it comes to 
predicate logic.
-/


def P := pVar (var.mk 0)
def Q := pVar (var.mk 1)
def R := pVar (var.mk 2)

def true_intro : pExp := pTrue
def false_elim := pFalse >> P
def true_imp := pTrue >> P
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
def affirm_disjunct := (P ∨ Q) >> (P >> ¬ Q)
def deny_antecedent := (P >> Q) >> (¬ P >> ¬ Q)
