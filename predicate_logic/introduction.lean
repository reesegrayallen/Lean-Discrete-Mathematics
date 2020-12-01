/-

Predicate logic:

(1) Vastly extends concept of domain: can be pretty much anything
- domain no longer just boolean, but can involve objects of any type
- e.g., natural numbers, persons, programs, program states, locations
- variables can now range over objects of any type (e.g., n : ℕ)
- can also refer to *relations*, e.g., =, is_even, is_mother_of, likes
- you've been using predicate logic in limited ways all along in Lean

(2) Language of propositions is extended, in syntax and semantics
- variables can range over objects of arbitrary types
- inherits all logical connectives from propositional logic
- adds ability to use functions to indirectly refer to objects
- adds universal (∀) and existential (∃) quantifiers
- adds predicates to represent properties of and relations among objects
- (predicates are propositions with parameters; give values to get a proposition)
- question of validity is greatly complicated, no longer a fixed domain 

Examples:

- ∀ (n : ℕ), n = 0 ∨ n ≠ 0
- ∀ (n : ℕ), (∃ (m : ℕ), n - m = 0)
- ∀ (p1 : Person), ∀ (p2 : Person), likes p1 p2 -- likes is a relation
- ∀ (p1 : Person), ∃ (p2 : Person), likes p2 p1
- ∃ (p1 : Person), ∀ (p2 : Person), likes p2 p1
- ∃ (p1 : Person), ∀ (p2 : Person), likes p2 p1
- ∃ (p1 : Person), ∀ (p2 : Person), ¬ likes p2 p1
- ∀ (o : Object), madeOfUranium o → relativelyHeavy o -- properties
- ∃ (a b c : ℕ), a^2 + b^2 = c^2                -- the pythagorean predicate
- ∃ (a b c : ℕ), a>0 ∧ b>0 ∧ c>0 ∧ a^2 + b^2 = c^2 -- the pythagorean predicate
- ∃ (a b c : ℕ), pythagorean a b c              -- pythagorean is a relation
- ¬ exist (a b c n: ℕ), a>0 ∧ b>0 ∧ c>0 ∧ n>2 ∧ a^n+b^n=c^n -- Fermat's last theorem



(3) Introduces the concept of *proof* as arbiter of truth
- a proposition is deemed true iff there's a *proof* of it
- this is the fundamental idea underlying all of mathematics
- fundamental question: what then constitutes a correct proof?
- answer: a formal argument from accepted truths (axioms) using
  accepted rules of reasoning (most of which we've already seen!)
  to deduce the conclusion that a given proposition must be true.

Example: 

Conjecture: Assume P and Q are propositions. Prove P ∧ Q → Q ∧ P.

The following quasi-formal proof (written in natural language
but rigorously following formal logical rules of reasoning)
uses predicate logic versions of the rules of and elimination
and and introduction to prove the "conjecture". Reminders:

- P ∧ Q → P         (left and elimination)
- P ∧ Q → Q         (right and elimination)
- X → Y → X ∧ Y     (and introduction)

Strategy: To prove the implication, P ∧ Q → Q ∧ P, we have to 
show that *if we assume* that P ∧ Q is true, which is to say
that we have a proof of it, pq, then from this assumption and
by using only valid rules of logical reasoning, we can deduce
(a better word is "construct") a proof of Q ∧ P.

Proof: Assume that we have a proof, pq, of P ∧ Q. Apply the
left and elimination rule to pq to deduce a proof, p, of P.
Next apply the right and elimination rule to pq to deduce a
proof, q, of Q. Finally, apply the and introduction rule to
q and p, in that order, to construct a proof of Q ∧ P. QED.

This shows that from the *assumption* (or *condition*) that
there is a proof of P ∧ Q one can derive a proof of Q ∧ P. 
Thus is P ∧ Q is true, then Q ∧ P *must* also be true.


Exercise: Prove that if P is true then so is P ∨ Q. That is,
prove P → P ∨ Q. or_intro_left.


Exercise: Prove that P ∧ Q → P ∨ Q.

Exercise: Produce a different but equally good quasi-formal 
proof of this proposition.

Exercise: Prove P ∨ Q → Q ∨ P.


(4) As to deciding whether a putative proof itself is correct,
that is a major problem! In traditional mathematical practice,
deciding whether a proof is correct is a *social* process. The
community of mathematicians reviews purported proofs of major
novel claims and tries to determine whether the proof depends
only on accepted premises and from there correctly applies the
rules of logical reasoning to deduce a proof of the proposition
to be proved. This is in general a difficult, costly, and also
unreliable process, though it remains for the most part the way
that mathematics works in practice.

Consider the famous and controversial putative proof by Mochizuki
of the so-called ABC conjecture. Here's the statement of the ABC
conjecture. For every positive real number ε, there exist only
finitely many triples (a, b, c) of coprime positive integers, with 
a + b = c, such that c > rad(abc)^(1 + ε). It was just announced
that his nearly impenetrable 600-page putative proof of this
profoundly important conjecture will be published, even though
there is very significant concern that the proof contains a
fundamental flaw in reasoning. You can read about it in Nature:
https://www.nature.com/articles/d41586-020-00998-2 (you don't
have to understand the maths to read this article). 

(5) To address this concern, there is an emerging effort among
some mathematicians to formally and automatically *verify* the
correctness of proofs in mathematical logic. Lean is an example
of an automated logic in which this goal is being pursued. Coq
is another example. 

Such systems are based on a rich logic called "type theory", or
constructive, or intuitionistic logic. That's what you are using
in Lean. Such logics are so expressive that we can "implement"
many other logics within them. We have already seen how we can
"embed" propositional logic, including validity checkers and 
satisfiability solvers, in Lean. Going forward we will learn
to reason very precisely in predicate logic by seeing how it
is embedded in Lean. The goal here is not to teach Lean, but
to make the processes of reasoning in predicate logic precise,
and to give you a sense for how such reasoning can be checked
automatically by a proof checker, such as Lean or Coq.

You are responsible for being able to write quasi-formal proofs
of basic propositions in mathematics and in other domains. The
way to learn to do this in this class is to learn the entire set
of rules of reasoning and how to apply them in Lean. One can then
easily write quasi-formal proofs, skipping over obviously correct
details to make for more readable proofs. Of course Mochizuki's
tale highlights the risks of skipping over potentially critical
details!
-/

                            -- sTuCK!