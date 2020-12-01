/-
If P is an arbitrary proposition, then the 
negation introduction rule tells you how to
prove ¬P. You do it by showing that P → false.

In English, you do it by *assuming* that P is
true and then *showing* that that leads to a
contradiction from which a proof of false can
be obtained. Because there is no proof of 
false, the assumption that P is true has to
be wrong, so there must be no proof of P, and
that is what justifies the conclusion, ¬P.
-/

/-
As a simple example, suppose P = false. To
prove ¬ P, we just have to show P → false,
which means false → false. This is easy: if
we assume false, then we can conclude false.
-/

lemma not_false' : ¬ false := λ (f : false), f

-- Note: Lean already defines not_false

#check not_false
#check not_false'

/-
As another example, suppose we want to show
that 0 ≠ 1. This is notation for ¬ 0 = 1,
which in turn is defined as 0 = 1 → false.
-/

example : 0 ≠ 1 :=
λ (h : 0 = 1), _
/-
Here, h is assumed to be a proof of a
proposition for which *there is no proof*.
There is no equality (eq) constructor that 
can produce this proof, h. There is only
eq.refl, and it can't possibly construct 
a proof that two different values are equal
because it only takes one value as an argument!
Case analysis of h thus works to finish the
proof: we want to show that no matter which 
eq constructor  produced h, that a proof of
false can be produced; but there is no case
in which an eq constructor (the only one being
eq.refl) could have produced h, so there are
no cases to consider, and we're done! 

This is essentially false elimination: doing
a case analysis on a proof of false reveals
that there are no cases to consider and so
the conclusion is trivially true *for all of
the ways in which such a proof could have 
been constructed* (of which there are none).
-/

example : false → 0 = 1 :=
λ f, match f with /- no cases!-/ end

/-
Now for the elimination rule for false. We 
just saw it: if one is given or can construct
a proof of false (from inconsistent assumptions)
then one can finish off any proof by showing 
that the conclusion, whatever it is, is true
for *all* of the ways that that proof could
have been constructive, again of which there
are none. False elimination is essentially 
done by case analysis on a proof of false.
-/

example : ∀ (P : Prop), false → P :=
λ (P : Prop) (f : false),
    match f with /- no cases -/ end

/-
We can also use false.elim as a shorthand
-/

example : ∀ (P : Prop), false → P :=
λ (P : Prop) (f : false), false.elim f


/-
A key pattern in proof construction is
thus first to derive a contradiction, in
the sense that for some proposition, P,
one has both a proof of P and a proof of
¬ P, then to *apply* the proof of ¬ P (a
proof of P → false) to the proof of P 
to derive a proof of false, and finally
then to use false elimination to finish
off the proof. 
-/

example : ∀ (P Q : Prop), P → ¬ P → Q :=
λ P Q p np, false.elim (np p)

/-
Such contradictions often arise in case
analysis of other proofs. For example, if
one applies the law of the excluded middle
to derive from a proposition, P, a proof of
P ∨ ¬ P, and then does case analysis on 
this proof, it will often happen that one
of the cases is self-contradictory. You
have to recognize the contradition in your
context, and then you can finish the proof
using the preceding "proof pattern".

In fact, this form of reasoning is so
common that Lean provides a shorthand
"tactic" to deal with it. If you ever
get into a situation in which you have
both (p : P) and (np : ¬ P) you can
finish off your proof "by contradition".
-/

example : ∀ (P Q : Prop), P → ¬ P → Q :=
λ P Q p np, by contradiction

/-
You may use this "tactic" if you wish on
the exam, but won't be required to do so.
-/


/-
Finally we come to the elimination rule for
negation (not). In predicate logic, this is
the rule that allows us to deduce the truth
of any proposition, P, from a proof of ¬ ¬ P.

As we've seen, this rule *not* valid in the
constructive logic of Lean but can be made
valid by accepting the axiom of the excluded
middle.
-/

theorem em_implies_neg_elim : 
    (∀ (P : Prop), P ∨ ¬ P) → 
    (∀ (P : Prop), ¬ ¬ P → P) :=
λ excluded_middle, 
λ P nnp,
match (excluded_middle P) with
| or.inl p := p
| or.inr np := false.elim (nnp np)
end

/-
In English, suppose that for any proposition,
P, P ∨ ¬ P is true (and that you have a proof
of this disjunction). Prove that given any P,
¬ ¬ P → P.

Proof: By case analysis on the assumed proof
of P ∨ ¬ P. First consider the case in which 
it is true because P is true. In this case, 
the conclusion, P, is obviously true.

Now consider the case in which P ∨ ¬ P is true
because ¬ P is true. But this case can't happen
because we've already assumed that ¬ P is false
(¬(¬P) is true). In other words, this case leads
to a contradiction, and so can be ignored). QED.
-/

/-
Here's a key proof strategy. It's called "proof
by contradiction". Suppose we want to prove P. 
One way to do it is to assume ¬ P and show that
this leads to a contradiction. This shows that
¬ P must be false, therefore ¬ ¬ P is true by
negation. But (assuming the law of the excluded
middle), ¬ ¬ P → P, which proves P.

Be able to state this principle clearly: To 
prove P, assume that it is false, show that
this assumption leads to a contradition, which
shows ¬ ¬ P is true, and then deduce using the
principle of negation elimination (which relies
on the law of the excluded middle) that P must
be true. 
-/

/-
Let's accept negation elimination as a theorem.
-/

theorem neg_elim : ∀ {P : Prop}, ¬ ¬ P → P :=
λ P nnp, 
    match (classical.em P) with
    | or.inl p := p
    | or.inr np := false.elim (nnp np)
    end


/-
Exercise: Prove 0 = 0 using proof by contradiction.
-/

example : 0 = 0 :=
neg_elim _
-- Note carefully what neg_elim needs.

-- Answer: (λ nzeqz, nzeqz (eq.refl 0))

/-
We apply neg_elim, which is the strategy of
proof by contradiction.

What it requires is a proof of ¬¬0=0. It
transforms the goal 0=0 into the goal ¬¬0=0!

That is, it requires a proof of ¬0=0 → false. 
To prove this, we assume ¬0=0 (the negation
of the proposition to be proved) and show that
this assumption leads to a contradiction and so
must be false. This is done by using refl to
construct a proof of 0=0 and by seeing that
this directly contradicts the assumption ¬0=0. 
So the assumption is show to be false and we
conclude that ¬¬0=0 is true. Finally by the
the (classical) rule of negation elimination
we have proved 0=0. QED.  
-/

/-
Proof Strategies: 

Proof by negation. To prove ¬ P,  show that 
assuming P leads to a contradiction, so P
must be false. That proves ¬ P. 

Proof by contradiction. To prove P (notice the
difference), show that assuming ¬ P leads to a
contradiction. Conclude that ¬ P is false, that
is ¬ ¬ P is true. Then use negation elimination
to deduce that P must be true.
-/