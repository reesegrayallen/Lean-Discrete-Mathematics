/- ∀ introduction

Suppose P and Q are arbitrary propositions. 
To prove a proposition given in the form of
a universal generalization, ∀ (p : P), Q,
assume that P is proved and that you have an
arbitrary but specific proof p' of P, and
show that, in this context, Q must be true,
by showing you can construct a proof of it.

Here's an example. The proposition says that
for all propositions, P and Q, if P ∨ Q is
proven, then Q ∨ P can be proven. To prove it,
*assume* P and Q are arbitrary but specific,
propositions, then, in this context, prove
the rest (that P ∨ Q → Q ∨ P).

In short, to prove ∀ (p : P), Q, assume that
you have a proof of P and show that in this
context you can then prove Q. This is the rule
of ∀ introduction.
-/

theorem or_commutative : ∀ {P Q : Prop}, P ∨ Q → Q ∨ P :=
λ (P Q : Prop),     -- assume arbitrary values of P, Q 
                    -- in this context, prove the rest
                    -- for completeness, here's the rest
    λ (porq : P ∨ Q),   -- by → introduction
        match porq with -- by case analysis
        | or.inl p := or.inr p  -- true in this case
        | or.inr q := or.inl q  -- true in other case
        end                     -- QED


/- ∀ elimination

Suppose that in the set of proofs you already have 
or that you have assumed, you have a proof, all_p_q,
of ∀ (p : P), Q. The rule of ∀ elimination allows
you to *apply* this generalization to any specific
value, p' : P, to obtain a corresponding proof of Q.

To put it simply, once you've proved a *general*
theorem, you can apply that result to any particular
instance. For example, we just proved that the ∨ 
connective of predicate logic is commutative, *in
general*. So now suppose we're given a proof of
1=1 ∨ 2=3 and what we need to prove is 2 = 3 ∨ 1 = 1.
We do *not* need to prove this special case from 
scratch; rather we can simply *apply* the theorem
and be done with it. 
-/

-- First, let's get a proof of (1 = 1 ∨ 2 = 3)

lemma l1 : 1=1 ∨ 2=3 := or.inl rfl

-- Just apply theorem to get proof of 2 = 3 ∨ 1 = 1
#check or_commutative l1

example : 2 = 3 ∨ 1 = 1 := or_commutative l1

/-
It would be hard to overstate the importance of the
idea of ∀ elimination. It's just a fancy way to say
that if you've proven a general theorem, you can use
it immediately without having to re-prove anything to
prove any particular special case that matches the
conditions that it demands (here that P and Q are
any propositions and that you have a proof of P ∨ Q).

You can think of a theorem as a subroutine that you 
have already implemented that you can apply whenever
you need it! This idea is what allows mathematics to
work, so not every proof has to start from scratch.

In the constructive logic of Lean, indeed a proof of
∀ (p : P), Q, *is* a function: one that, if given any
proof (or equivalently, a value) of P returns a proof
(a value) of Q.
-/

