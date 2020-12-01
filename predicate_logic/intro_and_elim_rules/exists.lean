/-
To prove that (∃ (p : P), Q) we show that there
is a specific value, p, in the context of which
we can prove Q. 
-/

/-
Here's a silly example. We want to show that
we can pick some natural number in the context
of which we can construct a proof of 1=1. Of
course it doesn't matter what number we pick
because 1=1 is true in any case. So in the
following example, we pick 524. But any value
will do. 
-/

lemma silly : ∃ (n : ℕ), 1 = 1 :=
exists.intro 524 rfl

/-
The identifier, silly, is now bound to a
proof of ∃ (n : ℕ), 1 = 1, and we can see
that this proof is actually an ordered pair,
labelled by the exists.intro constructor, the
first element of which is a specific value of
type P and the second of which is a proof of Q.
-/

#reduce silly

/-
In practice, Q will almost always be a
predicate taking a value of type P. In
this case, ∃ (p : P), Q p asserts that
there is some value, p : P, that makes
the predicate, Q p true. In other words,
∃ (p : P), Q p asserts that there is some
p with propery Q.
-/

axiom Ball : Type   -- assume there are Balls
axioms b1 b2 : Ball -- b1 and b2 are balls
axiom Blue : Ball → Prop -- Blue is a property
axiom b1_is_blue : Blue b1 -- b1 is blue

-- Prove there exists a blue ball
example : ∃ (b : Ball), Blue b :=
-- use exists.intro
exists.intro 
    b1          -- here's the ball we picked 
    b1_is_blue  -- here's a proof it's Blue

/-
Here's another example. We'll define ev to be
a predicate specifying a property of natural
numbers of "being even". Then we'll show that
there exists a number that has this property.
-/

def even : ℕ → bool := λ n, n%2 = 0

example : exists (n : ℕ), even n :=
exists.intro 6 rfl

/-
The elimination rule for ∃ tells us what we
can do with a a proof of an existentially
quanitified proposition.

Suppose for example that we're given a proof
that there exists an even natural number. What
can we deduce from this fact? We can deduce
two things: first, there is a specific number
and *we can give it a name*, such as n, for 
which, second, there is a proof, that we can
also name, e.g., pf, that *that specific n* 
is even. This is the elimination rule. 

It sounds complicated but it's not really.
Compare exists.intro and exists.elim to 
and.intro and and.elim. The and.intro rule
takes two proofs and forms a pair. The and
elimination rule takes such a pair and lets
us get back (and give names to) the component
proofs. Similarly, exists.intro forms a pair,
of a value and a proof (usually a proof that
that specific value has some property); and
the exists.elimination rule, given a proof
that such a value exists, let's us then give
names to that value and the associated proof.
*We can then use those two values in building
other proofs*. And, as you might expect, we
bind names to the component elements of a
proof of ∃ (p : P), Q by case analysis, and
specifically by pattern matching.
-/

/-
Example: Assume there are people and a binary
predicate/relation called Likes.
-/
axiom Person : Prop
axiom Likes : Person → Person → Prop

/-
Show that if there exists someone everyone
likes then everyone likes someone.
-/
example :   (∃ (p : Person), ∀ (q : Person), Likes q p) →  
            (∀ (p : Person), ∃ (q : Person), Likes p q):=
λ h : (∃ (p : Person), ∀ (q : Person), Likes q p),  -- assume proof of ∃ (n : ℕ), even n
    match h with    -- destructure this proof
    -- there's only one constructor, exists.intro
    -- give names to arguments to which it must have been applied 
    | exists.intro beloved liked_by_all := 
    -- now use *these* (now named) values to constructed needed proof
        λ anyone, 
            exists.intro beloved (liked_by_all beloved)
    end



example :   (∃ (p : Person), ∀ (q : Person), Likes q p) →  
            (∀ (p : Person), ∃ (q : Person), Likes p q):=
λ person_exists_that_everyone_likes,
match person_exists_that_everyone_likes with 
| exists.intro beloved loved_by_all := λ anyone,
_
end 
-- exists.intro beloved (loved_by_all beloved ) 
-- end 



/-
Here it is in plain English.

Suppose there's someone everyone likes. Show that everyone
likes someone. 

Proof: From the fact that there exists someone that everyone
likes, we can deduce that (1) there is a specific person, who
everyone likes; let's call that person "beloved"; and (2) it
is the case that everyone likes beloved. Now we must show that 
everyone likes someone. Pick an arbitrary but specific person,
call this person "anyone". We must show that there is someone
that "anyone" likes. But everyone likes beloved, so "anyone",
in particular, likes "beloved". Note: "anyone" might or might
not like other people, but we can be sure that "anyone" likes
beloved, and all we needed to show was that there is someone
that "anyone" likes. QED.
-/

/-
In Lean, if you already have a proof of some existentially
quantified proposition in your context, do case analysis on
it to assign names to its two components: first a value and
then a proof that that value makes the rest of the proposition
true. By the way, we call such a value a "witness" to the
given proposition.
-/

