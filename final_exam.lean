/-
| REESE ALLEN (rga2uz)
| CS2102 S20 Sullivan
| Final Exam
-/


/-
1. You know from our study of the Boolean 
satisfiability problem that there are 2^n
possible combinations of Boolean values for
n Boolean variables. 

Let's make the property of
natural numbers that is at issue clear by
defining "P n" to be proposition that "the
number of possible combinations of values
for *n* Boolean variables is *2^n*."

What your are to prove is the proposition
that this is true for any value of n. That
is, you are to prove ∀ n, P n.

Mext, recall that a proof of a universal
generalization (such as ∀ n, P n) *by induction*
is based on the application of the *induction
principle* for for the given data type. Here 
the data type is ℕ, and the induction rule for
ℕ is as follows:

∀ {P : Prop}, 
P 0 → 
(∀ n', P n' → P (n' + 1)) → 
∀ n, P n.

Reading backwards, this says that if you
want to prove ∀ n, P n, it will *suffice*
to prove P 0 and ∀ n', P n' → P (n' + 1)).
The reason is that you can then apply the
rule to deduce that ∀ n, P n must be true.
In other words, you can reduce the task of
proving ∀ n, P n to the tasks of proving
the two antecedents of this conclusion in
the induction rule.
-/


/-
*ANSWER* 

Theorem: For any natural number, n, the
number of combinations of values for n
Boolean variables is 2^n.

Proof: By induction. To prove ∀ n, P n,
where P is defined to be the proposition,
"the number of possible combinations of
values for n Boolean variables is 2^n,"
it will suffice to prove P 0 and 
∀ n', P n' → (n' + 1)


Here is a more complete quasi-formal version 
of the proof with algebra: 

Our aim is to prove the predicate [P(n)], which 
says that for any ℕ n, the number of possible 
combinations of values, i.e. interpretations, for 
n Boolean variables is 2^n. We do so inductively 
and must first prove / show two things: [1] The 
proposition P is true for n = 0, our base case. 
[2] If we assume the number of combinations for n' 
Boolean variables is 2^n' for some arbitrary but 
specific ℕ n', our induction hypothesis, then the 
number of combinations of (n' + 1) Boolean 
variables is 2^(n' + 1). 

By the principle of induction, through assuming 
P(n') is true and using it to prove that P(n' + 1) 
is true, we can conclude that P(n) is true for 
all ℕs n. 

[1] This is easy. Our base case says that for zero 
Boolean variables, there is one combination. 
We treat P(0) = 1 almost like an axiom. We have 
defined the number of combinations of values for 
0 Boolean variables to be 1. This is certainly true. 

[2] We can prove this second step algebraically. I'm 
going to use k here to represent n' because it is a
bit cleaner to read. Assuming P(k) = 2^k is true,
we want to show P(k + 1) = 2^(k + 1) is true.
2^(k + 1) is equivalent to (2^k) + (2^1) by our
rules of exponents, which is equivalent to 
(2^k) * 2; it follows that P(k + 1) = P(k) * 2. 
Because P(k) is true for any k, it must be that 
P(n) is true for any n. 
-/




/-  2  -/

def aProp :=    ∀ (α : Type), ∀ (Heavy Charmed: α → Prop),
                (∃ (a : α), Heavy a ∧ Charmed a) →
                (∃ (a : α), Charmed a)


/- 
2a. English language rendition of this proposition:

The proposition aProp says suppose that you have 
ojects of some type α and that Heavy and Charmed 
are properties of type α. If there exists an 
object a of type α that is both Heavy and Charmed,
then there exists some object that is only Charmed. 
-/


/- 2b. Give a formal proof of it. -/

example : aProp := 
λ α : Type, 
    λ H C : α → Prop,
        λ hac : ∃ (a : α), H a ∧ C a,
        match hac with 
        | exists.intro obj pf := let Cobj := pf.right in
            exists.intro obj Cobj 
        end 


/- 
2c. Quasi-formal, English-language proof:

To prove the proposition aProp, we suppose that objects 
of type α exist and that Heavy and Charmed are predicates 
that take an object of type α as an argument and return a 
proposition, which could be true or false. We will just 
say that heavy and charmed are properties of these 
objects. Denoting an object of type α as a and the 
predicates Heavy and Charmed as H and C, respectively,
when we say that there is a proof of heavy and charmed,
for example, what we mean is that there is a proof that 
the conjunction of H(a) and C(a) is true. 

In this context, we want to prove an implication by 
showing that if there is an object that is both heavy 
and charmed, then there is an object that is charmed. 
Given a proof that objects of type α exist that are both 
heavy and charmed, which we call hac, we can deduce that 
there is an object that has the properties of heavy and 
charmed. We assume this by reasoning through case analysis 
and with existential instantiation, i.e. the exists 
introduction rule. We call our single arbitrary but 
specific object of type α obj. The only case in which our 
proof hac could have been constructed is by applying the 
exists introduction rule to obj and a proof that heavy 
and charmed is true, i.e. that obj has the properties of 
heavy and charmed, which we call pf. The proof pf is 
constructed through conjunction introduction, another rule 
of inference. We can destructure pf with the right 
elimination rule; given a proof of heavy and charmed, we 
can derive a proof of just charmed, which we call Cobj. 
We can then use instantiation again by applying the exists 
introduction rule to our object obj and our proof of 
charmed Cobj. By showing that a proof that an object of 
type α can be constructed from a proof that objects of 
type α exist with the properties of heavy and charmed, 
we have proved aProp.
-/



/-  3  -/

def aProp2 :=   ∀ (α : Type), ∀ (Heavy Charmed: α → Prop),
                (∃ (a : α), Heavy a ∨ Charmed a) →
                (∃ (a : α), Heavy a) ∨ (∃ (a : α), Charmed a)


/- 
3a. English language rendition of this proposition:

The proposition aProp2 says suppose that you have 
objects of some type α and that Heavy and Charmed 
are properties of type α. If there exists an 
object a of type α that is Heavy or Charmed, then 
there exists an object that is just Heavy or there
exists an object that is just Charmed. 
-/


/- 3b. Give a formal proof of it. -/

example : aProp2 := 
λ α : Type,
    λ H C : α → Prop, 
        λ hoc : ∃ (a : α), H a ∨ C a, 
        match hoc with
        | exists.intro obj pf := 
            match pf with 
            | or.inl h := or.inl (exists.intro obj h)
            | or.inr c := or.inr (exists.intro obj c)
            end 

        end 


/- 
3c. Quasi-formal, English-language proof:

To prove the proposition aProp2, we suppose that objects 
of type α exist and that Heavy and Charmed are predicates 
that take an object of type α as an argument and return a 
proposition, which could be true or false. We will just 
say that heavy and charmed are properties of these objects. 

When we say that there is a proof of heavy or charmed, 
for example, what we mean is that there is a proof that 
the disjunction of the predicates Heavy and Charmed, when 
each is given an object of type α, is true. This is 
analogous to saying that the object has the property of 
heavy, the property of charmed, or both.   

In this context, we want to prove an implication 
by showing that if there is an object that is heavy or 
charmed, then there is an object that is heavy or there 
is an object that is charmed. Given a proof that objects of 
type α exist that are heavy or charmed, which we call hoc, 
we can deduce that there is an object that has the properties
of heavy or charmed. We assume this by reasoning through 
case analysis and with existential instantiation, i.e. the 
exists introduction rule. We call our single arbitrary but 
specific object of type α obj. The only case in which our 
proof hoc could have been constructed is by applying the 
exists introduction rule of inference to obj and a proof 
that obj is heavy or charmed, which we call pf. The proof 
pf is constructed through disjunction introduction. Using 
case analysis again, we can destructure pf to show the two
ways in which it could have been formed. A proof of a 
disjunction is constructed either from a proof of the left
disjunct or a proof of the right disjunct. We assume that 
our object obj has the property of heavy in the first case, 
the proof of which we denote as h, and that obj has the 
property of charmed in the second case, which we denote as c. 
To prove the first case, we use the left elimination rule 
applied to a proof that there exists an object that is heavy, 
which is given through instantiation by applying the exists 
introduction rule to our object obj and our proof h. Similarly, 
to prove the second case, we use the right elimination rule 
applied to a proof that there exists an object that is charmed, 
which is given through instantiation by applying the exists 
introduction rule to our object obj and our proof c. By showing 
that a proof that an object of type α has the property of heavy
and a proof that an object of type α has the property of 
charmed can be constructed from a proof that objects of type 
α exists that are heavy or charmed, we have proved aProp2.
-/




/- 4.
Formally specify the syntax and semantics
of a language of *arithmetic* expressions that
can include variables, where the meaning of
an expression is (reduces to) a natural number.

Hint: model your answer on our specification
of the syntax and semantics of *propositional
logic* expressions.
-/

/- In this language, an interpretation will
map variables to natural numbers rather than
to Boolean values. We'll give you a start on
a solution by defining (1) a type of variables
that are distinguished from one another by a
ℕ-valued index, (2) specifying the type of an
interpretation, and (3) giving an example of
an interpretation in which all variables have
the value zero.
-/

-- our variable type
structure a_var : Type := mk :: (index : ℕ)


-- friendly names for a few variables
def X_var := a_var.mk 0
def Y_var := a_var.mk 1
def Z_var := a_var.mk 2

-- the type of an interpretation
def interp := a_var → ℕ 

-- one possible interpretation, "all zero"
def all_zero_interp : interp := λ v, 0

/-
4a. Define an interpretation in which X has
value 3, Y has value 7, and Z has value 1,
and all other variables have value 0.
-/

def an_interp : interp := λ v,
match v with 
| a_var.mk 0 := 3
| a_var.mk 1:= 7
| a_var.mk 2 := 1
| _ := 0
end 
    

/-
4b. Define the syntax of your language to have
the following kinds of expressions. 

- ℕ literal expression
- ℕ variable expression
- expression + expression
- expression * expression

Do this by defining an inductive type, aexp, 
the values of which are arithmetic expressions
in our language. Call your constructors lit, 
var, add, and mul. When you succeed, the test
expressions we give you should type check.
-/

inductive aexp : Type
| lit : ℕ → aexp
| var : a_var → aexp 
| add : aexp → aexp → aexp 
| mul : aexp → aexp → aexp 

open aexp

-- These expressions should type-check
def X := aexp.var X_var
def Y := aexp.var Y_var
def Z := aexp.var Z_var
def l6 := aexp.lit 6
def e1 := aexp.add X Y
def e2 := aexp.mul X Z
def e3 := aexp.mul e1 l6


/-
4c. Define a semantics for your
language so that expressions evaluate
to natural numbers as they would using
the standard notions of addition and
multiplication. Furthermore, literal
expressions should evaluate to their
natural numbers arguments, and variable
expressions should evaluate the natural
numbers according to an interpretation
given to the evaluation function (call
it aEval). Remember to put constructor
expressions in parentheses when using
pattern matching / destructuring. When
you've succeeded, the test cases we've
provided should all pass.
-/

-- Your answer here
def aEval : aexp → interp → ℕ 
| (lit n) _ := n 
| (var av) i  := i av
| (add ae1 ae2) i := (aEval ae1 i) + (aEval ae2 i)
| (mul ae1 ae2) i := (aEval ae1 i) * (aEval ae2 i )


-- Test cases that should pass when you've succeeded
example : aEval X an_interp = 3 := rfl
example : aEval Y an_interp = 7 := rfl
example : aEval Z an_interp = 1 := rfl
example : aEval l6 all_zero_interp = 6 := rfl
example : aEval e1 all_zero_interp = 0  := rfl
example : aEval e2 an_interp = 3 := rfl
example : aEval e3 an_interp = 60 := rfl



/-
5. Explain concisely but also precisely how a
proof of a proposition, P, "by contradiction"
would be carried out. Be sure to point out
exactly where negation elimination is involved.

Then explain concisely and precisely how a
proof of a proposition, ¬ P, would be carried
out. 

To carry out a proof of a proposition P by contradiction,
we assume ¬P and show that this leads to a contradiction.
Negation elimination essentially allows us to delete 
double-negatives and is given by the law of the excluded
middle, which we treat as an axiom in Lean. Specifically, 
classical.em : ∀ (P : Prop), P ∨ ¬ P. It allows us to 
assume that for any proposition, either that proposition
is true or its negation is true 


In order to carry out a proof of a proposition ¬ P, we 
use proof by negation. We start by assuming that there is 
a proof that the proposition is true and show that this 
enables us to construct a proof of false. A proof of false 
does not exist, so if assuming P allows us to construct one, 
then the assumption that P is true must be wrong, i.e. ¬ P
is true. ¬ P is equivalent to P → false. To prove ¬P, we just 
show that if P is true then false is true. An example would 
be to use case analysis to prove the implication P → false. 
Assuming P, we match the proof of P with a constructor, which 
is an empty match statement (there are no cases). This shows 
that P implies false, so we have proved that ¬ P, the negation 
of P, must be true.  

-/



/- 6. A simplish proof. Give a formal proof
of the following proposition. Then explain
briefly in English why the proposition must
be true no matter what propositions P and Q
are.
-/

example : ∀ (P Q R : Prop), ¬ ((P ∧ ¬ Q) ∧ (Q ∧ ¬ R)) :=
λ P Q R, 
    λ h,
    match h with 
    | and.intro panq qanr := 
        let nq := panq.right in 
        let q := qanr.left in
        nq q 
    end 

/-
Our goal is to prove that for any propositions P, Q, and R, 
it is not the case that the conjunction of P and not Q, the 
left conjunct, and Q and not R, the right conjunct, is true.
This is to show that (P ∧ ¬ Q) ∧ (Q ∧ ¬ R) implies false. We 
start by assuming that we have propositions P, Q, and R and 
a proof, which we call h, that (P ∧ ¬ Q) ∧ (Q ∧ ¬ R) is true. 
We reason by case analysis and show that to construct h, the 
and introduction rule is applied to the left and right conjuncts.
Using the left and right elimination rules applied to the 
left and right conjuncts of h respectively, we arrive at a proof,
or a construction, of ¬ Q ∧ Q, which is false. By showing that 
(P ∧ ¬ Q) ∧ (Q ∧ ¬ R) leads to a contradiction, we have proved 
that h implies false, i.e. ¬ ((P ∧ ¬ Q) ∧ (Q ∧ ¬ R)) is true. 

-/
