/-
REESE ALLEN (rga2uz)
Homework 4
CS 2102, Sullivan S20
-/


/- #1 

Representing Partial Functions as Total Functions
[20 points]

Consider the strictly partial function, pid, from 
natural numbers to natural numbers, defined by cases
as follows. If n is zero, the function is undefined,
otherwise pid n = n. We can't represent this function
directly in Lean, because Lean requires all functions
to be total. The usual approach is to represent such
a partial function as a total function that returns
not a nat (for then it would have to return a nat,
even when the argument is zero) but a value of type
option nat. Use this approach to implement pid in
Lean. Use "by cases" syntax. (Fill in the blanks.)
-/

def pid : ℕ → option ℕ 
| 0 := option.none  
| x := option.some x

#reduce pid 4 -- some 4
#reduce pid 0 -- none




/- #2 

Defining functions by cases (by pattern matching)
[15 points]

Given a value of type option ℕ, the value might be
none or it might be some n, where n is a value of 
type ℕ. Write a funtion option_to_nat that takes 
any value of type option ℕ as an argument and that
returns a natural number: namely 0 if the option
value is none, and n if the option value is some n.

Write your definition using C-style syntax, with 
an explicit return type specified. You will want 
to use a "match ... with ... end" expression to do
the required pattern matching.

(Note that it will be impossible to tell from the
return value alone whether a given option was none
or some 0.)
-/

def option_to_nat (op : option ℕ) :=
match op with 
| option.none := 0
| option.some x := x 
end

#eval option_to_nat (option.some 5) -- 5
#eval option_to_nat (option.none) -- 0


/-
Personal Notes:
there is not built-in notion of a partial function in dependent type theory; every element of a function
is assumed to have a value at every input - option type provides a way of representing partial functions
ex - an element of option β is either none or of the form some b, for some value b : β 
    can think of an element f of type α → option β as being a partial function from α to β:
    for every a : α, f either returns none, indicating f is "undefined", or some b

-/



/- #3

Inductive definitions.
[15 points]

You have probably yelled into a canyon (or maybe
between two buildings) and heard a reverberating
echo. An echo is a sound followed by another echo,
or, eventually an echo is no sound at all (at which
point the reverberation ends). 

Define a data type, echo, values of which represent
echoes. For our purposes, an echo comes in one of
two forms: it is either "silence" (at which point 
there is no more reverberation) OR it is a "sound"
followed another echo.

You can think of "silence" as a "base case" and
"sound" as an inductive case, in the sense that 
an echo of this form is a sound followed by a
smaller echo. Give each of these cases its own 
constructor.

Once you've defined your data type, define e0,
e1, and e3 to be identifiers bound to three values 
of this type, where e0 is bound to "silence", e1
is bound to an echo with one sound followed by
silence, and e3 is bound to an echo with three
sounds followed by silence. 
-/

-- this is not a "flat" type; constructors can act on elements of the very type being defined
-- (opposed to those that just wrap data and insert it into a type, which the recursor unpacks)

inductive echo : Type
| silence : echo
| succ (e : echo) : echo 

def e0 := echo.silence 
def e1 := echo.succ e0
def e2 := echo.succ (echo.succ e1)

#check e0 -- e0 : echo
#reduce e0 -- echo.silence
#check e1 -- e1 : echo
#reduce e1 -- echo.succ echo.silence
#check e2
#check @echo.rec_on

-- this is just another way to write the same thing
inductive echo' : Type 
| silence' : echo'
| succ : echo' →  echo'

def e0' := echo'.silence'
def e1' := echo'.succ e0'
#check echo'.rec_on 


/- #4

Lists. A word list type.
[10 points]

Define a data type, list_words_ values of which 
represent lists of words, where words are represented 
as  values of type string. For our purposes, such a 
list comes in one of two forms: it is either "nil" 
(the word we tend to use for empty lists), or it is
*constructed* from a word followed by a smaller list 
of words. Give each form of list its own constructor.
Call the constructors nil and cons.

Once you've defined your data type, define l0,
l1, and l3 to be identifiers bound to three values 
of this type, where l0 is bound to an empty list
of words, l1 is bound to a list with one word
(followed by the empty list), and l3 is bound to
a list with three words. We don't care what words
you put in your lists (but be nice :-). 
-/



-- inductive list_words_ : Type 
-- | nil : list_words_
-- | cons : list_words_ → string→ list_words_ 

inductive list_words_: Type 
| nil : list_words_
| cons (h: list_words_) (t: string) : list_words_

#check list_words_
#check @list_words_.rec_on


def l0 := list_words_.nil
def l1 := list_words_.cons l0 "first"
def l3 := (list_words_.cons(list_words_.cons l1 "second") "third")

#check l0
#check l1
#check l3



/- #5

Recursive definitions. Length of word list.
[10 points]

Define a function, num_words, that takes a word
list (as just defined) as an argument and that
returns the length of the list as a value of type
ℕ. 
-/

def num_words : list_words_ → ℕ
| (list_words_.nil) := 0
| (list_words_.cons α β) := 1 + (num_words α)

#reduce num_words l0 -- 0
#reduce num_words l1 -- 1
#reduce num_words l3 -- 3


/- #6 

Recursion. Number of permutations of a set.
[10 points]

Suppose you have a set containing n objects,
where n is a natural number. How many ways are
there to make an ordered list of n objects from
this (unordered) set? Such an ordered list is
called a permutation.

As an example, consider the set, { x, y, z}.
Here are the lists:
- x, y, z
- x, z, y
- y, x, z
- y, z, x
- z, x, y
- z, y, x

It's not too hard to see the answer to the
question. First, if the set is empty, there
is only *one* way to make a list: it is the
empty list. If the list is not empty, there
are n ways to pick the first element of the
list (so in our example, there are three ways
to pick the first element: it has to be x or
y or z); and then what's left is to make the
rest of each list from remaining n-1 (in our
example, 2) elements. So the number of lists
has to be n *times* the number of lists that
can be produced from a set of size n-1.

We can express this idea as a function. Let's
call it the permutations function, or perms, 
for short. As we've seen, perms 0 must be one.
This is the base case. Implement the function,
perms: ℕ → ℕ, to compute the number of perms
for a set of any given size, n. Note that in
Lean you'll need to use "by cases" syntax to
define a recursive function.
-/

-- n!
def perms : ℕ → ℕ 
| 0 := 1
| (nat.succ n) := nat.succ n * perms n 

#eval perms nat.zero -- 1
#eval perms 4 -- 24


/- #7

Recursion. Number of subsets of a given set.
[20 points]

How many subsets are there of a set of size
n?

A subset of a set, s, is a set all of whose
elements are in s. So every set is a subset
of itself, and the empty set is a subset of
every set, s (since all of its elements, of
which there are none(!), are in s).

So how many subsets are there of a set of 
size n? We can answer this question nicely
using recursion. First, how many subsets are
there of the empty set? It's one, right? If
you don't see this immediately, reread the
preceding explanation.

Now, consider a set, s, of size n, where n
is one more than some number, n'. How many
subsets does s have? 

To see the answer, ask the question, how
many subsets does a subset of s of size n'
= (n-1) have? If you have the answer to 
that question, then you can easily compute 
the number of subsets of s. A set, s', of 
size  n' must have left out one element of
s, let's call it e. For each subset of s', 
you can form *two* subsets of s: one with,
and one without e. 

Write a function, power_set_cardinality,
that takes a natural number representing
the size of a set, s, and that then returns
a natural number expressing the number of
subsets there are of a set of that size. 
-/


def power_set_cardinality: ℕ → ℕ
| nat.zero := 1
| (nat.succ n) := 2 * (power_set_cardinality n)

#eval power_set_cardinality 5 -- 32