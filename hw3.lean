/-
Review: bool
New: Product types
New: Polymorphic types
-/


/-
1. [30 points]

In class we implemented a polymorphic ordered
pair abstract data type that we called prod_S_T.
In a new file called dm_prod.lean re-implement
this ADT but call it dm_prod. Implement at least
the following functions:

- fst
- snd
- set_fst
- set_snd
- swap

For this part of the homework, write the function
definitions using lambda expressions and in all 
cases specific "implicit arguments" for the type
arguments of these functions.

Then, in a second file called dm_prod_test.lean,
write test cases for your implementation. You
will have to import your dm_prod.lean file into
this test file so that it has access to your 
dm_prod definitions.

Your test cases should include (1) the definitions 
of three ordered pairs, p1, p2, and p3, with elements 
types of ℕ and ℕ, ℕ and bool, and bool and bool,
respectively; (2) the use of #eval or #reduce to
confirm that your functions operate as expected,
at least for these test cases.
-/

/-
2. [40 points].

After each function definition in your dm_prod.test
file, write two new equivalent function definitions,
the first one using C-style and the second using "by
cases" style. Add one prime/tick mark to the name of
each C-style function to avoid name conflicts, and
two tick marks for the "cases-style" definitions. For
all functions, specify the use of implicit arguments
for type arguments.
-/

/-
3. [30 points]

Define a polymorphic ADT called dm_box. This type
builder takes one type argument. The intuitive 
idea is that a dm_box contains one value of the
type specified by the type argument. Define dm_box 
to have one constructor, mk, that takes one value 
of the specified type and that produces a dm_box
with that value stored "in" the box. Note: a box
is very much like an ordered pair but it contains
only one value, not two.  Define one "inspector"
function, unbox, that takes a dm_box and returns
the value "inside" the box. Write unbox, unbox',
and unbox'', using respectively lambda, C-style,
and cases syntax. Put your definitions in a file,
dm_box.lean, and write a few test cases, using
values of different types, in dm_box_test.lean.
-/

/-
Submit all four files required for this assigment
via the HW#3 assignment page on Collab.
-/