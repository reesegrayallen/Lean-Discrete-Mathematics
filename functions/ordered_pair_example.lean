/-
Explicit type arguments
-/

/-
A polymorphic type, poly, with one type
parameter, here named alpha. Objects of
this type represent ordered pairs where
both elements are of the same type, e.g.,
ordered pairs of natural numbers, ordered
pairs of strings, etc. 
-/
inductive my_prod (α : Type) : Type
| mk : α → α → my_prod

def p := my_prod.mk 3 3


/-

Note: The fact that we use a Greek letter,
alpha, for the type argument, has no real
significance other than being a convention
in Lean. 
-/

def p1 := my_prod.mk 3 5

def swap (α : Type) : my_prod α → my_prod α
| (my_prod.mk x y) := my_prod.mk y x

def p2 := swap ℕ p1 -- type argument explicit

#reduce p2

/-
Implicit type arguments
-/

/-
This version uses curly braces around the
declaration of the type argument, α. What
this tells Lean is that it should not expect
an explicit type parameter, rather it should
use type inference to infer the value of this
parameter automatically (from the value to
which the funtion is applied).
-/

def swap' {α : Type} : my_prod α → my_prod α
| (my_prod.mk x y) := my_prod.mk y x

def p3 := swap' p1  -- type argument implicit

-- It worked!

/-
If you have specified use of implicit arguments
you may NOT give arguments explicitly. If for 
some reason you must (typically because Lean
does not have enough information to infer them),
turn off implicit arguments by prefixing a given
function application @.
-/

def p4 := @swap' ℕ p1   -- type argument explicit

/-
In summary, when you want the programmer to be
able to apply a polymorphic functions without 
explicitly giving type arguments, enclose the 
declarations of the arguments in curly braces 
and then do not give these arguments when the f
unctions are applied. 
-/

