import .higher_order_2

/-
Exercise: Consider apply_n again. It takes a
function, f, and a natural number, n, and returns 
a new function, let's call it f^n, that applies f 
n times to its argument. 

Note: f^n is simply the function f composed with 
itself n times. Write a new version of apply_n,
with exactly the same type as apply_n, but now 
using the ∘ notation for function composition and
Lean's polymorphic "id" (identity) function.
-/

-- Answer

def apply_n' {α : Type} : (α → α) → ℕ → (α → α) 
| f 0 := id
| f (n' + 1)  := f ∘ (apply_n' f n')

/-
Suppose we want to compute a Boolean value, with the
result, true (tt), if all of the strings in a list of 
strings has even length, and false (ff) otherwise. To
build this function, it'd be nice to have three helper 
functions: len : string → ℕ, that computes the length
of a given string; ev_nat, that determines whether a
given natural number is even (tt) or not. Third, we
can compose these functions to computer whether a
given string is of even length. 
-/

def len := string.length

def ev : ℕ → bool 
    | 0:=tt 
    | 1:=ff 
    | (n'+2):=ev n'

def ev_string := compose len ev

/-
The composition, compose len ev, gives us a new
function that takes a string and return a boolean
that depends on whether its length is even or not.
-/

#eval ev_string "Hello!"

/-
We can easily confirm that ev_string : string → bool.
-/

#check ev_string



/-
Here's the key idea: we can reduce a list of strings to 
a Boolean indicating whether the list has the all-even 
property as the conjunction of two predicates: (1) h is 
even, (2) the rest of the list has the all-even property.

The algorithm is thus, first reduce the rest of the list
to a boolean value, then compute whether the current head
has the property, then compute the conjunction (and) of
these two Boolean values. 

In a sense we start at the right end of the list and 
reduce it to an "accumulated" value, starting with an
"identity" value, then moving right to left, updating
the accumulated value with the value for the curent list
head. 

Let's think, then, about a function that takes these two
values -- the current head, (h : string) and the result,
(acc : bool), of having already reduced the tail of the
list to a bool -- and that combines these two values, a
string and an accumulated bool into a bool result. 
-/

def all_ev_op : string → bool → bool 
| s b := band (ev_string s) b

#eval foldr nat.add 0 [1,2,3,4,5,6,7,8,9,10]
#eval foldr nat.mul 1 [1,2,3,4,5,6,7,8,9,10]

def add_all := foldr nat.add 0
def mul_all := foldr nat.mul 1

#eval mul_all [1,2,3,4,5,6,7,8,9,10]



def sum_list := foldr nat.add 0 
def prod_list := foldr nat.mul 1




def all_ev := foldr all_ev_op tt

def some_ev_op : string → bool → bool
| s b := bor (ev_string s) b

def some_ev := foldr some_ev_op ff

#eval some_ev []
#eval some_ev ["aa","f"]

def le : ℕ → ℕ → bool
| 0 _ := tt
| (n' +1) 0 := ff
| (n' + 1) (m' + 1) := le n' m'


#check @foldr


#eval all_ev ["eelfff","eeee","fffff"]

#eval filter ev_string ["","BVKI",""]







