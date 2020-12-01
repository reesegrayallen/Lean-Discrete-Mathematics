

import .higher_order


/-
Iterated function application
-/
#eval apply_n nat.succ 2 5
#eval (apply_n (λ n : ℕ, n^2) 2) 5
def square_2 := apply_n (λ n : ℕ, n^2) 2
#eval square_2 5


/-
Map function over list
-/
#eval map_list nat.succ [1,2,3,4,5]
#eval map_list (λ (n : ℕ), n^2) [1,2,3,4,5]
#eval map_list string.length ["Hello","I", "love", "CS!"]
#eval map_list (λ s, s ++ "!!!") ["I", "Love", "Logic!"]



/-
Foldr (op having same argument and result types)
-/

/-
Let's look at two special cases of foldr: the
first uses any binary operator, op : ℕ → ℕ → ℕ
to reduce a given list ℕ to a single ℕ result.
-/

def foldr_nat : (ℕ → ℕ → ℕ) → ℕ → list ℕ → ℕ 
| op id [] := id 
| op id (h :: t) := op h (foldr_nat op id t)

/-
The second generalizes from ℕ to any type, α.
-/

def foldr_α {α : Type} : (α → α → α) → α → list α → α 
| op id [] := id 
| op id (h :: t) := op h (foldr_α op id t)



/-
We can now use our ℕ-specific version to 
compute sums of lists and products of list.
-/
#eval foldr_nat nat.add 0 [1,2,3,4,5]
#eval foldr_nat nat.mul 1 [1,2,3,4,5]

/-
The generalized version works just as well.
-/
#eval foldr_α nat.add 0 [1,2,3,4,5]
#eval foldr_α nat.mul 1 [1,2,3,4,5]

/-
But the generalized version can also reduce 
lists of strings to strings, lists of bools
to bools, and so forth. That as we've seen
is the power of parametric polymorphism.
-/
#eval foldr_α string.append "" ["I", " ", "Love", " ", "Logic!"]
#eval foldr_α bor ff [ff,ff,tt,ff]  -- is *some* element true?
#eval foldr_α band tt [tt,tt,tt,tt] -- are *all* elements true?


/-
Now we're prepared to take on a most general
notion of folding right over lists. The rest o
this page provides motivation and a concrete,
worked out, example.

We formulate a simple computing problem to be 
solved. We want to reduce a list of strings to
a bool that is true if all strings in the list
are of even length and false otherwise. 

We'll build up to the solution in steps. Some
of them involve building of basic functions 
for our application. So let's get started.
-/



-- A predicate for deciding whether a ℕ is even 
def nat_even : ℕ → bool
| 0 := tt
| 1 := ff
| (n' + 2) := nat_even n'


-- A predicate for deciding if a string has even length
def string_even_length := nat_even ∘ string.length 


/-
Now we can use foldr_α to define a predicate on lists of
strings for *all* being of even length.
-/
def all_strings_even (l : list string) : bool := 
    foldr_α 
        band 
        tt 
        (map_list string_even_length l)



#eval all_strings_even ["","","ld"]


/---------------------------------------------------------------/






















--def apply_n {α : Type} : (α → α) → ℕ → (α → α) 
def apply_n {α : Type} : (α → α) → ℕ → α → α
| f 0 := λ (a : α), a
| f (nat.succ n') := 
    λ (a : α), f ((apply_n f n') a)


#eval (apply_n (λ n, n^2) 5) 2
#eval apply_n nat.succ 2 5


/-
Function composition 
-/
def compose {α β γ : Type} : (β → γ) → (α → β) → (α → γ ) := 
λ g f, 
    λ (a : α), 
        g (f a)

def is_even : ℕ → bool
| 0 := tt
| 1 := ff
| (n + 2) := is_even n

#eval compose is_even string.length "I love logic!"

def even_string := compose is_even string.length

/-
-/

def list_map {α β : Type} : (α → β) → list α → list β 
| f [] := []
| f (h :: t) := (f h :: (list_map f t))

#eval list_map is_even [1,2,3,4,5]

def exclaim : string → string
| s := s ++ "!"

#eval list_map exclaim ["Hello", "Lean"]

def foldn : (ℕ → ℕ → ℕ) → ℕ → list ℕ → ℕ 
| op id [] := id
| op id (h :: t) := op h (foldn op id t)


#eval foldn nat.add 0 [1,2,3,4,5]
#eval foldn nat.mul 1 [1,2,3,4,5]