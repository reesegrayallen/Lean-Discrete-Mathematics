/- Iterated function application

The concept of "iterated function application"
is important: in computer science, to the concept
of fractals, and in the area known as "dynamical
systems" (weather, mixing of fluids, and chaotic
systems), among other areas.

Here we define a general purpose function,
apply_n, that implements this concept. It is
polymorphic in one type parameter α. Given a 
function, f : α → α, and a natural number, n, 
it returns a function that, when applied to 
its argument, a : α, returns the result of
applying f n times to a. Another way to say
this is that (apply_n f n) returns the 
function, f composed with itself n times
-/

def apply_n {α : Type} : (α → α) → ℕ → (α → α) 
| f 0 := λ (a : α), a
| f (n' + 1)  := λ (a : α), f ((apply_n f n') a)



/- Function composition

Suppose α, β, and γ are types, and that f : α → β 
and g : β → γ are functions. We can define a new
function, the composition of f and g written as 
(g ∘ f) : α → γ, where (g ∘ f) a = g (f a). Read
the preceding definition until you understand it. 

Composition "glues together" two functions into 
a new function: one that first "runs its argument
through f" and then "runs the result through g".
For f and g to be composable, the result type of 
f has to be the same as the argument type of g. 

If α, β, and γ are arbitrary types, then we can
compose any two functions, f and g, as long as
f : α → β and g : β → γ.

Here then is a completely general, mathematically
precise definition of function composition. And
because we have expressed it in Lean, we can use
it as an actual function. Lean provides function
composition as operation through its libraries,
with the convenient, standard ∘ notation. 
-/
def compose {α β γ : Type} : (α → β) → (β → γ) → (α → γ) 
| f g := λ (a : α), g (f a)



/- Map a function over a list

A "map" function takes a function, f : α → β and turns
it into a function of type list α → list β, that in turn
converts each (a : α) in the list into a corresponding 
(f a : β) in the result list. For example, (map_list 
nat.succ) is a function that turns a list of nats into 
a new list of nats by adding one to each element of the 
first list. Applying this function to the list [1,2,3]
would produce the list [2,3,4], for example.
-/
def map_list {α β : Type} : (α → β) → (list α → list β) 
| f [] := []
| f (h :: t) := ((f h) :: (map_list f t))




/- 
Fold-right a funtion over a list.

Fold-right (foldr) takes an operator, one that combines
the head of a given list with the result of foldr of the
tail, and an identity value of the result type. Given a
list, it uses it to combine the head of a list with the
result of applying the foldr function recursively to the
tail (with the same operator and identity element); with
the result for an empty list being that identity element.

Now think about a list (h :: nil). What the operator does
in this case is to derive a result for the whole list by
performing a computation on h and the result of folding
over the tail. In this case, the operator will combine h,
and the identity element for the result type, to derive
the result for the overall list. 

One can then repeat this process as many times as a list
is long to derive the correct result for the whole list.
-/
def foldr {α β : Type} : 
    /-op:-/   (α → β → β)  → 
    /-id:-/     β  → 
    /-lst:-/    list α → 
    /-result:-/ β 
-- by case analysis on list
| op id [] := id
| op id (h :: t) := op h (foldr op id t)



/-
Filter list under a predicate.

Exercise: Write a precise, correct, useful explanation
of the filter function, modeled on the explanations of
map and foldr.
-/
def filter {α : Type} : (α → bool) → list α → list α 
| p [] := []
| p (h :: t) := match (p h) with 
                | tt := (h :: filter p t)
                | _ := filter p t
                end 