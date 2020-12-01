/-
Take funtion as argument and use it in implementation.
-/

def apply_nat_to_nat (f : ℕ → ℕ) (n : ℕ) : ℕ := 
    f n

#eval apply_nat_to_nat nat.succ 1
#eval apply_nat_to_nat nat.pred 1

/-
Make idea completely general using polymorphism
-/

def apply {α β : Type} (f : α → β) (a : α) : β := 
    f a

#eval apply nat.succ 1
#eval apply nat.pred 1
#eval apply string.length "I love logic!"


/-
Return function as a result
-/

def apply_twice {α : Type} (f : α → α ) : α → α := 
    λ a, f (f a)

#reduce (apply_twice nat.succ) 
#reduce apply_twice nat.pred

def double (n : ℕ) := 2 * n

def square (n : ℕ) := n ^ 2

#eval apply_twice nat.succ 3    -- application is left associative
#eval apply_twice nat.pred 3    
#eval (apply_twice double) 3  

def square_twice := apply_twice square
def double_twice := apply_twice double

#eval square_twice 5

/-
That's composition of a function with itself,
but we can also compose different functions.
Here's a special case.
-/

def compose_1 {α : Type} (g : α → α ) (f : α → α ): α → α := 
    λ a, g (f a)

def double_inc := compose_1 double nat.succ
#reduce double_inc
#eval double_inc 3

-- Define and try out inc_double (first double then increment)

def is_even (n : ℕ) : bool := n % 2 = 0

#eval is_even 6

def compose {α β γ : Type} (g : β → γ) (f : α → β) : α → γ :=
    λ (a : α), g (f a)

def even_length := compose is_even string.length
#eval even_length "I love logic!!!!!!!"

def even_length' := is_even ∘ string.length     -- math notation

/-
Functions are objects, too, and there are associated 
operations that apply to functions. Composition is one
such operation. Differentiation is another example of 
a function of functions.
-/

/-
Exercise: apply_n
-/

/-
List map.
-/

def list_map {α β : Type} : (α → β) → list α → list β 
| f [] := []
| f (h :: t) := list.cons (f h) (list_map f t)

-- exercise box_map
-- exercise option_map
-- exercise tree_map