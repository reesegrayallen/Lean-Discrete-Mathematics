-- Function expressions / lambda abstraction 
-- anonymous functions

#check λ (n : ℕ), 0
#check λ (n : ℕ), n
#check λ (a b : ℕ), a+b
#check λ (a b c x: ℕ), a*x^2 + b*x + c

-- Function *application* expressions

#check (λ (n : ℕ), 0) 5
#check (λ (n : ℕ), n) 5
#check (λ (a b : ℕ), a+b) 3 2
#check (λ (a b c x: ℕ), a*x^2 + b*x + c) 1 2 3 10

-- Binding names (identifiers) to function values

def z := λ (n : ℕ), 0
def id_nat := λ (n : ℕ), n
def add := λ (a b : ℕ), a+b
def quad := λ (a b c x: ℕ), a*x^2 + b*x + c

-- Now we can use names as shorthands

#eval z 5
#eval id_nat 5
#eval add 2 3
#eval quad 1 2 3 10

-- Extra: partial evaluation

def q := quad 1 2 3
#check q
#eval q 10
#eval q 0
#eval q 5


-- Lambda-style
-- C-style
-- By cases
-- Tactic script

-- C-style

def z' (n : ℕ) := 0
def id_nat' (n : ℕ) := n
def add' (n m : ℕ) := n + m
def quad' (a b c x : ℕ) := a*x^2 + b*x + c

#reduce z' -- same function as z exactly

-- By cases

def z'' : ℕ → ℕ 
| _ := 0

def id_nat'' : ℕ → ℕ 
| n := n

def add'' : ℕ → ℕ → ℕ 
| n m := n + m

def quad'' : ℕ → ℕ → ℕ → ℕ → ℕ 
| a b c x := a*x^2 + b*x + c


-- Functions with arguments of several types

-- Example: if (b==tt) then (n:ℕ) else (m:ℕ)

-- by cases
def if_then_else : bool → ℕ → ℕ → ℕ 
| tt n m := n
| ff n m := m

-- try it out
#eval if_then_else ff 3 4

-- by cases using match
def ite' (b : bool) (n m : ℕ) :=
    match b with
    | tt := n
    | ff := m
    end

-- by cases using lambda and match
def ite'' : bool → ℕ → ℕ → ℕ := 
    λ (b : bool) (n m : ℕ), 
        match b with
        | tt := n
        | ff := m
        end


