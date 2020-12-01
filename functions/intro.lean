-- Quick preview: higher-order functions

def inc (n : ℕ) := n + 1
def sq (n : ℕ) := n^2

def is := inc ∘ sq  -- function composition
#eval is 7

-- How to implement it yourself
-- Takes two functions and returns composition
def comp (f g : ℕ → ℕ) :=
    λ (n : ℕ), 
        f (g n)

#eval (comp inc sq) 7
