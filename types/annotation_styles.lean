def z' : ℕ := (nat.zero : ℕ)
def z''  := (nat.zero : ℕ)
def z''' : ℕ := nat.zero
def z := 0

/-
If you want a rational zero or a real
zero, you'd have to say so explicitly.
Note: to make this code work without
errors requires importing definitions
from mathlib. We won't do this right 
now, so you will see red squiggle errors
in these examples.
-/

def q := (0 : ℚ)    -- zero of type rational
def r := (0 : ℝ)    -- zero of type real