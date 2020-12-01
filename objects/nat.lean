-- Natural numbers

-- data type
#eval nat.zero 
#eval (nat.succ nat.zero)
#eval nat.succ (nat.succ nat.zero)

-- notation
#eval 0
#eval 1
#eval 2 

-- operators
#eval nat.add 1 2   -- addition
#eval nat.mul 2 3   -- multiplication
#eval nat.pow 2 3   -- exponentiation
#eval nat.sub 4 1   -- subtraction
#eval nat.div 4 3   -- quotient
#eval nat.mod 4 3   -- remainder

-- notation
#eval 1 + 2
#eval 2 * 3
#eval 4 - 1 
#eval 4 / 3
#eval 4 % 3

-- a theorem and its already Lean-defined proof
def add_commutes : ∀ (n m : ℕ), n + m = m + n := nat.add_comm