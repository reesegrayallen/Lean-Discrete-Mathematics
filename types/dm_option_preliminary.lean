namespace hidden







inductive dm_option (α : Type): Type
| none : dm_option
| some (a : α) : dm_option

/-
Heres an example of a representation in Lean of
a partial function, p, from ℕ to ℕ, such that 
p(n) = 0 if n=0 and p(n) is undefined otherwise.  
-/

def p : ℕ → dm_option ℕ 
| nat.zero := dm_option.some nat.zero
| _ := dm_option.none ℕ       -- needs explicit type!


end hidden
