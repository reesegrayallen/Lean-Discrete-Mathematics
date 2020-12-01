/-
HOMEWORK 3
Reese Allen   (rga2uz)
CS2102 - Sullivan
-/


-- defining new polymorphic abstract data type

inductive dm_box (α : Type) : Type
| mk : (α : Type) → dm_box 


 -- function defintions using lambda expressions, c-style (') and by cases ('')

def unbox {α : Type} : (dm_box α) → α :=
λ (b : dm_box α),
match b with 
| dm_box.mk x := x
end 

def unbox' {α : Type } (b : dm_box α) :=
match b with 
| dm_box.mk x := x
end 

def unbox'' {α : Type} : (dm_box α) → α
| (dm_box.mk x) := x


