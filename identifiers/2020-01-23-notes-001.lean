def x := 1 + 2
#print x
#eval x

/-
Identifiers, bindings, types
-/

def b' : bool := (tt : bool)
def b'' := tt

-- type inference

def s' : string := "I love logic!"

def n' : ℕ := 1

/-
Functions and their application
-/

#eval band tt tt
#eval tt && tt

#eval nat.add 3 4

#eval string.append "Hello, " "Logic!"
#eval "Hello, " ++ "Logic!"

#check band



/-
Types
-/

/-
Every term has exactly one type
A type defines a set of terms
These sets are disjoint
-/

#check 0
#check "Hello"
#check tt
#check prod.mk 2 "Hi!"
#check true     -- a proposition

#check bool
#check string
#check ℕ 

#check Type 0
#check Type 1

#check Prop
#check Sort 0
#check Sort 1
#check Sort 2

