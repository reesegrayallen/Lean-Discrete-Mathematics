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
#check true -- a proposition

#check bool
#check string
#check ℕ

#check Type 0
#check Type 1

#check Prop
#check Sort 0
#check Sort 1
#check Sort 2
