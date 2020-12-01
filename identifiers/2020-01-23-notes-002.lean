def pop := prod.mk         
        (prod.mk 2 tt) 
        (prod.mk "Hello" 3)

#eval prod.mk         
        (prod.mk 2 tt) 
        (prod.mk "Hello" 3)

#eval pop

-- Oops. Immutable. So this won't work.
def pop := prod.mk         
        (prod.mk 2 tt) 
        (prod.mk "Hello" 3)


/-
Big conversation about mutable vs immutable, functional 
vs imperative, referential transparency.
-/

def b := tt

/-
Rule for evaluating identifier expressions.
-/

#eval tt
#eval b

def n := 2
#eval n

def s := "Hello"
#eval s

/-
Every term has exactly one type
A type defines a set of terms
Types are disjoint
-/

#check 0
#check n
#check b
#check prod.mk         
        (prod.mk 2 tt) 
        (prod.mk "Hello" 3)

#reduce (ℕ × bool) × string × ℕ

/-
-/

#check 3
#check ℕ 
#check bool
#check string 

#check Prop
#check Type 
#check Type 2

/-
Abstract data type (ADT)

data type + set of functions
-/

#eval band tt tt
#eval tt && tt
#eval tt || ff

#eval bor tt ff
#eval bor (band tt tt) ff


#eval nat.add 3 4
#eval nat.mul 3 4
#eval nat.sub 4 3
#eval nat.sub 3 4

#eval string.append "I love " "Logic"
#eval string.length "I love Logic"
#eval "I love " ++ "Logic"

#check bor