import init.algebra.field
import data.real

namespace peirce

universe u

/-
Typeclass: Vector space, uniquely identified by index, 
over a field, α, of dimension dim.
-/
class vector_space (α : Type u) (dim : ℕ) (index : ℕ) : Type (u+1) :=
mk

instance real_1_vector_space ℝ 1 0

#check vector_space

structure scalar (α : Type u): Type u:=
mk :: (value : α)

inductive scalar_expr : Type
| slit (s: scalar)
| sadd : scalar_expr → scalar_expr → scalar_expr
| sneg : scalar_expr → scalar_expr
| smul : scalar_expr → scalar_expr → scalar_expr
| sinv : scalar_expr → scalar_expr
open scalar_expr


notation s1 + s2 := sadd s1 s2
notation s1 * s2 := smul s1 s2
-- complete


/-
VECTOR
-/
structure vector {α : Type u} {d : ℕ} {i : ℕ} (s : vector_space α d i) := 
mk 

structure vector_ident : Type :=
mk :: (index : ℕ)

inductive vector_expr : Type
| vlit (v : vector)
| vvar (i : vector_ident)
| vmul (a : scalar_expr) (e : vector_expr)
| vadd (e1 e2 : vector_expr)
open vector_expr

notation v1 + v2 := vadd v1 v2
notation a * v := vmul a v

/-
PROGRAM
-/

inductive vector_prog : Type
| pass (i : vector_ident) (e : vector_expr)
| pseq (p1 p2 : vector_prog)
open vector_prog

notation i = e := pass i e
notation p1 ; p2 := pseq p1 p2

/-
EXAMPLE
-/

-- some scalars
def s1 := scalar.mk 1
def s2 := scalar.mk 2
def s3 := scalar.mk 0

-- some scalar expressions
def se1 := slit s1 
def se2 := slit s2 
def se3 := se1 + se2
def se4 := se1 * se2

-- some spaces
def sp1 := space.mk 0
def sp2 := space.mk 1

-- some vectors
def v1 := vector.mk sp1
def v2 := vector.mk sp2
def v3 := vector.mk sp2

-- some vector expressions
def ve1 := vlit v1
def ve2 := vlit v2
def ve3 := ve1 + ve2
def ve4 := se1 * ve1
def ve5 := (se1 + se2) * ve1
def ve6 := se1 * (ve1 + ve2)

-- some vector identifiers
def i1 := vector_ident.mk 0 
def i2 := vector_ident.mk 1 
def i3 := vector_ident.mk 2

-- some vector computations
def p1 :=   i1 = ve1   
def p2 :=   i2 = ve2   
def p3 :=   p1 ; p2    
def p4 :=   i3 = ve5 ; 
            p3 ; 
            p2

end peirce



structure identifier : Type :=
mk :: (index : ℕ)


