/-
We've seen how to write simple product types
and associated funtions.
-/

namespace ex1

inductive prod_nat_nat : Type
| mk : ℕ → ℕ → prod_nat_nat

def p := prod_nat_nat.mk 3 5

def fst (p : prod_nat_nat) : ℕ :=
    match p with 
        | prod_nat_nat.mk x y := x
    end

def sec (p : prod_nat_nat) : ℕ :=
    match p with 
        | prod_nat_nat.mk x y := y
    end

#eval fst (prod_nat_nat.mk 3 4)
#eval sec (prod_nat_nat.mk 3 4)

end ex1

/-
We can also use C-style argument notation
when defining the type.
-/

namespace ex2

inductive prod_nat_nat : Type
| mk (x y : ℕ) : prod_nat_nat

def fst (p : prod_nat_nat) : ℕ :=
    match p with 
        | prod_nat_nat.mk x y := x
    end

def sec (p : prod_nat_nat) : ℕ :=
    match p with 
        | prod_nat_nat.mk x y := x
    end

#eval fst (prod_nat_nat.mk 3 4)
#eval sec (prod_nat_nat.mk 3 4)

end ex2

/-
Even better though, when defining a product
type, is to use "structure" syntax. The key
idea is that we give names to fields, just as
in Java or Python, and we can then refer to
field values by name, rather than having to
write our own "projection functions". Instead,
projection functions are provided for us. This
is what's really happening in Java, too.
-/

namespace ex3

structure prod_nat_nat : Type :=
mk :: (fst : ℕ) (snd : ℕ)

/-
No more explicit projection functions!
-/

#eval prod_nat_nat.fst (prod_nat_nat.mk 3 4)
#eval prod_nat_nat.snd (prod_nat_nat.mk 3 4)
#eval (prod_nat_nat.mk 3 4).fst
#eval (prod_nat_nat.mk 3 4).snd

def p := (prod_nat_nat.mk 3 4)
#eval p.fst
#eval p.snd



end ex3


