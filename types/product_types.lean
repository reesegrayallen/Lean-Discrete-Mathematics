-- Product types, record types, structures, tuples
-- Polymorphic types and functions

namespace hidden

inductive prod_nat_nat : Type
| mk : ℕ → ℕ → prod_nat_nat

-- Polymorphic data type! Yay!
inductive prod_S_T (S T : Type) : Type
| mk: S → T → prod_S_T

def p1 := prod_nat_nat.mk 5 3
def p2 := prod_nat_nat.mk 4 0

-- Polymorphic

def p3 := prod_S_T.mk "String!" tt
def p4 := prod_S_T.mk tt 4
def p5 := prod_S_T.mk tt ff


-- inspector/getter
def fst_nat_nat : prod_nat_nat → ℕ :=
    λ (p : prod_nat_nat),
        match p with
        | (prod_nat_nat.mk x _) := x
        end

-- polymorphic
def fst_S_T (S T : Type) : (prod_S_T S T) → S :=
    λ (p : prod_S_T S T),
        match p with
        | (prod_S_T.mk x _) := x
        end


def snd_nat_nat : prod_nat_nat → ℕ :=
    λ (p : prod_nat_nat),
        match p with
        | (prod_nat_nat.mk _ y) := y
        end

-- polymorphic
def snd_S_T (S T : Type) : (prod_S_T S T) → T :=
    λ (p : prod_S_T S T),
        match p with
        | (prod_S_T.mk _ y) := y
        end

#reduce snd_S_T string bool p3


/-
Takes a pair, p, and a nat, n, and returns a new
pair, like p, but with n as its new first element.
-/
def set_fst_nat_nat : prod_nat_nat → ℕ → prod_nat_nat :=
    λ (p : prod_nat_nat) (n : ℕ),
        prod_nat_nat.mk n (snd_nat_nat p)

/-
-- polymorphic
Takes an S-T pair, p, and an S object, s, and returns a
new S-T pair like p but with s as a new first value
-/
def set_fst_S_T (S T : Type) : (prod_S_T S T) → S → prod_S_T S T :=
    λ (p : prod_S_T S T) (s : S),
        prod_S_T.mk s (snd_S_T S T p)


def set_snd_nat_nat : prod_nat_nat → ℕ → prod_nat_nat :=
   λ p n,
        prod_nat_nat.mk (fst_nat_nat p) n 

def swap_nat_nat : prod_nat_nat → prod_nat_nat :=
    λ p,
        match p with
        | (prod_nat_nat.mk x y) := prod_nat_nat.mk y x
        end


#eval fst_nat_nat p1
#reduce set_fst_nat_nat p1 9
#reduce set_snd_nat_nat p1 9
#reduce swap_nat_nat p1



-- distance
-- pairwise addition

end hidden