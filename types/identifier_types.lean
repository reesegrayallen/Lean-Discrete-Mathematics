/-
Identifiers, bindings, types
-/

/-
Identifiers are terms in Lean. All terms have
types. So identifiers have types. The type of
an identifier is the type of the term to which
the identifier is bound.
-/

def b' : bool := (tt : bool) -- types explicit
def b := tt                -- types inferred

-- type inference

def s : string := "I love logic!"
def n : ℕ := 1
def n' := 1    -- Lean assumes (1 : ℕ)

