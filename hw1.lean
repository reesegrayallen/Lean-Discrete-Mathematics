/-
Homework #1
Reese Allen, rga2uz
20Sp CS 2102-001
-/


-- namespace for identifiers in this file
-- namespace ends below, see end of file

namespace hidden


/-
An abstract data type combines a data type 
and a set of functions that operate on values 
of that type. As we're implementing a Boolean
algebra ADT, we define a bool data type and a
set of standard Boolean operators (functions). 
-/


/-  *********
    DATA TYPE
    ********* -/


inductive dm_bool : Type
| dm_tt : dm_bool
| dm_ff : dm_bool

-- Data type has it's own namespace

open dm_bool

-- Some examples of definitions using this type

def b1 := dm_tt
def b2 := dm_ff

/-  *********
    FUNCTIONS
    ********* -/

-- a unary function, a.k.a, operator

/-
Truth table for "not"

 ARG    RES
------|------
dm_tt | dm_ff
------|------
dm_ff | dm_tt
------|------
-/


def dm_not : dm_bool → dm_bool := 
    λ (b : dm_bool), 
        match b with
        | dm_tt := dm_ff
        | dm_ff := dm_tt
        end 


-- binary functions, a.k.a., operators 

/-
Truth table for "and"
b1 b2 res
---------
tt tt tt
tt ff ff
ff tt ff
ff ff ff
-/


def dm_and : dm_bool → dm_bool → dm_bool :=
    λ (b1 b2 : dm_bool),
        match b1, b2 with
        | dm_tt, dm_tt := dm_tt
        | dm_tt, dm_ff := dm_ff
        | dm_ff, dm_tt := dm_ff
        | dm_ff, dm_ff := dm_ff
        end
#reduce dm_and dm_tt dm_tt

-- A shorter though less clear definition
def dm_and' : dm_bool → dm_bool → dm_bool :=
   λ (b1 b2 : dm_bool),
    match b1 with
    | dm_tt := b2
    | _ := dm_ff
    end

-- The definition of "or" is similar
def dm_or : dm_bool → dm_bool → dm_bool :=
   λ (b1 b2 : dm_bool),
    match b1 with
    | dm_ff := b2
    | _ := dm_tt
    end



/-
Truth table for "identity function"

 ARG    RES
------|------
dm_tt | dm_tt
------|------
dm_ff | dm_ff
------|------
-/ 

def dm_id : dm_bool → dm_bool :=
    λ (b : dm_bool), 
        match b with 
        | dm_tt := dm_tt
        | dm_ff := dm_ff
        end 



/-
Truth table for "xor" (exclusive-or) ; true only when inputs differ

b1 b2 res
---------
tt tt ff
tt ff tt
ff tt tt
ff ff ff

-/

def dm_xor : dm_bool → dm_bool → dm_bool := 
    λ (b1 b2 : dm_bool),
    match b1, b2 with
    | dm_tt, dm_ff := dm_tt
    | dm_ff, dm_tt := dm_tt
    | _ , _ := dm_ff
    end 





/-
Truth table for "nand" ; essentially the opposite of and

b1 b2 res
---------
tt tt ff
tt ff tt
ff tt tt
ff ff tt

-/

def dm_nand : dm_bool → dm_bool → dm_bool :=
    λ (b1 b2 : dm_bool),
    match b1, b2 with
    | dm_tt, dm_tt := dm_ff
    | _ , _ := dm_tt
    end 



/-
Truth table for "implies"

b1 b2 res
---------
tt tt tt
tt ff ff
ff tt tt
ff ff tt

-/

def dm_implies : dm_bool → dm_bool → dm_bool :=
    λ (b1 b2 : dm_bool),
    match b1, b2 with
    | dm_tt, dm_ff := dm_ff
    | _ , _ := dm_tt
    end 


/-
Truth table for "equivalent"

b1 b2 res
---------
tt tt tt
tt ff ff
ff tt ff
ff ff tt

-/

def dm_equiv : dm_bool → dm_bool → dm_bool :=
    λ (b1 b2 : dm_bool),
    match b1, b2 with
    | dm_tt, dm_tt := dm_tt
    | dm_ff, dm_ff := dm_tt
    | _ , _ := dm_ff
    end 




end hidden