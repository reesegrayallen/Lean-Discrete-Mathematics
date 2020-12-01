/-
A list abstract data type.
-/

namespace hidden

/-
A list is either empty (nil) or it is
"cons"tructed from an element, h, at
its "head" (h) and from a smaller list,
t, as its "tail".
-/

inductive list (α : Type) : Type
| nil {} : list
| cons (h : α) (t : list) : list

/-
Notes: α in final type is implicit, and 
from this Lean also infers α as the type
argument for the type of t.
-/

def l0 := @list.nil nat
def l1 := list.cons 0 l0
def l2 := list.cons 1 l1
def l3 := list.cons 2 l2
def l4 := list.cons 3 l2

def length (α : Type): list α → ℕ 
| list.nil := 0
| (list.cons h t) := 1 + length t


def append {α : Type} : list α → list α → list α 
| list.nil l2 := l2
| (list.cons h t) l2 := list.cons h (append t l2)

#reduce append l2 l4

end hidden



namespace mylist

inductive list (α : Type) : Type
| nil {} : list
| cons (h : α) (t : list) : list

def length {α : Type}: list α → nat 
| (list.nil) := 0
| (list.cons h t) := 1 + length t

def l0 := @list.nil nat
def l1 := list.cons 0 list.nil
def l2 := list.cons 1 l1
def l3 := list.cons 2 l2
def l4 := list.cons 3 l3

#eval length l0     -- expect 0
#eval length l4     -- expect 4

#check list

end mylist

def fib : ℕ → ℕ 
| 0 := 0
| 1 := 1
| (n'' + 2) := (fib n'') + fib (n''+1)

#eval fib 0     -- expect 0
#eval fib 1     -- expect 1
#eval fib 2     -- expect 1
#eval fib 3     -- expect 2
#eval fib 4     -- expect 3
#eval fib 10
#eval fib 20
#eval fib 21
#eval fib 23



def equals : ℕ → ℕ → bool
| 0 0 := tt
| _ 0 := ff
| 0 _ := ff
| (nat.succ n') (nat.succ m') := equals n' m'

#eval equals 0 0 
#eval equals 5 0
#eval equals 0 5
#eval equals 5 5
#eval equals 5 6


def sub : ℕ → ℕ → ℕ 
| 0 0 := 0
| n 0 := n
| 0 _ := 0
| (nat.succ n') (nat.succ m') := sub n' m'

#eval sub 0 0 -- exp 0
#eval sub 0 5 -- exp 0
#eval sub 5 0 -- exp 5
#eval sub 5 5 -- exp 0
#eval sub 7 4 -- exp 3
#eval sub 4 7 -- exp 0