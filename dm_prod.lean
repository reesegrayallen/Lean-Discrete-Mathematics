/-
HOMEWORK 3
Reese Allen   (rga2uz)
CS2102 - Sullivan
-/


-- defining polymorphic ordered pair abstract data type

inductive dm_prod 
(α β : Type ): Type
| mk : α → β → dm_prod 

 
-- function defintions using lambda expressions, c-style (') and by cases ('')


/- FST -/
def fst {α β : Type } : (dm_prod α β) → α :=
λ (p : dm_prod α β),
match p with 
| dm_prod.mk x _ := x
end 

def fst' {α β : Type} (p: dm_prod α β) :=
match p with
| (dm_prod.mk α β) := α 
end 

def fst'' {α β : Type} : (dm_prod α β) → α 
| (dm_prod.mk x y) := x


/- SND -/
def snd {α β : Type } : (dm_prod α β) → β :=
λ (p : dm_prod α β),
match p with 
| dm_prod.mk _ y := y
end

def snd' {α β : Type} (p : dm_prod α β) :=
match p with
| (dm_prod.mk α β) := β
end 

def snd'' {α β : Type} : (dm_prod α β) → β 
| (dm_prod.mk x y) := y


/- SET_FST -/
def set_fst {α β : Type } {c : Type}: (dm_prod α β) → c → (dm_prod c β) :=
λ (p : dm_prod α β) (x : c ),
match p with
| dm_prod.mk _ y := dm_prod.mk x y
end 

def set_fst' {α β : Type} {c : Type} (p : dm_prod α β) (x : c) :=
match p with
|dm_prod.mk _ y := dm_prod.mk x y
end 

def set_fst'' {α β : Type} {c : Type}  : (dm_prod α β) → c → (dm_prod c β)
|(dm_prod.mk _ y) (c) := dm_prod.mk c y


/- SET_SND -/
def set_snd {α β : Type } {c : Type} : (dm_prod α β) → c → (dm_prod α c) :=
λ (p : dm_prod α β) (y : c),
match p with
| dm_prod.mk x _ := dm_prod.mk x y
end

def set_snd' {α β : Type} {c : Type} (p : dm_prod α β) (y : c) :=
match p with
|dm_prod.mk x _ := dm_prod.mk x y
end 

def set_snd'' {α β : Type} {c : Type} : (dm_prod α β) → c → (dm_prod α c)
| (dm_prod.mk x _) (c) := dm_prod.mk x c


/- SWAP -/
def swap {α β : Type } : (dm_prod α β ) → (dm_prod β α) :=
λ (p : dm_prod α β),
match p with 
| dm_prod.mk x y := dm_prod.mk y x
end 

def swap' {α β : Type } (p : dm_prod α β) :=
match p with 
|dm_prod.mk x y := dm_prod.mk y x
end 

def swap'' {α β : Type} : (dm_prod α β) → (dm_prod β α)
| (dm_prod.mk x y) := dm_prod.mk y x 




