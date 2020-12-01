inductive dm_list (α : Type) : Type 
| nil {} : dm_list
| cons (h : α) (t : dm_list) : dm_list


def l0 := @dm_list.nil bool

def l1 := dm_list.cons
            tt
            l0

def l2 := dm_list.cons
            ff
            (
                dm_list.cons
                    tt
                    dm_list.nil 
            )


def length {α : Type}: dm_list α → ℕ 
| dm_list.nil := 0
| (dm_list.cons h t) := 1 + length t

#eval length l2


def append {α : Type}: dm_list α → dm_list α → dm_list α 
| (dm_list.nil) l2 := l2
| (dm_list.cons h t) l2 := dm_list.cons h (append t l2)

#reduce append l2 l2


def reverse {α : Type} : dm_list α →  dm_list α 
| dm_list.nil := dm_list.nil 
| (dm_list.cons h t) := append (reverse t)  (dm_list.cons h dm_list.nil)

#reduce reverse l2



























inductive dm_list (α : Type) : Type 
| nil : dm_list
| cons (h : α) (t : dm_list) : dm_list

def l0 := dm_list.nil bool

def l1 := dm_list.cons 
            tt
            (dm_list.nil bool)

def l2 := dm_list.cons
            tt
            (dm_list.cons
                ff
                dm_list.nil
            )


def length (α : Type) : dm_list α → nat 
| dm_list.nil := 0
| (dm_list.cons h t) := 1 + length t