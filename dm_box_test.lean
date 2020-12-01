/-
HOMEWORK 3
Reese Allen   (rga2uz)
CS2102 - Sullivan
-/

import .dm_box 


def b1 := dm_box.mk 123
def b2 := dm_box.mk "stuck in a box"
def b3 := dm_box.mk (4,5) 
def b4 := dm_box.mk tt

#reduce unbox b1
#eval unbox b2
#reduce unbox b3
#reduce unbox b4
