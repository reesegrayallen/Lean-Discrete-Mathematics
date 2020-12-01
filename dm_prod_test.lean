/-
HOMEWORK 3
Reese Allen   (rga2uz)
CS2102 - Sullivan
-/


import .dm_prod 

-- defining ordered pairs to use in testing 

def p1 := dm_prod.mk 5 2
def p2 := dm_prod.mk 3 tt
def p3 := dm_prod.mk ff tt

#check p1 -- dm_prod ℕ ℕ 
#check p2 -- dm_prod ℕ bool
#check p3 -- dm_prod bool bool

-- additional ordered pairs 
def p4 := dm_prod.mk "yes" "no"
def p5 := dm_prod.mk (3, 4) ff
def p6 := dm_prod.mk "seven" 7


-- test cases for fst
#reduce fst p1 
#reduce fst p2 
#reduce fst p3 

#eval fst' p4 
#reduce fst' p5 
#eval fst' p6 

#reduce fst'' p1 
#reduce fst'' p3 
#reduce fst'' p5 


-- test cases for snd
#reduce snd p1 
#reduce snd p2 
#reduce snd p3 

#eval snd' p4 
#reduce snd' p5
#eval snd' p6 

#reduce snd'' p1 
#reduce snd'' p3 
#reduce snd'' p5  


-- test cases for set_fst
#reduce set_fst p1 ff 
#reduce set_fst p2 (1, 100)
#reduce set_fst p3 1 

#reduce set_fst' p1 7
#reduce set_fst' p2 (1, 100) 
#reduce set_fst' p3 tt 

#reduce set_fst'' p1 (100, 1)
#reduce set_fst'' p2 ff 
#reduce set_fst'' p3 4

-- test cases for set_snd
#reduce set_snd p1 ff
#reduce set_snd p2 (1, 100)
#reduce set_snd p3 1 

#reduce set_snd' p1 7
#reduce set_snd' p2 (1, 100, 1000)
#reduce set_snd' p3 (tt, 5)

#reduce set_snd'' p5 (ff, tt)
#reduce set_snd'' p3 ff
#reduce set_snd'' p5 9


-- test cases for swap 
#reduce swap p1 
#reduce swap p2 
#reduce swap p3 

#reduce swap' p3 
#reduce swap' p5 
#reduce swap' p1 

#reduce swap'' p1 
#reduce swap'' p2 
#reduce swap'' p5 



















