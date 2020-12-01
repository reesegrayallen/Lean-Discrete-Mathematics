-- Ordered pairs
#eval prod.mk 2 3   -- represents (2, 3)
#eval prod.mk 2 tt  -- represents (2, tt)
#eval prod.mk tt ff -- represents (tt, ff)
#eval prod.mk       -- a pair of pairs
        (prod.mk 2 tt) 
        (prod.mk "Hello" 3)

-- Notation
#eval (2, 3)      -- prod.mk 2 3
#eval (2, tt)     -- etc.
#eval (tt, ff)
#eval ((2, tt), ("Hello", 3))    

-- Functions
#eval prod.fst ((2, tt), ("Hello", 3))   
#eval prod.snd ((2, tt), ("Hello", 3))   

-- Notation
#eval (2, 3).1      -- fst
#eval (2, 3).2      -- snd