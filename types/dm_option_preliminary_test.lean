import .dm_option_preliminary

open hidden 

def o1 := dm_option.none        -- Hmm. Check it.

#check o1


def o2 := dm_option.none bool   -- Probably right

def o3 := dm_option.some tt

#reduce p 0
#reduce p 1
#reduce p 0
-- etc

