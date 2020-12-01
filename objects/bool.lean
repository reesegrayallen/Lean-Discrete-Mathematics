-- The terms of type bool
#eval bool.tt
#eval bool.ff

--Shorthand
#eval tt
#eval ff

-- Boolean not operator
#eval bnot tt
#eval bnot ff

-- Boolean and operator
#eval band tt tt
#eval band tt ff
#eval band ff tt
#eval band ff ff

-- Boolean or operator
#eval  bor tt tt
#eval  bor tt ff
#eval  bor ff tt
#eval  bor ff ff

-- Notation
#eval tt && ff  -- band
#eval tt || ff  -- bor