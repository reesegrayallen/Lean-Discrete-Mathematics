import .propositional_logic_syntax_and_semantics
import .rules_of_reasoning

/-
Here we implement a propositional logic validity
checker as a function, is_valid: pExp → bool. This 
main routine is defined at the bottom of this file. 

As is good practice in the design of software and
of logical specifications and proofs, it is expressed
in terms of just a few lower-level abstractions that 
we then recursively define in the same "top-down" way
in the code that precedes this main routine.

For this class, you are required to fully understand
all aspects of this implementation. Understanding such
formal definitions is often best done by starting at 
the top (with the main routine, at the bottom of the
file), and working one's way "down" into each of the
sub-ordinate definitions. You then understand them in
the same top-down way. 

You may find the "go to definition" function in VSCode
to be useful here. If you right-click on an identifier
and select Go To Definition, VS Code will take you to
the definition of the selected identifier. Use this
code-browsing function will allow you to jump to the
code you need to get to in your "top-down" reading of
these definitions.
-/



/- 
***************************************************
 interpretations_for_n_vars : ℕ → list (var → bool).

 The follow set of definitions leads to this function.
 Given n : ℕ, it generates a list of 2^n interpretations,
 each a function of type var → bool, for n propositional
 logic variables.
***************************************************
-/

/-
Return mth bit from right in binary representation of n
Consider binary representation of 6. It's 101 (with an
infinite string of zeros to the left). The 0'th bit from
the right is 1. The 1'th bit from the right is 0. The
2'th bit from the right is 1. Then all the rest are 0.
-/
def mth_bit_from_right_in_binary_representation_of_n: ℕ → ℕ → ℕ  
| 0 n := n % 2              -- return rightmost bit
| (nat.succ m') n :=        -- shift right n and recurse on m
    mth_bit_from_right_in_binary_representation_of_n m' (n/2) 

/-
#eval mth_bit_from_right_in_binary_representation_of_n 5 5
#eval mth_bit_from_right_in_binary_representation_of_n 2 7
-/

/-
Covert 0 or 1 to ff and tt respectively. Any non-negative
argument is converted to ff. Introduces "let" construct in
Lean. Important concept in mathematics in general: give a
name to a value and then use name subsequently.
-/
def mth_bool_from_right_in_binary_representation_of_n : ℕ → ℕ → bool
| m n := 
    let r := mth_bit_from_right_in_binary_representation_of_n m n in
    (match r with
    | 0 := ff
    | _ := tt
    end)


/-
Return m'th row of truth table with n relevant variables.
That is, return m'th of 2^n interpretations. Remember that
an interpretation is a function from variables to Booleans.

The complication is that the set of variables is infinite
and we need to return something for any value of m and n.
So, if m (the row number) is greater than 2^n-1, we just
return an all-false interpretation. 

Furthermore, given an interpretation, we need to return a
Boolean value for any variable index. For indices greater
than n-1, we just return false.

The way to understand this visually is that any truth
table extends infinitely to the right, but is all false
values beyond the n variables we care about; and it also
extends infinitely far down, but every row is all false
beyond the 2^n rows that we care about.
-/
def mth_interpretation_for_n_vars (m n: ℕ) : (var → bool) :=
if (m >= 2^n)
    then λ v, ff
else
    λ v : var, 
    match v with
    | (var.mk i) := 
        if i >= n then ff
        -- return the right bool truth value for column i, row m
        else mth_bool_from_right_in_binary_representation_of_n i m
    end

/-
Now we define a function to generate a standard truth table (except
for the output column, i.e., just the input tows) as a list of 2^n 
interpretations.
-/

def interpretations_helper : nat → nat → list (var → bool)
| 0 n := list.cons (mth_interpretation_for_n_vars 0 n) list.nil
| (nat.succ m') n := 
    list.cons 
        (mth_interpretation_for_n_vars (nat.succ m') n)
        (interpretations_helper m' n)



def interpretations_for_n_vars : ℕ → list (var → bool)
| n := interpretations_helper (2^n-1) n





/- 
***************************************************
 map_pEval_over_truth_table_for_prop (p : pExp) (n : ℕ) : list bool

 Given a list of interpretations with n variables, this
 function evaluates the given expression, p, under each of
 the interpretations and returns the resulting list of bool
 values. This function uses the higher-order list.map function
 that we studied previous under "higher-order functions". The
 implementation of this function is somewhat tricky, so spend
 some extra time to puzzle out exactly how it's working. 
***************************************************
-/


def map_pEval_over_truth_table_for_prop (p : pExp) (n : ℕ) : list bool :=
list.map 
    (λ (i : var → bool), pEval p i)
    (interpretations_for_n_vars n)      -- truth table inputs, list of (var → bool)





/- 
***************************************************
set_of_variables_in_expression : pExp -> var_set

 Given a propositional logic expression, return the set
 of variables that it contains (without duplicates). The
 key idea is that literal values contain no variables, a
 variable expression contains exactly one variable, and
 expressions built using connectives contain the union 
 of the variables of the their constituent sub-expressions.

 Here we first implement the concept of a set of variables
 as a list of variables without duplicates. We define a few
 set operations, including membership test and set union. We
 then use these concepts to implement the main routine in
 this section by structural recursion over a given pExp.  
***************************************************
-/

/-
When adding a variable to a set represented as a list, we 
need to be sure it is not already in the set (list). So we 
need to be able to check if a given var is equal to another. 
We define two variables to be equal (to be the same variable)
if their *indices* (the natural numbers we give to var.mk 
when we creat a variable) are the same.
-/
def eq_var : var → var → bool
| (var.mk n) (var.mk m) := n = m


/-
We represent a set of variables as as a list without dups.
Note that here we're just giving an abstract name, var_set, 
to the *type*, list var. We call such a name a "type alias."
From now on we'll use the type var_set rather than list var,
so that our *intent* is clear.
-/
def var_set := list var 


/-
Make a new empty var set (represented as an empty list var).
-/
def mk_var_set : var_set := list.nil


/-
Set membership predicate:  return true if given var v is in 
given var set, otherwise return false. We implement this function
by structural recursion on the list. Note the use of pattern
matching on the Boolean result of comparing v with the head of
the given list (representing a set of variables), and returning
of a result accordingly.
-/
def in_var_set : var → var_set → bool
| v [] := ff
| v (h::t) := match (eq_var v h) with   -- note
                | tt := tt 
                | ff := in_var_set v t 
              end


/-
Return union of two var sets, l1 and l2. If l1 is empty we
just return l2. Here we assume that l2 already represents a
set, i.e., is a list with no duplicates. If l2 is not empty
we check if its head is in l2. If it's not, we "add" it to
the returned var_set (list); otherwise we don't. 

Note well: We introduce the use of if...then...else in Lean.
It works just as you'd expect.
-/
def var_set_union : var_set → var_set → var_set 
| [] l2 := l2
| (h::t) l2 :=  if (in_var_set h l2) 
                then var_set_union t l2
                else (h::var_set_union t l2)


/-
Here's the main routine: a function that, given an expression, 
e, returns the set of all and only the variables that appear
in e. Literal expressions contain no variables. A variable
expression contains one variable. And recursively a logical
expression built with a connective contains the union of 
the sets of variables of its constituent sub-expressions.
-/
open pExp
def set_of_variables_in_expression : pExp -> var_set
| pTrue  := []
| pFalse := []
| (pVar v) :=  [v]
| (pNot e) := set_of_variables_in_expression e
| (pAnd e1 e2) := 
        var_set_union 
            (set_of_variables_in_expression e1) 
            (set_of_variables_in_expression e2)
| (pOr e1 e2) := 
        var_set_union 
            (set_of_variables_in_expression e1) 
            (set_of_variables_in_expression e2)
| (pImp e1 e2) := 
        var_set_union 
            (set_of_variables_in_expression e1) 
            (set_of_variables_in_expression e2)
| (pIff e1 e2) := 
        var_set_union 
            (set_of_variables_in_expression e1) 
            (set_of_variables_in_expression e2)
| (pXor e1 e2) := 
        var_set_union 
            (set_of_variables_in_expression e1) 
            (set_of_variables_in_expression e2)


/-
The cardinality of a set is the number of elements it contains. As
we represent a set as a list *without duplicates*, the size of the
set is just the length of the list that represents it concretely. 
-/
def var_set_cardinality : var_set → ℕ 
| s := s.length

/-
The number of variables in an expression is thus the cardinality of
the set of variables it contains.
-/
def number_of_variables_in_expression : pExp → ℕ
| e := var_set_cardinality (set_of_variables_in_expression e)


/- 
***************************************************
Terminology: We say an interpretation, i, is a *model*
of a propositional logic expression, e, if and only if
e is true given the interpretation i. That is, i is a
model of e if and only if (pEval e i) is true.  
***************************************************
-/

/-
We say an interpretation is a "model" of an expression in
logic if it makes that expression true. 
-/
def isModel (i: var → bool) (e : pExp) : bool :=
    pEval e i


/- 
***************************************************
Now we build the main function, is_valid: pExp → bool. 
Given a pExp, e, we compute the number, n, of variables
it contains; we generate a list of the 2^n possible
interpretations for e; we map (pEval e) over this list
of interpretations; and finally we reduce the resulting
list of Boolean values to a final result, true if every
interpretation is a model of e, and false otherwise, by
doing a reduce/foldr of the list of Boolean values under
the band (Boolean and) operator. 
***************************************************
-/


/-
This function takes an expression, evaluates it for each
interpretation in a list of interpretations, and returns the
list of the resulting Boolean values.
-/
def map_pEval_over_interps : pExp → list (var → bool) → list bool
| e [] := []
| e (i::t) := (isModel i e :: map_pEval_over_interps e t)

/-
Reduce list of Booleans to a bool value, true if and only if 
every bool in a list of bools is tt. This is a special case of 
the higher-order foldr function that we studied under the 
section on higher-order functions.
-/
def foldr_and : list bool → bool
| [] := tt
| (h::t) := band h (foldr_and t)


/-
Here is our main definition. It precisely specifies what it
means for an expression in proposition logic to have the 
*property* of being valid.
-/
def is_valid (e : pExp) : bool :=
    let n := number_of_variables_in_expression e in 
    let is := interpretations_for_n_vars n in
    let rs := map_pEval_over_interps e is in 
    foldr_and rs


/-
For test cases, see the file, validity_test.lean.
-/