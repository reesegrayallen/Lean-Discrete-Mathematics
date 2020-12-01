/-
Our own implementation of Lean's option type.
We call it dm_option to avoid any possible name
conflicts. 
-/

namespace hidden

/-
In the preceding example, an explicit type
argument for dm_option.none is required, even
though there is enough context for Lean to infer
that the type argument must be ℕ. If you want
Lean to infer such values when it can, put a
{} right after the name of the constructor.
-/

inductive dm_option (α : Type): Type
| none {} : dm_option      -- {} after constructor
| some (a : α) : dm_option

end hidden
