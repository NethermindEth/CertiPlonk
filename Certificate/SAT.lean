import Batteries.Data.AssocList

open Batteries

namespace CertiPlonk

structure FiniteFieldValue where
    val : Nat
    size: Nat
deriving Repr

-- Temporary
abbrev Variable := String

abbrev Model := AssocList Variable FiniteFieldValue

end CertiPlonk
