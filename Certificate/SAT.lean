import Batteries.Data.AssocList

open Batteries

namespace CertiPlonk

structure FiniteFieldValue where
  val : Nat
  size: Nat
deriving Repr

abbrev Variable := String -- Temporary
abbrev Model := AssocList Variable FiniteFieldValue

end CertiPlonk
