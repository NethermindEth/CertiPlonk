import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit

opaque undefined : Prop

lemma assert_eq [Field F] (a b: F):
  (a - b = 0) = (a = b)
:= by grind

section BusIndices
  abbrev ExecutionBus : ℕ := 0
  abbrev MemoryBus : ℕ := 1
  abbrev RangeCheckerBus : ℕ := 4
  abbrev ReadInstructionBus : ℕ := 8
  abbrev BitwiseBus : ℕ := 9
  abbrev RangeTupleCheckerBus : ℕ := 11

  lemma execution_bus_simplifcation:
    (if index = 0 then a else b) =
    if index = ExecutionBus then a else b
  := rfl

  lemma memory_bus_simplifcation:
    (if index = 1 then a else b) =
    if index = MemoryBus then a else b
  := rfl

  lemma range_checker_bus_simplifcation:
    (if index = 4 then a else b) =
    if index = RangeCheckerBus then a else b
  := rfl

  lemma read_instruction_bus_simplifcation:
    (if index = 8 then a else b) =
    if index = ReadInstructionBus then a else b
  := rfl

  lemma bitwise_bus_simplifcation:
    (if index = 9 then a else b) =
    if index = BitwiseBus then a else b
  := rfl

  lemma range_tuple_checker_bus_simplifcation:
    (if index = 11 then a else b) =
    if index = RangeTupleCheckerBus then a else b
  := rfl
end BusIndices
