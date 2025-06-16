import Mathlib.Lean.CoreM
import Certificate.SAT

open Lean in
unsafe def CertiPlonk.withImportModules {α : Type} (imports : Array Import) (opts : Options)
    (act : Environment → IO α) (trustLevel : UInt32 := 0) : IO α := do
  let env ← importModules (loadExts := true) imports opts trustLevel
  try act env finally env.freeRegions

open Lean Core in
def CertiPlonk.CoreM.withImportModules {α : Type} (modules : Array Name) (run : CoreM α)
    (searchPath : Option SearchPath := none) (options : Options := {})
    (trustLevel : UInt32 := 0) (fileName := "") :
    IO α := unsafe do
  if let some sp := searchPath then searchPathRef.set sp
  CertiPlonk.withImportModules (modules.map ({ module := · })) options (trustLevel := trustLevel)
    fun env =>
      let ctx := {fileName, options, fileMap := default}
      let state := {env}
      Prod.fst <$> (CoreM.toIO · ctx state) do
        run

namespace CertiPlonk

-- scoped instance : MonadLift IO (EIO String) := ⟨IO.toEIO (s!"{·}")⟩
-- scoped instance : MonadLift (EIO String) IO := ⟨EIO.toIO (s!"{·}")⟩

declare_syntax_cat ffval
declare_syntax_cat ffmodel
declare_syntax_cat ffsat

section Syntax

syntax "FFV(" num "," num ")" : ffval
syntax "MODEL(" ident "," ffval ")" : ffmodel
syntax "SAT(" ffmodel+ ")" : ffsat

end Syntax

section Semantic

open Lean

section SAT

def parseFFV (s: TSyntax `ffval) : Except String FiniteFieldValue :=
  match s with
  | `(ffval| FFV($n1:num, $n2:num)) => return ⟨n1.getNat, n2.getNat⟩
  | stx => throw s!"Unrecognised finite field value: {stx}"

def parseVarAssignment (s: TSyntax `ffmodel) : Except String (Variable × FiniteFieldValue) := do
  match s with
  | `(ffmodel| MODEL($var:ident, $ffv:ffval)) =>
    match var.getId with
    | .str _ s => return ⟨s, (← parseFFV ffv)⟩
    | x => throw s!"Unrecognized variable {repr x}"
  | stx => throw s!"Unrecognised variable model: {stx}"

def parseModel (s: TSyntax `ffsat) : Except String Model := do
  match s with
  | `(ffsat| SAT($ms:ffmodel*)) =>
    match ms.toList with
    | [] => throw s!"Empty model"
    | ms => return (← (ms.mapM parseVarAssignment)).toAssocList
  | stx => throw s!"Unrecognised SAT: {stx}"

-- unsafe def checkFFV (input : String) : IO FiniteFieldValue :=
--   CertiPlonk.withImportModules #[`Certificate] Options.empty λ env ↦ do
--     match Parser.runParserCategory env `ffval input with
--     | .ok stx => match parseFFV ⟨stx⟩ with
--                  | .ok m => pure m
--                  | .error _ => pure ⟨1,2⟩
--     | .error _ => pure ⟨1,2⟩

-- unsafe def checkAssignment (input : String) : IO (Variable × FiniteFieldValue) :=
--   CertiPlonk.withImportModules #[`Certificate] Options.empty λ env ↦ do
--     match Parser.runParserCategory env `ffmodel input with
--     | .ok stx => match parseVarAssignment ⟨stx⟩ with
--                  | .ok m => pure m
--                  | .error _ => pure ⟨"a",⟨1,2⟩⟩
--     | .error _ => pure ⟨"a",⟨1,2⟩⟩

-- unsafe def checkSAT (input : String) : IO Model :=
--   CertiPlonk.withImportModules #[`Certificate] Options.empty λ env ↦ do
--     match Parser.runParserCategory env `ffsat input with
--     | .ok stx => match parseModel ⟨stx⟩ with
--                  | .ok m => pure m
--                  | .error _ => pure [⟨"a",⟨1,2⟩⟩].toAssocList
--     | .error _ => pure [⟨"a",⟨1,2⟩⟩].toAssocList

-- #eval checkSAT "
-- SAT(
-- MODEL(b, FFV(42,43))
-- MODEL(c, FFV(55,56))
-- )
-- "

end SAT

end Semantic

end CertiPlonk
