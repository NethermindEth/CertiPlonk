import Lean.Meta
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

-- SAT
declare_syntax_cat ffval
declare_syntax_cat ffmodel
declare_syntax_cat ffsat

-- UNSAT
declare_syntax_cat ffunsat
declare_syntax_cat ffpolys
declare_syntax_cat ffred

section Syntax

-- SAT
syntax "FFV(" num "," num ")" : ffval
syntax "MODEL(" ident "," ffval ")" : ffmodel
syntax "SAT(" ffmodel+ ")" : ffsat

-- UNSAT
-- syntax "P(" num "," term ")" : ffpoly
syntax "POLYNOMIALS(" ("P(" num "," term ")")+ ")" : ffpolys
syntax "M(" num "," num ")" : ffred
syntax "S(" num "," num "," num "," term ")" : ffred
syntax "R(" num ";" (num"{" term "}"),+ ";" num ")" : ffred
syntax "UNSAT(" ("NO_CERTIFICATE" <|> num) ")" : ffunsat

-- Test
syntax "test_pol(" ffpolys ")" : term
syntax "test_red(" ffred ")" : term

#check_failure test_pol( POLYNOMIALS(P(42, x + 2) P(52, x + 3)) )
#check_failure test_red( M(1, 2) )
#check_failure test_red( S(1, 2, 3, z + 42) )
#check_failure test_red( R(1; 4{x + 1}, 42{z * 2}; 5) )

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
    let ml := ms.toList
    if ml.isEmpty then throw s!"Empty model" else
    return (← (ml.mapM parseVarAssignment)).toAssocList
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

section UNSAT

open Lean Elab Term Meta

opaque X : Nat → Nat := fun n => n

-- COMMENT FUTURE:
-- I think a better option is to create a parser for polynomials, something like:
-- monomial: num*(indets "*")+
-- indets: var("^" num)?
-- var: ident "_" num
-- Then we can extract all information we want and construct an MVPolynomial
-- Instead of parsing as a term and traversing TSyntax to extract the information
#check `(fun x1 x2 x3 => 3*x1^6 + 4*x2^7)
#check `(fun x1 x2 x3 => 3*(X 1)^6 + 4*(X 2)^7)

def elabPolynomial (s: TSyntax `term): MetaM Expr :=
  match s with
  | stx@`(ffpolys| POLYNOMIALS( $[P($n:num, $p:term)]* ) ) =>
    if n.isEmpty || p.isEmpty then throw $ .error stx "WRONG1" else
    _
  | stx@_ => throw $ .error stx "WRONG2"



end UNSAT

end Semantic

end CertiPlonk
