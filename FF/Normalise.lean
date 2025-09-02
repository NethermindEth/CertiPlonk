import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.MvPolynomial.Basic
import Qq
import Lean

namespace EzPz

/--
Workaround to use a `term` parser instead of `location`.
-/
scoped syntax "spoon" Lean.Parser.Tactic.location : term 

open Lean Qq Parser Elab Tactic Meta 

/--
Dumps `goal`'s context `FVarId → Name` assignments.

- Debugging only.
-/
private def debugGoalDecls (goal : Option MVarId) : MetaM Unit := do
  let m := logInfo m!"ctx: {repr (((←getLCtx).fvarIdToDecl).map (fun ldec ↦ ldec.userName)).toArray}"
  match goal with
  | .none => m
  | .some goal => goal.withContext m  

/--
Dumps the main target.

- Debugging only.
-/
private def debugTarget (goal : MVarId) : MetaM Unit := goal.withContext do
  logInfo m!"target: {repr (←goal.getType)}"

def pOfZModEq (goal : MVarId) (e : Expr) : MetaM (Option ℕ) := goal.withContext do
  let (``Eq, ⟨.app (.const name _) k :: _⟩) := e.getAppFnArgs | return .none
  let k ← unsafe evalExpr ℕ q(ℕ) k
  return if name == ``ZMod then .some k else .none

def isZModEq (goal : MVarId) (e : Expr) : MetaM Bool := goal.withContext do
  pOfZModEq goal e <&> Option.isSome

def zModEqs (goal : MVarId) : MetaM (Array FVarId × Bool) := goal.withContext do
  let includeTarget ← isZModEq goal (←goal.getType)
  let Γmod ← (← getLocalHyps).filterM (inferType · >>= isZModEq goal)
  return (Γmod.map (·.fvarId!), includeTarget)

abbrev Location := TSyntax `Lean.Parser.Tactic.location

def locationOfName (name : Name) : MetaM Location := do
  let .ok stx := runParserCategory (←getEnv) `term s!"spoon at {name}"
    | throwError s!"{name} cannot be used as location."
  let `(spoon $l:location) := stx | throwError "Malformed location."
  `(location| $l)

/--
Empty list of names suffixes `⊢` regardless of `includeTarget`.
-/
def locationOfNames (names : Array Name) (includeTarget : Bool := false) : MetaM Location := do
  let locationStr := s!"spoon at {" ".intercalate (names.map Name.toString).toList} " ++
                     s!"{if includeTarget || names.isEmpty then "⊢" else ""}"
  let .ok stx := runParserCategory (←getEnv) `term locationStr
    | throwError s!"{names} cannot be used as location."
  let `(spoon $l:location) := stx | throwError "Malformed location."
  `(location| $l)

/--
If `fv.isNone`, yields `at ⊢`.
-/
def locationOfFVarId (goal : MVarId) (fv : Option FVarId) : MetaM Location := goal.withContext do
  match fv with
  | .none => locationOfNames #[] true
  | .some fv => locationOfNames #[(←fv.getUserName)]

def exprMapOfFVarIDsAndTarget
  (goal : MVarId) (hyps : Array FVarId) (includeTarget : Bool) : MetaM (Std.HashMap (Option FVarId) Expr) := goal.withContext do
  let mut result := hyps.map Option.some |>.zip <| hyps.map (LocalDecl.type ∘ (← getLCtx).get!)
  if includeTarget then result := result.push (.none, ←goal.getType)
  return Std.HashMap.ofList result.toList

section

open Lean.Grind.CommRing

partial def grindMonoOfZMod {kQ : Q(ℕ)}
  (eQ : Q(ZMod $kQ)) (indetMap : Std.HashMap Name Var) : MetaM (Option Mon) := do
  let grindMonoOfZMod e := grindMonoOfZMod e indetMap
  match eQ with
  | ~q($xQ * $yQ) => do
    let .some x ← grindMonoOfZMod xQ | return .none
    let .some y ← grindMonoOfZMod yQ | return .none
    return .some (x.concat y)
  | ~q($xQ⁻¹ ^ $expQ) =>
    -- We match this explicitly to simplify the logic of `$indetQ ^ $expQ`.
    logError m!"Monomials must of the form `<indet>`, `<indet> * <indet>` or `<indet>^K`.\n{eQ} is impermissible."
    return .none
  | ~q($indetQ ^ $expQ) =>
    -- Qq is unhappy about matching on `indetQ` here.
    let name ← indetQ.fvarId?.mapM (·.getUserName) <&> (Option.getD (dflt := indetQ.constName))
    return .some <| .mult ⟨indetMap[name]!,← unsafe evalExpr ℕ q(ℕ) expQ⟩ .unit
  | ~q(@OfNat.ofNat (ZMod _) $_nQ $_instQ) =>
    let n ← unsafe evalExpr (ZMod (← unsafe evalExpr ℕ q(ℕ) kQ)) q(ZMod $kQ) eQ
    if n != 1 then return .none
    return .some .unit
  | ~q($_symQ) => grindMonoOfZMod q($eQ^1)
  | _ => logError m!"Unrecognised ZMod eq shape: {eQ}."; return .none

partial def grindPolyOfZMod {kQ : Q(ℕ)}
  (eQ : Q(ZMod $kQ)) (indetMap : Std.HashMap Name Var) : MetaM (Option Poly) := do
  let .succ _ ← unsafe evalExpr ℕ q(ℕ) kQ | return .none
  let grindPolyOfZMod e := grindPolyOfZMod (kQ := kQ) e indetMap
  match eQ with
  | ~q($xQ + $yQ) =>
    let .some x ← grindPolyOfZMod xQ | return .none
    let .some y ← grindPolyOfZMod yQ | return .none
    return .some (x.combine y)
  | ~q($xQ - $yQ) =>
    let .some x ← grindPolyOfZMod xQ | return .none
    let .some y ← grindPolyOfZMod yQ | return .none
    return .some (x.combine (y.mulConst (-1)))
  | ~q((@OfNat.ofNat (ZMod _) $nQ $_instQ) * $monoQ) =>
    let n ← unsafe evalExpr ℕ q(ℕ) nQ
    let .some mon ← grindMonoOfZMod q($monoQ) indetMap | return .none
    return .some (Poly.num 0 |>.insert n.cast mon)
  | ~q($monoQ * (@OfNat.ofNat (ZMod _) $_nQ $_instQ)) =>
    -- Ouch, cannot do `name@pattern` in `~q()`.
    grindPolyOfZMod q((@OfNat.ofNat (ZMod _) $_nQ $_instQ) * $monoQ)
  | ~q(@OfNat.ofNat (ZMod _) $nQ $_instQ) => grindPolyOfZMod q($eQ * 1)
  | ~q(@Neg.neg (ZMod _) $_instQ₁ (@OfNat.ofNat (ZMod _) $nQ $_instQ₂)) =>
    return .some (Poly.num (Int.negOfNat (← unsafe evalExpr ℕ q(ℕ) nQ)))
  | ~q(-$polyQ) => Option.map (Poly.mulConst (-1)) <$> grindPolyOfZMod polyQ
  | ~q($monoQ) =>
    let .some mon ← grindMonoOfZMod monoQ indetMap | return .none
    return .some (Poly.ofMon mon)
  | _ => logError m!"Unrecognised ZMod eq shape: {eQ}."; return .none

def grindPolyOfZModEq (eQ : Q(Prop)) (indetMap : Std.HashMap Name ℕ) : MetaM (Option Poly) := do
  match eQ with
  | ~q(@Eq (ZMod $k) $lhs 0) => grindPolyOfZMod lhs indetMap
  | _ => throwError "Expected _ = 0. Got: {eQ}"

/--
In a polynomial `xc₁ * xc₂ * ... * xcₖ + xc₁' * xc₂' * ... * xcⱼ' + ... + xc₁'' * ... * xcₗ''`,
returns `[xcₖ, xcₖ', xcₗ'']`.
-/
partial def isolatedConstantsOfMonomials {kQ : Q(ℕ)} (eQ : Q(ZMod $kQ)) : MetaM (Array ℕ) := do
  let .succ _ ← unsafe evalExpr ℕ q(ℕ) kQ | return #[]
  match eQ with
  | ~q($xQ + $yQ) =>
    let x ← isolatedConstantsOfMonomials xQ
    let y ← isolatedConstantsOfMonomials yQ
    return x ++ y
  | ~q($xQ - $yQ) =>
    isolatedConstantsOfMonomials q($xQ + $yQ)
  | ~q(-$monoQ) =>
    isolatedConstantsOfMonomials q($monoQ)
  | ~q($monoQ) =>
    let ~q(_ * @OfNat.ofNat (ZMod _) $nQ $_instQ) := monoQ | return #[]
    return #[← unsafe evalExpr ℕ q(ℕ) nQ]
  
end

/--
`x = .none` means target, which we name `⊢`.
-/
def userNameOfFvarId? (x : Option FVarId) : MetaM Name :=
  match x with | .none => return Name.mkSimple "⊢" | .some x => x.getUserName >>= pure

structure NormaliseST where
  goal : MVarId
  goals : Array MVarId

abbrev MTac := MVarId → MetaM (List MVarId)

/--
Similar to `TacticM`.
-/
abbrev MTacM := StateT NormaliseST MetaM

def NormaliseST.ofGoal (goal : MVarId) : NormaliseST :=
  {
    goal := goal
    goals := #[]
  }

/--
Descend an `MTacM` into `MVarId → MetaM (List MVarId)`, where the latter is used at interface
boundaries with existing functionality.

- see also `liftMTac`
-/
def MTacM.toMTac (m : MTacM Unit) : MTac :=
  fun goal ↦ do
    let (_, {goal := goal, goals := goals, ..}) ← m.run (NormaliseST.ofGoal goal)
    pure (goal :: goals.toList)

/--
Similar to `TacticM.withMainContext`.
-/
def withMainContext {α : Type} (m : MTacM α) : MTacM α := do (←get).goal.withContext m

/--
Evaluates to all `ZMod k` indeterminates of the system and enforces uniform `k`.
-/
def consistentIndeterminates : MTacM (Option (Array Name × ℕ)) := do
  let mut mod : Option Nat := .none
  let mut indets : Array Name := #[]
  for hyp in ← getLocalHyps do
    let (``ZMod, #[(.app (.app _ kexpr@(.lit _)) _)]) := (←inferType hyp).getAppFnArgs | continue
    let k ← unsafe evalExpr ℕ q(ℕ) kexpr
    let name ← hyp.fvarId!.getUserName
    match mod with
    | .none => mod := .some k
               indets := indets.push name
    | .some k' => if k == k'
                  then indets := indets.push name
                  else return .none
  return pure (indets.qsort (·.toString < ·.toString), mod.getD 0)

def indeterminatesMap : MTacM (Std.HashMap Name ℕ) := do
  let .some (indets, _) ← consistentIndeterminates | throwError "The system is inconsistent."
  return Std.HashMap.ofList indets.zipIdx.toList

def indeterminates : MTacM (Array Name) := indeterminatesMap >>= (return ·.keys.toArray)

def systemMod : MTacM ℕ := do
  let .some (_, mod) ← consistentIndeterminates | throwError "The system is inconsistent."
  return mod

/--
Lift a function of `MVarId` to operate over `MTacM` instead. The domain determines the main goal.
-/
def lift {α : Type} (f : MVarId → MetaM α) : MTacM α := do f (←get).goal

/--
Dual of `MTacM.toMTac`.
-/
def liftMTac (f : MTac) : MTacM Unit := do
  match ← lift f with
  | [] => pure ()
  | goal :: goals => set {NormaliseST.ofGoal goal with goals := goals.toArray ++ (←get).goals}

def locationOfZModEqs : MTacM Location := do
  let (zmodEqs, isTargetZmodEq) ← lift zModEqs
  locationOfNames (←zmodEqs.mapM (·.getUserName)) isTargetZmodEq

def locationsOfZModEqs : MTacM (Array Location) := do
  let (zmodEqs, isTargetZmodEq) ← lift zModEqs
  let hyps ← zmodEqs.mapM fun hyp ↦ do locationOfName (←hyp.getUserName)
  let target ← (if isTargetZmodEq then do pure #[←`(location|at ⊢)] else pure #[])
  return hyps ++ target

/--
TODO: Panics with unrecognised hypotheses. Fix one day.
-/
def exprMap : MTacM (Std.HashMap (Option FVarId) Expr) := do
  let (hyps, isTargetZmodEq) ← lift zModEqs
  let mut result := hyps.map Option.some |>.zip <| hyps.map (LocalDecl.type ∘ (←getLCtx).get!)
  if isTargetZmodEq then result := result.push (.none, ←(←get).goal.getType)
  return Std.HashMap.ofList result.toList

def foreachZmodExpr (f : Option FVarId → Expr → MTacM Unit) : MTacM Unit := do
  for (hyp, e) in ←exprMap do f hyp e

def runTactic' (tacticCode : Syntax) (mvarId : MVarId) : MetaM (List MVarId) :=
  (·.1) <$> runTactic mvarId tacticCode

/--
ZMod equations have specific shape requirements, careful whence this is called.

- The leading coefficient of the least monomial with respect to the grevlex order,
  as enforced by construction of `Poly`.
-/
def leadingCoeff (e : Expr) : MTacM ℤ := do
  let .some grindPoly ← grindPolyOfZModEq e (←indeterminatesMap)
    | throwError "Failed to compute LC of: {e}"
  return grindPoly.lc

def ring_nf : MTacM Unit := withMainContext do
  for l in ←locationsOfZModEqs do
  liftMTac ∘ runTactic' <| (←`(tactic| try (ring_nf $l:location)))

def subst_eqs : MTacM Unit := withMainContext do
  liftMTac ∘ runTactic' <| (←`(tactic| subst_eqs))

/--
Divides all ZMod equations by the leading coefficient. Discharges all necessary injectivity 
obligations.
-/
def divideByLC : MTacM (Std.HashMap Name (ℤ × ℕ)) := withMainContext do
  let env ← getEnv
  let mod ← systemMod
  let modS := Syntax.mkNumLit s!"{mod}"
  let inverseOf (z : ℤ) : ℕ := ((z.cast : ZMod mod).cast : ℤ).toNat
  let mut lcInfo : Std.HashMap Name (ℤ × ℕ) := {}
  for (hyp, e) in ←exprMap do
    let lcZ ← leadingCoeff e
    let lc : ℕ := inverseOf lcZ
    let (_, inverse) := Nat.xgcd (←systemMod) lc
    lcInfo := lcInfo.insert (←userNameOfFvarId? hyp) (lcZ, inverseOf inverse)
    let .ok lcZStx := runParserCategory env `term s!"{lcZ}" | throwError s!"{lcZ} is not a valid number."
    let lcZStx : Term := ⟨lcZStx⟩
    let loc ← locationOfNames (← liftM <| hyp.mapM FVarId.getUserName).toArray
    let goals ← runTactic' (←`(tactic|apply_fun (·/($lcZStx : ZMod $modS)) $loc:location)) (←get).goal    
    match goals with
    | [goal] => modify ({· with goal := ← liftM (goal.modifyTarget instantiateMVars)})
    | [goal, injective] =>
      modify ({· with goal := ← liftM (goal.modifyTarget instantiateMVars)})
      try let [] ← runTactic' (←`(tactic|(intros x y h
                                          try simp at h
                                          try rwa [div_left_inj'] at h
                                          grind)))
                              injective
                     | throwError "Discharging tactic didn't solve all goals."
      catch e => throwError "Cannot solve: {injective}\nWhy:\n{e.toMessageData}"
    | _ => throwError m!"Did not expect {goals.length} goals after `apply_fun`."
  return lcInfo

lemma neg_inv_mul_cancel₀ {α : Type*} [Field α] {x : α} (h : x ≠ 0)
  : (-x)⁻¹ * x = -1 := by simp only [inv_neg, neg_mul, neg_inj]; exact inv_mul_cancel₀ h

/--
Discharge `-C = C'` finite field equalities that are not `rfl`.
-/
local elab "neg_inv_mul_cancel" : tactic => do
  evalTactic (←`(tactic| (unfold_projs
                          simp [ZMod.inv, ZMod.val, ZMod, Nat.gcdA, Nat.xgcd, Nat.xgcdAux]
                          try rfl)))

/--
Normalisation after division by the leading coefficient. Cancels `a⁻¹ * a` and `-a⁻¹ * a`.
-/
def cancelMultiplicands (lcInfo : Std.HashMap Name (ℤ × ℕ)) : MTacM Unit := withMainContext do
  for (hyp, e) in ←exprMap do
    have e : Q(Prop) := e
    let ~q(@Eq (ZMod $k) $lhs 0) := e | throwError s!"{e} must have rhs = 0."
    let res ← isolatedConstantsOfMonomials (kQ := q($k)) lhs
    if res.isEmpty then continue
    let hyp ← userNameOfFvarId? hyp
    let mkRewriteFrom (lem loc : String) : String := s!"try rw [{lem}] at {loc}"
    let (lc, _) := lcInfo[hyp]!
    let rewrites :=
      "(\n" ++
      (
        (res.map (fun n ↦ mkRewriteFrom s!"@mul_assoc _ _ _ ({lc})⁻¹ {n}" s!"{hyp}") ++
         #[
           mkRewriteFrom "inv_mul_cancel₀ (by grind)" s!"{hyp}",
           mkRewriteFrom "mul_one" s!"{hyp}",
           mkRewriteFrom "neg_inv_mul_cancel₀ (by grind)" s!"{hyp}",
           mkRewriteFrom "mul_neg_one" s!"{hyp}"
         ])
      |>.toList.intersperse "\n").foldl (·++·) "" ++
      "\n)"
    let .ok stx := runParserCategory (←getEnv) `tactic rewrites | throwError "{rewrites} is not a valid tactic."
    liftMTac <| runTactic' stx

/--
Normalises inverses in a finite field.
-/
def normaliseConstants (lcInfo : Std.HashMap Name (ℤ × ℕ)) : MTacM Unit := withMainContext do
  let modS := Syntax.mkNatLit (←systemMod)
  let env ← getEnv
  for (name, const, inverse) in lcInfo do
    if inverse == 1 then continue
    let .ok const' := runParserCategory env `term s!"{((const.cast : ZMod (←systemMod)).cast : ℤ).toNat}" | throwError s!"{const} is not a valid number."
    let const' : Term := ⟨const'⟩
    let inverse := Syntax.mkNatLit inverse
    let l ← locationOfNames (if name == Name.mkSimple "⊢" then #[] else #[name])
    let .ok const := runParserCategory env `term s!"{const}" | throwError s!"{const} is not a valid number."
    let const : Term := ⟨const⟩
    withMainContext ∘ liftMTac ∘ runTactic' <|
      (←`(tactic| try rw [show ($const : ZMod $modS) = $const' by neg_inv_mul_cancel] $l:location))
    withMainContext ∘ liftMTac ∘ runTactic' <|
      (←`(tactic| try rw [show (($const')⁻¹ : ZMod $modS) = $inverse from ZMod.inv_eq_of_mul_eq_one _ _ _ rfl] $l:location))

/--
TODO: This is likely insufficient.
-/
def clearRHS : MTacM Unit := withMainContext do
  let l ← locationOfZModEqs
  liftMTac ∘ runTactic' <| (←`(tactic| (try ring_nf $l:location
                                        try rw [←sub_eq_zero] $l
                                        try ring_nf $l:location)))

def normaliseSystem : MTacM Unit := do
  ring_nf
  subst_eqs
  clearRHS
  let lcInfo ← divideByLC
  ring_nf
  cancelMultiplicands lcInfo
  normaliseConstants lcInfo
  ring_nf

elab "normalise_system" : tactic => liftMetaTactic normaliseSystem.toMTac

example {x y z : ZMod 394357} [Fact (Nat.Prime 394357)]
  (h : z * x * 9 * y + x * 9 - z * 2 = 3)
  (h' : z * x * (-9) * y + x * 9 - z * 2 = 3)
  (h'' : z * x * (-5) * y + x * 9 - z * 2 = 3)
  (h₁ : x * 4 * y * 4 * x + z^4 = 2)
  (h₂ : z^3 + x^2 + x^2 = 0)
  (h₃ : 5 * x * y + y * x + 4 * x^2 + 5 * z^3 * x = 0)
  (h₄ : x * y + y * x + z^3 * x = 0)
  (h₆ : 2 * 394356 * x = 0)
  : x - 42 = 0 := by
  normalise_system
  sorry

  
end EzPz
