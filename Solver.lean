import Lean.Data.AssocList

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Qq

import CMvPolynomial.CMvMonomial
import CMvPolynomial.CMvPolynomial

open Lean Qq CPoly

namespace EzPz

scoped syntax "spoon" Lean.Parser.Tactic.location : term

open Lean Parser Elab Tactic Meta

def isZModEq (e : Expr) : TacticM Bool := withMainContext do
  let (_, ⟨.app (.const name _) _ :: _⟩) := e.getAppFnArgs | return false
  pure (name == ``ZMod)

def zModEqs : TacticM (Array FVarId × Bool) := withMainContext do
  let includeTarget ← isZModEq (← getMainTarget)
  let Γmod ← (← getLocalHyps).filterM (inferType · >>= isZModEq)
  return (Γmod.map (·.fvarId!), includeTarget)

def locactionOfFVarIDsAndTarget
  (hyps : Array FVarId × Bool) : TacticM (TSyntax `Lean.Parser.Tactic.location) := withMainContext do
  let (hyps, includeTarget) := hyps
  let ΓmodNames ← hyps.mapM (·.getUserName <&> Name.toString)
  let .ok stx := runParserCategory (←getEnv) `term
                   s!"spoon at {" ".intercalate ΓmodNames.toList}{if includeTarget then "⊢" else ""}"
                     | throwError s!"{ΓmodNames} cannot be used as 'location'."
  -- Lean is not happy with `location` being used in `runParserCategory`, so we add a step via `term`.
  let `(spoon $l:location) := stx | throwError "Malformed location."
  `(location|$l)

def expressionsOfFVarIDsAndTarget
  (hyps : Array FVarId × Bool) : TacticM (Std.HashMap (Option FVarId) Expr) := withMainContext do
  let (hyps, includeTarget) := hyps
  let mut result := hyps.map Option.some |>.zip <| hyps.map (LocalDecl.type ∘ (← getLCtx).get!)
  if includeTarget then result := result.push (.none, ←getMainTarget)
  return Std.HashMap.ofList result.toList

def indeterminates : TacticM (Array String) := do
  let zmodHyps ← (← getLocalHyps).filterM (inferType · <&> (·.getAppFnArgs.1 == ``ZMod))
  zmodHyps.mapM (·.fvarId!.getUserName <&> Name.toString)  

instance {n : ℕ} : ToExpr (CMvMonomial n) :=
  let arityQ : Q(ℕ) := mkNatLit n
  {
    toExpr mono := mkApp3 (mkConst ``CMvMonomial.mk) arityQ (toExpr mono.1) q(Eq.refl $arityQ)
    toTypeExpr := mkApp2 (mkConst ``Vector [0]) q(ℕ) arityQ
  }

/--
TODO: Note this assumes that `nf_ring` puts `ZMod` equations in a certain format, as determined
      by what shapes of terms we are matching on.

- We take `arity` in addition to `indetMap` even if we enforce `indetMap.size = arity`.
  This is to help articulate the Q-return type of the function.
-/
partial def cMvMonoOfZMod {kQ : Q(ℕ)}
  (eQ : Q(ZMod $kQ)) (indetMap : Std.HashMap String ℕ) (arityQ : Q(ℕ)) :
  MetaM (Option Q(CMvMonomial $arityQ)) := do
  assert! (indetMap.size == (← unsafe evalExpr ℕ q(ℕ) arityQ))
  let cMvMonoOfZMod e := cMvMonoOfZMod e indetMap arityQ
  match eQ with
  | ~q($xQ * $yQ) => do
    -- Assumes x * x was normalised to x^2 by `ring_nf`.
    let .some xQ ← cMvMonoOfZMod xQ | return .none
    let .some yQ ← cMvMonoOfZMod yQ | return .none
    let evalMono e := unsafe evalExpr (CMvMonomial indetMap.size) q(CMvMonomial $arityQ) e
    return .some (toExpr ((← evalMono xQ) * (← evalMono yQ)))
  | ~q($indetQ ^ $eQ) => do
    let finIndetQ : Q(ℕ) := toExpr indetMap[indetQ.constName.getString!]!
    .some <$> mkAppOptM ``CPoly.CMvMonomial.mk #[
      arityQ,
      ←reduce q(Array.replicate $arityQ 0 |>.set! $finIndetQ $eQ),
      q(Eq.refl $arityQ)
    ]
  | ~q(@OfNat.ofNat (ZMod _) $_nQ $_instQ) => do
    -- Assumes this is 1, for more is 1 + 1 + ... + 1, i.e. a polynomial.
    let n ← unsafe evalExpr (ZMod (← unsafe evalExpr ℕ q(ℕ) kQ)) q(ZMod $kQ) eQ
    if n != 1 then return .none
    return .some q(CMvMonomial.one $arityQ)
  | ~q($_symQ) => -- Assumes this is an identifier.
    cMvMonoOfZMod q($eQ^1)
  | _ => logInfo m!"Unrecognised ZMod eq shape: {eQ}."; return .none
  
def cMvMonoOfZModEq (e : Q(Prop)) (indetMap : Std.HashMap String ℕ) (arity : Q(ℕ)) : MetaM (Option Q(CPoly.CMvMonomial $arity)) := do
  match e with
  | ~q(@Eq (ZMod $k) $lhs $rhs) =>
    let kval ← unsafe evalExpr ℕ q(ℕ) k
    if (← unsafe evalExpr (ZMod kval) q(ZMod $k) rhs) != 0 then throwError "Expected _ = 0. Rhs: {rhs}"
    cMvMonoOfZMod lhs indetMap arity
  | _ => logInfo m!"Expected: lhs = rhs for ZMod k. Expr: {e}"; return .none

instance {n : ℕ} : ToExpr (ZMod n) where
  toExpr z := match n with
              | 0 => ToExpr.toExpr (show ℤ from z)
              | k + 1 => ToExpr.toExpr (show Fin (k + 1) from z)
  toTypeExpr := .app (mkConst ``ZMod) (toExpr n)

instance {n : ℕ} {R : Type} [ToExpr R] : ToExpr (CPoly.Unlawful n R) where
  toExpr map := have nQ : Q(ℕ) := mkNatLit n
                have rQ : Q(Type) := toTypeExpr R
                let list : Q(List (CPoly.CMvMonomial $nQ × $rQ)) := toExpr map.toList
                q(@CPoly.Unlawful.ofList $nQ $rQ $list)
  toTypeExpr := mkApp2 (mkConst ``CPoly.Unlawful) (toExpr n) (toTypeExpr R)

partial def cMvPolyOfZMod {k : Q(ℕ)}
  (e : Q(ZMod $k)) (indetMap : Std.HashMap String ℕ) (arity : Q(ℕ)) : TacticM (Option Q(CPoly.Lawful $arity (ZMod $k))) := do
  match e with
  | ~q($x + $y) => do
    -- Assumes x * x was normalised to x^2 by `ring_nf`.
    let .some lhs ← cMvPolyOfZMod x indetMap arity | return .none
    let .some rhs ← cMvPolyOfZMod y indetMap arity | return .none
    let kval ← unsafe evalExpr ℕ q(ℕ) k
    let lhsval ← unsafe evalExpr (CPoly.CMvPolynomial indetMap.size (ZMod kval)) q(CPoly.CMvPolynomial $arity (ZMod $k)) lhs
    let rhsval ← unsafe evalExpr (CPoly.CMvPolynomial indetMap.size (ZMod kval)) q(CPoly.CMvPolynomial $arity (ZMod $k)) rhs
    let lhsunlawful : Q(CPoly.Unlawful $arity (ZMod $k)) := toExpr lhsval.1
    let rhsunlawful : Q(CPoly.Unlawful $arity (ZMod $k)) := toExpr rhsval.1
    let combined : Q(CPoly.Unlawful $arity (ZMod $k)) := q($lhsunlawful + $rhsunlawful)
    -- Do we want to reduce here?
    return .some q(CPoly.Lawful.fromUnlawful $combined)
  | ~q((@OfNat.ofNat (ZMod _) $n $inst) * $mono) => do
    -- I think `ring_nf` normalises to `_ * OfNat.` only anyway, but alright.
    -- 0 is verboten.
    let n@(_ + 1) ← unsafe evalExpr ℕ q(ℕ) n | return .none
    let .some monomial ← cMvMonoOfZMod mono indetMap arity | return .none
    let unlawful : Q(CPoly.Unlawful $arity (ZMod $k)) := q(CPoly.Unlawful.ofList [($monomial, ($n : ZMod $k))])
    let mvarid₁ ← mkFreshMVarId
    let proof ← mkFreshExprMVarWithId mvarid₁ (q(CPoly.Unlawful.isNoZeroCoef $unlawful))
    let X ← evalTacticAt (←`(tactic|grind)) mvarid₁
    let lawful ←
      mkAppOptM ``Subtype.mk #[
        .some q(CPoly.Unlawful $arity (ZMod $k)),
        .some q(CPoly.Unlawful.isNoZeroCoef (n := $arity) (R := ZMod $k)),
        unlawful,
        proof
      ]
    return .some lawful
  | ~q($mono * (@OfNat.ofNat (ZMod _) $n $inst)) =>
    cMvPolyOfZMod q((@OfNat.ofNat (ZMod _) $n $inst) * $mono) indetMap arity
  | ~q(@OfNat.ofNat (ZMod _) $n $inst) =>
    let kval ← unsafe evalExpr ℕ q(ℕ) k
    let nval ← unsafe evalExpr (ZMod kval) q(ZMod $k) e
    let nvalQ : Q(ZMod $k) := ToExpr.toExpr nval
    let monomial : Q(CPoly.CMvMonomial $arity) := q(CPoly.CMvMonomial.one (n := $arity))
    let unlawful : Q(CPoly.Unlawful $arity (ZMod $k)) := q(CPoly.Unlawful.ofList [($monomial, ($nvalQ : ZMod $k))])
    let mvarid₁ ← mkFreshMVarId
    let proof ← mkFreshExprMVarWithId mvarid₁ (q(CPoly.Unlawful.isNoZeroCoef $unlawful))
    let X ← evalTacticAt (←`(tactic|grind)) mvarid₁
    let lawful ←
      mkAppOptM ``Subtype.mk #[
        .some q(CPoly.Unlawful $arity (ZMod $k)),
        .some q(CPoly.Unlawful.isNoZeroCoef (n := $arity) (R := ZMod $k)),
        unlawful,
        proof
      ]
    return .some lawful
  | ~q($mono) =>
    let .some mono ← cMvMonoOfZMod mono indetMap arity | return .none
    let unlawful : Q(CPoly.Unlawful $arity (ZMod $k)) := q(CPoly.Unlawful.ofList [($mono, (1 : ZMod $k))])
    let mvarid₁ ← mkFreshMVarId
    let proof ← mkFreshExprMVarWithId mvarid₁ (q(CPoly.Unlawful.isNoZeroCoef $unlawful))
    let X ← evalTacticAt (←`(tactic|grind)) mvarid₁
    let lawful ←
      mkAppOptM ``Subtype.mk #[
        .some q(CPoly.Unlawful $arity (ZMod $k)),
        .some q(CPoly.Unlawful.isNoZeroCoef (n := $arity) (R := ZMod $k)),
        unlawful,
        proof
      ]
    return .some lawful
  | _ => pure .none

def cMvPolyOfZModEq {k : Q(ℕ)}
  (e : Q(Prop)) (indetMap : Std.HashMap String ℕ) (arity : Q(ℕ)) : TacticM (Option Q(CPoly.Lawful $arity (ZMod $k))) := do
  match e with
  | ~q(@Eq (ZMod $k) $lhs $rhs) =>
    let kval ← unsafe evalExpr ℕ q(ℕ) k
    if (← unsafe evalExpr (ZMod kval) q(ZMod $k) rhs) != 0 then throwError "Expected _ = 0. Rhs: {rhs}"
    cMvPolyOfZMod lhs indetMap arity
  | _ => logInfo m!"Expected: lhs = rhs for ZMod k. Expr: {e}"; return .none

-- elab "testme" : tactic => do
--   -- let x ← cMvPolyOfZModEq (k := q(290)) q(x^4 * y^2 = 0) syms (ToExpr.toExpr syms.size)
--   -- let x ← cMvPolyOfZModEq (k := q(290)) q((4 : ZMod 290) = 0) syms (ToExpr.toExpr syms.size)
--   -- let x ← cMvPolyOfZModEq (k := q(290)) q((x^2 + y^2) = 0) syms (ToExpr.toExpr syms.size)
--   let x ← cMvPolyOfZModEq (k := q(290)) q((4 * x^2 + y) = 0) syms (ToExpr.toExpr syms.size)
--   logInfo m!"x: {x}"

open CPoly

-- example : False := by
--   testme
  
  

-- #eval cMvPolyOfZModEq (k := q(290)) q(x^4 * y^2 = 0) syms (ToExpr.toExpr syms.size) -- monomial: CPoly.CMvMonomial.mk #[4, 2] ⋯


-- elab "tt" loc:(location)? : tactic => withMainContext do
--   match loc with
--   | .none => throwError "no location"
--   | .some loc =>
--     match loc with
--     | `(location|at $[$idns:ident]*) =>
--       let hyps ← getLCtx
--       let hyps := idns.mapM fun idn => do
--         let .some idn := hyps.findFromUserName? idn.getId | throwError s!"{idn.getId} is not a local hypothesis"
--         logInfo m!"e: {idn.type}"
--         let e ← cMvMonoOfZModEq idn.type
--         (pure idn.userName : TacticM Name)
--       logInfo m!"hyps: {←hyps}"
      
      
--       throwError "match"
--     | _ => throwError s!"loc is: {loc}"

def normaliseSystem : TacticM (Std.HashMap String ℕ) := withMainContext do
  -- Phase 0: Normalise ring expressions and substitute equations.
  let tstx ← locactionOfFVarIDsAndTarget (← zModEqs)
  evalTactic (←`(tactic| (try ring_nf $tstx:location); subst_eqs))  
  withMainContext do
  -- Phase 1: In the new context, do a final ring normalisation pass and normalise all `ZMod`
  -- equations to be of the `lhs = 0` form.

  -- TODO: Currently, the isolation is very simple with `rw [←sub_eq_zero]`, this might need
  -- to be made a little bit more sophisticated.
  let tstx ← locactionOfFVarIDsAndTarget (← zModEqs)
  evalTactic (←`(tactic| (try ring_nf $tstx:location
                          try rw [←sub_eq_zero] $tstx
                          try ring_nf $tstx:location)))
  withMainContext do
  -- Phase 3: In the new context, gather the indeterminates, create the `<X> → Fin k` mapping for
  -- `k`-variete polys and gather `Expr`essions in need of converting.
  let xyz ← indeterminates <&> Array.qsort
  let indetMap := Std.HashMap.ofList xyz.toList.zipIdx
  let exprs ← expressionsOfFVarIDsAndTarget (← zModEqs)
  for (hyp, e) in exprs do
    match hyp with
    | .none => logInfo m!"⊢ → {e}"
    | .some hyp => logInfo m!"{←hyp.getUserName} → {e}"
                   let .some test ← cMvPolyOfZModEq (k := q(290)) e syms (ToExpr.toExpr syms.size)
                     | throwError "Cannot synthesize CMvPolynomial from: {e}"
                   logInfo m!"test: {test}"
  -- Phase 4: Synthesize polynomials given the `exprs`.

  pure indetMap

elab "compute_poly" : tactic => withMainContext do
  discard normaliseSystem

-- def makeComputable : TacticM Unit := withMainContext do
--   let indeterminates ← normaliseSystem
--   withMainContext do
--   let ctx := (← getLocalHyps).push (←getMainTarget)
--   logInfo m!"indeterminates: {repr indeterminates} ctx: {ctx}"

-- elab "compute_poly" : tactic => withMainContext do
--   makeComputable

theorem test'' {x: ZMod 290} {y: ZMod 290}
        (h₁: x^4 * y^2 = 0)
 : False := by
 compute_poly

-- theorem test {x: ZMod 290} {y: ZMod 290}
--         (h6: x * (y + 20 + 30) = 10 * x)
--         --(h3: x = 20)
--         (h8: y = 42 - 42)
--         (h1: x * 2 * (x ^ 3) = 0)
--  : x + 30 = y - 80 := by
--   compute_poly
--   pz
--   compute_poly
--   tt at h1 h6
-- -- h6 ∧ h3 ∧ h8 ∧ ... ∧ (¬ goal)
--   ring_nf at *
--   subst_eqs
--   ring_nf at *

end EzPz
