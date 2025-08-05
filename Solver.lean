import Lean.Data.AssocList

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Qq

import CMvPolynomial.CMvMonomial
import CMvPolynomial.CMvPolynomial

open Qq

-- We want to construct CMVPolys from a bunch of X = Y where both X and Y are in ZMod n.
-- The first step, of the (for now) called pz tactic, is collect all indeterminates (variables Lean.Name)
-- in the context of type ZMod n. Check if all are in the same modules n, and construct a symbol
-- table assigning each indet a natural number that would be used to construct CMVPoly.
-- The second step is transform an expression X = Y into a CMVPoly. Here inters my idea of using ring_nf
-- to simplify the expressions.
-- As an example of simplification we want is: x = 2 and y = x + z become only y = 2 + z
--
-- Ideal format : x1 ∘ x2 ∘ ... ∘ xn where ∘ := + or -
--                xi := y1 * y2 * ... * yn
--                yi := lit or sym or sym ^ lit
-- x * (y + z) -> x * y + x * z
-- X = Y, ..., X2 = Y2
-- X - Y = 0 sat <-> CMVPoly sat


abbrev SymbolTable := Lean.AssocList Lean.Name Nat

-- elab "#printExpr" t:term : command => do
--   let e ← Lean.Elab.Command.liftTermElabM (Lean.Elab.Term.elabTerm t .none)
--   Lean.logInfo s!"term: {repr e}"

-- elab "#printOpExpr" t:term : command => do
--   let e ← Lean.Elab.Command.liftTermElabM (Lean.Elab.Term.elabTerm t .none)
--   let e' := (← Lean.Elab.Command.liftTermElabM $ Lean.Meta.withReducible <| Lean.Meta.whnf e).getAppFnArgs
--   Lean.logInfo s!"term: {repr e'}"

-- opaque k : ZMod 20
-- opaque j : ZMod 20
-- opaque z : ZMod 20

-- #printExpr (j * 10)

def zmodExpr : Lean.Expr := Lean.Expr.const ``ZMod []

-- Collect ZMod names and respective modules
def collectZMods : Lean.MetaM (Array (Lean.Name × Array Lean.Expr)) := do
  let h ← Lean.getLocalHyps
  let hty ← h.mapM (fun e ↦ do return (← Lean.Meta.inferType e).getAppFnArgs)
  return hty.filter (fun (n, _) ↦ n == ``ZMod)

def buildSymbolTable (n : Array Lean.Name) : SymbolTable :=
  (n.foldl (fun (s,i) a ↦ (s.insert a i, i + 1)) (∅,0)).fst

-- Given symbol table construct a "Monomial" : x1 * x2 * ... * xn wher
-- xi = natlit or sym or sym^natlit
inductive MTerm where
  | lit : Nat → MTerm
  | sym : Lean.Name → MTerm
  | pow : Lean.Name → Nat → MTerm
  | mul : MTerm → MTerm → MTerm
deriving Inhabited, Repr

partial def MTerm.ofTerm (t : Lean.Term) : Lean.MetaM MTerm := do
  match t with
  | `($x * $y) => .mul <$> ofTerm x <*> ofTerm y
  | `($b:ident ^ $n:num) => return .pow b.getId n.getNat
  | `($x:ident) => return .sym x.getId
  | `($n:num) => return .lit n.getNat
  | _ => throwError m!"{t} not in monomial form"

deriving instance Repr for Lean.AssocList

structure MTermInfo where
  coeff : Option Nat
  indets : Lean.AssocList Lean.Name Nat -- occurrences of each name
deriving Inhabited, Repr

-- x * y

-- state?
private def MTermInfo.ofMTerm_aux (m : MTerm) (mi : MTermInfo) : Lean.MetaM MTermInfo := do
  match m with
  | .lit n =>
    unless mi.coeff.isNone do throwError "coefficient already assigned"
    return { mi with coeff := n }
  | .sym s => updateIndet s 1
  | .pow s n => updateIndet s n
  | .mul l r => return ←ofMTerm_aux r (←ofMTerm_aux l mi)
where
  updateIndet i n :=
    match mi.indets.find? i with
    | some v => return {mi with indets := mi.indets.replace i (v + n)}
    | none => return {mi with indets := mi.indets.insert i n}

def MTermInfo.ofMTerm (m : MTerm) : Lean.MetaM MTermInfo :=
  ofMTerm_aux m default

open Lean Elab Command in
elab "#abc" t:term : command => liftTermElabM do
  let mt ← MTerm.ofTerm t
  logInfo s!"MTERM -- {repr mt}"
  logInfo s!"MINFO -- {repr (← MTermInfo.ofMTerm mt)}"

namespace EzPz

scoped syntax "spoon" Lean.Parser.Tactic.location : term

open Lean Parser Elab Tactic Meta

inductive MTerm where
  | lit (_ : ℕ)
  | sym (_ : Name)
  | pow (_ : Name) (_ : ℕ)
  | mul (_ _ : MTerm)
deriving Inhabited, Repr, BEq

namespace MTerm

partial def ofTerm (t : Term) : MetaM MTerm := do
  match t with
  | `($x * $y) => .mul <$> ofTerm x <*> ofTerm y
  | `($b:ident ^ $n:num) => return .pow b.getId n.getNat
  | `($x:ident) => return .sym x.getId
  | `($n:num) => return .lit n.getNat
  | _ => throwError m!"{t} not in monomial form."

end MTerm

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
  let lctx ← getLCtx
  let mut result := hyps.map Option.some |>.zip <| hyps.map (LocalDecl.type ∘ lctx.get!)
  if includeTarget then result := result.push (.none, ←getMainTarget)
  return Std.HashMap.ofList result.toList

def indeterminates : TacticM (Array String) := do
  let zmodHyps ← (← getLocalHyps).filterM (inferType · <&> (·.getAppFnArgs.1 == ``ZMod))
  zmodHyps.mapM (·.fvarId!.getUserName <&> Name.toString)  

open Lean in
instance {n : ℕ} : ToExpr (CPoly.CMvMonomial n) where
  toExpr mono := -- TODO: I think we need the h actually, instead of the `Eq.refl`.
                 match mono with
                 | ⟨vec, _⟩ => let arrExpr := ToExpr.toExpr vec
                               let arityQ : Q(ℕ) := ToExpr.toExpr n
                               mkApp3 (mkConst ``CPoly.CMvMonomial.mk) arityQ arrExpr q(Eq.refl $arityQ)
  toTypeExpr := let arityQ : Q(ℕ) := ToExpr.toExpr n
                mkApp2 (mkConst ``Vector [0]) q(ℕ) arityQ

-- open Lean in
-- instance {n : ℕ} {R : Type} [ToExpr R] [Zero R] : ToExpr (CPoly.Unlawful n R) where
--   toExpr map := let arityQ : Q(ℕ) := ToExpr.toExpr n
--                 let ringQ : Q(Type) := ToExpr.toTypeExpr R
--                 mkApp4 (mkConst ``Std.ExtTreeMap.mk [0, 0])
--                        q(CPoly.CMvMonomial $arityQ)
--                        q($ringQ)
--                        q(Ord.compare (α := CPoly.CMvMonomial $arityQ))
--                        _
--   toTypeExpr := sorry

-- open Lean in
-- instance {n : ℕ} {R : Type} [Zero R] : ToExpr (CPoly.CMvPolynomial n R) where
--   toExpr mono := -- TODO: I think we need the h actually, instead of the `Eq.refl`.
--                  match mono with
--                  | ⟨map, prop⟩ => let arrExpr := ToExpr.toExpr map
--                                   let arityQ : Q(ℕ) := ToExpr.toExpr n
--                                mkApp3 (mkConst ``CPoly.CMvMonomial.mk) arityQ arrExpr q(Eq.refl $arityQ)
--   toTypeExpr := let arityQ : Q(ℕ) := ToExpr.toExpr n
--                 mkApp2 (mkConst ``Vector [0]) q(ℕ) arityQ

/--
TODO: Note this assumes that `nf_ring` puts `ZMod` equations in a certain format.
      This will need a tiny bit more finesse if we need to collect terms ourselves.

      - nat
      - ident
      - ident ^ nat
      - mono * mono

TODO: Simplify the way expressions are returned, there's currently some log statements scattered
      that make this process convoluted.
-/
partial def cMvMonoOfZMod {k : Q(ℕ)}
  (e : Q(ZMod $k)) (xyzMap : Std.HashMap String ℕ) (arity : Q(ℕ)) : MetaM (Option Q(CPoly.CMvMonomial $arity)) := do
  -- let arityQ : Q(ℕ) := ToExpr.toExpr xyzMap.size
  let kval ← unsafe evalExpr ℕ q(ℕ) k
  match e with
  | ~q($x * $y) => do
    -- Assumes x * x was normalised to x^2 by `ring_nf`.
    let .some lhs ← cMvMonoOfZMod x xyzMap arity | return .none
    let .some rhs ← cMvMonoOfZMod y xyzMap arity | return .none
    let lhsval ← unsafe evalExpr (CPoly.CMvMonomial xyzMap.size) q(CPoly.CMvMonomial $arity) lhs
    let rhsval ← unsafe evalExpr (CPoly.CMvMonomial xyzMap.size) q(CPoly.CMvMonomial $arity) rhs
    let combined := lhsval * rhsval
    -- logInfo m!"monomial: {ToExpr.toExpr combined}"
    return .some (ToExpr.toExpr combined)
  | ~q($sym ^ $e) => do
    -- Assumes this is an identifier ^ natural number.
    let exponentvalQ : Q(ℕ) ← ToExpr.toExpr <$> unsafe evalExpr ℕ q(ℕ) e
    let xyzIdxQ : Q(ℕ) := ToExpr.toExpr xyzMap[sym.constName.getString!]!
    let monomial : Q(CPoly.CMvMonomial $arity) ← mkAppOptM ``CPoly.CMvMonomial.mk #[
      arity,
      ←reduce q(Array.replicate $arity 0 |>.set! $xyzIdxQ $exponentvalQ),
      q(Eq.refl $arity)
    ]
    -- logInfo m!"monomial: {monomial}"
    -- logInfo m!"monomial: {←inferType (monomial)}"
    return .some monomial
  | ~q(@OfNat.ofNat (ZMod _) $n $inst) => do
    -- Assumes this is 1, for more is 1 + 1 + ... + 1, i.e. a polynomial.
    let nval ← unsafe evalExpr (ZMod kval) q(ZMod $k) e
    if nval != 1 then return .none
    let monomial : Q(CPoly.CMvMonomial $arity) := q(CPoly.CMvMonomial.one (n := $arity))
    -- logInfo m!"monomial: {monomial}"
    return .some monomial
  | ~q($sym) => -- Assumes this is an identifier.
    cMvMonoOfZMod q($e^1) xyzMap arity
  | _ => logInfo m!"Unrecognised ZMod eq shape: {e}."; return .none
  
-- def x : ZMod 290 := 4
-- def y : ZMod 290 := 4
-- def syms := Std.HashMap.ofList [("x", 0), ("y", 1)]
-- #eval cMvMonoOfZMod q((y)) syms (ToExpr.toExpr syms.size)
-- #eval cMvMonoOfZMod q(((291 : ZMod 290))) syms (ToExpr.toExpr syms.size)
-- #eval cMvMonoOfZMod q(y^4) syms (ToExpr.toExpr syms.size)
-- #eval cMvMonoOfZMod q(x * y) syms (ToExpr.toExpr syms.size)

def cMvMonoOfZModEq (e : Q(Prop)) (xyzMap : Std.HashMap String ℕ) (arity : Q(ℕ)) : MetaM (Option Q(CPoly.CMvMonomial $arity)) := do
  match e with
  | ~q(@Eq (ZMod $k) $lhs $rhs) =>
    let kval ← unsafe evalExpr ℕ q(ℕ) k
    if (← unsafe evalExpr (ZMod kval) q(ZMod $k) rhs) != 0 then throwError "Expected _ = 0. Rhs: {rhs}"
    cMvMonoOfZMod lhs xyzMap arity
  | _ => logInfo m!"Expected: lhs = rhs for ZMod k. Expr: {e}"; return .none

def x : ZMod 290 := 4
def y : ZMod 290 := 4
def syms := Std.HashMap.ofList [("x", 0), ("y", 1)]
/-
  These are ok.
-/
-- #eval cMvMonoOfZModEq q((y = 0)) syms (ToExpr.toExpr syms.size) -- monomial: CPoly.CMvMonomial.mk { toList := [0, 1] } ⋯
-- #eval cMvMonoOfZModEq q(((291 : ZMod 290) = 0)) syms (ToExpr.toExpr syms.size) -- monomial: CPoly.CMvMonomial.one
-- #eval cMvMonoOfZModEq q(y^(4) = 0) syms (ToExpr.toExpr syms.size) -- monomial: CPoly.CMvMonomial.mk { toList := [0, 4] } ⋯
-- #eval cMvMonoOfZModEq q(x^4 * y^2 = 0) syms (ToExpr.toExpr syms.size) -- monomial: CPoly.CMvMonomial.mk #[4, 2] ⋯

def cMvPolyOfZMod {k : Q(ℕ)}
  (e : Q(ZMod $k)) (xyzMap : Std.HashMap String ℕ) (arity : Q(ℕ)) : MetaM (Option Q(CPoly.Lawful $arity (ZMod $k))) := do
  match e with
  | ~q($x + $y) => pure .none
  | ~q(@OfNat.ofNat (ZMod _) $n $inst) =>
    let kval ← unsafe evalExpr ℕ q(ℕ) k
    let nval ← unsafe evalExpr (ZMod kval) q(ZMod $k) e
    pure .none
  | ~q($mono) =>
    let .some mono ← cMvMonoOfZMod mono xyzMap arity | return .none
    let unlawful : Q(CPoly.Unlawful $arity (ZMod $k)) := q(CPoly.Unlawful.ofList [($mono, (1 : ZMod $k))])
    logInfo m!"unlawful: {unlawful}"
    let proof ← mkFreshExprMVar (.some q(CPoly.Unlawful.isNoZeroCoef $unlawful))
    logInfo m!"proof: {proof}"
    let lawful : Q(CPoly.Lawful $arity (ZMod $k)) := q(⟨$unlawful, by sorry⟩)
    logInfo m!"lawful: {lawful}"
    return .some lawful
  | _ => pure .none

def cMvPolyOfZModEq {k : Q(ℕ)}
  (e : Q(Prop)) (xyzMap : Std.HashMap String ℕ) (arity : Q(ℕ)) : MetaM (Option Q(CPoly.Lawful $arity (ZMod $k))) := do
  match e with
  | ~q(@Eq (ZMod $k) $lhs $rhs) =>
    let kval ← unsafe evalExpr ℕ q(ℕ) k
    if (← unsafe evalExpr (ZMod kval) q(ZMod $k) rhs) != 0 then throwError "Expected _ = 0. Rhs: {rhs}"
    cMvPolyOfZMod lhs xyzMap arity
  | _ => logInfo m!"Expected: lhs = rhs for ZMod k. Expr: {e}"; return .none

-- #eval cMvPolyOfZMod q(x^4 * y^2) syms (ToExpr.toExpr syms.size) -- monomial: CPoly.CMvMonomial.mk #[4, 2] ⋯
-- #eval cMvPolyOfZMod q(y) syms (ToExpr.toExpr syms.size) -- monomial: CPoly.CMvMonomial.mk { toList := [0, 1] } ⋯
-- #eval cMvPolyOfZMod q((291 : ZMod 290)) syms (ToExpr.toExpr syms.size) -- monomial: CPoly.CMvMonomial.one
-- #eval cMvPolyOfZMod q(y^(4)) syms (ToExpr.toExpr syms.size) -- monomial: CPoly.CMvMonomial.mk { toList := [0, 4] } ⋯

#eval cMvPolyOfZModEq (k := q(290)) q(x^4 * y^2 = 0) syms (ToExpr.toExpr syms.size) -- monomial: CPoly.CMvMonomial.mk #[4, 2] ⋯


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
  let xyzMap := Std.HashMap.ofList xyz.toList.zipIdx
  let exprs ← expressionsOfFVarIDsAndTarget (← zModEqs)
  for (hyp, e) in exprs do
    match hyp with
    | .none => logInfo m!"⊢ → {e}"
    | .some hyp => logInfo m!"{←hyp.getUserName} → {e}"
                   let .some test ← cMvPolyOfZModEq (k := q(290)) e syms (ToExpr.toExpr syms.size)
                     | throwError "Cannot synthesize CMvPolynomial from: {e}"
                   logInfo m!"test: {test}"
  -- Phase 4: Synthesize polynomials given the `exprs`.

  pure xyzMap

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

theorem test {x: ZMod 290} {y: ZMod 290}
        (h6: x * (y + 20 + 30) = 10 * x)
        --(h3: x = 20)
        (h8: y = 42 - 42)
        (h1: x * 2 * (x ^ 3) = 0)
 : x + 30 = y - 80 := by
  compute_poly
  pz
  compute_poly
  tt at h1 h6
-- h6 ∧ h3 ∧ h8 ∧ ... ∧ (¬ goal)
  ring_nf at *
  subst_eqs
  ring_nf at *

end EzPz

-- abbrev SymbolTable := Lean.AssocList Lean.Name Nat

-- def buildSymbolTableFromContext : Lean.MetaM SymbolTable := do
--   let mut st : SymbolTable := ∅
--   let mut occ : Nat := 0
--   for ldecl in ← Lean.getLCtx do
--     let ty ← Lean.Meta.inferType (ldecl.toExpr)
--     if Meta.isDefEq `` ty.getAppFn



-- def symbolTableFromDecl : Lean.Elab.Tactic.TacticM SymbolTable :=
--   Lean.Elab.Tactic.withMainContext do
--     return (← (← Lean.getLCtx).foldrM f (∅,0)).fst
-- where
--   f ldecl s := do
--     if let some n ← (zmodname ldecl) then return (s.1.insert n s.2 , s.2 + 1)
--       else return s

--   zmodname ldecl := do
--     let ⟨1, ~q(ZMod _), _⟩ ← inferTypeQ ldecl.toExpr | return none
--     return some ldecl.userName

-- elab "symbolTable" : tactic => do
--   let l ← symbolTableFromDecl
--   Lean.logInfo m!"{l.toList}"

-- -- Indets and its # ocurrence in a monomial
-- abbrev Indets := List (Nat × Nat)

-- structure MonomialInfo n where
--   coeff : ZMod n
--   indets : Indets

-- def Indets.combine (m1 m2: Indets) : Lean.MetaM Indets :=
--   match m1, m2 with
--   | [] , [] => return []
--   | x :: xs, y :: ys => return ((x.1, x.2 + y.2) :: (← combine xs ys))
--   | _ , _ => failure

-- def Indets.updateIndex (i : Nat) (o : Nat) : Indets → Indets
--   | [] => []
--   | (ident, occ) :: is => if i == ident then (ident, occ + o) :: is
--     else (ident, occ) :: updateIndex i o is

-- -- TODO: better handling of the coefficients
-- def MonomialInfo.combine {n} (m1 m2 : MonomialInfo n) : Lean.MetaM (MonomialInfo n) :=
--   let (⟨c1,i1⟩,⟨c2,i2⟩) := (m1,m2)
--   if c1 = 1 then return ⟨c2, ← i1.combine i2⟩
--   else if c2 = 1 then return ⟨c2, ← i1.combine i2⟩
--   else failure -- two different coefficients

-- #eval MonomialInfo.combine ⟨(1 : ZMod 20), [(1, 0), (2,1)]⟩ ⟨1, [(1, 0), (2,1)]⟩
-- #eval MonomialInfo.combine ⟨(1 : ZMod 20), [(1, 0), (2,1), (0,4)]⟩ ⟨1, [(1, 0), (2,1)]⟩
-- #eval MonomialInfo.combine ⟨(1 : ZMod 20), [(1, 0), (2,1)]⟩ ⟨4, [(1, 0), (2,1)]⟩
-- #eval MonomialInfo.combine ⟨(5 : ZMod 20), [(1, 0), (2,1)]⟩ ⟨4, [(1, 0), (2,1)]⟩

-- def MonomialInfo.updateIndex {n} (m : MonomialInfo n) (index : Nat) (occ : Nat) : MonomialInfo n :=
--   ⟨m.coeff, m.indets.updateIndex index occ⟩

-- -- The function expects a normalized expression: M0 ∘ M1 ∘ ... ∘ Mn, where ∘ := + or -
-- -- Mx := N0 * N1 * ... Nn
-- -- Nx := number or indets or k ^ y, with k indet and y Nat

-- unsafe def monomial_aux
--   {n : Nat}
--   (st: SymbolTable)
--   (m : MonomialInfo n)
--   (pz: Q(ZMod $n))
--   : Lean.MetaM (MonomialInfo n) :=
--   match pz with
--   | ~q($x + $y) | ~q($x - $y) => failure -- no addition at this point, wrong normalization
--   | ~q((_ * _) ^ _) => failure           -- should have been normalized
--   | ~q($x * $y) => (← monomial_aux st m x).combine (← monomial_aux st m y)
--   | ~q($x ^ $y) =>
--     if let some i := Lean.AssocList.find? x.constName st then return up m i (← evalNat y)
--     else failure
--   | n =>
--     if let some i := Lean.AssocList.find? n.constName st then return up m i 1
--     else return ⟨(← evalNat n), m.indets⟩
-- where
--   evalNat n := Lean.Meta.evalExpr Nat q(Nat) n
--   up m i v := MonomialInfo.updateIndex m i v

-- elab "monomial" t:term : tactic => do
--   let ⟨1, ~q(Nat), ~q(10)⟩ ← inferTypeQ (← Lean.Elab.Term.elabTerm t (some q(Nat))) | throwError m!"!error! {t}"
--   -- let t ← elabTermEnsuringTypeQ (u := Lean.levelOne) t q(ZMod $n)
--   -- Lean.logInfo m!"Term: {t}"
--   -- let st ← symbolTableFromDecl
--   -- Lean.logInfo m!"Symbol table: {st.toList}"
--   pure ⟨⟩
--   --let mi ← monomial_aux st ⟨0, []⟩ te

-- example: 10 = 20 := by
--   (monomial 10)
--   sorry

-- theorem test {x: ZMod 290} {y: ZMod 290}
--         --(h3 : (42 : ZMod 80) = 43)
--         (h6: x * (y + 20 + 30) = 10)
--         (h3: x = 20)
--         (h8: y = 42 - 42)
--  : x + 30 = y - 80 := by
--   monomial 10
--   -- ring_nf! at h6
--   -- subst_eqs

-- partial def monomials {n : Q(Nat)} (st: SymbolTable) : (pz: Q(ZMod $n)) → Lean.MetaM (List Q(ZMod $n))
--   | ~q($x + $y) => return (← monomials st x) ++ (← monomials st y)
--   | ~q($x - $y) => return (← monomials st x) ++ (← monomials st y)
--   | ~q($x * $y) => return (← monomials st x) ++ (← monomials st y)
--   | ~q($x ^ $y) => return (← monomials st x) ++ (← monomials st y)
--   | n => return [n]


-- opaque k : ZMod 10
-- opaque m : ZMod 10

-- opaque z : Nat

-- abbrev zdouble (a : ZMod 10) := a + a
-- abbrev wdouble (a : ZMod 10) := a - a

-- theorem test {x: ZMod 290} {y: ZMod 290}
--         --(h3 : (42 : ZMod 80) = 43)
--         (h6: x * (y + 20 + 30) = 10)
--         (h3: x = 20)
--         (h8: y = 42 - 42)
--  : x + 30 = y - 80 := by
--   symbol
--   ring_nf! at h6
--   subst_eqs

-- partial def literal: (pz: Q(Nat)) → MetaM Bool
--   | ~q($x * $y) => return (← literal x) ∨ (← literal y)
--   | n => return n.isLit

-- #eval q(ZMod 10)

-- mutual
-- partial def poly {n : Q(Nat)} : (pz: Q(ZMod $n)) → MetaM (List Q(ZMod $n))
--   | ~q($x + $y) => return (← poly x) ++ (← poly y)
--   | ~q($x - $y) => return (← poly x) ++ (← poly y)
--   | n => return [n]

-- partial def monomials {n : Q(Nat)} : (pz: Q(ZMod $n)) → MetaM (List Q(ZMod $n))
--   | ~q($x * $y) => return (← monomial x) ++ (← monomial y)
--   | n => return [n]
-- end

-- elab "pz" : tactic => do
--   Elab.Tactic.evalTactic (← `(tactic| norm_num at *))
--   Elab.Tactic.withMainContext do
--     for ldecl in ← getLCtx do
--       if let some ty ← checkTypeQ (u := levelOne) ldecl.type q(Prop) then
--         logInfo m!"{ldecl.userName} has value? {ldecl.hasValue}"
--         match ty with
--         | ~q(($p : ZMod $n) = $q) =>
--           if (← Meta.isDefEq q q(0 : ZMod $n)) then
--             logInfo m!"EQ0 left = {p}, right = {q}"
--           else logInfo m!"EQ1 left = {p}, right = {q}"
--         | _ => return

-- open Lean.Elab.Tactic in
-- elab "custom_have " n:ident " : " t:term " := " v:term : tactic =>
--   withMainContext do
--     let t ← elabTerm t none
--     let v ← elabTermEnsuringType v t
--     liftMetaTactic fun mvarId => do
--       let mvarIdNew ← mvarId.assert n.getId t v
--       let (_, mvarIdNew) ← mvarIdNew.intro1P
--       return [mvarIdNew]

-- partial def summands {α : Q(Type $u)} (inst : Q(Add $α)) : Q($α) → MetaM (List Q($α))
--   | ~q($x + $y) => return (← summands inst x) ++ (← summands inst y)
--   | n => return [n]

-- opaque k : Nat
-- opaque m : Nat

-- abbrev double (a : Nat) := a + a
-- #eval summands q(inferInstance) q(double k + m)

-- #eval show MetaM Bool from do
--   let x : Q(Nat) := q(k + m)
--   match x with
--   | ~q(Nat.add $a $b) => return true
--   | _ => return false

-- abbrev square (a : Nat) :=
--   have : Add Nat := ⟨(· * ·)⟩
--   a + a

-- #eval square 10
-- #eval summands q(inferInstance) q(k + square (square k))
-- #eval summands q(⟨(· * ·)⟩) q(k * square (square k))

-- def matchProd (e : Nat × Q(Nat)) : MetaM Bool := do
--   let (2, ~q(1)) := e | return false
--   return true

-- #eval do guard <| (←matchProd (2, q(1))) == true

-- def getNatAdd (e : Expr) : MetaM (Option (Q(Nat) × Q(Nat))) := do
--   let ⟨Level.succ Level.zero, ~q(Nat), ~q($a + $b)⟩ ← inferTypeQ e | return none
--   return some (a, b)

-- example (a b: ZMod 42): a + b = b + a := by
--   sorry

-- -- theorem list_app_cons_not_nil (y: α) (xs ys: List α) :
-- --   [] ≠ xs ++ (y :: ys) := by
-- --   cases xs <;> (intro h'; contradiction)

-- -- elab "applyit" : tactic => do
-- --   let goal ← getMainTarget
-- --   if let some goalType ← checkTypeQ (u := levelOne) goal q(Prop) then
-- --     if let ~q([] ≠ $xs ++ ($y :: $ys)) := goalType then
-- --       logInfo m!"xs = {xs}, y = {y}, ys = {ys}"
-- --       evalTactic (← `(tactic| apply list_app_cons_not_nil))

-- -- elab "print_list_cons_in_hyp" : tactic => do
-- --   for ldecl in ← getLCtx do
-- --     if let some ty ← checkTypeQ (u := levelOne) ldecl.type q(Prop) then
-- --       if let ~q([] ≠ $xs ++ ($y :: $ys)) := ty then
-- --         let name := ldecl.userName
-- --         logInfo m!"name = {name}, xs = {xs}, y = {y}, ys = {ys}"

-- -- example(H1: 2 = 2): [] ≠ xs ++ (y :: ys) := by
-- --   print_list_cons_in_hyp
-- --   applyit

-- -- def traceGoals : TacticM Unit :=
-- --   do
-- --     logInfo m!"Lean version: {Lean.versionString}"
-- --     logInfo "All goals:"
-- --     let goals ← getUnsolvedGoals
-- --     logInfo m!"{goals}"
-- --     match goals with
-- --     | [] => return
-- --     | _ :: _ =>
-- --       logInfo "First goal's target:"
-- --       let target ← getMainTarget
-- --       logInfo m!"{target}"

-- -- elab "trace_goals" : tactic => traceGoals

-- -- theorem test (α: Type) (a : α) : 42 = 52 := by
-- --   trace_goals

-- -- def hypothesis : TacticM Unit :=
-- --   withMainContext do
-- --     let target ← getMainTarget
-- --     let lctx ← getLCtx
-- --     for ldecl in lctx do
-- --       if ! LocalDecl.isImplementationDetail ldecl then
-- --         let eq ← isDefEq (LocalDecl.type ldecl) target
-- --         if eq then
-- --           let goal ← getMainGoal
-- --           MVarId.assign goal (LocalDecl.toExpr ldecl)
-- --           return
-- --     failure

-- -- elab "hypothesis" : tactic => hypothesis

-- -- partial def destructAndExpr (hP : Expr) : TacticM Bool :=
-- --   withMainContext do
-- --     let target ← getMainTarget
-- --     let P ← inferType hP
-- --     if (← isDefEq P target) then
-- --       MVarId.assign (← getMainGoal) hP
-- --       return true
-- --     else
-- --       match Expr.and? P with
-- --       | Option.none => return false
-- --       | Option.some (_, _) =>
-- --         let hQ ← mkAppM ``And.left #[hP]
-- --         if (← destructAndExpr hQ) then return true
-- --         else
-- --           let hR ← mkAppM ``And.right #[hP]
-- --           destructAndExpr hR

-- -- def destructAnd (name : Name) : TacticM Unit :=
-- --   withMainContext do
-- --     let h ← getFVarFromUserName name
-- --     if !(← destructAndExpr h) then failure
