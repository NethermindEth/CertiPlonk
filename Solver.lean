import Lean.Data.AssocList

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Qq

open Qq

abbrev SymbolTable := Lean.AssocList Lean.Name Nat

elab "#printExpr" t:term : command => do
  let e ← Lean.Elab.Command.liftTermElabM (Lean.Elab.Term.elabTerm t .none)
  Lean.logInfo s!"term: {repr e}"

elab "#printOpExpr" t:term : command => do
  let e ← Lean.Elab.Command.liftTermElabM (Lean.Elab.Term.elabTerm t .none)
  let e' := (← Lean.Elab.Command.liftTermElabM $ Lean.Meta.withReducible <| Lean.Meta.whnf e).getAppFnArgs
  Lean.logInfo s!"term: {repr e'}"

opaque k : ZMod 20
opaque j : ZMod 20
opaque z : ZMod 20

#printExpr (j * 10)

def zmodExpr : Lean.Expr := Lean.Expr.const ``ZMod []

-- Collect ZMod names and respective modules
def collectZMods : Lean.MetaM (Array (Lean.Name × Array Lean.Expr)) := do
  let h ← Lean.getLocalHyps
  let hty ← h.mapM (fun e ↦ do return (← Lean.Meta.inferType e).getAppFnArgs)
  return hty.filter (fun (n, _) ↦ n == ``ZMod)

def buildSymbolTable (n : Array Lean.Name) : SymbolTable :=
  (n.foldl (fun (s,i) a ↦ (s.insert a i, i + 1)) (∅,0)).fst

-- ring_nf

-- Given symbol table construct a "Monomial" : x1 * x2 * ... * xn wher
-- xi = natlit or sym or sym^natlit
inductive MTerm where
  | lit : Nat → MTerm
  | sym : Lean.Name → MTerm
  | pow : Lean.Name → Nat → MTerm
  | mul : MTerm → MTerm → MTerm
deriving Inhabited, Repr

-- lemma abc : ∀ {a b : Nat}, (b = 1) → a + 0 = a := sorry

-- example : 42 + 0 = 42 := by
--   rw [abc]

open Lean Meta

-- partial def MTerm.ofExpr (e : Lean.Expr) : Lean.MetaM MTerm := do
--   match e.getAppFnArgs with
--   | (``HMul.hMul, #[_, _, _, _, l, r]) => return .mul (← MTerm.ofExpr l) (← MTerm.ofExpr r)
--   | (``HPow.hPow, #[_, _, _, _, b, p]) =>
--     let .const n _ := b.getAppFn | throwError "base should be a symbol"
--     return .pow n p
--   | (s, #[]) => return MTerm.sym s
--   | _ =>
--     let m₂ ← Lean.Meta.mkFreshExprMVar (← inferType e)
--     Lean.logInfo m!"m₂ PRE = {m₂}"
--     if ← Lean.Meta.isDefEq e m₂ then
--       Lean.logInfo m!"m₂ POST = {m₂}"
--       return MTerm.lit m₂
--     else throwError "Something went wrong!"



partial def MTerm.ofExpr' (e : Term) : Elab.Command.CommandElabM MTerm := do
  match e with
  | `($x * $y) => 
    logInfo m!"Entered: {x} * {y}"
    return .mul (←MTerm.ofExpr' x) (←MTerm.ofExpr' y)
  | `($b:ident ^ $n:num) =>
    logInfo m!"Entered: {b} ^ {n}"
    return .pow b.getId n.getNat
  | `($x:ident) => 
    logInfo m!"Entered: {x}"
    return .sym x.getId
  | `($n:num) =>
    logInfo m!"Entered: {n}"
    return .lit n.getNat
  | _ => logInfo m!"Catch any!"
         pure default

open Core

elab "#abc" t:term : command => do
  discard (MTerm.ofExpr' t)

#abc 10 * j * k

elab "#printMTerm" t:term : command => do
  let e ← Lean.Elab.Command.liftTermElabM (Lean.Elab.Term.elabTerm t .none)
  let e'' ← Lean.Elab.Command.liftTermElabM $ Lean.instantiateMVars e
  let e' ← Lean.Elab.Command.liftTermElabM (MTerm.ofExpr e'')
  Lean.logInfo s!"term: {repr e'}"

#printMTerm (10 * j * k)
#printOpExpr 10 * k

open Lean AssocList in
def Indets.combine (m1 m2: AssocList Lean.Name Q(Nat)) : AssocList Name Q(Nat) :=
  match m1, m2 with
  | .empty, n => .empty
  | .cons tx nx xs, .cons ty ny ys => return ((x.1, x.2 + y.2) :: (← combine xs ys))
  | _ , _ => failure

structure MTermInfo where
  coeff : Q(Nat)
  indets : Lean.AssocList Lean.Name Q(Nat) -- occurrences of each name



-- TODO: better handling of the coefficients
def MTermInfo.combine (m1 m2 : MTermInfo) : Lean.MetaM MTermInfo :=
  let (⟨c1,i1⟩,⟨c2,i2⟩) := (m1,m2)
  if c1 = 1 then return ⟨c2, ← i1.combine i2⟩
  else if c2 = 1 then return ⟨c2, ← i1.combine i2⟩
  else failure -- two different coefficients

def MTermInfo.ofMTerm (m : MTerm) : Lean.MetaM MTermInfo := do
  let mi : MTerm.Info := ⟨q(0), []⟩
  match m with
  | .lit ~q(n) => { mi with coeff := $n }
  |

elab "pz" : tactic => do
  -- Elab.Tactic.evalTactic (← `(tactic| norm_num at *))
  Lean.Elab.Tactic.withMainContext do
    let (names, mods) := (← collectZMods).unzip
    unless !names.isEmpty do throwError "No indets found"
    unless ← mods.allM (fun m ↦ Lean.Meta.isDefEq m[0]! (mods[0]!)[0]!) do
      throwError m!"All modules should be equal. Found: {mods.map (·[0]!)}"

    Lean.logInfo m!"+ Hey, I'm zmod: {mods}"
    return ()
    -- for ldecl in ← Lean.getLCtx do
    --   let arr ← Lean.getLocalHyps
    --   let lExpr := ldecl.toExpr
    --   let lName := ldecl.userName
    --   let lType ← Lean.Meta.inferType lExpr
    --   let (name, args) := lType.getAppFnArgs
    --   --let .forallE n .. := lType | throwError "LOL"
    --   Lean.logInfo m!"+ Hey, I'm zmod: {arr}"
    --   -- if let some ty ← checkTypeQ (u := levelOne) ldecl.type q(Prop) then
    --   --   logInfo m!"{ldecl.userName} has value? {ldecl.hasValue}"
    --   --   match ty with
    --   --   | ~q(($p : ZMod $n) = $q) =>
    --   --     if (← Meta.isDefEq q q(0 : ZMod $n)) then
    --   --       logInfo m!"EQ0 left = {p}, right = {q}"
    --   --     else logInfo m!"EQ1 left = {p}, right = {q}"
    --   --   | _ => return

theorem test {x: ZMod 290} {y: ZMod 290}
        --(h3 : (42 : ZMod 80) = 43)
        (h6: x * (y + 20 + 30) = 10)
        (h3: x = 20)
        (h8: y = 42 - 42)
 : x + 30 = y - 80 := by
  pz

abbrev SymbolTable := Lean.AssocList Lean.Name Nat

def buildSymbolTableFromContext : Lean.MetaM SymbolTable := do
  let mut st : SymbolTable := ∅
  let mut occ : Nat := 0
  for ldecl in ← Lean.getLCtx do
    let ty ← Lean.Meta.inferType (ldecl.toExpr)
    if Meta.isDefEq `` ty.getAppFn



def symbolTableFromDecl : Lean.Elab.Tactic.TacticM SymbolTable :=
  Lean.Elab.Tactic.withMainContext do
    return (← (← Lean.getLCtx).foldrM f (∅,0)).fst
where
  f ldecl s := do
    if let some n ← (zmodname ldecl) then return (s.1.insert n s.2 , s.2 + 1)
      else return s

  zmodname ldecl := do
    let ⟨1, ~q(ZMod _), _⟩ ← inferTypeQ ldecl.toExpr | return none
    return some ldecl.userName

elab "symbolTable" : tactic => do
  let l ← symbolTableFromDecl
  Lean.logInfo m!"{l.toList}"

-- Indets and its # ocurrence in a monomial
abbrev Indets := List (Nat × Nat)

structure MonomialInfo n where
  coeff : ZMod n
  indets : Indets

def Indets.combine (m1 m2: Indets) : Lean.MetaM Indets :=
  match m1, m2 with
  | [] , [] => return []
  | x :: xs, y :: ys => return ((x.1, x.2 + y.2) :: (← combine xs ys))
  | _ , _ => failure

def Indets.updateIndex (i : Nat) (o : Nat) : Indets → Indets
  | [] => []
  | (ident, occ) :: is => if i == ident then (ident, occ + o) :: is
    else (ident, occ) :: updateIndex i o is

-- TODO: better handling of the coefficients
def MonomialInfo.combine {n} (m1 m2 : MonomialInfo n) : Lean.MetaM (MonomialInfo n) :=
  let (⟨c1,i1⟩,⟨c2,i2⟩) := (m1,m2)
  if c1 = 1 then return ⟨c2, ← i1.combine i2⟩
  else if c2 = 1 then return ⟨c2, ← i1.combine i2⟩
  else failure -- two different coefficients

#eval MonomialInfo.combine ⟨(1 : ZMod 20), [(1, 0), (2,1)]⟩ ⟨1, [(1, 0), (2,1)]⟩
#eval MonomialInfo.combine ⟨(1 : ZMod 20), [(1, 0), (2,1), (0,4)]⟩ ⟨1, [(1, 0), (2,1)]⟩
#eval MonomialInfo.combine ⟨(1 : ZMod 20), [(1, 0), (2,1)]⟩ ⟨4, [(1, 0), (2,1)]⟩
#eval MonomialInfo.combine ⟨(5 : ZMod 20), [(1, 0), (2,1)]⟩ ⟨4, [(1, 0), (2,1)]⟩

def MonomialInfo.updateIndex {n} (m : MonomialInfo n) (index : Nat) (occ : Nat) : MonomialInfo n :=
  ⟨m.coeff, m.indets.updateIndex index occ⟩

-- The function expects a normalized expression: M0 ∘ M1 ∘ ... ∘ Mn, where ∘ := + or -
-- Mx := N0 * N1 * ... Nn
-- Nx := number or indets or k ^ y, with k indet and y Nat

unsafe def monomial_aux
  {n : Nat}
  (st: SymbolTable)
  (m : MonomialInfo n)
  (pz: Q(ZMod $n))
  : Lean.MetaM (MonomialInfo n) :=
  match pz with
  | ~q($x + $y) | ~q($x - $y) => failure -- no addition at this point, wrong normalization
  | ~q((_ * _) ^ _) => failure           -- should have been normalized
  | ~q($x * $y) => (← monomial_aux st m x).combine (← monomial_aux st m y)
  | ~q($x ^ $y) =>
    if let some i := Lean.AssocList.find? x.constName st then return up m i (← evalNat y)
    else failure
  | n =>
    if let some i := Lean.AssocList.find? n.constName st then return up m i 1
    else return ⟨(← evalNat n), m.indets⟩
where
  evalNat n := Lean.Meta.evalExpr Nat q(Nat) n
  up m i v := MonomialInfo.updateIndex m i v

elab "monomial" t:term : tactic => do
  let ⟨1, ~q(Nat), ~q(10)⟩ ← inferTypeQ (← Lean.Elab.Term.elabTerm t (some q(Nat))) | throwError m!"!error! {t}"
  -- let t ← elabTermEnsuringTypeQ (u := Lean.levelOne) t q(ZMod $n)
  -- Lean.logInfo m!"Term: {t}"
  -- let st ← symbolTableFromDecl
  -- Lean.logInfo m!"Symbol table: {st.toList}"
  pure ⟨⟩
  --let mi ← monomial_aux st ⟨0, []⟩ te

example: 10 = 20 := by
  (monomial 10)
  sorry

theorem test {x: ZMod 290} {y: ZMod 290}
        --(h3 : (42 : ZMod 80) = 43)
        (h6: x * (y + 20 + 30) = 10)
        (h3: x = 20)
        (h8: y = 42 - 42)
 : x + 30 = y - 80 := by
  monomial 10
  -- ring_nf! at h6
  -- subst_eqs

partial def monomials {n : Q(Nat)} (st: SymbolTable) : (pz: Q(ZMod $n)) → Lean.MetaM (List Q(ZMod $n))
  | ~q($x + $y) => return (← monomials st x) ++ (← monomials st y)
  | ~q($x - $y) => return (← monomials st x) ++ (← monomials st y)
  | ~q($x * $y) => return (← monomials st x) ++ (← monomials st y)
  | ~q($x ^ $y) => return (← monomials st x) ++ (← monomials st y)
  | n => return [n]


opaque k : ZMod 10
opaque m : ZMod 10

opaque z : Nat

abbrev zdouble (a : ZMod 10) := a + a
abbrev wdouble (a : ZMod 10) := a - a

theorem test {x: ZMod 290} {y: ZMod 290}
        --(h3 : (42 : ZMod 80) = 43)
        (h6: x * (y + 20 + 30) = 10)
        (h3: x = 20)
        (h8: y = 42 - 42)
 : x + 30 = y - 80 := by
  symbol
  ring_nf! at h6
  subst_eqs

partial def literal: (pz: Q(Nat)) → MetaM Bool
  | ~q($x * $y) => return (← literal x) ∨ (← literal y)
  | n => return n.isLit

#eval q(ZMod 10)

mutual
partial def poly {n : Q(Nat)} : (pz: Q(ZMod $n)) → MetaM (List Q(ZMod $n))
  | ~q($x + $y) => return (← poly x) ++ (← poly y)
  | ~q($x - $y) => return (← poly x) ++ (← poly y)
  | n => return [n]

partial def monomials {n : Q(Nat)} : (pz: Q(ZMod $n)) → MetaM (List Q(ZMod $n))
  | ~q($x * $y) => return (← monomial x) ++ (← monomial y)
  | n => return [n]
end

elab "pz" : tactic => do
  Elab.Tactic.evalTactic (← `(tactic| norm_num at *))
  Elab.Tactic.withMainContext do
    for ldecl in ← getLCtx do
      if let some ty ← checkTypeQ (u := levelOne) ldecl.type q(Prop) then
        logInfo m!"{ldecl.userName} has value? {ldecl.hasValue}"
        match ty with
        | ~q(($p : ZMod $n) = $q) =>
          if (← Meta.isDefEq q q(0 : ZMod $n)) then
            logInfo m!"EQ0 left = {p}, right = {q}"
          else logInfo m!"EQ1 left = {p}, right = {q}"
        | _ => return

open Lean.Elab.Tactic in
elab "custom_have " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

partial def summands {α : Q(Type $u)} (inst : Q(Add $α)) : Q($α) → MetaM (List Q($α))
  | ~q($x + $y) => return (← summands inst x) ++ (← summands inst y)
  | n => return [n]

opaque k : Nat
opaque m : Nat

abbrev double (a : Nat) := a + a
#eval summands q(inferInstance) q(double k + m)

#eval show MetaM Bool from do
  let x : Q(Nat) := q(k + m)
  match x with
  | ~q(Nat.add $a $b) => return true
  | _ => return false

abbrev square (a : Nat) :=
  have : Add Nat := ⟨(· * ·)⟩
  a + a

#eval square 10
#eval summands q(inferInstance) q(k + square (square k))
#eval summands q(⟨(· * ·)⟩) q(k * square (square k))

def matchProd (e : Nat × Q(Nat)) : MetaM Bool := do
  let (2, ~q(1)) := e | return false
  return true

#eval do guard <| (←matchProd (2, q(1))) == true

def getNatAdd (e : Expr) : MetaM (Option (Q(Nat) × Q(Nat))) := do
  let ⟨Level.succ Level.zero, ~q(Nat), ~q($a + $b)⟩ ← inferTypeQ e | return none
  return some (a, b)

example (a b: ZMod 42): a + b = b + a := by
  sorry

-- theorem list_app_cons_not_nil (y: α) (xs ys: List α) :
--   [] ≠ xs ++ (y :: ys) := by
--   cases xs <;> (intro h'; contradiction)

-- elab "applyit" : tactic => do
--   let goal ← getMainTarget
--   if let some goalType ← checkTypeQ (u := levelOne) goal q(Prop) then
--     if let ~q([] ≠ $xs ++ ($y :: $ys)) := goalType then
--       logInfo m!"xs = {xs}, y = {y}, ys = {ys}"
--       evalTactic (← `(tactic| apply list_app_cons_not_nil))

-- elab "print_list_cons_in_hyp" : tactic => do
--   for ldecl in ← getLCtx do
--     if let some ty ← checkTypeQ (u := levelOne) ldecl.type q(Prop) then
--       if let ~q([] ≠ $xs ++ ($y :: $ys)) := ty then
--         let name := ldecl.userName
--         logInfo m!"name = {name}, xs = {xs}, y = {y}, ys = {ys}"

-- example(H1: 2 = 2): [] ≠ xs ++ (y :: ys) := by
--   print_list_cons_in_hyp
--   applyit

-- def traceGoals : TacticM Unit :=
--   do
--     logInfo m!"Lean version: {Lean.versionString}"
--     logInfo "All goals:"
--     let goals ← getUnsolvedGoals
--     logInfo m!"{goals}"
--     match goals with
--     | [] => return
--     | _ :: _ =>
--       logInfo "First goal's target:"
--       let target ← getMainTarget
--       logInfo m!"{target}"

-- elab "trace_goals" : tactic => traceGoals

-- theorem test (α: Type) (a : α) : 42 = 52 := by
--   trace_goals

-- def hypothesis : TacticM Unit :=
--   withMainContext do
--     let target ← getMainTarget
--     let lctx ← getLCtx
--     for ldecl in lctx do
--       if ! LocalDecl.isImplementationDetail ldecl then
--         let eq ← isDefEq (LocalDecl.type ldecl) target
--         if eq then
--           let goal ← getMainGoal
--           MVarId.assign goal (LocalDecl.toExpr ldecl)
--           return
--     failure

-- elab "hypothesis" : tactic => hypothesis

-- partial def destructAndExpr (hP : Expr) : TacticM Bool :=
--   withMainContext do
--     let target ← getMainTarget
--     let P ← inferType hP
--     if (← isDefEq P target) then
--       MVarId.assign (← getMainGoal) hP
--       return true
--     else
--       match Expr.and? P with
--       | Option.none => return false
--       | Option.some (_, _) =>
--         let hQ ← mkAppM ``And.left #[hP]
--         if (← destructAndExpr hQ) then return true
--         else
--           let hR ← mkAppM ``And.right #[hP]
--           destructAndExpr hR

-- def destructAnd (name : Name) : TacticM Unit :=
--   withMainContext do
--     let h ← getFVarFromUserName name
--     if !(← destructAndExpr h) then failure
