import Mathlib.Data.ZMod.Basic
import Qq
import Lean
import Lean.Data.NameMap
import FF.Sexp
import FF.Normalise

open Qq Lean

inductive FF.Term where
  | Lit : Nat → Term         -- (as ffℤ FFℕ)
  | Sym : Name → Term
  | Neg : Term → Term
  | Sub : Term → Term → Term -- ff.neg
  | Add : Term → Term → Term -- ff.add
  | Mul : Term → Term → Term -- ff.mul
  | Exp : Term → Nat → Term  -- ff.mul x₁ x₂ ... ×ₙ
  | Eq  : Term → Term → Term
deriving Repr

partial def toString (fs: Nat) : FF.Term → String
  | .Lit n   => "(as ff" ++ n.repr ++ " FF" ++ fs.repr ++ ")"
  | .Sym n   => n.toString
  | .Neg n   => "(ff.neg " ++ toString fs n ++ ")"
  | .Sub m n => "(ff.add " ++ toString fs m ++ " (ff.neg " ++ toString fs n ++ ")"
  | .Add m n => "(ff.add " ++ toString fs m ++ " " ++ toString fs n  ++ ")"
  | .Mul m n => "(ff.mul " ++ toString fs m ++ " " ++ toString fs n  ++ ")"
  | .Exp b p => "(ff.mul" ++ (List.replicate p b).foldl (· ++ " " ++ toString fs ·) "" ++ ")"
  | .Eq  l r => "(= " ++ toString fs l ++ " " ++ toString fs r ++ ")"

-- From lean-smt Recognizers.lean
namespace Lean.Expr
  def natLitOf? (e : Expr) (α : Expr) : Option Nat :=
    let_expr OfNat.ofNat β n _ := e | none
    if β == α then
      n.rawNatLit?
    else
      none

  def hAddOf? (e : Expr) (α : Expr) (β : Expr) : Option (Expr × Expr) :=
    let_expr HAdd.hAdd γ δ _ _ x y := e | none
    if γ == α && δ == β then
      return (x, y)
    else
      none

  def hSubOf? (e : Expr) (α : Expr) (β : Expr) : Option (Expr × Expr) :=
    let_expr HSub.hSub γ δ _ _ x y := e | none
    if γ == α && δ == β then
      return (x, y)
    else
      none

  def hMulOf? (e : Expr) (α : Expr) (β : Expr) : Option (Expr × Expr) :=
    let_expr HMul.hMul γ δ _ _ x y := e | none
    if γ == α && δ == β then
      return (x, y)
    else
      none

  def hPowOf? (e : Expr) (α : Expr) (β : Expr) : Option (Expr × Expr) :=
    let_expr HPow.hPow γ δ _ _ x y := e | none
    if γ == α && δ == β then
      return (x, y)
    else
      none

  def negOf? (e : Expr) (α : Expr) : Option Expr :=
    let_expr Neg.neg β _ x := e | none
    if β == α then
      return x
    else
      none

  def eqOf? (e : Expr) (α : Expr) : Option (Expr × Expr) :=
    let_expr Eq β _ x y := e | none
    if β == α then
      return (x, y)
    else
      none
namespace Lean.Expr

mutual

partial def translate! (e : Expr) : MetaM FF.Term := do
  let some tm ← translate? e | throwError "no translation for {e}"
  return tm

partial def translate? (e: Expr) : /-StateT FF.TranslateS-/ MetaM (Option FF.Term) := do
  let ⟨Level.succ Level.zero, ~q(ZMod $s), _⟩ ← inferTypeQ e | throwError f!"Not ZMod expression."
  let mkZMod := q(ZMod $s)
  if let some n := e.natLitOf? mkZMod then
    return some (.Lit n)
  else if let some (x, y) := e.hAddOf? mkZMod mkZMod then
    return some (.Add (← translate! x) (← translate! y))
  else if let some (x, y) := e.hMulOf? mkZMod mkZMod then
    return some (.Mul (← translate! x) (← translate! y))
  else if let some (x, y) := e.hSubOf? mkZMod mkZMod then
    return some (.Sub (← translate! x) (← translate! y))
  else if let some x := e.negOf? mkZMod then
    return some (.Neg (← translate! x))
  else if let some (b, p) := e.hPowOf? mkZMod (.const ``Nat []) then
    let p ← unsafe Meta.evalExpr ℕ q(ℕ) p
    return some (.Exp (← translate! b) p)
  else if let some n := e.fvarId? then
    return some (.Sym $ ←Lean.FVarId.getUserName n)
  else
    return none
end

structure FF.TranslateST where
  asserts : List FF.Term

def translateEq (eQ : Q(Prop)) : MetaM FF.Term := do
  match eQ with
  | ~q(@Eq (ZMod $k) $lhs $rhs) => return .Eq (← translate! lhs) (← translate! rhs)
  | _ => throwError "Not Eq ZMod expression"

def isZModSym (goal : MVarId) (e : Expr) : MetaM (Option ℕ) := goal.withContext do
  let (``ZMod, #[size]) := e.getAppFnArgs | return .none
  let size ← unsafe Lean.Meta.evalExpr ℕ q(ℕ) size
  return .some size

def zModSyms (goal : MVarId) : MetaM (Array (FVarId × ℕ)) := goal.withContext do
  (← getLocalHyps).filterMapM f
where
  f e := Lean.Meta.inferType e >>= isZModSym goal >>= Option.mapM (λ a => return (e.fvarId!, a))

elab "test" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let (ids, szs) := (← zModSyms goal).unzip
  unless szs.sortDedup.size = 1 do throwError "Multiple field sizes"
  logInfo m!"(define-sort FF{szs[0]!} () (_ FiniteField {szs[0]!}))"
  let vars ← ids.mapM (·.getUserName)
  for v in vars do
    logInfo m!"(declare-fun {Lean.Name.toString v} () FF{szs[0]!})"
  let (zeqs, b) ← EzPz.zModEqs goal
  let terms := (← zeqs.mapM (·.getType)).mapM translateEq
  for i in ←terms do
    logInfo m!"term: {toString szs[0]! i}"

example {x y z : ZMod 394357} [Fact (Nat.Prime 394357)]
  (h : x ^ 3 = 3)
  (h' : z * x * (-9) * y + x * 9 - z * 2 = 3)
  (h'' : z * x * (-5) * y + x * 9 - z * 2 = 3)
  (h₁ : x * 4 * y * 4 * x + z^4 = 2)
  (h₂ : z^3 + x^2 + x^2 = 0)
  (h₃ : 5 * x * y + y * x + 4 * x^2 + 5 * z^3 * x = 0)
  (h₄ : x * y + y * x + z^3 * x = 0)
  (h₆ : 2 * 394356 * x = 0)
  : x - 42 = 0 := by
  test
  sorry
