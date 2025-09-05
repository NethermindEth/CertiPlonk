import Lean
import Qq

import FF.CoCoA

open Lean Elab Term Qq

namespace EzPz

namespace CoCoA

declare_syntax_cat cocoa
declare_syntax_cat reduction
declare_syntax_cat polynomial
declare_syntax_cat zmodeq

abbrev Cocoa := TSyntax `cocoa
abbrev Reduction := TSyntax `reduction
abbrev Polynomial := TSyntax `polynomial
abbrev ZmodEq := TSyntax `zmodeq

syntax "UNSAT" "(" "REDUCTIONS" "(" reduction* ")" "POLYNOMIALS" "(" polynomial* ")" ")" : cocoa

syntax indexedTerm := num noWs "{" zmodeq "}"

syntax "P(" num "," zmodeq ")" : polynomial

syntax "M(" num "," num ")" : reduction
syntax "S(" indexedTerm "," indexedTerm "," num ")" : reduction
syntax "R(" num ";" indexedTerm,* ";" num ")" : reduction 

syntax num : zmodeq
syntax ident : zmodeq
syntax "-" num : zmodeq
syntax "diseq" "[" num "]" : zmodeq
syntax zmodeq " * " zmodeq : zmodeq
syntax zmodeq " + " zmodeq : zmodeq
syntax zmodeq " - " zmodeq : zmodeq
syntax ident "^" num : zmodeq

syntax "[zmodeq|" zmodeq "]" : term
syntax "[CoCoA|" cocoa "]" : term

def translateIdent (idn : TSyntax `ident) : MacroM Term :=
  let idn := Syntax.mkStrLit idn.getId.toString
  `(Γ[$idn]!)

private partial def translateZmodEq : ZmodEq → MacroM Term
  | `(zmodeq|$n:num) => `($n)
  | `(zmodeq|$idn:ident) => translateIdent idn
  | `(zmodeq|-$n) => `(-$n)
  | `(zmodeq|diseq[$n]) =>
    let idn := mkIdent (Name.mkSimple s!"diseq{n.getNat}")
    translateIdent idn
  | `(zmodeq|$lhs * $rhs) => do
    let lhs ← translateZmodEq lhs
    let rhs ← translateZmodEq rhs
    `($lhs * $rhs)
  | `(zmodeq|$lhs + $rhs) => do
    let lhs ← translateZmodEq lhs
    let rhs ← translateZmodEq rhs
    `($lhs + $rhs)
  | `(zmodeq|$lhs - $rhs) => do
    let lhs ← translateZmodEq lhs
    let rhs ← translateZmodEq rhs
    `($lhs - $rhs)
  | `(zmodeq|$lhs:ident ^ $rhs:num) => do
    let lhs ← translateIdent lhs
    `($lhs ^ $rhs)
  | stx => Macro.throwError s!"Unrecognised: {stx}"

-- partial def translateZmodEq : ZmodEq → MacroM Term
--   | `(zmodeq|$zmodeq) => do
--   let zmodeq ← translateZmodEq_aux zmodeq
--   `(fun (Γ : Std.HashMap String (ZMod 41)) ↦ $zmodeq)

macro_rules
  | `([zmodeq|$z]) => translateZmodEq z

macro_rules
  | `(indexedTerm|$n{$t}) => do let t ← translateZmodEq t; `(Ast.IndexedTerm.mk $n $t)

open Ast.Polynomial Ast.Reduction

def translateIndexedTerm : TSyntax `EzPz.CoCoA.indexedTerm → MacroM Term
  | `(indexedTerm|$n{$t}) => do let t ← translateZmodEq t; `(Ast.IndexedTerm.mk $n $t)
  | stx => Macro.throwError s!"Expected IndexedTerm. Got: {stx}"

def translateReduction : Reduction → MacroM Term
  | `(reduction|M($n₁, $n₂)) => `(M $n₁ $n₂)
  | `(reduction|S($i₁{$t₁}, $i₂{$t₂}, $n)) => do
    let t₁ ← translateZmodEq t₁
    let t₂ ← translateZmodEq t₂
    `(S ⟨$i₁, $t₁⟩ ⟨$i₂, $t₂⟩ $n)
  | `(reduction|R($n₁; $[$its],*; $n₂)) => do
    let indexedTerms ← its.mapM translateIndexedTerm
    `(R $n₁ $n₂ #[$indexedTerms,*])
  | _ => default

def translatePolynomial : Polynomial → MacroM Term
  | `(polynomial|P($n, $t)) => do let t ← translateZmodEq t; `(P $n $t)
  | _                       => default

def translateCocoa : Cocoa → MacroM Term
  | `(cocoa|UNSAT(REDUCTIONS($[$reductions]*) POLYNOMIALS($[$polynomials]*))) => do
    let reductions ← reductions.mapM translateReduction
    let polynomials ← polynomials.mapM translatePolynomial
    `(Ast.Cocoa.mk #[$reductions,*] #[$polynomials,*])
  | _ => default

macro_rules
  | `([CoCoA|$cocoa]) => do
  let cocoa ← translateCocoa cocoa
  `(fun (Γ : Std.HashMap String (ZMod 41)) ↦ $cocoa)

#check [CoCoA|
  UNSAT(
    REDUCTIONS(
      M(13, 14)
      S(11{1}, 12{diseq[0]}, 13)
      R(5; 6{c1*x}, 8{2*c1*x}, 8{c2*x}, 9{2*c1*x}, 9{2*c2*x}, 9{c3*x}, 10{2*c1*x}, 10{2*c2*x}, 10{2*c3*x}, 10{c4*x}, 6{7*x}, 8{5*x}, 9{3*x}, 10{x}, 6{-1}, 8{-1}, 9{-1}, 10{-1}; 12)
      R(7; 6{x*diseq[0]}, 8{x*diseq[0]}, 9{x*diseq[0]}, 10{x*diseq[0]}; 11)
    )
    POLYNOMIALS(
      P(5, c1^2*x +2*c1*c2*x +c2^2*x +2*c1*c3*x +2*c2*c3*x +c3^2*x +2*c1*c4*x +2*c2*c4*x +2*c3*c4*x +c4^2*x -c1 -c2 -c3 -c4)
      P(6, c1 -1)
      P(7, c1*x*diseq[0] +c2*x*diseq[0] +c3*x*diseq[0] +c4*x*diseq[0] -diseq[0] +1)
      P(8, c2 -1)
      P(9, c3 -1)
      P(10, c4 -1)
      P(11, x*diseq[0] +98589*diseq[0] -98589)
      P(12, x +98589)
      P(13, -98589)
      P(14, 1)
    )
)]

-- #check [zmodeq|c1^2*x +2*c1*c2*x +c2^2*x +2*c1*c3*x +2*c2*c3*x +c3^2*x +2*c1*c4*x +2*c2*c4*x +2*c3*c4*x +c4^2*x -c1 -c2 -c3 -c4]
   
end CoCoA

end EzPz
