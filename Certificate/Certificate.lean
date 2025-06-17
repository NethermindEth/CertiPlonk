import Certificate.SAT
import Certificate.UNSAT

namespace CertiPlonk

inductive Certificate where
  | sat   : Model → Certificate
  | unsat : Option Reduction → Certificate

end CertiPlonk
