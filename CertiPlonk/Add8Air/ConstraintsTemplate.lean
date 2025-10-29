import CertiPlonk.Add8Air.Air
import CertiPlonk.Add8Air.Extraction
import CertiPlonk.Fundamentals.BabyBear
import CertiPlonk.Util

import LeanZKCircuit_Plonky3.Interactions

namespace NAME.constraints

  section constraint_simplification

    -- Note: `air` and `row` are not included as section variables
    --       so that the file can still be used with `sorry`
    --       during the extraction process
    --       Additionally, the proofs are split into more stages
    --       than required so that it can be easily checked that all
    --       intending folding is occuring

    variable [Field F] [Field ExtF]

    section row_constraints

      -- constraints and constraints_of_extraction

    end row_constraints

    section interactions

      -- Note: use `congr; funext row` after `simp [h]; clear h` in
      --       the lemmas below to get the expression in the infoview

      --busRows, constrain_interactions, and constrain_interactions_of_extraction

    end interactions

  end constraint_simplification

  section allHold

    -- constraint list and allHold

  end allHold

  section properties

    variable[Field ExtF]

  end properties

end NAME.constraints
