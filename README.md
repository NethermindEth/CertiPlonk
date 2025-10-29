![https://www.nethermind.io/](https://cdn.prod.website-files.com/63bcd69729ab7f3ec1ad210a/64bf04d14176fe2fb1aff258_Nethermind_Light_Horizontal%201.webp "Nethermind")

### The CertiPlonk verification framework

The CertiPlonk is a framework for extracting and formally verifying constraint systems from the [Plonky3 zkDSL](https://github.com/Plonky3/Plonky3) using the [Lean proof assistant](https://lean-lang.org/).
We have produced
1. A [fork of Plonky3](https://github.com/NethermindEth/Plonky3) that uses a symbolic air builder to extract constraint systems from Plonky3.
2. A [model of Plonky3 AIRs](https://github.com/NethermindEth/LeanZKCircuit-Plonky3) that acts as a basis for verifying the extracted circuits.
3. A [tactic](https://github.com/NethermindEth/FF_CVC5_Lean) for automatically proving goals over finite fields, by extracting the relevant goal and assumptions into CVC5's FF theory and reconstructing the resulting Gröbner basis reduction in Lean. 

More complete README coming soon!

# How Does It Work?

There are two key steps in formally verifying a constraint system using Plonky3: *(1) Constraint extraction into the Lean proof assistant*, and *(2) Proving desired properties using Lean*.

To illustrate this process, we'll walk through a simple example: adding two 8-bit numbers. The beauty of this approach is that from the circuit's perspective, nothing changes. You simply evaluate your AIR using our new *symbolic builder* — an AirBuilder designed for evaluating constraints symbolically and recording them for extraction into Lean.

## Step 1: Understanding the Circuit

For the complete constraint definitions, check out the implementation here: https://github.com/NethermindEth/Plonky3/blob/main/air/src/add_test.rs. As you'll see, this is standard Plonky3 code. No modifications are necessary to extract constraints from your circuit. The magic happens in the `extract_add8` test.

### Walking Through the Code

Let's break down the implementation. We're building an 8-bit adder with correct overflow semantics, performing checks at the binary level:
```
impl Air for Add8Air {

fn eval(&self, builder: &mut AB) {
   let main = builder.main();
   let local = main.row_slice(0).expect("Matrix is empty?");
```
The local variable holds our execution trace table where:
- local[0] contains input a
- local[1] contains input b
- local[2] contains the result c
- local[3] contains the overflow bit r

#### Constraint 1: Addition with Overflow
```
   let pow_of_2 = (0..=8).map(|i| AB::F::from_u64(1 << i)).collect::<Vec<_>>();
   // a + b = 2^8 * r + c
   builder.assert_eq(local[0] + local[1], (local[3] * pow_of_2[8]) + local[2]);
```
Our first constraint asserts that a + b = 2^8 * r + c, correctly modeling overflow behavior using an overflow bit `r`. When no overflow occurs, r = 0 and a + b = c. When overflow happens, r = 1 and c holds the wrapped value. This leads us to our next constraint on `r`.

#### Constraint 2: Boolean Constraint on Overflow Bit
```
   // r^2 - r = 0
   builder.assert_eq((local[3]) * (local[3]), (local[3]).into());
```
This constraint is straightforward: since `r` is our overflow bit, we constrain it to be either 0 or 1 using the equation r^2 = r.

#### Constraint 3: Binary Decomposition of Result
```
   // c = c₀ + 2*c₁ + 4*c₂ + ... + 128*c₇
   builder.assert_eq(
      (local[2]).into(),
      local[4..12]
         .iter()
         .enumerate()
         .map(|(i, cell)| *cell * pow_of_2[i])
         .sum::<AB::Expr>(),
   );
```
Next, we constrain the result `c` to be within the range of 8-bit numbers. While we could use a range check here, we've opted for explicit binary decomposition to keep the example self-contained. The result is represented as a sum of powers of 2, where columns 4 through 11 hold the bits `c₀`, `c₁`, ..., `c₇`.

#### Constraint 4: Boolean Constraints on Result Bits
```
   // ∀ i, cᵢ² - cᵢ = 0
   for c in &local[4..12] {
      builder.assert_eq(*c * *c, (*c).into());
   }
}
```
Finally, we ensure each bit `cᵢ` is boolean using the same x^2 = x constraint as `r`.

## Step 2: Extracting Constraints to Lean
Now we evaluate this constraint system using our symbolic air builder and extract all necessary information into Lean by calling `print_lean_constraints()`.

The output of the function will have the following structure:
```
--Base constraints---
…
-----Constraint simplification------
…
-----Interaction simplification-----
…
-----All hold definitions-----------
…
```

### Organizing the Lean Files
These sections need to be split into different Lean files:

1. Extraction.lean (use `ExtractionTemplate.lean` as template)
- Copy the content from `--Base constraints---` section
- Paste inside the namespace `NAME.extraction`
- Replace `NAME` with a descriptive circuit name (in our case: `Add8Air`)

2. Constraints.lean (use `ConstraintsTemplate.lean` as template)
- Constraint simplification → section `row_constraints` (all `constraint_n` and `constraint_n_of_simplification` definitions)
- Interaction simplification → section `interactions`
- All hold definitions → section `allHold`
- Section properties is where we'll write the properties we want to prove (we'll return to this later)

Don't forget to substitute NAME throughout the file.

### Defining Column Names

Since Plonky3 doesn't track column names, we need to specify them to make property proofs more intuitive. For this, create a new file called `Air.lean` and use this as template:

```
import Mathlib
import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

open Plonky3

set_option linter.unusedVariables false

#define_air "Add8Air" using "plonky3_encapsulation" where
   Column["a"]
   Column["b"]
   Column["c"]
   Column["r"]
   Column["c₀"]
   Column["c₁"]
   Column["c₂"]
   Column["c₃"]
   Column["c₄"]
   Column["c₅"]
   Column["c₆"]
   Column["c₇"]
```

This should be self-explanatory: we're defining an AIR table called `Add8Air` (keep naming consistent across files) and specifying names for each column. *Caution: the column order from `#define_air` command should be the same order of the Plonky3 circuit implementation*.

## Step 3: Writing Constraint Specifications
Now we can write specifications for each constraint using these named columns. You'll notice that constraint definitions are initially left as `sorry` (Lean's placeholder for unproven theorems). As example, let's fill the first two constraint (you can look the rest in the `Constraint.lean` file):

*Constraint 0*: a + b = 2^8 * r + c
```
def constraint_0 (air : Valid_Add8Air F ExtF) (row : ℕ) : Prop :=
   air.a row 0 + air.b row 0 - (air.r row 0 * 256 + air.c row 0) = 0
```

*Constraint 1*: r^2 - r = 0
```
def constraint_1 (air : Valid_Add8Air F ExtF) (row : ℕ) : Prop :=
   air.r row 0 * air.r row 0 - air.r row 0 = 0
```

Continue this pattern for all constraints.

For interactions (lookup tables), since we don't use them in this example, we specify an "empty constraint":
```
def constrain_interactions (air : Valid_Add8Air F ExtF) : Prop :=
   air.bus = List.flatMap (fun row ↦ []) (List.range (air.last_row + 1))
```

## Step 4: Proving Circuit Properties

With the integration complete, we can now prove the properties we care about. For this circuit, we'll prove *determinism*, *soundness*, and *completeness*. Note that `allHold` theorems are automatically generated by our Plonky3 infrastructure. See `Constraints.lean` file for the whole proof.

### Soundness
Soundness means that if the circuit constraints hold, column `c` contains the correct value of the 8-bit addition (modulo 256):
```
theorem spec_soundness_FBB
{air : Valid_Add8Air FBB ExtF}
{row}
(r_le : row ≤ air.last_row)
(h_a : air.a row 0 < 256)
(h_b : air.b row 0 < 256)
:
allHold_simplified air row r_le → air.c row 0 = (air.a row 0 + air.b row 0) % 256
:= by …
```

### Determinism
Determinism ensures that identical inputs produce identical outputs:
```
theorem determinism
{air₁ : Valid_Add8Air FBB ExtF}
{air₂ : Valid_Add8Air FBB ExtF}
{row₁ row₂}
(r_le₁ : row₁ ≤ air₁.last_row)
(r_le₂ : row₂ ≤ air₂.last_row)
(h_a : air₁.a row₁ 0 < 256)
(h_b : air₁.b row₁ 0 < 256)
(h_cstrs₁ : allHold_simplified air₁ row₁ r_le₁)
(h_cstrs₂ : allHold_simplified air₂ row₂ r_le₂)
(h_eq_a : air₁.a row₁ 0 = air₂.a row₂ 0)
(h_eq_b : air₁.b row₁ 0 = air₂.b row₂ 0)
:
air₁.a row₁ 0 = air₂.a row₁ 0 ∧
air₂.b row₂ 0 = air₂.b row₂ 0
  →
air₁.c row₁ 0 = air₂.c row₂ 0 ∧
air₁.r row₁ 0 = air₂.r row₂ 0 ∧
air₁.c₀ row₁ 0 = air₂.c₀ row₁ row₁ 0 = air₂.c₁ row₂ 0 ∧
air₁.c₂ row₁ 0 = air₂.c₂ row₂ 0 ∧
air₁.c₃ row₁ 0 = air₂.c₃ row₂ 0 ∧
air₁.c₄ row₁ 0 = air₂.c₄ row₂ 0 ∧
air₁.c₅ row₁ 0 = air₂.c₅ row₂ 0 ∧
air₁.c₆ row₁ 0 = air₂.c₆ row₂ 0 ∧
air₁.c₇ row₁ 0 = air₂.c₇ row₂ 0
:= by ...
```

### Completeness
Completeness proves that for any valid inputs, there exists an execution trace that satisfies all constraints:
```
theorem spec_completeness
{a b : FBB}
(h_a : a < 256)
(h_b : b < 256)
:
∃ (air : Valid_Add8Air FBB ExtF) (row : ℕ) (r_le : row ≤ air.last_row),
  air.a row 0 = a ∧ air.b row 0 = b ∧
  allHold_simplified air row r_le
:= by ...
```

And that's it! You now have a formally verified arithmetic circuit with machine-checked proofs of its key properties.