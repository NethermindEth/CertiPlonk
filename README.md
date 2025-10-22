![https://www.nethermind.io/](https://cdn.prod.website-files.com/63bcd69729ab7f3ec1ad210a/64bf04d14176fe2fb1aff258_Nethermind_Light_Horizontal%201.webp "Nethermind")

### The CertiPlonk verification framework

The CertiPlonk is a framework for extracting and formally verifying constraint systems from the [Plonky3 zkDSL](https://github.com/Plonky3/Plonky3) using the [Lean proof assistant](https://lean-lang.org/).
We have produced
1. A [fork of Plonky3](https://github.com/NethermindEth/Plonky3) that uses a symbolic air builder to extract constraint systems from Plonky3.
2. A [model of Plonky3 AIRs](https://github.com/NethermindEth/LeanZKCircuit-Plonky3) that acts as a basis for verifying the extracted circuits.
3. A [tactic](https://github.com/NethermindEth/FF_CVC5_Lean) for automatically proving goals over finite fields, by extracting the relevant goal and assumptions into CVC5's FF theory and reconstructing the resulting Gröbner basis reduction in Lean. 

More complete README coming soon! 
