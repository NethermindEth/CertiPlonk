### The CertiPlonk verification framework

The CertiPlonk is a framework for extracting and formally verifying constraint systems from the (Plonky3 zkDSL)[https://github.com/Plonky3/Plonky3].
We have produced:
1. A (fork of Plonky3)[https://github.com/NethermindEth/Plonky3] that uses a symbolic air builder to extract constraint systems from Plonky3.
2. A (model of Plonky3 AIRs)[https://github.com/NethermindEth/LeanZKCircuit-Plonky3] that acts as a basis for verifying the extracted circuits.
