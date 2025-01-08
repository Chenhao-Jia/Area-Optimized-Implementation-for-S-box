# Area-Optimized-Implementation-for-S-box
This repository contains the source codes of improved automatic search tool for efficient hardware implementations of lightweight S-boxes, which is described or founded in the paper "How Small Can S-box Be?", ToSC Volume 2025, Issue 1.
## Required Software
This model establishes constraints based on the satisfiability problem to search for whether an S-box exists under specific constraints. The required software is the SMT-based STP solver, which can be run on Linux or Mac OS. STP solver supports solving using the CVC language, which based on the Conjunctive Normal Form (CNF).  The necessary sources for the STP solver are shown below.
 * Homepage: [https://stp.github.io/](https://stp.github.io/)
 * Source Code: [https://github.com/stp/stp](https://github.com/stp/stp)
 * Syntax Rules of CVC Language: [https://stp.readthedocs.io/en/stable/cvc-input-language.html](https://stp.readthedocs.io/en/stable/cvc-input-language.html)

## How to Run
To help generate the CVC language model more quickly, we have written a script file, which is placed in `main.cpp`. In the script file, we have modularized the constraints for various cryptographic properties and circuit implementations, and added detailed notes in each module. Users can generate the corresponding STP solving model by selecting the cryptographic properties or circuit implementations they want to constrain. Running the script will generate a `Model.cvc` file, and users can modify the name in `main.cpp` before calling the STP solver to solve the `Model.cvc` file. The specific operations are as follows:
```
g++ main.cpp
./a.out
stp Model.cvc
```
