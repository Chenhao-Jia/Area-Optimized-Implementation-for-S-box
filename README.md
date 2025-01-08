# Area-Optimized-Implementation-for-S-box
This repository contains the source codes of improved automatic search tool for efficient hardware implementations of lightweight S-boxes, which is described or founded in the paper "How Small Can S-boxes Be?", ToSC Volume 2025, Issue 1.
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

To help users better understand our model, we have provided two examples of STP models generated using the script file: the `KECCAK_17GE.cvc` file and the `SKINNY128_26.67GE.cvc` file. By running the commands `stp KECCAK_17GE.cvc` and `stp SKINNY128_26.67GE.cvc`, users can obtain the area optimization results for the KECCAK S-box and the SKINNY128 S-box, respectively.


## How to Analyze the Result File
To analyze the Result File, users need to first understand the meaning of the variables in the CVC model file. Taking the variables in the `KECCAK_17GE.cvc` file as an example, in Equation (24) of the paper, the variables representing the control logic gates' four input connections to the preceding gate or input bit are denoted as `a,b,c,d` respectively. In this file, we use the variable `a` to represent them, with subscripts incrementing sequentially. The `KECCAK_17GE.cvc` file uses a three-input gate model. In the constraints between Line 3379 and Line 3381, we fixed the order of inputs for the first logic gate in the S-box implementation circuit. In the constraints between Line 3383 and Line 3385, we fixed the order of inputs for the second logic gate, and so on. For more information on the meaning of other variables, please refer to the main body of the paper. 

Users typically analyze the model in cases where a solution exists. When designing the S-box, users generally impose constraints based on cryptographic properties in the model and are interested in the S-box's LUT (Look-Up Table). To obtain the LUT for the S-box, users need to search for all the variable `y` values in the result file and assemble them into the LUT. When searching for the optimized circuit of the S-box, users are usually concerned with the circuit structure of the S-box. In this case, users need to extract all the variable `a` values and construct the S-box circuit diagram based on the approach presented in the paper.
