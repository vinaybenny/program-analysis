# program-analysis
Meta-analysis of program flow in typical Java programs using Soot Jimple. This repository will be used to refresh and re-learn the basics of of program analysis based on my previous coursework material.

- **source-taintanalysis:** This folder holds an analyser that performs intra-procedural and inter-procedural (context insensitive) taint analysis of program components tainted by user input. Any values provided by the user, and any values derived from this input are all considered tainted as a security vulnerability. This includes all data/expressions using that value or derived values, and any control flow in the program controlled by the value or derived values. This taint analyser only determines variables and expressions in the program that are tainted.
**Note:** The following code pieces: CDA.java, HelloWorld.java, InterMainDriver.java, InterTest.java, IntraTest.java are from the CS5218 Program Analysis (NUS) assignments. Only the authorship of classes that do the taint analysis belong to this repository.


## Requirements
- Soot 2.0, a Tool for Analyzing and Transforming Java Bytecode
