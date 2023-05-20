# Proof-Carrying Plans Overview

This repository contains all versions of the inference systems created for the submission of the PhD: Planning Problems as Types, Plans as Programs: A Dependent Types Infrastructure for Verification and Reasoning about Automated Plans in Agda.

## Repo Structure 

The general repo structure follows:

```
Inference system
-- Automation
-- src
---- Proofs
-- test 
```

All inference systems such as `PCPLogic` are self contained and therefore contain their own agda library and README files.

*Automation* contains all of the scripts to automatically generate the agda code to validate plans. It also contains all examples given in the results tables. These example do not contain the generated agda files just the scripts that generate them. 

*src* contains all of the agda code necessary to define the relevant inference system. 

*Proofs* contain all of the soundness and consistency proofs given for that inference system in the thesis. 

*test* contains miscellaneous examples for the various inference systems. For example in `PCPStarLogicTyped` it contains the relevant code for the enriched handlers examples.

## Chapter Mapping

```
Chapter 4 -> PCPLogic
Chapter 5 -> PCPRLogic
Chapter 6 -> PCPStarLogic & PCPRStarLogicTyped
```

Note on Chapter 6: `PCPStarLogic` contains all of the automation and the universal property example. `PCPStarLogicTyped` contains the enriched handler examples for the taxi domain. 

Note on Automation Results: Automation results are contained in the relevant inference systems folder.

`ConsistentPCPLogic` is an additional repository showcasing another strategy for making PCPLogic consistent not included in the PhD thesis. 

## Versioning 

All inference systems have been tested with the following versions:

Agda Version: 2.6.3

Libraries: 

Agda Standard Library:

    Version: 2.0 
    
    repo   : https://github.com/agda/agda-stdlib/
    
    Commit : 7c5f3ff90fa7ff1b9d4a522050291119f209a85b

Agda Prelude:

    Version: Master
    
    repo   : https://github.com/UlfNorell/agda-prelude
    
    Commit : 3d143d6d0a3f75966602480665623e87233ff93e
    

