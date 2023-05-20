# PCP* Logic

This inference system is a version of PCP* Logic that can be used with untyped PDDL domains. This folder contains all of the automation examples for PCP* Logic, a code extraction example and the universal property example for Blocks World.  

# How to Run

All examples are contained in the Automation folder. An example can be run by executing the relevant run.lisp file. 

## Example with Blocks World 

Go to the root of the folder then run
```shell
cd Automation/Blocksworld
clisp run.lisp
```

## Example extraction with Blocks World 

Go to the root of the folder then run:
```shell
cd Automation/Blocksworld
clisp runWithExtraction.lisp
```

Run the resultant binary file with:

```shell
./run
```

Note that only the Blocksworld folder contains a `runWithExtraction.lisp` file however this file works with any given example provided that the `domainfile` and `problemfile` variables get updated. See the relevant `run.lisp` file for the correct definitions of these variables. 

## Use Automation for Custom PDDL Files

1. Create build folder and add it to the `agda-planning.agda-lib` file. Note that the folder is assumed to be 1 folder deep into Automation e.g. `Automation/ExampleProblem`. 
2. Add the PDDL domain and problem files to the created folder. 
3. Add the plan file that you want to verify to the folder.
5. Copy `run.lisp` from the `Automation/auto` folder into the created folder. 
4. Change the `domainfile`, `problemfile` and `planfile` variables in `run.lisp` to the relevant files.
5. Change the `outputfile` variable to the change the agda output file name.
6. Run `run.lisp` with the command `clisp run.lisp`

*Note on plan file format**: The plan is assumed to be a list of PDDL actions in the form ((action1)(action2)...).

*Note on binary extraction*: To do extract a binary file do the above steps with the `runWithExtraction.lisp` file instead of the `run.lisp file`.

