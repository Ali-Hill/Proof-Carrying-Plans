# PCP Logic

This folder contains the PCP Logic inference system. This folder contains all of the automation examples for PCP Logic as well as a blocksworld example and a naughty example deriving an inconsistent state.

# How to Run

All examples are contained in the Automation folder. An example can be run by executing the relevant run.lisp file. 

## Example with Blocks World 

Go to the root of the folder then run
```shell
cd Automation/Blocksworld
clisp run.lisp
```

## Use Automation for Custom PDDL Files

1. Create build folder and add it to the `agda-planning.agda-lib` file. Note that the folder is assumed to be 1 folder deep into Automation e.g. `Automation/ExampleProblem`. 
2. Add the PDDL domain and problem files to the created folder. 
3. Add the plan file that you want to verify to the folder.
5. Copy `run.lisp` from the `Automation/auto` folder into the created folder. 
4. Change the `domainfile`, `problemfile` and `planfile` variables in `run.lisp` to the relevant files.
5. Change the `outputfile` variable to the change the agda output file name.
6. Run `run.lisp` with the command `clisp run.lisp`

*Note on plan file format*: The plan is assumed to be a list of PDDL actions in the form ((action1)(action2)...).

