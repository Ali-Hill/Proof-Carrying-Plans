(setq domainfile "blocksworld-domain.pddl")
(setq problemfile "blocksworld-problem.pddl")
(setq outputfile "blocksworld")


(setq plan
  '((pickup_from_table 'a)
   (putdown_on_stack 'a 'b)))

(time
  (progn
    (load "../auto/convert_agda")
    (load "../auto/solver")))

(print "compiling...")

(time (run-shell-command (concatenate 'string "agda " outputfile ".agda")))

#||
Real time: 0.017343 sec.
Run time: 0.017103 sec.
Space: 2358736 Bytes
GC: 1, GC time: 0.003505 sec.
"compiling..." Checking blocksworld (/home/alasdair/Documents/PCPLogic_Experimental/PCPLogic-master (1)/PCPLogic-master/Examples/Automation/Blockworld/blocksworld.agda).

Real time: 9.80057 sec.
Run time: 8.2E-5 sec.
Space: 376 Bytes
||#


