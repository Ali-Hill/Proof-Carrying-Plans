(setq domainfile "blocksworld-domain.pddl")
(setq problemfile "blocksworld-problem.pddl")
(setq outputfile "blocksworld")

(setq plan '((pickup_from_table 'e)
(putdown_on_stack 'e 'f1)
(pickup_from_table 'd)
(putdown_on_stack 'd 'e)
(pickup_from_table 'c)
(putdown_on_stack 'c 'd)
(pickup_from_table 'b)
(putdown_on_stack 'b 'c)
(pickup_from_table 'a)
(putdown_on_stack 'a 'b)))

(time
  (progn
    (load "../auto/convert_agda")
    (load "../auto/solver")))

(print "compiling...")

(time (run-shell-command (concatenate 'string "agda " outputfile ".agda")))

;Real time: 0.030145 sec.
;Run time: 0.030047 sec.
;Space: 2345320 Bytes
;GC: 2, GC time: 0.003504 sec.
;"compiling..." Checking blocksworld (/home/alasdair/Documents/PCPLogic_Experimental/PCPLogic-master (1)/PCPLogic-master/Examples/Blockworld/blocksworld.agda).
;Real time: 16.072989 sec.
;Run time: 1.13E-4 sec.
;Space: 376 Bytes

