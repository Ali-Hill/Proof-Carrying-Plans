(setq domainfile "mprime-domain.pddl")
(setq problemfile "mprime-problem.pddl")
(setq outputfile "mprime")

(setq plan '((feast 'aesthetics 'shrimp 'scallion 'quebec 'bosnia)
(feast 'aesthetics 'scallion 'muffin 'surrey 'quebec)
(overcome 'hangover 'aesthetics 'muffin 'mars 'vulcan)
(feast 'aesthetics 'muffin 'arugula 'oregon 'kentucky)
(feast 'aesthetics 'arugula 'scallop 'oregon 'kentucky)
(succumb 'hangover 'aesthetics 'scallop 'mars 'vulcan)
(feast 'aesthetics 'scallop 'grapefruit 'bosnia 'oregon)
(overcome 'sciatica 'aesthetics 'grapefruit 'mars 'vulcan)
(drink 'cherry 'grapefruit 'kentucky 'oregon 'bosnia 'surrey 'quebec)
(feast 'aesthetics 'grapefruit 'wurst 'surrey 'quebec)
(succumb 'sciatica 'aesthetics 'wurst 'mars 'vulcan)))

(time
  (progn
    (load "../auto/convert_agda")
    (load "../auto/solver")))

(print "compiling...")

(time (run-shell-command (concatenate 'string "agda " outputfile ".agda")))

;Real time: 0.087704 sec.
;Run time: 0.087562 sec.
;Space: 16899064 Bytes
;GC: 19, GC time: 0.024812 sec.
;"compiling..." Checking mprime (/home/alasdair/Documents/PCPLogic_Experimental/P;CPLogic-master (1)/PCPLogic-master/Examples/mprime/mprime.agda).

;Real time: 50.04608 sec.
;Run time: 1.26E-4 sec.
;Space: 360 Bytes
