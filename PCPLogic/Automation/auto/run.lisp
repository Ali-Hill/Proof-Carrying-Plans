(setq domainfile "blocksworld-domain.pddl")
(setq problemfile "blocksworld-problem.pddl")
(setq outputfile "blocksworld")
(setq planfile "solution.plan")

(time
  (progn
    (load "../auto/convert_agda")
    (load "../auto/solver")))

(print "typechecking...")

(time (run-shell-command (concatenate 'string "agda " outputfile "Example.agda")))
