#!/usr/bin/env hy

(import [intcode [IntcodeComputer read-puzzle-input]])


(defmain [&rest _]
  (setv computer (.from-file IntcodeComputer "input" :input 1))
  (.run-program computer)
  (if (any (cut (. computer outputs) None -1)) (raise (Exception "error in program exection")))
  (print computer.output)
  (setv computer (.from-file IntcodeComputer "input" :input 5))
  (if (any (cut (. computer outputs) None -1)) (raise (Exception "error in program exection")))
  (.run-program computer)
  (print computer.output))
