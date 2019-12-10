#!/usr/bin/env hy

(import [intcode [IntcodeComputer read-puzzle-input]])


(defmain [&rest _]
  (setv computer (.from-file IntcodeComputer "input" :input 1))
  (.run-program computer)
  (print computer.output)
  (setv computer (.from-file IntcodeComputer "input" :input 5))
  (.run-program computer)
  (print computer.output))
