#!/usr/bin/env hy

(require hyrule [defmain])

(import intcode [IntcodeComputer])


(defmain []
  (setv computer (.from-file IntcodeComputer "input" :input 1))
  (.run-program computer)
  (print computer.output)
  (setv computer (.from-file IntcodeComputer "input" :input 2))
  (.run-program computer)
  (print computer.output))
