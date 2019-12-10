#!/usr/bin/env hy

(import [intcode [IntcodeComputer read-puzzle-input]])


(setv TARGET-OUTPUT 19690720)


(defn solve-for [memory noun verb]
  (setv memory (list memory))
  (assoc memory 1 noun)
  (assoc memory 2 verb)
  (setv computer (IntcodeComputer memory))
  (.run-program computer)
  (return (get computer.memory 0)))


(defn part2 [memory]
  (next
    (gfor
      noun (range 100)
      verb (range 100)
      :if (= (solve-for memory noun verb) TARGET-OUTPUT)
      (+ (* 100 noun) verb))))


(defmain [&rest _]
  (->>
    (read-puzzle-input "input")
    (setv memory))
  (->
    memory
    (solve-for 12 2)
    (print))
  (->
    memory
    (part2)
    (print)))
