#!/usr/bin/env hy

(import collections [deque])
(import itertools [permutations])
(import queue [Queue])
(import threading [Thread])

(import more-itertools [last])
(import pytest [mark])

(import intcode [IntcodeComputer])

(require hyrule [defmain])


(defclass YieldingComputer [IntcodeComputer]

  (setv OUTPUTS-TYPE Queue)

  (defn [property] output [self]
    (last self.outputs.queue))

  (defn [output.setter] output [self value]
    ((. self outputs put) value)))


(defn
  [(mark.parametrize
    "program, expected, inputs"
    [#("3,15,3,16,1002,16,10,16,1,16,15,15,4,15,99,0,0" 43210 (range 5))
     #("3,23,3,24,1002,24,10,24,1002,23,-1,23,101,5,23,23,1,24,23,23,4,23,99,0,0" 54321 (range 5))
     #((+ "3,31,3,32,1002,32,10,32,1001,31,-2,31,1007,31,0,33,"
           "1002,33,7,33,1,33,31,31,1,32,31,31,4,31,99,0,0,0") 65210 (range 5))
     #((+ "3,26,1001,26,-4,26,3,27,1002,27,"
           "2,27,1,27,26,27,4,27,1001,28,-1,28,1005,28,6,99,0,0,5") 139629729 (range 5 10))
     #((+ "3,52,1001,52,-5,52,3,53,1,52,56,54,1007,54,5,55,1005,55,26,1001,54,"
           "-5,54,1105,1,12,1,53,54,53,1008,54,0,55,1001,55,1,55,2,53,55,53,4,"
           "53,1001,56,-1,56,1005,56,6,99,0,0,0,0,10") 18216 (range 5 10))])]
  test-day-07-examples [tmpchdir program expected inputs]
  (.write (/ tmpchdir "input") program)
  (assert (= (solve inputs) expected)))


(defn run-amplifiers [inputs]
  (setv inputs (list inputs)
        output-queues (deque (lfor i inputs (Queue)))
        input-queues (deque output-queues))
  (for [[value q] (zip inputs output-queues)]
       (.put q value))
  (.put (get input-queues 0) 0)
  (.rotate output-queues (- 1))
  (setv computers (lfor
                    [input output] (zip input-queues output-queues)
                    (.from-file YieldingComputer "input"
                                :input (iter
                                         (fn [* [input input]]
                                             (.get input :timeout 1))
                                         None)
                                :outputs output))
        threads (lfor c computers (Thread :target c.run-program)))
  (for [t threads] (.start t))
  (for [t threads] (.join t))
  (return (. (last computers) output)))


(defn solve [inputs]
  (return (max (map run-amplifiers (permutations inputs)))))


(defmain []
  (print (solve (range 5)))
  (print (solve (range 5 10))))
