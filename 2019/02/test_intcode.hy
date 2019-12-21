(import [pytest [mark]])

(import [intcode [IntcodeComputer parse]])


(with-decorator
  (mark.parametrize
    "initial, expected"
    [(, "1,0,0,0,99" "2,0,0,0,99")
     (, "2,3,0,3,99" "2,3,0,6,99")
     (, "2,4,4,5,99,0" "2,4,4,5,99,9801")
     (, "1,1,1,4,99,5,6,0,99" "30,1,1,4,2,5,6,0,99")])
  (defn test-day-02-examples [initial expected]
    (setv computer (.from-string IntcodeComputer initial))
    (.run-program computer)
    (assert (= computer.memory (parse expected)))))


(defn test-day-02-part-1-example []
  (setv computer (.from-file IntcodeComputer "input_test"))
  (.run-program computer)
  (assert (= 3500 (get computer.memory 0))))
