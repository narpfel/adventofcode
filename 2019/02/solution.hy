#!/usr/bin/env hy

(import [pytest [mark]])


(setv TARGET-OUTPUT 19690720)


(defn read-input [filename]
  (with [f (open filename)]
    (->>
      (.read f)
      (parse)
      (return))))


(defn parse [string]
  (->
    string
    (.strip)
    (.split ",")
    ((fn [xs] (map int xs)))
    (list)
    (return)))


(defn run-program [memory]
  (defn lookup [i] (get memory i))
  (setv index 0)
  (while True
    (setv command (lookup index))
    (cond
      [(= command 1)
       (setv operation +)]
      [(= command 2)
       (setv operation *)]
      [(= command 99)
       (break)]
      [True (raise (ValueError f"invalid opcode {command !r}"))])
    (assoc memory
           (lookup (+ index 3))
           (operation
             (lookup (lookup (+ index 1)))
             (lookup (lookup (+ index 2)))))
    (+= index 4)))


(defn solve-for [memory noun verb]
  (setv memory (list memory))
  (assoc memory 1 noun)
  (assoc memory 2 verb)
  (run-program memory)
  (return (get memory 0)))


(defn part2 [memory]
  (next
    (gfor
      noun (range 100)
      verb (range 100)
      :if (= (solve-for memory noun verb) TARGET-OUTPUT)
      (+ (* 100 noun) verb))))


(with-decorator (mark.parametrize "initial, expected" [(, "1,0,0,0,99" "2,0,0,0,99")
                                                      (, "2,3,0,3,99" "2,3,0,6,99")
                                                      (, "2,4,4,5,99,0" "2,4,4,5,99,9801")
                                                      (, "1,1,1,4,99,5,6,0,99" "30,1,1,4,2,5,6,0,99")])
  (defn test-examples [initial expected]
    (setv memory (parse initial))
    (run-program memory)
    (assert (= memory (parse expected)))))


(defn test-part-1-example []
  (->>
    (read-input "input_test")
    (setv memory))
  (run-program memory)
  (assert (= 3500 (get memory 0) )))


(defmain [&rest _]
  (->>
    (read-input "input")
    (setv memory))
  (->
    memory
    (solve-for 12 2)
    (print))
  (->
    memory
    (part2)
    (print)))
