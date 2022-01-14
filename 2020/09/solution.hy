#!/usr/bin/env hy

(import collections [deque])
(import itertools [combinations islice])

(require hyrule [-> ->> defmain])

(defn is-sum-of? [k numbers needle]
  (->
    numbers
    (combinations :r k)
    ((fn [xss] (map (fn [xs] (= (sum xs) needle)) xss)))
    any))

(defn solve [length numbers is-solution? make-solution]
  (setv
    numbers (iter numbers)
    last-numbers (deque (islice numbers length) :maxlen length))
  (for [n numbers]
    (if (is-solution? last-numbers n) (return (make-solution last-numbers n)))
    (.append last-numbers n)))

(defn solve-part-1 [length numbers]
  (solve
    length
    numbers
    (fn [last-numbers n] (->> n (is-sum-of? 2 last-numbers) not))
    (fn [_ n] n)))

(defn solve-part-2 [numbers needle]
  (for [length (->> numbers len (range 2))]
    (setv
      solution
      (solve
        length
        numbers
        (fn [last-numbers _] (= needle (sum last-numbers)))
        (fn [last-numbers _] (+ (min last-numbers) (max last-numbers)))))
    (if solution (return solution))))

(defmain []
  (setv
    numbers (with [lines (open "input")] (->> lines (map int) list))
    part1 (solve-part-1 25 numbers))
  (print part1)
  (-> numbers (solve-part-2 part1) print))
