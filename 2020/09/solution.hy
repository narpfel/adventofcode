#!/usr/bin/env hy

(import [collections [deque]])
(import [itertools [combinations islice]])

(defn is-sum-of? [k numbers needle]
  (->
    numbers
    (combinations :r k)
    ((fn [xss] (map (fn [xs] (= (sum xs) needle)) xss)))
    any))

(defn solve [length numbers]
  (setv
    numbers (iter numbers)
    last-numbers (deque (islice numbers length) :maxlen length))
  (for [n numbers]
    (if-not (is-sum-of? 2 last-numbers n) (return n))
    (.append last-numbers n)))

(defmain [&rest _]
  (with [lines (open "input")]
    (->> lines (map int) (solve 25) (print))))
