(import [collections [namedtuple]])
(import [enum [IntEnum]])
(import [inspect [signature]])
(import logging)
(import [logging [debug]])
(import [os [environ]])


(logging.basicConfig :style "{" :level logging.DEBUG)

; Remove `debug` calls at compile time for performance reasons: Even no-op function
; calls take a significant amount of time if they are in a hot loop. PyPy helps a bit,
; but even on PyPy the code is > 10 % slower without this hack.
(defmacro debug [&rest _])


(defclass Mode [IntEnum]
  (setv
    POSITION 0
    IMMEDIATE 1))


(setv Operation (namedtuple "Operation" "function, parameter_count"))


(defn read-puzzle-input [filename]
  (with [f (open filename)]
    (->>
      (.read f)
      (parse))))


(defn parse [string]
  (->
    string
    (.strip)
    (.split ",")
    ((fn [xs] (map int xs)))
    (list)))


(defn with-parameter-count [f]
  (setv
    parameter-count
    (->
      f
      (signature)
      (. parameters)
      (len)
      (+ (- 1))))
  (Operation f parameter-count))


(defclass IntcodeComputer []

  (defn --init-- [self memory &optional [input 0]]
    (setv self.memory (list memory))
    (setv self.instruction-pointer 0)
    (setv self.input input)
    (setv self.output 0))

  (with-decorator classmethod
    (defn from-string [cls string &rest args &kwargs kwargs]
      (cls (parse string) #* args #** kwargs)))

  (with-decorator classmethod
    (defn from-file [cls path &rest args &kwargs kwargs]
      (with [f (open path)]
        (.from-string cls (.read f) #* args #** kwargs))))

  (defn lookup [self address]
    (get self.memory address))

  (defn read [self mode]
    (setv result
          (.lookup self (cond
                          [(= mode Mode.POSITION)
                           (.lookup self self.instruction-pointer)]
                          [(= mode Mode.IMMEDIATE)
                           self.instruction-pointer]
                          [True
                           (raise (ValueError f"unknown read mode {mode !r}"))])))
    (debug "read %s (%s) → %s" self.instruction-pointer (Mode mode) result)
    (+= self.instruction-pointer 1)
    (return result))

  (defn write [self value]
    (setv addr (.read self Mode.IMMEDIATE))
    (debug "write value %s to address %s" value addr)
    (assoc self.memory addr value))

  (defn run-program [self]
    (while True
           (debug "run-program: %s\t%s" self.instruction-pointer self.memory)
           (setv opcode (.read self Mode.IMMEDIATE))
           (setv command (% opcode 100))
           (if (= command 99) (break))
           (if (!= self.output 0) (raise Exception))
           (setv operation (get self.OPERATIONS command))
           (setv parameter-modes
                 (if
                   (= operation.parameter-count 0) []
                   (reversed
                     (lfor
                       x (.zfill (str (// opcode 100)) operation.parameter-count)
                       (int x)))))
           (operation.function self #* (.read-operands self parameter-modes))))

  (defn read-operands [self parameter-modes]
    (gfor
      mode parameter-modes
      (.read self mode)))

  (defn add [self a b]
    (.write self (+ a b)))

  (defn multiply [self a b]
    (.write self (* a b)))

  (defn read-input [self]
    (debug "read-input")
    (.write self self.input))

  (defn write-output [self value]
    (debug "output value %s" value)
    (setv self.output value))

  (defn jump-if-true [self value target]
    (debug "jump-if-true from %s on value %s to %s" self.instruction-pointer value target)
    (if value (setv self.instruction-pointer target)))

  (defn jump-if-false [self value target]
    (debug "jump-if-false from %s on value %s to %s" self.instruction-pointer value target)
    (if (not value) (setv self.instruction-pointer target)))

  (defn less-than [self lhs rhs]
    (.write self (int (< lhs rhs))))

  (defn equals [self lhs rhs]
    (.write self (int (= lhs rhs))))



  (setv OPERATION-FUNCTIONS
        [add multiply read-input write-output jump-if-true jump-if-false less-than equals])

  (setv OPERATIONS
        (dfor
          [opcode function] (enumerate OPERATION-FUNCTIONS 1)
          [opcode (with-parameter-count function)])))
