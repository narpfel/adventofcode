(import collections [namedtuple UserList])
(import collections.abc [Iterable])
(import enum [IntEnum])
(import inspect [signature])
(import logging)
(import logging [debug])

(require hyrule [-> ->> assoc lif])

(logging.basicConfig
  :style "{"
  :level logging.DEBUG
  :format "{threadName} {levelname}:{name}:{message}")

; Remove `debug` calls at compile time for performance reasons: Even no-op function
; calls take a significant amount of time if they are in a hot loop. PyPy helps a bit,
; but even on PyPy the code is > 10 % slower without this hack.
(defmacro debug [#* _])


(defn iterable? [value]
  (isinstance value Iterable))


(defclass Mode [IntEnum]
  (setv
    POSITION 0
    IMMEDIATE 1
    RELATIVE 2))


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


(defclass InfiniteList [UserList]

  (defn _fill [self length]
    (.extend self (* [0] (- (+ length 1) (len self)))))

  (defn __getitem__ [self index]
    (try
      (.__getitem__ (super) index)
      (except [IndexError]
              (do
                (._fill self index)
                (return 0)))))

  (defn __setitem__ [self index value]
    (try
      (.__setitem__ (super) index value)
      (except [IndexError]
              (do
                (._fill self index)
                (assoc self index value))))))


(defclass Cell []
  (defn __init__ [self computer address mode]
    (setv self.computer computer
          self.address address
          self.mode mode)
    (assert (isinstance address int)))

  (defn [property] value [self]
    ((. self computer lookup)
      (cond
        (= self.mode Mode.POSITION)
         ((. self computer lookup) self.address)
        (= self.mode Mode.IMMEDIATE)
         self.address
        (= self.mode Mode.RELATIVE)
         (do
           (setv val ((. self computer lookup) self.address))
           (debug
             "relative mode read: relative base %s offset %s"
             self.computer.relative-base val)
           (setv x (+ ((. self computer lookup) self.address) self.computer.relative-base))
           (debug "relative mode read: read from address %s" x)
           x)
        True
         (raise (ValueError f"unknown read mode {mode !r}")))))

  (defn store [self value]
    (cond
      (= self.mode Mode.POSITION)
       (do
         (setv address ((. self computer lookup) self.address))
         (debug "write value %s to address %s in %s" value address self.mode)
         (assoc self.computer.memory address value))
      (= self.mode Mode.IMMEDIATE)
       (raise Exception)
      (= self.mode Mode.RELATIVE)
       (do
         (setv address (+ self.computer.relative-base ((. self computer lookup) self.address)))
         (debug "write value %s to address %s in %s" value address self.mode)
         (assoc
           self.computer.memory
           (+ self.computer.relative-base ((. self computer lookup) self.address))
           value))
      True
       (raise Exception))))


(defclass IntcodeComputer []

  (setv OUTPUTS-TYPE list)

  (defn __init__ [self memory * [input 0] [outputs None]]
    (setv self.inputs (if (iterable? input) (iter input)
                          (iter [input]))
          self.memory (InfiniteList memory)
          self.instruction-pointer 0
          self.outputs (lif outputs outputs (self.OUTPUTS-TYPE))
          self.relative-base 0))

  (defn [classmethod] from-string [cls string #* args #** kwargs]
    (cls (parse string) #* args #** kwargs))

  (defn [classmethod] from-file [cls path #* args #** kwargs]
    (with [f (open path)]
      (.from-string cls (.read f) #* args #** kwargs)))

  (defn lookup [self address]
    (get self.memory address))

  (defn read [self mode]
    (setv result (Cell self self.instruction-pointer mode))
    (debug
      "read %s (%s) in %s → %s"
      self.instruction-pointer (.lookup self self.instruction-pointer) (Mode mode) result.value)
    (+= self.instruction-pointer 1)
    (return result))

  (defn write [self address value]
    (.store address value))

  (defn run-program [self]
    (while True
           (debug "\n")
           (debug "run-program: %s" self.instruction-pointer)
           (setv opcode (. (.read self Mode.IMMEDIATE) value))
           (setv command (% opcode 100))
           (when (= command 99) (break))
           (setv operation (get self.OPERATIONS command))
           (debug "instruction: %s (%s): %s" command opcode operation.function.__name__)
           (debug "state: ip: %s" self.instruction-pointer)
           (debug "state: rb: %s" self.relative-base)
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

  (defn add [self a b addr]
    (debug "add %s to %s" a.value b.value)
    (.write self addr (+ a.value b.value)))

  (defn multiply [self a b addr]
    (debug "multiply %s with %s" a.value b.value)
    (.write self addr (* a.value b.value)))

  (defn read-input [self addr]
    (setv input (next self.inputs))
    (debug "read-input %s with parameter-mode %s" input addr.mode)
    (.write self addr input))

  (defn write-output [self value]
    (debug "output value %s" value.value)
    (setv self.output value.value))

  (defn jump-if-true [self value target]
    (debug
      "jump-if-true from %s on value %s to %s"
      self.instruction-pointer value.value target.value)
    (when value.value (setv self.instruction-pointer target.value)))

  (defn jump-if-false [self value target]
    (debug
      "jump-if-false from %s on value %s to %s"
      self.instruction-pointer value.value target.value)
    (when (not value.value) (setv self.instruction-pointer target.value)))

  (defn less-than [self lhs rhs addr]
    (debug "less-than %s < %s => %s" lhs.value rhs.value (< lhs.value rhs.value))
    (.write self addr (int (< lhs.value rhs.value))))

  (defn equals [self lhs rhs addr]
    (debug "equals: %s == %s => %s" lhs.value rhs.value (= lhs.value rhs.value))
    (.write self addr (int (= lhs.value rhs.value))))

  (defn adjust-relative-base [self offset]
    (debug
      "adjust-relative-base from %s by %s to %s"
      self.relative-base offset.value (+ self.relative-base offset.value))
    (+= self.relative-base offset.value))

  (setv OPERATION-FUNCTIONS
        [add multiply read-input write-output jump-if-true jump-if-false less-than equals
         adjust-relative-base])

  (setv OPERATIONS
        (dfor
          [opcode function] (enumerate OPERATION-FUNCTIONS 1)
          opcode (with-parameter-count function))))
