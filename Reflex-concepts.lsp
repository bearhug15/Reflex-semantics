(defun concept () ())
(defun concept-by-union () ()) 
(defun concept-by-value () ())
(deftype int () t) 
(deftype nat () t)
(deftype tbool () t) 
(defun aget () ())
(defun aset () ())
(defun transformation () ())

(concept-by-union boolean-constant true false)
(concept-by-value integer-constant int)
(concept-by-value natural-constant nat)
(concept-by-value float-constant float)

(concept days :constructor d :arguments (value nat))
(concept hours :constructor h :arguments (value nat))
(concept minutes :constructor m :arguments (value nat))
(concept seconds :constructor s :arguments (value nat))
(concept milliseconds :constructor ms :arguments (value nat))
(concept time-constant :constructor rtime :arguments (d :opt days) (h :opt hours) (m :opt minutes) (s :opt seconds) (ms :opt milliseconds))
;(rtime (m 2))

(concept-by-union non-time-constant integer-constant natural-constant 
  float-constant boolean-constant)

(concept-by-union constant non-time-constant time-constant)

(concept-by-value name symbol)
(concept-by-value variable-name name)
(concept-by-value process-name name)
(concept-by-value state-name name)
(concept-by-value program-name name)
(concept-by-value structure-name name)
(concept-by-value field-name name)
(concept-by-value enum-name name)
(concept-by-value port-name name)


(concept integer-type int)
(concept natural-type nat)
;(concept-by-value integer-type int)
;(concept-by-value natural-type nat)
(concept-by-value float-type float)
(concept-by-value boolean-type true false)
(concept-by-value time-type rtime)
(concept-by-union simple-type integer-type natural-type float-type boolean-type time-type)

(concept array-type :constructor arrayt :arguments (element-type rtype) (size integer-expression))

(concept structure-field :constructor field :arguments (name variable-name)(element-type rtype))
(concept-by-value structure-type structure-name)

(concept-by-value enum-type enum-name)

(concept-by-union rtype simple-type array-type structure-type enum-type)

;Expressions
(concept |+| :constructor |+| :arguments (first expression) (second expression))
(concept |-| :constructor |-| :arguments (first expression) (second expression))
(concept |*| :constructor |*| :arguments (first expression) (second expression))
(concept |/| :constructor |/| :arguments (first expression) (second expression))
(concept |%| :constructor |%| :arguments (first expression) (second expression))
(concept |>>| :constructor |>>| :arguments (first expression) (second expression))
(concept |<<| :constructor |<<| :arguments (first expression) (second expression))

(concept |==| :constructor |==| :arguments (first expression) (second expression))
(concept |!=| :constructor |!=| :arguments (first expression) (second expression))
(concept |>=| :constructor |>=| :arguments (first expression) (second expression))
(concept |<=| :constructor |<=| :arguments (first expression) (second expression))
(concept |>| :constructor |>| :arguments (first expression) (second expression))
(concept |<| :constructor |<| :arguments (first expression) (second expression))

(concept |&&| :constructor |&&| :arguments (first expression) (second expression))
(concept |\|\|| :constructor |\|\|| :arguments (first expression) (second expression))

(concept |&| :constructor |&| :arguments (first expression) (second expression))
(concept |\|| :constructor |\|| :arguments (first expression) (second expression))
(concept |^| :constructor |^| :arguments (first expression) (second expression))
(concept cast :constructor cast  :arguments (rtype simple-type) 
  (expression expression))

(concept |!.| :constructor |!.| :arguments (operand expression))
(concept |-.| :constructor |-.| :arguments (first expression))
(concept |~.| :constructor |~.| :arguments (first expression))


(concept array-element-access :constructor |[.]| :arguments 
  	(name variable-name) (index expression))
(concept struct-simple-element-access :constructor |.| :agruments (name variable-name)
  (fields :flatten (list field-name)))
(concept struct-array-element-access :constructor |.[.]| :agruments (name variable-name)
  (fields :flatten (list field-name)) (index expression))
(concept enum-element-access :constructor |::| :arguments 
    (name enum-name) (field field-name))
(concept-by-union element-access variable-name array-element-access struct-simple-element-access struct-array-element-access enum-element-access)

(concept |=| :constructor |=| :arguments (first element-access) (second expression))
(concept |+=| :constructor |+=| :arguments (first element-access) (second expression))
(concept |-=| :constructor |-=| :arguments (first element-access) (second expression))
(concept |*=| :constructor |*=| :arguments (first element-access) (second expression))
(concept |\=| :constructor |\=| :arguments (first element-access) (second expression))

(concept |++.| :constructor |++.| :arguments (first element-access))
(concept |.++| :constructor |.++| :arguments (first element-access))
(concept |--.| :constructor |--.| :arguments (first element-access))
(concept |.--| :constructor |.--| :arguments (first element-access))

(concept-by-union activity active inactive rstop nonstop rerror nonerror)
(concept process-state-checking :constructor process-in-state :arguments (process process-name) (activity activity))


(concept-by-union expression |+| |-| |*| |/| |>>| |<<| |==| |!=| |>=| |<=| |>| |<| |&&| |\|\|| |^| |!.| |-.| |~.| cast element-access |=| |+=| |-=| |*=| |\=| process-state-checking constant)

;Statements

(concept reset-timer :constructor reset)
(concept set-state :constructor set-state :arguments (state state-name))

(concept restart-process :constructor restartp)
(concept start-process :constructor start-process :arguments (process process))

(concept stop-current-process :constructor stop-cur)
(concept stop-process :constructor stop-process :arguments (process process))

(concept error-current-process :constructor error-cur)
(concept error-process :constructor error-process :arguments (process process))

(concept-by-union process-oriented-statement reset-timer set-state restart-process start-process stop-current-process stop-process error-current-process current-process timeout-statement)


(concept if-then-statement :constructor if 
:arguments (condition expression) (then statement))
(concept if-then-else-statement :constructor if-else 
:arguments (condition expression) (then statement) (else statement))
(concept-by-union if-statement if-then-statement if-then-else-statement)

(concept switch-statement :constructor switch :arguments (controlling-expression expression) (cases :flatten (list case-statement)) (default :opt default-statement))
(concept default-statement :constructor default :arguments (statements :flatten (list statement)))
(concept-by-union integer-constant-expression expression)
(concept case-statement :constructor case :arguments  (label integer-constant-expression) (statements :flatten (list statement)) :tags break)

(concept statement-block :constructor block (statements :flatten (list statement)))

(concept expression-statement :constructor expr :arguments (expression expression))

(concept-by-union statement expression-statement if-statement switch-statement statement-block 
process-oriented-statement barrier-statement)
(concept timeout-statement :constructor timeout :arguments (controlling-expression expression) (statements :flatten (list statement)))



(concept wait :constructor wait (condition boolean-expression) )
(concept slice :constructor slice )
(concept transition :constructor transition (condition expression))
(concept-by-union barrier-statement wait slice transition)
(concept state-declaration :constructor state :arguments (name state-name) (body :alab :flatten (list statement)))

(state имя (:body s1  s2) (:barriers b1 b2 b3) timeout-statement)

(concept constant-declaration :constructor const :arguments (rtype simple-type) (name variable-name) (value expression))

(concept-by-value simple-init expression)
(concept simple-variable-declaration :constructor var :arguments (rtype simple-type) (name variable-name) (init :opt simple-init) :tag shared)

(concept-by-value array-init (list expression))
(concept array-variable-declaration :constructor arvar :arguments (rtype array-type) (name variable-name) (size :opt int) (init :opt array-init) :tag shared)

(concept-by-union variable-declaration simple-variable-declaration array-variable-declaration)
(concept imported-variable-declaration :constructor impvar (name variable-name) (source-proc process-name) (source-var process-name))

(concept physical-variable-declaration :constructor physvar :arguments (rtype simple-type) (name variable-name) (port port-name) (index int))

(concept structure-field-declaration :constructor sf-decl :arguments (name field-name) (rtype rtype))
(concept structure-declaration :constructor struct-decl :arguments (name variable-name) (fields :flatten (list structure-field-declaration)))

(concept-by-union process-variable-declaration simple-variable-declaration array-variable-declaration physical-variable-declaration imported-variable-declaration)

(concept process-declaration :constructor process :arguments 
    (name process-name) 
    (variables :flatten (list process-variable-declaration))
    (states :flatten (list state-declaration)))


(concept struct-init (map fieled-name reflex-init))
(concept structure-variable-declaration :constructor struct-var-decl :arguments (name variable-name) (rtype structure-name) (init :opt struct-init))
(concept-by-union reflex-init simple-init array-init struct-init enum-element-access)

(concept enum-fields :constructor efield :arguments (name variable-name) (value :opt int))
(concept enum-declaration :constructor enum-declaration :arguments (fields :flatten (list enum-fields)))

(concept enum-variable-declaration :constructor enum-variable-declaration :arguments (name variable-name) (rtype enum-name) (init :opt enum-element-access))

(concept-by-union port-type input output)
(concept port-declaration :constructor port :arguments (port-type port-type) (name port-name) (addr1 int) (addr2 int) (size int))

(concept-by-union program-item-declaration
  port-declaration
  constant-declaration 
  simple-variable-declaration 
  array-variable-declaration 
  structure-declaration 
  structure-variable-declaration 
  enum-declaration
  enum-variable-declaration)

(concept-by-union clock natural-constant time-constant)
(concept program-declaration :constructor program 
    :arguments (name program-name) 
    (clock clock)
    (declarations :flattent (list program-item-declaration))
    (processes :flatten (list process))
)


(concept-by-union reflex-value constant array-value structure-value)
(concept-by-value structure-value (map field-name reflex-value))
(concept-by-value array-value (list reflex-value))