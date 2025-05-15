(defun concept () ())
(defun concept-by-union () ()) 
(defun concept-by-value () ())
(deftype int () t) 
(deftype nat () t)
(deftype tbool () t) 
(defun aget () ())
(defun aset () ())
(defun transformation () ())

;возвращает список ключей в мапе 
(defun get-keys (map) ())


(concept context :constructor context :attributes
;There used raw variable names
;variable exists whether in is-process-variable or is-global-variable
;if variable is in shared-in-process then it should be in is-process-variable
;is-input/is-output is exclusive categories 

(is-global-variable (map variable-name tbool))
(is-process-variable (map process-name (map variable-name tbool)))
(is-global-constant (map variable-name tbool))
(is-process-constant (map process-name (map variable-name tbool)))
(shared-in-process (map process-name (map variable-name process-name)))
(shared-variable (map process-name (map variable-name (map process-name variable-name))))

;for global variables process-name is '_
(input-variable-port (map process-name (map variable-name port-name)))
(input-variable (map process-name (map variable-name (map port-name int))))
(output-variable-port (map process-name(map variable-name port-name)))
(output-variable (map process-name (map variable-name (map port-name int))))

(input-ports (list port-name))
(output-ports (list port-name))

;There used mapped variable names
;variable-type includes constant types 
(variable-type (map variable-name rtype))
(is-variable (map variable-name tbool))
(is-declaration (map variable-name tbool))
(is-simple-variable (map variable-name tbool))
(is-array-variable (map variable-name tbool))
(is-struct-variable (map variable-name tbool))
(is-enum-variable (map variable-name tbool))
(is-constant (map variable-name tbool))

(input-variables (list varibale-name))
(constant-value (map variable-name constant))
(array-variable-size (map variable-name int))
(variable-init (map variable-name reflex-init))
(processes-states-names (map process-name (list state-name)))

(struct-fields (map structure-name (map variable-name rtype)))
(enum-value (map enum-name (map field-name int)))

(clock int)
)

(concept agent :constructor agent :attributes
(variable-value (map variable-name reflex-value))
(process-state (map process-name state-name))
(process-substate (map process-name int))
(process-time (map process-name natural-constant))
(current-process process-name)
(current-state state-name)
(current-substate int)

(processes-to-start (list process-name ))

)

(defun map-name (a c name is-var)
    (if is-var
        (if (aget a 'current-process)
            (let ((cur-proc (aget a 'current-process)))
                (if (aget c 'is-process-variable cur-proc name)
                    (if (aget c 'shared-in-process cur-proc name)
                        (mashup-symbol 'pv_ (aget c 'shared-in-process cur-proc) '_  (aget c 'shared cur-proc name (aget c 'shared-in-process cur-proc)))
                        (if (aget c 'input-variable-port name)
                            (mashup-symbol (aget c 'input-variable-port cur-proc name) '_ (aget c 'input-variable cur-proc name (aget c 'input-variable-port cur-proc name))))
                            (if (aget c 'output-variable-port name) 
                                (mashup-symbol (aget c 'output-variable-port  cur-proc name) '_ (aget c 'output-variable-port cur-proc name (aget c 'output-variable-port  cur-proc name)))
                                (mashup-symbol 'pv_ (aget a 'current-process) '_ name))
                    )
                    (if (aget c 'is-global-variable name)
                        (if (aget c 'input-variable-port '_ name)
                            (mashup-symbol (aget c 'input-variable-port name) '_ (aget c 'input-variable '_ name (aget c 'input-variable-port name)))
                            (if (aget c 'output-variable-port '_ name) 
                                (mashup-symbol (aget c 'output-variable-port '_ name) '_ (aget c 'output-variable-port name (aget c 'output-variable-port '_ name)))
                                (mashup-symbol 'gv_ name)))
                        nil
                        #|(progn (aset a 'stack nil)
                            (error "Unkown variable"))|#
                    )
                )
                (if (aget c 'is-global-variable name)
                    (if (aget c 'input-variable-port '_ name)
                        (mashup-symbol (aget c 'input-variable-port name) '_ (aget c 'input-variable '_ name (aget c 'input-variable-port name)))
                        (if (aget c 'output-variable-port '_ name) 
                            (mashup-symbol (aget c 'output-variable-port '_ name) '_ (aget c 'output-variable-port name (aget c 'output-variable-port '_ name)))
                            (mashup-symbol 'gv_ name)))
                    nil
                    #|(progn (aset a 'stack nil)
                        (error "Unkown variable"))|#
                )
            )
        )
        (if (aget a 'current-process)
            (let ((cur-proc (aget a 'current-process)))
                (if (aget 'is-process-constant name)
                    (mashup-symbol 'pc_ name)
                    (if (aget c 'is-global-constant name)
                        (mashup-symbol 'gc_ name)
                        nil
                        #|(progn (aset a 'stack nil)
                            (error "Unkown constant"))|#
                    )))
            (if (aget c 'is-global-constant name)
                (mashup-symbol 'gc_ name)
                nil
                #|(progn (aset a 'stack nil)
                            (error "Unkown constant"))|#
            ))   
    )
)

(defun rtype-default-val (t &rest len)
    (if (> (length len) 0)
        (case (get-concep t)
            ('natural-type (make-list (car len) :initial-element 0))
            ('integer-type (make-list (car len) :initial-element 0))
            ('float-type (make-list (car len) :initial-element 0.0))
            ('boolean-type (make-list (car len) :initial-element 'false))
            ('time-type (make-list (car len) :initial-element (rtime))))
        (case (get-concep t)
            ('natural-type 0)
            ('integer-type 0)
            ('float-type 0.0)
            ('boolean-type 'false)
            ('time-type (rtime)))))

;Transformations


(transformation opsem :concept time-constant :stages
    nil :do 
    (let ((days (aget i 'd 'value))
                    (hours (aget i 'h 'value))
                    (minutes (aget i 'm 'value))
                    (seconds (aget i 's 'value))
                    (milis (aget i 'ms 'value)))
                (+ (if (milis) milis 0)
                    (* (+ (if (seconds) secons 0)
                        (* (+ (if (minutes) minutes 0)
                            (* (+ (if (hours) hours 0)
                                (* (if (days) days 0) 24)) 60)) 60)) 1000)))
)

(transformation opsem :concept non-time-constant :stages 
    nil :do i)

(transformation opsem :concept variable-name :stages 
    nil :do 
    (let ((vname (map-name a c i t))
            (cname (map-name a c i nil)))
        (if (or (aget c 'is-simple-variable vname) (aget c 'is-enum-variable vname))
            (aget a 'variable-value vname)
            (if (aget c 'is-constant cname)
                (aget c 'constant-value cname)
                (progn (aset a 'stack nil)
                    (error "Not a simple, enum or constant variable"))))))

(transformation opsem :concept array-element-access :stages 
    nil :do (to-stage 'val)
        (if (aget c 'is-array-variable (map-name a c (aget i 'name) t))
            (opsem (aget i 'index) a c)
            (progn (aset a 'stack nil)
                (error "Array not exists")))
    val :do 
        (let ((loc-var (aget a 'value))
                (variable-name (map-name a c (aget i 'name) t)))
            (if (and (>= loc-var 0) 
                    (< loc-var (aget c 'array-variable-size variable-name)))
                (aget a 'variable-value (map-name a c (aget i 'name) t) loc-var)
                (progn (aset a 'stack nil)
                    (error "Index out of bounds"))
            )
        )
)



(transformation opsem :concept struct-simple-element-access :stages 
    nil :do (aget a 'variable-value (cons (map-name a c (aget i 'name) t) (aget i 'fields)))
    )

(transformation opsem :concept struct-array-element-access :stages 
    nil :do (to-stage 'val) (opsem (aget i 'index) a c)
    val :do (aget a 'variable-value (cons (map-name a c (aget i 'name) t) (aget i 'fields)) (aget a 'value))
)    

(transformation opsem :concept enum-element-access :stages 
    nil :do (aget c 'enum-value (aget i 'name) (aget i 'field)))
;Transformations: expressions
(transformation opsem :concept |+| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (opsem (aget i 'second) a c))
    (second left) :do (+ left (aget a 'value))
(transformation opsem :concept |-| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (opsem (aget i 'second) a c))
    (second left) :do (- left (aget a 'value))
(transformation opsem :concept |*| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (opsem (aget i 'second) a c))
    (second left) :do (* left (aget a 'value))
(transformation opsem :concept |/| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (opsem (aget i 'second) a c))
    (second left) :do (/ left (aget a 'value))
(transformation opsem :concept |%| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (opsem (aget i 'second) a c))
    (second left) :do (mod left (aget a 'value))

(transformation opsem :concept |<<| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (opsem (aget i 'second) a c))
    (second left) :do (lsh left (aget a 'value))
(transformation opsem :concept |>>| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (opsem (aget i 'second) a c))
    (second left) :do (lsh left (* -1 (aget a 'value)))

(transformation opsem :concept |==| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (opsem (aget i 'second) a c))
    (second left) :do (= left (aget a 'value))
(transformation opsem :concept |!=| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (opsem (aget i 'second) a c))
    (second left) :do (/= left (aget a 'value))
(transformation opsem :concept |>=| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (opsem (aget i 'second) a c))
    (second left) :do (>= left (aget a 'value))
(transformation opsem :concept |<=| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (opsem (aget i 'second) a c))
    (second left) :do (<= left (aget a 'value))
(transformation opsem :concept |>| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (opsem (aget i 'second) a c))
    (second left) :do (> left (aget a 'value))
(transformation opsem :concept |<| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (opsem (aget i 'second) a c))
    (second left) :do (< left (aget a 'value))
(transformation opsem :concept |&&| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do 
        (let ((subres (aget a 'value)))
            (if (subres)
                (progn (to-stage 'second (aget a 'value))
                    (opsem (aget i 'second) a c)))))
    (second left) :do (and left (aget a 'value))
(transformation opsem :concept |\|\|| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do 
        (let ((subres (aget a 'value))) 
            (if (not subres) 
                (progn (to-stage 'second subres) 
                    (opsem (aget i 'second) a c)))))
    (second left) :do (or left (aget a 'value))

(transformation opsem :concept |&| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (opsem (aget i 'second) a c))
    (second left) :do (logand left (aget a 'value))
(transformation opsem :concept |\|| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (opsem (aget i 'second) a c))
    (second left) :do (logior left (aget a 'value))
(transformation opsem :concept |^| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (opsem (aget i 'second) a c))
    (second left) :do (logxor left (aget a 'value))


(concept cast :constructor cast  :arguments (rtype simple-type) 
  (expression expression))
(transformation opsem :concept cast :stages
    nil :do (to-stage 'cast) (opsem (aget i 'expression) a c)
    cast :do 
        (let ((sub (aget i 'value)))
            (case (get-concept (aget i 'rtype))
                ('integer-type (floor (aget i 'value)))
                ('natural-type 
                    (if (>= sub 0)
                        (floor sub)
                        (+ (floor sub) (aget i 'rtype 'max-value))))
                ('boolean-type 
                    (if (= sub 0)
                        'false
                        'true))
                ('float-type (+ sub 0.0)))
        )
)


(transformation opsem :concept |!.| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (not (aget a 'value)))
(transformation opsem :concept |-.| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (- 0 (aget a 'value)))
(transformation opsem :concept |~.| :stages 
    nil :do (to-stage 'first) (opsem (aget i 'first) a c)
    first :do (lognot (aget a 'value)))


(transformation opsem :concept |=| :stages 
    nil :do 
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) struct-array-element-access))
                (progn (to-stage 'val)
                    (opsem (aget i 'second) a c))
                (progn (to-stage 'nonarray)
                    (opsem (aget i 'second) a c))))
    nonarray :do 
        (let ((res (aget a 'value))
                (variable-name (map-name a c (aget i 'first 'name) t)))
            (case (get-concept (aget i 'first))
                ('variable-name 
                    (progn (aset a 'variable-value variable-name res)
                        res))
                ('struct-simple-element-access
                    (progn (aset a 'variable-value (cons variable-name (aget i 'first 'fields)) res)
                        res)))
        )
    val :do (to-stage 'arr (aget a 'value)) (opsem (aget i 'index) a c)
    (arr res) :do 
        (let ((index (aget a 'value))
                (variable-name (map-name a c (aget i 'first 'name) t)))
            (case (get-concept (aget i 'first))
                ('array-element-access 
                    (progn (aset a 'variable-value variable-name index res)
                        res))
                (progn 
                    (aset a 'variable-value (cons variable-name (aget i 'first 'fields)) index res)
                    res))
        )
)  

(transformation opsem :concept |+=| :stages 
    nil :do 
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) struct-array-element-access))
                (progn (to-stage 'val)
                    (opsem (aget i 'second) a c))
                (progn (to-stage 'nonarray)
                    (opsem (aget i 'second) a c))))
    nonarray :do 
        (let ((res (aget a 'value))
                (variable-name (map-name a c (aget i 'first 'name) t)))
            (case (get-concept (aget i 'first))
                ('variable-name 
                    (let ((new-res (+ res (aget a 'variable-value variable-name))))
                        (aset a 'variable-value variable-name new-res)
                        new-res))
                ('struct-simple-element-access 
                    (let ((variable-name (cons variable-name (aget i 'first 'fields)))
                            (new-res (+ res (aget a 'variable-value variable-name)))) 
                        (aset a 'variable-value variable-name new-res)
                        new-res)))
        )
    val :do (to-stage 'arr (aget a 'value)) (opsem (aget i 'index) a c)
    (arr res) :do 
        (let ((index (aget a 'value))
                (variable-name (map-name a c (aget i 'first) t)))
            (case (get-concept (aget i 'first))
                ('array-element-access 
                    (let ((new-res (+ res (aget a 'variable-value variable-name index)))) 
                        (aset a 'variable-value variable-name index new-res)
                        new-res))
                ('struct-array-element-access
                    (let ((variable-name (cons variable-name (aget i 'first 'fields)))
                            (new-res (+ res (aget a 'variable-value variable-name index)))) 
                        (aset a 'variable-value variable-name index new-res)
                        new-res)))
        )
) 
(transformation opsem :concept |-=| :stages 
    nil :do
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) struct-array-element-access))
                (progn (to-stage 'val)
                    (opsem (aget i 'second) a c))
                (progn (to-stage 'nonarray)
                    (opsem (aget i 'second) a c))))
    nonarray :do 
        (let ((res (aget a 'value))
                (variable-name (map-name a c (aget i 'first 'name) t)))
            (case (get-concept (aget i 'first))
                ('variable-name 
                    (let ((new-res (- (aget a 'variable-value variable-name) res )))
                        (aset a 'variable-value variable-name new-res)
                        new-res))
                ('struct-simple-element-access 
                    (let ((variable-name (cons variable-name (aget i 'first 'fields)))
                            (new-res (- (aget a 'variable-value variable-name) res ))) 
                        (aset a 'variable-value variable-name new-res)
                        new-res)))
        )
    val :do (to-stage 'arr (aget a 'value)) (opsem (aget i 'index) a c)
    (arr res) :do 
        (let ((index (aget a 'value))
                (variable-name (map-name a c (aget i 'first) t)))
            (case (get-concept (aget i 'first))
                ('array-element-access 
                    (let ((new-res (- (aget a 'variable-value variable-name index) res))) 
                        (aset a 'variable-value variable-name index new-res)
                        new-res))
                ('struct-array-element-access
                    (let ((variable-name (cons variable-name (aget i 'first 'fields)))
                            (new-res (- (aget a 'variable-value variable-name index) res))) 
                        (aset a 'variable-value variable-name index new-res)
                        new-res)))
        )
)

(transformation opsem :concept |*=| :stages 
    nil :do
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) struct-array-element-access))
                (progn (to-stage 'val)
                    (opsem (aget i 'second) a c))
                (progn (to-stage 'nonarray)
                    (opsem (aget i 'second) a c))))
    nonarray :do 
        (let ((res (aget a 'value))
                (variable-name (map-name a c (aget i 'first 'name) t)))
            (case (get-concept (aget i 'first))
                ('variable-name 
                    (let ((new-res (* (aget a 'variable-value variable-name) res)))
                        (aset a 'variable-value variable-name new-res)
                        new-res))
                ('struct-simple-element-access 
                    (let ((variable-name (cons variable-name (aget i 'first 'fields)))
                            (new-res (* (aget a 'variable-value variable-name) res))) 
                        (aset a 'variable-value variable-name new-res)
                        new-res)))
        )
    val :do (to-stage 'arr (aget a 'value)) (opsem (aget i 'index) a c)
    (arr res) :do 
        (let ((index (aget a 'value))
                (variable-name (map-name a c (aget i 'first) t)))
            (case (get-concept (aget i 'first))
                ('array-element-access 
                    (let ((new-res (* (aget a 'variable-value variable-name index) res))) 
                        (aset a 'variable-value variable-name index new-res)
                        new-res))
                ('struct-array-element-access
                    (let ((variable-name (cons variable-name (aget i 'first 'fields)))
                            (new-res (* (aget a 'variable-value variable-name index) res))) 
                        (aset a 'variable-value variable-name index new-res)
                        new-res)))
        )
)

(transformation opsem :concept |/=| :stages 
    nil :do
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) structure-array-element-access))
                (progn (to-stage 'val)
                    (opsem (aget i 'second) a c))
                (progn (to-stage 'nonarray)
                    (opsem (aget i 'second) a c))))
    nonarray :do 
        (let ((res (aget a 'value))
                (variable-name (map-name a c (aget i 'first 'name) t)))
            (case (get-concept (aget i 'first))
                ('variable-name 
                    (let ((new-res (/ (aget a 'variable-value variable-name) res)))
                        (aset a 'variable-value variable-name new-res)
                        new-res))
                ('struct-simple-element-access 
                    (let ((variable-name (cons variable-name (aget i 'first 'fields)))
                            (new-res (/ (aget a 'variable-value variable-name) res))) 
                        (aset a 'variable-value variable-name new-res)
                        new-res)))
        )
    val :do (to-stage 'arr (aget a 'value)) (opsem (aget i 'index) a c)
    (arr res) :do 
        (let ((index (aget a 'value))
                (variable-name (map-name a c (aget i 'first) t)))
            (case (get-concept (aget i 'first))
                ('array-element-access 
                    (let ((new-res (/ (aget a 'variable-value variable-name index) res))) 
                        (aset a 'variable-value variable-name index new-res)
                        new-res))
                ('struct-array-element-access
                    (let ((variable-name (cons variable-name (aget i 'first 'fields)))
                            (new-res (/ (aget a 'variable-value variable-name index) res))) 
                        (aset a 'variable-value variable-name index new-res)
                        new-res)))
        )
)


(concept |++.| :constructor |++.| :arguments (first element-access))
(concept |.++| :constructor |.++| :arguments (first element-access))
(concept |--.| :constructor |--.| :arguments (first element-access))
(concept |.--| :constructor |.--| :arguments (first element-access))

(transformation opsem :concept |++.| :stages
    nil :do 
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) structure-array-element-access))
                (progn (to-stage 'arr)
                    (opsem (aget i 'index) a c))
                (to-stage 'nonarray)
            )
        )
    nonarray :do
        (let ((variable-name (map-name a c (aget i 'first 'name) t)))
            (case (get-concept (aget i 'first))
                ('variable-name 
                    (let ((new-res (+ (aget a 'variable-value variable-name) 1)))
                        (aset a 'variable-value variable-name new-res)
                        new-res))
                ('struct-simple-element-access 
                    (let ((variable-name (cons variable-name (aget i 'first 'fields)))
                            (new-res (+ (aget a 'variable-value variable-name) 1))) 
                        (aset a 'variable-value variable-name new-res)
                        new-res)))
        )
    (arr index) :do 
        (let ((variable-name (map-name a c (aget i 'first) t)))
            (case (get-concept (aget i 'first))
                ('array-element-access 
                    (let ((new-res (+ (aget a 'variable-value variable-name index) 1))) 
                        (aset a 'variable-value variable-name index new-res)
                        new-res))
                ('struct-array-element-access
                    (let ((variable-name (cons variable-name (aget i 'first 'fields)))
                            (new-res (+ (aget a 'variable-value variable-name index) 1))) 
                        (aset a 'variable-value variable-name index new-res)
                        new-res)))
        )
)

(transformation opsem :concept |.++| :stages
    nil :do 
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) structure-array-element-access))
                (progn (to-stage 'arr)
                    (opsem (aget i 'index) a c))
                (to-stage 'nonarray)
            )
        )
    nonarray :do
        (let ((variable-name (map-name a c (aget i 'first 'name) t)))
            (case (get-concept (aget i 'first))
                ('variable-name 
                    (let ((sub-res (aget a 'variable-value variable-name index)))
                        (aset a 'variable-value variable-name (+ sub-res 1))
                        sub-res))
                ('struct-simple-element-access 
                    (let ((variable-name (cons variable-name (aget i 'first 'fields)))
                            (sub-res (aget a 'variable-value variable-name index))) 
                        (aset a 'variable-value variable-name (+ sub-res 1))
                        sub-res)))
        )
    (arr index) :do 
        (let ((variable-name (map-name a c (aget i 'first) t)))
            (case (get-concept (aget i 'first))
                ('array-element-access 
                    (let ((sub-res (aget a 'variable-value variable-name index))) 
                        (aset a 'variable-value variable-name index (+ sub-res 1))
                        sub-res))
                ('struct-array-element-access
                    (let ((variable-name (cons variable-name (aget i 'first 'fields)))
                            (sub-res (aget a 'variable-value variable-name index) )) 
                        (aset a 'variable-value variable-name index (+ sub-res 1))
                        sub-res)))
        )
)

(transformation opsem :concept |--.| :stages
    nil :do 
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) structure-array-element-access))
                (progn (to-stage 'arr)
                    (opsem (aget i 'index) a c))
                (to-stage 'nonarray)
            )
        )
    nonarray :do
        (let ((variable-name (map-name a c (aget i 'first 'name) t)))
            (case (get-concept (aget i 'first))
                ('variable-name 
                    (let ((new-res (- (aget a 'variable-value variable-name) 1)))
                        (aset a 'variable-value variable-name new-res)
                        new-res))
                ('struct-simple-element-access 
                    (let ((variable-name (cons variable-name (aget i 'first 'fields)))
                            (new-res (- (aget a 'variable-value variable-name) 1))) 
                        (aset a 'variable-value variable-name new-res)
                        new-res)))
        )
    (arr index) :do 
        (let ((variable-name (map-name a c (aget i 'first) t)))
            (case (get-concept (aget i 'first))
                ('array-element-access 
                    (let ((new-res (- (aget a 'variable-value variable-name index) 1))) 
                        (aset a 'variable-value variable-name index new-res)
                        new-res))
                ('struct-array-element-access
                    (let ((variable-name (cons variable-name (aget i 'first 'fields)))
                            (new-res (- (aget a 'variable-value variable-name index) 1))) 
                        (aset a 'variable-value variable-name index new-res)
                        new-res)))
        )
)

(transformation opsem :concept |.--| :stages
    nil :do 
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) structure-array-element-access))
                (progn (to-stage 'arr)
                    (opsem (aget i 'index) a c))
                (to-stage 'nonarray)
            )
        )
    nonarray :do
        (let ((variable-name (map-name a c (aget i 'first 'name) t)))
            (case (get-concept (aget i 'first))
                ('variable-name 
                    (let ((sub-res (aget a 'variable-value variable-name index)))
                        (aset a 'variable-value variable-name (- sub-res 1))
                        sub-res))
                ('struct-simple-element-access 
                    (let ((variable-name (cons variable-name (aget i 'first 'fields)))
                            (sub-res (aget a 'variable-value variable-name index))) 
                        (aset a 'variable-value variable-name (- sub-res 1))
                        sub-res)))
        )
    (arr index) :do 
        (let ((variable-name (map-name a c (aget i 'first) t)))
            (case (get-concept (aget i 'first))
                ('array-element-access 
                    (let ((sub-res (aget a 'variable-value variable-name index))) 
                        (aset a 'variable-value variable-name index (- sub-res 1))
                        sub-res))
                ('struct-array-element-access
                    (let ((variable-name (cons variable-name (aget i 'first 'fields)))
                            (sub-res (aget a 'variable-value variable-name index) )) 
                        (aset a 'variable-value variable-name index (- sub-res 1))
                        sub-res)))
        )
)

(transformation opsem :concept active :stages 
    nil :do (and (not (equal (aget a 'value) (state-name 'stop)))
    (not (equal (aget a 'value) (state-name 'error))))
)
(transformation opsem :concept inactive :stages 
    nil :do (or (equal (aget a 'value) (state-name 'stop))
    (equal (aget a 'value) (state-name 'error)))
)
(transformation opsem :concept rstop :stages 
    nil :do (equal (aget a 'value) (state-name 'stop))
)
(transformation opsem :concept rerror :stages 
    nil :do (equal (aget a 'value) (state-name 'error))
)
(transformation opsem :concept process-state-checking :stages 
    nil :do (aget a 'process-state (aget i 'process))
    (opsem (aget i 'activity) a c) 
)

;Transformations: statements
(defun next-process-state (a c)
	(let (lst (member (aget c 'processes-states-names (aget a 'current-process)) (current-state a)))
        (if (or (not lst) (= (length lst) 1))
            nil
            (car (cdr lst))))
)

(defun first-state (c process)
    (car (aget c 'process-states process)))
(defun current-first-state (a c)
    (car (aget c 'process-states (aget a 'current-process))))

(defun mashup-symbol (&rest objects) 
    (intern (format nil "~{~a~}" objects)))

(defun mashup-symbol-list (lst) 
    (reduce #'mashup-symbol lst))

(transformation opsem :concept reset-time :stages 
    nil :do (aset a 'process-time (aget a 'current-process) 0))

(transformation opsem :concept set-state :stages 
nil :do (aset a 'process-time (aget a 'current-process) 0) 
    (if (aget i 'state)
        (progn (aset a 'process-state (aget a 'current-process) (aget i 'state))
            (aset a 'process-substate (aget a 'current-process) nil ))
        (let ((res (next-process-state a c)))
            (if (res)
                (progn (aset a 'process-state (aget a 'current-process) state)
                    (aset a 'process-substate (aget a 'current-process) nil))
                (progn (aset a 'stack nil)
                    (error "Current state is last one")))))
)

(defun cons-to-inner-list (a path-list val)
    (aset a path-list (cons val (aget a path-list))))

(transformation opsem :concept restart-process :stages 
nil :do (aset a 'process-state (aget a 'current-process) (aget i 'state))
	(cons-to-inner-list a (list 'processes-to-start) (aget a 'current-process))
	(aset a 'process-time (aget a 'current-process) 0)
)

(transformation opsem :concept start-process :stages 
nil :do (let ((cur-proc (aget a 'current-process))
                (proc (aget i 'process)))
            (if (equal proc cur-proc)
                (opsem (restartp) a c)
                (progn (aset a 'process-state proc (first-state a proc))
                    (cons-to-inner-list a (list 'processes-to-start) proc)
                    (aset a 'process-time proc 0))))
)

(transformation opsem :concept stop-current-process :stages 
nil :do (aset a 'process-state (aget a 'current-process) (state-name 'stop))
    (aset a 'process-time (aget a 'current-process) 0)
)
(transformation opsem :concept stop-process :stages 
nil :do (let ((cur-proc (aget a 'current-process))
                (proc (aget i 'process)))
            (if (equal proc cur-proc)
                (opsem (stop-cur) a c)
                (progn (aset a 'process-state proc 'stop)
                    (aset a 'process-time proc 0))))
)

(transformation opsem :concept error-current-process :stages 
nil :do (aset a 'process-state (aget a 'current-process) (state-name 'error))
    (aset a 'process-time (aget a 'current-process) 0)
)
(transformation opsem :concept error-process :stages 
nil :do (let ((cur-proc (aget a 'current-process))
                (proc (aget i 'process)))
            (if (equal proc cur-proc)
                (opsem (error-cur) a c)
                (prog (aset a 'process-state proc 'error)
                    (aset a 'process-time proc 0))))
)

(transformation opsem :concept if-then-else-statement :stages 
    nil :do (to-stage 'condition) (opsem (aget i 'condition) a c) 
    condition :do 
        (if (equal (aget a 'value) 'true) 
            (opsem (aget i 'then) a c) 
            (opsem (aget i 'else) a c)))

(transformation opsem :concept if-then-statement :stages 
    nil :do (to-stage 'condition) (opsem (aget i 'condition) a c) 
    condition :do 
        (if (equal (aget a 'value) 'true) 
            (opsem (aget i 'then) a c)))


(transformation opsem :concept switch-statement :stages 
    nil :do (to-stage 'condition) (opsem (aget i 'controlling-expression) a c)
    condition :do (let ((cases (aget i 'cases)))
    (if (not (null cases))
    (to-stage 'cases-label cases (aget a 'value) 0 (length cases))))

    (case-label cases cond index length) :do
        (if (< index length)
    (progn (to-stage 'case-iter cases cond index length)
    (opsem (aget (nth index cases) 'label)))
    (to-stage 'default))

    (cases-iter cases cond index length) :do
        (let ((label (aget a 'value)))
            (if (= cond label)
                (progn (if (not (aget (nth index cases) 'break))
                        (to-stage 'cont-case-iter cases (+ index 1) length)
                    (opsem (nth index cases) a c)))
                (to-stage 'case-label cases cond (+ index 1) length)
            ))

    (cont-case-iter cases index length) :do
    (if (< index length)
    (progn (if (not (aget (nth index cases) 'break))
    (to-stage 'cont-case-iter cases (+ index 1) length))
    (opsem (nth index cases) a c))
    (to-stage 'default))

    default :do (let ((def (aget i 'default)))
    (if (not (null def))
    (opsem def a c)))
)
(transformation opsem :concept default-statement :stages
    nil :do (to-stage 'statement (aget i 'statements) 0 (length (aget i 'statements))))
    (statement sts index length) :do (if (index<length)
    (progn (to-stage 'statement sts (+ index 1) length)
    (opsem (nth index sts) a c)))
(transformation opsem :concept case-statement :stages
    nil :do (to-stage 'statement (aget i 'statements) 0 (length (aget i 'statements))))
    (statement sts index length) :do (if (index<length)
    (progn (to-stage 'statement sts (+ index 1) length)
    (opsem (nth index sts) a c)))	


(transformation opsem :concept statement-block :stages
    nil :do (to-stage 'statement (aget i 'statements) 0 (length (aget i 'statements))))
    (statement sts index length) :do (if (index<length)
    (progn (to-stage 'statement sts (+ index 1) length)
    (opsem (nth index sts) a c)))	

(transformation opsem :concept expression-statement :stages
    nil :do (opsem (aget i 'expression) a c)
)

(concept timeout-statement :constructor timeout :arguments (controlling-expression expression) (body :flatten (list statement)))

(transformation opsem :concept timeout-statement :stages
    nil :do (to-stage 'cond) (opsem (aget i 'controlling-expression))
    cond :do (let ((cond (aget a 'value))
        (if (<= value (aget a 'process-time (aget a 'current-process)))
            (to-stage 'body (aget i 'body) 0 (length (aget i 'body))))))
    (body sts index length) :do
        (if (< index length)
            (opsem (nth sts index) a c))
)

(transformation opsem :concept wait :stages
    nil :do (opsem (aget i 'condition)))
(transformation opsem :concept slice :stages
    nil :do ())
(transformation opsem :concept transition :stages
    nil :do (opsem (aget i 'condition)))

(transformation opsem :concept state-declaration :stages
    nil :do (to-stage 'statements 
                (aget i 'body) 
                (let ((substate (aget a 'current-substate)))
                    (if substate substate 0)) 
                (length (aget i 'body)))
    (statements sts index length) :do 
        (if (< index length)
            (progn (if (is-concept (nth sts index) 'barrier-statement) 
                    (to-stage 'barrier (nth sts index) index length)
                    (to-stage 'statements sts (+ index 1) length)
                (opsem (nth sts index) a c)))
            )
    (barrier sts index length) :do
        (if (is-concept (nth sts index) 'wait)
            (if (= (aget a 'value) 'true)
                (progn (to-stage 'statements sts (+ index 1) length)
                    (aset a 'process-substate (aget a 'current-process) (+ index 1)))
                (aset a 'process-substate (aget a 'current-process) index))
            (if (is-concept (nth sts index) 'slice)
                (aset a 'process-substate (aget a 'current-process) index)
                (if (is-concept (nth sts index) 'transition)
                    (if (equal (aget a 'current-substate) index)
                        (if (= (aget a 'value) 'true)
                            (progn (to-stage 'statements sts (+ index 1) length)
                                (aset a 'process-substate (aget a 'current-process) (+ index 1)))
                            (aset a 'process-substate (aget a 'current-process) index))
                        (aset a 'process-substate (aget a 'current-process) index))
                    )))
)


(transformation opsem :concept constant-declaration :stages
    nil :do 
    (let ((name (aget i 'name))
            (cur-proc (aget a 'current-proc)))
        (if (or (aget c 'is-global-variable name) 
                (aget c 'is-process-variable cur-proc name) 
                (aget c 'is-global-constant name) 
                (aget c 'is-process-constant cur-proc name)))
            (progn (aset a 'stack nil)
                (error "Double constant declaration"))
            (progn 
                (if cur-proc
                    (aset c 'is-process-constant cur-proc name t)
                    (aset c 'is-global-variable name t))
                (aset c 'variable-type (map-name a c name nil) (aget i 'rtype))
                (aset c 'is-constant (map-name a c name nil) t)
                (aset c 'constant-value (map-name a c name nil) (aget i 'value))))
)

(concept-by-union variable-declaration simple-variable-declaration array-variable-declaration structure-variable-declaration enum-variable-declaration)



(transformation opsem :concept simple-variable-declaration :stages
    nil :do (to-stage 'first) 
        (if (aget i 'init) 
            (aget i 'init)
            (rtype-default-val (aget i 'rtype)))
    first :do (to-stage 'inited (aget a 'value))
        (let ((name (aget i 'name)))
            (if (aget a 'current-process)
                (if (aget c 'is-process-variable (aget a 'current-process) name)
                    (progn (aset a 'stack nil)
                        (error "Double variable declaration"))
                    (aset c 'is-process-variable (aget a 'current-process) name)
                )
                (if (aget c 'is-global-variable name)
                    (progn (aset a 'stack nil)
                        (error "Double variable declaration"))
                    (aset c 'is-global-variable name)
            )
        ))
    (inited init) :do 
        (let ((name (map-name a c (aget i 'name) t)))
            (progn (aset c 'is-variable name)
                (aset c 'is-simple-variable name)
                (aset c 'variable-init name init)
                (aset c 'variable-type name (aget i 'rtype))))
)

(transformation opsem :concept array-variable-declaration :stages
    nil :do (to-stage 'first) 
        (if (aget i 'init) 
            (aget i 'init)
            (rtype-default-val (aget i 'rtype) (aget i 'size))
        )
    first :do (to-stage 'inited (aget a 'value))
        (let ((name (aget i 'name)))
            (if (aget a 'current-process)
                (if (aget c 'is-process-variable (aget a 'current-process) name)
                    (progn (aset a 'stack nil)
                        (error "Double variable declaration"))
                    (aset c 'is-process-variable (aget a 'current-process) name)
                )
                (if (aget c 'is-global-variable name)
                    (progn (aset a 'stack nil)
                        (error "Double variable declaration"))
                    (aset c 'is-global-variable name)
                )
        ))
    (inited init) :do 
        (let ((name (map-name a c (aget i 'name) t)))
            (progn (aset c 'is-variable name)
                (aset c 'is-array-variable name)
                (aset c 'variable-init name init)
                (aset c 'array-variable-size name (if (aget i 'size)
                                                        (aget i 'size)
                                                        (length (if (is-concept init array-initializer)
                                                                    (aget init 'values)
                                                                    init))))
                (aset c 'variable-type name (aget i 'rtype))))
)

(transformation opsem :concept imported-variable-declaration :stages
    nil :do (let ((cur-proc (aget c 'current-process))
                    (name (aget i 'name))
                    (source-proc (aget i 'source-proc))) 
                (aset c 'is-process-variable cur-proc name source-proc)
                (aset c shared-in-process cur-proc name source-proc (aget i 'source-var))))

(transformation axsem :concept physical-variable-declaration :stages
    nil :do 
    (let ((name (aget i 'name)))
        (if (aget a 'current-process)
            (if (aget c 'is-process-variable)
                (progn (aset a 'stack nil)
                    (error "Unknown variable type"))
                (progn (aset c 'is-process-variable name)
                    (let ((port-name (aget i 'port))
                            (cur-proc (aget a 'current-process))) 
                        (if (member (aget c 'input-ports) port-name)
                            (progn (aset c 'input-variable-port cur-proc name port-name)
                                (aset c 'input-variable cur-proc name port-name (aget i 'index))
                                (aset c 'input-variables (adjoin (aget c 'input-variables) (map-name a c name t)))
                                (aset c 'variable-type (map-name a c name t) (aget i 'rtype)))     
                            (if (member (aget c 'output-ports) port-name)
                                (progn (aset c 'output-variable-port cur-proc name port-name )
                                    (aset c 'output-variable cur-proc name port-name (aget i 'index))
                                    (aset c 'variable-type (map-name a c name t) (aget i 'rtype)))
                                (progn (aset a 'stack nil)
                                    (error "Variable mapped to unkown port"))))))
            )
            (if (aget c 'is-global-variable name)
                (progn (aset a 'stack nil)
                    (error "Double variable declaration"))
                (progn (aset c 'is-global-variable name)
                    (let ((port-name (aget i 'port))) 
                        (if (member (aget c 'input-ports) port-name)
                            (progn (aset c 'input-variable-port '_ name port-name)
                                (aset c 'input-variable '_ name port-name (aget i 'index))
                                (aset c 'input-variables (adjoin (aget c 'input-variables) (map-name a c name t)))
                                (aset c 'variable-type (map-name a c name t) (aget i 'rtype)))
                            (if (member (aget c 'output-ports) port-name)
                                (progn (aset c 'output-variable-port '_ name port-name )
                                    (aset c 'output-variable '_ name port-name (aget i 'index))
                                    (aset c 'variable-type (map-name a c name t) (aget i 'rtype)))
                                (progn (aset a 'stack nil)
                                    (error "Variable mapped to unkown port")))))
                )
            )
        )
    )

)

(transformation opsem :concept structure-declaration :stages
    nil :do 
        (if (aget c 'is-declaration (aget i 'name))
            (progn (aset a 'stack nil)
                (error "Double struct or enum declaration"))
            (let ((fields (aget i 'fields))) 
                (to-stage 'field (aget i name) fields 0 (length fields))
                (aset c 'is-declaration (aget i 'name))))
    (field name fields index length) :do 
        (if (< index length)
            (let ((field (nth index fields)))
                (to-stage 'field name fields (+ index 1) length)
                (aset c 'struct-fields (aget field 'name) (aget field 'rtype))
                (if (is-concept (aget field 'rtype) 'array-type)
                    (aset c 'array-variable-size (mashup-symbol (aget i 'name) (aget field 'name)) (aget field 'rtype 'size))))
            ())
)

(transformation opsem :concept process-declaration :stages
    nil :do 
        (aset a 'current-process (aget i 'name))
        (aset a 'current-state (aget a 'process-state (aget i 'name)))
        (aset a 'current-substate (aget a 'process-substate (aget i 'name)))
        ; (opsem nil)?
        (opsem (find-if (lambda (state) (equal state (aget a 'current-state))) (aget i 'states)) a c) 
)

(transformation opsem :concept structure-variable-declaration :stages
    nil :do
        (let ((name (aget i 'name)))
            (if (aget a 'current-process)
                (if (aget c 'is-process-variable (aget a 'current-process) name)
                    (progn (aset a 'stack nil)
                        (error "Double variable declaration"))
                    (aset c 'is-process-variable (aget a 'current-process) name)
                )
                (if (aget c 'is-global-variable name)
                    (progn (aset a 'stack nil)
                        (error "Double variable declaration"))
                    (aset c 'is-global-variable name)
            )
        ))
        ;? необходим получение элементов map парами
    (inited init) :do 
        (let ((name (map-name a c (aget i 'name) t)))
            (let ((struct-fileds (get-keys (aget c 'struct-fields name)))) 
                (aset c 'is-variable name)
                (aset c 'is-struct-variable name)
                (aset c 'variable-init name (aget i 'init))
                (aset c 'variable-type name (aget i 'rtype))
                (to-stage 'type-unfold name nil struct-fileds 0 (length struct-fileds))))
    (type-unfold name collected fields index length) :do 
        (if (< index length)
            (let* ((entry-key (nth fields index))
                    (entry-value (aget c 'struct-fields name entry-key)))
                (to-stage type-unfold name collected fields (+ index 1) length)
                (if (is-concept entry-value 'structure-type)
                    (let ((struct-fileds (aget c 'struct-fields entry-value)))
                        (to-stage 'type-unfold name (cons (first entry) collected) struct-fileds 0 (length struct-fileds)))
                    (aset c 'variable-type (mashup-symbol-list (cons name (reverse (cons entry-key collected))))))))
)

(transformation opsem :concept enum-declaration :stages
    nil :do (to-stage 'fields (aget i 'fields) 0 (length (aget i 'fields)))
        (let ((name (aget i 'enum-name)))
            (if (aget c 'is-declaration name)
                (progn (aget a 'stack nil)
                    (error “repeated struct or enum declaration”))
                (progn (to-stage 'field name (aget i 'fields) 0 (length (aget i 'fileds)) -1))
                    (aset c 'is-declaration name t)))
    (field name fields index length last-value) :do 
        (if (< index length)
            (let ((field (nth index fields)))
                (if (aget field 'value)
                    (progn (to-stage 'field name fields (+ index 1) length (aget field 'value))
                        (aset c 'enum-value name (ncon (aget c 'enum-value name) (list (aget field 'value)))))
                    (progn (to-stage 'field name fields (+ index 1) length (+ last-value 1))
                        (aset c 'enum-value name (ncon (aget c 'enum-value name) (list (+ last-value 1)))))))
            ())
)

(transformation opsem :concept enum-variable-declaration :stages
    nil :do (to-stage 'first) 
        (if (aget i 'init) 
            (opsem (aget i 'init) a c) 
            0)
    first :do (to-stage 'inited (aget a 'value))
        (let ((name (aget i 'name)))
            (if (aget a 'current-process)
                (if (aget c 'is-process-variable)
                    (progn (aset a 'stack nil)
                        (error "Double variable declaration"))
                    (aset c 'is-process-variable name)
                    
                )
                (if (aget c 'is-global-variable name)
                    (progn (aset a 'stack nil)
                        (error "Double variable declaration"))
                    (aset c 'is-global-variable name)
                )
        ))
    (inited init) :do 
        (let ((name (map-name a c (aget i 'name) t)))
            (progn (aset c 'is-variable name)
                (aset c 'is-enum-variable name)
                (aset context 'variable-init name init)
                (aset c 'variable-type name (aget i 'rtype))))
)

(transformation opsem :concept port-declaration :stages
    nil :do
    (let ((inputs (aget c 'input-ports)) (outputs (aget c 'output-ports))))
        (if (or (member inputs (aget i 'name)) (member outputs (aget i 'name))
            (progn (aset a 'stack nil)
                (error "Double port declaration"))
            (if (is-concept (aget i 'port-type) input)
                (aset c 'input-ports (cons (aget i 'name) inputs))
                (aset c 'output-ports (cons (aget i 'name) outputs)))))
)

(transformation opsem :concept clock :stages
    nil :do 
    (if (is-concept i 'time-constant)
        (opsem i a c)
        i)
)

(transformation opsem :concept program-declaration :stages
    nil :do (to-stage 'clock) (opsem (aget i 'clock))
    clock :do (to-stage 'declarations (aget i 'declarations) 0 (length (aget i 'declarations))) 
        (aset c 'clock (aget a 'value))
    (declarations declarations index length) :do
        (if (index <length)
            (progn (to-stage 'declarations declarations (+ index 1) length)
                (opsem (nth declarations index) a c))
            (to-stage 'processes-prep (aget i 'processes) 0 (length (aget i 'processes))))
    (processes-prep processes index length) :do 
        (if (< index length)
            (let ((process (nth processes index)))
                (to-stage 'processes-prep processes (+ index 1) length)
                (to-stage 'process-var-prep (aget process 'variables) 0 (length (aget process 'variables)))
                (aset c 'processes-state-names (mapcar (lambda (s) (aget s 'name)) (aget process 'states)))
                (aset a 'current-process (aget process 'name))
                (aset a 'process-time (aget process 'name) 0)
                (aset a 'process-state (aget process 'name) 
                    (if (= index 0)
                        (progn
                            (aset a 'processes-to-start (aget process 'name) )
                            (car (aget c 'processes-state-names (aget process 'name))))
                        'stop)))
            (progn (to-stage 'work (aget i 'processes) (length 0 (aget i 'processes)))
                (to-stage 'init-input-vars (aget c 'input-variables) index (length (aget c 'input-variables)))
                (aset a 'processes-to-start 0 (aget i 'processes 0 'name))
                (to-stage 'init-started-procs)
                (to-stage 'init-global-vars (aget i 'declarations) 0 (length (aget i 'declarations))) ))
    (process-var-prep vars index length) :do 
        (if (< index length)
            (opsem (nth index vars) a c))
    (init-global-vars declarations index length) :do 
        (if (< index length)
            (progn (to-stage 'init-global-vars declarations (+ index 1) length)
                (let ((var (nth declarationa index)))
                    (if (or (is-concept var simple-variable-declaration) (is-concept var 'array-variable-declaration) (is-concept var 'enum-variable-declaration))
                        (opsem-init var a c))))
        )
    (work procs index length) :do
        (if (< index length)
            (progn (to-stage 'work (+ index 1) length)
                (opsem (nth procs index) a c)
                (to-stage 'init-started-proc (aget a 'processes-to-start) 0 (length (aget a 'processes-to-start))))
            (progn (to-stage 'work procs 0 length)
                (to-stage 'init-input-vars (aget c 'input-variables) index (length (aget c 'input-variables)))))

    (init-started-proc procs index length) :do
        (if (< index length) 
            (progn (to-stage 'init-started-proc procs (+ index 1) length)
                (if (member (aget procs index 'name) (aget a 'processes-to-start))
                    (opsem-init (nth procs index) a c)))
            (aset a 'processes-to-start nil))
    ;?затычка для рандомной инициализации
    (init-input-vars vars index length) :do
        (if (< index length)
            (progn (to-stage 'init-input-vars vars (+ index 1) length)
                (let ((name (map-name a c (nth vars index) t)))
                    (aset a 'variable-value name (random 100)))
            )
        )
)

(transformation opsem-init :concept simple-variable-declaration :stages
    nil :do (to-stage 'inited)
        (opsem (aget c 'variable-init (map-name a c (aget i 'name) t)) a c)
    inited :do (aset a 'variable-value (map-name a c (aget i 'name) t) (aget a 'value))
)

(transformation opsem-init :concept array-variable-declaration :stages
    nil :do 
    (let ((name (map-name a c (aget i 'name) t)))
        (to-stage 'to-init name (aget c 'variable-init name) 0 (length (aget c 'variable-init name))))
    (to-init name arr index length) :do 
        (if (< index length)
            (progn (to-stage 'inited name arr index length)
                (opsem (aget arr index) a c)))
    (inited name arr index length) :do (to-stage 'to-init name arr (+ index 1) length)
        (aset a 'variable-value name index (aget a 'value))
)

(concept struct-init (map fieled-name reflex-init))
(concept structure-variable-declaration :constructor struct-var-decl :arguments (name variable-name) (rtype structure-name) (init :opt struct-init))
(concept-by-union reflex-init simple-init array-init struct-init enum-element-access)

(transformation opsem-init :concept structure-variable-declaration :stages 
    nil :do 
    (let ((name (map-name a c (aget i 'name) t)))
        (if (aget c 'variable-init name)
            (to-stage 'struct-init name nil (get-keys (aget c 'variable-init name)) 0 (length (get-keys(aget c 'variable-init name))))))
    ;collected backwards
    (struct-init name collected key-names index length) :do
        (if (< index length)
            (let* ((key-name (nth key-names index))
                    (value (aget c 'variable-init name key-name)))
                (if (is-concept (second init) 'struct-init)
                    (progn (to-stage 'struct-init name collected key-names (+ index 1) length)
                        (to-stage 'struct-init name (cons collected key-name) (get-keys value) 0 (get-keys value)))
                    (if (is-concept (second init) 'simple-init)
                        (progn (to-stage 'simple-init name (cons collected key-name))
                            (opsem key-name a c))
                        (if (is-concept value 'simple-init)
                            (to-stage 'array-init name collected value 0 (length value)))
                            )))
        )
    (simple-init name collected) :do 
        (aset a 'variable-value (cons name (reverse collected)) (aget a 'value))
    (array-init name collected arr index length) :do
        (if (< index length)
            (progn (to-stage 'array-init name collected arr (+ index 1) length)
                (to-stage 'array-init-set name collected index)
                (opsem (nth arr index) a c)))
    (array-init-set name collected index) :do
        (aset a 'variable-value (cons name (reverse collected)) index (aget a 'value))
)

(transformation opsem-init :concept enum-variable-declaration :stages
    nil :do (to-stage 'inited)
        (opsem (aget c 'variable-init (map-name a c (aget i 'name) t)) a c)
    inited :do (aset a 'variable-value (map-name a c (aget i 'name) t) (aget a 'value))
)

(transformation opsem-init :concept process-variables :stages
    nil :do (to-stage 'init-vars (aget i 'variables) 0 (length (aget i 'variables))))
        (aset a 'process-time (aget i 'name) 0)
        (aset a 'process-state (aget i 'name) (first-state c (aget i 'name)))
        (aset a 'process-substate (aget i 'name) 0)
    (init-vars vars index length) :do
        (if (< index length)
            (opsem-init (nth vars index) a c))
