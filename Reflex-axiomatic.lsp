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

(struct-fields (map variable-name (map variable-name rtype)))
(enum-value (map enum-name (map field-name int)))

(clock int)

(conditions (list vc-lemma))
(conditions-printed int)
(state-num int)
(condition-num int)
(is-printed tbool)
)

(concept agent :constructor agent :attributes
(variable-value (map variable-name reflex-value))
(current-process process-name)

(processes-to-start (list process-name))


(cur-cond (list formula))

;expression attributes
(precond (list formula))
(proc-act (map process-name activity))
(state program-state)
)


(defun clone-agent (a c)
    (let ((ag (agent :attributes
            (aget a 'variable-value)
            (aget a 'current-process)
            (aget a 'processes-to-start)


            (aget a 'cur-cond)
           
            (aget a 'precond)
            (aget a 'proc-act)
            (aget a 'state)
            )))
        (aset ag 'stack (aget a 'stack))
        (cons-to-inner-list c (list 'agents) ag)
        ag)
)


(defun clear-agent-expr (a)
    (progn 
        (aset a 'precond nil)
        (aset a 'proc-act nil)
        (aset a 'expressions nil)
        (aset a 'state (placeholder))
        (aset a 'domain nil)
        (aset a 'bool-val nil)
        (aset a 'expr-break nil)))

;Не перепутает ли концепты с символами
(concept-by-value program-state-name symbol)

(concept-by-value real-name name)

(concept-by-value outer-var name)
(concept-by-union term actuatable-term nonactuatable-term)
(concept-by-union actuatable-term binary-operation unary-operation simple-value-getter array-value-getter cast-operation)
(concept-by-union nonactuatable-term constant pstate-compare outer-var)
(concept-by-union program-state program-state-name simple-value-setter array-value-setter)

(concept simple-value-getter :constructor sv-get :arguments (type simple-type) (state program-state) (name real-name) :tag actuated)
(concept array-value-getter :constructor av-get :arguments (type simple-type) (state program-state) (name real-name) (index term) :tag actuated)
(concept simple-value-setter :constructor sv-set :arguments (type simple-type) (state program-state) (name real-name) (value term))
(concept array-value-setter :constructor av-set :arguments (type simple-type) (state program-state) (name real-name) (index term) (value term))

(concept binary-operation :constructor binop :arguments (type simple-type) (op bop) (left term) (right term) :tag actuated)
(concept unary-operation :constructor unop :arguments (type simple-type) (op uop) (right term) :tag actuated)
(concept cast-operation :constructor castop :arguments (type simple-type) (term term) :tag actuated)

(concept-by-union logic-binop '&& '|| '== '!= '< '<= '> '>=)
(concept-by-union num-binop '+ '- '* '/ '% '& '| '^ '<< '>>)
(concept-by-union bop logic-bop num-bop)
(concept-by-union uop  '-. '!. '~. )

(concept pstate-compare :constructor ps-comp (state program-state) (process process-name) (pstate state-name))

(concept implication :constructor impl :arguments (left term) (right term))
(concept conjunction :construction conj :arguments (formulas (list formula)))
(concept disjunction :construction dish :arguments (formulas (list formula)))

(concept-by-union formula forall exists state-update ltime-check term implication inv-plug conjunction disjunction)
(concept-by-union state-update program-state reset to-env)

(concept-by-value arg-name symbol)
(concept forall :constructor forall :arguments (args :flatten (list arg-name)) (formula formula))
(concept exists :constructor exists :arguments (args :flatten (list arg-name)) (formula formula))
(concept reset :constructor rreset :arguments (state program-state))
(concept to-env :constructor to-env :arguments (state program-state))
(concept ltime-check :constructor ltime :arguments (state program-state) (process process-name) (compare-val term) :tags exceed)


(concept vc-lemma :constructor vc-lemma :argumets (precondition formula) (postcondition formula) (steps (list formula)))

(defun cons-to-inner-list (a path-list val)
    (aset a path-list (cons val (aget a path-list))))

;добавляет ограничения на состояния процессов к предусловию и обнуляет их
(defun finalize-proc-act (a)
    (let ((res (mapcar 
                (lambda (proc-name) 
                    (case (get-concept (aget a 'proc-act proc-name))
                        ('active (conj (lits (unop (true) '!. (ps-comp 'blank proc-name 'stop)) (unop (true) '!. (ps-comp 'blank  proc-name 'error)))))
                        ('inactive (disj (lits (ps-comp 'blank proc-name 'stop) (ps-comp 'blank proc-name 'error))))
                        ('rstop (ps-comp 'blank proc-name 'stop))
                        ('rerror (ps-comp 'blank proc-name 'stop))
                        ('nonstop (unop (true) '!. (ps-comp 'blank proc-name 'stop)))
                        ('nonerror (unop (true) '!. (ps-comp 'blank proc-name 'error)))
                    )) 
                (get-keys (aget a 'proc-act)))))
        (if (> (length res) 1)
            (cons-to-inner-list a (list 'cur-cond) (conj res))
            (if (= (length res) 1)
                (cons-to-inner-list a (list 'cur-cond) res)))))

;добавляет обновление на состояния программы к предусловию и обнуляет его
;Что возвращает get-concept? Что если было обьявление concept-by-value?
(defun finalize-state (a)
    (if (not (is-concept (aget a 'state) 'program-state-name))
        (cons-to-inner-list a (list 'cur-cond) (aget a 'state)))
)
;добавляет локальное предусловие к предусловию и обнуляет его
(defun finalize-precond (a)
    (if (> (length (aget a 'precond)) 1)
            (cons-to-inner-list a (list 'cur-cond) (conj (aget a 'precond)))
            (if (= (len res) 1)
                (cons-to-inner-list a (list 'cur-cond) (aget a 'precond)))))

(defun finalize-expression (a)
    (progn 
        (finalize-proc-act a)
        (finalize-precond a)
        (finalize-state a)))

(defun create-lemma (a postcondition)
    (vc-lemma (inv-plug) postcondition (reverse 
        (progn (finalize-expression a)
                (aget a 'cur-cond)))))

(defun finalize-lemma (a c postcondition)
    (cons-to-inner-list c (list 'conditions) (create-lemma a postcondition)))

(defun finalize-base-lemma (a c)
    (cons-to-inner-list c (list 'conditions) (vc-lemma (true) (inv-plug) (reverse (aget a 'cur-cond)))))

(defun finalize-general-lemma (a c)
    (cons-to-inner-list c (list 'conditions) (vc-lemma (inv-plug) (inv-plug) (reverse (aget a 'cur-cond)))))



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


(transformation actuate :concept simple-value-getter :stages 
    nil :do 
        (if (aget i 'actuated)
            i
            (sv-get (aget i 'type) (aget a 'state) (aget i 'name) :tags t))
)

#|int c[3]={0,0,0};
    c[c[0]]=++c[0];
    c={1,1,0} |#
(transformation actuate :concept array-value-getter :stages 
    nil :do 
        (if (aget i 'actuated)
            i
            (av-get (aget i 'type) (aget a 'state) (aget i 'name) (actuate (aget i 'index)) :tags t))
)    

(transformation actuate :concept binary-operation :stages
    nil :do 
        (if (aget i 'actuated)
            i
            (binop (aget i 'op) (actuate (aget i 'left)) (actuate (aget i 'right)))))

(transformation actuate :concept binary-operation :stages
    nil :do 
        (if (aget i 'actuated)
            i
            (binop (aget i 'op) (actuate (aget i 'left)) (actuate (aget i 'right)))))
(transformation actuate :concept unary-operation :stages
    nil :do 
        (if (aget i 'actuated)
            i
            (unop (aget i 'op) (actuate (aget i 'right)))))
(transformation actuate :concept cast-operation :stages
    nil :do 
        (if (aget i 'actuated)
            i
            (castop (aget i 'type) (actuate (aget i 'term)))))
(transformation actuate :concept nonactuatable-term :stages 
    nil :do i)


;TODO
(defun type-eval (op left right)
    (if (is-concept op 'logic-binop)
        (true)
        (if (or (is-concept left 'float-type) (is-concept right 'float-type))
            (0.0)
            ())))


;Применяется к term
(transformation get-type :concept constant :stages  
    nil :do i)
(transformation get-type :concept pstate-compare :stages 
    nil :do (true))
(transformation get-type :concept outer-var :stages
    nil :do (aget c 'variable-type i))
(transformation get-type :concept binary-operation :stages
    nil :do (aget i 'type))
(transformation get-type :concept unary-operation :stages
    nil :do (aget i 'type))
(transformation get-type :concept cast-operation :stages
    nil :do (aget i 'type))
(transformation get-type :concept simple-value-getter :stages
    nil :do (aget c 'variable-type 'name))
(transformation get-type :concept array-value-getter :stages
    nil :do (aget c 'variable-type 'name))


(transformation axsem :concept time-constant :stages
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

(transformation axsem :concept non-time-constant :stages 
    nil :do i
)

;expression возвращает term 
(transformation axsem :concept variable-name :stages 
    nil :do 
    (let*
        ((state (aget ))
            (vname (map-name a c i t))
            (cname (map-name a c i nil)))
        (if cname
            (aget c 'constant-value cname)
            (if vname
                (sv-get (aget c 'variable-type vname) (aget a 'state) vname)
                (progn (aset a 'stack nil)
                    (error "Uknown variable")))
            (sv-get (aget c 'variable-type vname) (aget a 'state) vname)))
)

(transformation axsem :concept array-element-access :stages 
    nil :do (to-stage 'val)
        (if (aget c 'is-array-variable (map-name a c (aget i 'name) t))
            (axsem (aget i 'index) a c)
            (progn (aset a 'stack nil)
                (error "Array not exists")))
    val :do 
        (let ((idx (aget a 'value))
                (name (map-name a c (aget i 'name) t)))
            (finalize-lemma a c (binop '&& (binop '>= idx 0) (binop '< idx (aget c 'array-variable-size name))))
            (cons-to-inner-list a (list 'precond) (binop '&& (binop '>= idx 0) (binop '< idx (aget c 'array-variable-size name))))
            (av-get (aget c 'variable-type vname) (aget a 'state) vname idx)
        )
)


(transformation axsem :concept struct-simple-element-access :stages
    nil :do 
        (let ((name (mashup-symbol-list (cons (map-name a c (aget i 'name) t) (aget i 'fields)))))
            (sv-get (aget c 'variable-type name) (aget a 'state) name))
)

(transformation axsem :concept struct-array-element-access :stages 
    nil :do (to-stage 'val) (axsem (aget i 'index) a c)
    val :do 
        (let ((idx (aget a 'value))
                (name (mashup-symbol-list (cons (map-name a c (aget i 'name) t) (aget i 'fields)))))
            (finalize-lemma a c (binop '&& (binop '>= idx 0) (binop '< idx (aget c 'array-variable-size name))))
            (cons-to-inner-list a (list 'precond) (binop '&& (binop '>= idx 0) (binop '< idx (aget c 'array-variable-size name))))
            (av-get (aget c 'variable-type vname) (aget a 'state) vname idx)
        )
)    

(transformation axsem :concept enum-element-access :stages 
    nil :do (aget c 'enum-value (aget i 'name) (aget i 'field)))

;Transformations: expressions
(transformation axsem :concept |+| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (axsem (aget i 'second) a c))
    (second left) :do 
        (let* ((new-left (actuate left a c))
                (new-right (actuate (aget a 'value) a c))
                (new-type (type-eval '+ (get-type new-left) (get-type new-right))))
            (binop new-type '+ new-left new-right))
(transformation axsem :concept |-| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (axsem (aget i 'second) a c))
    (second left) :do 
        (let* ((new-left (actuate left a c))
                (new-right (actuate (aget a 'value) a c))
                (new-type (type-eval '- (get-type new-left) (get-type new-right))))
            (binop new-type '- new-left new-right))
(transformation axsem :concept |*| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (axsem (aget i 'second) a c))
    (second left) :do 
        (let* ((new-left (actuate left a c))
                (new-right (actuate (aget a 'value) a c))
                (new-type (type-eval '* (get-type new-left) (get-type new-right))))
            (binop new-type '* new-left new-right))
(transformation axsem :concept |/| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (axsem (aget i 'second) a c))
    (second left) :do 
        (let* ((new-left (actuate left a c))
                (new-right (actuate (aget a 'value) a c))
                (new-type (type-eval '/ (get-type new-left) (get-type new-right))))
            (finalize-lemma a c (binop (true)'!= new-right 0))
            (cons-to-inner-list a (list 'precond) (binop (true) '!= new-right 0))
            (binop new-type '/ new-left new-right))
(transformation axsem :concept |%| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (axsem (aget i 'second) a c))
    (second left) :do 
        (let* ((new-left (actuate left a c))
                (new-right (actuate (aget a 'value) a c))
                (new-type (type-eval '% (get-type new-left) (get-type new-right))))
            (finalize-lemma a c (binop (true) '!= new-right 0))
            (cons-to-inner-list a (list 'precond) (binop (true) '!= new-right 0))
            (binop new-type '% new-left new-right))
(transformation axsem :concept |<<| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (axsem (aget i 'second) a c))
    (second left) :do 
        (let* ((new-left (actuate left a c))
                (new-right (actuate (aget a 'value) a c))
                (new-type (type-eval '<< (get-type new-left) (get-type new-right))))
            (binop new-type '<< new-left new-right))
(transformation axsem :concept |>>| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (axsem (aget i 'second) a c))
    (second left) :do 
        (let* ((new-left (actuate left a c))
                (new-right (actuate (aget a 'value) a c))
                (new-type (type-eval '>> (get-type new-left) (get-type new-right))))
            (binop new-type '>> new-left new-right))

(transformation axsem :concept |==| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (axsem (aget i 'second) a c))
    (second left) :do 
        (let ((new-left (actuate left a c))
                (new-right (actuate (aget a 'value) a c)))
            (if (and (is-concept new-left 'boolean-constant) (is-concept new-right 'boolean-constant))
                (cond ((or (and (is-concept new-left 'true) (is-concept new-right 'true))
                            (and (is-concept new-left 'false) (is-concept new-right 'false))) 
                        (true))
                    ((or (and (is-concept new-left 'false) (is-concept new-right 'true))
                        (and (is-concept new-left 'true) (is-concept new-right 'false))) 
                    (false)))
                (binop (true) '== new-left new-right)))
(transformation axsem :concept |!=| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (axsem (aget i 'second) a c))
    (second left) :do 
        (let ((new-left (actuate left a c))
                (new-right (actuate (aget a 'value) a c)))
            (if (and (is-concept new-left 'boolean-constant) (is-concept new-right 'boolean-constant))
                (cond ((or (and (is-concept new-left 'true) (is-concept new-right 'false))
                            (and (is-concept new-left 'false) (is-concept new-right 'true))) 
                        (true))
                    ((or (and (is-concept new-left 'true) (is-concept new-right 'true))
                        (and (is-concept new-left 'false) (is-concept new-right 'false))) 
                    (false)))
                (binop (true) '!= new-left new-right)))
(transformation axsem :concept |>=| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (axsem (aget i 'second) a c))
    (second left) :do 
        (let ((new-left (actuate left a c))
                (new-right (actuate (aget a 'value) a c)))
            (if (and (is-concept new-left 'boolean-constant) (is-concept new-right 'boolean-constant))
                (cond ((or (and (is-concept new-left 'true) (is-concept new-right 'true))
                            (and (is-concept new-left 'false) (is-concept new-right 'false))
                            (and (is-concept new-left 'true) (is-concept new-right 'false))) 
                        (true))
                    ((and (is-concept new-left 'false) (is-concept new-right 'true)) 
                    (false)))
                (binop (true) '>= new-left new-right)))
(transformation axsem :concept |<=| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (axsem (aget i 'second) a c))
    (second left) :do 
        (let ((new-left (actuate left a c))
                (new-right (actuate (aget a 'value) a c)))
            (if (and (is-concept new-left 'boolean-constant) (is-concept new-right 'boolean-constant))
                (cond ((or (and (is-concept new-left 'true) (is-concept new-right 'true))
                            (and (is-concept new-left 'false) (is-concept new-right 'false))
                            (and (is-concept new-left 'false) (is-concept new-right 'true))) 
                        (true))
                    ((and (is-concept new-left 'true) (is-concept new-right 'false)) 
                    (false)))
                (binop (true) '<= new-left new-right)))
(transformation axsem :concept |>| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (axsem (aget i 'second) a c))
    (second left) :do 
        (let ((new-left (actuate left a c))
                (new-right (actuate (aget a 'value) a c)))
            (if (and (is-concept new-left 'boolean-constant) (is-concept new-right 'boolean-constant))
                (cond ((and (is-concept new-left 'true) (is-concept new-right 'false)) 
                        (false))
                    ((or (and (is-concept new-left 'true) (is-concept new-right 'true))
                        (and (is-concept new-left 'false) (is-concept new-right 'false))
                        (and (is-concept new-left 'false) (is-concept new-right 'true))) 
                    (true)))
                (binop (true) '> new-left new-right)))
(transformation axsem :concept |<| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (axsem (aget i 'second) a c))
    (second left) :do 
        (let ((new-left (actuate left a c))
                (new-right (actuate (aget a 'value) a c)))
            (if (and (is-concept new-left 'boolean-constant) (is-concept new-right 'boolean-constant))
                (cond ((and (is-concept new-left 'false) (is-concept new-right 'true)) 
                        (false))
                    ((or (and (is-concept new-left 'true) (is-concept new-right 'true))
                        (and (is-concept new-left 'false) (is-concept new-right 'false))
                        (and (is-concept new-left 'true) (is-concept new-right 'false))) 
                    (true)))
                (binop (true) '< new-left new-right)))


(transformation axsem :concept |&&| :stages 
    nil :do (to-stage 'long) (to-stage 'short :agent (clone-agent a c)) (axsem (aget i 'first) a c)
    short :do 
        (let ((res (actuate (aget a 'value) )))
            (cons-to-inner-list a (list 'precond) (unop '! res))
            (false))
    long :do
        (let ((res (actuate (aget a 'value))))
            (to-stage 'second) 
            (cons-to-inner-list a (list 'precond) res)
            (axsem (aget i 'second) a c))
    second :do 
        (let ((res (actuate (aget a 'value))))
            res)
)

(transformation axsem :concept |\|\|| :stages 
    nil :do (to-stage 'long) (to-stage 'short :agent (clone-agent a c)) (axsem (aget i 'first) a c)
    short :do 
        (let ((res (actuate (aget a 'value) )))
            (cons-to-inner-list a (list 'precond)  res)
            (true))
    long :do
        (let ((res (actuate (aget a 'value))))
            (to-stage 'second) 
            (cons-to-inner-list a (list 'precond) (unop '! res))
            (axsem (aget i 'second) a c))
    second :do 
        (let ((res (actuate (aget a 'value))))
            res)
)

(transformation axsem :concept |&| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (axsem (aget i 'second) a c))
    (second left) :do 
        (let* ((new-left (actuate left a c))
                (new-right (actuate (aget a 'value) a c))
                (new-type (type-eval '& (get-type new-left) (get-type new-right))))
            (binop new-type '& new-left new-right))
(transformation axsem :concept |\|| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (axsem (aget i 'second) a c))
    (second left) :do 
        (let* ((new-left (actuate left a c))
                (new-right (actuate (aget a 'value) a c))
                (new-type (type-eval '| (get-type new-left) (get-type new-right))))
            (binop new-type '\ new-left new-right))
(transformation axsem :concept |^| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (to-stage 'second (aget a 'value)) (axsem (aget i 'second) a c))
    (second left) :do 
        (let* ((new-left (actuate left a c))
                (new-right (actuate (aget a 'value) a c))
                (new-type (type-eval '^ (get-type new-left) (get-type new-right))))
            (binop new-type '^ new-left new-right))

(transformation axsem :concept cast :stages 
    nil :do (to-stage 'cast) (axsem (aget i 'expression) a c)
    cast :do 
        (let ((res (actuate (aget a 'value) a c)))
            (castop (aget i 'rtype) res)))

(transformation axsem :concept |!.| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (unop (true) '!. (actuate (aget a 'value))))
(transformation axsem :concept |-.| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do 
        (let* ((res (actuate (aget a 'value)))
                (new-type (get-type res)))
            (unop new-type '-. res)))
(transformation axsem :concept |~.| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do 
        (let* ((res (actuate (aget a 'value)))
                (new-type (get-type res)))
            (unop new-type '~. res)))
(transformation axsem :concept |+.| :stages 
    nil :do (to-stage 'first) (axsem (aget i 'first) a c)
    first :do (actuate (aget a 'value)))

(transformation axsem :concept |=| :stages 
    nil :do 
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) struct-array-element-access))
                (progn (to-stage 'val)
                    (axsem (aget i 'second) a c))
                (progn (to-stage 'nonarray)
                    (axsem (aget i 'second) a c))))
    nonarray :do 
        (let ((res (actuate (aget a 'value) a c))
                (name (if (is-concept (aget i 'first) variable-name)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields))))))
            (aset a 'state (sv-set  (aget c 'variable-type name) (aget a 'state) name res))
            (sv-get (aget c 'variable-type name) (aget a 'state) name))
    val :do 
        (let ((res (actuate (aget a 'value) a c)))
            (to-stage 'arr res)
            (axsem (aget i 'index) a c))
    (arr res) :do
        (let ((index (actuate (aget a 'value) a c))
                (name (if (is-concept (aget i 'first) array-element-access)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields))))))
            (finalize-lemma a c (binop '&& (binop '>= index 0) (binop '< index (aget c 'array-variable-size name))))
            (cons-to-inner-list a (list 'precond) (binop '&& (binop '>= index 0) (binop '< index (aget c 'array-variable-size name))))
            (aset a 'state (av-set (aget c 'variable-type name) (aget a 'state) name index res))
            (av-get (aget c 'variable-type name) (aget a 'state) name index))
)

(transformation axsem :concept |+=| :stages 
    nil :do 
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) struct-array-element-access))
                (progn (to-stage 'val)
                    (axsem (aget i 'second) a c))
                (progn (to-stage 'nonarray)
                    (axsem (aget i 'second) a c))))
    nonarray :do 
        (let* ((res (actuate (aget a 'value) a c))
                (name (if (is-concept (aget i 'first) variable-name)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields)))))
                (right (actuate (sv-get (aget c 'variable-type name) (aget a 'state) name) a c))
                (new-type (type-eval '+ (get-type res) (get-type right)))
                (val (binop new-type '+ res right)))
            (aset a 'state (sv-set  (aget c 'variable-type name) (aget a 'state) name val))
            (sv-get (aget c 'variable-type name) (aget a 'state) name))
    val :do 
        (let ((res (actuate (aget a 'value) a c)))
            (to-stage 'arr res)
            (axsem (aget i 'index) a c))
    (arr res) :do
        (let* ((index (actuate (aget a 'value) a c))
                (name (if (is-concept (aget i 'first) array-element-access)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields)))))
                (right (actuate (av-get (aget c 'variable-type name) (aget a 'state) name index) a c))
                (new-type (type-eval '+ (get-type res) (get-type right)))
                (val (binop new-type '+ res right)))
            (finalize-lemma a c (binop (true) '&& (binop (true) '>= index 0) (binop (true) '< index (aget c 'array-variable-size name))))
            (cons-to-inner-list a (list 'precond) (binop (true) '&& (binop (true) '>= index 0) (binop (true) '< index (aget c 'array-variable-size name))))
            (aset a 'state (av-set (aget c 'variable-type name) (aget a 'state) name index val))
            (av-get (aget c 'variable-type name) (aget a 'state) name index))
)
(transformation axsem :concept |-=| :stages 
    nil :do 
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) struct-array-element-access))
                (progn (to-stage 'val)
                    (axsem (aget i 'second) a c))
                (progn (to-stage 'nonarray)
                    (axsem (aget i 'second) a c))))
    nonarray :do 
        (let* ((res (actuate (aget a 'value) a c))
                (name (if (is-concept (aget i 'first) variable-name)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields)))))
                (right (actuate (sv-get (aget c 'variable-type name) (aget a 'state) name) a c))
                (new-type (type-eval '- (get-type res) (get-type right)))
                (val (binop new-type '- res right)))
            (aset a 'state (sv-set  (aget c 'variable-type name) (aget a 'state) name val))
            (sv-get (aget c 'variable-type name) (aget a 'state) name))
    val :do 
        (let ((res (actuate (aget a 'value) a c)))
            (to-stage 'arr res)
            (axsem (aget i 'index) a c))
    (arr res) :do
        (let* ((index (actuate (aget a 'value) a c))
                (name (if (is-concept (aget i 'first) array-element-access)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields)))))
                (right (actuate (av-get (aget c 'variable-type name) (aget a 'state) name index) a c))
                (new-type (type-eval '- (get-type res) (get-type right)))
                (val (binop new-type '- res right)))
            (finalize-lemma a c (binop (true) '&& (binop (true) '>= index 0) (binop (true) '< index (aget c 'array-variable-size name))))
            (cons-to-inner-list a (list 'precond) (binop (true) '&& (binop (true) '>= index 0) (binop (true) '< index (aget c 'array-variable-size name))))
            (aset a 'state (av-set (aget c 'variable-type name) (aget a 'state) name index val))
            (av-get (aget c 'variable-type name) (aget a 'state) name index))
)

(transformation axsem :concept |*=| :stages 
    nil :do 
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) struct-array-element-access))
                (progn (to-stage 'val)
                    (axsem (aget i 'second) a c))
                (progn (to-stage 'nonarray)
                    (axsem (aget i 'second) a c))))
    nonarray :do 
        (let* ((res (actuate (aget a 'value) a c))
                (name (if (is-concept (aget i 'first) variable-name)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields)))))
                (right (actuate (sv-get (aget c 'variable-type name) (aget a 'state) name) a c))
                (new-type (type-eval '* (get-type res) (get-type right)))
                (val (binop new-type '* res right)))
            (aset a 'state (sv-set  (aget c 'variable-type name) (aget a 'state) name val))
            (sv-get (aget c 'variable-type name) (aget a 'state) name))
    val :do 
        (let ((res (actuate (aget a 'value) a c)))
            (to-stage 'arr res)
            (axsem (aget i 'index) a c))
    (arr res) :do
        (let* ((index (actuate (aget a 'value) a c))
                (name (if (is-concept (aget i 'first) array-element-access)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields)))))
                (right (actuate (av-get (aget c 'variable-type name) (aget a 'state) name index) a c))
                (new-type (type-eval '* (get-type res) (get-type right)))
                (val (binop new-type '* res right)))
            (finalize-lemma a c (binop (true) '&& (binop (true) '>= index 0) (binop (true) '< index (aget c 'array-variable-size name))))
            (cons-to-inner-list a (list 'precond) (binop (true) '&& (binop (true) '>= index 0) (binop (true) '< index (aget c 'array-variable-size name))))
            (aset a 'state (av-set (aget c 'variable-type name) (aget a 'state) name index val))
            (av-get (aget c 'variable-type name) (aget a 'state) name index))

)

(transformation axsem :concept |/=| :stages 
    nil :do 
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) struct-array-element-access))
                (progn (to-stage 'val)
                    (axsem (aget i 'second) a c))
                (progn (to-stage 'nonarray)
                    (axsem (aget i 'second) a c))))
    nonarray :do 
        (let* ((res (actuate (aget a 'value) a c))
                (name (if (is-concept (aget i 'first) variable-name)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields)))))
                (right (actuate (sv-get (aget c 'variable-type name) (aget a 'state) name) a c))
                (new-type (type-eval '/ (get-type res) (get-type right)))
                (val (binop new-type '/ res right)))
            (finalize-lemma a c (binop (true) '!= res 0))
            (cons-to-inner-list a (list 'precond) (binop (true) '!= res 0))
            (aset a 'state (sv-set  (aget c 'variable-type name) (aget a 'state) name val))
            (sv-get (aget c 'variable-type name) (aget a 'state) name))
    val :do 
        (let ((res (actuate (aget a 'value) a c)))
            (to-stage 'arr res)
            (axsem (aget i 'index) a c))
    (arr res) :do
        (let* ((index (actuate (aget a 'value) a c))
                (name (if (is-concept (aget i 'first) array-element-access)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields)))))
                (right (actuate (av-get (aget c 'variable-type name) (aget a 'state) name index) a c))
                (new-type (type-eval '/ (get-type res) (get-type right)))
                (val (binop new-type '/ res right)))
            (finalize-lemma a c (binop (true) '!= res 0))
            (cons-to-inner-list a (list 'precond) (binop (true) '!= res 0))
            (finalize-lemma a c (binop (true) '&& (binop (true) '>= index 0) (binop (true) '< index (aget c 'array-variable-size name))))
            (cons-to-inner-list a (list 'precond) (binop (true) '&& (binop (true) '>= index 0) (binop (true) '< index (aget c 'array-variable-size name))))
            (aset a 'state (av-set (aget c 'variable-type name) (aget a 'state) name index val))
            (av-get (aget c 'variable-type name) (aget a 'state) name index))
)

(transformation axsem :concept |++.| :stages
    nil :do 
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) struct-array-element-access))
                (progn (to-stage 'arr)
                    (axsem (aget i 'index) a c))
                (progn (to-stage 'nonarray)
                    )))
    nonarray :do 
        (let* ((name (if (is-concept (aget i 'first) variable-name)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields)))))
                (res (actuate (sv-get (aget c 'variable-type name) (aget a 'state) name) a c))
                (new-type (type-eval '+ (get-type res) 1))
                (val (binop new-type '+ res 1)))
            (aset a 'state (sv-set  (aget c 'variable-type name) (aget a 'state) name val))
            (sv-get (aget c 'variable-type name) (aget a 'state) name))
    arr :do
        (let* ((index (actuate (aget a 'value))) 
                (name (if (is-concept (aget i 'first) array-element-access)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields)))))
                (res (actuate (av-get (aget c 'variable-type name) (aget a 'state) name index) a c))
                (new-type (type-eval '+ (get-type res) 1))
                (val (binop new-type '+ res 1)))
            (finalize-lemma a c (binop (true) '&& (binop (true) '>= index 0) (binop (true) '< index (aget c 'array-variable-size name))))
            (cons-to-inner-list a (list 'precond) (binop (true) '&& (binop (true) '>= index 0) (binop (true) '< index (aget c 'array-variable-size name))))
            (aset a 'state (av-set (aget c 'variable-type name) (aget a 'state) name index val))
            (av-get (aget c 'variable-type name) (aget a 'state) name index))
)


(transformation axsem :concept |.++| :stages
    nil :do 
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) struct-array-element-access))
                (progn (to-stage 'arr)
                    (axsem (aget i 'index) a c))
                (progn (to-stage 'nonarray)
                    )))
    nonarray :do 
        (let* ((name (if (is-concept (aget i 'first) variable-name)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields)))))
                (res (actuate (sv-get (aget c 'variable-type name) (aget a 'state) name) a c))
                (new-type (type-eval '+ (get-type res) 1))
                (val (binop new-type '+ res 1))
                )
            (aset a 'state (sv-set  (aget c 'variable-type name) (aget a 'state) name val))
            res)
    arr :do
        (let* ((index (actuate (aget a 'value)))  
                (name (if (is-concept (aget i 'first) array-element-access)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields)))))
                (res (actuate (av-get (aget c 'variable-type name) (aget a 'state) name index) a c))
                (new-type (type-eval '+ (get-type res) 1))
                (val (binop new-type '+ res 1))
                )
            (finalize-lemma a c (binop '&& (binop '>= index 0) (binop '< index (aget c 'array-variable-size name))))
            (cons-to-inner-list a (list 'precond) (binop '&& (binop '>= index 0) (binop '< index (aget c 'array-variable-size name))))
            (aset a 'state (av-set (aget c 'variable-type name) (aget a 'state) name index val))
            res)
)

(transformation axsem :concept |--.| :stages
    nil :do 
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) struct-array-element-access))
                (progn (to-stage 'arr)
                    (axsem (aget i 'index) a c))
                (progn (to-stage 'nonarray)
                    )))
    nonarray :do 
        (let* ((name (if (is-concept (aget i 'first) variable-name)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields)))))
                (res (actuate (sv-get (aget c 'variable-type name) (aget a 'state) name) a c))
                (new-type (type-eval '- (get-type res) 1))
                (val (binop new-type '- res 1)))
            (aset a 'state (sv-set  (aget c 'variable-type name) (aget a 'state) name val))
            (sv-get (aget c 'variable-type name) (aget a 'state) name))
    arr :do
        (let* ((index (actuate (aget a 'value)))  
                (name (if (is-concept (aget i 'first) array-element-access)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields)))))
                (res (actuate (av-get (aget c 'variable-type name) (aget a 'state) name index) a c))
                (new-type (type-eval '- (get-type res) 1))
                (val (binop new-type '- res 1)))
            (finalize-lemma a c (binop (true) '&& (binop (true) '>= index 0) (binop (true) '< index (aget c 'array-variable-size name))))
            (cons-to-inner-list a (list 'precond) (binop (true) '&& (binop (true) '>= index 0) (binop (true) '< index (aget c 'array-variable-size name))))
            (aset a 'state (av-set (aget c 'variable-type name) (aget a 'state) name index val))
            (av-get (aget c 'variable-type name) (aget a 'state) name index))
)

(transformation axsem :concept |.--| :stages
    nil :do 
        (if (is-concept (aget i 'first) 'enum-element-access)
            (progn (aset i 'stack nil)
                (error "Trying to set value for enum element access"))
            (if (or (is-concept (aget i 'first) array-element-access)
                    (is-concept (aget i 'first) struct-array-element-access))
                (progn (to-stage 'arr)
                    (axsem (aget i 'index) a c))
                (progn (to-stage 'nonarray)
                    )))
    nonarray :do 
        (let* ((name (if (is-concept (aget i 'first) variable-name)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields)))))
                (res (actuate (sv-get (aget c 'variable-type name) (aget a 'state) name) a c))
                (new-type (type-eval '- (get-type res) 1))
                (val (binop new-type '- res 1))
                )
            (aset a 'state (sv-set  (aget c 'variable-type name) (aget a 'state) name val))
            res)
    arr :do
        (let* ((index (actuate (aget a 'value))) 
                (name (if (is-concept (aget i 'first) array-element-access)
                        (map-name a c (aget i 'first 'name) t)
                        (mashup-symbol-list (cons (map-name a c (aget i 'first 'name) t) (aget i 'fields)))))
                (res (actuate (av-get (aget c 'variable-type name) (aget a 'state) name index) a c))
                (new-type (type-eval '- (get-type res) 1))
                (val (binop new-type '- res 1))
                )
            (finalize-lemma a c (binop '&& (binop '>= index 0) (binop '< index (aget c 'array-variable-size name))))
            (cons-to-inner-list a (list 'precond) (binop '&& (binop '>= index 0) (binop '< index (aget c 'array-variable-size name))))
            (aset a 'state (av-set (aget c 'variable-type name) (aget a 'state) name index val))
            res)
)


(defun activity-to-int (activity)
    (case (get-concept activity)
        ('active 1)
        ('inactive 3)
        ('rstop 5)
        ('nonstop 7)
        ('rerror 11)
        ('nonerror 13)))

(defun insert-proc-act (a process act)
    (let ((prev-act (aget a 'proc-act process))
        (if prev-act
            (case (* (activity-to-int prev-act) (activity-to-int act))
                ((3 5 11 35 55 143) nil)
                ((1 7 13 91) (progn (aset a 'proc-act process (active)) t))
                (9 (progn (aset a 'proc-act process (inactive)) t))
                ((15 39 25 65) (progn (aset a 'proc-act process (rstop)) t))
                (49 (progn (aset a 'proc-act process (nonstop)) t))
                ((21 33 121 77) (progn (aset a 'proc-act process (rerror)) t))
                (169 (progn (aset a 'proc-act process (nonerror)) t)))
            (progn (aset a 'proc-act process act)
                t)))))

(defun invert-activity (act)
    (case (get-concept act)
        ('active (inactive))
        ('inactive (active))
        ('rstop (nonstop))
        ('rerror (nonerror))))

(transformation axsem :concept process-state-checking :stages 
    nil :do (to-stage 'true) (to-stage 'false :agent (clone-agent a c))
    true :do 
        (if (insert-proc-act a (aget i 'process) (aget i 'activity))
            (true)
            (aset a 'stack nil))
    false :do 
        (if (insert-proc-act a (aget i 'process) (invert-activity (aget i 'activity)))
            (false)
            (aset a 'stack nil))
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

(transformation axsem :concept reset-time :stages 
    nil :do 
        (cons-to-inner-list a (list 'cur-cond) (reset))
)

(transformation axsem :concept set-state :stages 
    nil :do 
        (if (aget i 'state)
            (cons-to-inner-list a (list 'cur-cond) (ps-set (aget a 'current-process) (aget i 'state)))
            (cons-to-inner-list a (list 'cur-cond) (ps-set (aget a 'current-process) (next-process-state a c))))
)   

(transformation axsem :concept restart-process :stages 
    nil :do 
        (cons-to-inner-list a (list 'cur-cond) (ps-set (aget a 'current-process) (current-first-state a c)))
        (cons-to-inner-list a (list 'processes-to-start) (aget a 'current-process))
)


(transformation axsem :concept start-process :stages 
    nil :do 
        (let ((cur-proc (aget a 'current-process))
                (proc (aget i 'process)))
            (if (equal proc cur-proc)
                (axsem (restartp) a c)
                (progn 
                    (cons-to-inner-list a (list 'cur-cond) (ps-set proc (first-state c proc)))
	                (cons-to-inner-list a (list 'processes-to-start) proc))))
)

(transformation axsem :concept stop-current-process :stages 
    nil :do (cons-to-inner-list a (list 'cur-cond) (ps-set (aget a 'current-process) 'stop))
)

(transformation axsem :concept stop-process :stages 
    nil :do 
        (let ((cur-proc (aget a 'current-process))
                (proc (aget i 'process)))
            (if (equal proc cur-proc)
                (axsem (stop-cur) a c)
                (cons-to-inner-list a (list 'cur-cond) (ps-set proc 'stop))
                ))
)

(transformation axsem :concept error-current-process :stages 
    nil :do (cons-to-inner-list a (list 'cur-cond) (ps-set (aget a 'current-process) 'error))
)
(transformation axsem :concept error-process :stages 
    nil :do 
        (let ((cur-proc (aget a 'current-process))
                (proc (aget i 'process)))
            (if (equal proc cur-proc)
                (axsem (error-cur) a c)
                (cons-to-inner-list a (list 'cur-cond) (ps-set proc 'error))
                ))
)

(transformation axsem :concept if-then-else-statement :stages
;Разделяется ли 'value на два?
    nil :do 
    (let ((clone (clone-agent a c)))
        (to-stage 'true-condition) 
        (axsem (aget i 'condition) a c)
        (to-stage 'false-condition :agent clone)
        (axsem (aget i 'condition) clone c))
    true-condition :do 
        (let ((val (actuate (aget a 'value) a c)))
            (finalize-expression a)
            (clear-agent-expr a)
            (case (get-concept val)
                ('true (axsem (aget i 'then) a c))
                ('false (aset a 'stack nil))
                (otherwise (progn (cons-to-inner-list a (list 'cur-cond) val)
                            (axsem (aget i 'then) a c)))))
    false-condition :do 
        (let ((val (actuate (aget a 'value) a c)))
            (finalize-expression a)
            (clear-agent-expr a)
            (case (get-concept val)
                ('false (axsem (aget i 'else) a c))
                ('true (aset a 'stack nil))
                (otherwise (progn (cons-to-inner-list a (list 'cur-cond) (unop '!. val))
                            (axsem (aget i 'else) a c)))))
)

(transformation axsem :concept if-then-statement :stages 
    nil :do 
    (let ((clone (clone-agent a c)))
        (to-stage 'true-condition) 
        (axsem (aget i 'condition) a c)
        (to-stage 'false-condition :agent clone)
        (axsem (aget i 'condition) clone c))
    true-condition :do 
        (let ((val (actuate (aget a 'value) a c)))
            (finalize-expression a)
            (clear-agent-expr a)
            (case (get-concept val)
                ('true (axsem (aget i 'then) a c))
                ('false (aset a 'stack nil))
                (otherwise (progn (cons-to-inner-list a (list 'cur-cond) val)
                            (axsem (aget i 'then) a c)))))
    false-condition :do 
        (let ((val (actuate (aget a 'value) a c)))
            (finalize-expression a)
            (clear-agent-expr a)
            (case (get-concept val)
                ('false ())
                ('true (aset a 'stack nil))
                (otherwise (cons-to-inner-list a (list 'cur-cond) (unop '!. val)))))    
)


(transformation axsem :concept switch-statement :stages 
    nil :do (to-stage 'condition) (axsem (aget i 'controlling-expression) a c)
    condition :do 
        (let ((cases (aget i 'cases)))
            (if cases
                ()
                (progn 
                    (finalize-expression a)
                    (clear-agent-expr a)
                    (to-stage 'cases-label cases (actuate (aget a 'value) a c) 0 (length cases)))))
    (case-label cases cond index length) :do
        (if (< index length)
            (let ((clone (clone-agent a c c))) 
                (to-stage 'case-iter-true cases cond index length)
                (to-stage 'case-iter-true cases cond index length :agent clone)
                (axsem (aget (nth index cases) 'label) a c)
                (axsem (aget (nth index cases) 'label) clone c))
            (to-stage 'default))
    (cases-iter-true cases cond index length) :do
        (let ((label (actuate (aget a 'value) a c)))
            (cons-to-inner-list a (list 'cur-cond) (binop '== cond label))
            ;(finalize-expression a)
            (if (not (aget (nth index cases) 'break))
                (to-stage 'cont-case-iter cases (+ index 1) length))
            (axsem (nth index cases) a c))
    (cases-iter-false cases cond index length) :do
        (let ((label (actuate (aget a 'value) a c)))
            (cons-to-inner-list a (list 'cur-cond) (binop '!= cond label))
            (to-stage 'case-label cases cond (+ index 1) length))
    (cont-case-iter cases index length) :do
        (if (< index length)
            (progn (if (not (aget (nth index cases) 'break))
                    (to-stage 'cont-case-iter cases (+ index 1) length))
                (axsem (nth index cases) a c))
            (to-stage 'default))
    default :do 
        (let ((def (aget i 'default)))
            (if (not (null def))
                (axsem def a c)))
)

(transformation axsem :concept default-statement :stages
    nil :do (to-stage 'statement (aget i 'statements) 0 (length (aget i 'statements))))
    (statement sts index length) :do 
        (if (< index length)
            (progn (to-stage 'statement sts (+ index 1) length)
                (axsem (nth index sts) a c)))
(transformation axsem :concept case-statement :stages
    nil :do (to-stage 'statement (aget i 'statements) 0 (length (aget i 'statements))))
    (statement sts index length) :do 
        (if (< index length)
            (progn (to-stage 'statement sts (+ index 1) length)
                (axsem (nth index sts) a c)))


(transformation axsem :concept statement-block :stages
    nil :do (to-stage 'statement (aget i 'statements) 0 (length (aget i 'statements))))
    (statement sts index length) :do 
        (if (< index length)
            (progn (to-stage 'statement sts (+ index 1) length)
                (axsem (nth index sts) a c)))	

(transformation axsem :concept expression-statement :stages
    nil :do (axsem (aget i 'expression) a c) (finalize-expression a) (clear-agent-expr a)
)

(concept timeout-statement :constructor timeout :arguments (controlling-expression expression) (body :flatten (list statement)))

(transformation axsem :concept timeout-statement :stages
    nil :do (to-stage 'cond) (axsem (aget i 'controlling-expression) a c)
    cond :do 
        (let ((cond (actuate (aget a 'value)))
                (clone (clone-agent a c)))
            (to-stage 'body (aget i 'body) 0 (length (aget i 'body)) :agent clone)
            ;? создать с означенным тегом
            (cons-to-inner-list clone (list 'cur-cond) (ltime 'blank (aget a 'current-process)) cond :tags t)
            (cons-to-inner-list a (list 'cur-cond) (ltime 'blank (aget a 'current-process)) cond)
        )
    (body sts index length) :do
        (if (< index length)
            (axsem (nth sts index) a c))
)

(transformation axsem :concept wait :stages
    nil :do (axsem (aget i 'condition) a c))
(transformation axsem :concept slice :stages
    nil :do nil)
(transformation axsem :concept transition :stages
    nil :do (axsem (aget i 'condition) a c))

(transformation axsem :concept state-declaration :stages
    nil :do (aset a 'current-state (aget i 'name))
            (to-stage 'statements 
                (aget i 'body)
                (length (aget i 'body))
                a)
    (statements sts index length clear-agent) :do 
        (if (< index length)
            (progn (if (is-concept (nth sts index) 'barrier-statement) 
                    (to-stage 'barrier (nth sts index) index length clear-agent)
                    (to-stage 'statements sts (+ index 1) length clear-agent)
                (axsem (nth sts index) a c)))
        )
    (barrier sts index length clear-agent) :do 
        (case (get-concept (nth sts index))
            ('wait (let ((cond (actuate (aget a 'value)))
                        (clone (clone-agent a c))
                        (clear-clone1 (clone-agent clear-agent))
                        (clear-clone2 (clone-agent clear-agent)))

                    (cons-to-inner-list clone (list 'cur-cond) (unop '!. cond))
                    (to-stage 'nothing :agent clone)

                    (cons-to-inner-list a (list 'cur-cond) cond)
                    (to-stage 'statements sts (+ index 1) length clear-agent)

                    (cons-to-inner-list clear-clone1 (list 'cur-cond) (unop '!. cond))
                    (to-stage 'nothing :agent clear-clone1)
                    
                    (cons-to-inner-list clear-clone2 (list 'cur-cond) cond)
                    (to-stage 'statements sts (+ index 1) length clear-agent :agent clear-clone2)
                    )
            )
            ('slice (let ((clear-clone (clone-agent clear-agent)))
                    (to-stage 'nothing)
                    (to-stage 'statements sts (+ index 1) length clear-agent :agent clear-clone)
            ))
            ('transition (let ((cond (actuate (aget a 'value)))
                        (clear-clone1 (clone-agent clear-agent))
                        (clear-clone2 (clone-agent clear-agent)))

                    (to-stage 'nothing a)

                    (cons-to-inner-list clear-clone1 (list 'cur-cond) (unop '!. cond))
                    (to-stage 'nothing :agent clear-clone1)
                    
                    (cons-to-inner-list clear-clone2 (list 'cur-cond) cond)
                    (to-stage 'statements sts (+ index 1) length clear-agent :agent clear-clone2)
                    )))
    nothing :do nil
                
)

(transformation axsem :concept constant-declaration :stages
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

(transformation axsem :concept simple-variable-declaration :stages
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

(transformation axsem :concept array-variable-declaration :stages
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

(transformation axsem :concept imported-variable-declaration :stages
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

(transformation axsem :concept structure-declaration :stages
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

;?Запутался с агентами
(transformation axsem :concept process-declaration :stages
    nil :do 
        (aset a 'current-process (aget i 'name)) 
        (to-stage 'state (aget i 'states) 0 (length (aget i 'states)) a)
    (state states index length clear-agent) :do
        (if (< index length)
            (let ((clear-clone (clone-agent clear-agent)))
                (to-stage 'states (+ index 1) length clear-agent :agent clear-clone)
                (axsem (nth states index) clear-agent c))
            (to-stage 'stop clear-agent))
    (stop clear-agent) :do
        (to-stage 'error :agent (clone-agent clear-agent))
        (ps-comp 'blank (aget i 'name) 'stop)
    error :do
        (ps-comp 'blank (aget i 'name) 'stop)
)

;Добавить для enum-type трансляцию
(transformation axsem :concept structure-variable-declaration :stages
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

(transformation axsem :concept enum-declaration :stages
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

(transformation axsem :concept enum-variable-declaration :stages
    nil :do (to-stage 'first) 
        (if (aget i 'init) 
            (axsem (aget i 'init) a c) 
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

(transformation axsem :concept port-declaration :stages
    nil :do
    (let ((inputs (aget c 'input-ports)) (outputs (aget c 'output-ports))))
        (if (or (member inputs (aget i 'name)) (member outputs (aget i 'name))
            (progn (aset a 'stack nil)
                (error "Double port declaration"))
            (if (is-concept (aget i 'port-type) input)
                (aset c 'input-ports (cons (aget i 'name) inputs))
                (aset c 'output-ports (cons (aget i 'name) outputs)))))
)

(transformation axsem :concept clock :stages
    nil :do 
    (if (is-concept i 'time-constant)
        (axsem i a c)
        i)
)

(transformation axsem :concept program-declaration :stages
    nil :do (to-stage 'clock) (axsem (aget i 'clock))
    clock :do (to-stage 'declarations (aget i 'declarations) 0 (length (aget i 'declarations))) 
        (aset c 'clock (aget a 'value))
    (declarations declarations index length) :do
        (if (index <length)
            (progn (to-stage 'declarations declarations (+ index 1) length)
                (axsem (nth declarations index) a c))
            (to-stage 'processes-prep (aget i 'processes) 0 (length (aget i 'processes))))
    (processes-prep processes index length) :do 
        (if (< index length)
            (let ((process (nth processes index)))
                (to-stage 'processes-prep processes (+ index 1) length)
                (to-stage 'process-var-prep (aget process 'variables) 0 (length (aget process 'variables)))
                (aset c 'processes-state-names (mapcar (lambda (s) (aget s 'name)) (aget process 'states)))
            )
            (progn 
                (to-stage 'print-lemmas)
                (to-stage 'pre-work)
                (to-stage 'base-condition :agent (clone-agent a c))))
    (process-var-prep vars index length) :do 
        (if (< index length)
            (axsem (nth index vars) a c))
    (base-condition) :do 
        (to-stage 'base-conclude)
        (aset a 'processes-to-start 0 (aget i 'processes 0 'name))
        (to-stage to-stage 'init-started-proc (aget a 'processes-to-start) 0 (length (aget a 'processes-to-start)))
        (to-stage 'init-global-vars (aget i 'declarations) 0 (length (aget i 'declarations)))
    (init-global-vars declarations index length) :do 
        (if (< index length)
            (progn (to-stage 'init-global-vars declarations (+ index 1) length)
                (let ((var (nth declarationa index)))
                    (if (or (is-concept var simple-variable-declaration) (is-concept var 'array-variable-declaration) (is-concept var 'enum-variable-declaration))
                        (axsem-init var a c))))
        )
    (pre-work) :do
        (progn
            (init-input-vars (aget c 'input-variables) 0 (length (aget c 'input-variables)))
            (to-stage 'work (aget i 'processes) 0 (length (aget i 'processes))))
    (work procs index length) :do
        (if (< index length)
            (progn (to-stage 'work (+ index) length)
                (to-stage 'pre-init-started-proc)
                (axsem (nth procs index) a c))
            (to-stage 'conclude))

    (pre-init-started-proc) :do 
        (to-stage 'init-started-proc (aget a 'processes-to-start) 0 (length (aget a 'processes-to-start)))
    (init-started-proc procs index length) :do
        (if (< index length) 
            (progn (to-stage 'init-started-proc procs (+ index 1) length)
                (if (member (aget procs index 'name) (aget a 'processes-to-start))
                    (axsem-init (nth procs index) a c)))
            (aset a 'processes-to-start nil))
    (init-input-vars vars index length) :do
        (if (< index length)
                (let* ((name (map-name a c (nth vars index) t))
                        (rtype (aget c 'variable-type name)))
                    (to-stage 'init-input-vars vars (+ index 1) length)
                    (cons-to-inner-list a 'cur-cond (sv-set rtype 'blank name name)))
        )
    (base-conclude) :do
        (finalize-base-lemma a c)
    (conclude) :do
        (finalize-base-lemma a c)
        (to-stage 'print-lemmas)
    ;Как сделать нормальную печать
    (print-lemmas) :do
        (if (not (aget c 'is-printed))
            (progn (aset c 'is-printed)
                (to-stage 'print-l (aget c 'conditions) 0 (length (aget c 'conditions)))))
    (print-l lemmas index length) :do
        (if (< index length)
            (progn (aset c 'conditions-printed index)
                (aset c 'state-num 0)
                (aset c 'condition-num 0)
                (Isabelle-print (nth index lemmas length))))
)

(transformation axsem-init :concept simple-variable-declaration :stages
    nil :do (to-stage 'inited)
        (axsem (aget c 'variable-init (map-name a c (aget i 'name) t)) a c)
    inited :do 
        (let* ((name (map-name a c (aget i 'name) t))
                (rtype (aget c 'variable-type name)))
            (clear-agent-expr a)
            (cons-to-inner-list c (list 'cur-cond) (sv-set rtype 'blank name (aget a 'value))))
)

(transformation axsem-init :concept array-variable-declaration :stages
    nil :do 
    (let* ((name (map-name a c (aget i 'name) t))
            (rtype (aget c 'variable-type name)))
        (to-stage 'to-init name rtype (aget c 'variable-init name) 0 (length (aget c 'variable-init name))))
    (to-init name rtype arr index length) :do 
        (if (< index length)
            (progn (to-stage 'inited name arr index length)
                (axsem (aget arr index) a c)))
    (inited name rtype arr index length) :do 
        (to-stage 'to-init name rtype arr (+ index 1) length)
        (clear-agent-expr a)
        (cons-to-inner-list c (list 'cur-cond) (av-set rtype 'blank name index (aget a 'value)))
)

(concept struct-init (map fieled-name reflex-init))
(concept structure-variable-declaration :constructor struct-var-decl :arguments (name variable-name) (rtype structure-name) (init :opt struct-init))
(concept-by-union reflex-init simple-init array-init struct-init enum-element-access)

;?Требуется возможность получения всех пар ключ-значение списком 
(transformation axsem-init :concept structure-variable-declaration :stages 
    nil :do 
    (let ((name (map-name a c (aget i 'name) t)))
        (if (aget c 'variable-init name)
            (to-stage 'struct-init name nil (get-keys (aget c 'variable-init name)) 0 (length (get-keys(aget c 'variable-init name))))))
    (struct-init name collected key-names index length) :do
        (if (< index length)
            (let* ((key-name (nth key-names index))
                    (value (aget c 'variable-init name key-name)))
                (if (is-concept (second init) 'struct-init)
                    (progn (to-stage 'struct-init name collected key-names (+ index 1) length)
                        (to-stage 'struct-init name (cons collected key-name) (get-keys value) 0 (get-keys value)))
                    (if (is-concept (second init) 'simple-init)
                        (progn (to-stage 'simple-init name (cons collected key-name))
                            (axsem key-name a c))
                        (if (is-concept value 'simple-init)
                            (to-stage 'array-init name collected value 0 (length value)))
                            )))
        )
    (simple-init name collected) :do 
        (let* ((name (mashup-symbol-list (cons name (reverse collected))))
                (rtype (aget c 'variable-type name)))
            (clear-agent-expr a)
            (cons-to-inner-list c (list 'cur-cond) (sv-set rtype 'blank name (aget a 'value))))
    (array-init name collected arr index length) :do
        (if (< index length)
            (progn (to-stage 'array-init name collected arr (+ index 1) length)
                (to-stage 'array-init-set name collected index)
                (axsem (nth arr index) a c)))
    (array-init-set name collected index) :do
        (let* ((name (mashup-symbol-list (cons name (reverse collected))))
                (rtype (aget c 'variable-type name)))
            (clear-agent-expr a)
            (cons-to-inner-list c (list 'cur-cond) (av-set rtype 'blank name index (aget a 'value))))
)

(transformation axsem-init :concept enum-variable-declaration :stages
    nil :do (to-stage 'inited)
        (axsem (aget c 'variable-init (map-name a c (aget i 'name) t)) a c)
    inited :do 
        (clear-agent-expr a)
        (cons-to-inner-list c (list 'cur-cond) (sv-set rtype 'blank (map-name a c (aget i 'name) t) (aget a 'value)))
)

(transformation axsem-init :concept process-variables :stages
    nil :do (to-stage 'init-vars (aget i 'variables) 0 (length (aget i 'variables))))
    (init-vars vars index length) :do
        (if (< index length)
            (axsem-init (nth vars index) a c))

