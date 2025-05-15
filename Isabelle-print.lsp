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

(concept pstate-compare :constructor ps-comp (process process-name) (pstate state-name))

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

(defun create-state-name (num)
    (concatenate 'string "st" (string num)))

; У нас есть несколько concept-by-value на одно  
(transformation Isabelle-print :concept name :stages
    nil :do (concatenate 'string "\'\'" (string i) "\'\'"))

(transformation Isabelle-print :concept binary-operation :stages
    nil :do 
        (case (aget i 'op)
            ('&& (concatenate 'string  "(" (Isabelle-print (aget i 'left)) " \\<and> " (Isabelle-print (aget i 'left)) ")"))
            ('|| (concatenate 'string "(" (Isabelle-print (aget i 'left)) " \\<or> " (Isabelle-print (aget i 'left)) ")"))
            ('== (concatenate 'string "(" (Isabelle-print (aget i 'left)) " \\<eq> " (Isabelle-print (aget i 'left)) ")"))
            ('!= (concatenate 'string "(" (Isabelle-print (aget i 'left)) " = " (Isabelle-print (aget i 'left)) ")"))
            ('< (concatenate 'string "(" (Isabelle-print (aget i 'left)) " < " (Isabelle-print (aget i 'left)) ")"))
            ('<= (concatenate 'string "(" (Isabelle-print (aget i 'left)) " \\<le> " (Isabelle-print (aget i 'left)) ")"))
            ('> (concatenate 'string "(" (Isabelle-print (aget i 'left)) " > " (Isabelle-print (aget i 'left)) ")"))
            ('>= (concatenate 'string "(" (Isabelle-print (aget i 'left)) " \\<ge> " (Isabelle-print (aget i 'left)) ")"))
            ('+ (concatenate 'string "(" (Isabelle-print (aget i 'left)) " + " (Isabelle-print (aget i 'left)) ")"))
            ('- (concatenate 'string "(" (Isabelle-print (aget i 'left)) " - " (Isabelle-print (aget i 'left)) ")"))
            ('* (concatenate 'string "(" (Isabelle-print (aget i 'left)) " * " (Isabelle-print (aget i 'left)) ")"))
            ('/ (concatenate 'string "(" (Isabelle-print (aget i 'left)) " div " (Isabelle-print (aget i 'left)) ")"))
            ('% (concatenate 'string "(" (Isabelle-print (aget i 'left)) " mod " (Isabelle-print (aget i 'left)) ")"))
            ('& (concatenate 'string "(" (Isabelle-print (aget i 'left)) " bit& " (Isabelle-print (aget i 'left)) ")"))
            ('| (concatenate 'string "(" (Isabelle-print (aget i 'left)) " bit| " (Isabelle-print (aget i 'left)) ")"))
            ('^ (concatenate 'string "(" (Isabelle-print (aget i 'left)) " bit\\<oplus> " (Isabelle-print (aget i 'left)) ")"))
            ('<< (concatenate 'string "(" (Isabelle-print (aget i 'left)) " << " (Isabelle-print (aget i 'left)) ")"))
            ('>> (concatenate 'string "(" (Isabelle-print (aget i 'left)) " >> " (Isabelle-print (aget i 'left)) ")"))
        ))

;TODO bit inversion        
(transformation Isabelle-print :concept unary-operation :stages 
    nil :do 
        (case (aget i 'op)
            ('-. (concatenate 'string "(- " (Isabelle-print (aget i 'right)) ")"))
            ('!. (concatenate 'string "(\\<not> " (Isabelle-print (aget i 'right)) ")"))
            ('~. (concatenate 'string "( ~" (Isabelle-print (aget i 'right)) ")"))))

(transformation Isabelle-print :concept cast-operation :stages 
    nil :do 
        (case (get-concept (aget i 'type))
            ('integer-type (concatenate 'string "(int " (Isabelle-print (aget i 'term)) ")"))
            ('natural-type (concatenate 'string "(nat " (Isabelle-print (aget i 'term)) ")"))
            ('float-type (concatenate 'string "(real " (Isabelle-print (aget i 'term)) ")"))
            ('boolean-type (concatenate 'string "(bool " (Isabelle-print (aget i 'term)) ")"))))

(defun get-type-name (type)
    (case (get-type type)
        ('natural-type "Nat")
        ('integer-type "Int")
        ('boolean-type "Bool")
        ('float-type "Real")))

(transformation Isabelle-print :concept simple-value-getter :stages
    nil :do (to-stage 'state) (Isabelle-print (aget i 'state))     
    state :do (to-stage 'name (aget a 'value)) (Isabelle-print (aget i 'name))
    (name state) :do (concatenate 'string "(getVar" (get-type-name (aget i 'type)) " " state " " (aget a 'value)")"))
(transformation Isabelle-print :concept array-value-getter :stages
    nil :do (to-stage 'state) (Isabelle-print (aget i 'state))     
    state :do (to-stage 'name (aget a 'value)) (Isabelle-print (aget i 'index))
    (index state) :do (to-stage 'name state (aget a 'value)) (Isabelle-print (aget i 'name))
    (name state index) :do (concatenate 'string "(getArVar" (get-type-name (aget i 'type)) " " state " " (aget a 'value) " " index ")")
)
(transformation Isabelle-print :concept simple-value-setter :stages
    nil :do (to-stage 'state) (Isabelle-print (aget i 'state))     
    state :do (to-stage 'name (aget a 'value)) (Isabelle-print (aget i 'name))
    (name state) :do (to-stage 'value state (aget a 'value)) (Isabelle-print (aget i 'value))
    (value state name) :do (concatenate 'string "(setVar" (get-type-name (aget i 'type)) " " state " " name " " (aget a 'value)")")
)
(transformation Isabelle-print :concept array-value-setter :stages
    nil :do (to-stage 'state) (Isabelle-print (aget i 'state))     
    state :do (to-stage 'name (aget a 'value)) (Isabelle-print (aget i 'index))
    (index state) :do (to-stage 'name state (aget a 'value)) (Isabelle-print (aget i 'name))
    (name state index) :do (to-stage 'value state index (aget a 'value)) (Isabelle-print (aget i 'value))
    (value state index name) :do (concatenate 'string "(setArVar" (get-type-name (aget i 'type)) " " state " " name " " index " " (aget a 'value)")")
)

(transformation Isabelle-print :concept implication :stages
    nil :do (to-stage 'left) (Isabelle-print (aget i 'left))
    left :do (to-stage 'right (aget a 'value)) (Isabelle-print (aget i 'right))
    (right left) :do (concatenate 'string "(" left " \\<longrightarrow> " (aget a 'value) ")")
)

(transformation Isabelle-print :concept conjunction :stages
    nil :do 
        (to-stage 'formulas nil 0 (length (aget i 'formulas)))
        (Isabelle-print (aget i 'formulas 0))
    (formulas formula index length) :do
        (if (< index length)
            (let* ((value (aget a 'value))
                    new-formula ((if formula
                        (concatenate 'string formula "\\<and>" value)
                        value)))
                (to-stage 'formulas new-formula (+ index 1) length)
                (Isabelle-print (aget i 'formulas (+ index 1)))
            )
            formula)
)
(transformation Isabelle-print :concept disjunction :stages
    nil :do 
        (to-stage 'formulas nil 0 (length (aget i 'formulas)))
        (Isabelle-print (aget i 'formulas 0))
    (formulas formula index length) :do
        (if (< index length)
            (let* ((value (aget a 'value))
                    new-formula ((if formula
                        (concatenate 'string formula "\\<or>" value)
                        value)))
                (to-stage 'formulas new-formula (+ index 1) length)
                (Isabelle-print (aget i 'formulas (+ index 1)))
            )
            formula)
)

(transformation Isabelle-print :concept pstate-compare :stages
    nil :do (to-stage 'state) 
        (Isabelle-print (aget i 'state))   
    state :do (to-stage 'process (aget a 'value)) 
        (Isabelle-print (aget i 'process))
    (process state) :do (to-stage 'process state (aget a 'value)) 
        (Isabelle-print (aget i 'pstate))
    (process-state state process) :do
        (concatenate 'string "(getPstate " state " " process " = " (aget a 'value) ")")
)



(transformation Isabelle-print :concept program-state-name :stages
    nil :do (create-state-name (aget c 'state-num)))

(transformation Isabelle-print :concept forall :stages
    nil :do (to-stage 'formula) (Isabelle-print (aget i 'formula))
    formula :do 
        (concatenate 'string "(\\<forall> " (format nil "~{~A~^ ~}" (mapcar (lambda (x) (string x)) (aget i 'args))) ". " (aget a 'value) ")"))
(transformation Isabelle-print :concept exist :stages
    nil :do (to-stage 'formula) (Isabelle-print (aget i 'formula))
    formula :do 
        (concatenate 'string "(\\<exist> " (format nil "~{~A~^ ~}" (mapcar (lambda (x) (string x)) (aget i 'args))) ". " (aget a 'value) ")"))

(transformation Isabelle-print :concept reset :stages 
    nil :do (to-stage 'reset) (Isabelle-print (aget i 'formula))
    reset :do (concatenate 'string "(reset " (aget a 'value) ")")
)

(concept to-env :constructor to-env :arguments (state program-state))
(concept ltime-check :constructor ltime :arguments (state program-state) (process process-name) (compare-val term) :tags exceed)

(transformation Isabelle-print :concept to-env :stages
    nil :do (to-stage 'env) (Isabelle-print (aget i 'state))
    env :do (concatenate 'string "(toEnv " (aget a 'value)")"))

(transformation Isabelle-print :concept ltime-check :stages
    nil :do (to-stage 'env) (Isabelle-print (aget i 'state))
    state :do (to-stage 'process (aget a 'value)) (Isabelle-print (aget i 'process))
    process state :do (to-stage 'val state process) (Isabelle-print (aget i 'compare-val))
    val state process :do 
        (if (aget i 'exceed)
            (concatenate 'string "(ltime " state " " process " \\<ge>" (aget a 'value)")")
            (concatenate 'string "(ltime " state " " process " <" (aget a 'value)")"))
)   

(transformation Isabelle-print :concept inv-plug :stages 
    nil :do ()
)

(concept vc-lemma :constructor vc-lemma :argumets (precondition formula) (postcondition formula) (steps (list formula)))

(transformation Isabelle-print :concept vc-lemma :stages
    nil :do (to-stage 'precond) (Isabelle-print (aget i 'precondition))
    precond :do 
        (let* ((precond (concatenate 'string "base_inv: \"" (aget a 'value) "\""))
                (res (concatenate 'string "Theory Lemma" (string (aget c 'conditions-printed)) "\n"
                        "imports Reflex Reflex-patterns\n "
                        "lemma\n"
                        )))
            (to-stage 'main 
                (concatenate 'string res "assumes base_inv: \"" (aget a 'value) "\"")
                (aget i 'steps)
                0
                (length (aget i 'steps)))
            (Isabelle-print (aget i 'steps 0)))
    
    (main lemma steps index length) :do 
        (if (< index length)
            (let* ((step (aget a 'value)))
                (if (is-concept (aget i 'steps index) 'state-update)
                    (let* ((next-state (create-state-name (+ (aget c 'state-num) 1))) 
                            (completed-step (concatenate 'string "\tand " next-state ":\"" next-state " = " step "\""))
                            (new-lemma (concatenate 'string lemma "\n" completed-step)))
                        (aset c 'state-num (+ (aget c 'state-num) 1))
                        (to-stage new-lemma steps (+index 1) length))
                    (let* ((completed-step (concatenate 'string "\tand condition" (aget c 'condition-num) ":\"" step "\""))
                            (new-lemma (concatenate 'string lemma "\n" completed-step)))
                        (aset c 'condition-num (+ (aget c 'condition-num) 1))
                        (to-stage new-lemma steps (+index 1) length))
                )
                (Isabelle-print (aget i 'steps (+ index 1))))
            (progn (to-stage 'postcond lemma)
                (Isabelle-print (aget i 'post-condition))))
    (postcond lemma) :do 
        (let* ((postcond (aget a 'value))
                (res (concatenate 'string "\n shows " postcond)))
            (to-stage 'conclude res)
        )
    (conclude lemma) :do ;TODO print to folder
)
