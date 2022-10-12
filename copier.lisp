
(defconstant layer-inactive-state :inactive)

(defconstant layer-active-state :active)

(defmacro deflayer (layer-name &optional documentation)
  "Create a layer called LAYER-NAME, which must be a symbol."
  (check-type layer-name symbol)
  (check-type documentation (or null string))
  `(setf (get ',layer-name 'layer-documentation) ,documentation
         (get ',layer-name 'layer-p) t))

(eval-when (:compile-toplevel :load-toplevel :execute)

  (defun activeness-descriptor-p (thing)
    (or (handler-case
            (destructuring-bind (operation layer-name) thing
              (and (or (eq layer-active-state operation)
                       (eq layer-inactive-state operation))
                   (symbolp layer-name)
                   thing))
          (t () nil))
        (and (symbolp thing)
             `(,layer-active-state ,thing))))
  
  (defun standardize-activeness-descriptors (activeness-descriptors)
    (cond ((symbolp activeness-descriptors)
           `((,layer-active-state ,activeness-descriptors)))
          ((activeness-descriptor-p activeness-descriptors)
           (list activeness-descriptors))
          (t (let ((maybe-standardized-descriptors
                     (mapcar #'activeness-descriptor-p activeness-descriptors)))
               (if (every #'identity maybe-standardized-descriptors)
                   maybe-standardized-descriptors
                   (error "Unacceptable activeness-descriptors ~A"
                          activeness-descriptors)))))))

(defparameter *active-layers* '(t)
  "Active layer names")

(defun next-active-layers (std-activeness-desc
                              &optional (active-layers *active-layers*))
  "Compute next active layers based on `*active-layers*' and
STD-ACTIVENESS-DESC. See `standardize-activeness-descriptors' for more
information about the parameter."
  (loop :with next-layers := (reverse active-layers)
        :for desc :in std-activeness-desc :do
          (destructuring-bind (operation layer-name) desc
            (let ((clean-layers (remove layer-name next-layers)))
              (cond ((eq layer-active-state operation)
                     (push layer-name clean-layers))
                    ((not (eq layer-inactive-state operation))
                     (error "Unstandardized activeness descriptors: ~S"
                            std-activeness-desc)))
              (setf next-layers clean-layers)))
        :finally (return (reverse next-layers))))

(defmacro with (activeness-descriptors &body body)
  "Activate or inactivate layers described by ACTIVENESS-DESCRIPTORS,
which is in one of following forms:

- a layer-descriptor ;; Equal to a list which has only one
                     ;; layer-descriptor
- a list of layer-descriptor

where layer-descriptor is one of following form:

- symbol              ;; Equal to (:active symbol)
- (:active symbol)
- (:inactive symbol)

Macro `with' will standardize ACTIVENESS-DESCRIPTORS to a list of list like

  ((:active L1) (:active L2) (:inactive B1))

then activate or inactivate particular layers from left to
right. Specifically, for element (:active <layer>) <layer> will be
activated and for (:inactive <layer>) <layer> will be inactivate. As
for example above, the executive sequence is

1. activate L1
2. activate L2
3. inactivate B1

BODY will be executed under the activeness specified by
ACTIVENESS-DESCRIPTORS."
  (let ((descs (standardize-activeness-descriptors activeness-descriptors)))
    `(let ((*active-layers* (next-active-layers ',descs)))
       ,@body)))

(defun resolve-functions (available-functions
                          &optional (active-layers *active-layers*))
  "Given ACTIVE-LAYERS, trim unrelated functions and sort functions by
order of its corresponding layer in ACTIVE-LAYERS. AVAILABLE-FUNCTIONS
is a `alist' whose first element is a name of layer and second element
is a function object. Return a `alist' in the same form with
AVAILABLE-FUNCTIONS."
  (let ((order-table (make-hash-table :test #'eq)))
    (loop :for layer :in active-layers :for i :from 0 :do
      (setf (gethash layer order-table) i))
    (sort (loop :for cell :in available-functions
                :if (gethash (car cell) order-table)
                  :collecting cell)
          #'< :key (lambda (cell) (gethash (car cell) order-table)))))

(defun apply-with-context (function-symbol &rest arguments)
  "Apply functions restored in property `layered-functions' of
FUNCTION-SYMBOL by ARGUMENTS, in context of `*active-layers*'."
  (let* ((args (and arguments (apply #'list* arguments)))
         (available-functions (get function-symbol 'layered-functions))
         (function-cells (resolve-functions available-functions))
         (functions (mapcar #'cdr function-cells)))
    (loop :for fn :in functions
          :collecting (apply fn args))))

(defun remove* (element list &key (key #'identity) (test #'eql))
  "Like standard function `remove' except only operating on `list'
and returning second value to indicate whether the invocation removed
item actually."
  (loop :with removed-p := nil
        :for e :in list
        :if (funcall test element (funcall key e))
          :do (setf removed-p t)
        :else
          :collecting e :into clean-list
        :finally (return (values clean-list removed-p))))

(defun install-layered-function (function-symbol layer function
                                 &optional force-p)
  "Install a layered function named FUNCTION-SYMBOL in LAYER with
FUNCTION. A warning will be raised if there is a function in LAYER
called FUNCTION-SYMBOL. Pass FORCE-P as `t' to prevent it."
  (let ((current-functions (get function-symbol 'layered-functions)))
    (multiple-value-bind (clean-functions removed-p)
        (remove* layer current-functions :key #'car :test #'eq)
      (when (and (not force-p) removed-p)
        (warn "Function ~A in layer ~A has been defined" function-symbol layer))
      (setf (get function-symbol 'layered-functions)
            (cons (cons layer function)
                  clean-functions)))))

(defun install-layered-function-combiner (function-symbol function
                                          &optional force-p)
  "Install a combiner for FUNCTION-SYMBOL as FUNCTION. A warning will
be raised if there exists a combiner. Pass FORCE-P as `t' to prevent
it."
  (when (and (not force-p) (get function-symbol 'layered-functions-combiner))
    (warn "Redefined layered function combiner of ~A" function-symbol))
  (setf (get function-symbol 'layered-functions-combiner)
        function))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun tagged-list-p (lst)
    "If LST is a `list' which has at least one element, return the
first element. `nil' otherwise."
    (handler-case (destructuring-bind (tag &rest _) lst
                    (declare (ignore _))
                    tag)
      (t () nil)))

  (defun extract-variables-from-lambda-list (lambda-list)
    "Extract variables from LAMBDA-LIST, which is a ordinary lambda
list. Return a property list, which has four properties:

1. :required Positional arguments (List of symbol)
2. :key      Keyword arguments (List of symbol)
3. :rest     Rest argument (Symbol)
4. :optional Optional argument (Symbol)"
    )

  (defun create-layered-lambda (name lambda-list)
    "Create source code of layered function."
    (declare (ignore lambda-list))
    `(lambda (&rest arguments)
       (let ((combiner (get ',name 'layered-functions-combiner))
             (result (apply-with-context ',name arguments)))
         (if combiner
             (funcall combiner result)
             result))))

  (defun deflun-aux (name lambda-list clauses)
    "Define layered functions named NAME with LAMBDA-LIST. CLAUSES is
any number of forms which has one of following structures:

  1. (:in-layer <layer-name>
       <function-body>)

  2. (:finally (<variable-name>)
       <result-producer>)

  3. (:documentation <doc-string>)

every clause (1.) defines a function in layer <layer-name>, and all of them
in CLAUSES has the same signature (NAME . LAMBDA-LIST).

Although `deflun-aux' can be called in several times, clause two and
three should only appear once, or otherwise a warning will be
signaled. (2.)  clause define a combinator of the layered
function. Since a single invocation of a layered function may yield
many returning value corresponding to activated layers, the default is
every returning value will be returned as a `list'. You can modify
this behavior by adding a combinator or collector in the second type
of clause: <variable-name> will be bound to the resulting list and
<result-producer> yield the real result.

The third documentation clause is a equivalent of docstring of `defun'."
    (loop :for clause :in clauses
          :for tag := (tagged-list-p clause)
          :if (not tag)
            :do (error "Invalid clause for `deflun': ~S" clause)
          :else
            :collecting
            (ecase tag
              ((:in-layer in-layer)
                  (destructuring-bind (_ layer &body body) clause
                    (declare (ignore _))
                    `(install-layered-function ',name ',layer
                                               (lambda ,lambda-list ,@body))))
              ((:documentation note-that)
               (destructuring-bind (_ docstring) clause
                 (declare (ignore _))
                 `(progn (when (documentation ',name 'function)
                           (warn "Redefined documentation of ~A" ',name))
                         (setf (documentation ',name 'function) ,docstring))))
              ((:finally finally)
                  (destructuring-bind (_ result-name &body body) clause
                    (declare (ignore _))
                    `(install-layered-function-combiner
                      ',name
                      (lambda ,result-name ,@body)))))
            :into transformed-clauses
          :finally
             (return
               `(progn ,@transformed-clauses
                       (setf (symbol-function ',name)
                             ,(create-layered-lambda name lambda-list)))))))

(defmacro deflun (name lambda-list &body clauses)
  (deflun-aux name lambda-list clauses))

(defmacro in-layer (name &body body)
  "Create a function in layer NAME. This macro must be invoked in
context of `deflun'."
  (declare (ignore name body))
  (error "`in-layer' must be called in context of `defun'"))

(defmacro finally ((result) &body body)
  "Create a combiner of functions in all layers. This macro must be
invoked in context of `deflun'."
  (declare (ignore result body))
  (error "`fianlly' must be called in context of `defun'"))

(defmacro note-that (string)
  "Create documentation for current function. This macro must be
invoked in context of `deflun'"
  (declare (ignore string))
  (error "`note' must be called in context of `deflun'"))

(defstruct person name email age)

(deflun detail (person)
  (in-layer t
    (format nil "Name: ~A" (person-name person)))
  (in-layer email
    (format nil "; Email: ~A" (person-email person)))
  (in-layer age
    (format nil "; Age: ~A" (person-age person)))
  (finally (result)
    (apply #'concatenate 'string result))
  (note-that "This is a function"))
