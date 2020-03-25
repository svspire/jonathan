(in-package :cl-user)
(defpackage jonathan.helper
  (:use :cl
        :jonathan.error
        :jonathan.util
        :jonathan.encode)
  (:import-from :babel
                :string-to-octets)
  (:import-from :fast-io
                :fast-write-sequence
                :make-output-buffer
                :finish-output-buffer)
  (:import-from :ppcre
                :scan)
  (:import-from :alexandria
                :length=
                :ensure-list
                :last-elt
                :starts-with-subseq)
  (:import-from :trivial-types
                :proper-list-p)
  (:export :with-output-to-string*
           :compile-encoder))
(in-package :jonathan.helper)

(defvar *compile-encoder-prefix* "jonathan-encoder")

;;; Copied from cl-annot;utils to remove that dependency

(defun macrop (symbol)
  "Return non-nil if SYMBOL is a macro."
  (and (symbolp symbol)
       (macro-function symbol)
       t))

(defun macroexpand-until-normal-form (form)
  "Expand FORM until it brecomes normal-form."
  (if (and (consp form)
           (macrop (car form))
           (let ((package (symbol-package (car form))))
             (and package
                  (member package
                          (list (find-package :cl)
                                #+clisp (find-package :clos))))))
      (values form nil)
      (multiple-value-bind (new-form expanded-p)
          (macroexpand-1 form)
        (if (or (not expanded-p) (null new-form))
            (values form nil)
            (values (macroexpand-until-normal-form new-form) t)))))

(defun progn-form-last (progn-form)
  "Return the last form of PROGN-FORM which should be evaluated at
last. If macro forms seen, the macro forms will be expanded using
MACROEXPAND-UNTIL-NORMAL-FORM."
  (let ((progn-form (macroexpand-until-normal-form progn-form)))
    (if (and (consp progn-form)
             (eq (car progn-form) 'progn))
        (progn-form-last (car (last progn-form)))
        progn-form)))

(defun progn-form-replace-last (last progn-form)
  "Replace the last form of PROGN-FORM with LAST. If LAST is a
function, the function will be called with the last form and used for
replacing. If macro forms seen, the macro forms will be expanded using
MACROEXPAND-UNTIL-NORMAL-FORM."
  (let ((progn-form (macroexpand-until-normal-form progn-form)))
    (if (and (consp progn-form)
             (eq (car progn-form) 'progn))
        `(,@(butlast progn-form)
            ,(progn-form-replace-last last (car (last progn-form))))
        (if (functionp last)
            (funcall last progn-form)
            last))))

;;; End of cl-annot stuff

(defmacro with-output-to-string* (&body body)
  "Output *stream* as string."
  `(with-output-to-string (stream)
     (with-output (stream)
       ,@body)))

(defun check-args (args)
  (let ((passed))
    (dolist (item args)
      (etypecase item
        (keyword (error "~s is a keyword, and cannot be used as a local variable." item))
        (symbol t)
        (t (error "Required argument is not a symbol: ~s" item)))
      (if (member item passed)
          (error "The variable ~s occurs more than once in the lambda list." item)
          (push item passed)))
    t))

(defun normalize-form (object)
  (flet ((unquote-when-comma (item)
           (if +impl-comma-p+
               (if (comma-p item)
                   (normalize-form (comma-expr item))
                   (if (or (keywordp item)
                           (stringp item))
                       item
                       (list 'quote item)))
               (error "Not supported.")))
         (make-quote (sym)
           (if (or (keywordp sym)
                   (stringp sym))
               sym
               (list 'quote sym)))
         (map-dotted-list (fn list)
           (loop for (item . rest) on list
                 collecting (funcall fn item)
                 when (not (consp rest))
                   collecting (funcall fn rest))))
    (if (consp object)
        (let ((sym-name (symbol-name (car object))))
          (cond
            ((or (equal sym-name "LIST")
                 (equal sym-name "LIST*"))
             (mapcar #'normalize-form object))
            ((equal sym-name "CONS")
             (cons 'list* (cdr object)))
            ((equal sym-name "QUOTE")
             (cond
               ((proper-list-p (cadr object))
                (cons 'list (mapcar #'make-quote (cadr object))))
               ((consp (cadr object))
                (cons 'list* (map-dotted-list #'make-quote (cadr object))))
               (t object)))
            ((equal sym-name "QUASIQUOTE")
             (cond
               ((proper-list-p (cadr object))
                (cons 'list (mapcar #'(lambda (item)
                                        (cond
                                          ((proper-list-p item)
                                           (normalize-form (list *quasiquote* item)))
                                          ((consp item)
                                           (cons 'list* (map-dotted-list #'unquote-when-comma item)))
                                          (t (unquote-when-comma item))))
                                    (cadr object))))
               ((consp (cadr object))
                (cons 'list* (map-dotted-list #'unquote-when-comma (cadr object))))
               (t object)))
            (t object)))
        object)))

(defun replace-form-with-placeholders (form)
  (let ((placeholders (make-hash-table :test #'equal)))
    (flet ((genstr () (symbol-name (gensym *compile-encoder-prefix*)))
           (swap (object placeholder)
             (setf (gethash placeholder placeholders) object)
             placeholder))
      (labels ((sub (object)
                 (etypecase object
                   (string object)
                   (keyword object)
                   (symbol (swap object (genstr)))
                   (cons (let ((sym-name (symbol-name (car object))))
                           (cond
                             ((equal sym-name "LIST*")
                              (cons 'list* (mapcar #'sub (cdr object))))
                             ((equal sym-name "LIST")
                              (cons 'list (mapcar #'sub (cdr object))))
                             ((equal sym-name "QUOTE")
                              object)
                             (t (swap object (genstr)))))))))
        (values (sub form) placeholders)))))

(defmacro compile-encoder ((&key octets from return-form) (&rest args) &body body)
  "Compile encoder."
  (check-args args)
  (let* ((main (last-elt body))
         (progn-p (and (consp main)
                       (eql (car main) 'progn))))
    (when progn-p
      (setq main (progn-form-last main)))
    (handler-case
        (multiple-value-bind (form placeholders) (replace-form-with-placeholders (normalize-form main))
          `(let* ((*from* ,from)
                  (result (list (with-output-to-string* (%to-json ,form)))))
             ,@(loop for key being the hash-keys of placeholders
                       using (hash-value val)
                     collecting `(setq result
                                       (loop for item in result
                                             for matched-p = nil
                                             when (stringp item)
                                               do (multiple-value-bind (start end)
                                                      (scan (with-output-to-string*
                                                              (%to-json ,key))
                                                            item)
                                                    (when (and start end)
                                                      (setq matched-p t)
                                                      (setq item
                                                            (list (subseq item 0 start)
                                                                  ',val
                                                                  (subseq item end)))))
                                             if matched-p
                                               nconc (ensure-list item)
                                             else
                                               collecting item)))
             (setq result (remove-if #'(lambda (item)
                                         (and (stringp item)
                                              (length= item 0)))
                                     result))
             (let ((form `(let ((*stream* ,(if ,octets
                                                `(make-output-buffer :output :vector)
                                                `(make-string-output-stream :element-type 'character)))
                                (*from* ,,from)
                                (*octets* ,,octets))
                            ,@(loop for item in result
                                    if (stringp item)
                                      collecting (if ,octets
                                                     `(fast-write-sequence ,(string-to-octets item) *stream*)
                                                     `(write-string ,item *stream*))
                                    else
                                      collecting `(%to-json ,item))
                            ,(if ,octets
                                 `(finish-output-buffer *stream*)
                                 `(get-output-stream-string *stream*)))))
               (when ,progn-p
                 (setq form (progn-form-replace-last form ',(last-elt body))))
               (setf (last-elt ',body) form)
               (if ,return-form
                   ',body
                   (eval `(lambda (,@',args) ,@',body))))))
      (<jonathan-not-supported-error> ()
        (if return-form
            `(list `(to-json (progn ,@',body) :from ,',from :octets ,',octets))
            `(lambda (,@args) (to-json (progn ,@body) :from ,from :octets ,octets)))))))

(define-compiler-macro to-json (&whole form args &key from octets)
  (handler-case
      `(progn
         ,@(eval
            `(compile-encoder (:from ,from :octets ,octets :return-form t) nil
               ,args)))
    (error () form)))
