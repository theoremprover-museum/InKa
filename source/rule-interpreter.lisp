;;;;; -*- Package: INKA; Syntax: Common-Lisp -*-

(in-package :inka)

;;;;;
;;;;; How to use this tool:
;;;;; =====================
;;;;;
;;;;;
;;;;; The *rules* are given as lisp-functions, which are defined by defrule instead of
;;;;; defun. This lisp-functions should be free of any side effects and internal memory.
;;;;; Hence, the result of such a lisp-function may only depend on the given parameters
;;;;; and not on any global values.
;;;;;
;;;;; This module differs between to kinds of datas.
;;;;; The first one are datas special to some applications which are not maintained by this module.
;;;;; The second one are data structures the functions to create, access some nested structure and replace
;;;;; some nested structures are known by the module (see above).
;;;;; All changes of these datastructures are protocolled and in case of failure of some rule all
;;;;; intermediate changes are undone.
;;;;;
;;;;;
;;;;; Declaration of rules:
;;;;; ---------------------
;;;;;
;;;;; *rules* are lisp-functions defined by defrule.
;;;;;
;;;;; The parameter list may obtain two additional keywords:
;;;;;
;;;;; - &others :      which seperated parameters which are maintained by this module and 
;;;;;                  datastructures which are maintained by some application. All parameters
;;;;;                  before this keyword (or in case of missing of the keyword: all parameters)
;;;;;                  are assumed to be maintained by this module.
;;;;;
;;;;;                  Notice, that there will be a Lisp-Error in case application-maintained 
;;;;;                          datastructures are assumed to be maintained by this module.
;;;;;
;;;;; The result of the rule determines the success or failure of the rule. The rule is considered
;;;;; to be failed iff the result is NIL. All intermediate changes of maintained datastructures are 
;;;;; undone. The history of a failed rule is removed from the protocol unless there was an call
;;;;; of an alternative computation (see:  ...) inside the computation of the rule. In that case the
;;;;; computation of the failed rule is protocoled. 



(defstruct (rl*object  (:CONC-NAME rl=OBJ.) (:PRINT-FUNCTION rl=OBJ.PRINT))

  CONTENT                                ; 
  TYPE
  top.object
  top.object.taf
  )


(defstruct (rl*mod (:conc-name rl=mod.) (:print-function rl=mod.print))

  object
  mod
  inverse.mod
  inverted
  information
  validation
  alternatives
  plans
  )


(defvar rl*modifications nil)


(defvar rl*level
  
  ;;; global variables for protocol use.

  0)


(defvar rl*prot.level -1)


(PROCLAIM '(TYPE FIXNUM rl*level rl*prot.level))


(defvar rl*actual.plan 

  ;;; stores the actual hierarchy of tasks

  nil)


(defvar rl*abort

  ;;; the global variables rl*abort and rl*break are used for interrupting the rule-interpreter.
  ;;; with the help of the macro rl-suspend one can set/reset rl*break. In case rl*break is T
  ;;; the call of any rule is interrupted and rl-break is called. Within rl-break the user may
  ;;; specify an arbitrary position in the rule-control-stack to with the interpreter backtracks
  ;;; with result nil.

  nil)


(defvar rl*break

  ;;; see: rl*abort

  nil)


(defstruct (rule (:conc-name rl=rule.))
  
  ;;; rl=rule is defstruct-object to maintain all neccessary informations of a given rule
  
  name                                  ; name of the rule
  module                                ; abbreviation of the module the rule belongs t
  depth                                 ; an integer denoting the "relevance" of the rule
  printing                              ; a flag which is T iff any call of the rule has to be protocolled
  long.inf                              ; a string containing an explanation of the semantic of the rule
  short.inf                             ; a format string which is printed in case of protocol
  no.of.par                             ; number of parameters of the rule
  no.of.obj                             ; number of parameters which are maintained by this module
  interrupt                             ; 
  )



#+(or CLTL2 DRAFT-ANSI-CL-2)
(defmethod make-load-form ((self rule) &optional environment)
	  (make-load-form-saving-slots self
                                       #-CMU17 :slots 
				       #+CMU17 :slot-names
				       '(name module depth printing long.inf short.inf no.of.par no.of.obj)
                                       :environment environment))


(defvar rl*rules.all

  ;;; rl*rules.all is an association list:
  ;;;        (module(1) . rule(1,1) ... rule(1,n(1)) ) ... (module(k) . rule(k,1) ... rule(k,n(k)) )
  ;;; of all rules sorted by their corresponding modules. rule(i,j) are instances of the defstruct `rule`.

  nil)


(defun rl=OBJ.PRINT (OBJECT STREAM DEPTH)
  
  (declare (ignore depth))
  (win-io.format STREAM "~D" (rl-object OBJECT)))



(defun rl=mod.PRINT (OBJECT STREAM DEPTH)
  
  (declare (ignore depth))
  (win-io.format STREAM "~D / ~D" (rl=mod.mod OBJECT) (rl=mod.inverse.mod OBJECT)))


(defun rl-prot.level.set (level)

  ;;; Input:  either the atom 'default' or a number
  ;;; Effect: sets the level of protocol to the input and in case of
  ;;;         default to 4.
  ;;; Value:  undefined.

  (declare (type fixnum level))
  (setq rl*prot.level (cond ((eq level 'default) -1)
			    (t level))))


(defmacro rl-prot.level ()

  ;;; Effect: see value
  ;;; Value:  returns the actual level of protocol.

  `rl*prot.level)


(defun rl-reset (prot.level)

  ;;; Input:  None
  ;;; Effect: initializes the rule interpreter and destroys all present informations
  ;;;         about any rule-calls.
  ;;; Value:  undefined

  (declare (type fixnum prot.level))
  (setq rl*level 0)
  (setq rl*modifications nil)                       ; no modifications done
  (setq rl*abort nil)
  (setq rl*actual.plan nil)
  (setq rl*prot.level prot.level)
  (setq rl*break nil))


(defmacro defrule (name arguments description &body body)

  ;;; Input:  an atom, a list of atoms, two list of strings and an s-expression
  ;;; Effect: defines a LISP-function with \verb$NAME$ and \verb$ARGUMENTS$ and \verb$BODY$ as the function-body
  ;;; Value : Undefined

  (multiple-value-bind (no.of.obj no.of.prot.args args) (rl=parse.arguments arguments)
    (let ((descr (rl=rule.define name description no.of.obj no.of.prot.args)))
      `(progn (defparameter ,name ,descr)
	      (defun ,name ,args
		(let ((modifications rl*modifications)
		      result)
		  (cond ((rl=break.entry? ,name))
			(t (rl=rule.insert)
			   (rl=protocol.rule.entry ,descr ,args)
			   (catch 'rl*abort
			     (setq result (progn ,@body)))
			   (rl=protocol.rule.exit result ,descr)
			   (rl=rule.remove result modifications)))
		  (rl=handle.possible.abort)
		  result))))))


;;;; functions to create and manipulate objects


(defun rl-object (object)

  ;;; Input:   a pointer to an \verb$RL=OBJECT$
  ;;; Effect:  see value
  ;;; Value:   returns the actual sexpression denoted by \verb$OBJECT$

  (case (rl=obj.type object)
    (gterm (car (rl=obj.content object)))
    (object (sel=object.gterm (rl=obj.content object)))
    (condition (sel-case.condition (rl=obj.content object)))
    (binding (car (rl=obj.content object)))))


(defmacro rl-with.problem (&rest args)

  ;;; Input:  a sequence of sexpressions and their type and finally a functional
  ;;; Effect: the sexpressions are introduced as rl-objects and the functional is
  ;;;         applied to it. The object- and history-stacks are reset after
  ;;;         the execution.
  ;;; Values: a multiple-value: for each sexpression a modification tree denoting all
  ;;;         changes which have been made during the execution of the functional.
  
  (let* ((body (car (last args))) (expressions (butlast args 1))
	 (arguments (smapcar #'(lambda (x) x) #'cddr expressions))
	 (types (smapcar #'(lambda (x) x) #'cddr (cdr expressions)))		    
	 (names (mapcar #'(lambda (x) (declare (ignore x)) (gensym)) arguments)))
    `(let ((modifications rl*modifications)
	   ,@(mapcar #'(lambda (name argument type)
			 `(,name (rl=object.create ,argument ,type nil nil)))
		     names arguments types))
       (catch 'rl*abort (funcall ,body ,@names))
       (multiple-value-prog1
	(values ,@(mapcar #'(lambda (name) 
			      `(rl=object.compute.manipulations ,name modifications))
			  names))
	(setq rl*modifications modifications)))))


(defmacro rl-with.objects (&rest args)

  ;;; Input:   a sequence of sexpressions and their type and finally a functional
  ;;; Effect:  the sexpressions are introduced as rl-objects and the functional is
  ;;;          applied to it. The object- and history-stacks are not (!) reset after
  ;;;          the execution.
  ;;; Value:   a multiple-value: for each sexpression a modification tree denoting all
  ;;;          changes which have been made during the execution of the functional.

  (let* ((body (car (last args))) (expressions (butlast args 1))
	 (arguments (smapcar #'(lambda (x) x) #'cddr expressions))
	 (types (smapcar #'(lambda (x) x) #'cddr (cdr expressions)))
	 (names (mapcar #'(lambda (x) (declare (ignore x)) (gensym)) arguments)))
  `(let ,(append `((modifications rl*modifications))
		 (mapcar #'(lambda (name argument type)
			     `(,name (rl=object.create ,argument ,type nil nil)))
			 names arguments types))
     (funcall ,body ,@names)
     (values ,@(mapcar #'(lambda (name) `(rl=object.compute.manipulations ,name modifications))
		       names)))))


(defmacro rl-with.sub.objects (&rest args)

  ;;; Input:   a sequence of sexpressions and their specifications of the substructure
  ;;;          and  a functional at the end.
  ;;; Effect:  the substructures of the sexpressions are introduced as rl-objects and the functional is
  ;;;          applied to it. The object- and history-stacks are not (!) reset after
  ;;;          the execution.
  ;;; Value:   the result of evaluation body

  (let* ((body (car (last args))) (expressions (butlast args 1))
	 (arguments (smapcar #'(lambda (x) x) #'cddr expressions))
	 (tafs (smapcar #'(lambda (x) x) #'cddr (cdr expressions))))
    `(funcall ,body
	      ,@(mapcar #'(lambda (argument taf)
			    `(rl=object.create nil nil ,argument ,taf))
			 arguments tafs))))


(defmacro rl-with.sub.problem (&rest args)

  ;;; Input:   a sequence of sexpressions and their specifications of the substructure
  ;;;          and  a functional at the end.
  ;;; Effect:  the substructures of the sexpressions are introduced as rl-objects and the functional is
  ;;;          applied to it. The object- and history-stacks are  reset after
  ;;;          the execution.
  ;;; Value:   a multiple-value: for each sexpression a modification tree denoting all
  ;;;          changes which have been made during the execution of the functional.

  (let* ((body (car (last args))) (expressions (butlast args 1))
	 (arguments (smapcar #'(lambda (x) x) #'cddr expressions))
	 (tafs (smapcar #'(lambda (x) x) #'cddr (cdr expressions)))
	 (names (mapcar #'(lambda (x) (declare (ignore x)) (gensym)) arguments)))
    `(let ,(append `((modifications rl*modifications))
		   (mapcar #'(lambda (name argument taf)
			       `(,name (rl=object.create nil nil ,argument ,taf t)))
			   names arguments tafs))
       (funcall ,body ,@names)
       (values ,@(mapcar #'(lambda (name) 
			     `(rl=object.compute.manipulations ,name modifications))
			 names)))))


(defun rl-object.change (object new.value &optional taf &rest modifier)

  ;;; Input:   two pointesr to an \verb$RL=OBJECT$, a specification of a sub-structure of \verb$OBJECT$
  ;;;          and a sexpression containing additional information.
  ;;; Effect:  changes the denoted substructure of \verb$OBJECT$ by \verb$NEW.OBJECT$.
  ;;; Value:   unchanged

  (cond ((eq (rl=obj.type object) 'condition)
	 (rl-object.changes object (list (list 'replace.top new.value)) nil modifier))
	((eq (rl=obj.type object) 'binding)
	 (rl-object.changes object (list (list 'replace.binding new.value)) nil modifier))
	(t (rl-object.changes object (list (list 'replace taf new.value)) nil modifier))))


(defun rl-object.changes (object modifications information validation)

  (cond ((neq object (rl=obj.top.object object))
	 (mapc #'(lambda (single.mod)
		   (cond ((neq (car single.mod) 'REPLACE.TOP)
			  (setf (second single.mod) 
				(append (second single.mod) (rl=obj.top.object.taf object))))))
	       modifications)
	 (setq object (rl=obj.top.object object))))
  (push (make-rl*mod :object object :mod modifications
		     :inverse.mod (rl=modification.inverse (rl-object object) modifications)
		     :information information :validation validation :inverted t
		     :plans rl*actual.plan)
	rl*modifications)
  (rl=modification.change (car rl*modifications)))



(defun rl=modification.inverse (content modification)

  ;;; Input:    modification is a list of either (REPLACE taf new.gterm) (COLOUR.UNTIL TAF TAFS KEY COLOUR)
  ;;;           (COLOUR.TOP TAF KEY COLOUR) (COLOUR.ALL TAF KEY COLOUR) or (REPLACE.TOP NEW.ENTRY)
  ;;; Effect:

  (mapcan #'(lambda (single.mod)
	      (case (car single.mod)
		    (REPLACE (list (list 'REPLACE (second single.mod) (da-access (second single.mod) content))))
		    (REPLACE.TOP (list (list 'REPLACE.TOP content)))
		    (REPLACE.BINDING (list (list 'REPLACE.BINDING content)))
		    (COLOUR.UNTIL (sel=gterm.colour.information (da-access (second single.mod) content)
								(fourth single.mod) (fifth single.mod)
								(mapcar #'(lambda (taf)
									    (append taf (second single.mod)))
									(third single.mod))
								(second single.mod)))
		    (COLOUR.TOP (LIST (LIST 'COLOUR.TOP (second single.mod) (third single.mod) 
					    (da-gterm.colour (da-access (second single.mod) content) 
							     (third single.mod)))))
		    (COLOUR.ALL (sel=gterm.colour.information (da-access (second single.mod) content)
							      (third single.mod)
							      (fourth single.mod) nil
							      (second single.mod)))))
	  (reverse modification)))


(defun rl=modification.change (modification)

  ;;; Input:    modification is a list of either (REPLACE taf new.gterm) (COLOUR.UNTIL TAF TAFS KEY COLOUR)
  ;;;           (COLOUR.TOP TAF KEY COLOUR) (COLOUR.ALL TAF KEY COLOUR) or (REPLACE.TOP NEW.ENTRY)

  (let* ((object (rl=mod.object modification))
	 (new.content (rl-object object)))
    (setq new.content (rl=modification.change.context new.content modification))
    (setf (rl=mod.inverted modification) (not (rl=mod.inverted modification)))
    (case (rl=obj.type object)
          (binding (setf (car (rl=obj.content object)) new.content))
	  (gterm (setf (car (rl=obj.content object)) new.content))
	  (object (setf (sel=object.gterm (rl=obj.content object)) new.content))
	  (condition (sel-case.replace.condition (rl=obj.content object) new.content)))))


(defun rl=modification.change.context (new.content modification &optional copy)

  ;;;  (COLOUR.UNTIL TAF TAFS KEY COLOUR)

  (mapc #'(lambda (single.mod)
	    (case (car single.mod)
		  (REPLACE (setq new.content (da-replace (second single.mod) new.content
							 (cond (copy (da-gterm.copy (third single.mod)))
							       (t (third single.mod))))))
		  (REPLACE.TOP (setq new.content (second single.mod)))
		  (REPLACE.BINDING (setq new.content (second single.mod)))
		  (COLOUR.UNTIL (da-gterm.colourize.until (da-access (second single.mod) new.content)
							  (third single.mod) (fifth single.mod) (fourth single.mod)))
		  (COLOUR.TOP (setf (da-gterm.colour (da-access (second single.mod) new.content)
						     (third single.mod))
				    (fourth single.mod)))
		  (COLOUR.ALL (da-gterm.colourize (da-access (second single.mod) new.content) 
						  (fourth single.mod) (third single.mod)))))
	(cond ((rl=mod.inverted modification) (rl=mod.mod modification))
	      (t (rl=mod.inverse.mod modification))))
  new.content)


(defun rl-object.top.object (object)

  ;;; Input:  a pointer to an \verb$RL=OBJECT$
  ;;; Value:  the top-level object and the sub-structure specification for \verb$OBJECT$ wrt the top-level object

  (values (rl=obj.top.object object)
	  (rl=obj.top.object.taf object)))


(defun rl=object.create (expression type upper.object upper.object.taf &optional top.level)

  ;;; Input:  a sexpression, an atom ...

  (cond ((null type) (setq type (rl=obj.type upper.object))
	 (cond ((and (eq type 'object) upper.object.taf) (setq type 'gterm)))))
  (let* ((content 
	  (case type
		(gterm (cond (expression (list expression))
			     ((null upper.object.taf) (rl=obj.content upper.object))
			     (t (nthcdr (1- (car upper.object.taf))
					(da-gterm.termlist (da-access (cdr upper.object.taf) 
								      (rl-object upper.object)))))))
		(object (cond (expression)
			      ((null upper.object.taf) (rl=obj.content upper.object))
			      (t (nthcdr (1- (car upper.object.taf))
					 (da-gterm.termlist 
					  (da-access (cdr upper.object.taf)
						     (sel=object.gterm (rl=obj.content upper.object))))))))
		(binding (list expression))
		(condition expression)))
	 (obj (make-rl*object :content content :type type
			      :top.object.taf (cond ((and (null top.level) upper.object)
						     (append upper.object.taf 
							    (rl=obj.top.object.taf upper.object)))))))
    (setf (rl=obj.top.object obj)
	  (cond ((and (null top.level) upper.object)
		 (rl-object.top.object upper.object))
		(t obj)))
    obj))


;;;; functions to add/remove a rule call in the ruler-caller-stack:


(defmacro rl=rule.insert ()
  
  ;;; Input:   a rule description and a list of arguments of the actual call
  ;;; Effect:  inserts rule-call into the stack
  ;;; Value:   undefined
  
  `(progn (incf rl*level)))


(defmacro rl=rule.remove (result modifications)
  
  ;;; Input:   a sexpression and two numbers denoting the stack adresses of the rule to be removed.
  ;;; Effect:  rule-call is removed from the stack. If result was nil all modifications during the
  ;;;          call are undone.
  ;;; Value:   undefined.

  `(progn (cond ((null ,result) (rl=rule.backtrack ,modifications)))
	  (decf rl*level)
	  ,result))


(defun rl=rule.backtrack (modifications)

  (let (failed.mods)
    (while (neq rl*modifications modifications)
      (rl=modification.change (car rl*modifications))
      (push (car rl*modifications) failed.mods)
      (pop rl*modifications))))


;;;;; functions to protocol entry and exit of a rule


(defmacro rl=protocol.rule.entry (description args)

  (let* ((long.inf (rl=rule.long.inf description))
	 (selected.args (mapcar #'(lambda (i)
				    (declare (type fixnum i))
				    (cond ((<= i (rl=rule.no.of.obj description)) `(rl-object ,(nth (1- i) args)))
					  (t (nth (1- i) args))))
				(cdr long.inf)))
	 (short.inf (rl=protocol.parse.short.inf (rl=rule.short.inf description) args)))
    `(progn (cond ((< ,(rl=rule.depth description) 4)
		   (push ,short.inf rl*actual.plan)))
	    (cond ((> rl*prot.level ,(rl=rule.depth description))
		   (win-io.format (WIN-WINDOW 'proof) (format nil "~~~D,0T" (min 30 (* rl*level 2))))
		   (win-io.format (win-window 'proof) ,(car long.inf) ,@selected.args)
		   (win-io.terpri (win-window 'proof)))))))


(defun rl=protocol.parse.short.inf (short.inf args)

  (cond (short.inf
	 (list 'list 
	       (car short.inf) 
	       (cons 'list (mapcar #'(lambda (i) (nth (1- i) args)) (second short.inf)))
	       (cond ((eq (third short.inf) 'col) 'sel*actual.colour)
		     ((numberp (third short.inf)) (nth (1- (third short.inf)) args)))
	       (cons 'list (mapcar #'(lambda (i)
				       `(copy-tree ,(nth (1- i) args)))
				   (fourth short.inf)))))))

	      

(defmacro rl=protocol.rule.exit (result description)

  (append (list 'progn)
	  (cond ((< (rl=rule.depth description) 4)
		 (list `(pop rl*actual.plan))))
	  (list `(cond ((and (null ,result)
			     (> rl*prot.level ,(rl=rule.depth description))
			     (win-io.format (WIN-WINDOW 'proof)
					    (format nil "~~~D,0Tfailed~%" (min 30 (* rl*level 2))))))))))

;;;;; functions to handle break and abort:


(defun rl-suspend (flag)
  
  ;;; Input:  T or nil
  ;;; Effect: sets the global variable which denotes whether the prover has to be interrupted or not.
  ;;; Value:  undefined
  
  (setq rl*break flag))


(defun rl=handle.possible.abort ()
  
  ;;; Input:  none
  ;;; Effect: if an abort of some rules is executed the target level is determined and
  ;;;         in case this level is not yet reached a throw to the next level is executed.
  ;;; Value : undefined
  
  (cond ((and rl*abort (< rl*abort rl*level))
	 (throw 'rl*abort nil))
	(t (setq rl*abort nil))))


(defun rl=break.entry? (description)
  
  ;;; Input:  a description of a rule
  ;;; Effect: if a break has to be executed the user-interface is activated.
  ;;; Value:  T if an abort has to be executed NIL else.
  
  (let (result)
    (cond ((or rl*break (rl=rule.interrupt description))
	     (setq result (sel-handle.interrupt rl*break))
	     (cond ((eq result t)
		    (setq rl*break nil)
		    nil)
		   (T (eval result)))))))


(defmacro rl-break.rule (description flag)

  ;;; Input:   a description of a rule and a boolean.
  ;;; Effect:  sets the interrupt-flag of the corresponding rule, i.e. each execution
  ;;;          of the denoted rule is interrupted and control is given to \verb$RL-BREAK$.
  ;;; Value:   undefined.
  
  `(setf (rl=rule.interrupt ,description) ,flag))



;;;;;;

(defun rl=parse.arguments (arguments)

  (declare (type list arguments))
  (let (no.of.objects no.of.prot.args)
    (setq no.of.objects (cond ((position '&others (remove '&no.protocol arguments)))
			      (t (length (remove '&no.protocol arguments)))))
    (setq no.of.prot.args (cond ((position '&no.protocol (remove '&others arguments)))
				(t (length (remove '&others arguments)))))
    (setq arguments (remove '&others (remove '&no.protocol arguments)))
    (values no.of.objects no.of.prot.args arguments)))



(defun rl=rule.define (name description no.of.obj no.of.par)

  (declare (type fixnum no.of.obj no.of.par))
  (multiple-value-bind (module depth long.inf short.inf) (values-list description)  
    (make-rule :name name
	       :module module
	       :depth depth
	       :printing nil
	       :long.inf long.inf
	       :short.inf short.inf
	       :no.of.par no.of.par
	       :no.of.obj no.of.obj)))


(defun rl=rule.print.alternative (name)
  
  (dotimes (i rl*level) (win-io.princ "| " (win-window 'proof)))
  (win-io.format (win-window 'proof) "to consider further:  ~A : " name)
  (win-io.terpri (win-window 'proof)))



(defun rl=object.compute.manipulations (object modifications)

  (let ((actual.mods rl*modifications) object.mods)
    (while (and actual.mods (neq actual.mods modifications))
      (cond ((eq object (rl=mod.object (car actual.mods)))
	     (push (car actual.mods) object.mods)
	     (rl=object.actualize.focus (car actual.mods) object)))
      (pop actual.mods))
    object.mods))


(defun rl=object.actualize.focus (mod object)

  (setf (rl=mod.plans mod)
	(mapcar #'(lambda (single.step)
		    (list (car single.step)
			  (mapcan #'(lambda (occ)
				      (cond ((eq (rl=obj.top.object occ) object)
					     (list (rl=obj.top.object.taf occ)))))
				  (second single.step))
			  (third single.step)
			  (fourth single.step)))
		(rl=mod.plans mod))))


(defun sel=gterm.colour.information (gterm solution colour tafs &optional taf)

  (multiple-value-bind (top.result other.result)
		       (sel=gterm.colour.information.1 gterm solution colour tafs taf nil)
    (nconc top.result other.result)))


(defun sel=gterm.colour.information.1 (gterm solution colour bottom.tafs &optional taf rel.taf)

  ;;;  (COLOUR.UNTIL TAF TAFS KEY COLOUR)
  
  (let* ((s.taf (da-taf.create.zero taf))
	 (new.colour (da-gterm.colour gterm solution))
	 top.results sub.results all.top.results all.sub.results tafs all.ignore.tafs ignore.tafs)
    (cond ((member taf bottom.tafs :test 'equal) (values nil nil (list rel.taf)))
	  ((eq colour new.colour)
	   (setq rel.taf (da-taf.create.zero rel.taf))
	   (mapc  #'(lambda (s.term)
		      (setq s.taf (da-taf.create.next s.taf))
		      (setq rel.taf (da-taf.create.next rel.taf))
		      (multiple-value-setq (top.results sub.results ignore.tafs)
			 (sel=gterm.colour.information.1 s.term solution new.colour bottom.tafs s.taf rel.taf))
		      (setq all.top.results (nconc top.results all.top.results) 
			    all.sub.results (nconc sub.results all.sub.results)
			    all.ignore.tafs (nconc ignore.tafs all.ignore.tafs)))
		  (da-gterm.termlist gterm))
	   (values all.top.results all.sub.results all.ignore.tafs))
	  (t (setq rel.taf (da-taf.create.zero nil))
	     (mapc  #'(lambda (s.term)
		      (setq s.taf (da-taf.create.next s.taf))
		      (setq rel.taf (da-taf.create.next rel.taf))
		      (multiple-value-setq (top.results sub.results ignore.tafs)
			 (sel=gterm.colour.information.1 s.term solution new.colour bottom.tafs s.taf rel.taf))
		      (setq all.top.results (nconc top.results all.top.results)
			    all.sub.results (nconc sub.results all.sub.results)
			    all.ignore.tafs (nconc ignore.tafs all.ignore.tafs)))
		  (da-gterm.termlist gterm))
	     (setq tafs (append (mapcar #'(lambda (result) (second result)) all.top.results) 
				all.ignore.tafs))
	     (values (list (list 'colour.until taf tafs solution new.colour))
		     (nconc all.top.results all.sub.results))))))