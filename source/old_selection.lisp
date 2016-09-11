;;; -*- Package: INKA; Mode: LISP -*-
;;; $Header: /home/inka/system-4-1/source/RCS/selection.lisp,v 1.11 2000/03/24 13:26:05 hutter Exp hutter $

(IN-PACKAGE :INKA)

(defvar sel*case.actual

  ;;; the actual case which is tried to be proved.

  nil)


(defvar sel*case.condition

  ;;; this variable is used to store the condition of the actual case.

  nil)


(defvar sel*suspend

  ;;; this variable is t if a request to interrupt the proof-process is given

  nil)


(defvar sel*active.proof

  ;;; this variable is T, if a proof attempt is running

  nil)


(defvar sel*actual.colour 'equality)


(defvar sel*failed.lemma.cache

  ;;; this variable is a list of failed litera;s to be established since the last
  ;;; change of the active database

  nil)


(defvar sel*constrains

  ;;; the constrains for applying any modifiers

  (list 'var.restrictions t))


(defvar sel*refutation.depth

  ;;; number of the actual recursive calls of the prover in order to prove
  ;;; conditions of an equation or implication

  0)


(defvar sel*variables

  ;;; list of variables which are regarded as constants

  nil)


(defvar sel*pred.symbols

  ;;; list of predicate and function symbols which occur in the formula to be proven

  nil)


(defvar sel*choice nil)


(defvar sel*eq.bindings nil)

(defvar sel*no.stored 0)

(defvar sel*stored nil)

(defvar sel*stored.proof nil)

(defvar sel*eq.colours 0)



;;;;;=========================================================================================================
;;;;;
;;;;;  Chapter 1
;;;;;  ---------
;;;;;
;;;;;  Definition of the abstract datatypes.
;;;;;
;;;;;=========================================================================================================


(DEFSTRUCT (SEL*OBJECT (:CONC-NAME SEL=OBJECT.) (:PRINT-FUNCTION SEL=OBJECT.PRINT))

  GTERM                                 ; the denoted gterm
  SUCCS                                 ; the edges to the following objects
  STATUS                                ; \verb$SKETCH$, \verb$SKETCH.PROP$, \verb$CONNECTED$, \verb$CONNECTED.PROP$,
					; \verb$CONNECTED.FIRST$, \verb$SOLVED$
  TYPE                                  ; \verb$SIMPLIFICATION$, \verb$INDUCTION$, \verb$RESOLUTION$, 
                                        ;                        \verb$RESOLUTION.SET$ ...
  HINTS                                 ; in case of induction the information of the predecessors
  EDGE                                  ; the edge to the previous object
  SUBSTS                                ; a list of substitutitions each of them representing an instance of the original
                                        ; goal which could be refuted
  ATTRIBUTES                            ; a property-list
  PREV.OBJECT                           ; pointer to the object which has the current object as one of its successor-node.
  )


(DEFSTRUCT (SEL*EDGE (:CONC-NAME SEL=EDGE.) (:PRINT-FUNCTION sel=edge.print))

  TYPE
  SUCC.OBJECT               ; the ending point of the edge
  MODIFICATION              ; the modifications to be done on the previous object to apply the edge
  STATUS
  MODIFIER                  ; either a modifier, a gterm or an atom
  TAF                       ; the term-access-function the modifier is applied to the object.
  INPUT.SUBST               ; the substitution applied to object
  )


(DEFSTRUCT (SEL*CASE (:CONC-NAME SEL=CASE.) (:PRINT-FUNCTION sel=case.print))

  TYPE
  STATUS
  NAME
  SUB.CASES                   ; a list of cases replacing the original case
  PREV.CASE                   ; the case causing this case
  PROOF                       ; a proof graph
  INSTANCES                   ; a suggested instantiation of the all-quantified variables
  CONDITION                   ; a list of clauses denoting the simplified case conditions
  INFORMATION                 ; additional informations about this case (a list of strings)
  )




(DEFUN SEL-THEOREM.PROVE (THEOREM &OPTIONAL QUIET FILE)

  ;;; Input:   a formula, a boolean flag and a pathname
  ;;; Effect:  tries to prove \verb$THEOREM$ wrt the actual database. In case
  ;;;          \verb$QUIET$ is T no protocol is printed to the terminal and no
  ;;;          graphical representation of the proof (attempt) is given.
  ;;;          In case the proof was successful, \verb$THEOREM$ is added in the
  ;;;          list of proved  formulas of the actual deduction problem.
  ;;;          In case \verb$FILE$ is specified the proof of \verb$THEOREM$ is
  ;;;          stored under this pathname.
  ;;; Value:   T, in case a proof was found or \verb$THEOREM$ has been proved
  ;;;          within the same deduction problem before.

  (COND ((SOME #'(LAMBDA (AXIOM)
		   (OR (UNI-GTERM.ARE.EQUAL AXIOM THEOREM)
		       (UNI-GTERM.MATCH THEOREM AXIOM)))
	       (DED-INPUT.AXIOMS))
	 T)
	(T (LET (OK?)
	     (rl-reset (cond (quiet -1) (t (rl-prot.level))))
	     (MULTIPLE-VALUE-SETQ (OK? FILE) (SEL=THEOREM.PROVE THEOREM QUIET FILE))
	     (cond (ok? (DED-INPUT.AXIOMS.INSERT (DA-GTERM.COPY THEOREM) FILE)
			T))))))


(DEFUN SEL=THEOREM.PROVE (THEOREM QUIET FILE)

  ;;; Input:  a formula, a boolean flag and a pathname
  ;;; Effect: tries to prove \verb$THEOREM$ wrt the actual database. In case
  ;;;          \verb$QUIET$ is T no protocol is printed to the terminal and no
  ;;;          graphical representation of the proof (attempt) is given.
  ;;;          In case \verb$FILE$ is specified the proof of \verb$THEOREM$ is
  ;;;          stored under this pathname.
  ;;; Value:   a multiple value: the first value is T iff \verb$THEOREM$ has been
  ;;;          proved. The second value is the actual filename of the stored
  ;;;          proof (it is stored at all).

  (let ((neg.theorem (NORM-NORMALIZATION (DA-FORMULA.NEGATE (da-gterm.copy THEOREM))))
	(sel*refutation.depth 0) (SEL*SUSPEND NIL)
	(SEL*VARIABLES NIL) (sel*active.proof NIL) (sel*case.actual nil)
	(sel*failed.lemma.cache nil)
	(sel*constrains (list 'var.restrictions t))
	(sel*actual.colour 'equality)
	printed case time)
    (setq case (make-sel*case :proof (make-sel*object :gterm neg.theorem
						      :type 'simplification
						      :substs (list nil)
						      :status 'connected)
			      :status 'initial
			      :condition nil
			      :name "Top level case"
			      :prev.case nil))
    (win-io.print.status (win-window 'main) "Proving ...")
    (with-simple-restart (sel-top "Abort the automatic proof")
			 (catch 'sel*end.of.proof (setq time (sel=handle.cases case))))
    (setq printed (PR-PRINT.FORMULA THEOREM))
    (COND ((not QUIET)
	   (cond (time (win-io.print.status (win-window 'main) (format nil "time spent: ~F sec" time))))
	   (pr-graphic.interact 
	    (win-window 'description_1)
	    `(sel=pr.case (quote ,case)
			  (quote ,(FORMAT NIL "Proving  ~A"
					  (SUBSEQ (CAR PRINTED) 0
						  (MIN (LENGTH (CAR (PR-PRINT.FORMULA THEOREM))) 100))))))))
    (cond ((or file (setq file (edt-proof.save.file)))
	   (sel=case.store case file)
	   (edt-save.proof.finished)))
    (values (sel=case.is.proved case) file)))


(DEFUN SEL-SUSPEND (FLAG)

  ;;; Input:   a flag
  ;;; Effect:  sets the global interrupt signal
  ;;; Value:   undefined

  (SETQ SEL*SUSPEND FLAG))


(DEFUN SEL-HANDLE.INTERRUPT (FLAG)

  ;;; Input:  a flag
  ;;; Effect: aborts the rule-interpreter and stops the proof-attempt
  ;;; Value:  undefined

  (SEL-SUSPEND NIL)
  (rl-suspend nil)
  (cond ((null sel*active.proof) nil)
	((eq flag 'no.questions) `(progn (rl-reset (rl-prot.level)) (throw 'sel*end.of.proof 'aborted)))
	(t (CASE (CAR (WIN-MN.choose (WIN-WINDOW 'DESCRIPTION_1) 
				     (LIST (CONS "Abort automatic proof" 1)
					   (CONS "Continue proof" 2))))
		 (1 `(progn (rl-reset (rl-prot.level)) (throw 'sel*end.of.proof 'aborted)))
		 (OTHERWISE NIL)))))



(DEFUN SEL-PROOF.EXAMINE (FILE)

  ;;; Input:   a file (in which a proof is stored)
  ;;; Effect:  displays graphically the stored proof.
  ;;; Value:   undefined.

  (COND ((PROBE-FILE FILE)
	 (LOAD FILE)
	 (PR-GRAPHIC.SHOW (WIN-WINDOW 'DESCRIPTION_1)
			  `(sel=pr.case (quote ,sel*stored.proof)
					(quote ,(FORMAT NIL "Examining Proof")))))))


(DEFUN sel-GTERM.simplify (gterm subst)
  
  (let ((new.gterm gterm) old.gterm)
    (while (not (uni-gterm.are.equal new.gterm old.gterm))
      (setq old.gterm new.gterm)
      (multiple-value-setq (new.gterm subst) 
			   (sel=gterm.simplify.by.internal.equations (da-gterm.copy new.gterm) subst))
      (setq new.gterm
	    (EG-EVAL 
	     (SEL=GTERM.EVALUATE.ground.LITERALS.WITH.COMPLEX.ARGUMENTS (EG-EVAL new.gterm)))))
    (values new.gterm subst)))


;;;;;=========================================================================================================
;;;;;
;;;;;  Chapter 2
;;;;;  ---------
;;;;;
;;;;;  Handling cases
;;;;;
;;;;;=========================================================================================================


(defun sel-case.condition (case)

  ;;; Input:  an object of type \verb$SEL*CASE$
  ;;; Effect: see value
  ;;; Value:  returns the conditions of \verb$CASE$, i.e. a list of gterms
  
  (sel=case.condition case))


(defun sel-case.replace.condition (case new.conditions)

  ;;; Input:  an object of type \verb$SEL*CASE$ and a list of gterms
  ;;; Effect: replaces the conditions of \verb$CASE$ by \verb$new.conditions$
  ;;; Value:  undefined.
  
  (mapc #'(lambda (gterm) (db-gterm.delete gterm)) (set-difference (sel=case.condition case) new.conditions))
  (mapc #'(lambda (gterm) (db-gterm.insert gterm 'theorem)) 
	(set-difference new.conditions (sel=case.condition case)))
  (setf (sel=case.condition case) new.conditions))


(defun sel=case.all.cases (case)

  ;;; Input:  an object of type \verb$SEL*CASE$
  ;;; Value:  a list of all leafs of the case tree

  (cond ((sel=case.sub.cases case)
	 (mapcan #'(lambda (sub.case)
		     (sel=case.all.cases sub.case))
		 (sel=case.sub.cases case)))
	(t (list case))))


(defun sel=handle.cases (top.case)

  ;;; Input:   an object of type \verb$SEL*CASE$
  ;;; Effect:  tries to prove \verb$TOP.CASE$.
  ;;; Value:   undefined.

  (let (case (time (get-internal-run-time)) (sel*active.proof t))
    (while (setq case (sel=find.untackled.case top.case))
      (sel=with.active.case case (sel=case.handle)))
    (/ (- (get-internal-run-time) time) internal-time-units-per-second)))


(defun sel=find.untackled.case (case)

  ;;; Input:   an object of type \verb$SEL*CASE$
  ;;; Effect:  searches for the first (sub)case of \verb$CASE$ which which
  ;;;          has not been tackled before, i.e. with state = \verb$INITIAL$.
  ;;; Value:   a case with this attribute or NIL.

  (cond ((sel=case.sub.cases case)
	 (some #'(lambda (sub.case)
		   (sel=find.untackled.case sub.case))
	       (sel=case.sub.cases case)))
	((eq 'initial (sel=case.status case)) case)))


(defmacro sel=with.active.case (case &rest body)

  `(let ((actual.case ,case) (sel*case.actual ,case))
     (unwind-protect (progn (mapc #'(lambda (gterm)
				      (setf (getf (da-gterm.attributes gterm) 'kind) 'theorem)
				      (db-gterm.insert gterm 'theorem))
				  (sel=case.condition actual.case))
			    (setq sel*failed.lemma.cache nil)
			    (progn ,@body))
       (progn (mapc #'(lambda (gterm)
			(setf (getf (da-gterm.attributes gterm) 'kind) nil)
			(db-gterm.delete gterm))
		    (sel=case.condition sel*case.actual))))))



(defun sel=case.handle ()

  (cond ((and (neq 'induction.step (sel=case.type sel*case.actual)) (sel=generalize.case sel*case.actual)))
	((sel=refute (sel=case.proof sel*case.actual))
	 (setf (sel=case.status sel*case.actual) 'finished))
	((sel=generalize.case sel*case.actual))
	((and (neq 'induction.step (sel=case.type sel*case.actual)) (sel=case.split.by.induction sel*case.actual)))
	(t (setf (sel=case.status sel*case.actual) 'finished))))



(defun sel=case.has.advanced (case old.case)

  (let* ((gterm (sel=object.gterm.compute (sel=object.simplified.formula (sel=case.proof case))))
	 (old.gterm (sel=object.gterm.compute (sel=object.simplified.formula (sel=case.proof old.case))))
	 (symbols (da-prefun.independent.symbols (da-gterm.prefuns gterm)))
	 (old.symbols (da-prefun.independent.symbols (da-gterm.prefuns old.gterm)))
	 (skolems (da-gterm.functions gterm 'skolem))
	 (old.skolems (da-gterm.functions old.gterm 'skolem)))
    (and (every #'(lambda (symbol) 
		    (or (member symbol old.symbols)
			(not (da-prefun.is.independent symbol old.symbols))))
		symbols)
	 (or (some #'(lambda (symbol) (da-prefun.is.independent symbol symbols)) old.symbols)
	     (and (set-difference old.skolems skolems)
		  (null (set-difference skolems old.skolems)))))))


(defun sel=case.is.proved (case)

  ;;; Input:   an object of type \verb$SEL*CASE$
  ;;; Value:   T, if \verb$CASE$ is proved.

  (cond ((sel=case.sub.cases case)
	 (every #'(lambda (sub.case)
		    (sel=case.is.proved sub.case))
		 (sel=case.sub.cases case)))
	(t (eq (sel=object.status (sel=case.proof case)) 'solved))))



(defun sel=refute (object)

  ;;; Input:   a sel=object
  ;;; Effect:  tries to refute the given object according to the existing proof-tree
  ;;; Value:   T, iff object has been refuted

  (cond ((> sel*refutation.depth 2) nil)
	(t (let ((status (sel=object.status object)))
	     (cond ((member status '(connected))
		    (cond ((case (sel=object.type object)
			     (simplification (sel=simplify.object object))
			     (simplification.cases (sel=simplify.cases object))
			     (induction (sel=refute.by.induction object))
			     (t (sel=refute.object object)))
			   (sel=refute object))))
		   ((member status '(connected.prop connected.first sketch.first))
		    (sel=refute.close.edges object))		    
		   ((eq status 'solved) t))))))


(defun sel=refute.backward (object)

  ;;; Input:   a sel=object
  ;;; Effect:  tries to establish a first-order connection between object and a theorem in
  ;;;          the propositional refutation tree.
  ;;;          If succeeded all objects on the way are instantiated and adapted.
  ;;; Value:   t, if the connection has been established.

  (let (result)
    (cond ((member (sel=object.gterm object) (db-theorems))
	   (sel=object.copy.and.rename.gterm object)
	   (setf (sel=object.status object) 'sketch.first)
	   t)
	  (T (some #'(lambda (taf.edges)
		       (cond ((eq 'resolution (sel=edge.type (third taf.edges)))
			      (cond ((sel=refute.backward (sel=edge.succ.object (third taf.edges)))
				     (setq result (sel=edge.res.establish.back object taf.edges))
				     (cond ((null result)
					    (cond ((sel=refute.undo.backward object)
						   (sel=refute.backward object))))
					   (t (setf (getf (sel=object.attributes object) 'taf.edges) taf.edges)
					      (setf (sel=object.status object) 'sketch.first)
					      t)))))))
		   (sel=object.succs object))))))


(defun sel=refute.undo.backward (object)

  ;;; Input:    a sel=object
  ;;; Effect:   undoes all instantiations of the connection between object and a theorem
  ;;;           tries to establish another connection.
  ;;; Value:    t, if another connection has been established.

  (let (taf.edges)
    (setf (sel=object.gterm object) (getf (sel=object.attributes object) 'initial.value))
    (setf (sel=object.status object) 'sketch.prop)
    (setf (sel=object.substs object) (list nil))
    (cond ((setq taf.edges (getf (sel=object.attributes object) 'taf.edges))
	   (setf (sel=edge.status (third taf.edges)) 'initial)
	   (setf (sel=edge.modification (third taf.edges)) nil)
	   (setf (sel=edge.input.subst (third taf.edges)) nil)
	   (cond ((sel=refute.undo.backward (sel=edge.succ.object (third taf.edges))))
		 ((sel=refute.literal.next.solution object taf.edges))
		 (t (sel=refute.object.with.alternative.and object taf.edges))))
	  ((sel=refute.literal.next.solution object taf.edges))
	  ((sel=refute.object.with.alternative.and object taf.edges)))))



(defun sel=refute.close.edges (object)

  ;;; Input:   an object
  ;;; Effect:  refines the propositional graph in order to obtain a first order refutation
  ;;; Value:   T, if a proof for object has been found.
  
  (let (failed.taf.edges)
    (setf (sel=object.substs object) (list nil))
    (cond ((every #'(lambda (taf.edges)
		      (cond ((or (neq 'output (second taf.edges))
				 (DB-WITH.GTERMS.INSERTED
				  (sel=object.conjunctive.parts object (car taf.edges)) 'theorem nil
				  (let ((sel*variables (union sel*variables (DA-GTERM.VARIABLES.ALONG.TAF
									     (sel=object.gterm object) (car taf.edges))))
					(sel*pred.symbols (union sel*pred.symbols (da-gterm.predicates (sel=object.gterm object))))
					(sel*failed.lemma.cache nil))
				    (sel=object.close.edge object taf.edges)))))
			    (t (setq failed.taf.edges taf.edges)
			       nil)))
		  (sel=object.succs object))
	   (setf (sel=object.status object) 'solved))
	  ((and (member (sel=object.type object) '(resolution resolution.decompose))
		(sel=refute.object.with.alternative.and object failed.taf.edges))
	   (sel=refute.close.edges object)))))


(defun sel=object.close.edge (object taf.edges)

  ;;; Input:   an object and a description of a literal-refutation
  ;;; Effect:  tries to establish the refutation of the seleceted part
  ;;;          of object.
  ;;; Value:   T, if the refutation was successful.

  (let (result)
    (while (and (null (setq result (sel=refute.close.edge object taf.edges (third taf.edges))))
		(member (sel=edge.type (third taf.edges)) '(resolution factor))
		(sel=refute.literal.next.solution object taf.edges)))
    (cond (result (sel=object.propagate.substs object (third taf.edges))))))


(defun sel=object.propagate.substs (object edge)

  ;;; Input:   an object and an edge
  ;;; Effect:  collects the substitutions of the modification at the edge and merges them
  ;;;          into the substs-slot of object.
  ;;; Value:   undefined.
  
  (let ((substs (sel=object.substs object)))
    (setq substs (uni-subst.list.merge substs (list (sel=edge.input.subst edge))))
    (cond ((eq (sel=edge.type edge) 'resolution)
	   (setq substs (uni-subst.list.merge
			 substs
			 (mapcar #'(lambda (subst)
				     (uni-subst.restriction subst #'(lambda (var) (member var sel*variables))))
				 (uni-subst.list.merge (sel=object.substs (sel=edge.succ.object edge))
						       (list (sel=edge.input.subst (sel=object.edge (sel=edge.succ.object edge)))))))))
	  (t (setq substs (uni-subst.list.merge substs (sel=object.substs (sel=edge.succ.object edge))))))
    (setf (sel=object.substs object) substs)))


(defun sel=refute.close.edge (object taf.edges edge)
  
  (cond ((eq (sel=edge.status edge) 'finished)
	 (sel=refute (sel=edge.succ.object edge)))
	(T (cond ((eq (sel=edge.type edge) 'resolution)
		  (sel=refute.res.establish.prop.part object taf.edges edge))
		 ((eq (sel=edge.type edge) 'factor)
		  (cond ((sel=edge.fac.establish object taf.edges)
			 (setf (sel=object.status (sel=edge.succ.object edge)) 'solved))))
		 ((eq (sel=edge.type edge) 'paramodulation)
		  (cond ((sel=edge.par.establish object taf.edges)
			 (setf (sel=object.status (sel=edge.succ.object edge)) 'solved))))
		 ((eq (sel=edge.type edge) 'subproblem)
		  (sel=edge.sub.problem.establish object taf.edges))
		 ((sel=edge.mod.establish object taf.edges)
		  (sel=refute (sel=edge.succ.object edge)))))))


(defun sel=refute.res.establish.prop.part (object taf.edges edge)

  (let* ((other.object (sel=edge.succ.object (third taf.edges)))
	 (attr (getf (sel=object.attributes other.object) 'up)))
    (cond ((and attr (eq (sel=object.status other.object) 'sketch.prop))
	   (sel=refute.backward other.object)))
    (cond ((sel=edge.res.establish object taf.edges)
	   (setf (sel=object.status (sel=edge.succ.object edge)) 'connected.prop)
	   (sel=refute (sel=edge.succ.object edge)))
	  ((and attr (sel=refute.undo.backward other.object))
	   (setf (sel=edge.status edge) 'initial)
	   (setf (sel=edge.modification edge) nil)
	   (setf (sel=edge.input.subst edge) nil)
	   (sel=refute.res.establish.prop.part object taf.edges edge)))))


;;;;;=========================================================================================================
;;;;;
;;;;;  Chapter 3
;;;;;  ---------
;;;;;
;;;;;  finding a proposional logical proof.
;;;;;
;;;;;=========================================================================================================


(defun sel=refute.object (object)

  ;;; Input:   a sel=object
  ;;; Effect:  builds up a propositional proof tree for object which is stored under the
  ;;;          slot succs
  ;;; Value:   undefined.

  (cond ((not (member (sel=object.status object) '(sketch connected)))
	 (every #'(lambda (taf.edges)
		    (cond ((eq (second taf.edges) 'output)
			   (sel=refute.object (sel=edge.succ.object (third taf.edges))))))
		(sel=object.succs object)))
	((da-formula.is.false (sel=object.gterm object))
	 (setf (sel=object.type object) 'trivial)
	 (setf (sel=object.status object)
	       (cond ((eq (sel=object.status object) 'connected) 'connected.prop)
		     (t 'sketch.prop))))
	((cond ((null (sel=object.edge object))
		(sel=refute.gterm object (sel=object.gterm object) nil))
	       (t (sel=refute.without.taf object (sel=object.gterm object) (sel=edge.taf (sel=object.edge object)) nil)))
	 (setf (sel=object.type object) 'resolution)
	 (setf (sel=object.status object)
	       (cond ((eq (sel=object.status object) 'connected) 'connected.prop)
		     (t 'sketch.prop))))))


(defun sel=refute.gterm (object gterm taf)

  ;;; Input:   a sel=object, a gterm which is a part of object and a term-access-function, denoting gterm
  ;;;          in object.
  ;;; Effect:  computes a propositional proof tree for gterm which is stored under the
  ;;;          slot succs. Old proofs (or proof attempts) remain in the succ-slot.         
  ;;; Value:   an sexpression =/ nil if a prop. proof was found else nil

  (let ((edges (sel=object.succs object)))
    (cond ((and (da-literal.is gterm)
		(sel=refute.literal object gterm taf)))
	  ((and (eq 'and (da-gterm.symbol gterm))
		(sel=refute.conjunction object gterm taf)))
	  ((and (eq 'or (da-gterm.symbol gterm))
		(sel=refute.disjunction object gterm nil taf)))
	  (t (setf (sel=object.succs object) edges)
	     nil))))


(defun sel=refute.without.taf (object gterm dest.taf taf)

  ;;; Input:   a sel=object, a gterm and its taf inside object and a taf (dest.taf) of
  ;;;          a sub-gterm of gterm which is assumed to be false.
  ;;; Effect:  computes a prop. refutation of gterm using a path through the denoted sub-gterm
  ;;; Value:   an sexpression =/ nil if a prop. proof was found else nil

  (cond ((cdr dest.taf)
	 (setq gterm (sel=refute.without.taf object gterm (cdr dest.taf) taf))))
  (cond ((null gterm) nil)
	((null dest.taf) gterm)
	((or (eq 'and (da-gterm.symbol gterm))
	     (sel=refute.disjunction object gterm (car dest.taf) (append (cdr dest.taf) taf)))
	 (nth (1- (car dest.taf)) (da-gterm.termlist gterm)))))


(defun sel=refute.conjunction (object gterm taf)

  ;;; Input:  a sel=object, a gterm (a conjunction) and its taf inside object
  ;;; Effect:  computes a propositional proof tree for gterm which is stored under the
  ;;;          slot succs.
  ;;; Value:   an sexpression =/ nil if a prop. proof was found else nil

  (LET ((new.taf (da-taf.create.zero taf)))
    (UNWIND-PROTECT (PROGN (MAPC #'(LAMBDA (GTERM)
				     (setq new.taf (da-taf.create.next new.taf))
				     (DB-GTERM.INSERT GTERM 'IGNORE (cons object new.taf))) 
				 (da-gterm.termlist gterm))
			   (setq taf (da-taf.create.zero taf))
			   (some #'(lambda (gterm)
					(setq taf (da-taf.create.next taf))
					(cond ((or (eq 'resolution.decompose (sel=object.type object))
						   (and (not (getf (da-gterm.attributes gterm) 'equation))
							(not (getf (da-gterm.attributes gterm) 'implication))))
					       (sel=refute.gterm object gterm taf))))
				    (da-gterm.termlist gterm)))
      (MAPC #'(LAMBDA (GTERM) (DB-GTERM.DELETE GTERM t)) (REVERSE (da-gterm.termlist gterm))))))
  


(defun sel=refute.disjunction (object gterm arg taf)

  ;;; Input:   a sel=object, a gterm (a disjunction) and its taf inside object
  ;;; Effect:  computes a propositional proof tree for gterm which is stored under the
  ;;;          slot succs.
  ;;; Value:   an sexpression =/ nil if a prop. proof was found else nil

  (let ((edges (sel=object.succs object)))
    (setq taf (da-taf.create.zero taf))
    (cond ((every #'(lambda (subgterm)
		      (setq taf (da-taf.create.next taf))
		      (cond ((eq (car taf) arg) t)
			    ((sel=refute.gterm object subgterm taf))))
		  (da-gterm.termlist gterm)))
	  (t (setf (sel=object.succs object) edges)
	     nil))))


(defun sel=refute.literal (object literal taf)

  ;;; Input:   a sel=object, a gterm (a literal) and its taf inside object
  ;;; Effect:  computes a propositional proof tree for the literal which is stored under the
  ;;;          slot succs.
  ;;;          WHAT ABOUT THE OLD PROOFS ???
  ;;; Value:   an sexpression =/ nil if a prop. proof was found else nil

  (let* ((symbol (da-literal.symbol literal))
	 (taf.edges (assoc taf (sel=object.succs object) :test 'equal))
	 prev.object eq.sign)
    (cond ((and (eq 'resolution.decompose (sel=object.type object))      ; do not destroy the given decomposition
		taf.edges
		(neq 'output (second taf.edges)))
	   nil)
	  ((and taf.edges (third taf.edges) (eq (second taf.edges) 'failed)) nil)
	  ((and taf.edges (third taf.edges))                                   ; a proof has been found
	   (setf (second taf.edges) 'output))
	  ((and (da-predicate.is.equality symbol)
		(da-sign.is.negative (da-literal.sign literal))
		(not (dp-literal.is.predefined literal))) ; paramodulation
	   (sel=edge.introduce object taf 'paramodulation
			       (make-sel*object :gterm (da-literal.false) :substs (list nil)
						:type 'trivial :status 'sketch.prop :prev.object object)
			       (dp-gterm.eq.reflexivity)))
	  ((multiple-value-setq (prev.object eq.sign)
	       (sel=refute.find.prev.object object literal))   ; factorization
	   (cond (eq.sign
		  (sel=edge.introduce object taf 'factor
				      (make-sel*object :gterm (da-literal.false) :substs (list nil)
						       :type 'trivial :status 'sketch.prop)
				      (list 'factor prev.object nil (make-sel*edge :status 'initial))))
		 (t nil)))
	  (T (DB-PREDICATE.DATABASE.selection
	      literal (da-sign.other.sign (da-literal.sign literal))
	      #'(lambda (other.side) ; resolution
		  (let (new.symbols)
		    (cond ((and ; (sel=refute.solution.has.not.been.considered object other.side)
			    (setq new.symbols (sel=refute.other.side.does.not.exceed other.side)))
			   (let ((sel*pred.symbols (union sel*pred.symbols new.symbols)))
			     (sel=refute.single.literal object other.side taf)))))))))))


(defun sel=refute.solution.has.not.been.considered (object other.side)

  (let (gterm)
    (every #'(lambda (taf.edges)
	       (or (eq (second taf.edges) 'output)
		   (progn (setq gterm (da-access (car taf.edges) (sel=object.gterm object)))
			  (and (neq gterm (car other.side))
			       (neq gterm (getf (da-gterm.attributes (car other.side)) 'origin))))))
	   (sel=object.succs object))))


(defun sel=refute.other.side.does.not.exceed (other.side)

  ;;; Input:   a database entry
  ;;; Effect:  tests whether the predicates occurring in other.side are not greater than those
  ;;;          occurring in the proof so far.
  ;;; Value:   the list of new predicate symbols.

  (let* ((gterm (cond ((da-gterm.is (third other.side)) (third other.side))
		      (t (da-access (cdr (third other.side)) (sel=object.gterm (car (third other.side)))))))
	 (preds2 (da-gterm.predicates gterm)))
    (cond ((some #'(lambda (pred2)
		     (and (not (member pred2 sel*pred.symbols))
			  (some #'(lambda (pred1)
				    (da-prefun.is.less pred1 pred2))
				sel*pred.symbols)
			  (every #'(lambda (pred1)
				     (not (da-prefun.is.less pred2 pred1)))
				 sel*pred.symbols)))
		 preds2)
	   nil)
	  (t preds2))))
			       

(defun sel=refute.single.literal (object other.side taf)  ;;  &optional stop

  ;;; Input:   a sel=object, a tuple as it is described in DB, a taf denoting the literal in object,
  ;;;          and a flag
  ;;; Effect:  tries to compute a prop. refutation of the literal with the help of other.side
  ;;;          if stop is nil, else other.side is appended to object.
  ;;; Value:   an sexpression =/ nil if a prop. proof was found else nil

  (let ((other.object (make-sel*object :prev.object object
				       :substs (list nil)
				       :gterm (third other.side)
				       :edge (make-sel*edge :succ.object object :taf (fourth other.side))
				       :type 'resolution
				       :status 'sketch.prop   ;;; (cond (stop 'sketch) (t 'sketch.prop))
				       :attributes (list 'up (sel=refute.other.side.goes.up other.side))))
	(gterm (cond ((consp (third other.side)) (da-access (cdr (third other.side)) (sel=object.gterm (car (third other.side)))))
		     (t (third other.side))))
	new.taf)
    (cond ((cond ((eq gterm (sel=object.gterm object))
		  (setq new.taf (da-taf.common.taf (list (fourth other.side) taf)))
		  (sel=refute.without.taf other.object (da-access new.taf gterm)
					  (DA-TAF.DIFFERENCE.OF.TWO.TAFS (fourth other.side) new.taf)
					  new.taf))
		 (t (sel=refute.without.taf other.object gterm (fourth other.side) nil)))
	   (sel=edge.introduce object taf 'resolution other.object (car other.side))))))


;;; in case stop is true:	 (sel=edge.introduce object taf 'resolution other.object (car other.side))


(defun sel=refute.other.side.goes.up (other.side)

  (and (da-gterm.is (third other.side))
       (some #'(lambda (pred)
		 (da-prefun.is.less (da-gterm.symbol (car other.side)) pred))
	     (da-gterm.predicates (third other.side)))))


(defun sel=refute.find.prev.object (object literal)

  ;;; Input:   a sel=object and a literal
  ;;; Effect:  walks back through the proof tree in order to find a literal which has the same predicate
  ;;;          symbol as literal.
  ;;; Value:   a multiple value: the object of the found literal and a flag indicating whether the signs
  ;;;          of both literals are equal (T) or not (nil).

  (cond ((null object) nil)
	((sel=object.edge object)
	 (let* ((gterm (cond ((da-gterm.is (sel=object.gterm object)) (sel=object.gterm object))
		      (t (da-access (cdr (sel=object.gterm object)) (sel=object.gterm (car (sel=object.gterm object)))))))
		(other.literal (da-access (sel=edge.taf (sel=object.edge object)) gterm)))
	   (cond ((eq (da-literal.symbol literal) (da-literal.symbol other.literal))
		  (values object (eq (da-literal.sign literal) (da-literal.sign other.literal))))
		 (t (sel=refute.find.prev.object (sel=object.prev.object object) literal)))))))


(defun sel=refute.literal.next.solution (object taf.edges)

  ;;; Input:   a sel=object and a refutation-sketch of a literal
  ;;; Effect:  computes another propositional way to refute the literal denoted by object and (car taf.edges)
  ;;;          which is not already stored
  ;;; Value:   T, if some literal has been found.

  (let ((gterm (da-access (car taf.edges) (sel=object.gterm object))))
    (cond ((and (da-literal.is gterm)
		(not (sel=refute.find.prev.object object gterm)))
	   (cond ((DB-PREDICATE.DATABASE.selection
		   gterm (da-sign.other.sign (da-literal.sign gterm))
		   #'(lambda (other.side)
		       (cond ((and (sel=refute.solution.has.not.been.considered object other.side)
				   (every #'(lambda (edge)
					      (and (neq (car other.side) (sel=edge.modifier edge))
						   (neq (getf (da-literal.attributes (car other.side)) 'origin)
							(sel=edge.modifier edge))))
					  (cddr taf.edges)))
			      (sel=refute.single.literal object other.side (car taf.edges))))))
		  (cond ((sel=edge.modification (fourth taf.edges))
			 (setf (sel=object.gterm object)
			       (sel=object.change.edge.modification (sel=object.gterm object)
								    (sel=edge.modification (fourth taf.edges))
								    T (car taf.edges)))))
		  t))))))
    
    
(defun sel=refute.object.with.alternative.and (object taf.edges)

  ;;; Input:   a sel=object and a refutation-sketch of a literal
  ;;; Effect:  computes another propositional way to refute the gterm denoted by object and (car taf.edges)
  ;;;          which is not already stored or it searches for conjunctive alternatives for the denoted
  ;;;          literal and computes a refutation for that sub-gterm of object.
  ;;; Value:   an sexpression =/ nil if an alternative was found.

  (let* (taf new.gterm result)
    (setq taf (car taf.edges))
    (while (and taf (null result)
		(or (null (sel=object.edge object))
		    (not (da-taf.is.subtaf (cdr taf) (sel=edge.taf (sel=object.edge object))))))
      (setq new.gterm (da-access (cdr taf) (sel=object.gterm object)))
					; goto top-level until the next conjunctive part
      (cond ((eq (da-gterm.symbol new.gterm) 'and)
	     (sel=refute.disable.subterm object (cdr taf))
	     (setq result (sel=refute.gterm object new.gterm (cdr taf)))))
      (pop taf))
    (setf (sel=object.status object)
	  (cond ((and result (member (sel=object.status object) '(connected connected.prop))) 'connected.prop)
		((and (null result) (member (sel=object.status object) '(connected connected.prop))) 'connected)
		(result 'sketch.prop)
		(t 'sketch)))
    result))


(defun sel=refute.disable.subterm (object taf)

  ;;; Input:    a sel=object and a term-access-function
  ;;; Effect:   all refutation-paths of gterms inside taf are disabled.
  ;;; Value:    undefined.

  (mapc #'(lambda (taf.edges)
	    (cond ((and (da-taf.is.subtaf taf (car taf.edges))
			(eq (second taf.edges) 'output))
		   (sel=object.undo.edge object (car taf.edges))
		   (setf (second taf.edges) 'failed))))
	(sel=object.succs object)))


;;;;;============================================================================================================
;;;;;
;;;;; Handling the termlists
;;;;;
;;;;;============================================================================================================


(defun sel=edge.res.establish (object taf.edges)

  ;;; Input:   a sel=object and a refutation sketch
  ;;; Effect:  tries to find a first order refutation between the denoted literal of object
  ;;;          and the specified opposite literal in the refutation sketch.
  ;;; Value:   an sexpression =/ nil if a refutation has been found.
  
  (let* ((other.object (sel=edge.succ.object (third taf.edges))))
    (sel=edge.res.establish.1 object other.object
			      (third taf.edges) (sel=object.edge other.object))))
  


(defun sel=edge.res.establish.back (object taf.edges)

  (let* ((other.object (sel=edge.succ.object (third taf.edges))))
    (sel=edge.res.establish.1 other.object object
			      (sel=object.edge other.object) (third taf.edges))))


(defun sel=edge.res.establish.1 (object other.object edge back.edge)

  (let (add.conditions sol1 sol2 lit1 lit2 result)
    (cond ((or (eq (sel=edge.status edge) 'initial)
	       (eq (sel=edge.status back.edge) 'initial))
	   (sel=object.copy.and.rename.gterm other.object (sel=edge.taf back.edge))))
    (setq add.conditions 
	  (rl-with.problem sel*case.actual 'condition nil 'binding
			   object 'object other.object 'object
			   #'(lambda (sel*case.condition sel*eq.bindings occ1 occ2)
			       (multiple-value-setq (sol1 sol2)
				   (rl-with.sub.problem
				    occ1 (sel=edge.taf edge)
				    occ2 (sel=edge.taf back.edge)
				    #'(lambda (occ1 occ2)
					(cond ((setq result (and (not (da-literal.is.true (eg-eval (rl-object occ1))))          
								 (sel=equalize.gterms occ1 occ2))))
					      ((and (da-literal.is (rl-object occ1)) (dp-literal.is.predefined (rl-object occ1)))
					       (rl-object.change
						occ1 (dp-literal.simplify (rl-object occ1)
									  #'(lambda (cond)
									      (every #'(lambda (lit)
											 (da-formula.is.false (eg-eval lit)))
										     cond)))
						nil "predefined datatypes")
					       (setq result (and (not (da-literal.is.true (eg-eval (rl-object occ1))))
								 (sel=equalize.gterms occ1 occ2)))))))))))
    (cond (result (cond (add.conditions
			 (sel=case.introduce.case.analysis object (sel=edge.taf edge) sol1 add.conditions)))
		  (sel=edge.modification.append edge sol1)
		  (sel=edge.modification.append back.edge sol2)
		  (setq lit1 (da-access (sel=edge.taf edge) (sel=object.gterm object)))
		  (setq lit2 (da-access (sel=edge.taf back.edge) (sel=object.gterm other.object)))
		  (cond ((uni-gterm.are.equal lit1 lit2 nil nil 'opposite)
			 (cond ((and (sel=edge.finish? edge)
				     (sel=edge.finish? back.edge))
				(cond ((null (getf (sel=object.attributes other.object) 'initial.value))
				       (setf (getf (sel=object.attributes other.object) 'initial.value)
					     (sel=object.gterm other.object))))
				(setf (sel=object.gterm other.object)
				      (uni-subst.replace (sel=edge.input.subst back.edge)
							 (sel=object.gterm other.object)))
				t)))))
	  (t (setf (sel=edge.status edge) 'open)
	     nil))))


(defun sel=edge.fac.establish (object taf.edges)

  ;;; Input:   a sel=object and a refutation sketch
  ;;; Effect:  tries to equalize the denoted literal of object
  ;;;          and the specified literal in the refutation sketch in order to
  ;;;          factorize both
  ;;; Value:   an sexpression =/ nil if a refutation has been found.

  (let* (lit1 lit2 sol1 sol2 add.conditions result (other.object (sel=edge.modifier (third taf.edges))))
    (cond ((eq (sel=edge.status (third taf.edges)) 'initial)
	   (setf (third other.object)
		 (da-literal.negate (da-gterm.copy (da-access (sel=edge.taf (sel=object.edge (second other.object)))
							      (sel=object.gterm (second other.object))))))))
    (setq add.conditions
	(rl-with.problem sel*case.actual 'condition nil 'binding
			 object 'object (third other.object) 'gterm
			 #'(lambda (sel*case.condition sel*eq.bindings occ1 occ2)
			     (multiple-value-setq (sol1 sol2)
				 (rl-with.sub.problem occ1 (car taf.edges)
						      #'(lambda (sub.occ1)
							  (cond ((setq result (sel=equalize.gterms sub.occ1 occ2))
								 (setf (third other.object) (rl-object occ2))
								 t))))))))
    (cond (result (cond (add.conditions (sel=case.introduce.case.analysis object (car taf.edges) sol1 add.conditions)))
		  (sel=edge.modification.append (third taf.edges) sol1)
		  (sel=edge.modification.append (fourth other.object) sol2)
		  (setq lit1 (da-access (car taf.edges) (sel=object.gterm object)))
		  (setq lit2 (third other.object))
		  (cond ((uni-gterm.are.equal lit1 lit2 nil nil 'opposite)
			 (cond ((and (sel=edge.finish? (third taf.edges))
				     (sel=edge.finish? (fourth other.object)))
				t))))))))


(defun sel=edge.par.establish (object taf.edges)

  ;;; Input:   a sel=object and a refutation sketch
  ;;; Effect:  tries to equalize both sides of the denoted (negated) equation of object
  ;;; Value:   an sexpression =/ nil iff both sides can be equalized.

  (let (sol add.conditions result)
    (setq add.conditions
	  (rl-with.problem sel*case.actual 'condition object 'object nil 'binding
			   #'(lambda (sel*case.condition occ sel*eq.bindings)
			       (setq sol (rl-with.sub.problem
					  occ (car taf.edges)
					  #'(lambda (sub.occ)
					      (cond ((da-literal.is.false (rl-object sub.occ)) (setq result t))
						    (t (rl-with.sub.objects 
							sub.occ (da-taf.create.left) sub.occ (da-taf.create.right)
							#'(lambda (occ1 occ2)
							    (setq result (sel=equalize.gterms occ1 occ2))))))))))))
    (cond (result (cond (add.conditions (sel=case.introduce.case.analysis object (car taf.edges) sol add.conditions)))
		  (sel=edge.modification.append (third taf.edges) sol)
		  (let ((literal (da-access (car taf.edges) (sel=object.gterm object))))
		    (cond ((and (da-literal.is literal)
				(or (da-literal.is.false literal)
				    (uni-term.are.equal (car (da-literal.termlist literal))
							(second (da-literal.termlist literal)))))
			   (sel=edge.finish? (third taf.edges)))))))))



(defun sel=edge.mod.establish (object taf.edges)

  (let ((other.object (sel=edge.succ.object (third taf.edges))))
    (setf (sel=object.status other.object) 'connected)
    (setf (sel=object.gterm other.object) (NORM-NORMALIZE.GTERM (da-gterm.copy (sel=object.gterm object))))
    (setf (sel=object.type other.object) 'resolution.set)
    (setf (sel=object.succs other.object) nil)
    (sel=edge.finish? (third taf.edges))))


(defun sel=edge.sub.problem.establish (object taf.edges)

  (DB-WITH.GTERMS.INSERTED
   (sel=object.conjunctive.parts object (car taf.edges)) 'theorem nil
   (let ((sel*variables (union sel*variables (DA-GTERM.VARIABLES.ALONG.TAF
					      (sel=object.gterm object) (car taf.edges))))
	 (sel*pred.symbols (union sel*pred.symbols (da-gterm.predicates (sel=object.gterm object))))
	 (sel*failed.lemma.cache nil))
     (cond ((sel=refute (sel=edge.modifier (third taf.edges)))
	    (sel=edge.finish? (third taf.edges)))))))


;;;;;=========================================================================================================
;;;;;
;;;;;  Chapter 1
;;;;;  ---------
;;;;;
;;;;;  Simplification of a formula
;;;;;
;;;;;=========================================================================================================


(defrule sel=simplify.cases (&others object)

  (SIMPLIFY 0 ("simplifying by case analysis ~A" 1) ("simplify" nil nil (1)))

  (let (modification add.conditions)
    ;(cond ((multiple-value-setq (modification add.conditions)
;				(rl-with.problem object 'object sel*case.actual 'condition
;						 #'(lambda (occ sel*case.condition)
;						     (sel=simpl.introduce.cases occ)))) 
;	   (cond (add.conditions (sel=case.introduce.case.analysis object nil modification add.conditions)))
;	   (setf (sel=object.status object) 'connected.first)
;	   (sel=object.insert.mod.edge object modification 'simplification)
;	   T)
;	  (t (setf (sel=object.type object) 'resolution.set)))

    (setf (sel=object.type object) 'resolution.set)
    ))


(defun sel=simpl.introduce.cases (occ)

  (let (cases)
    (cond ((setq cases (sel=simpl.elim.suggests.case.analysis (rl-object occ)))
	   (rl-object.change sel*case.condition
			     (cons (da-literal.create '+ (da-predicate.equality) 
						      (list (da-term.create (caar cases))
							    (third (car cases))))
				   (rl-object sel*case.condition))
			     nil "Inventing case analysis")
	   (mapc #'(lambda (taf)
		     (rl-object.change occ (da-term.copy (third (car cases))) taf "case assumption"))
		 (da-symbol.occurs.in.gterm (caar cases) (rl-object occ)))
	   t))))




(defrule sel=simplify.object (&others object)

  ;;; Input:   a sel=object and a list of formulas
  ;;; Effect:  simplifies object according the following rules:
  ;;;
  ;;; Value:   an sexpression =/ nil (never backtrack)

  (SIMPLIFY 0 ("simplifying ~A" 1) ("simplify" nil nil nil))

  (let (modification add.conditions)
    (cond ((multiple-value-setq (modification add.conditions)
	       (rl-with.problem object 'object sel*case.actual 'condition
				#'(lambda (occ sel*case.condition)
				    (sel=simpl.apply.instantiations occ (sel=case.instances sel*case.actual))
				    (sel=simpl.top.level occ))))
	   (cond (add.conditions (sel=case.introduce.case.analysis object nil modification add.conditions)))
	   (setf (sel=object.status object) 'connected.first)
	   (sel=object.insert.mod.edge object modification 'simplification.cases)
	   T)
	  (t (setf (sel=object.type object) 'simplification.cases)))))


(defun sel=simpl.apply.instantiations (occ termsubst)

  (let (unifier)
    (cond (termsubst
	   (smapl #'(lambda (termsubst)
		      (setq unifier (car (uni-subst.merge unifier
							  (car (uni-term.unify (car termsubst) (second termsubst)))))))
		  #'cddr
		  termsubst)
	   (rl-object.changes occ
			      (mapcar #'(lambda (taf.value)
					  (list 'replace (car taf.value) (cdr taf.value)))
				      (uni-subst.replacements unifier (rl-object occ)))
			      nil
			      (list "instance" unifier nil))))))

	     

(defun sel=simpl.top.level (occ)

  ;;; Input:   a rl-object
  ;;; Effect:  simplifies the object with the help of algorithmic definitions,
  ;;;          Integer-routines, constant elimination and first-order simplification
  ;;; Value:   undefined

  (let (termsubst cond changed gterm)
    ;(cond ((setq termsubst (sel=simpl.elim.equations (sel=case.condition sel*case.actual) (rl-object occ)))
    ;  (sel=simpl.insert.elim.equations nil occ termsubst)))
    (setq gterm (eg-eval (rl-object occ)))
    (cond ((not (uni-gterm.are.equal gterm (rl-object occ)))
	   (rl-object.change occ (cond ((da-term.is gterm) (da-term.copy gterm))
				       (t (da-gterm.copy (norm-normalization gterm))))
			     nil "symbolic evaluation")))
    (sel=simpl.set.theory occ)
    (let ((sel*variables (union sel*variables (da-gterm.variables (rl-object occ)))))
      (sel=simpl.gterm occ)
      (setq gterm (eg-eval (rl-object occ)))
      (cond ((not (uni-gterm.are.equal gterm (rl-object occ)))
	     (rl-object.change occ (cond ((da-term.is gterm) (da-term.copy gterm))
					 (t (da-gterm.copy (norm-normalization gterm))))))))))

;;  (cond ((setq termsubst (sel=simpl.elim.equations nil (rl-object occ)))
;; 	   (multiple-value-setq (cond changed) (sel=simpl.insert.elim.equations nil occ termsubst))
;; 	   (cond (changed (sel=simpl.top.level occ)))))


(defun sel=simpl.set.theory (occ)

  (cond ((not (sel=simpl.gterm.is.set.theory (rl-object occ))) nil)
	((da-formula.is.false (DP-SET.SIMPLIFICATION (rl-object occ) (da-gterm.variables (rl-object occ))))
	 (rl-object.change occ (da-literal.false) nil "set theory"))))


(defun sel=simpl.gterm.is.set.theory (gterm)

  (and (not (da-term.is gterm))
       (DA-GTERM.LITERALS.WITH.PROPERTY gterm
					#'(lambda (lit)
					    (dp-set.literal.is lit)))))


(defun sel=simpl.and.eval.gterm (occ)

  (let ((gterm (eg-eval (rl-object occ))))
    (cond ((not (uni-gterm.are.equal gterm (rl-object occ)))
	   (rl-object.change occ (cond ((da-term.is gterm) (da-term.copy gterm))
				       (t (da-gterm.copy (norm-normalization gterm))))
			     nil "symbolic evaluation")))
    (sel=simpl.gterm occ)
    (setq gterm (eg-eval (rl-object occ)))
    (cond ((not (uni-gterm.are.equal gterm (rl-object occ)))
	   (rl-object.change occ (cond ((da-term.is gterm) (da-term.copy gterm))
				       (t (da-gterm.copy (norm-normalization gterm))))
			     nil "symbolic evaluation")))))


(defun sel=simpl.gterm (occ)

  ;;; Input:   a rl-object and a list of formulas (assumed to be false)
  ;;; Effect:  simplifies the given rl-object
  ;;; Value:   undefined
  
  (cond ((da-literal.is (rl-object occ)) (sel=simpl.literal occ))
	((eq 'and (da-gterm.symbol (rl-object occ)))
	 (sel=simpl.and.junction occ))
	((eq 'or (da-gterm.symbol (rl-object occ)))
	 (sel=simpl.or.junction occ))
	((da-term.is (rl-object occ))
	 (sel=simpl.term occ))))


(defun sel=simpl.literal (occ)

  ;;; Input:   a rl-object and a list of formulas (assumed to be false)
  ;;; Effect:  simplifies the given rl-object (literal)
  ;;; Value:   undefined

  (let ((taf (da-taf.create.zero nil))
	(predefined (dp-literal.is.predefined (rl-object occ)))
	unis right new.lit)
    (mapc #'(lambda (term)
	      (declare (ignore term))
	      (setq taf (da-taf.create.next taf))
	      (rl-with.sub.objects occ taf #'(lambda (sub.occ) (sel=simpl.term sub.occ predefined))))
	  (da-gterm.termlist (rl-object occ)))
    (cond ((dp-literal.is.predefined (rl-object occ))
	   (rl-object.change
	    occ (eg-eval (dp-literal.simplify (rl-object occ)
					      #'(lambda (cond)
						  (every #'(lambda (lit)
							     (da-formula.is.false (eg-eval lit)))
							 cond))))
	    nil "predefined datatypes"))
	  (t (cond ((and (da-literal.is.equality (rl-object occ))
			 (uni-term.are.equal (car (da-literal.termlist (rl-object occ)))
					     (second (da-literal.termlist (rl-object occ)))))
		    (rl-object.change occ (cond ((da-sign.is.positive (da-literal.sign (rl-object occ)))
						 (da-literal.true))
						(t (da-literal.false)))
				      nil "symbolic evaluation"))
		   ((or (db-predicate.database.selection
			 (rl-object occ) (da-sign.other.sign (da-literal.sign (rl-object occ)))
			 #'(lambda (other.side)
			     (cond ((and (eql (second other.side) 0)
					 (UNI-WITH.CONSTANTS sel*variables
					    (uni-literal.match (car other.side) (rl-object occ) T 'ignore)))
				    (rl-object.change occ (da-literal.false) nil (car other.side) nil)))))
			(DB-MODIFIER.SELECTion
			 (rl-object occ) 'simplifications nil
			 #'(lambda (modifier)
			     (cond ((and (setq unis (UNI-WITH.CONSTANTS sel*variables
					              (uni-literal.match (da-modifier.input modifier)
								         (rl-object occ) T 'opposite)))
					 (sel=refute.condition (da-modifier.condition modifier) (car unis) t))
				    (setq right (uni-subst.apply (car unis) (da-modifier.value modifier)))
				    (rl-object.change occ right nil modifier nil)
				    T))))
			(sel=simpl.reduce.case.analysis.term occ))
		    (sel=simpl.gterm occ))
		   (t (setq new.lit (eg-eval (rl-object occ)))
		      (cond ((not (uni-gterm.are.equal new.lit (rl-object occ)))
			     (rl-object.change occ (da-gterm.copy (norm-normalization new.lit))
					       nil "symbolic evaluation")))))))))


(defun sel=simpl.or.junction (occ)

  ;;; Input:  a rl-object denoting a disjunction
  ;;; Effect: simplifies the disjunction by simplifying each member of the disjunction
  ;;;         assuming each previous simplified member as false
  ;;; Value:  undefined.
  
  (let (gterm termlist)
    (sel=simpl.handle.termlist occ
			       #'(lambda (occ arg)
				   (cond ((> arg 0)
					  (let ((arg (nth (1- arg) (da-gterm.termlist (rl-object occ)))))
					    (cond ((da-literal.is arg) (list (da-formula.negate arg))))))))
			       #'(lambda (sub.occ) (sel=simpl.gterm sub.occ)))
    (cond ((some #'(lambda (gterm) (da-formula.is.true gterm))
		 (da-gterm.termlist (rl-object occ)))
	   (rl-object.change occ (da-literal.true) nil "Or-Simplification"))
	  ((some #'(lambda (lit) (da-formula.is.false lit))
		 (da-gterm.termlist (rl-object occ)))
	   (setq gterm (rl-object occ))
	   (setq termlist (remove-if #'(lambda (lit) (da-formula.is.false lit)) (da-gterm.termlist gterm)))
	   (rl-object.change occ (cond ((null termlist) (da-literal.false))
				       ((null (cdr termlist)) (car termlist))
				       (t (da-gterm.create (da-gterm.symbol gterm) termlist)))
			     nil "Or-Simplification")))))


(defun sel=simpl.and.junction (occ)

  ;;; Input:  a rl-object denoting a conjunction
  ;;; Effect: simplifies the conjunction by simplifying each member of the conjunction
  ;;;         assuming each previous simplified member as true
  ;;; Value:  undefined.

  (let (gterm termlist)
    (sel=simpl.handle.termlist occ
			       #'(lambda (occ arg)
				   (cond ((> arg 0)
					  (let ((term (nth (1- arg) (da-gterm.termlist (rl-object occ)))))
					    (list term)))))
					   ;  (cond ((da-literal.is term) (list term)))
			       #'(lambda (sub.occ) (sel=simpl.gterm sub.occ)))
    (sel=simpl.comp.and occ)
    (cond ((some #'(lambda (lit) (da-formula.is.false lit))
		 (da-gterm.termlist (rl-object occ)))
	   (rl-object.change occ (da-literal.false) nil "And-Simplification"))
	  ((some #'(lambda (lit) (da-formula.is.true lit))
		 (da-gterm.termlist (rl-object occ)))
	   (setq gterm (rl-object occ))
	   (setq termlist (remove-if #'(lambda (lit) (da-formula.is.true lit)) (da-gterm.termlist gterm)))
	   (rl-object.change occ (cond ((null termlist) (da-literal.true))
				       ((null (cdr termlist)) (car termlist))
					     (t (da-gterm.create (da-gterm.symbol gterm) termlist)))
			     nil "And-Simplification")))))

(defun sel=simpl.comp.and (occ)

  ;;; Input:  a rl-object denoting a conjunction
  ;;; Effect: seraches for complementary literals and replaces one of them by false.
  ;;; Value:  undefined

  (let (result (gterms (remove-if-not #'(lambda (lit) (da-literal.is lit))
				      (da-formula.junction.open 'and (rl-object occ)))))
    (some #'(lambda (taf)
	      (rl-with.sub.objects occ taf
				   #'(lambda (sub.occ)
				       (rl-object.change sub.occ (da-literal.false)
							 nil "theorem" nil)))
	      (sel=simpl.junction occ taf)
	      (setq result t))
	  (da-gterm.literal.tafs (rl-object occ)
				 #'(lambda (lit)
				     (some #'(lambda (other.lit)
					       (uni-literal.are.equal lit other.lit nil 'opposite))
					   gterms))))
    (cond (result (sel=simpl.comp.and occ)))))


(defun sel=simpl.junction (occ taf)

  ;;; Input:   a rl-object denoting a conjunction and a term-access-function denoting a false
  ;;;          literal.
  ;;; Effect:  simplifies the surroundings of the false literal.
  ;;; Value:   undefined

  (cond (taf
	 (let ((gterm (da-access (cdr taf) (rl-object occ))))
	   (cond ((null (cddr (da-gterm.termlist gterm)))
		  (cond ((eq 'and (da-gterm.symbol gterm))
			 (rl-object.change occ (da-literal.false) (cdr taf) "And-Simplification")
			 (sel=simpl.junction occ (cdr taf)))
			((eq 'or (da-gterm.symbol gterm))
			 (rl-object.change occ (car (remove-if #'(lambda (lit) (da-formula.is.false lit))
							       (da-gterm.termlist gterm)))
					   (cdr taf) "Or-Simplification")))))))))


(defun sel=simpl.handle.termlist (occ activate.fct apply.fct &optional (arg 0))

  ;;; Input:  a rl-object (denoting a gterm), two lambda-expressions and an integer
  ;;; Effect: applies apply.fct to each term of occ while inserting the result of
  ;;;         applying activate.fct to occ into the database
  ;;; Value:  undefined.
 
  (cond ((eql arg (length (da-gterm.termlist (rl-object occ))))  t)
	(t (DB-WITH.GTERMS.INSERTED (funcall activate.fct occ arg)
				    'theorem nil
				    (let ((sel*failed.lemma.cache nil))
				      (rl-with.sub.objects occ (list (1+ arg))
							   #'(lambda (sub.occ) (funcall apply.fct sub.occ)))
				      (sel=simpl.handle.termlist occ activate.fct apply.fct (1+ arg)))))))


(defun sel=simpl.term (occ &optional flag)

  ;;; Input:   a rl-object and a boolean
  ;;; Effect:  simplies term by simplification-equations and integer-routines
  ;;; Value:   the simplified term
  
  (let ((taf (da-taf.create.zero nil))
	(pre.defined (dp-term.is.predefined (rl-object occ)))
	unis right)
    (mapc #'(lambda (ignore)
	      (declare (ignore ignore))
	      (setq taf (da-taf.create.next taf))
	      (rl-with.sub.objects occ taf #'(lambda (sub.occ)
					       (sel=simpl.term sub.occ pre.defined))))
	  (da-gterm.termlist (rl-object occ)))
    (cond (pre.defined
	   (cond ((null flag) (rl-object.change occ (dp-term.simplify (rl-object occ)) nil "predefined datatypes"))))
	  ((da-prefun.is (da-gterm.symbol (rl-object occ)))
	   (cond ((DB-MODIFIER.SELECTION
		   (rl-object occ) 'SIMPLIFICATIONS nil
		   #'(lambda (modifier)
		       (cond ((and (setq unis (UNI-WITH.CONSTANTS sel*variables
					        (uni-term.match (da-modifier.input modifier) (rl-object occ) T)))
				   (sel=refute.condition (da-modifier.condition modifier) (car unis) t))
			      (setq right (uni-subst.apply (car unis) (da-modifier.value modifier)))
			      (rl-object.change occ right nil modifier nil)
			      T))))
		  (sel=simpl.term occ flag))
		 ((sel=simpl.reduce.case.analysis.term occ)
		  (sel=simpl.term occ flag)))))
    (rl-object occ)))



(defun sel=simpl.reduce.case.analysis.term (occ)

  (cond ((some #'(lambda (ind.term)
		   (uni-gterm.are.equal ind.term (rl-object occ)))
	       (getf (sel=case.information sel*case.actual) :gterms.suggested))
	 (DB-MODIFIER.SELECTION
	  (rl-object occ) 'top.level nil
	  #'(lambda (modifier)
	      (sel=modifier.test.and.apply modifier occ nil nil))))))



(defun sel=simpl.elim.suggests.case.analysis (gterm)

  (let ((sub.terms (da-formula.junction.open 'and gterm)) fail all.substs pair case.substs)
    (cond ((cdr sub.terms)
	   (mapc #'(lambda (sub.term)
		     (setq all.substs nil)
		     (cond ((eq 'or (da-gterm.symbol sub.term))
			    (setq fail nil)
			    (DA-GTERM.MAP.LITERALS 
			     sub.term
			     #'(lambda (lit)
				 (cond ((setq pair (cond ((setq pair (sel=simpl.lit.is.elim lit nil))
							  (list (car pair) 1 (cdr pair)))
							 (t (sel=simpl.lit.is.neg.elim lit))))
					(setq all.substs (sel=simpl.elim.insert.pair pair all.substs)))
				       (t (setq fail t)))))
			    (cond ((not fail)
				   (setq case.substs (sel=simpl.elim.join.pairs all.substs case.substs)))))))
		 sub.terms)
	   (sort case.substs #'(lambda (x y) (> (second x) (second y))))))))


(defun sel=simpl.elim.insert.pair (left.right subst)

  (let ((entry (assoc (car left.right) subst)))
    (cond ((null entry) (push left.right subst))
	  ((da-symbol.has.attribute (da-gterm.symbol (third entry)) 'structure)
	   (incf (second entry) (second left.right)))
	  ((da-symbol.has.attribute (da-gterm.symbol (third left.right)) 'structure)
	   (incf (second entry) (second left.right))
	   (setf (third entry) (third left.right))))
    subst))


(defun sel=simpl.elim.join.pairs (subst1 subst2)
  (mapc #'(lambda (pair)
	    (setq subst2 (sel=simpl.elim.insert.pair pair subst2)))
	subst1)
  subst2)


(defun sel=simpl.elim.equations (condition gterm)

  (let (termsubst value)
    (mapc #'(lambda (gterm)
	      (cond ((and (da-literal.is gterm)
			  (setq value (sel=simpl.lit.is.elim gterm t)))
		     (push value termsubst))))
	  (da-formula.junction.open 'or gterm))
    termsubst))


(defun sel=simpl.insert.elim.equations (condition occ termsubst)

  (let (changed)
    (mapc #'(lambda (symbol.value)
	      (mapc #'(lambda (taf)
			(setq changed t)
			(rl-object.change occ (da-term.copy (cdr symbol.value)) taf
					  (format nil "Eliminating ~A" (car symbol.value))))
		    (da-symbol.occurs.in.gterm (car symbol.value) (rl-object occ)))
	      (mapc #'(lambda (gterm)
			(mapc #'(lambda (taf)
				  (setq changed t)
				  (da-replace taf gterm (da-term.copy (cdr symbol.value))))
			      (da-symbol.occurs.in.gterm (car symbol.value) gterm)))
		    condition))
	  termsubst)
    (values condition changed)))


(defun sel=simpl.lit.is.neg.elim (lit)

  (let ((term (da-literal.denotes.match lit)))
    (cond ((and term (null (da-term.termlist term))
		(da-sort.is.finite (da-term.sort term))
		(da-function.skolem (da-term.symbol term)))
	   (list (da-term.symbol term)
		 1
		 (cond ((eq term (car (da-literal.termlist lit))) 
			(second (da-literal.termlist lit)))
		       (t (car (da-literal.termlist lit)))))))))

	      
(defun sel=simpl.lit.is.elim (literal flag)

  (let ((termlist (da-literal.termlist literal))
	(sign (cond (flag (da-sign.minus)) (t (da-sign.plus)))))
    (cond ((and (da-predicate.is.equality (da-literal.symbol literal))
		(eq sign (da-literal.sign literal)))
	   (cond ((and (null (da-term.termlist (car termlist)))
		       (cond (flag (da-variable.is (da-term.symbol (car termlist))))
			     (t (and (da-function.is (da-term.symbol (car termlist)))          
				     (da-function.skolem (da-term.symbol (car termlist))))))
		       (not (da-symbol.occurs.in.gterm (da-term.symbol (car termlist)) (second termlist)))
		       (da-sort.is.subsort (da-term.sort (second termlist))
					   (da-term.sort (car termlist))))
		  (cons (da-term.symbol (car termlist)) (second termlist)))
		 ((and (null (da-term.termlist (second termlist)))
		       (cond (flag (da-variable.is (da-term.symbol (second termlist))))
			     (t (and (da-function.is (da-term.symbol (second termlist)))  
				     (da-function.skolem (da-term.symbol (second termlist))))))
		       (not (da-symbol.occurs.in.gterm (da-term.symbol (second termlist)) (car termlist)))
		       (da-sort.is.subsort (da-term.sort (car termlist))
					   (da-term.sort (second termlist))))
		  (cons (da-term.symbol (second termlist)) (car termlist))))))))




;;;;;=========================================================================================================
;;;;;
;;;;;  Chapter 5
;;;;;  ---------
;;;;;
;;;;;  Induction.
;;;;;
;;;;;=========================================================================================================

;;; each hypothesis is a dotted pair of induction variable descriptions and local variables.
;;; a induction variable description is a triple: a variable v its predecessor p(v) and
;;; the term-access-function of the occurrence of v in p(v).


(defun sel=refute.by.induction (object)

  ;;; Input:   a \verb$SEL*OBJECT$
  ;;; Effect:  handles the induction step where \verb$OBJECT$ is considered as a conclusion and the
  ;;;          \verb$HINTS$ slot contains the information about the predecessors (resp. the hypotheses)
  ;;; Value:   T iff the proof of the induction step was successful.
  
  (let ((termsubsts (mapcar #'car (sel=object.hints object)))
	(hints (sel=object.hints object))
	(gterm (da-gterm.copy (sel=object.gterm object)))
	hypos)
    (setq hypos (mapcar #'(lambda (hypo) (sel=ind.create.hypothesis gterm hypo)) hints))
    (db-with.gterms.inserted (cons gterm hypos) 'theorem nil
			     (let ((sel*pred.symbols (union sel*pred.symbols (da-gterm.predicates gterm)))
				   (sel*failed.lemma.cache nil))
			       (multiple-value-bind (modifications add.conditions)
				   (sel=ind.enable.induction object termsubsts hints)
				 (prog1 (sel=ind.apply.hypotheses object modifications add.conditions 
								  gterm hypos hints)))))))


(defun sel=ind.create.hypothesis (gterm hypo.descr)

  (let (replacement)
    (cond ((and (da-term.is gterm)
		(setq replacement (cond ((somef #'(lambda (prop value)
						    (cond ((uni-term.are.equal gterm prop)
							   value)))
						(car hypo.descr)))
					((getf (second hypo.descr) (da-gterm.symbol gterm)))
					((getf (third hypo.descr) (da-gterm.symbol gterm))))))
	   (da-term.copy replacement))
	  (t (let ((symbol (da-gterm.symbol gterm))
		   (termlist (mapcar #'(lambda (subterm)
					 (sel=ind.create.hypothesis subterm hypo.descr))
				     (da-gterm.termlist gterm))))
	       (setq symbol (cond ((eq symbol 'and) 'or) ((eq symbol 'or) 'and) (t symbol)))
	       (case (type-of gterm)
		     (term (da-term.create symbol termlist nil nil))
		     (literal (da-literal.create (da-sign.other.sign (da-literal.sign gterm)) symbol termlist nil nil))
		     (formula (da-formula.create symbol termlist nil))
		     (otherwise (da-gterm.create symbol termlist nil nil))))))))


(defun sel=ind.enable.induction (object termsubsts hints)

  (rl-with.problem object 'object sel*case.actual 'condition nil 'binding
		   #'(lambda (occ sel*case.condition sel*eq.bindings)
		       (da-gterm.colourize (rl-object occ) 'initial 'induction)
		       (mapc #'(lambda (taf)
				 (da-gterm.colourize (da-access taf (rl-object occ)) nil 'induction))
			     (da-gterm.tafs (rl-object occ) #'(lambda (gt) (da-variable.is (da-gterm.symbol gt)))))
		       (cond ((setq termsubsts (sel=ind.insert.all.contexts occ termsubsts 'induction))
			      (cond ((neq 'success (sel=context.move.up occ 'induction))
				     (let ((tafs (sel=ind.sink.tafs occ hints termsubsts)))
				       (mapc #'(lambda (taf) (da-gterm.colourize (da-access taf (rl-object occ)) 'sink 'induction))
					     tafs)
				       (sel=context.move.down occ tafs 'induction 'sink.context t)
				       (cond ((sel=ind.collect.corresponding.sinks occ termsubsts 'induction)
					      (sel=context.move.up occ 'induction)))))))))))


(defun sel=ind.sink.tafs (occ hints termsubsts)

  ;;; Input:  an object denoting a gterm
  ;;; Value:  returns list of term-accesss functions to all possible sinks.

  (let ((local.fcts (sel=ind.local.variables hints termsubsts)))
    (da-gterm.tafs (rl-object occ)
		   #'(lambda (gt)
		       (and (not (da-colour.is.fade (da-gterm.colour gt 'induction)))
			    (member (da-gterm.symbol gt) local.fcts))))))


(defun sel=ind.local.variables (hypotheses termsubsts)
  (some #'(lambda (hypo)
	    (cond ((eq (car hypo) (car termsubsts))
		   (smapcar #'(lambda (x) x)
			    #'cddr (second hypo)))))
	 hypotheses))



;;;;;-----------------------------------------------------------------------------------------------------------------
;;;;;
;;;;;   Section ? :   Application of the hypotheses
;;;;;
;;;;;-----------------------------------------------------------------------------------------------------------------


(defun sel=ind.apply.hypotheses (object modification add.conditions org.gterm hypotheses termsubsts)

  ;;; Input:  a \verb$SEL*OBJECT$, a modification-chain, a list of additional conditions, the original
  ;;;         conclusion, a list of hypotheses, and informations about the predecessors.
  ;;; Effect: tests whether the hypotheses are applicable to the conclusion and in case they are
  ;;;         creates the resulting gterm and the original conclusion plus hypotheses. Otherwise
  ;;;         the modified conclusion, the origial conclusion (in case it is no equation) and the
  ;;;         hypotheses are used as result of the application of the hypotheses.
  ;;; Value:  ?
  
  (let ((new.gterm (sel=ind.hypotheses.apply (sel=object.gterm object) hypotheses (car termsubsts))) (taf (da-taf.create.zero nil)) succ.object)
    (cond (new.gterm
	   (cond (add.conditions (sel=case.introduce.case.analysis object nil modification add.conditions)))
	   (sel=object.insert.mod.edge 
	    object modification 'simplification
	    (da-gterm.create 'and (nconc (copy-list new.gterm)
					 (cond ((or (not (da-literal.is org.gterm))
						    (not (da-literal.is.negated.equation org.gterm)))
						(list org.gterm)))
					 (LIST (NORM-NORMALIZE.GTERM (DA-GTERM.CREATE 'and hypotheses))))))
	   (setf (sel=object.status object) 'connected.first)
	   (setq succ.object (sel=edge.succ.object (third (assoc nil (sel=object.succs object)))))
	   (prog1 (mapc #'(lambda (sub.form)
			    (sel=object.insert.subproblem.edge succ.object (setq taf (da-taf.create.next taf))
							       (cond ((not (da-literal.is sub.form)) 'simplification) 
								     (t 'resolution.set))))
			new.gterm)
	     (setf (sel=object.status succ.object) 'connected.first)))
	  (t (cond (add.conditions (sel=case.introduce.case.analysis object nil modification add.conditions)))
	     (setf (sel=object.status object) 'connected.first)
	     (sel=object.insert.mod.edge object modification 'simplification
					 (da-gterm.create 
					  'and (nconc (list (da-gterm.copy (sel=object.gterm object)))
						      (cond ((or (not (da-literal.is org.gterm))
								 (not (da-literal.is.negated.equation org.gterm)))
							     (list (da-gterm.copy org.gterm))))
						      (list (NORM-NORMALIZE.GTERM 
							     (DA-GTERM.CREATE 'and hypotheses))))))
	     t))))


(defun sel=ind.hypotheses.apply (conclusion hypotheses termsubsts)

  ;;; Input:    a gterm (the conclusion), the hypothesis and the termsubst-information
  ;;; Effect:   searches for each literal (resp. left/right-hand side of an equation) in
  ;;;           hypothesis a corresponding literal (resp. term) in CONCLUSION, such that
  ;;;           there is a common unifier all theses correspondences.
  ;;; Value:    an object of the type \verb$SEL*IND.APPL$ with the corresponding entries.

  (let* ((vars (smapcar #'(lambda (x) x) #'cddr (car termsubsts)))
	 (adv.hypos (sel=ind.mark.correspondent.literals conclusion hypotheses vars))
	 (hypothesis (car (car adv.hypos)))
	 (substs (second (car adv.hypos)))
	 (sucesses (third (car adv.hypos))))
    (cond (substs
	   (multiple-value-bind (residuum new.substs)
	       (sel=ind.compute.resolvent (list conclusion) (list hypothesis)
					  substs sucesses (cdr adv.hypos))
	     (cond (new.substs (mapcar #'(lambda (form)
					   (uni-subst.apply (car new.substs) form nil 'induction 'induction))
				       residuum))))))))


(defun sel=ind.compute.resolvent (conclusion hypothesis substs sucesses alt)

  ;;; Input:  two list of gterms representing the (partly) decomposed conclusion
  ;;;         and hypotheses.
  ;;; Effect: computes the gterm denoting the resolvent of the conclusion with all the hypotheses
  ;;; Value:  a multiple value of a gterm denoting the residuum and possible instantiations

  (let (add.concl add.hypos residuum total.residuum)
    (cond ((da-literal.is (car hypothesis))
	   (sel=ind.compute.single.resolvent conclusion hypothesis substs sucesses alt))
	  (t (mapc #'(lambda (concl hypo)
		       (cond ((eq 'and (da-gterm.symbol (car conclusion)))
			      (setq add.concl (remove concl (da-gterm.termlist (car conclusion)))))
			     (T (setq add.hypos (remove hypo (da-gterm.termlist (car hypothesis))))))
		       (multiple-value-setq (residuum substs)
			 (sel=ind.compute.resolvent (cons concl (append add.concl (cdr conclusion)))
						    (cons hypo (append add.hypos (cdr hypothesis)))
						    substs sucesses alt))
		       (setq total.residuum (append residuum total.residuum)))
		   (da-gterm.termlist (car conclusion))
		   (da-gterm.termlist (car hypothesis)))
	     (values total.residuum substs)))))


(defun sel=ind.compute.single.resolvent (concl hypo substs sucesses alt)

  (let (new.concl new.substs newest.concl residuum unused.hypos total.residuum
	(subtaf.descrs (getf (da-gterm.attributes (car concl)) 'induction)))
    (setq new.concl (da-gterm.copy (car concl)))
    (mapc #'(lambda (subtaf.descr)
	      (cond ((sel=ind.subtaf.descr.is.successful subtaf.descr (car concl) sucesses)
		     (setq new.concl (sel=ind.replace.subterm new.concl (car hypo) subtaf.descr))
		     (setq subtaf.descrs (remove subtaf.descr subtaf.descrs)))))
	  subtaf.descrs)
    (mapc #'(lambda (subtaf.descr)
	      (cond ((and (sel=ind.subtask.is.open new.concl (third subtaf.descr))
			  (multiple-value-setq (newest.concl residuum new.substs)
			    (sel=ind.search.for.alternative.descr new.concl concl substs subtaf.descr alt)))
		     (setq total.residuum (append residuum total.residuum))
		     (setq new.concl newest.concl)
		     (setq subtaf.descrs (remove subtaf.descr subtaf.descrs))
		     (setq substs new.substs))))
	  subtaf.descrs)
    (push (cond (subtaf.descrs (da-gterm.create 'and (cons new.concl (cons (da-gterm.colourize (car hypo) 'induction 'hypo)
									   (cdr concl)))))
		(t (da-formula.junction.closure 'and (cons new.concl (cdr concl)))))
	  total.residuum)
    (values total.residuum substs)))


(defun sel=ind.subtask.is.open (gterm taf)

  (or (null taf)
      (not (eq 'and (da-gterm.symbol (da-access (cdr taf) gterm))))
      (every #'(lambda (subterm) (not (and (da-formula.is subterm) (da-formula.is.false subterm))))
	     (da-gterm.termlist (da-access (cdr taf) gterm)))))


(defun sel=ind.replace.subterm (concl hypo subtaf.descr)

  ;;; Input:  a part of the conclusion, a part of the hypothesis, and a description where to apply
  ;;;         the hypothesis within the conclusion
  ;;; Effect: applies hypothesis by resolution or paramodulation depending on the subtaf.descr.
  ;;; Value:  the changed part of the conclusion
  ;;; Note:     colors to be inserted for later generalization !!!

  (cond ((eq (car subtaf.descr) 'res)
	 (da-replace (third subtaf.descr) concl (da-literal.false)))	
	(t (da-replace (append (fifth subtaf.descr) (fourth subtaf.descr) (third subtaf.descr))
		       concl (da-gterm.colourize (da-gterm.copy (da-access (da-taf.otherside (fourth subtaf.descr)) hypo))
						 'hypo 'induction)))))


(defun sel=ind.search.for.alternative.descr (new.concl concl substs failed.descr alt)

  (let (hypo residuum new.substs sucesses (taf (car (getf (da-gterm.attributes (car concl)) 'taf))))
    (cond ((some #'(lambda (hypo.subst.subtaf.descr)
		     (setq new.substs (uni-subst.list.merge (second hypo.subst.subtaf.descr) substs))
		     (setq sucesses (third hypo.subst.subtaf.descr))
		     (cond ((and new.substs (sel=ind.subtaf.descr.is.successful failed.descr (car concl) sucesses))
			    (setq hypo (car hypo.subst.subtaf.descr)) 
			    (setq new.concl (sel=ind.replace.subterm new.concl (da-access taf hypo) failed.descr))
			    (multiple-value-setq (residuum new.substs)
			      (sel=ind.refute.remaining.lits (cdr concl) hypo substs sucesses taf)))))
		 alt)
	   (values new.concl residuum new.substs)))))
	    

(defun sel=ind.refute.remaining.lits (concl hypo substs sucesses taf)

  (let (residuum total.residuum)
    (mapc #'(lambda (hypo.part)
	      (multiple-value-setq (residuum substs)
		  (sel=ind.refute.hypo.part (da-formula.junction.open 'and hypo.part) concl substs sucesses))
	      (setq total.residuum (append residuum total.residuum)))
	  (da-formula.junction.open 'or (DA-GTERM.WITHOUT.TAFS hypo taf)))
    (values total.residuum substs)))


(defun sel=ind.refute.hypo.part (hypo.part concl substs sucesses)

  (let (residuum total.residuum new.substs new.concl)
    (cond ((some #'(lambda (hypo)
		     (and (da-literal.is hypo)
			  (some #'(lambda (concl.part)
				    (cond ((and (getf (da-gterm.attributes hypo) 'taf)
						(equal (getf (da-gterm.attributes concl.part) 'taf)
						       (getf (da-gterm.attributes hypo) 'taf)))
					   (multiple-value-setq (residuum new.substs)
					     (sel=ind.compute.single.resolvent 
					      (cons concl.part (remove concl.part concl))
					      (list hypo) substs sucesses nil)))))
				concl)))
		 hypo.part)
	   (values residuum new.substs))
	  ((setq new.concl (find-if #'(lambda (concl.part) (null (getf (da-gterm.attributes concl.part) 'taf))) concl))
	   (cond ((eq (da-gterm.symbol new.concl) 'and)
		  (sel=ind.refute.hypo.part hypo.part (append (da-gterm.termlist new.concl) (remove new.concl concl))
					    substs sucesses))
		 ((eq (da-gterm.symbol new.concl) 'or)
		  (mapc #'(lambda (co)
			    (multiple-value-setq (residuum substs)
			      (sel=ind.refute.hypo.part hypo.part (cons co (remove new.concl concl)) substs sucesses))
			    (setq total.residuum (append residuum total.residuum)))
			  (da-gterm.termlist new.concl))
		  (values total.residuum substs)))))))


(defun sel=ind.subtaf.descr.is.successful (subtaf.descr gterm subtaf.descrs)

  (some #'(lambda (gterm.taf.subtaf)
	    (and (eq (car gterm.taf.subtaf) gterm)
		 (eq (third gterm.taf.subtaf) subtaf.descr)))
	subtaf.descrs))


(defun sel=ind.mark.correspondent.literals (conclusion hypotheses vars)

  ;;; Input::  the manipulated induction conclusion and a list of induction hypotheses
  ;;; Effect:  marks corresponding literals of conclusion and hypotheses by a 
  ;;;          triple: (sign taf org.gterm), where sign is + for hypotheses and - for 
  ;;;          conclusion, taf is the access function for the subterm and org.gterm the
  ;;;          original gterm.
  ;;; Value:   undefined.

  (let ((tafs (da-gterm.literals.with.property (car hypotheses) #'(lambda (lit) lit)))
	total.unifiers adv.hypotheses sucesses concl.lit hypo.lit unifiers)
    (sel=ind.concl.insert.ind.terms conclusion tafs vars)
    (mapc #'(lambda (hypothesis)
	      (setq total.unifiers (list nil))
	      (setq sucesses nil)
	      (mapc #'(lambda (taf)
			(setq concl.lit (da-access taf conclusion))
			(setq hypo.lit (da-access taf hypothesis))
			(setf (getf (da-gterm.attributes hypo.lit) 'taf) (list taf))
			(mapc #'(lambda (subtaf.descr)
				  (setq unifiers
					(cond ((eq (car subtaf.descr) 'res)
					       (uni-literal.unify 
						hypo.lit (da-access (third subtaf.descr) concl.lit) 'opposite))
					      (t (uni-term.unify (da-access (fourth subtaf.descr) hypo.lit)
								 (da-access (append (fifth subtaf.descr)
										    (fourth subtaf.descr)
										    (third subtaf.descr))
									    concl.lit)))))
				  (cond (unifiers (setq total.unifiers (uni-subst.list.merge
									unifiers total.unifiers))
						  (push (list concl.lit taf subtaf.descr) sucesses))))
			      (getf (da-gterm.attributes concl.lit) 'induction)))
		    tafs)
	      (push (list hypothesis total.unifiers sucesses) adv.hypotheses))
	  hypotheses)
    (sort adv.hypotheses #'(lambda (x y) (> (length (third x)) (length (third y)))))))


(defun sel=ind.concl.insert.ind.terms (conclusion tafs vars)

  ;;; Input :  the induction conclusion and a list of term access functions
  ;;;          denoting the positions corresponding to literals in the
  ;;;          hypothesis.
  ;;; Effect : inserts the term-access functions of all inductive arguments into
  ;;;          the 'induction attribute of the corresponding subformula.
  ;;; Value :  undefined

  (mapc #'(lambda (taf)
	    (let ((concl.subformula (da-access taf conclusion)) concl.lit side)
	      (setf (getf (da-gterm.attributes concl.subformula) 'taf) (list taf))
	      (setf (getf (da-gterm.attributes concl.subformula) 'induction)
		    (mapcan #'(lambda (subtaf)
				(setq concl.lit (da-access subtaf concl.subformula))
				(cond ((da-literal.is.negated.equation concl.lit)
				       (setq side (sel=ind.gterm.choose.equation.side concl.lit vars))
				       (mapcar #'(lambda (term.taf)
						   (list 'par taf subtaf side term.taf))
					       (da-gterm.colourful.terms (da-access side concl.lit) 
									 'induction nil)))
				      (t (list (list 'res taf subtaf)))))
			    (da-gterm.literals.with.property
			     concl.subformula
			     #'(lambda (lit)
				 (not (da-colour.is.fade (da-gterm.colour lit 'induction)))))))))
	tafs))


(defun sel=ind.gterm.choose.equation.side (equation ind.vars)

  ;;; Input:  a literal denoting a negated equation
  ;;; Effect: computes which side should be used for weak fertilization.
  ;;; Value:  a taf, denoting the left or right hand side of equation.

  (let ((ex.vars (da-gterm.variables equation))
	(left (car (da-literal.termlist equation)))
	(right (second (da-literal.termlist equation))))
    (cond ((not (da-gterm.tafs left #'(lambda (term) (member term ind.vars :test 'uni-gterm.are.equal))))
	   (da-taf.create.right))
	  ((not (da-gterm.tafs right #'(lambda (term) (member term ind.vars :test 'uni-gterm.are.equal))))
	   (da-taf.create.left))
	  ((and ex.vars (not (intersection (da-gterm.variables right) ex.vars)))
	   (da-taf.create.right))
	  ((and ex.vars (not (intersection (da-gterm.variables left) ex.vars)))
	   (da-taf.create.left))
	  ((null (da-term.termlist left))
	   (da-taf.create.right))
	  ((remove nil (da-gterm.max.faded.gterms (da-access (da-taf.create.left) equation) 'induction))
	   (da-taf.create.right))	   
	  (t (da-taf.create.left)))))



;;;;;-------------------------------------------------------------------------------------------------------------------
;;;;;
;;;;;   Section ? . 1:    Guiding Induction proofs
;;;;;
;;;;;--------------------------------------------------------------------------------------------------------------------


(defrule sel=ind.insert.all.contexts (occ &others replacements colour.key)
 
  ;;; Input  : an rl-object denoting a gterm and a list of termsubstitutions where the left side of a
  ;;;          replacement is a subterm of the right side.
  ;;; Effect : tries to manipulate occ in such a way that all occurrences of some left-hand side term
  ;;;          in one replacement is replaced by the corresponding on the right hand side. I.e. occ is
  ;;;          blown up with some context.
  ;;; Value  : the list of replacements, which are compatible with the manipulation.

  (RIPPLING 0 ("performing one replacement ~A in ~A" 2 1)  ("insert context" (1) 3 nil))
  
  (let (tafs used.terms (environment (uni-environment (cons 'key colour.key))))
    (everyf #'(lambda (term ignore)
		(setq term (da-gterm.copy term))
		(da-gterm.colourize term 'initial colour.key)
		(setq used.terms (sel=ind.preds.of.term term replacements))
		(while (setq tafs (da-gterm.occurs.in.gterm term (rl-object occ) environment environment))
		  (cond ((setq used.terms (sel=context.insert occ (car (sort tafs '> :key 'length))
							      used.terms colour.key 'solved 'failed.to.expand
							      'solved))
			 (setq replacements (sel=ind.termsubst.of.value replacements term used.terms))))))
	    (car replacements))
    replacements))


(defun sel=ind.preds.of.term (term replacements)

  ;;; Input:   a term and a list of termsubstitutions
  ;;; Effect:  searches for all ranges of term in the different termsubstitutions
  ;;; Value:   the list of ranges
  
  (let (wished.term)
    (mapcan #'(lambda (replacement)
		(cond ((setq wished.term (somef #'(lambda (domain.term new.term)
						    (cond ((uni-term.are.equal term domain.term) new.term)))
						replacement))
		       (list wished.term))))
	    replacements)))


(defun sel=ind.termsubst.of.value (replacements term used.terms)

  ;;; Input:   a list of termsubstitutions, a term, and a list of terms
  ;;; Effect:  searches for all termsubstitutions which range of term is
  ;;;          member of \verb$USED.TERMS$.
  ;;; Value:   the list of termsubstitutions

  (let (wished.term)
    (mapcan #'(lambda (replacement)
		(cond ((setq wished.term (somef #'(lambda (domain.term new.term)
						    (cond ((uni-term.are.equal term domain.term) new.term)))
						replacement))
		       (cond ((member wished.term used.terms ':test 'uni-gterm.are.equal)
			      (list replacement))))))
	    replacements)))



;;;;;-------------------------------------------------------------------------------------------------------------------
;;;;;
;;;;;   Section ?       Adjusting contexts around the sinks.
;;;;;
;;;;;--------------------------------------------------------------------------------------------------------------------


(defun sel=ind.adjust.corresponding.sinks (occ taf.pred.sets predset.sinks colour.key)

  (let (lit)
    (mapc #'(lambda (taf)
	      (setq lit (da-access taf (rl-object occ)))
	      (cond ((da-literal.is.negated.equation lit)
		     (mapc #'(lambda (sub.taf)
			       (sel=ind.adjust.corresponding.sinks.for.pred
				occ (append sub.taf (list 1) taf) taf.pred.sets predset.sinks colour.key))
			   (DA-GTERM.COLOURFUL.TERMS (car (da-literal.termlist lit)) colour.key))
		     (mapc #'(lambda (sub.taf)
			       (sel=ind.adjust.corresponding.sinks.for.pred
				occ (append sub.taf (list 2) taf) taf.pred.sets predset.sinks colour.key))
			   (DA-GTERM.COLOURFUL.TERMS (second (da-literal.termlist lit)) colour.key)))
		    (t (sel=ind.adjust.corresponding.sinks.for.pred
			occ taf taf.pred.sets predset.sinks colour.key))))
	  (da-gterm.literal.tafs (rl-object occ)
				 #'(lambda (lit)
				     (and (da-gterm.colour lit colour.key)
					  (not (da-colour.is.fade (da-gterm.colour lit colour.key)))))))))


(defun sel=ind.adjust.corresponding.sinks.for.pred (occ taf taf.pred.sets predset.sinks colour.key)

  (let (pred.sets sinks)
    (rl-with.sub.objects occ taf
			 #'(lambda (sub.occ)
			     (setq pred.sets (cassoc taf taf.pred.sets :test 'equal))
			     (cond ((null (cdr pred.sets))
				    (setq sinks (cassoc (car pred.sets) predset.sinks))
				    (cond ((every #'(lambda (sink.value) (neq (cdr sink.value) 'fail)) sinks)
					   (while (sel=ind.adjust.single.sinks sub.occ sinks colour.key))
					   (sel=context.move.up sub.occ colour.key)))))))))


(defun sel=ind.adjust.single.sinks (occ sinks colour.key)

  (let (sink local.var wished.sink local.taf)
    (some #'(lambda (taf)
	      (setq sink (da-access taf (rl-object occ)))
	      (setq local.var (cond ((setq local.taf (da-gterm.coloured.terms sink 'sink colour.key))
				     (da-access (car local.taf) sink))
				    (t sink)))
	      (setq wished.sink (cassoc local.var sinks :test 'uni-gterm.are.equal))
	      (cond ((and wished.sink (not (uni-gterm.are.equal wished.sink sink)))
		     (sel=ind.adjust.single.sink occ taf wished.sink colour.key))))
	  (da-gterm.or.coloured.terms (rl-object occ) '(sink sink.context) colour.key))))


(defrule sel=ind.adjust.single.sink (occ &others taf wished.sink colour.key)
  
  ;;; Input:  a rl-object denoting a gterm, a list of termsubstitutions and a term to be blown up.
  ;;; Effect: The occurrence of term in occ is blown up to the correspondent right hand side of term
  ;;;         in some replacement.
  ;;; Value:  the list of termsubstitutions, which are compatible with the manipulation.

  (RIPPLING 5 ("trying ~A" 2))
  
  (cond ((sel=context.insert occ taf (list wished.sink) colour.key 'sink.context 'sink))
	((sel=context.insert.by.backward occ taf wished.sink colour.key 'sink.context))))



(defun sel=ind.collect.corresponding.sinks (occ termsubsts colour.key)
  
  ;;; f"ur alle Literale, die gef"arbt sind und die 

  (let (lit potential.applications)
    (setq termsubsts (list (mapcar #'(lambda (replacement)
				       (smapcar #'(lambda (x) x) #'cddr (cdr replacement)))
				   termsubsts)))
    (mapc #'(lambda (taf)
	      (setq lit (da-access taf (rl-object occ)))
	      (cond ((da-literal.is.negated.equation lit)
		     (mapc #'(lambda (sub.taf)
			       (push (cons (append sub.taf (list 1) taf)
					   (sel=ind.corresponding.sinks 
					    (da-access sub.taf (car (da-literal.termlist lit)))
					    termsubsts colour.key))
				     potential.applications))
			   (DA-GTERM.COLOURFUL.TERMS (car (da-literal.termlist lit)) colour.key))
		     (mapc #'(lambda (sub.taf)
			       (push (cons (append sub.taf (list 2) taf)
					   (sel=ind.corresponding.sinks 
					    (da-access sub.taf (second (da-literal.termlist lit)))
					    termsubsts colour.key))
				     potential.applications))
			   (DA-GTERM.COLOURFUL.TERMS (second (da-literal.termlist lit)) colour.key)))
		    (t (push (cons taf (sel=ind.corresponding.sinks lit termsubsts colour.key)) potential.applications))))
	  (da-gterm.literal.tafs (rl-object occ)
				  #'(lambda (lit)
				      (and (da-gterm.colour lit colour.key)
					   (not (da-colour.is.fade (da-gterm.colour lit colour.key)))))))
    (sel=ind.adjust.corresponding.sinks occ potential.applications termsubsts colour.key)))


(defun sel=ind.corresponding.sinks (gterm termsubsts colour.key)

  (let (sinks preds local.var sink all.pred.sink.lists entry)
    (setq sinks (mapcar #'(lambda (taf)
			    (setq sink (da-access taf gterm))
			    (setq local.var (cond ((setq taf (da-gterm.coloured.terms sink 'sink colour.key))
						   (da-access (car taf) sink))
						  (t sink)))
			    (cons local.var sink))
			(da-gterm.or.coloured.terms gterm '(sink.context sink) colour.key)))
    (cond (sink (setq preds (mapcar #'(lambda (taf)
					(da-access taf gterm))
				    (da-gterm.coloured.terms gterm 'solved colour.key)))
		(mapc #'(lambda (pred.sink.list)
			  (cond ((null (set-difference preds (car pred.sink.list) :test #'uni-gterm.are.equal))
				 (push (car pred.sink.list) all.pred.sink.lists)
				 (mapc #'(lambda (localvar.sink)
					   (cond ((setq entry (assoc (car localvar.sink) (cdr pred.sink.list)
								     :test 'uni-gterm.are.equal))
						  (cond ((eq (cdr entry) 'fail))
							((da-gterm.occurs.in.gterm (cdr entry) (cdr localvar.sink))
							 (setf (cdr entry) (cdr localvar.sink)))
							((da-gterm.occurs.in.gterm (cdr localvar.sink) (cdr entry)))
							(t (setf (cdr entry) 'fail))))
						 (t (setf (cdr pred.sink.list) 
							  (cons localvar.sink (cdr pred.sink.list))))))
				       sinks))))
		      termsubsts)))
    all.pred.sink.lists))



;;;;;=========================================================================================================
;;;;;
;;;;;  Chapter 6
;;;;;  ---------
;;;;;
;;;;;  Rippling and other stuff
;;;;;
;;;;;=========================================================================================================


;;;;;-------------------------------------------------------------------------------------------------------------------
;;;;;
;;;;;   Section ? . 1:    Creating Contexts in a gterm
;;;;;
;;;;;--------------------------------------------------------------------------------------------------------------------


(defun sel=context.insert (occ taf wished.terms colour.key solution.colour failure.colour &optional sink.colour)
  
  ;;; Input:  a rl-object and a term-access function denoting a gterm, a list of terms, a
  ;;;         colour key, a colour for the generated context, and a colour for the actual
  ;;;         positions which cannot be blown up to some wished term.
  ;;; Effect: The occurrence in occ is blown up by some member of \verb$wished.terms$
  ;;; Value:  the list of terms, which are generated.
 
  (let ((org.colour (da-gterm.colour (da-access taf (rl-object occ)) colour.key))
	used.wished.terms new.wished.terms tafs actual.expansion wished.tafs)
    (rl-object.changes occ (list (list 'colour.top taf colour.key 'blow.up)) nil nil)
    (while (setq tafs (da-gterm.or.coloured.terms (rl-object occ) '(created.context blow.up) colour.key))
      (setq actual.expansion (da-access (car tafs) (rl-object occ)))
      (cond ((some #'(lambda (type)
		       (some #'(lambda (wished.term)
				 (cond ((setq wished.tafs (da-gterm.occurs.in.gterm
							   actual.expansion wished.term))
					(setq new.wished.terms
					      (cond ((cond (type (sel=context.insert.is.trivial 
								  occ (car tafs) wished.terms colour.key solution.colour 
								  org.colour sink.colour))))
						    (t (setq sel.taf (sel=context.select.appropriate.taf
								      wished.tafs wished.term))
						       (sel=context.insert.by.eqs
							occ (car tafs)
							(da-gterm.symbol (da-access sel.taf wished.term))
							wished.terms colour.key solution.colour org.colour sink.colour
							type)))))))
			     wished.terms))
		   '(t nil))
	     (setq used.wished.terms (union new.wished.terms used.wished.terms)))
	    (t (rl-with.sub.objects occ (car tafs)
		  #'(lambda (sub.occ) 
		      (sel=context.insert.final.colouring sub.occ colour.key failure.colour 
							  failure.colour sink.colour))))))
    used.wished.terms))


(defun sel=context.select.appropriate.taf (tafs gterm)

  ;;; Input :   a list of tafs and a gterm
  ;;; Effect:   selects a taf denoting the immediate supertaf of one of the tafs such 
  ;;;           preferably its sort is identical to its subterm.
  ;;; Value:    the selected taf

  (let ((sort (da-term.sort (da-access (car tafs) gterm))))
    (cdr (cond ((find-if #'(lambda (taf)
			     (and taf (da-sort.is.subsort (da-term.sort (da-access (cdr taf) gterm)) sort)))
			 tafs))
	       (t (car tafs))))))


(defun sel=context.insert.is.trivial (occ occ.taf wished.terms colour.key 
					    solution.colour org.colour sink.colour)

  (cond ((and (cdr occ.taf)
	      (sel=context.insert.enlarge occ (cdr occ.taf) wished.terms colour.key 
					  solution.colour org.colour sink.colour))
	 wished.terms)))


(defrule sel=context.insert.by.eqs (occ &others occ.taf f.symbol wished.terms colour.key 
					solution.colour org.colour sink.colour type)
  
  ;;; Input:  a rl-object denoting a gterm, a taf denoting a subterm t of occ, the original term to be blown up,
  ;;;         a function symbol f which has to be introduced and a list of term substitutions.
  ;;; Effect: applies a C-equation to the subterm of occ denoted by occ.taf such that the result contains a
  ;;;         subterm f(..., t,...) which is also a subterm of the correspondent right-hand side of some
  ;;;         termsubstitution.
  ;;; Value:  the list of termsubstitutions, which are compatible with the manipulation.

  (RIPPLING 5 ("using insertion of ~A to achieve ~A" 3 4))

  (let (used.wished.terms)
    (cond ((DB-MODIFIER.SELECTION
	    (da-term.create f.symbol) 'insert nil
	    #'(lambda (modifier)
		(and (cond (type (da-modifier.input.taf modifier))
			   (t (null (da-modifier.input.taf modifier))))	; use first definitions instead of x = s(p(x))
		     (sel=modifier.test.and.apply
		      modifier occ occ.taf colour.key
		      :test.fct #'(lambda (value)
				    (setq used.wished.terms
					  (sel=context.insert.check.result 
					   value wished.terms colour.key solution.colour 
					   org.colour sink.colour)))))))
	   used.wished.terms))))


(defun sel=context.insert.check.result (resulting.term wished.terms colour.key solution.colour org.colour sink.colour)
  
  ;;; Input:   two terms and a list of termsubstitutions
  ;;; Effect:  Redyes the direct context of a subterm of resulting term coloured by 'blow.up also with
  ;;;          'blow.up resp. 'solved if the this larger subterm is also part of the corresponding right
  ;;;          hand side of some replacement.
  ;;; Value:   the list of termsubstitutions which are used to enlarge the subterm.

  (let (wished.tafs sub.term faded.terms used.wished.terms org.tafs)
    (mapc #'(lambda (taf)
	      (setq sub.term (da-access (cdr taf) resulting.term))
	      (cond ((da-colour.is.fade (da-gterm.colour sub.term colour.key))
		     (cond ((some #'(lambda (wished.term)
				      (cond ((setq wished.tafs (da-gterm.occurs.in.gterm sub.term wished.term))
					     (setq used.wished.terms (adjoin wished.term used.wished.terms)))))
				  wished.terms)
			    (cond ((member nil wished.tafs)
				   (setq org.tafs (da-gterm.coloured.terms sub.term 'blow.up colour.key))
				   (da-gterm.colourize.until sub.term org.tafs solution.colour colour.key)
				   (da-gterm.colour.replace sub.term colour.key 'blow.up 
							    (cond (sink.colour) (t org.colour))))
				  (t (da-gterm.colourize.context sub.term colour.key 'created.context))))
			   (t (push sub.term faded.terms))))))
	  (da-gterm.or.coloured.terms resulting.term '(created.context blow.up) colour.key))
    (cond (used.wished.terms
	   (mapc #'(lambda (s.term) (da-gterm.colourize s.term (da-colour.faded) colour.key)) faded.terms)
	   (sel=GTERM.CHECK.COLOURS resulting.term COLOUR.KEY)
	   used.wished.terms))))


(DEFUN sel=GTERM.CHECK.COLOURS (GTERM COLOUR.KEY)

  (let (result)
    (COND ((AND (NOT (DA-LITERAL.IS GTERM)) (NOT (DA-TERM.IS GTERM)))
	   (MAPC #'(LAMBDA (SUB.TERM) (sel=GTERM.CHECK.COLOURS SUB.TERM COLOUR.KEY)) (DA-GTERM.TERMLIST GTERM)))
	  ((NULL (DA-GTERM.TERMLIST GTERM))
	   (NOT (DA-COLOUR.IS.FADE (da-gterm.colour gterm colour.key))))
	  ((DA-COLOUR.IS.FADE (da-gterm.colour gterm colour.key))
	   (SETQ RESULT NIL)
	   (MAPC #'(LAMBDA (SUB.TERM)
			   (SETQ RESULT (OR (sel=GTERM.CHECK.COLOURS SUB.TERM COLOUR.KEY) RESULT)))
		 (DA-GTERM.TERMLIST GTERM))
	   RESULT)
	  (T (SETQ RESULT T)
	     (MAPC #'(LAMBDA (SUB.TERM)
			     (SETQ RESULT (AND (sel=GTERM.CHECK.COLOURS SUB.TERM COLOUR.KEY) RESULT)))
		   (DA-GTERM.TERMLIST GTERM))
	     (COND ((NULL RESULT) 
		    (DA-GTERM.COLOURIZE gterm (DA-COLOUR.FADED) colour.key)
		    NIL)
		   (T T))))))


(defun sel=context.insert.enlarge (occ taf wished.terms colour.key solution.colour org.colour sink.colour)
  
  ;;; Input:   two terms and a list of termsubstitutions
  ;;; Effect:  Redyes the direct context of a subterm of resulting term coloured by 'blow.up also with
  ;;;          'blow.up resp. 'solved if the this larger subterm is also part of the corresponding right
  ;;;          hand side of some replacement.
  ;;; Value:   the list of termsubstitutions which are used to enlarge the subterm.
  
  (let (wished.tafs faded.terms used.wished.terms)
    (mapc #'(lambda (s.taf)
	      (rl-with.sub.objects occ (append s.taf taf)
		 #'(lambda (sub.occ)
		     (cond ((and (da-colour.is.fade (da-gterm.colour (rl-object sub.occ) colour.key))
				 (some #'(lambda (wished.term)
					   (cond ((setq wished.tafs (da-gterm.occurs.in.gterm
								     (rl-object sub.occ) wished.term))
						  (setq used.wished.terms (adjoin wished.term used.wished.terms)))))
				       wished.terms))
			    (cond ((member nil wished.tafs)
				   (sel=context.insert.final.colouring sub.occ colour.key solution.colour
								       org.colour sink.colour))
				  (t (rl-object.changes sub.occ (list (list 'colour.until nil 
									    (da-gterm.colourful.terms (rl-object sub.occ)
												      colour.key)
									    colour.key 'created.context))
							nil nil))))
			   ((eq (da-gterm.colour (rl-object sub.occ) colour.key) solution.colour))
			   (t (push (append s.taf taf) faded.terms))))))
	  (remove-duplicates (mapcar #'cdr (da-gterm.or.coloured.terms (da-access taf (rl-object occ)) 
								       '(created.context blow.up) colour.key))
			     :test 'equal))
    (cond (used.wished.terms
	   (cond (faded.terms (rl-object.changes occ (mapcar #'(lambda (s.taf) 
								 (list 'colour.all s.taf colour.key (da-colour.faded)))
							     faded.terms)
						 nil nil)))
	   used.wished.terms))))


(defun sel=context.insert.final.colouring (occ colour.key created.colour org.colour sink.colour)

  (let ((org.tafs (da-gterm.coloured.terms (rl-object occ) 'blow.up colour.key)))
    (rl-object.changes occ
		       (cons (list 'colour.until nil org.tafs colour.key created.colour)
			     (mapcar #'(lambda (org.taf)
					 (list 'colour.top org.taf colour.key (cond (sink.colour) (t org.colour))))
				     org.tafs))
		       nil nil)))


(defun sel=context.insert.by.backward (occ taf wished.term colour.key sink.colour)

  (let (result gterm2 mod.val gterm1 mod target.term (sub.term (da-access taf (rl-object occ))))
    (setq gterm2 (da-gterm.copy (rl-object occ) t nil))
    (setq gterm2 (cond ((da-term.is (rl-object occ)) (da-gterm.copy (rl-object occ) t nil))
		       (t (norm-normalize.gterm (da-formula.negate (da-gterm.copy (rl-object occ) t nil))))))
    (da-gterm.colourize gterm2 'skeleton colour.key)
    (setq mod.val (da-gterm.copy wished.term t nil))
    (da-gterm.colourize mod.val (da-colour.faded) colour.key)
    (mapc #'(lambda (staf) (da-gterm.colourize (da-access staf mod.val) 'skeleton colour.key))
	  (da-gterm.occurs.in.gterm sub.term mod.val))
    (setq gterm2 (da-replace taf gterm2 mod.val))
    (setq mod (rl-with.problem gterm2 'gterm #'(lambda (sub.occ)
						 (cond ((setq result (sel=context.remove sub.occ colour.key))
							(setq gterm1 (da-gterm.copy (rl-object sub.occ))))))))
    (cond ((eq result 'success)
	   (setq target.term (da-gterm.copy (rl-object occ)))
	   (setq mod.val (da-gterm.copy wished.term t nil))
	   (da-gterm.colourize mod.val sink.colour colour.key)
	   (mapc #'(lambda (staf) (da-replace staf mod.val (da-gterm.copy sub.term)))
		 (da-gterm.occurs.in.gterm sub.term mod.val))
	   (setq target.term (da-replace taf target.term  mod.val))
	   (cond ((da-term.is (rl-object occ))
		  (rl-object.change occ (da-gterm.copy gterm1) nil "reform.")
		  (sel=context.reverse.mods occ gterm1 mod)
		  (rl-object.change occ target.term nil ""))
		 (t (rl-object.change occ target.term nil "reform." 
				      (sel=edge.subst.compute mod))))
	   t))))


;;;;;-------------------------------------------------------------------------------------------------------------------
;;;;;
;;;;;   Section ? . 2:    Moving Contexts to top-level
;;;;;
;;;;;--------------------------------------------------------------------------------------------------------------------


(defrule sel=context.move.up.backtrack (occ colour.key)

  (RIPPLING 0 ("moving contexts up in ~A" 1) ("ripple out" (1) 2 nil))

  (eq 'success (sel=context.move.up.1 occ colour.key)))



(defrule sel=context.move.up (occ colour.key)

  (RIPPLING 0 ("moving contexts up in ~A" 1) ("ripple out" (1) 2 nil))

  (sel=context.move.up.1 occ colour.key))


(defrule sel=context.move.up.1 (occ &others colour.key)
  
  ;;; Input:   a rl-object denoting a gterm
  ;;; Effect:  tries to move all contexts occurring in occ to top-level.
  ;;; Value:   an sexpression =/ nil.

  (RIPPLING 10 ("moving contexts up in ~A" 1) ("ripple out" (1) 2 nil))

  (let ((result 'success))
    (cond ((some #'(lambda (taf)
		     (cond ((DA-TAF.IS.TOP.LEVEL taf (rl-object occ)) nil)
			   ((or (sel=context.move.up.by.taut occ taf colour.key)
				(sel=context.remove.by.ceq occ taf colour.key nil)
				(sel=context.move.up.by.ceq occ taf colour.key)
				(and (eq sel*refutation.depth 0)
				     (sel=context.remove.by.identity occ taf colour.key))))
			   (T (setq result 'fail)
			      nil)))
		 (da-gterm.max.faded.gterms (rl-object occ) colour.key))
	   (setq result (sel=context.move.up.1 occ colour.key))))
    result))


(defrule sel=context.remove (occ &others colour.key)
  
  ;;; Input:   a rl-object denoting a gterm
  ;;; Effect:  tries to remove all contexts occurring in occ
  ;;; Value:   an sexpression =/ nil.

  (RIPPLING 0 ("removing contexts in ~A" 1) ("remove context" (1) 2))
  
  (sel=context.remove.1 occ colour.key))


(defrule sel=context.remove.1 (occ &others colour.key)

  (RIPPLING 10 ("removing contexts in ~A" 1) ("remove context" (1) 2))
  
  (let ((result 'success))
    (cond ((some #'(lambda (taf)
		     (cond ((or (sel=context.remove.by.ceq occ taf colour.key t)
				(and (not (DA-TAF.IS.TOP.LEVEL taf (rl-object occ)))
				     (sel=context.move.up.by.ceq occ taf colour.key))
				(and (eq sel*refutation.depth 0)
				     (sel=context.remove.by.identity occ taf colour.key))))
			   (T (setq result 'fail)
			      nil)))
		 (da-gterm.max.faded.gterms (rl-object occ) colour.key))
	   (setq result (sel=context.remove.1 occ colour.key))))
    result))


(defrule sel=context.move.up.by.ceq (occ &others taf colour.key)
  
  ;;; Input:   a rl-object denoting a gterm and a term-access-function denoting contexts in occ
  ;;; Effect:  applies an appropriate C-equation such that a context moves upside.
  ;;; Value:   the term-access-function of the changed subterm.

  (RIPPLING 5 ("at the position ~A using C-equations" 2))
  
  (or (DB-MODIFIER.SELECTION (da-access taf (rl-object occ)) 'move.up nil
			     #'(lambda (modifier)
				 (sel=modifier.test.and.apply modifier occ taf colour.key)))
      (sel=context.move.aside.and.away occ taf colour.key 'move.up nil)))


(defrule sel=context.remove.by.ceq (occ &others taf colour.key search.inside)
  
  ;;; Input:   a rl-object denoting a gterm and a term-access-function denoting contexts in occ
  ;;; Effect:  applies an appropriate C-equation such that a context moves upside.
  ;;; Value:   the term-access-function of the changed subterm.

  (RIPPLING 5 ("at the position ~A using C-equations" 2))
  
  (or (DB-MODIFIER.SELECTION (da-access taf (rl-object occ)) 'remove nil
			     #'(lambda (modifier)
				 (sel=modifier.test.and.apply modifier occ taf colour.key)))
      (sel=context.move.aside.and.away occ taf colour.key 'remove search.inside)))


(defrule sel=context.move.up.by.taut (occ &others taf colour.key)
  
  ;;; Input:   a rl-object denoting a gterm and a term-access-function denoting a contexts in occ
  ;;; Effect:  tries to apply the tautology rule to the denoted subterm
  ;;; Value:   T, iff the rule was applied.

  (RIPPLING 5 ("at the position ~A using tautologies" 2))
  
  (rl-with.sub.objects 
   occ (cdr taf)
   #'(lambda (sub.occ)
       (cond ((da-term.is (rl-object sub.occ))
	      (let ((argument (nth (1- (car taf)) (da-gterm.termlist (rl-object sub.occ)))) (counter 0) all.sinks)
		(cond ((and (eq (da-term.symbol (rl-object sub.occ))
				(da-term.symbol argument))
			    (every #'(lambda (arg1 arg2)
				       (incf counter)
				       (cond ((eql counter (car taf)))
					     (t (and (da-gterm.is.fade arg2 colour.key)
						     (or (uni-term.are.equal arg1 arg2
									     (uni-environment (cons 'key colour.key))
									     (uni-environment (cons 'key colour.key)))
							 (cond ((member (da-gterm.colour arg1 colour.key) '(sink sink.context))
								(push counter all.sinks))))))))
				   (da-term.termlist (rl-object sub.occ))
				   (da-term.termlist argument)))	        
		       (rl-object.change sub.occ (sel=ind.context.term.create (rl-object sub.occ) (car taf) all.sinks colour.key)
					 nil "tautology")
		       t))))))))

(defun sel=ind.context.term.create (term pos all.sinks colour.key)

  (let ((sub.termlist (da-term.termlist (nth (1- pos) (da-term.termlist term))))
	(counter1 0) (counter2 0))
    (da-term.create (da-term.symbol term)
		    (mapcar #'(lambda (arg1 arg2)
				(incf counter1)
				(cond ((eql counter1 pos)
				       (da-term.create (da-term.symbol term)
						       (mapcar #'(lambda (arg1 arg2)
								   (incf counter2)
								   (cond ((eql counter2 pos) arg2)
									 ((member counter2 all.sinks)
									  (setq arg2 (da-gterm.copy arg2))
									  (da-gterm.colourize arg2 'sink colour.key)
									arg2)
									 (t (da-gterm.copy arg1))))
							       (da-term.termlist term)
							     sub.termlist)
						       (da-term.colours term)))
				      ((member counter1 all.sinks)
				       (setq arg1 (da-gterm.copy arg1))
				       (da-gterm.colourize arg1 (da-colour.faded) colour.key)
				       arg1)
				      (t (da-gterm.copy arg2))))
			    (da-term.termlist term)
			    sub.termlist)
		    (da-term.colours (nth (1- pos) (da-term.termlist term))))))


(defun sel=context.move.aside.and.away (occ taf colour.key type search.inside)
  
  ;;; Edited    : 06.04.1994
  ;;; Input     : an object, a taf to a context and a colour.key
  ;;; Effect    : tries to apply a move.aside modifier and a \verb$TYPE$ modifier
  ;;; Value     : an sexp =/= nil, iff it was succesfull; NIL otherwise
  ;;; Note      : /

  (DB-MODIFIER.SELECTION 
   (da-access taf (rl-object occ)) 'move.aside nil
   #'(lambda (move.aside.modifier)
       (sel=context.move.aside.and.away.1
	occ taf colour.key move.aside.modifier search.inside
	(DB-MODIFIER.COLLECTION
	 (da-access taf (rl-object occ)) type nil
	 #'(lambda (move.up.modifier)
	     (cond ((uni-term.match (da-modifier.input move.up.modifier)
				    (da-modifier.value move.aside.modifier))
		    (list move.up.modifier)))))))))


(defrule sel=context.move.aside.and.away.1 (occ &others taf colour.key move.aside.modifier search.inside 
						move.up.modifiers)
  
  ;;; Edited    : 06.04.1994
  ;;; Input     : an object, a taf to a context, a colour.key, a move.aside and a move.up modifier
  ;;; Effect    : tries to apply the move.aside modifier and the move.up modifier
  ;;; Value     : an sexp =/= nil, iff it was succesfull; NIL otherwise
  ;;; Note      :/

  (RIPPLING 5 ("moving context aside and up in ~a ..." 1))

  (let ((new.apply.taf (da-taf.compose.two.tafs
			(da-taf.super.taf taf (da-taf.length (da-cmodifier.input.taf move.aside.modifier)))
			(car (da-cmodifier.value.taf move.aside.modifier)))))
    (and (sel=modifier.test.and.apply move.aside.modifier occ taf colour.key)
	 (or (some #'(lambda (move.up.modifier)
		       (sel=modifier.test.and.apply move.up.modifier occ new.apply.taf colour.key))
		   move.up.modifiers)
	     (and search.inside (sel=context.remove.inside occ new.apply.taf colour.key))))))


(defrule sel=context.remove.inside (occ taf colour.key)

  (RIPPLING 5 ("moving context inside and away in ~a ..." 1))

  (some #'(lambda (s.taf)
	      (setq s.taf (da-taf.create.zero s.taf))
	      (some #'(lambda (term)
			(declare (ignore term))
			(setq s.taf (da-taf.create.next s.taf))
			(sel=context.remove.inside.taf occ taf s.taf colour.key))
		    (da-gterm.termlist (da-access taf (rl-object occ)))))
	  (da-gterm.colourful.terms (da-access taf (rl-object occ)) colour.key taf)))


(defrule sel=context.remove.inside.taf (occ context.taf target.taf colour.key)

  (RIPPLING 5 ("moving context inside to ~A in ~a" 3 1))

  (and (sel=context.move.down.to.taf occ context.taf target.taf colour.key (da-colour.faded))
       (sel=context.remove.below.taf occ context.taf colour.key)))


(defrule sel=context.remove.below.taf (occ context.taf colour.key)
 
 (RIPPLING 5 ("removing context inside ~a" 1))
 
 (let ((tafs (da-gterm.max.faded.gterms (da-access context.taf (rl-object occ)) colour.key context.taf)))
    (cond ((null tafs) t)
	  ((some #'(lambda (taf)
		     (sel=context.remove.by.ceq occ taf colour.key nil))
		 tafs)
	   (sel=context.remove.below.taf occ context.taf colour.key)))))



(defrule sel=context.remove.by.identity (occ &others taf colour.key)

  (RIPPLING 5 ("at the position ~A using identity" 2))
  
  (let* ((gterm (da-access taf (rl-object occ)))
	 (symbol (da-gterm.symbol (da-access taf (rl-object occ)))) 
	 (sel*refutation.depth (1+ sel*refutation.depth)) result id id.symbol context.pos id.modifier)
    (cond ((and (da-function.is symbol)
		(setq id (car (getf (da-function.attributes symbol) 'identity))))
	   (cond ((setq context.pos (position-if #'(lambda (term) (null (da-gterm.colourful.terms term colour.key)))
						 (da-gterm.termlist gterm)))
		  (setq context.pos (list (incf context.pos)))
		  (setq id.symbol (car (da-attribute.arguments id)))
		  (setq id.modifier (caar (third (assoc (third (da-attribute.arguments id))
						       (getf (da-gterm.attributes (da-attribute.justification id)) 'modframes)
						       :test 'equal))))
		  (cond ((or (equal context.pos (second (da-attribute.arguments id)))
			     (da-symbol.has.attribute symbol 'commutative))
			 (db-modifier.selection (da-term.create (car (da-attribute.arguments id))) 'top.level nil
				  #'(lambda (modifier)
				      (cond ((and (null (da-modifier.condition modifier))
						  (da-gterm.occurs.in.gterm (da-access context.pos gterm) 
									    (da-modifier.value modifier)))
					     (setq result (sel=context.remove.by.identity.and.mod 
							   occ (append context.pos taf) modifier id.modifier
							   id.symbol))))))
			 result))))))))


(defrule sel=context.remove.by.identity.and.mod (occ &others taf reduce.modifier id.modifier id.symbol)

  (RIPPLING 2 ("enabling" 1) ("enable" (1) nil (4)))

  (let (target.gterm (inverse.reduce.modifier (da-modifier.inverse reduce.modifier)))
    (cond ((setq target.gterm
		 (sel=context.remove.by.identity.and.mod.1 occ taf inverse.reduce.modifier id.symbol))
	   (rl-object.change occ target.gterm nil id.modifier)
	   t))))


(defrule sel=context.remove.by.identity.and.mod.1 (occ &others taf reduce.modifier id.symbol)

  (RIPPLING 2 ("enabling" 1) ("enable" (1) nil (3)))
 
  (let (result gterm2 mod.val gterm1 target.gterm mod gterm3)
    (setq gterm3 (da-gterm.copy (rl-object occ)))
    (setf (da-gterm.symbol (da-access taf gterm3)) id.symbol)
    (setq gterm2 (da-gterm.copy (rl-object occ)))
    (da-gterm.colourize gterm2 'skeleton 'id.blow.up)
    (setq mod.val (da-gterm.copy (da-modifier.input reduce.modifier) t nil))
    (da-gterm.colourize mod.val (da-colour.faded) 'id.blow.up)
    (mapc #'(lambda (staf) (da-gterm.colourize (da-access staf mod.val) 'skeleton 'id.blow.up))
	  (da-gterm.occurs.in.gterm (da-access taf gterm2) mod.val))
    (setq gterm2 (da-replace taf gterm2 mod.val))
    (setq mod (rl-with.problem gterm2 
			       'gterm #'(lambda (sub.occ)
					  (cond ((setq result (sel=context.remove sub.occ 'id.blow.up))
						 (setq gterm1 (da-gterm.copy (rl-object sub.occ))))))))
     (cond ((eq result 'success)
	    (setq target.gterm (da-replace (cdr taf) (da-gterm.copy (rl-object occ))
					   (da-gterm.copy (da-access (da-taf.otherside taf) (rl-object occ)))))
	    (rl-object.change occ (da-gterm.copy gterm1) nil "Start RE")
	    (sel=context.reverse.mods occ gterm1 mod)
	    (rl-object.change occ (rl-object occ) nil "End RE")
	    (rl-object.change occ gterm3 nil reduce.modifier)
	    target.gterm))))


(defrule sel=context.reverse.mods (occ &others gterm modification)

  (RIPPLING 3 ("insert context" 1) ("insert context" (1) 'id.blow.up nil))

  (sel=context.reverse.mods.1 occ gterm modification))


(defun sel=context.reverse.mods.1 (occ gterm modification)

  (let (modifier tafs taf new.gterm)
    (cond ((null modification) gterm)
	  (t (setq gterm (sel=context.reverse.mods.1 occ gterm (cdr modification)))
	     (multiple-value-setq (gterm tafs)
				  (rl=modification.change.context gterm (car modification) t))
	     (setq modifier (sel=mod.modifier (car modification)))
	     (cond ((da-modifier.is modifier) 
		    (setq modifier (da-modifier.inverse modifier))))
	     (setq taf (DA-TAF.COMMON.TAF tafs))
	     (setq new.gterm (da-gterm.copy (da-access taf gterm)))
	     (rl-object.change occ new.gterm taf modifier)
	     gterm))))


;;;;;--------------------------------------------------------------------------------------------------------------------
;;;;;
;;;;;   Section ? . 3:    Moving contexts to some sink
;;;;;
;;;;;--------------------------------------------------------------------------------------------------------------------


(defrule sel=context.move.down (occ &others tafs colour.key solution.colour ignore.top.level)
  
  ;;; Input:   a rl-object denoting a gterm and a sets of variables denoting possible locations for context
  ;;; Effect:  tries to move all contexts in occ to some sinks in set of sinks.
  ;;; Value:   T iff the context has been moved to the sinks.

  (RIPPLING 0 ("moving context to a sink in ~A" 1) ("ripple-in" (1) 3 nil))

  (let (result org.colour) 
    (cond ((every #'(lambda (context.taf)
		      (and ignore.top.level (da-taf.is.top.level context.taf (rl-object occ))))
		  tafs)
	   'success)
	  (t (rl-object.changes occ (mapcar #'(lambda (taf)
						(setq org.colour (da-gterm.colour (da-access taf (rl-object occ)) colour.key))
						(list 'colour.top taf colour.key 'sink))
					    tafs)
				nil nil)
	     (cond ((setq result (sel=context.move.down.1 occ colour.key solution.colour ignore.top.level))
		    (rl-object.changes occ (mapcar #'(lambda (taf)
						       (list 'colour.top taf colour.key org.colour))
						   (da-gterm.colourful.terms (rl-object occ) 'sink colour.key))
				       nil nil)
		    result))))))


(defrule sel=context.move.down.1 (occ &others colour.key solution.colour ignore.top.level)

  (RIPPLING 10 ("moving context to a sink in ~A" 1))
  
  (let (org.colour int.colour)
    (cond ((every #'(lambda (context.taf)
		      (and ignore.top.level (da-taf.is.top.level context.taf (rl-object occ))))
		  (da-gterm.max.faded.gterms (rl-object occ) colour.key))
	   'success)
	  ((some #'(lambda (sink.taf)
		     (setq org.colour (da-gterm.colour (da-access sink.taf (rl-object occ)) colour.key))
		     (setq int.colour (cond ((eq org.colour 'sink) 'target.sink)
					    (t 'target.sink.context)))
		     (rl-object.changes occ (list (list 'colour.top sink.taf colour.key int.colour))
					nil nil)
		     (prog1 (sel=context.move.to.target.sink occ colour.key solution.colour ignore.top.level)
		       (rl-object.changes occ (mapcar #'(lambda (s.taf) 
							  (list 'colour.top s.taf colour.key org.colour))
						      (da-gterm.coloured.terms (rl-object occ) int.colour colour.key))
					  nil nil)))
		 (da-gterm.or.coloured.terms (rl-object occ) '(sink sink.context) colour.key))
	   (sel=context.move.down.1 occ colour.key solution.colour ignore.top.level)))))


(defrule sel=context.move.to.target.sink (occ &others colour.key solution.colour ignore.top.level)

  (RIPPLING 5 ("move to target sink"))
  
  (let (sink.taf result other.result)
    (setq sink.taf (car (da-gterm.coloured.terms (rl-object occ) 'target.sink colour.key)))
    (cond ((some #'(lambda (context.taf)
		     (cond ((and (not ignore.top.level) (da-taf.is.top.level context.taf (rl-object occ))) nil)
			   ((da-tafs.are.independent sink.taf context.taf)
			    (setq result (sel=context.move.aside.to.taf occ context.taf sink.taf colour.key)))
			   ((some #'(lambda (colour.taf)
				      (cond ((da-taf.is.subtaf colour.taf sink.taf)
					     (setq result (sel=context.move.down.to.taf
							   occ (da-taf.super.taf colour.taf) sink.taf
							   colour.key solution.colour)))))
				  (da-gterm.max.coloured.gterms (da-access context.taf (rl-object occ))
								colour.key context.taf)))))
		 (da-gterm.max.faded.gterms (rl-object occ) colour.key))
	   (setq other.result (sel=context.move.to.target.sink occ colour.key solution.colour ignore.top.level))
	   (cond ((eq other.result 'success) (setq result 'success)))))
    result))


(defrule sel=context.move.single.to.target.sink (occ &others colour.key solution.colour ignore.top.level)

  (RIPPLING 5 ("move to target sink in ~A" 1))
  
  (let (sink.taf result)
    (setq sink.taf (car (da-gterm.coloured.terms (rl-object occ) 'target.sink colour.key)))
    (cond ((some #'(lambda (context.taf)
		     (cond ((and (not ignore.top.level) (da-taf.is.top.level context.taf (rl-object occ))) nil)
			   ((da-tafs.are.independent sink.taf context.taf)
			    (setq result (sel=context.move.aside.to.taf occ context.taf sink.taf colour.key)))
			   ((some #'(lambda (colour.taf)
				      (cond ((da-taf.is.subtaf colour.taf sink.taf)
					     (setq result (sel=context.move.down.to.taf
							   occ (da-taf.super.taf colour.taf) sink.taf
							   colour.key solution.colour)))))
				  (da-gterm.max.coloured.gterms (da-access context.taf (rl-object occ))
								colour.key context.taf)))))
		 (reverse (da-gterm.max.faded.gterms (rl-object occ) colour.key)))
	   (cond ((eq result 'changed)
		  (setq result (sel=context.move.single.to.target.sink
				occ colour.key solution.colour ignore.top.level))))))
    result))


(defrule sel=context.move.aside.to.taf (occ &others context.taf sink.taf colour.key)

  (RIPPLING 0 ("selecting position ~A" 2) ("ripple-aside" (1) 4 nil))
  
  ;;; Input:   a rl-object denoting a gterm and a sets of variables denoting possible locations for context
  ;;; Effect:  tries to move the top-level context of occ into the position denoted by target.taf.
  ;;; Value :  ?

  (let ((context.gterm (da-access context.taf (rl-object occ))))
    (cond ((DB-MODIFIER.SELECTION
	    context.gterm 'move.aside nil
	    #'(lambda (modifier)
		(sel=modifier.test.and.apply modifier occ context.taf colour.key :value.taf sink.taf)))
	   'changed))))


(defrule sel=context.move.down.to.taf (occ &others context.taf sink.taf colour.key solution.colour)

  (RIPPLING 0 ("selecting position ~A" 2) ("ripple-in" (1) 4 nil))
  
  ;;; Input:   a rl-object denoting a gterm and a sets of variables denoting possible locations for context
  ;;; Effect:  tries to move the top-level context of occ into the position denoted by target.taf.
  ;;; Value :  ?

  (let ((context.gterm (da-access context.taf (rl-object occ))))
    (cond ((and (da-taf.is.subtaf context.taf sink.taf)
		(member (DA-TAF.DIFFERENCE.OF.TWO.TAFS sink.taf context.taf)
			(da-gterm.colourful.terms context.gterm colour.key)
			:test #'(lambda (x y) (da-taf.are.equal x y))))
	   (da-gterm.colourize.context context.gterm colour.key solution.colour)
	   'success)
	  ((DB-MODIFIER.SELECTION context.gterm 'move.down nil
				  #'(lambda (modifier)
				      (sel=modifier.test.and.apply modifier occ context.taf colour.key :value.taf sink.taf)))
	   'changed))))


(defrule sel=context.move.down.with.coordination (occ &others sink.colours colour.key coordinated)
  
  ;;; Input:   a rl-object denoting a gterm and a sets of variables denoting possible locations for context
  ;;; Effect:  tries to move all contexts in occ to some sinks in set of sinks.
  ;;; Value:   T iff the context has been moved to the sinks.

  (RIPPLING 0 ("moving context to a sink in ~A" 1) ("ripple-in" (1) 3))

  (let (result)
    (cond ((not (da-colour.is.fade (da-gterm.colour (rl-object occ) colour.key)))
	   coordinated)
	  ((some #'(lambda (sink.colour.set)
		     (some #'(lambda (sink.colour)
			       (setq result (sel=context.move.to.common.sinks
					     occ sink.colour (car sink.colour.set) colour.key coordinated)))
			   (car sink.colour.set)))
		 sink.colours)
	   (sel=context.move.down.with.coordination occ sink.colours colour.key result)))))


(defrule sel=context.move.to.common.sinks (occ &others sink.colour sink.colour.set colour.key coordinated)

  (EQ 5 ("moving contexts into some sink"))

  (let ((sink.taf (car (da-gterm.coloured.terms (rl-object occ) sink.colour colour.key))))
    (rl-object.changes occ (list (list 'colour.top sink.taf colour.key 'target.sink)) nil nil)
    (cond ((sel=context.move.single.to.target.sink occ colour.key 'temp.sink.context t)
	   (sel=context.coordinate.move.down occ sink.colour sink.colour.set colour.key coordinated)))))


(defun sel=context.coordinate.move.down (occ sink.colour sink.colour.set colour.key coordinated)

  (let (result mods value tafs gterm)
    (cond ((null (cdr sink.colour.set))
	   (setq tafs (da-gterm.coloured.terms (rl-object occ) 'temp.sink.context colour.key))
	   (rl-object.changes occ (list (list 'colour.all (car tafs) colour.key sink.colour)) nil nil)
	   (cons (list sink.colour.set (da-access (car tafs) (rl-object occ))) coordinated))
	  (t (setq gterm (da-access (car (da-gterm.colourful.terms (rl-object occ) colour.key)) (rl-object occ)))
	     (cond ((multiple-value-setq (result mods)
			(sel=context.replace.sinks.and.move.out (da-gterm.copy gterm) sink.colour.set colour.key))
		    (cond ((setq tafs (da-gterm.occurs.in.gterm result (rl-object occ)))
			   (multiple-value-setq (gterm value)
			       (sel=context.replace.sinks.by.context
				(da-gterm.copy gterm) sink.colour.set sink.colour colour.key))
			   (rl-object.change occ gterm (car tafs)
					     "by equality handling" (car (sel=edge.subst.compute mods))
					     nil)   ; mods
			   (cons (list sink.colour.set value) coordinated)))))))))


(defun sel=context.replace.sinks.and.move.out (gterm sink.colours colour.key)

  ;;; Input:  a gterm with no contexts, a list of tafs denoting the same term and
  ;;;         a gterm
  ;;; Effect: inserts gterm at each position of \verb$OCC$ denoted by \verb$TAFS$ and tries
  ;;;         to move the contexts to top-level
  ;;; Value:  a multiple-value: the resulting gterm and a modification chain denoting the
  ;;;         modification.

  (let (result mods context.tafs context tafs new.context)
    (setq context.tafs (da-gterm.coloured.terms gterm 'temp.sink.context colour.key))
    (setq context (da-gterm.copy (da-access (car context.tafs) gterm)))
    (da-gterm.colour.replace context colour.key 'temp.sink.context (da-colour.faded))
    (mapc #'(lambda (sink.colour)
	      (setq tafs (da-gterm.coloured.terms gterm sink.colour colour.key))
	      (cond ((and tafs (not (da-taf.is.subtaf (car context.tafs) (car tafs))))
		     (setq new.context (da-gterm.copy context))
		     (da-gterm.colour.replace new.context colour.key 'target.sink sink.colour)
		     (setq gterm (da-replace (car tafs) gterm new.context)))))
	  sink.colours)
    (setq mods (rl-with.problem gterm 'gterm
				#'(lambda (occ)
				    (cond ((eq 'success (sel=context.move.up occ colour.key))
					   (setq result (rl-object occ)))))))
    (cond (result (values result mods)))))


(defun sel=context.replace.sinks.by.context (gterm sink.colour.set colour colour.key)

  (let (context.tafs context tafs new.context)
    (setq context.tafs (da-gterm.coloured.terms gterm 'temp.sink.context colour.key))
    (setq context (da-gterm.copy (da-access (car context.tafs) gterm)))
    (da-gterm.colourize (da-access (car context.tafs) gterm) colour colour.key)
    (da-gterm.colour.replace context colour.key 'temp.sink.context (da-colour.faded))
    (mapc #'(lambda (sink.colour)
	      (cond ((neq sink.colour colour)
		     (setq tafs (da-gterm.coloured.terms gterm sink.colour colour.key))
		     (setq new.context (da-gterm.copy context))
		     (da-gterm.colourize new.context sink.colour colour.key)
		     (setq gterm (da-replace (car tafs) gterm new.context)))))
	  sink.colour.set)
    (values gterm (da-access (car context.tafs) gterm))))




;;;;;=========================================================================================================
;;;;;
;;;;;  Chapter ?
;;;;;  ---------
;;;;;
;;;;;  Equality handling, Adapting and Instantiation of two gterms
;;;;;
;;;;;=========================================================================================================


(defrule sel=equalize.gterms (occ1 occ2)

  ;;; Input :  two occurrences
  ;;; Effect:  tries to instantiate and equalize both gterm with the help of the given database
  ;;; Value:   t iff both gterms have been successfully adapted.

  (EQ 0 ("equalizing ~A and ~A" 1 2) ("equalize" (1 2) col nil))

  (cond ((sel=gterms.are.different (rl-object occ1) (rl-object occ2)) nil)
	(T (da-gterm.colourize (rl-object occ1) (da-colour.faded)  sel*actual.colour)
	   (da-gterm.colourize (rl-object occ2) (da-colour.faded)  sel*actual.colour)
	   (let ((sel*eq.colours 0))
	     (cond ((sel=gterms.are.unifiable occ1 occ2)
		    (sel=gterms.insert.eq.bindings occ1 occ2))
		   ((And (sel=eq.inherit.induction.information occ1 occ2)
			 (sel=eq.adapt.skolems occ1 occ2)
			 (sel=eq.equalize.with.subterms occ1 occ2)
			 (sel=eq.equalize.top.level occ1 occ2))
		    (sel=gterms.insert.eq.bindings occ1 occ2)))))))
  


;;;;;-------------------------------------------------------------------------------------------------------------------
;;;;;
;;;;;   Section ? :    equality test of two gterms (ground and unification)
;;;;;
;;;;;--------------------------------------------------------------------------------------------------------------------



(defun sel=eq.adapt.skolems (occ1 occ2)

  (let ((sko1 (da-gterm.functions (rl-object occ1) 'skolem))
	(sko2 (da-gterm.functions (rl-object occ2) 'skolem))
	diff)
    (cond ((some #'(lambda (func)
		     (DB-MODIFIER.SELECTION
		      (da-term.create func) 'dismset nil
		      #'(lambda (modifier)
			  (cond ((subsetp (da-gterm.functions (da-modifier.value modifier) 'skolem) sko2)
				 (sel=modifier.try.to.apply modifier occ1))))))
		 (set-difference sko1 sko2))
	   (sel=eq.adapt.skolems occ1 occ2)))
    t))



(defun sel=eq.inherit.induction.information (occ1 occ2)

  (let (tafs1 tafs2 gterm)
    (cond ((setq tafs1 (da-gterm.colourful.terms (rl-object occ1) 'induction))
	   (mapc #'(lambda (taf1)
		     (setq gterm (da-access taf1 (rl-object occ1)))
		     (cond ((and (null (da-gterm.colourful.terms gterm sel*actual.colour))
				 (da-gterm.termlist gterm)
				 (setq tafs2 (da-gterm.occurs.in.gterm gterm (rl-object occ2))))
			    (rl-with.sub.objects occ1 taf1 occ2 (car tafs2)
						 #'(lambda (sub.occ1 sub.occ2)
						   (sel=gterms.are.unifiable sub.occ1 sub.occ2))))))
		 tafs1))
	  ((setq tafs2 (da-gterm.colourful.terms (rl-object occ2) 'induction))
	   (mapc #'(lambda (taf2)
		     (setq gterm (da-access taf2 (rl-object occ2)))
		     (cond ((and (null (da-gterm.colourful.terms gterm sel*actual.colour))
				 (da-gterm.termlist gterm)
				 (setq tafs1 (da-gterm.occurs.in.gterm gterm (rl-object occ1))))
			    (rl-with.sub.objects occ1 (car tafs1) occ2 taf2
						 #'(lambda (sub.occ1 sub.occ2)
						     (sel=gterms.are.unifiable sub.occ1 sub.occ2))))))
		 tafs2))) 
    t))

			  

(defun sel=gterms.are.unifiable (occ1 occ2 &optional matching)

  ;;; Input : two occurrences
  ;;; Effect: tests whether both occurrences are unifiable wrt the denoted colours and in this case
  ;;;         colourizes both objects and applies the unifier to both.
  ;;; Value:  T iff both occurrences are unifiable

  (let (changes1 changes2 new.solution)
    (some #'(lambda (solution)
	      (cond ((setq new.solution (sel=bindings.add.unifier solution))
		     (multiple-value-setq (changes1 changes2) (sel=binding.replacements solution occ1 occ2))
		     (rl-object.change sel*eq.bindings new.solution)
		     (rl-object.changes occ1 changes1 nil (list ""))
		     (rl-object.changes occ2 changes2 nil (list ""))
		     t)))
	  (cond (matching (uni-gterm.match.lt (rl-object occ1) (rl-object occ2) 'opposite))
		(t (uni-gterm.unify (rl-object occ1) (rl-object occ2) nil nil nil 'opposite))))))


(defun sel=binding.replacements (subst occ1 occ2)

  (let* ((vars (uni-subst.domain subst))
	 (tafs1 (da-gterm.tafs (rl-object occ1) 
			       #'(lambda (subterm) (member (da-gterm.symbol subterm) vars))))
	 (tafs2 (da-gterm.tafs (rl-object occ2) 
			       #'(lambda (subterm) (member (da-gterm.symbol subterm) vars))))
	 (colour (incf sel*eq.colours)))
    (values (cons (list 'colour.until nil tafs1 sel*actual.colour colour)
		  (mapcar #'(lambda (taf) (list 'colour.all taf sel*actual.colour (incf sel*eq.colours))) tafs1))
	    (cons (list 'colour.until nil tafs2 sel*actual.colour colour)
		  (mapcar #'(lambda (taf) (list 'colour.all taf sel*actual.colour (incf sel*eq.colours))) tafs2)))))


(defun sel=bindings.add.unifier (unifier)

  (let ((old.bindings (rl-object sel*eq.bindings)) unifiers vars)
    (cond ((setq unifiers (uni-subst.merge unifier (car old.bindings)))
	   (setq vars (mapcar #'(lambda (var) (da-term.create var)) (uni-subst.domain unifier)))
	   (list (car unifiers) 
		 (append vars (second old.bindings))
		 (append (mapcar #'(lambda (var) (uni-subst.apply unifier var)) vars) (third old.bindings)))))))



(defun sel=gterms.insert.eq.bindings (occ1 occ2)

  (cond (sel*eq.bindings
	 (sel=apply.unifier (car (rl-object sel*eq.bindings)) occ1)
	 (sel=apply.unifier (car (rl-object sel*eq.bindings)) occ2)))
  (cond ((uni-gterm.are.equal (rl-object occ1) (rl-object occ2) nil nil 'opposite))
	(t nil)))


(defun sel=unifier.replace.binding (vars terms)

  (let* ((old.binding (rl-object sel*eq.bindings))
	 (varlist (second old.binding))
	 (values (copy-list (third old.binding)))
	 pos unifiers)
    (mapc #'(lambda (var value)
	      (cond ((setq pos (position-if #'(lambda (term) (eq (da-term.symbol term) var)) varlist))
		     (setf (car (nthcdr pos values)) value))
		    (t (push (da-term.create var) varlist)
		       (push value values))))
	  vars terms)
    (cond ((setq unifiers (uni-termlist.unify varlist values))
	   (rl-object.change sel*eq.bindings (list (car unifiers) varlist values))
	   T))))



(defun sel=eq.gterms.are.equal (occ1 taf1 occ2 taf2 &optional sign)

  ;;; Input:   two objects and two term access functions
  ;;; Effect:  tests whether both gterms denoted by \verb$OCC1$ and \verb$TAF1$ (resp.
  ;;;          \verb$OCC2$ and \verb$TAF2$ are equal and in this case
  ;;;          colourizes both objects.
  ;;; Value:   T iff both gterms are equal
  
  (let ((gterm1 (da-access taf1 (rl-object occ1))) (gterm2 (da-access taf2 (rl-object occ2))))
    (cond ((uni-gterm.are.equal gterm1 gterm2 nil nil sign)
	   (incf sel*eq.colours)
	   (cond ((da-colour.is.fade (da-gterm.colour gterm1 sel*actual.colour))
		  (rl-object.changes occ1 (list (list 'colour.until taf1 (da-gterm.colourful.terms gterm1 sel*actual.colour) 
						      sel*actual.colour sel*eq.colours))
				     nil (list ""))))
	   (cond ((da-colour.is.fade (da-gterm.colour gterm2 sel*actual.colour))
		  (rl-object.changes occ2 (list (list 'colour.until taf2 (da-gterm.colourful.terms gterm2 sel*actual.colour) 
						      sel*actual.colour sel*eq.colours))
				     nil (list ""))))
	   T))))
    

(defun sel=gterms.are.different (term1 term2)

  ;;; Input:   two gterms
  ;;; Effect:  checks, whether instances of both gterms can be equalized
  ;;; Value:   T iff both gterms (and their instances) are definitly different.

  (let ((symbol1 (da-gterm.symbol term1)) (symbol2 (da-gterm.symbol term2)))
    (or (and (da-term.is term1) (da-term.is term2)
	     (not (DA-SORT.is.subsort (da-term.sort term1) (da-term.sort term2)))
	     (not (DA-SORT.is.subsort (da-term.sort term2) (da-term.sort term1))))
	(and (da-function.is symbol1)
	     (da-function.is.constructor symbol1)
	     (getf (da-sort.attributes (da-term.sort term1)) 'free.structure)
	     (da-function.is symbol2)
	     (da-function.is.constructor symbol2)
	     (or (neq symbol1 symbol2)
		 (some #'(lambda (arg1 arg2) (sel=gterms.are.different arg1 arg2))
		       (da-term.termlist term1) (da-term.termlist term2)))))))


;;;;;------------------------------------------------------------------------------------------------------
;;;;;
;;;;;   Section ? :    equalize terms by adapting subterms
;;;;;
;;;;;------------------------------------------------------------------------------------------------------


(defun sel=eq.equalize.with.subterms (occ1 occ2 &optional removed.symbols)

  ;;; Input:   two occs, a flag and a list of prefuns
  ;;; Effect:  searches for an independent symbol in occ1 which do not occur inside
  ;;;          some argument of another independent symbol in occ1 and which do occur in occ2
  ;;;          and tries to equalize both subterms, when the disturbing things are equalized or
  ;;;          moved outside the common independent symbol and the function is entered recursively.
  ;;; Value:   T, if some independent symbol is used to adapt the gterms.
  ;;; Note:    missing strategies in case of _x = _y ?

  (let (result new.removed.symbols)
    (multiple-value-bind (shared.max.symbs left.max.symbs right.max.symbs)
      (sel=gterm.max.symbols (rl-object occ1) (rl-object occ2) sel*actual.colour)
      (cond ((or (null (da-gterm.fade.gterms (rl-object occ1) sel*actual.colour))
		 (null (da-gterm.fade.gterms (rl-object occ2) sel*actual.colour))))
	    ((and (null left.max.symbs) (sel=eq.term.is.inside occ1 occ2)))
	    ((and (null right.max.symbs) (sel=eq.term.is.inside occ2 occ1)))
	    ((cond ((and (or left.max.symbs right.max.symbs)
			 (setq new.removed.symbols
			       (sel=eq.adapt.context occ1 occ2 left.max.symbs 
						     right.max.symbs removed.symbols)))
		    (setq removed.symbols new.removed.symbols))
		   ((sel=eq.enlarge.skeleton occ1 occ2 shared.max.symbs) (setq result t))
		   ((and shared.max.symbs
			 (setq new.removed.symbols
			       (sel=eq.adapt.context occ1 occ2 shared.max.symbs 
						     shared.max.symbs removed.symbols)))
		    (setq removed.symbols new.removed.symbols))
		   ((and (null left.max.symbs) (null right.max.symbs) (null shared.max.symbs))
		    (sel=eq.adapt.trivial.terms occ1 occ2)))
	     (or (sel=eq.equalize.with.subterms occ1 occ2 removed.symbols)
		 result))))))


(defun sel=eq.adapt.trivial.terms (occ1 occ2)
  
  (let ((sel*constrains (copy-tree sel*constrains)))
    (push sel*actual.colour (getf sel*constrains 'colour.invariants))
    (or (DB-MODIFIER.SELECTION
	 (rl-object occ1) 'top.level nil
	 #'(lambda (modifier)
	     (cond ((eq (da-gterm.symbol (da-modifier.value modifier)) (da-gterm.symbol (rl-object occ2)))
		    (sel=modifier.try.to.apply modifier occ1)))))
	(DB-MODIFIER.SELECTION
	 (rl-object occ2) 'top.level nil
	 #'(lambda (modifier)
	     (cond ((eq (da-gterm.symbol (da-modifier.value modifier)) (da-gterm.symbol (rl-object occ1)))
		    (sel=modifier.try.to.apply modifier occ2))))))))
       

(defun sel=eq.adapt.context (occ1 occ2 left.max.symbs right.max.symbs removed.symbols)

  (cond ((and left.max.symbs (sel=eq.remove.symbols.in.occ occ1 occ2 left.max.symbs removed.symbols)))
	((and right.max.symbs (sel=eq.remove.symbols.in.occ occ2 occ1 right.max.symbs removed.symbols)))
	
	 ; ((progn (sel=eq.equalize.top.down occ1 occ2)) removed.symbols)
	))


(defun sel=eq.term.is.inside (occ1 occ2)

  ;;; Input:  two occurrences
  ;;; Effect: searches for an occurrence of an instance \verb$OCC1$ in an instance of \verb$OCC2$.
  ;;; Value:  T iff the search is successfull

  (cond ((or (null (da-gterm.colour (rl-object occ1) sel*actual.colour))
	     (da-gterm.is.fade (rl-object occ1) sel*actual.colour))
	 (or (and (da-variable.is (da-gterm.symbol (rl-object occ1)))
		  (and (or (da-gterm.is.fade (rl-object occ2) sel*actual.colour)
			   (null (da-gterm.colour (rl-object occ2) sel*actual.colour)))
		       (sel=gterms.are.unifiable occ1 occ2)))
	     (some #'(lambda (taf)
		       (rl-with.sub.objects occ2 taf
					    #'(lambda (sub.occ2)
						(and (da-gterm.is.fade (rl-object sub.occ2) sel*actual.colour)
						     (sel=gterms.are.unifiable occ1 sub.occ2 t)))))
		   (da-symbol.occurs.in.gterm (da-gterm.symbol (rl-object occ1)) (rl-object occ2)))))))


(defun sel=eq.enlarge.skeleton (occ1 occ2 shared.max.symbs)

  ;;; Input:   two occs, a list of lists like $(t \alpha_1 ... \alpha_n)$
  ;;; Effect:  searches for some $t$ in \verb$GTERM.TAFS$ for a corresponding occurrence
  ;;;          of the top-level symbol in \verb$OCC2$ such that both have a common subterm.
  ;;; Value:   T iff a corresponding subterm is found.

  (some #'(lambda (symbol)
	    (some #'(lambda (ranking.taf1.taf2)
		      (sel=eq.equalize.gterms.inside 
		       occ1 occ2 (second ranking.taf1.taf2) (third ranking.taf1.taf2))) 
		  (sel=eq.sort.alternative.gterms occ1 occ2 symbol)))
	shared.max.symbs))


(defun sel=eq.sort.alternative.gterms (occ1 occ2 symbol)

  ;;; Input:   two gterms
  ;;; Effect:  sorts the occurrences of the top-level symbol of \verb$GTERM1$ such that those
  ;;;          occurrences are prefered with share the most function symbols with \verb$GTERM1$.
  ;;; Value:   the sorted list of tafs to the occurrences.
  
  (let* ((tafs1 (sel=symbol.occurs.in.context symbol (rl-object occ1) sel*actual.colour))
	 (tafs2 (sel=symbol.occurs.in.context symbol (rl-object occ2) sel*actual.colour))
	 symbol.list symbols1 symbols2)
    (mapc #'(lambda (taf1)
	      (setq symbols1 (da-gterm.functions (da-access taf1 (rl-object occ1))))
	      (mapc #'(lambda (taf2)
			(setq symbols2 (da-gterm.functions (da-access taf2 (rl-object occ2))))
			(push (list (+ (length (set-difference symbols2 symbols1))
				       (length (set-difference symbols1 symbols2)))
				    taf1 taf2 
				    (sel=eq.similar.paths (rl-object occ1) (rl-object occ2) (reverse taf1) (reverse taf2)))
			      symbol.list))
		    tafs2))
	  tafs1)
     (sort symbol.list #'(lambda (x y) 
			   (or (< (car x) (car y))
			       (and (eql (car x) (car y))
				    (or (> (fourth x) (fourth y))
					(< (+ (length (second x)) (length (third x)))
					   (+ (length (second y)) (length (third y)))))))))))



(defun sel=eq.similar.paths (gterm1 gterm2 r.taf1 r.taf2)

  (cond ((or (null r.taf1) (null r.taf2)) 0)
	((and (eq (da-gterm.symbol gterm1) (da-gterm.symbol gterm2))
	      (eq (car r.taf1) (car r.taf2)))
	 (1+ (sel=eq.similar.paths (nth (1- (car r.taf1)) (da-gterm.termlist gterm1))
				   (nth (1- (car r.taf2)) (da-gterm.termlist gterm2))
				   (cdr r.taf1) (cdr r.taf2))))
	(t 0)))
	 

(defrule sel=eq.remove.symbols.in.occ (occ other.occ &others symbols removed.symbols)

  (EQ 2 ("try to remove ~A in ~A without ~A" 3 1 4) ("remove" (1 2) col (3)))

  ;;; Input:   an occurrence and two lists of symbols
  ;;; Effect:  tries to eliminate each occurrence of an element of \verb$SYMBOLS$
  ;;;          in \verb$OCC$ provided it is not member of \verb$REMOVED.SYMBOLS$.
  ;;;          Also no member of \verb$REMOVED.SYMBOLS$ may be introduced by
  ;;;          removing these symbols.
  ;;; Value:   T iff some occurrence has been eliminated.

  (let (tafs gterm)
    (some #'(lambda (type)
	      (cond ((some #'(lambda (symbol)
			       (cond ((setq tafs (da-gterm.tafs 
						  (rl-object occ) 
						  #'(lambda (subterm)
						      (and (eq (da-gterm.symbol subterm) symbol)
							   (da-colour.is.fade 
							    (da-gterm.colour subterm sel*actual.colour))))))
				      (push symbol removed.symbols)
				      (setq gterm (da-access (car tafs) (rl-object occ)))
				      (db-modifier.selection
				       gterm 'dismset nil
				       #'(lambda (modifier)
					   (and (member 'eliminate (getf (da-modifier.attributes modifier)
									 'types))
						(sel=eq.modifier.is.suitable 
						 (rl-object occ) (rl-object other.occ)
						 modifier removed.symbols)
						(sel=eq.remove.symbols.in.occ.1
						 occ modifier symbol type tafs)))))))
			   symbols)
		     (cond ((sel=eq.remove.symbols.in.occ occ other.occ symbols removed.symbols))
			   (t removed.symbols)))))
	  '(match unify))))


(defrule sel=eq.remove.symbols.in.occ.1 (occ &others modifier symbol type tafs)

  (EQ 10 ("try to remove ~A in ~A without ~A" 2 1 3))

  (let ((sel*constrains (copy-tree sel*constrains)))
    (push sel*actual.colour (getf sel*constrains 'colour.invariants))
    (cond ((sel=modifier.try.to.apply modifier occ type)
	   (< (length (da-gterm.tafs (rl-object occ) 
				     #'(lambda (subterm)
					 (and (eq (da-gterm.symbol subterm) symbol)
					      (da-colour.is.fade (da-gterm.colour subterm sel*actual.colour))))))
	      (length tafs))))))


(defun sel=eq.modifier.is.suitable (gterm1 gterm2 modifier removed.symbols)

  (and (null (intersection (da-gterm.prefuns (da-modifier.value modifier)) removed.symbols))
       (or (every #'(lambda (symbol) (not (and (da-function.is symbol) 
					       (da-function.skolem symbol))))
		  (set-difference (da-gterm.prefuns (da-modifier.input modifier))
				  (da-gterm.prefuns gterm2))))))

;;; was: P(cons(X, Y)) AND not P(x) AND x = cons(car(x), cdr(x)) AND y = cons(car(y), cdr(y))


(defrule sel=eq.equalize.top.down (occ1 occ2 &optional used.symbols)

  (EQ 5 ("equalizing top level ~A and ~A" 1 2))

  (cond ((sel=gterms.are.unifiable occ1 occ2))
	(t   (let ((sel*constrains (copy-tree sel*constrains)))
	       (push sel*actual.colour (getf sel*constrains 'colour.invariants))
	       (let (new.symbol result)
		 (while (and (null result) 
			     (setq new.symbol (sel=equalize.find.function.symbol occ1 occ2 used.symbols)))
		   (push new.symbol used.symbols)
		   (setq result (sel=eq.equalize.top.down.with.symbol occ1 occ2 new.symbol)))
		 result)))))


(defrule sel=eq.equalize.top.down.with.symbol (occ1 occ2 &others symbol)

  (EQ 5 ("using ~A as top-level symbol" 3))
  
  (and (sel=term.express.in.terms.of occ1 symbol)
       (sel=term.express.in.terms.of occ2 symbol)
       (sel=eq.equalize.top.down.termlists occ1 occ2)))


(defrule sel=eq.equalize.top.down.termlists (occ1 occ2)

  (EQ 5 ("searching for equal arguments"))
  
  (let ((result t) (taf (da-taf.create.zero nil)))
    (every #'(lambda (term)
	       (declare (ignore term))
	       (setq taf (da-taf.create.next taf))
	       (rl-with.sub.objects occ1 taf occ2 taf
				    #'(lambda (sub.occ1 sub.occ2)
					(setq result (sel=eq.equalize.top.down sub.occ1 sub.occ2))))
	       result)
	   (da-gterm.termlist (rl-object occ1)))
    result))


(defrule sel=eq.equalize.gterms.inside (occ1 occ2 &others taf1 taf2)

  (EQ 6 ("with tafs ~A and ~A" 3 4))

  ;;; Input:   two occs
  ;;; Effect:  tries to permute the termlists according to the ordering in sel=...
  ;;;          and adapts the pairs of corresponding arguments.
  ;;; Value:   ?

  (let (symbol result)
    (rl-with.sub.objects
     occ1 taf1 occ2 taf2
     #'(lambda (sub.occ1 sub.occ2)
	 (setq symbol (da-gterm.symbol (rl-object sub.occ1)))
	 (setq result (cond ((sel=eq.gterms.are.equal sub.occ1 nil sub.occ2 nil))
			    ((da-symbol.has.attribute symbol 'associative)
			     (sel=eq.equalize.gterms.inside.a sub.occ1 sub.occ2 symbol
							      (sel=eq.assoc.relations sub.occ1 sub.occ2)))
			    ((sel=eq.equalize.gterms.inside.one.to.one sub.occ1 sub.occ2))
			    ((or (da-symbol.has.attribute symbol 'commutative)
				 (da-symbol.has.attribute symbol 'symmetric))
			     (sel=eq.equalize.gterms.inside.commutative sub.occ1 sub.occ2))
			    ((sel=eq.equalize.gterms.inside.by.some.perm sub.occ1 sub.occ2))))))
    (cond (result (sel=eq.context.move.up.or.adapt occ1 occ2)))))


(defrule sel=eq.equalize.gterms.inside.one.to.one (occ1 occ2)

  ;;; Input:  two occs with same prefun symbol
  ;;; Effect: tries to adapt the termlists of both occs such that the corresponding terms
  ;;;         have a common subterm. In this case the common top-level prefun is coloured.
  ;;; Value:  t iff this succeeds
  
  (eq 3 ("adapting in ~A and ~A with ~A ~A" 1 2 3 4)  ("equalize (1:1)" (1 2) col nil))

  (let ((taf (da-taf.create.zero nil)) s.result)
    (cond ((every #'(lambda (term)
		      (declare (ignore term))
		      (setq taf (da-taf.create.next taf))
		      (rl-with.sub.objects occ1 taf occ2 taf
					   #'(lambda (sub.occ1 sub.occ2)
					       (setq s.result (sel=eq.equalize.with.subterms sub.occ1 sub.occ2))))
		      s.result)
		  (da-gterm.termlist (rl-object occ1)))
	   (sel=eq.colourize.top.level occ1 occ2)
	   t))))


(defrule sel=eq.equalize.gterms.inside.commutative (occ1 occ2)

  ;;; Input:  two occs with same prefun symbol
  ;;; Effect: tries to adapt the termlists of both occs such that the crosswise terms
  ;;;         have a common subterm. In this case the common top-level prefun is coloured.
  ;;; Value:  t iff this succeeds
  
  (eq 3 ("adapting in ~A and ~A by commutativity" 1 2) ("equalize (X)" (1 2) col nil))

  (let (s.result)
    (cond ((every #'(lambda (taf1 taf2)
		      (rl-with.sub.objects occ1 taf1 occ2 taf2
					   #'(lambda (sub.occ1 sub.occ2)
					       (setq s.result (sel=eq.equalize.with.subterms sub.occ1 sub.occ2))))
		      s.result)
		  (list (da-taf.create.left) (da-taf.create.right))
		  (list (da-taf.create.right) (da-taf.create.left)))
	   (sel=eq.colourize.top.level occ1 occ2)
	   t))))


;;;; asoociative adaption

(defrule sel=eq.equalize.gterms.inside.a (occ1 occ2 &others symbol taf.relations)

  (eq 3 ("adapting ~A and ~A by equal terms" 1 2) ("equalize (Ass)" (1 2) col nil))

  (sel=eq.equalize.gterms.inside.a.int occ1 occ2 symbol taf.relations))


(defrule sel=eq.equalize.gterms.inside.a.int (occ1 occ2 &others symbol taf.relations)
  
  (eq 10 ("adapting ~A and ~A by equal terms" 1 2))

  (let ((tafs1 (sel=eq.faded.taf.lists (rl-object occ1) symbol))
	(tafs2 (sel=eq.faded.taf.lists (rl-object occ2) symbol)))
   (cond ((or (null tafs1) (null tafs2))
	  (sel=eq.merge.contexts.under.theory occ1 occ2 symbol)
	  t)
	 ((neq (null (cdr tafs1)) (null (cdr tafs2)))
	  (sel=eq.equalize.with.merged.contexts occ1 occ2 tafs1 tafs2))
	 ((and (da-symbol.has.attribute symbol 'commutative)
	       (some #'(lambda (taf1)
			 (some #'(lambda (taf2)
				   (sel=eq.gterms.are.equal occ1 taf1 occ2 taf2))
			       tafs2))
		     tafs1))
	  (sel=eq.merge.contexts.under.theory occ1 occ2 symbol)
	  (sel=eq.equalize.gterms.inside.a.int occ1 occ2 symbol taf.relations))
	 (t (some #'(lambda (taf1)
		      (some #'(lambda (taf2)
				(cond ((sel=eq.assoc.relation.is.admissible symbol taf1 taf2 taf.relations)
				       (sel=eq.equalize.gterms.inside.a.1 
					occ1 occ2 taf1 taf2 symbol taf.relations))))
			    tafs2))
		  tafs1)))))


(defun sel=eq.equalize.with.merged.contexts (occ1 occ2 tafs1 tafs2)

  (let ((taf1 (da-taf.common.taf tafs1)) (taf2 (da-taf.common.taf tafs2)) s.result)
    (rl-with.sub.objects occ1 taf1 occ2 taf2
			 #'(lambda (sub.occ1 sub.occ2)
			     (setq s.result (sel=eq.equalize.with.subterms sub.occ1 sub.occ2))))
    s.result))
	 


(defrule sel=eq.equalize.gterms.inside.a.1 (occ1 occ2 &others taf1 taf2 &others symbol taf.relations)

  (eq 5 ("adapting ~A and ~A by equal terms" 1 2))

  (let (result)
    (rl-with.sub.objects
     occ1 taf1 occ2 taf2
     #'(lambda (sub.occ1 sub.occ2)
	 (setq result (sel=eq.equalize.with.subterms sub.occ1 sub.occ2))))
    (cond ((and result 
		(sel=eq.merge.contexts.under.theory occ1 occ2 symbol))
	   (sel=eq.equalize.gterms.inside.a.int occ1 occ2 symbol (cons (cons taf1 taf2) taf.relations))))))
  

(defun sel=eq.merge.contexts.under.theory (occ1 occ2 symbol)

  ;;; this function is buggy in case there are more than 2 equal subterms. Rippling will
  ;;; not sort the argument corretly!

  (let ((all.tafs.1 (sel=taf.list.common.sub.tafs (da-gterm.colourful.terms (rl-object occ1) sel*actual.colour) 
						  symbol (rl-object occ1)))
	(all.tafs.2 (sel=taf.list.common.sub.tafs (da-gterm.colourful.terms (rl-object occ2) sel*actual.colour)
						  symbol (rl-object occ2))))
    (cond ((or all.tafs.1 all.tafs.2) (incf sel*eq.colours)))
    (cond (all.tafs.1 (rl-object.changes occ1 (mapcar #'(lambda (taf) 
							  (list 'colour.top taf sel*actual.colour sel*eq.colours))
						      all.tafs.1)
					 nil nil)))
    (cond (all.tafs.2 (rl-object.changes occ2 (mapcar #'(lambda (taf) 
							  (list 'colour.top taf sel*actual.colour sel*eq.colours))
						      all.tafs.2)
					 nil nil)))
    (cond ((sel=eq.context.move.up.or.adapt occ1 occ2)))))



(defun sel=eq.assoc.relations (occ1 occ2)

  (let (other.tafs)
    (mapcan #'(lambda (taf)
		(cond ((setq other.tafs (da-gterm.coloured.terms
					 (rl-object occ2) 
					 (da-gterm.colour (da-access taf (rl-object occ1)) sel*actual.colour)
					 sel*actual.colour))
		       (list (cons taf (car other.tafs))))))
	    (da-gterm.colourful.terms (rl-object occ1) sel*actual.colour))))


(defun sel=eq.assoc.relation.is.admissible (symbol taf1 taf2 taf.relations)

  (or (da-symbol.has.attribute symbol 'commutative)
      (every #'(lambda (taf1.taf2)
		 (cond ((eq (da-taf.compare taf1 (car taf1.taf2)) 'left)
			(not (eq (da-taf.compare taf2 (cdr taf1.taf2)) 'right)))
		       (t (not (eq (da-taf.compare taf2 (cdr taf1.taf2)) 'left)))))
	     taf.relations)))


(defun sel=taf.list.common.sub.tafs (taf.list symbol gterm)

  (let (all.tafs common.taf)
    (mapl #'(lambda (tafs1)
	      (mapc #'(lambda (taf2)
			(setq common.taf (da-taf.common.taf (list (car tafs1) taf2)))
			(cond ((eq symbol (da-gterm.symbol (da-access common.taf gterm)))
			       (setq all.tafs (adjoin common.taf all.tafs :test 'equal)))))
		    (cdr tafs1)))
	  taf.list)
    all.tafs))
	    

(defun sel=eq.faded.taf.lists (gterm symbol &optional taf)

   (cond ((and (eq (da-term.symbol gterm) symbol)
	       (da-colour.is.fade (da-gterm.colour gterm sel*actual.colour)))
	  (let ((counter 0))
	    (mapcan #'(lambda (sub.term)
			(incf counter)
			(sel=eq.faded.taf.lists sub.term symbol(cons counter taf)))
		   (da-term.termlist gterm))))
	((da-gterm.is.fade gterm sel*actual.colour)
	 (list taf))))


;;; adapting via permutive lemmas:


(defrule sel=eq.equalize.gterms.inside.by.some.perm (occ1 occ2)

  (eq 5 ("adapting permutive in ~A and ~A with  ~A ~A" 1 2 3 4))

  (let ((permutation (sel=eq.perm.compute (rl-object occ1) (rl-object occ2))))
    (cond (permutation
	   (multiple-value-bind (result tafs)
	      (sel=gterm.make.permutations occ1 occ2 permutation
					   #'(lambda (x y) (declare (ignore x y)) t))
	      (cond ((eq 'success result)
		     (some #'(lambda (taf)
			       (rl-with.sub.objects occ1 taf
						    #'(lambda (sub.occ1)
							(sel=eq.equalize.gterms.inside.one.to.one sub.occ1 occ2))))
			   tafs))))))))


(defun sel=eq.perm.compute (gterm1 gterm2)

  ;;; for test uses only

  (let (fcts taf (taf2 (da-taf.create.zero nil)))
    (mapcan #'(lambda (sub.term1 sub.term2)
		(setq taf2 (da-taf.create.next taf2))
		(cond ((null (intersection (setq fcts (da-gterm.functions sub.term1 'skolem))
					   (da-gterm.functions sub.term2 'skolem)))
		       (setq taf (da-taf.create.zero nil))
		       (list (list nil taf2 (mapcan #'(lambda (other.term)
							(setq taf (da-taf.create.next taf))
							(cond ((and (neq other.term sub.term2)
								    (intersection fcts (da-gterm.functions other.term 'skolem)))
							       (list taf))))
						    (da-gterm.termlist gterm2)))))))
	    (da-gterm.termlist gterm1) (da-gterm.termlist gterm2))))


(defun sel=gterm.make.permutations (occ1 occ2 permutations test.fct)
  
  ;;; Input     : two gterms, a permutation list and a test.fct 
  ;;; Effect    : tries to apply recursive modifiers, such that the given permutations could be done on occ1
  ;;; Value     : a multiple-value: the first is either \verb$SUCCESS$ if it was successfull \verb$PARTIAL$
  ;;;             if it was partially successfull and \verb$FAIL$ otherwise. The second is a list of tafs
  ;;;             denoting the recursive occurrences of the symbol.
  ;;; Note      : the two gterms must have the same top.level symbol.

  (let ((result 'success)
	rest.permutations.and.tafs)
    (cond (permutations
	   (cond ((some #'(lambda (modifier)
			    (setq rest.permutations.and.tafs
				  (sel=gterm.recursive.modifier.test.and.apply occ1 modifier permutations test.fct)))
			(SEL=gterm.recursive.modifiers.sort (rl-object occ1) permutations))
		  (mapc #'(lambda (permutation.taf)
			    (rl-with.sub.objects occ1 (cdr permutation.taf)
						 #'(lambda (s.occ1)
						     (setq result (sel=gterm.make.permutations s.occ1 occ2
											       (car permutation.taf)
											       test.fct))))
			    (cond ((not (eq 'success result)) (setq result 'partial))))
			rest.permutations.and.tafs))
		 (T (setq result 'fail)))))
    (values result (mapcar #'(lambda (rest.permutation.and.taf) (cdr rest.permutation.and.taf)) rest.permutations.and.tafs))))


(defrule sel=gterm.recursive.modifier.test.and.apply (occ &others modifier permutations test.fct)

  ;;; input     : an object, a recursive modifier, a permutation-list and a test function
  ;;; value     : a list of dotted.pairs REST_PERMUTATIONS . TAF, iff the modifier could be applied with respect to test.fct
  ;;;             and if the number of permutations to be done has been reduced.

  (EQ 5 ("testing ~a" 2))
  
  (let ((old.gterm (da-gterm.copy (rl-object occ)))
	(sel*constrains (copy-tree sel*constrains))
	result tafs rest.permutation)
    (push sel*actual.colour (getf sel*constrains 'colour.invariants))
    (cond ((sel=modifier.test.and.apply (cond ((da-term.is (da-modifier.input modifier)) modifier)
					      (T (sel=object.modifier.variable.depending.modifier occ modifier)))
					occ nil nil)
	   (cond ((and (neq 'fail (setq tafs (sel=gterm.check.result.of.recursive.modifier.application 
					      test.fct old.gterm (rl-object occ))))
		       (some #'(lambda (taf)
				 (setq rest.permutation (sel=gterm.permutations.rest.permutations
							     old.gterm (da-access taf (rl-object occ)) permutations))
				 (push (cons rest.permutation taf) result)
				 (not (sel=permutations.are.equal permutations rest.permutation)))
			     tafs))
		  result))))))


(defun sel=object.modifier.variable.depending.modifier (occ modifier)

  ;;; input     : an object and a modifier
  ;;; value     : returns a modifier with the same input, but where literals from the conditions of MODIFIER,
  ;;;             in which occurs variables which doesnt occur in the object, have been moved into the value

  (let* ((object.variables (da-gterm.variables (rl-object occ)))
	 (new.conditions (remove-if #'(lambda (gterm) (set-difference (da-gterm.variables gterm) object.variables))
				    (da-modifier.condition modifier)))
	 (new.value (norm-normalize.gterm (da-gterm.create 'or
							   (cons (da-gterm.copy (da-modifier.value modifier))
								 (mapcar #'(lambda (gterm) (da-gterm.copy gterm))
									 (set-difference (da-modifier.condition modifier)
											 new.conditions)))))))
    (make-da*modifier :modframe (make-da*modframe :input (da-gterm.copy (da-modifier.input modifier))
						  :value new.value
						  :condition new.conditions)
		      :input.taf (da-modifier.input.taf modifier)
		      :attributes nil)))


(defun sel=gterm.check.result.of.recursive.modifier.application (test.fct left right)
  
  ;;; Value     : a list containing the TAFs to adequate subterms tj of RIGHT, such that:
  ;;;                 - Top-Level(tj) = Top-Level(left)     (*1*)
  ;;;                 - for all other subterms ti of RIGHT, with (*1*), test.fct(left,ti) = T.
  ;;;             'FAIL, if no such subterm tj exists.

  (let ((tafs (da-symbol.occurs.in.gterm (da-gterm.symbol left) right))
	(result nil))
    (cond ((null tafs) (setq result 'fail))
	  ((cdr tafs)
	   (cond ((null (setq result (remove-if-not #'(lambda (taf)
							(every #'(lambda (other.taf)
								   (funcall test.fct left (da-access other.taf right)))
							       (remove taf tafs :test #'(lambda (x y) (da-taf.are.equal x y)))))
						    tafs)))
		  (setq result 'fail))))
	  (T (setq result tafs)))
    result))


;;; Representation of a symbol permutation with repsect to two terms f(...) and f(+++)
;;; permutation = ( symbol (position in ...) ((position1 in +++) ... (positionN in +++)) )
;;;               where N >= 0.
;;;               if N = 0 then the symbol is removed (doesn't occur in +++)
;;;               the positions above have to be top-level-TAFS !!!


(DEFUN SEL=PERMUTATION.IS.POSSIBLE (PERMUTATION PERMUTATIONS)
  
  ;;; Edited    : 10.02.1994
  ;;; Input     : a permutation of some symbol and a list of permutations (of variables only!).
  ;;; Value     : T, iff the one of the wished permutation of the symbol is directly possible with the
  ;;;             given variable permutation.

  (SOME #'(LAMBDA (PERM)
	    (AND (EQUAL (CADR PERMUTATION) (CADR PERM))
		 (OR (AND (EQUALP (CADDR PERMUTATION) (CADDR PERM))
			  (EQUALP (CADDR PERM) NIL))
		     (INTERSECTION (CADDR PERMUTATION) (CADDR PERM) :TEST #'(LAMBDA (TAF1 TAF2) (DA-TAF.ARE.EQUAL TAF1 TAF2))))
		 T))
	PERMUTATIONS))


(defun sel=gterm.permutation.has.been.done (gterm1 gterm2 permutation)
  
  ;;; Input     : two gterms and a permutation. The symbol of the permutation must occur in gterm1
  ;;;             on the top-level TAF of the permutation. Both gterms must have the same top.level symbol.
  ;;; Value     : T, iff the symbol does not occur in gterm2 under the same top-level TAF, but on
  ;;;             one taf of the goal-tafs of the permutation, if there are some. NIL otherwise.

  (declare (ignore gterm1))
  (let ((symbol (car permutation)))
    (and (not (da-symbol.occurs.in.gterm symbol (da-access (cadr permutation) gterm2)))
	 (cond ((caddr permutation)
		(some #'(lambda (top-level-taf)
			  (da-symbol.occurs.in.gterm symbol (da-access top-level-taf gterm2)))
		      (caddr permutation)))
	       (T (null (da-symbol.occurs.in.gterm symbol gterm2))))
	 T)))


(defun sel=gterm.permutations.rest.permutations (gterm1 gterm2 wished.permutations)
  
  (mapcan #'(lambda (permutation)
	      (and (not (sel=gterm.permutation.has.been.done gterm1 gterm2 permutation))
		   (list permutation)))
	  wished.permutations))

(defun sel=permutation.are.equal (permutation1 permutation2)
  
  (and (equal (car permutation1) (car permutation2))
       (da-taf.are.equal (cadr permutation1) (cadr permutation2))
       (and (subsetp (caddr permutation1) (caddr permutation2) :test #'(lambda (x y) (da-taf.are.equal x y)))
	    (subsetp (caddr permutation2) (caddr permutation1) :test #'(lambda (x y) (da-taf.are.equal x y))))))

(defun sel=permutations.are.equal (permutations1 permutations2)
 
  (and (subsetp permutations1 permutations2 :test #'(lambda (x y) (sel=permutation.are.equal x y)))
       (subsetp permutations2 permutations1 :test #'(lambda (x y) (sel=permutation.are.equal x y)))))


(DEFUN SEL=PERMUTATIONS.NUMBER.OF.POSSIBLE.PERMUTATIONS (PERMUTATIONS PERMUTATIONS1)
  
  ;;; Input     : a list of wished permutations and a list of variable permutations
  ;;; Value     : the number of wished permutations, which are possible with the given variable
  ;;;             permutations
  
  (LET ((COUNTER 0))
    (MAPC #'(LAMBDA (PERMUTATION)
	       (COND ((SEL=PERMUTATION.IS.POSSIBLE PERMUTATION PERMUTATIONS1)
		      (INCF COUNTER))))
	   PERMUTATIONS)
    COUNTER))


(defun sel=gterm.recursive.modifiers.sort (gterm permutations)
  
  (LET (NUMBER list.of.numbers)
    (mapcar #'(lambda (number.modifier)
		(cdr number.modifier))
	    (SORT (db-modifier.collection
		   gterm 'recursive nil
		   #'(LAMBDA (MODIFIER)
		       (setq list.of.numbers (mapcar #'(lambda (taf.permutations)
							 (SEL=PERMUTATIONS.NUMBER.OF.POSSIBLE.PERMUTATIONS
							  permutations
							  (cadr taf.PERMUTATIONS)))
						     (GETF (DA-MODIFIER.ATTRIBUTES MODIFIER) 'CHANGES)))
		       (SETQ NUMBER (/ (+ (apply #'max list.of.numbers) (apply #'min list.of.numbers)) 2))
		       (COND ((> NUMBER 0)
			      (LIST (CONS NUMBER MODIFIER))))))
		  #'>
		  :key #'car))))
	    

(defun sel=permutation.rest.permutation (permutations1 permutations2)
  
  ;;; Value     : the permutations of PERMUTATIONS1, which are not possible with permutations2

  (mapcan #'(lambda (permutation)
	      (and (not (sel=permutation.is.possible permutation permutations2))
		   (list permutation)))
	  permutations1))



;;;;;-------------------------------------------------------------------------------------------------------------------
;;;;;
;;;;;   Section ? :    adapting the contexts of two gterms
;;;;;
;;;;;--------------------------------------------------------------------------------------------------------------------


(defrule sel=eq.context.move.up.or.adapt (occ1 occ2)

  (eq 5 ("removing contexts in ~A and ~A" 1 2))

  (let ((succ1 (eq (sel=context.move.up occ1 sel*actual.colour) 'success))
	(succ2 (eq (sel=context.move.up occ2 sel*actual.colour) 'success))
	tafs)
    (cond ((null succ1)
	   (setq tafs (da-gterm.max.faded.gterms (rl-object occ1) sel*actual.colour))
	   (rl-with.sub.objects occ1 (car tafs) #'(lambda (s.occ1)
						    (setq result (sel=ind.remove.context.directly
								  s.occ1 sel*actual.colour))))
	   (cond (result (setq succ1 (eq (sel=context.move.up occ1 sel*actual.colour) 'success))))))
    (cond ((null succ2)
	   (setq tafs (da-gterm.max.faded.gterms (rl-object occ2) sel*actual.colour))
	   (rl-with.sub.objects occ2 (car tafs) #'(lambda (s.occ2)
						    (setq result (sel=ind.remove.context.directly 
								  s.occ2 sel*actual.colour))))
	   (cond (result (setq succ2 (eq (sel=context.move.up occ2 sel*actual.colour) 'success))))))
    (cond ((and succ1 succ2) t)
	  ((or succ1 succ2)
	   (cond ((sel=eq.context.create.missing occ1 occ2 succ1 succ2))
	;;	 ((sel=eq.move.context.to.sinks occ1 occ2 succ1 succ2))
		 )))))



(defrule sel=eq.context.create.missing (occ1 occ2 &others succ1 succ2)

  (eq 5 ("insert context on other side ~A and ~A" 1 2))

  (some #'(lambda (taf1)
	    (some #'(lambda (taf2)
		      (rl-with.sub.objects 
		       occ1 taf1 occ2 taf2
		       #'(lambda (sub.occ1 sub.occ2)
			   (cond ((eq (da-gterm.colour (rl-object sub.occ1) sel*actual.colour) 
				      (da-gterm.colour (rl-object sub.occ2) sel*actual.colour))
				  (setq result
					(cond (succ1 (sel=eq.insert.missing.context sub.occ1 sub.occ2))
					      (succ2 (sel=eq.insert.missing.context sub.occ2 sub.occ1))))))))
		      result)
		  (da-gterm.colourful.terms (rl-object occ2) sel*actual.colour)))
	(da-gterm.colourful.terms (rl-object occ1) sel*actual.colour)))


(defrule sel=eq.move.context.to.sinks (occ1 occ2 &others succ1 succ2)

  (eq 5 ("move context to var position ~A and ~A" 1 2))

  (cond (succ1 (sel=context.adapt.by.moving.in occ1 occ2))
	(succ2 (sel=context.adapt.by.moving.in occ2 occ1))))


(defun sel=eq.equalize.top.level (occ1 occ2)

  ;;; Input:   two occurrences
  ;;; Effect:  tries to remove the top-level contexts of both occurrences
  ;;; Value:   T iff both occurrences are equal

  (let (succ1 succ2)
    (setq succ1 (or (not (da-colour.is.fade (da-gterm.colour (rl-object occ1) sel*actual.colour)))
		    (sel=ind.remove.context.directly occ1 sel*actual.colour)))
    (setq succ2 (or (not (da-colour.is.fade (da-gterm.colour (rl-object occ2) sel*actual.colour)))
		    (sel=ind.remove.context.directly occ2 sel*actual.colour)))
    (cond ((and succ1 succ2) t)
	  (succ1 (sel=context.adapt.by.moving.in occ1 occ2))
	  (succ2 (sel=context.adapt.by.moving.in occ2 occ1)))))


(defrule sel=context.adapt.by.moving.in (occ1 occ2)

  (RIPPLING 0 ("moving context in ~A into variable-positions of ~A" 2 1) ("ripple in" (1 2) col))

  (cond ((or (da-literal.is (rl-object occ2)) (da-term.is (rl-object occ2)))
	 (let* ((variables (set-difference (da-gterm.variables (rl-object occ1))
					   (da-gterm.variables (rl-object occ2))))
		top.gterm top.taf sink.colour.sets result)
	   (multiple-value-setq (top.gterm top.taf) (rl-object.top.object occ1))
	   (setq top.gterm (rl-object top.gterm))
	   (setq variables (remove-if #'(lambda (var)
					  (some #'(lambda (taf)
						    (and (not (da-taf.is.subtaf top.taf taf))
							 (da-gterm.colour (da-access taf top.gterm) sel*actual.colour)
							 (not (da-colour.is.fade 
							       (da-gterm.colour (da-access taf top.gterm) sel*actual.colour)))))
						(da-symbol.occurs.in.gterm var top.gterm)))
				      variables))
	   (cond ((setq sink.colour.sets (mapcar #'(lambda (var)
						     (cons (mapcar #'(lambda (taf)
								       (da-gterm.colour 
									(da-access taf (rl-object occ1)) sel*actual.colour))
								   (da-symbol.occurs.in.gterm var (rl-object occ1)))
							   var))
						 variables))
		  (cond ((setq result (sel=context.move.down.with.coordination occ2 sink.colour.sets
									       sel*actual.colour (list nil)))
			 (sel=context.adapt.binding (mapcar #'(lambda (set.term)
								(cons (cassoc (car set.term) sink.colour.sets) set.term))
							    result)
						    occ1 occ2)))))))))


(defun sel=context.adapt.binding (bindings occ1 occ2)

  ;;; Input:  bindings a list of triples (var.term colour.set value.term)

  (cond ((null bindings) nil)
	(t (let ((top.occ1 (rl-object.top.object occ1))
		 (top.occ2 (rl-object.top.object occ2))
		 values considered.vars)
	     (cond ((every #'(lambda (binding)
			       (or (null (car binding))
				   (member (car binding) considered.vars)
				   (cond ((and (every #'(lambda (taf)
							  (member (da-gterm.colour (da-access taf (rl-object top.occ1)) sel*actual.colour)
								  (second binding)))
						      (da-symbol.occurs.in.gterm (car binding) (rl-object top.occ1)))
					       (every #'(lambda (taf)
							  (member (da-gterm.colour (da-access taf (rl-object top.occ2)) sel*actual.colour)
								  (second binding)))
						      (da-symbol.occurs.in.gterm (car binding) (rl-object top.occ2))))
					  (push (car binding) considered.vars)
					  (push (third binding) values)))))
			   bindings)
		    (sel=unifier.replace.binding considered.vars values)))))))


(defrule sel=eq.insert.missing.context (occ1 occ2)

  (EQ 3 ("adapting ~A and ~A via insertion of context" 1 2)  ("insert context" (1 2) col nil))
  
  (let ((tafs (DA-GTERM.FADE.GTERMS (rl-object occ2) sel*actual.colour)) taf selected.term)
    (cond (tafs (setq taf (car tafs))
		(setq selected.term (da-gterm.copy (da-access taf (rl-object occ2))))
		(cond ((and (da-gterm.taf.is.defined (rl-object occ1) taf)
			    (sel=eq.blow.up.positition occ1 taf selected.term))
		       (rl-object.changes 
			occ2 (list (list 'colour.until taf 
					 (da-gterm.colourful.terms (da-access taf (rl-object occ2)) sel*actual.colour)
					 sel*actual.colour sel*eq.colours))
			nil (list "eq missed context1"))
		       t))))))


(defrule sel=eq.blow.up.positition (occ &others taf selected.term)

  (EQ 7 ("insertion of context in ~A, wished term: ~A" 1 2))

  (and (sel=context.insert occ taf (list selected.term) sel*actual.colour (incf sel*eq.colours)
			   (da-gterm.colour (da-access taf (rl-object occ)) sel*actual.colour))
       (sel=context.move.up.backtrack occ sel*actual.colour)))


;;;;;-------------------------------------------------------------------------------------------------------------------
;;;;;
;;;;;   Section ?  removing contexts 
;;;;;
;;;;;--------------------------------------------------------------------------------------------------------------------

(defun sel=eq.term.is.splitted.inside (occ1 occ2)

  (uni-term.diff.match (rl-object occ1) (rl-object occ2) nil t))


(defrule sel=ind.remove.context.directly (occ &others colour.key)

  (RIPPLING 5 ("thus eliminate the top-level context"))

  (let ((tafs (DA-GTERM.COLOURFUL.TERMS (rl-object occ) colour.key))
	(sel*constrains (copy-tree sel*constrains)))
    (push colour.key (getf sel*constrains 'colour.invariants))
    (cond ((member nil tafs) t)
	  ((some #'(lambda (taf)
		     (sel=eq.delete.context.along.taf occ taf colour.key))
		 tafs)
	   (sel=ind.remove.context.directly occ colour.key)))))


(defrule sel=eq.delete.context.along.taf (occ &others taf solution)

  (RIPPLING 3 ("at position ~A by some simplification rule" 2) ("delete context" (1) 3))

  (let (changed null.elem id.elem)
    (cond ((da-function.is (da-gterm.symbol (rl-object occ)))
	   (cond ((setq null.elem (getf (da-function.attributes (da-gterm.symbol (rl-object occ))) 'null))
		  (setq null.elem (car (da-attribute.arguments (car null.elem))))))
	   (cond ((setq id.elem (getf (da-function.attributes (da-gterm.symbol (rl-object occ))) 'identity))
		  (setq id.elem (car (da-attribute.arguments (car id.elem))))))))
    (or (null taf)
	(cond ((or (da-literal.is (rl-object occ)) (da-term.is (rl-object occ)))
	       (or (DB-MODIFIER.SELECTION
		    (rl-object occ) 'remove nil
		    #'(lambda (modifier)
			(sel=modifier.test.and.apply modifier occ nil solution)))
		   (DB-MODIFIER.SELECTION
		    (rl-object occ) 'remove nil
		    #'(lambda (modifier)
			(sel=modifier.try.to.apply modifier occ)))
		   (DB-MODIFIER.SELECTION
		    (rl-object occ) 'top.level nil
		    #'(lambda (modifier)
			(cond ((or (eq (da-gterm.symbol (da-modifier.value modifier)) null.elem)
				   (eq (da-gterm.symbol (da-modifier.value modifier)) id.elem))
			       (sel=modifier.try.to.apply modifier occ)))))))
	      (t (let* ((sub.taf (DA-TAF.LITERAL.TAF taf (rl-object occ)))
			(sel*refutation.depth (1+ sel*refutation.depth))			       
			(object (make-sel*object :gterm (uni-subst.apply 
							 (car (rl-object sel*eq.bindings))
							 (da-gterm.copy (da-gterm.without.tafs (rl-object occ) sub.taf)))
						 :type 'simplification
						 :substs (list nil)
						 :status 'connected)))
		   (cond ((and (sel=refute object)
			       (eq (sel=object.status object) 'solved))
			  (rl-object.change occ (da-gterm.copy (da-access sub.taf (rl-object occ)))
					    nil "solving subproblem"
					    (car (sel=object.substs object))
					    object)
			  (setq changed t)
			  (cond ((rl-object sel*eq.bindings)
				 (sel=apply.unifier (car (rl-object sel*eq.bindings)) occ solution)))
			  (sel=apply.unifier (car (sel=object.substs object)) occ solution)
			  (sel=eq.delete.context.along.taf occ (DA-TAF.DIFFERENCE.OF.TWO.TAFS taf sub.taf) solution))))))
	(and (cdr taf) (null changed)
	     (rl-with.sub.objects
	      occ (list (car (last taf)))
	      #'(lambda (sub.occ)
		  (sel=eq.delete.context.along.taf sub.occ (butlast taf 1) solution)))))))


(defun sel=substs.apply (substs term)

  (cond ((null substs) term)
	(t (uni-subst.apply (car substs) (sel=substs.apply (cdr substs) term)))))


;;;;;=========================================================================================================
;;;;;
;;;;;  Chapter 9
;;;;;  ---------
;;;;;
;;;;;  Reformulating terms
;;;;;
;;;;;=========================================================================================================


(defrule sel=term.express.in.terms.of (occ &others symbol)
  
  ;;; Edited :  8.8.87 by DH
  ;;; Input  :  OCC - an occurrence as defined in DT.
  ;;;           SYMBOL - a function symbol.
  ;;; Effect :  tries to find a solution for the equation TERM = SYMBOL(x(1) ... x(n)).
  ;;; Value  :  T, iff occ has modified, such that it's top-level symbol is SYMBOL2.

  (EQ 5 ("denote ~A in terms of ~A (...)" 1 2))

  (LET ((SYMBOL1 (DA-GTERM.SYMBOL (rl-object OCC))))
    (COND ((EQ SYMBOL1 SYMBOL) t)
	  ((AND (DA-PREFUN.IS SYMBOL1)                    ;;; KEINE MODIFIER MIT X = F(..X..)
		(DB-MODIFIER.SELECTION (rl-object OCC) 'TOP.LEVEL nil
				       #'(LAMBDA (MODIFIER)
					   (AND (EQ SYMBOL (DA-GTERM.SYMBOL (DA-MODIFIER.VALUE MODIFIER)))
						(SEL=MODIFIER.TEST.AND.APPLY MODIFIER OCC NIL NIL ))))))
	  ((AND (da-symbol.is symbol1)
		(DA-SYMBOL.HAS.ATTRIBUTE SYMBOL1 'STRUCTURE)
		(DA-SYMBOL.HAS.ATTRIBUTE SYMBOL 'STRUCTURE))
	   nil))))


(defun sel=equalize.find.function.symbol (occ1 occ2 used.symbols)
  (let ((symbol1 (da-gterm.symbol (rl-object occ1))) (symbol2 (da-gterm.symbol (rl-object occ2))))
    (cond ((and (da-symbol.is symbol1) (da-symbol.has.aTTRIBUTE SYMBOL1 'STRUCTURE))
	   (cond ((not (member SYMBOL1 used.symbols)) SYMBOL1)))
	  ((and (da-symbol.is symbol2) (DA-SYMBOL.HAS.ATTRIBUTE SYMBOL2 'STRUCTURE))
	   (cond ((not (member SYMBOL2 used.symbols)) SYMBOL2)))
	  ((and (not (member symbol1 used.symbols))
		(da-function.is symbol1)
		(eq symbol1 symbol2)) symbol1)
	  ((and (not (member symbol1 used.symbols))
		(da-symbol.is symbol1)
		(OR (NOT (DA-FUNCTION.IS SYMBOL1))
		    (not (da-symbol.is symbol2))
		    (NOT (DA-PREFUN.IS.LESS SYMBOL2 SYMBOL1))))
	   symbol1)
	  ((and (not (member symbol2 used.symbols))
		(da-symbol.is symbol2)
		(OR (NOT (DA-FUNCTION.IS SYMBOL2))
		    (not (da-symbol.is symbol1))
		    (NOT (DA-PREFUN.IS.LESS SYMBOL1 SYMBOL2))))
	   symbol2)
	  ((and (not (member symbol1 used.symbols)) (da-symbol.is symbol1)) symbol1)
	  ((and (not (member symbol2 used.symbols)) (da-symbol.is symbol2)) symbol2)
	  ((and (da-function.is symbol1)
		(da-function.is symbol2))
	   (find-if #'(lambda (symbol)
			(not (member symbol used.symbols)))
		    (intersection (DA-FUNCTION.DEFINING.SYMBOLS SYMBOL1)
				  (DA-FUNCTION.DEFINING.SYMBOLS SYMBOL2)))))))



;;;;;=========================================================================================================
;;;;;
;;;;;  Chapter 10
;;;;;  ----------
;;;;;
;;;;;  Others
;;;;;
;;;;;=========================================================================================================


(defun sel=eq.colourize.top.level (occ1 occ2)

  ;;;; COLOUR.TOP TAF KEY COLOUR

  (rl-object.changes occ1 (list (list 'colour.top nil sel*actual.colour (incf sel*eq.colours))) nil (list ""))
  (rl-object.changes occ2 (list (list 'colour.top nil sel*actual.colour sel*eq.colours)) nil (list "")))



(DEFUN sel=GTERM.prefuns (EXPRESSION colour.key &OPTIONAL FCTS)
  
  ;;; Input  : an expression and optional a list of variables
  ;;; Value  : the list of all function symbols occurring in the expression and in fcts

  (COND ((and (DA-prefun.IS (DA-GTERM.SYMBOL EXPRESSION))
	      (da-colour.is.fade (da-gterm.colour EXPRESSION colour.key)))
	 (SETQ FCTS (ADJOIN (DA-GTERM.SYMBOL EXPRESSION) FCTS))))
  (COND ((or (not (DA-prefun.IS (DA-GTERM.SYMBOL EXPRESSION)))
	     (da-colour.is.fade (da-gterm.colour EXPRESSION colour.key)))
	 (MAPC #'(LAMBDA (GTERM)
		   (SETQ FCTS (sel=GTERM.prefuns GTERM colour.key FCTS)))
	       (DA-GTERM.TERMLIST EXPRESSION))))
  FCTS)


(defun sel=symbol.occurs.in.context (symbol gterm colour.key &optional sign)

  (LET ((COUNTER 0))
    (cond ((or (null (da-gterm.colour gterm colour.key))
	       (da-colour.is.fade (da-gterm.colour gterm colour.key)))
	   (COND ((AND (EQ SYMBOL (DA-GTERM.SYMBOL GTERM))
		       (OR (NULL SIGN) (COND ((DA-LITERAL.IS GTERM) (EQ SIGN (DA-LITERAL.SIGN GTERM))))))
		  (CONS NIL
			(MAPCAN #'(LAMBDA (SUB.GTERM)
				(INCF COUNTER)
				(MAPL #'(LAMBDA (TAFS)
					  (SETF (CAR TAFS) (NCONC1 (CAR TAFS) COUNTER)))
				      (sel=symbol.occurs.in.context SYMBOL SUB.GTERM colour.key SIGN)))
			    (DA-GTERM.TERMLIST GTERM))))
		 (t (MAPCAN #'(LAMBDA (SUB.GTERM)
				(INCF COUNTER)
				(MAPL #'(LAMBDA (TAFS)
					  (SETF (CAR TAFS) (NCONC1 (CAR TAFS) COUNTER)))
				      (sel=symbol.occurs.in.context SYMBOL SUB.GTERM colour.key SIGN)))
			    (DA-GTERM.TERMLIST GTERM))))))))

	

(defun sel=gterm.max.symbols (gterm1 gterm2 colour.key)

  (let* ((prefuns.1 (sel=GTERM.prefuns gterm1 colour.key))
	 (prefuns.2 (sel=GTERM.prefuns gterm2 colour.key))
	 (union (union prefuns.1 prefuns.2))
	 (intersection (intersection prefuns.1 prefuns.2))
	 max.symbols common.max.symbols left.max.symbols right.max.symbols)
    (setq max.symbols (remove-if-not #'(lambda (prefun)
					 (da-prefun.is.independent prefun (remove prefun union)))
				     union))
    (setq common.max.symbols (intersection max.symbols intersection))
    (setq left.max.symbols (intersection (set-difference max.symbols intersection) prefuns.1))
    (setq right.max.symbols (intersection (set-difference max.symbols intersection) prefuns.2))
    (cond ((and (null common.max.symbols) (null right.max.symbols))
	   (setq left.max.symbols (append left.max.symbols
					  (remove-if-not
					   #'(lambda (prefun)
					       (and (not (member prefun left.max.symbols))
						    (or (not (da-function.is prefun))
							(and (not (da-function.is.constructor prefun))
							     (not (da-function.is.selector prefun))))
						    (not (member prefun prefuns.2))
						    (da-prefun.is.independent prefun prefuns.2)))
					   prefuns.1))))
	  ((and (null common.max.symbols) (null left.max.symbols))
	   (setq right.max.symbols (append right.max.symbols
					  (remove-if-not 
					   #'(lambda (prefun)
					       (and (not (member prefun right.max.symbols))
						    (or (not (da-function.is prefun))
							(and (not (da-function.is.constructor prefun))
							     (not (da-function.is.selector prefun))))
						    (not (member prefun prefuns.1))
						    (da-prefun.is.independent prefun prefuns.1)))
					   prefuns.2)))))
    (values common.max.symbols left.max.symbols right.max.symbols)))



;;;;;-------------------------------------------------------------------------------------------------------------------
;;;;;
;;;;;   Section ? :    Applying modifiers to formulas and terms
;;;;;
;;;;;--------------------------------------------------------------------------------------------------------------------


(defun sel=modifier.try.to.apply (modifier occ &optional type)

  (car (sel=modifier.try.to.apply1 occ modifier type)))


(defrule sel=modifier.try.to.apply1 (occ &others modifier type)

  (EQ 2 ("enable application of ~A in ~A" 2 1) ("enable" (1) col (2)))

  (let (tafs result colour.key (gterm (da-gterm.copy (rl-object occ))))
    (cond ((and (neq type 'unify)
		(setq colour.key (find-if #'(lambda (colour.key)
					      (and (sel=modifier.try.check.constrains gterm modifier colour.key)
						   (sel=modifier.adapt occ gterm colour.key)))
					  (uni-term.diff.match (da-modifier.input modifier) gterm
							       (da-gterm.variables (da-modifier.input modifier)) T))))
	   (setq tafs (da-gterm.max.coloured.gterms (rl-object occ) colour.key nil t))
	   (rl-with.sub.objects occ (car tafs)
				#'(lambda (s.occ)
				    (setq result (sel=modifier.test.and.apply modifier s.occ nil nil))))
	   (list result))
	  ((and (neq type 'match) (da-gterm.variables (rl-object occ)))
	   (some #'(lambda (taf)
		     (rl-with.sub.objects occ taf
					  #'(lambda (s.occ)
					      (setq result (sel=modifier.test.and.apply modifier s.occ nil nil)))))
		 (da-symbol.occurs.in.gterm (da-gterm.symbol (da-modifier.input modifier)) (rl-object occ)))
	   (list result)))))


(defun sel=modifier.try.check.constrains (gterm modifier colour.key.2)

  (every #'(lambda (colour.key.1)
	     (sel=modifier.try.check.colours gterm modifier colour.key.1 colour.key.2))
	 (getf sel*constrains 'colour.invariants)))


(defun sel=modifier.try.check.colours (gterm modifier colour.key1 colour.key2)

  (sel=gterm.check.result (da-modifier.value modifier) (sel=gterm.common.term gterm (da-modifier.input modifier) 
										     colour.key1 colour.key2)))

(defun sel=gterm.common.term (gterm1 gterm2 color1 color2)

  (cond ((not (da-colour.is.fade (da-gterm.colour gterm1 color2)))
	 (cond ((not (da-colour.is.fade (da-gterm.colour gterm1 color1)))	      
		(list (cons (da-gterm.symbol gterm2)
			    (mapcar #'(lambda (sub1 sub2)
					(sel=gterm.common.term sub1 sub2 color1 color2))
				    (da-gterm.termlist gterm1) (da-gterm.termlist gterm2)))))
	       (t (mapcan #'(lambda (sub1 sub2)
			      (sel=gterm.common.term sub1 sub2 color1 color2))
			  (da-gterm.termlist gterm1) (da-gterm.termlist gterm2)))))
	(t (mapcan #'(lambda (sub1)
		       (sel=gterm.common.term sub1 gterm2 color1 color2))
		   (da-gterm.termlist gterm1)))))



(defun sel=gterm.check.result (gterm structure)

  (every #'(lambda (struct)
	     (some #'(lambda (taf)
		       (every #'(lambda (subterm substruct)
				  (sel=gterm.check.result subterm substruct))
			      (da-gterm.termlist (da-access taf gterm)) (cdr struct)))
		   (da-symbol.occurs.in.gterm (car struct) gterm)))
	 structure))


(defrule sel=modifier.adapt (occ &others gterm colour.key)

  (eq 10 ("adapt ~A to modifier" 1))

  (rl-object.changes occ (cons (list 'colour.all nil colour.key (da-colour.faded))
			       (sel=gterm.colour.information gterm colour.key nil nil))
		     nil nil)
  (sel=context.move.up.backtrack occ colour.key))


(defun sel=resolution.apply (database.entry occ  &optional copy.flag)

  ;;; 
  
  (let* ((right (DA-GTERM.WITHOUT.TAFS (third database.entry) (fourth database.entry)))
	 (renaming (uni-create.var.renaming (da-gterm.variables right)))
	 (unifiers (uni-literal.unify (uni-subst.apply renaming (car database.entry)) (rl-object occ) 'opposite)))
    
    (cond (unifiers
	   (setq right (uni-subst.apply (car unifiers)
					(uni-subst.apply renaming right)))
	   (let* ((vars (da-gterm.variables (rl-object occ)))
		  (rest.unifier (UNI-SUBST.RESTRICTION (car unifiers) #'(lambda (var) (member var vars)))))
	     (sel=apply.unifier rest.unifier occ)
	     (rl-object.change occ (cond (copy.flag (da-gterm.create 'and (list right (da-gterm.copy (rl-object occ)))))
					 (t right))
			       nil (third database.entry) rest.unifier)
	     t)))))



(defun sel=modifier.test.and.apply (modifier occ input.taf colour.key &key ignore.conds value.taf test.fct)

  ;;; Input:   a modifier, an object, the taf denoting the subterm of interest, a colour key and 
  ;;;          a subterm of interest in the right-hand side.
  ;;; Effect:  tests whether \verb$MODIFIER$ is applicable and if so \verb$MODIFIER$ is applied to 
  ;;;          \verb$OCC$.
  ;;; Value:   T if \verb$MODIFIER$ was applied.

  (let (chain value unifiers apply.taf add.constrains)
    (multiple-value-setq (unifiers apply.taf) 
			 (sel=modifier.test.unify modifier (rl-object occ) input.taf colour.key value.taf))
    (some #'(lambda (unifier)
	      (setq value (uni-subst.apply unifier (da-modifier.value modifier) T
					   (cond (colour.key (uni-environment (cons 'key (da-cmodifier.solution modifier)))))
					   colour.key))
	      (cond ((and (multiple-value-setq (unifier add.constrains)
			     (sel=modifier.test.condition modifier unifier colour.key ignore.conds occ apply.taf))
			  (or (null test.fct) (funcall test.fct value))
			  (setq value (sel=modifier.apply.check.constrains (da-access apply.taf (rl-object occ))
									   value modifier unifier colour.key)))
		     (sel=modifier.apply modifier (car unifier) occ apply.taf value colour.key chain add.constrains)
		     t)))
	  unifiers)))


(defun sel=modifier.test.unify (modifier gterm taf colour.key &optional value.taf)

  ;;; Input:  a modifier, an object denoting a term, a term-access-function
  ;;; Effect: unifies the left side q of modifier with that subterm of occ,
  ;;;         such that occ | taf coincides with q | adjustment.taf.
  ;;; Value:  a list of c-unifiers, the taf on which the modifier was applied

  (let* ((adjustment.taf (da-modifier.input.taf modifier))
	 (other.side.tafs (cond ((DA-cmodifier.is modifier)
				 (da-cmodifier.value.taf modifier))))
	 (apply.taf (da-taf.super.taf taf (da-taf.length adjustment.taf)))
	 (adjusted.taf2 (butlast value.taf (length apply.taf)))
	 apply.gterm)
    (cond ((and (>= (da-taf.length taf) (da-taf.length adjustment.taf))
		(or (null value.taf) (da-taf.is.subtaf apply.taf value.taf)))
	   (setq apply.gterm (da-access apply.taf gterm))
	   (values (remove-if #'(lambda (uni)
				  (and sel*eq.bindings (null (sel=bindings.add.unifier uni))))
			      (uni-gterm.unify (da-modifier.input modifier)
					       apply.gterm
					       (cond (colour.key (uni-environment (cons 'key (da-cmodifier.solution modifier)))))
					       (cond (colour.key (uni-environment (cons 'key colour.key))))
					       (nconc (list (cons adjustment.taf (subseq taf 0 (length adjustment.taf))))
						      (cond (value.taf (list (cons (car other.side.tafs) adjusted.taf2)))))
					       'opposite))
		   apply.taf)))))


(defun sel=modifier.test.condition (modifier unifier colour.key ignore.conds &optional occ taf)

  (let ((add.clauses (sel=occ.conjunctive.parts occ taf)) chain)
    (DB-WITH.GTERMS.INSERTED
     add.clauses 'theorem nil
     (setq chain (sel=refute.condition (da-modifier.condition modifier) unifier)))
    (cond ((or (eq chain t) (and chain (member nil (sel=object.substs chain))))
	   (list unifier))
	  ((and chain (null colour.key)
		(setq unifier (uni-subst.merge unifier (car (sel=object.substs chain)))))
	   unifier)
	  (ignore.conds
	   (values (list unifier) (da-modifier.condition modifier))))))


(defun sel=modifier.apply (modifier unifier occ apply.taf value colour.key chain add.constrains)

  ;;; Input:   a modifier, a unifier of its left-hand side with the gterm denoted by \verb$OCC$,
  ;;;          and \verb$APPLY.TAF$ the new value and a colour key.
  ;;; Effect:  applies modifier to occ
  ;;; Value:   undefined

  (let* ((vars (nconc (da-gterm.variables (rl-object occ))
		      (da-gterm.xvariables (rl-object occ) colour.key)))
	 (rest.unifier (UNI-SUBST.RESTRICTION unifier #'(lambda (var)
							  (or (member var vars)
							      (member var sel*variables)))))
	 top.object top.object.taf)
    (multiple-value-setq (top.object top.object.taf) (rl-object.top.object occ))
    (uni-subst.replace unifier value colour.key colour.key)
    (rl-object.changes top.object 
		       (nconc (mapcar #'(lambda (taf.value)
					  (list 'replace (car taf.value) (cdr taf.value)))
				      (uni-subst.replacements rest.unifier (rl-object top.object) 
							      (uni-environment (cons 'key colour.key)) colour.key))
			      (list (list 'replace (append apply.taf top.object.taf) value)))
		       nil
		       (list modifier rest.unifier chain))
    (cond (add.constrains
	   (cond ((da-term.is (rl-object occ)) 
		  (setq top.object.taf (da-taf.literal.taf top.object.taf (rl-object top.object))))
		 (t (setq top.object.taf (append (da-taf.literal.taf apply.taf (rl-object occ)) top.object.taf))))
	   (rl-object.changes top.object 
			      (list (list 'replace top.object.taf
					  (norm-normalize.gterm
					   (da-gterm.create 'or (cons (da-access top.object.taf (rl-object top.object))
								      (mapcar #'(lambda (gterm)
										  (uni-subst.apply unifier gterm))
									      add.constrains))))))
			      nil nil)))))

;;;;;  Tests considering sel*constrains.


(defun sel=modifier.apply.check.constrains (old.term new.term modifier unifier colour.key)

  ;;; Input:   two gterms, a modifier, the unifier of its application and a colour key
  ;;; Effect:  tests whether \verb$NEW.TERM$ can be colourized in such a way that it has
  ;;;          the same skeletons wrt the actual colour keys of \verb$SEL*CONSTRAINS$ 
  ;;;          as \verb$OLD.TERM$.
  ;;; Value:   the new coloured term iff the test is successful.

  (cond ((and (or (null colour.key) 
		  (not (getf sel*constrains 'var.restriction))
		  (sel=modifier.test.var.restrictions old.term modifier unifier colour.key))
	      (every #'(lambda (colour.key.2)
			 (cond ((eq colour.key colour.key.2))
			       ((setq new.term (sel=gterm.propagate.colours old.term new.term colour.key.2)))))
		     (getf sel*constrains 'colour.invariants)))
	 new.term)))


(defun sel=gterm.propagate.colours (old.term new.term colour.key)

  (da-gterm.colourize new.term (da-colour.faded) colour.key)
  (cond ((sel=gterm.propagate.skels old.term new.term colour.key nil)
	 new.term)))


(defun sel=gterm.propagate.skels (old.term new.term colour.key new.term.taf &optional only.skel)

  ;;; Input:   two gterms and a colour key
  ;;; Effect:  tests whether ...

  (let ((subtafs (da-gterm.colourful.terms old.term colour.key)) used.tafs tafs)
    (every #'(lambda (subtaf)
	       (cond ((setq tafs (sel=gterm.propagate.skel (da-access subtaf old.term) 
							   new.term colour.key new.term.taf used.tafs only.skel))
		      (setq used.tafs (append tafs used.tafs)))))
	   subtafs)))


(defun sel=gterm.propagate.skel (org.term new.term colour.key new.term.taf used.tafs &optional only.skel)

  (let ((subtaf (da-taf.create.zero new.term.taf)))
    (cond ((and (every #'(lambda (used.taf) (not (da-taf.is.subtaf new.term.taf used.taf)))
		       used.tafs)
		(eq (da-gterm.symbol org.term) (da-gterm.symbol new.term))
		(cond ((every #'(lambda (org.sub.term new.sub.term)
				  (setq subtaf (da-taf.create.next subtaf))
				  (sel=gterm.propagate.skels 
				   org.sub.term new.sub.term colour.key subtaf
				   ; (or only.skel (da-gterm.is.coloured org.term colour.key))
				   nil))
			      (da-gterm.termlist org.term)
			      (da-gterm.termlist new.term)))
		      (t (da-gterm.colourize new.term (da-colour.faded) colour.key)
			 nil)))
	   (setf (da-gterm.colour new.term colour.key) 
		 (da-gterm.colour org.term colour.key))
	   (list new.term.taf))
	  ((not only.skel)
	     (setq subtaf (da-taf.create.zero new.term.taf))
	     (some #'(lambda (sub.new.term)
		       (setq subtaf (da-taf.create.next subtaf))
		       (sel=gterm.propagate.skel org.term sub.new.term colour.key subtaf used.tafs nil))
		   (da-gterm.termlist new.term))))))


;(defun sel=gterm.propagate.colours (old.term new.term colour.key)

;  ;;; Input:   two gterms and a colour key
;  ;;; Effect:  tests whether ...

;  (let (gterm)
;    (da-gterm.colourize new.term (da-colour.faded) colour.key)
;    (cond ((every #'(lambda (taf)
;		      (setq gterm (da-access taf old.term))
;		      (mapc #'(lambda (new.taf)
;				(sel=gterm.colourize.according.to (da-access new.taf new.term) colour.key gterm colour.key))
;			    (da-gterm.occurs.in.gterm gterm new.term)))
;		  (da-gterm.colourful.terms old.term colour.key))
;	   new.term))))


;(defun sel=gterm.colourize.according.to (gterm1 colour.key.1 gterm2 colour.key.2)

;  (setf (da-gterm.colour gterm1 colour.key.1) (da-gterm.colour gterm2 colour.key.2))
;  (mapc #'(lambda (sub.term1 sub.term2)
;	    (sel=gterm.colourize.according.to sub.term1 colour.key.1 sub.term2 colour.key.2))
;	(da-gterm.termlist gterm1)
;	(da-gterm.termlist gterm2)))


(defun sel=modifier.test.var.restrictions (old.gterm modifier unifier colour.key)

  ;;; Input:   a modifier, a unifier to apply modifier on occ, the actual term-access function and a colour
  ;;;          key.
  ;;; Effect:  tests whether the instantiated value of the modifier contains ...

  (let ((sub.term))
    (every #'(lambda (sub.taf)
	       (setq sub.term (da-access sub.taf old.gterm))
	       (or (da-gterm.is.fade sub.term colour.key)
		   (progn (setq sub.term (uni-subst.apply unifier sub.term t
							  (uni-environment (cons 'key (da-cmodifier.solution modifier))) 
							  colour.key))
			  (some #'(lambda (taf2)
				    (da-variable.is (da-term.symbol (da-access taf2 sub.term))))
				(da-gterm.colourful.terms sub.term colour.key)))))
	   (da-gterm.tafs old.gterm #'(lambda (gterm) (da-variable.is (da-gterm.symbol gterm)))))))



(defun sel=apply.unifier (unifier occ &optional colour.key)
  
  (setq occ (rl-object.top.object occ))
  (cond (unifier
	 (mapc #'(lambda (taf.value)
		   (rl-object.change occ (cdr taf.value) (car taf.value) "Instantiation" unifier))
	       (uni-subst.replacements unifier (rl-object occ) (uni-environment (cons 'key colour.key)) colour.key)))))




(defun sel=refute.condition (condition subst &optional simpl)

  (cond ((null condition) t)
	((and (> sel*refutation.depth 0) simpl) nil)
	((< sel*refutation.depth 2)
	 (let ((sel*refutation.depth (1+ sel*refutation.depth))
	       (sel*case.condition 'inhibit)
	       gterm edge object sol result)
	   (setq gterm (norm-normalize.gterm (da-gterm.create 'or
							      (mapcar #'(lambda (gt)
									  (uni-subst.apply subst gt))
								      condition))))
	   (setq sol (rl-with.problem gterm 'gterm nil 'binding
				      #'(lambda (occ sel*eq.bindings)
					  (cond ((setq result (sel=refute.instance.of.gterm occ simpl))
						 (setq gterm (rl-object occ)))))))
	   (cond (result (setq edge (make-sel*edge :type 'modification :status 'open
						   :succ.object (make-sel*object :gterm (da-literal.false)
										 :substs (list nil)
										 :type 'trivial
										 :status 'solved)
						   :modification sol
						   :modifier nil
						   :taf nil))
			 (cond ((sel=edge.finish? edge)
				(setq object (make-sel*object :gterm gterm
							      :succs (list (list nil 'output edge))
							      :status 'solved
							      :type 'simplification
							      :substs (list (sel=edge.input.subst edge))))
				(setf (sel=object.prev.object (sel=edge.succ.object edge)) object)
				object))))))))


(defun sel=refute.instance.of.gterm (occ simpl)

  ;;; Input:   a gterm, a substitution and a term-access-function
  ;;; Effect:  tests whether the instance of gterm is deducable inside
  ;;;          the given deduction.
  ;;; Value:   a list of dotted pairs (taf . chain) where chain is an
  ;;;          edge denoting a deduction of a literal and taf is its
  ;;;          access-function. 

  (let ((taf (da-taf.create.zero nil)))
    (cond ((da-literal.is (rl-object occ))
	   (sel=refute.instance.of.literal occ simpl))
	  ((eq 'AND (da-gterm.symbol (rl-object occ)))
	   (some #'(lambda (lit)
		     (declare (ignore lit))
		     (setq taf (da-taf.create.next taf))
		     (rl-with.sub.objects occ taf
					  #'(lambda (sub.occ)
					      (sel=refute.instance.of.gterm sub.occ simpl))))
	       (da-gterm.termlist (rl-object occ))))
	  ((eq 'or (da-gterm.symbol (rl-object occ)))
	   (every #'(lambda (lit)
		      (declare (ignore lit))
		      (setq taf (da-taf.create.next taf))
		      (rl-with.sub.objects occ taf
					   #'(lambda (sub.occ)
					       (sel=refute.instance.of.gterm sub.occ simpl))))
		  (da-gterm.termlist (rl-object occ)))))))


(defun sel=refute.instance.of.literal (occ simpl)

  (let (symbol term result lit)
    (rl-object.change occ (da-gterm.copy (eg-eval (rl-object occ))) nil "Symbolic Evaluation")
    (setq lit (rl-object occ))
    (cond ((member lit sel*failed.lemma.cache :test 'uni-gterm.are.equal) nil)
	  (t (multiple-value-setq (term symbol)
				  (DA-LITERAL.IS.NORMALIZED.MATCH (rl-object occ) (da-sign.minus)))
	     (cond ((and term (null simpl))
		    (rl-with.sub.objects occ (da-taf.create.left)
					 #'(lambda (sub.occ)
					     (setq result (sel=term.express.in.terms.of sub.occ symbol))))
		    (cond ((and (null result) (not (da-function.is.reflexive symbol)))
			   (setq result (sel=refute.instance.by.simplification occ nil)))))
		   ((setq result (sel=refute.instance.by.simplification occ simpl))))
	     (cond ((null result) (push lit sel*failed.lemma.cache)))
	     result))))


(defun sel=refute.instance.of.literal.using.database (occ)

  (let (result)
    (and (da-literal.is (rl-object occ))
	 (db-predicate.database.selection
	  (rl-object occ) (da-sign.other.sign (da-literal.sign (rl-object occ)))
	  #'(lambda (entry)
	      (and (eq 0 (second entry))
		   (progn (rl-with.objects (car entry) 'gterm
					   #'(lambda (occ2)
					       (sel=simpl.gterm occ2)
					       (cond ((and (da-literal.is (rl-object occ2))
							   (setq result (uni-literal.match (rl-object occ2)
											   (rl-object occ) T 'ignore)))
						      (rl-object.change occ (da-literal.false) nil (third entry)
									(car result))))))
			  result)))))
    result))


(defrule sel=refute.instance.by.simplification (occ simpl)

  (RIPPLING 7 ("proving ~A by simplification" 1))

  (let (result)
    (cond ((da-formula.is.false (rl-object occ)) t)
	  (t (sel=simpl.gterm occ)
	     (cond ((da-formula.is.false (rl-object occ)) t)
		   ((and (da-literal.is.negated.equation (rl-object occ))
			 (null simpl))
		    (rl-with.sub.objects occ (da-taf.create.left)
					 occ (da-taf.create.right)
					 #'(lambda (occ1 occ2)
					     (sel=simpl.term occ1 nil)
					     (sel=simpl.term occ2 nil)
					     (setq result (sel=equalize.gterms occ1 occ2))))
		    result)
		   ((not (da-literal.is (rl-object occ)))
		    (sel=refute.instance.of.gterm occ simpl))
		   (t (sel=refute.instance.of.literal.using.database occ)))))))


(defmacro sel=term.status (gterm) `(getf (da-gterm.attributes ,gterm) 'status))


(defun sel=literals.substitution (literals)

  (let (termsubst left right)
    (mapc #'(lambda (lit)
	      (cond ((da-literal.is.equation lit)
		     (setq left (car (da-literal.termlist lit)))
		     (setq right (second (da-literal.termlist lit)))
		     (cond ((and (da-function.is (da-term.symbol left))
				 (da-function.skolem (da-term.symbol left))
				 (not (da-gterm.occurs.in.gterm left right)))
			    (setq termsubst (uni-termsubst.create termsubst left right)))
			   ((and (da-function.is (da-term.symbol right))
				 (da-function.skolem (da-term.symbol right))
				 (not (da-gterm.occurs.in.gterm right left)))
			    (setq termsubst (uni-termsubst.create termsubst right left)))))))
	  literals)
    termsubst))


	       
;;;;;-------------------------------------------------------------------------------------------------------------------
;;;;;
;;;;;   Section ? :    Handling the proof-tree
;;;;;
;;;;;--------------------------------------------------------------------------------------------------------------------



(defun sel=object.conjunctive.parts (object taf)

  (let ((gterm (sel=object.gterm object)) counter all.clauses new.clause
	(renaming (uni-create.var.renaming (set-difference (da-gterm.variables (sel=object.gterm object))
							   sel*variables))))
    (setq taf (reverse taf))
    (while taf
      (cond ((eq 'and (da-gterm.symbol gterm))
	     (setq counter 0)
	     (mapc #'(lambda (arg)
		       (incf counter)
		       (cond ((not (eql counter (car taf)))
			      (setq new.clause (uni-subst.apply renaming arg))
			      (sel=gterm.mark.literals new.clause arg)
			      (push new.clause all.clauses))))
		   (da-gterm.termlist gterm))))
      (setq gterm (nth (1- (car taf)) (da-gterm.termlist gterm)))
      (pop taf))
    all.clauses))


(defun sel=occ.conjunctive.parts (occ taf)

  (let (gterm top.taf  counter all.clauses)
    (multiple-value-setq (gterm top.taf) (rl-object.top.object occ))
    (cond ((da-gterm.is (rl-object gterm))
	   (setq gterm (rl-object gterm))
	   (setq taf (append (reverse top.taf) (reverse taf)))
	   (while taf
	     (cond ((eq 'and (da-gterm.symbol gterm))
		    (setq counter 0)
		    (mapc #'(lambda (arg)
			      (incf counter)
			      (cond ((not (eql counter (car taf)))
			      (push arg all.clauses))))
			  (da-gterm.termlist gterm))))
	     (setq gterm (nth (1- (car taf)) (da-gterm.termlist gterm)))
	     (pop taf))
	   all.clauses))))


(defun sel=gterm.mark.literals  (gterm1 gterm2)

  (COND ((DA-LITERAL.IS GTERM1)
	 (setf (getf (da-literal.attributes gterm1) 'origin) gterm2))
	((DA-TERM.IS GTERM1) NIL)
	(T (MAPC #'(LAMBDA (SUB.TERM1 sub.term2)
		     (sel=gterm.mark.literals SUB.TERM1 sub.term2))
		 (DA-GTERM.TERMLIST GTERM1) (DA-GTERM.TERMLIST GTERM2)))))


  
(defun sel=object.gterm.compute (object)
  (let ((gterm (da-gterm.copy (sel=object.gterm object))))
    (mapc #'(lambda (taf.edges)
	      (cond ((and (eq (second taf.edges) 'output)
			  (third taf.edges))
		     (setq gterm (sel=object.reverse.modifications gterm
								   (sel=edge.modification (third taf.edges))
								   (sel=edge.status (third taf.edges))
								   (car taf.edges))))))
	  (sel=object.succs object))
    (cond ((sel=object.edge object)
	   (setq gterm (da-replace (sel=edge.taf (sel=object.edge object)) gterm (da-literal.false)))))
    gterm))


(defun sel=object.reverse.modifications (gterm modification status &optional taf)

  (cond ((null modification) (da-gterm.copy gterm))
	((eq status 'delayed) (da-gterm.copy gterm))
	(t (setq gterm (sel=object.reverse.modifications gterm (cdr modification) status taf))
	   (setq gterm (da-replace taf gterm 
				   (rl=modification.change.context (da-access taf gterm) (car modification) t))))))


(defun sel=object.undo.edge (object taf)

  (let* ((taf.edges (assoc taf (sel=object.succs object) :test 'equal)))
    (cond ((and (eq (second taf.edges) 'output) (third taf.edges))
	   (cond ((member (sel=object.status object) '(connected connected.first connected.prop solved))
		  (setf (sel=object.status object) 'connected))
		 (t (setf (sel=object.status object) 'sketch)))
	   (cond ((sel=edge.modification (third taf.edges))
		  (setf (sel=object.gterm object)
			(sel=object.change.edge.modification (sel=object.gterm object)
							     (sel=edge.modification (third taf.edges))
							     T (car taf.edges)))))))
    (cond (taf.edges (sel=object.invalid.verification (sel=object.prev.object object))  ;; JCL cond (taf.edges ... ) eingefuegt
		     (setf (second taf.edges) nil)))))


(defun sel=object.undo.all.edges (object taf)

  (mapc #'(lambda (taf.edges)
	    (cond ((not (equal taf (car taf.edges)))
		   (cond ((and (eq (second taf.edges) 'output)
			       (third taf.edges)
			       (sel=edge.modification (third taf.edges)))
			  (setf (sel=object.gterm object)
				(sel=object.change.edge.modification (sel=object.gterm object)
								     (sel=edge.modification (third taf.edges))
								     T (car taf.edges)))))
		   (setf (second taf.edges) nil))))
	(sel=object.succs object))
  (cond ((member (sel=object.status object) '(connected connected.first connected.prop solved))
	 (setf (sel=object.status object) 'connected))
	(t (setf (sel=object.status object) 'sketch)))
  (sel=object.invalid.verification (sel=object.prev.object object)))


(defun sel=object.invalid.verification (object)
 
  (cond (object (sel=object.invalid.verification.1 object))))


(defun sel=object.invalid.verification.1 (object)

  (cond (object
	 (cond ((eq (sel=object.status object) 'solved) (setf (sel=object.status object) 'connected.first)))
	 (sel=object.invalid.verification.1 (sel=object.prev.object object)))))


(defun sel=object.insert.edge (object taf edge)

  ;;; Input:   a sel*object, a term-access-function and an sel*edge
  ;;; Effect:  The edge is inserted as an active edge its modifications are
  ;;;          performed until the first choice point.

  (let ((taf.edges (assoc taf (sel=object.succs object) :test 'equal)))
    (cond ((sel=edge.modification edge)
	   (setf (sel=object.gterm object)
		 (sel=object.change.edge.modification (sel=object.gterm object)
						      (sel=edge.modification edge)
						      nil (car taf.edges)))))
    (setf (cddr taf.edges) (cons edge (delete edge (cdddr taf.edges))))
    (setf (second taf.edges) 'output)))



(defun sel=object.edge.of.literal (object taf lit)
  
  (find-if #'(lambda (edge)
	       (and edge (eq (sel=edge.modifier edge) lit)))
	   (cddr (assoc taf (sel=object.succs object) :test 'equal))))


(defun sel=object.change.edge.modification (gterm modification reverse? &optional taf)

  ;;; Input:   a gterm and a modification-sexpr computed by the RL-module
  ;;; Effect:  undos the manipulations specified by modification without
  ;;;          any choice-point. If reverse? is T, modification
  ;;;          will be handled from right to left.
  ;;; Value:   the modified gterm

  (da-replace taf gterm (sel=object.change.edge.modification.1 (da-access taf gterm) modification reverse?)))



(defun sel=object.change.edge.modification.1 (gterm modification reverse?)

  (cond ((null modification) gterm)
	(t  (cond (reverse? (setq gterm (sel=object.change.edge.modification.1
					 gterm (cdr modification) reverse?))))
	    (setq gterm (rl=modification.change.context gterm (car modification)))
	    (setf (rl=mod.inverted (car modification)) (not (rl=mod.inverted (car modification))))
	    (cond (reverse? gterm)
		  (t (sel=object.change.edge.modification.1 gterm (cdr modification) reverse?)))))
  gterm)



(defun sel=object.insert.mod.edge (object modification status &optional formula)

  (let (edge)
    (cond ((null formula) (setq formula (da-gterm.copy (sel=object.gterm object)))))
    (setq edge (sel=edge.introduce object nil 'modification
				   (make-sel*object :gterm formula :type status :status 'connected 
						    :substs (list nil))
				   'modification))
    (sel=edge.establish edge modification)))


(defun sel=object.insert.subproblem.edge (object taf type)

  (let (edge formula subproblem)
    (setq formula (da-gterm.copy (sel=object.gterm object)))
    (setq subproblem (da-access taf formula))
    (setq formula (da-replace taf formula (da-literal.false)))
    (setq edge (sel=edge.introduce object taf 'subproblem
				   (make-sel*object :gterm formula :type 'simplification :status 'connected :substs (list nil))
				   (make-sel*object :gterm subproblem
						    :type type
						    :substs (list nil)
						    :status 'connected)))
    (sel=edge.establish edge nil)))


(defun sel=edge.introduce (object taf type new.object modifier)

  (let (edge entry)
    (setq edge (make-sel*edge :type type :status 'initial
			      :succ.object new.object
			      :modifier modifier
			      :taf taf))
    (cond ((setq entry (assoc taf (sel=object.succs object) :test 'equal))
	   (push edge (cddr entry))
	   (setf (second entry) 'output))
	  (t (push (list (sel=edge.taf edge) 'output edge) (sel=object.succs object))))
    edge))


(defun sel=edge.modification.append (edge modification)

  ;;; Input:   an edge and a list of modifications
  ;;; Effect:  appends the modifications at the end of the given modification
  ;;; Value:   t, iff an already solved edge have been changed.
  ;;; ok.

  (setf (sel=edge.modification edge)
	(append (sel=edge.modification edge) modification))
  (cond ((eq (sel=edge.status edge) 'finished)
	 (setf (sel=edge.status edge) 'open)
	 T)))


(defun sel=edge.finish? (edge)

  ;;; Input:   an edge
  ;;; Effect:  tests whether all subproblems of the edge are solved, computes the
  ;;;          final substitution and changes the status of the edge
  ;;; Value:   T, if edge is complete validated.

  (let (substs)
    (cond ((eq (sel=edge.type edge) 'subproblem)
	   (cond ((sel=refute (sel=edge.modifier edge))
		  (setf (sel=edge.input.subst edge) (car (sel=object.substs (sel=edge.modifier edge))))
		  (setf (sel=edge.status edge) 'finished)
		  t)))
	  ((and (every #'(lambda (mod)
			   (or (null (sel=mod.subproblem mod))
			       (eq (sel=mod.subproblem mod) t)
			       (sel=refute (sel=mod.subproblem mod))))
		       (sel=edge.modification edge))
		(setq substs (sel=edge.subst.compute (sel=edge.modification edge))))
	   (setf (sel=edge.input.subst edge) (car substs))
	   (setf (sel=edge.status edge) 'finished)
	   T))))


(defun sel=mod.subproblem (mod) (third (rl=mod.validation mod)))

(defun sel=mod.subst (mod) (second (rl=mod.validation mod)))


(defun sel=mod.modifier (mod) (car (rl=mod.validation mod)))



(defun sel=edge.subst.compute (modification)

  ;;; Input:   a modification
  ;;; Effect:  computes the total substitution of all< modification steps
  ;;; Value:   the computed substitution.

  (let ((new.subst (list nil)))
    (mapc #'(lambda (mod.step)
	      (setq new.subst (uni-subst.list.merge new.subst (list (sel=mod.subst mod.step))))
	      (cond ((and (sel=mod.subproblem mod.step) (typep (sel=mod.subproblem mod.step) 'sel*object))
		     (setq new.subst (uni-subst.list.merge new.subst
							   (sel=object.substs (sel=mod.subproblem mod.step)))))))
	  modification)
    new.subst))


(defun sel=edge.establish (edge modification)

  (setf (sel=edge.modification edge) modification)
  (sel=edge.finish? edge))


;;;;;==============================================================================================================
;;;;;
;;;;; Interaction function for Proof - trees:
;;;;;
;;;;;==============================================================================================================



;;;; modification on cases:
;;;; ----------------------


(defun sel=man.case.interaction.leaf (case)

  (case (car (WIN-MN.POPUP (win-window 'description_1)
			   '(("Introduce induction" . 1)
			     ("Insert case analysis" . 4)
			     ("Generalize theorem" . 2)
			     ("Prove case automatically" . 3))))
	(1 (sel=mod.case.induction case))
	(4 (sel=man.case.insert.case.analysis case))
	(2 (sel=mod.case.generalization case))
	(3 (win-io.print.status (win-window 'main) "Proving ...")
	   (sel=mod.case.prove case))
	(otherwise (win-io.print.status (win-window 'description_1) "Nothing done")
		   nil)))


(defun sel=man.case.interaction.node (case)

  (case (car (WIN-MN.POPUP (win-window 'description_1)
			   '(("Reset underlying case analysis" . 1)
			     ("Prove case automatically" . 2))))
	(1 (sel=mod.case.reset.case.analysis case))
	(2 (win-io.print.status (win-window 'main) "Proving ...")
	   (sel=mod.case.prove case))
	(otherwise (win-io.print.status (win-window 'description_1) "Nothing done")
		   nil)))


(defun sel=man.case.insert.case.analysis (case)
  (sel=man.insert.case.analysis case (sel=case.proof case) t))


(defun sel=man.insert.case.analysis (case object &optional flag)
  (let* ((gterm (sel=object.gterm object))
	 (constants (da-gterm.functions gterm 'skolem))
	 (sel*choice nil))
    (pr-graphic.interact (win-window 'description_3)
			 `(sel=pr.select.case.analysis (quote ,gterm) (quote ,constants)))
    (cond (sel*choice
	   (sel=case.insert.case.analysis case sel*choice flag))
	  (t (win-io.print.status (win-window 'description_1) "Specifying case analysis aborted"))))
  nil)


(defun sel=pr.select.case.analysis (gterm constants)
  (let ((generated.constants (remove-if-not #'(lambda (const)
						(da-sort.is.generated (da-symbol.sort const)))
					    constants)))
    (pr-parse.headline "Introducing case analysis"
		       (pr-parse.itemize
			(list (pr-parse.closure (pr-parse.gterm gterm nil)
						'boxed 2 "LightGrey" 3 :font 'bold :size 'D)
			      (pr-parse.string "")
			      (pr-parse.string "Possible Applications: " :font 'italic :size 'B)
			      (pr-parse.string "")
			      (pr-parse.itemize
			       (nconc (mapcar #'(lambda (const)
						  (sel=mod.case.structural.case.analysis const))
					      (remove-if-not #'(lambda (const)
								 (null (da-function.domain.sorts const)))
							     generated.constants))
				      (list (pr-parse.string
					     "other case analysis" :font 'bold
					     :right `(sel=mod.new.case.analysis (quote ,constants)))))
			       'itemize))
			nil :font 'roman 'size 'D))))


(defun sel=mod.case.structural.case.analysis (const)

  (let* ((term (da-term.create const))
	 (structure.terms (reverse (da-sort.create.all.structure.terms term nil))))
    (pr-parse.string (format nil "- structural case analysis on ~A" const) :font 'bold
		     :double.left `(sel=pr.case.analysis (quote ,const) (quote ,term) (quote ,structure.terms))
		     :right `(progn (setq sel*choice
					  (da-literal.create
					   (da-sign.plus) (da-predicate.equality)
					   (list (quote ,term) (first (quote ,structure.terms)))))
				    1))))


(defun sel=pr.case.analysis (const term structure.terms)
  (let* ((counter 0))
    (pr-parse.headline (format nil "Structural case analyis on ~A" const)
		       (pr-parse.closure
			(pr-parse.tree
			 nil
			 (mapcar #'(lambda (case)
				     (pr-parse.gterm
				      (da-literal.create (da-sign.plus) (da-predicate.equality)
							 (list term case))
				      60))
				 structure.terms)
			 (mapcar #'(lambda (case)
				     (declare (ignore case))
				     (pr-parse.closure (pr-parse.string (format nil "Case ~D" (incf counter)) :font 'bold)
						       'boxed 2 "White" 3))
				 structure.terms))
			'boxed 2 "LightGrey")
		       nil
		       :font 'roman :size 'B)))


(defun sel=mod.new.case.analysis (constants)
  (let (add.condition error finished question (text (list "")))
    (setq question (format nil "Enter literal for case analysis ( using ~{~A ~})" constants))
    (while (not finished)
      (cond ((setq text (win-text.input (win-window 'description_1) question (car text)))
	     (cond (text (multiple-value-setq (error add.condition)
			     (com-compile.case.analysis text constants))
			 (cond ((null error) (setq finished t))
			       (t (setq question
					(format nil "Erroneous literal, enter again: ~%~A  [~D]" (third error) (car error))))))))
	    (t (setq finished t add.condition nil))))
    (cond (add.condition (setq sel*choice add.condition) 1))))


(defun sel=mod.case.generalization (case)
  (let* ((object (sel=object.simplified.formula (sel=case.proof case)))
	 (gterm (sel=object.gterm.compute object))
	 (sel*choice nil))
    (pr-graphic.interact (win-window 'description_3)
			 `(sel=pr.select.generalizations.general (quote ,gterm) (quote ,object)))
    (cond (sel*choice
	   (sel=case.insert.generalization case sel*choice))
	  (t (win-io.print.status (win-window 'description_1) "Specifying generalization aborted")))))


(defun sel=pr.select.generalizations.general (gterm object)
  (pr-parse.headline "Introducing generalization"
		     (pr-parse.itemize
		      (list (pr-parse.closure (pr-parse.gterm gterm nil)
						'boxed 2 "LightGrey" 3 :font 'bold :size 'D)
			    (pr-parse.string "")
			    (pr-parse.string "Possible Applications: " :font 'italic :size 'B)
			    (pr-parse.string "")
			    (pr-parse.itemize
			     (list (pr-parse.string "system suggestions" :font 'bold
						    :right `(sel=pr.select.system.generalizations (quote ,gterm)))
				   (pr-parse.string "interactive generalization" :font 'bold
						    :right `(sel=mod.interactive.generalization 
							     (quote ,gterm) (quote ,object)))
				   (pr-parse.string "enter generalization" :font 'bold
						    :right `(sel=mod.enter.generalization (quote ,gterm))))
			     'itemize))
		      nil)
		     nil :font 'roman :size 'D))


(defun sel=mod.enter.generalization (gterm)
  (let* (formula
	 new.gterm
	 (used.names (append (mapcar #'(lambda (fct)
					 (string-left-trim '(#\_) (da-symbol.pname fct)))
				     (da-gterm.constants gterm 'skolem))
			     (mapcar #'da-symbol.pname (da-gterm.variables gterm))))
	 finished
	 (text (list "")) error
	 (question (format nil "Please enter a generalization ~%not using the variable(s): ~{~A ~}"
			   used.names)))
    (while (not finished)
      (cond ((setq text (win-text.input (win-window 'description_1) question (car text)))
	     (multiple-value-setq (error formula)
		  (com-compile.theorem text))
	     (cond ((null error)
		    (cond ((intersection used.names (mapcar #'da-symbol.pname (da-gterm.variables formula)) :test #'string-equal)
			   (setq question (format nil "Error: do not use variables out of (~{~A ~}).~%Enter generalization again." used.names)))
			  (t (setq finished t))))
		   (t (setq question (format nil "Error in specifying a formula, enter generalization again:~%~A [~D]~%"
					     (third error) (first error))))))
	    (t (setq finished t))))
    (cond (text
	   (setq new.gterm (norm-normalization (da-formula.negate (da-gterm.copy formula))))
	   (cond ((sel=mod.generalization.is.valid (da-gterm.copy formula) gterm)
		  (setq sel*choice (list new.gterm)))
		 (t (setq sel*choice (list new.gterm
					   (da-gterm.create 'and (list (norm-normalization formula) (da-gterm.copy gterm)))))))
	   1))))


(defun sel=mod.generalization.is.valid (formula gterm)
  (let ((new.gterm (norm-normalization (da-formula.negate (norm-normalization formula)))))
    (uni-gterm.match (da-formula.quantification.closure 'all (da-gterm.variables new.gterm) new.gterm) gterm)))


(defun sel=mod.interactive.generalization (gterm object)
  
  (pr-parse.headline "Interactive Generalization"
		     (cond ((and (da-literal.is gterm)
				 (or (da-literal.is.true gterm)
				     (da-literal.is.false gterm)))
			    (pr-parse.gterm gterm nil))
			   (t (pr-parse.itemize
			       (list (pr-parse.closure (pr-parse.string "Generalize !")
						       'boxed 2 "LightGrey" 3
						       :double.left `(sel=mod.gen.interactive
								      (quote ,object)
								      (quote ,gterm)
								      (pr-selected.items)))
				     (pr-parse.string "")
				     (pr-parse.gterm.as.tree gterm #'(lambda (s.gterm taf)
								       (declare (ignore s.gterm))
								       (list :selection taf))))
			       nil :font 'bold)))))


(defun sel=mod.gen.interactive (object gterm tafs)

  (let* (new.gterm)
    (cond ((null tafs) (win-io.print.status (win-window 'description_3) "Nothing done") nil)
	  ((some #'(lambda (taf1)
		     (some #'(lambda (taf2)
			       (da-taf.is.subtaf taf1 taf2))
			   (remove taf1 tafs)))
		 tafs)
	   (win-io.print.status (win-window 'description_3) "Generalization not uniquely specified")
	   nil)
	  (t (setq new.gterm (gen-generalize.tafs (da-gterm.copy gterm) tafs))
	     (setq sel*choice (list new.gterm))
	     (sel=mod.interactive.generalization new.gterm object)
	     2))))


(defun sel=pr.select.system.generalizations (gterm)
  (let (gterms (counter 0))
    (win-io.print.status (win-window 'description_3) "It may take a while ...")
    (setq gterms (gen-generalize.all.possibilities (da-gterm.copy gterm)))
    (prog1 (pr-parse.headline "Generalization System Suggestions"
			      (cond (gterms 
				     (pr-parse.itemize
				      (mapcar #'(lambda (new.gterm)
						  (sel=pr.present.system.generalization new.gterm (incf counter)))
					      gterms)
				      nil))
				    (t (pr-parse.string "No suggestions available" :font 'bold :size 'D))))
      (win-io.print.status (win-window 'description_3) ""))))


(defun sel=pr.present.system.generalization (gterm counter)
  
  (PR-PARSE.itemize
   (nconc (list (PR-PARSE.STRING "")
		(pr-parse.string (format nil "Suggestion ~D" counter) :font 'bold :style 'underline))
	  (MAPCAN #'(LAMBDA (STRING)
		      (MAPCAR #'(LAMBDA (STR)
				  (PR-PARSE.STRING STR :font 'FIXROMAN))
			      (sel=pr.present.single.system.generalization string)))
		  (pr-print.gterm gterm)))
   NIL 
   :size 'D :font 'roman
   :right `(progn (setq sel*choice (list (quote ,gterm))) 2)))



(DEFUN sel=pr.present.single.system.generalization (STRING &OPTIONAL (OFFSET 0) ADD.FLAG)

  (COND ((< (LENGTH STRING) (+ 120 OFFSET))
	 (LIST (COND (ADD.FLAG (FORMAT NIL "   ~A" (SUBSEQ STRING OFFSET)))
		     (T (SUBSEQ STRING OFFSET)))))
	(T (LET ((POS (COND ((POSITION #\SPACE STRING :START (+ 100 OFFSET) :END (+ 120 OFFSET)))
			    ((POSITION #\SPACE STRING :START (+ 80 OFFSET) :END (+ 100 OFFSET)))
			    (T (+ 120 OFFSET)))))
	     (CONS (COND (ADD.FLAG (FORMAT NIL  "   ~A" (SUBSEQ STRING OFFSET POS)))
			 (T (SUBSEQ STRING OFFSET POS)))
		   (sel=pr.present.single.system.generalization STRING POS T))))))


(defun sel=mod.case.prove (case)

  (let ((sel*active.proof t))
    (with-simple-restart (sel-top "Abort the automatic proof")
			 (catch 'sel*end.of.proof (sel=handle.cases case)))
    nil))


(defun sel=mod.case.reset.case.analysis (case)

  (setf (sel=case.sub.cases case) nil)
  (setf (sel=case.status case) 'initial)
  nil)


(defun sel=mod.case.induction (case)

  (let* ((object (sel=object.simplified.formula (sel=case.proof case)))
	 (gterm (sel=object.gterm.compute object))
	 (sel*choice nil))
    (pr-graphic.interact (win-window 'description_3)
			 `(sel=pr.select.induction.scheme (quote ,gterm) (quote ,case)))
    (cond (sel*choice
	   (sel=mod.apply.induction case sel*choice object gterm nil))   ;;; gterm.suggested missing!
	  (t (win-io.print.status (win-window 'description_1) "Specifying induction scheme aborted")))))


(defun sel=pr.select.induction.scheme (gterm case)

  (pr-parse.headline "Introducing induction"
		     (pr-parse.itemize
		      (list (pr-parse.closure (pr-parse.gterm gterm nil)
					      'boxed 2 "LightGrey" 3)
			    (pr-parse.string "")
			    (pr-parse.string "Possible Applications: " :font 'italic)
			    (pr-parse.string "")
			    (pr-parse.itemize (nconc (mapcar #'(lambda (wfo)
								 (sel=mod.case.induction.wfo wfo))
							     (IND-DETERMINE.SUGGESTED.WFOS GTERM nil (sel=case.condition case)))
						     (mapcar #'(lambda (wfo)
								 (sel=mod.case.induction.wfo wfo t))
							     (sel=mod.case.struc.inductions
							      (da-gterm.constants gterm 'skolem)))
						     (list (pr-parse.string "other scheme" 
									    :right `(sel=mod.new.induction 
										     (quote ,gterm)))))
					      'itemize))
		      nil :font 'bold :size 'D)))


(defun sel=mod.case.struc.inductions (constants)

  (let (tree)
    (mapcan #'(lambda (constant)
		(setq constant (da-term.create constant))
		(setq tree (DA-WFO.STRUCTURAL.TREE.CREATE constant))
		(cond ((and (da-wfo.tree.subnodes tree)
			    (some #'(lambda (fct)
				      (da-function.is.reflexive fct))
				  (da-sort.constructor.fcts (da-term.sort constant))))
		       (list (DA-WFO.CREATE (LIST constant) tree NIL (LIST constant))))))
	    constants)))


(defun sel=mod.new.induction (gterm)

  (let (wfo instance)
    (COND ((multiple-value-setq (wfo instance)
	       (sel=mod.enter.induction (da-gterm.constants gterm 'skolem)))
	   (setq sel*choice (IND-WFO.INSTANTIATE wfo instance))
	   1))))


(defun sel=mod.enter.induction (constants)

  (let (finished (text (list "")) error parameter ordering instance wfo symbol
		 (question "Please enter well-founded ordering:"))
    (while (not finished)
      (cond ((setq text (win-text.input (win-window 'description_1) question (car text)))
	     (multiple-value-setq (error parameter ordering instance symbol)
		  (com-compile.induction text constants))
	     (cond ((null error)
		    (cond ((setq ordering (exp-induction.analyze parameter ordering))
			   (cond ((setq wfo (car (rec-induction.analyze parameter ordering symbol)))
				  (cond ((ind-wfo.is.applicable wfo instance)
					 (setq finished t))
					(t (setq wfo nil)
					   (setq question (format nil "Erroneous scheme, enter ordering again:~%~A"
								  "Ordering is not applicable on specified terms")))))
				 (t (setq question (format nil "Erroneous scheme, enter ordering again:~%~A"
							   "Ordering seems to be not well-ordered")))))
			  (t (setq question (format nil "Erroneous scheme, enter ordering again:~%Invalid case analysis")))))
		   (t (setq question (format nil "Erroneous scheme, enter ordering again:~%~A  [~D]~%"
					     (third error) (first error))))))
	    (t (setq finished t parameter nil ordering nil instance nil))))
    (values wfo instance)))


(defun sel=mod.case.induction.wfo (wfo &optional flag)

  (pr-parse.string (cond (flag (format nil "structural induction on ~A" (car (da-wfo.parameters wfo))))
			 (t (format nil "on ~A suggested by ~{~A ~}"
				    (da-wfo.parameters wfo)
				    (getf (da-wfo.attributes wfo) 'gterms.suggested))))
		   :font 'bold :size 'D
		   :double.left `(sel=pr.induction.wfo (quote, wfo)) 
		   :right `(progn (setq sel*choice (quote ,wfo)) 1)))


(DEFUN sel=pr.induction.wfo (wfo)

  (PR-PARSE.HEADLINE
   (FORMAT NIL "Well-founded ordering on ~A suggested by ~{~A ~}"
	   (da-wfo.parameters wfo) (getf (da-wfo.attributes wfo) 'gterms.suggested))
   (pr-parse.closure (SEL=pr.wfo (DA-WFO.TREE wfo)) 'BOXED 2)))


(DEFUN SEL=pr.wfo (TREE)
  (COND ((DA-WFO.TREE.IS.LEAF TREE)
	 (COND ((DA-WFO.TREE.PRED.SET TREE)
		(pr-parse.closure
		 (PR-PARSE.ITEMIZE
		  (list (PR-PARSE.STRING "Induction Step(s)")
			(PR-PARSE.ITEMIZE
			 (MAPCAR #'(LAMBDA (SUBST)
				     (PR-PARSE.SUBST SUBST 20))
				 (DA-WFO.TREE.PRED.SET TREE))
			 'ITEMIZE :font 'roman))
		  nil)
		 'BOXED 2 "White" 3))
	       (T (PR-PARSE.CLOSURE (PR-PARSE.STRING "Base Case")
				    'BOXED 2 "White" 3))))
	(T (PR-PARSE.TREE NIL
			  (MAPCAR #'(LAMBDA (CASE)
				      (PR-PARSE.ITEMIZE (MAPCAR #'(LAMBDA (formula)
								    (PR-PARSE.gterm (da-formula.negate formula) 60))
								(CDR CASE))
							nil :font 'roman))
				  (DA-WFO.TREE.SUBNODES TREE))
			  (MAPCAR #'(LAMBDA (CASE)
				      (DED=PREFUN.DESCR.REC.SCHEME (CAR CASE)))
				  (DA-WFO.TREE.SUBNODES TREE))))))


(defun sel=mod.apply.induction (case wfo object gterm gterm.suggested)

  (sel=case.split.by.induction.2 case (ind-apply.wfo gterm wfo) object gterm gterm.suggested)
  0)



;;;; modification on objects:
;;;; ------------------------


(defun sel=man.object.interaction (object no)

   (case (car (WIN-MN.POPUP (win-window 'description_1)
			    (cond ((member (sel=object.status object) '(connected.first solved connected))
				   (list (cons "Introduce Proof Sketch" 1)
					 (cons "Introduce Modification edge" 2)
					 (cons "Automatic" 4)))
				  (t (list (cons "Introduce Proof Sketch" 1))))))
	 (1 (win-io.print.status (win-window 'main) "Proving ...")
	    (sel=man.object.select.lits object no))
	 (2 (sel=man.object.insert.mod.edge object))
	 (4 (win-io.print.status (win-window 'main) "Proving ...")
	    (sel=man.object.deduce object))
	 (otherwise nil)))


(defun sel=man.generalization (object)
  (let ((gterm (sel=object.gterm object))
	(sel*choice nil))
    (pr-graphic.interact (win-window 'description_3)
			 `(sel=pr.select.generalizations.general (quote ,gterm) (quote ,object)))
    (cond(sel*choice
	  (sel=case.insert.generalization sel*case.actual sel*choice))
	 (t (win-io.print.status (win-window 'description_1) "Specifying generalization aborted")))
    nil))

(defun sel=man.object.insert.mod.edge (object)

  (sel=object.undo.all.edges object nil)
  (sel=object.undo.edge object nil)  ;; undo all (!) edges
  (sel=edge.introduce object nil 'modification
		      (make-sel*object :gterm (da-literal.false) :type 'trivial :status 'sketch.prop
				       :substs (list nil) :prev.object object)
		      'modification)
  (setf (sel=object.status object) 'connected.prop)
  nil)


(defun sel=man.object.select.lits (object no)

  (cond ((not (member (sel=object.type object) '(resolution resolution.set)))
	 (sel=object.undo.edge object nil)))
  (values (sel=pr.object object no t) `(sel=pr.object (quote ,object) (quote ,no) t)))


(defun sel=man.object.insert.case.analysis (object)
  (sel=man.insert.case.analysis sel*case.actual object))


(defun sel=man.object.deduce (object)

  (let ((sel*active.proof t))
    (with-simple-restart (sel-top "Abort the automatic proof")
		       (catch 'sel*end.of.proof 
			 (cond ((member (sel=object.status object) '(connected connected.prop connected.first))
				(cond ((sel=object.is.correctly.marked (sel=object.gterm object) object)
				       (setf (sel=object.type object) 'resolution.decompose)
				       (sel=refute object))
				      (t (sel=object.undo.all.edges object nil)
					 (sel=refute object)))))))
    nil))



(defun sel=man.literals.selection (object taf.taf.edges)
  
  (mapc #'(lambda (taf.edges)
	    (cond ((and (second taf.edges)
			(not (some #'(lambda (taf.taf.edges) (equal taf.edges (cdr taf.taf.edges)))
				   taf.taf.edges)))
		   (sel=object.undo.edge object (car taf.edges))
		   (setf (second taf.edges) nil))))
	(sel=object.succs object))
  (mapc #'(lambda (taf.taf.edges)
	    (cond ((cdr taf.taf.edges)
		   (setf (second (cdr taf.taf.edges)) 'output))
		  (t (push (list (car taf.taf.edges) 'output nil)
			   (sel=object.succs object))
		     (cond ((member (sel=object.status object) '(connected connected.first connected.prop solved))
			    (setf (sel=object.status object) 'connected))
			   (t (setf (sel=object.status object) 'sketch))))))
	taf.taf.edges)
  1)


(defun sel=man.edge.literal.selection (object taf.edges)
  
  (let ((literal (da-access (car taf.edges) (sel=object.gterm object)))
	comp.lit (taf (car taf.edges)))
    
    (cond ((setq comp.lit (sel=pr.select.database.entry
			   literal
			   (list (da-sign.other.sign (da-literal.sign literal))
				 (cond ((eq (da-sign.other.sign (da-literal.sign literal)) '-) '--)
				       (t '++)))))
	   (sel=object.undo.edge object taf)
	   (sel=refute.single.literal object comp.lit taf)
	   nil))))


(defun sel=mod.undo (object taf.edges length)
  
  (let ((gterm (sel=object.gterm object))
	(modification (cond ((third taf.edges) (sel=edge.modification (third taf.edges))))))
    (cond ((eq 1 (car (win-mn.popup (win-window 'description_1)
				    '(("Undo following steps" . 1)))))  
	   (setq gterm (sel=object.change.edge.modification gterm (lastn modification length) T))
	   (setf (sel=object.gterm object) gterm)
	   (setf (sel=edge.modification (third taf.edges))
		 (butlast modification length))
	   (sel=object.invalid.verification object)
	   (setf (sel=edge.status (third taf.edges)) 'open)))
    nil))



;;;; modifications on mods:
;;;; ----------------------


(defun sel=mod.gterm (object taf.edges)
  
  (let ((gterm (da-access (car taf.edges) (sel=object.gterm object))))
    (pr-parse.headline "Manipulating the formula"
		       (pr-parse.gterm.as.tree 
			gterm
			#'(lambda (gterm taf)
			    (declare (ignore gterm))
			    (list :right `(sel=mod.gterm.interactive (quote ,object)
								     (quote ,taf.edges)
								     (quote ,taf))))))))



(defun sel=mod.both.gterms (object1 taf.edges1 object2 taf.edges2)
  
  (let ((gterm1 (da-access (car taf.edges1) (sel=object.gterm object1)))
	(gterm2 (da-access (car taf.edges2) (sel=object.gterm object2))))
    (pr-parse.headline 
     "Manipulating both literals:"
     (pr-parse.table (list (pr-parse.gterm.as.tree
			    gterm1 #'(lambda (gterm taf)
				       (declare (ignore gterm))
				       (list :right `(sel=mod.gterm.interactive (quote ,object1)
								     (quote ,taf.edges1)
								     (quote ,taf)))))
			   (pr-parse.string "  by  ")
			   (pr-parse.gterm.as.tree
			    gterm2 #'(lambda (gterm taf)
				       (declare (ignore gterm))
				       (list :right `(sel=mod.gterm.interactive (quote ,object2)
								     (quote ,taf.edges2)
								     (quote ,taf))))))
		     3 :font 'bold :size 'D))))


(defun sel=mod.gterm.interactive (object taf.edges taf)
  
  (let (type selection)
    (cond ((third taf.edges)
	   (setq type (da-access taf (da-access (car taf.edges) (sel=object.gterm object))))
	   (setq selection (car (WIN-MN.POPUP (win-window 'description_1)
					      (append '(("Apply lemma " . 1)
							("Apply lemma (without establishing conditions)" . 2)
							("Enable application of lemma" . 4)
							("Symbolic evaluation" . 3)
							("Activate lemma" . 6)
							("Instantiation" . 8)
							("Case Analysis" . 9)
							("Generalization" . 10))
						      (cond ((not (da-term.is type))
							     '(("Cut" . 11))))))))
	   (cond ((member selection '(1 2 4 3 11 6 8))
		  (sel=mod.gterm.interactive.subterm object taf.edges taf selection))
		 ((eq selection 9) (sel=man.insert.case.analysis sel*case.actual object))
		 ((eq selection 10) (sel=man.generalization object))
		 (t (win-io.print.status (win-window 'description_1) "Nothing done")))
	   (setf (getf (getf (sel=object.attributes object) 'actual.mods) (car taf.edges)) nil)))	  
    nil))


(defun sel=mod.gterm.interactive.subterm (object taf.edges taf selection)

  (let (sol)
    (DB-WITH.GTERMS.INSERTED
     (sel=object.conjunctive.parts object (append taf (car taf.edges)))
     'theorem nil
     (rl-with.problem object 'object
		      #'(lambda (occ)
			  (setq sol (rl-with.sub.problem
				     occ (car taf.edges)
				     #'(lambda (sub.occ)
					 (case selection
					       (1  (sel=man.change.gterm.by.modifier sub.occ taf nil nil))
					       (2  (sel=man.change.gterm.by.modifier sub.occ taf nil t))
					       (4  (sel=man.change.gterm.by.modifier sub.occ taf t nil))
					       (3  (sel=mod.symbolic.evaluation.1 sub.occ taf))
					       (11 (rl-object.change sub.occ (da-gterm.copy (da-literal.true)) taf "Cut"))
					       (6  (sel=mod.activate.lemma sub.occ))
					       (8  (sel=mod.instantiation sub.occ))))))))
     (cond (sol (cond ((sel=edge.modification.append (third taf.edges) sol)
		       (sel=object.invalid.verification object))))
	   (t (win-io.print.status (win-window 'description_1) "No modifications done"))))))


(defun sel=mod.instantiation (occ)

  (let* ((gterm (rl-object occ))
	 (constants (da-gterm.functions gterm 'skolem))
	 (variables (set-difference (da-gterm.variables gterm) sel*variables))
	 subst error finished question (text (list "")))
    (setq question (format nil "Enter instantiation for the variable(s) ~{~A ~}" variables))
    (while (not finished)
      (cond ((setq text (win-text.input (win-window 'description_1) question (car text)))
	     (cond (text (multiple-value-setq (error subst)
					      (com-compile.instantiation text constants variables))
			 (cond ((null error) (setq finished t))
			       (t (setq question
					(format nil "Wrong instantiation, enter again: ~%~A  [~D]"
						(third error) (car error))))))))
	    (t (setq finished t subst nil))))
    (cond (subst
	   (rl-object.change occ
			     (da-gterm.create 'and (list (uni-subst.apply (uni-create.var.renaming variables)
									  (uni-subst.apply subst gterm))
							 (da-gterm.copy gterm)))
			     nil "Manual Instantiation")))))


(defun sel=mod.activate.lemma (occ)

  (let ((gterm (sel=mod.activate.selection occ)))
    (cond (gterm (rl-object.change occ (da-gterm.create 'and (list (da-gterm.copy (rl-object occ)) gterm))
				   nil "Activate Lemma")))))



(defun sel=mod.activate.selection (occ)

  (case (car (WIN-MN.POPUP (win-window 'description_1)
			   '(("Use function as key" . 1)
			     ("Use predicate as key" . 2)
			     ("Conditions of theorem" . 3)
			     ("Theorem" . 4))))
	(1 (sel=mod.activate.by.function))
	(2 (sel=mod.activate.by.predicate))
	(3 (sel=mod.activate.condition))
	(4 (uni-subst.apply (uni-create.var.renaming
			     (set-difference (da-gterm.variables (rl-object occ))
					     sel*variables))
			    (rl-object occ)))))


(defun sel=mod.activate.condition ()

  (let ((sel*choice nil))
    (pr-graphic.interact (win-window 'description_3) `(sel=pr.select.condition))
    (cond (sel*choice (da-gterm.copy sel*choice)))))


(defun sel=pr.select.condition ()
  (let (items (counter 0))
    (setq items (mapcar #'(lambda (item)
			    (pr-parse.string (format nil "Condition ~D" (incf counter)) 
					     :font 'bold :size 'B
					     :double.left `(pr-parse.headline
							    (format nil "Condition ~D:" (quote ,counter))
							    (pr-parse.gterm (quote ,item) nil))
					     :right `(progn (setq sel*choice (quote ,item)) 1)))
			(db-theorems)))
    (pr-parse.headline "Please choose an item"
		       (cond (items (pr-parse.table items 3))
			     (t (pr-parse.string "No possible choices" :font 'bold :size 'B))))))




(defun sel=mod.symbolic.evaluation.1 (occ taf)
  
  (rl-with.sub.objects occ taf
		       #'(lambda (sub.occ)
			   (sel=simpl.and.eval.gterm sub.occ))))


(defun sel=man.change.gterm.by.modifier (occ taf bridge.lemma? refute.condition?)
  
  (let ((symbol (da-gterm.symbol (da-access taf (rl-object occ)))) equation)
    (cond ((setq equation (cond ((da-function.is symbol)
				 (sel=pr.select.modifier (da-access taf (rl-object occ)) 
							 '(top.level changing variable)
							 bridge.lemma?))
				((da-predicate.is symbol)
				 (sel=pr.select.database.entry (da-access taf (rl-object occ))
							       (cond ((da-sign.is.positive 
								       (da-literal.sign 
									(da-access taf (rl-object occ))))
								      '(- --))
								     (t '(+ ++)))
							       bridge.lemma?))))
	   (cond ((and (da-function.is symbol) bridge.lemma?)
		  (rl-with.sub.objects occ taf #'(lambda (sub.occ) (sel=modifier.try.to.apply equation sub.occ))))
		 ((UNI-WITHOUT.THEORY (cond ((da-function.is symbol)
					     (sel=modifier.test.and.apply equation occ taf nil 
									  :ignore.conds refute.condition?)))))
		 ((da-function.is symbol) (sel=modifier.test.and.apply equation occ taf nil
								       :ignore.conds refute.condition?))
		 ((da-predicate.is symbol) (rl-with.sub.objects occ taf
						    #'(lambda (sub.occ) (sel=resolution.apply equation sub.occ)))))))))


(defun sel=object.is.correctly.marked (gterm object &optional taf)
  
  (cond ((second (assoc taf (sel=object.succs object) :test 'equal)))
	((eq (da-gterm.symbol gterm) 'and)
	 (setq taf (da-taf.create.zero taf))
	 (some #'(lambda (subgterm)
		   (setq taf (da-taf.create.next taf))
		   (sel=object.is.correctly.marked subgterm object taf))
	       (da-gterm.termlist gterm)))
	((eq (da-gterm.symbol gterm) 'or)
	 (setq taf (da-taf.create.zero taf))
	 (every #'(lambda (subgterm)
		    (setq taf (da-taf.create.next taf))
		    (sel=object.is.correctly.marked subgterm object taf))
		(da-gterm.termlist gterm)))
	(t (second (assoc taf (sel=object.succs object) :test 'equal)))))



(defun sel=man.modification.selection (object taf.edges modification)
  
  (sel=object.change.edge.modification (sel=object.gterm object) modification T)
  (let ((edge (third taf.edges)))
    (setf (sel=edge.modification edge) (butlast (sel=edge.modification edge) (length modification)))
    (push 'started (sel=edge.status edge))))



;;;;;==============================================================================================================
;;;;;
;;;;; Print function for Proof - trees:
;;;;;
;;;;;==============================================================================================================


;;;;;-------------------------------------------------------------------------------------------------------------------
;;;;;
;;;;;   Section ? :    Printing parts of the proof tree
;;;;;                  Part I:  Line-Printer representation
;;;;;
;;;;;--------------------------------------------------------------------------------------------------------------------


(DEFUN SEL=CASE.PRINT (CASE STREAM DEPTH)
  
  (declare (ignore depth))
  (win-io.format STREAM "(with ~A: ~A)" (sel=case.condition case) (sel=CASE.PROOF CASE)))


(DEFUN SEL=OBJECT.PRINT (OBJECT STREAM DEPTH)
  
  (declare (ignore depth))
  (win-io.format STREAM "(~D)" (sel=OBJECT.gterm OBJECT)))


(defun sel=edge.print (edge stream depth)
  
  (declare (ignore depth))
  (cond ((sel=edge.succ.object edge)
	 (cond ((neq (sel=edge.type edge) 'factor)
		(win-io.format stream "(-~A->) ~A" (sel=edge.modifier edge) (sel=edge.succ.object edge)))
	       (t (win-io.princ "Factor" stream))))
	(t (win-io.format stream "(-~A->) ?" (sel=edge.type edge)))))




;;;;;-------------------------------------------------------------------------------------------------------------------
;;;;;
;;;;;   Section ? :    Printing parts of the proof tree
;;;;;                  Part II:  graphic representation
;;;;;
;;;;;--------------------------------------------------------------------------------------------------------------------


(defun sel=pr.case (case header)
  (pr-parse.headline header (pr-parse.closure (sel=pr.case.structure case header)
					      'boxed 3 "LightGrey" 3 :distance 20
					      :right `(sel=man.prs (quote ,case)))))


(defun sel=pr.case.structure (case header &optional (depth 0))

    (cond ((or (null (sel=case.sub.cases case)) (> depth 2))
	   (sel=pr.case.information case
				    (cond ((null (sel=case.sub.cases case))
					   `(sel=pr.proof.tree (quote ,(sel=case.proof case)) (quote ,header)))
					  (t `(sel=pr.case.structure (quote ,case) (quote ,header) 0)))
				    `(sel=man.case.interaction.leaf (quote ,case))
				    `(sel=with.active.case (quote ,case) (pr-apply))))
	  (t (pr-parse.tree
	      (pr-parse.closure (pr-parse.string (sel=case.name case) :font 'roman :size 'D)
				'boxed 
				(cond ((sel=case.is.proved case) 3) (t 1))
				(cond ((sel=case.is.proved case) "LightBlue") (t "LightRed"))
				0
				:double.left `(sel=pr.proof.tree (quote ,(sel=case.proof case)) (quote ,header))
				:right `(sel=man.case.interaction.node (quote ,case))
				:environment `(sel=with.active.case (quote ,case) (pr-apply)))
	      (make-list (length (sel=case.sub.cases case)))
	      (mapcar #'(lambda (subcase)
			  (sel=pr.case.structure subcase header (1+ depth)))
		      (sel=case.sub.cases case))))))


(defun sel=pr.case.information (case double.left right envir)

  (pr-parse.closure
   (pr-parse.itemize (cons (pr-parse.string (sel=case.name case) :font 'bold :size 'D)
			   (mapcar #'(lambda (cond)
				       (pr-parse.gterm cond 60 nil :font 'italic :size 'D))
				   (sel=case.condition case)))
		     nil)
   'boxed 
   (cond ((sel=case.is.proved case) 3) (t 1))
   (cond ((sel=case.is.proved case) "LightBlue") (t "LightRed"))
   0
   :double.left double.left :right right :environment envir))

  
(defun sel=pr.proof.tree (object header &optional (no 0))
  (cond ((null object)
	 (pr-parse.headline header
			    (pr-parse.closure (pr-parse.string "no modifications have been done !" 
							       :font 'bold :size 'D)
					      'boxed 2)))
	(t  (pr-parse.headline header (sel=pr.proof object header no)))))


(defun sel=pr.proof (object heading &optional (no 0))
  
  ;;; note:  man.interact nur bei Kanten, die angebunden sind d.h. connected, connected.first, 
  ;;;        solved oder connected.prop
  
  (let ((edges (sel=object.succs object)) tree header other.object edge)
    (setq header (pr-parse.closure (pr-parse.string (format nil "~d" (incf no)) :font 'bold :size 'D)
				   'circle
				   (case (sel=object.status object)
					 ((sketch sketch.first sketch.prop connected connected.prop connected.first)  1)
					 (solved 3))
				   (case (sel=object.status object)
					 ((sketch sketch.first sketch.prop connected connected.prop connected.first) 
					  "LightRed")
					 (solved "LightBlue"))
				   0
				   :double.left `(sel=pr.object ,object (quote ,no))
				   :right `(sel=man.object.interaction (quote ,object) (quote ,no))))
    (setq tree (cond ((every #'(lambda (taf.edges)
				 (not (eq (second taf.edges) 'output)))
			     edges)
		      header)
		     (t (pr-parse.tree
			 header
			 (mapcan 
			  #'(lambda (taf.edges)
			      (cond ((eq  (second taf.edges) 'output)
				     (cond ((setq edge (third taf.edges))
					    (cond ((eq 'subproblem (sel=edge.type edge))
						   (list (pr-parse.string 
							  "manipulate conclusion" :font 'italic :size 'D
							  :colour (cond ((eq (sel=edge.status edge) 'finished)
									 "DarkBlue")
									(t "DarkRed"))
							  :double.left 
							  `(sel=pr.subproblem (quote ,(third taf.edges)))
							  :environment 
							  (sel=pr.object.environment object taf.edges))))
						  (t (list (pr-parse.string 
							    (cond ((eq 'paramodulation (sel=edge.type edge))
								   "equations")
								  ((eq 'induction (sel=object.type object))
								   "Induction hypotheses")
								  ((da-gterm.is (sel=edge.modifier edge))
								   (cond ((sel=edge.succ.object edge)
									  (COND ((da-gterm.pname
										  (sel=object.gterm
										   (sel=edge.succ.object edge))))
										(t "Theorem")))
									 (t "???")))
								  ((typep (sel=edge.modifier edge) 'da*modifier)
								   (da-modifier.pname (sel=edge.modifier edge)))
								  ((eq 'factor (sel=edge.type edge))
								   "factorizes")
								  ((eq (sel=edge.type edge) 'resolution)
								   "adapting lits")
								  ((eq (sel=edge.type edge) 'modification)
								   "manipulates"))
							    :font 'italic :size 'D
							    :colour (cond ((eq (sel=edge.status edge) 'finished)
									   "DarkBlue")
									  (t "DarkRed"))
							    :double.left `(sel=pr.edge (quote ,object) (quote ,taf.edges)))))))
					   (t (list (pr-parse.string "?" :font 'roman :size 'D
								     :double.left `(sel=pr.edge (quote ,object) 
												(quote ,taf.edges)))))))))
			  edges)
		       (mapcan #'(lambda (taf.edges)
				   (cond ((eq (second taf.edges) 'output)
					  (list (cond ((setq edge (third taf.edges))
						       (multiple-value-setq (other.object no)
							   (sel=pr.proof (sel=edge.succ.object edge) heading no))
						       other.object)
						      (t (pr-parse.closure (PR-PARSE.STRING "?" :font 'roman :size 'D)
									   'circle 1 "LightRed")))))))
			       edges)))))
    (values tree no)))

(defun sel=pr.object.environment (object taf.edges)

  `(multiple-value-bind (new.cl vars preds)
      (sel=refutation.environment (quote ,object) (quote ,taf.edges))
    (db-with.gterms.inserted
     new.cl 'theorem nil
     (let ((sel*variables (union vars sel*variables))
	   (sel*pred.symbols (union preds sel*pred.symbols)))
       (pr-apply)))))


(defun sel=pr.subproblem (edge)
  
  (sel=pr.proof.tree (sel=edge.modifier edge) "Refuting a subformula:"))


(defun sel=pr.edge (object taf.edges)
  
  (let ((edge (third taf.edges)) width height)
    (multiple-value-setq (width height) (win-io.size (win-window 'description_1)))
    (setq width (max width 400) height (max height 300))
    (cond ((or (null edge)
	       (eq 'resolution (sel=edge.type edge)))
	   (pr-parse.headline "Adapting literals"
			      (sel=pr.edge.res object taf.edges width height)))
	  ((eq 'paramodulation (sel=edge.type edge))
	   (pr-parse.headline "Equalizing terms" 
			      (sel=pr.edge.general.new object taf.edges sel*actual.colour width height)))
	  ((eq 'induction (sel=object.type object))
	   (pr-parse.headline "Enabling the induction hypotheses"
			      (sel=pr.edge.general.new object taf.edges 'induction width height)))
	  ((eq 'factor (sel=edge.type edge))
	   (pr-parse.headline "Factorizing literals" 
			      (sel=pr.edge.general.new object taf.edges nil width height)))
	  (t (pr-parse.headline "Modifying formula"
				(sel=pr.edge.general.new object taf.edges sel*actual.colour width height))))))


(defun sel=pr.edge.res (object taf.edges width height)
  
  (let* ((other.object (cond ((third taf.edges) (sel=edge.succ.object (third taf.edges)))))
	 (other.taf.edges (cond ((third taf.edges) (list (sel=edge.taf (sel=object.edge other.object))
							 'output (sel=object.edge other.object))))))
    ;;; (setq width (floor (/ width 2)))
    (pr-parse.table (list (sel=pr.edge.general.new object taf.edges sel*actual.colour (floor (/ width 2)) height)
			  (pr-parse.string "by" :font 'roman :size 'D)
			  (cond (other.object
				 (sel=pr.edge.general.new
				  other.object other.taf.edges sel*actual.colour (floor (/ width 2)) height))
				(t (pr-parse.closure (pr-parse.string " ? " :font 'bold :size 'D)
						     'boxed 3 "" 0
						     :right `(sel=man.edge.literal.selection
							      (quote ,object) (quote ,taf.edges))))))
		    3)))


(defun sel=pr.edge.general.new (object taf.edges &optional colour width height)
  
  (let* ((mod (sel=edge.modification (third taf.edges)))
	 (no (cond ((getf (getf (sel=object.attributes object) 'actual.mods) (car taf.edges)))
		   (t (length mod))))
	 (plan (getf (getf (sel=object.attributes object) 'actual.plan) (car taf.edges)))
	 (formula (sel=object.reverse.modifications (da-access (car taf.edges) (sel=object.gterm object))
						    (cond ((and (eq (second taf.edges) 'output)
								(third taf.edges)
								(nthcdr no mod))))
						    t nil)))
    (setq colour (cond (plan (third plan))))
    (pr-parse.itemize
     (list (pr-parse.string "")
	   (pr-parse.closure
	    (pr-parse.center
	     (cond ((getf (sel=object.attributes object) 'actual.representation)
		    (pr-parse.gterm.as.tree 
		     formula 
		     #'(lambda (gterm taf)
			 (append (cond ((eql no (length (sel=edge.modification (third taf.edges))))
					(list :right `(sel=mod.gterm.interactive (quote ,object)
										 (quote ,taf.edges)
										 (quote ,taf)))))
				 (cond (colour (sel=pr.colour.of.term gterm taf colour (second plan))))))))
		   (t (pr-parse.gterm 
		       formula (cons 'width (- width 120))
		       #'(lambda (gterm taf)
			   (append (cond ((eql no (length (sel=edge.modification (third taf.edges))))
					  (list :right `(sel=mod.gterm.interactive (quote ,object)
										   (quote ,taf.edges)
										   (quote ,taf)))))
				   (cond (colour (sel=pr.colour.of.term gterm taf colour (second plan)))))))))
	     (- width 80) (floor (/ height 3)))
	    'boxed 1 "LightGrey" 3
	    :environment (sel=pr.object.environment object taf.edges) :size 'D :font 'bold)
	   (pr-parse.string "")
	   (pr-parse.table
	    (list (sel=pr.changes object taf.edges
			     (cond ((< no (length mod)) 
				    (rl=mod.plans (nth no (sel=edge.modification (third taf.edges))))))
			     plan 160 (floor  (/ height 3)))
		  (sel=pr.modification.new object taf.edges (sel=edge.modification (third taf.edges)) no 
					   (floor (- width 260)) plan))
	    2))
     nil)))


(defun sel=pr.changes (object taf.edges plan actual.mod width height)
  
  (pr-parse.closure 
   (pr-parse.center
    (pr-parse.itemize (cons (pr-parse.string "Stack of methods:" :font 'bold :size 'D
					     :right `(sel=man.change.representation (quote ,object)))
			    (mapcar #'(lambda (mod)
					(let ((args (format nil "~A" (cond ((fourth mod) (car (fourth mod)))
									   (T "")))))
					  (cond ((> (length args) 25) 
						 (setq args (format nil "~A..." (subseq args 0 25)))))
					  (pr-parse.string (format nil "~A ~A" (car mod) args)
							   :colour (cond ((equal mod actual.mod) "DarkRed")
									 (t "Black"))
							   :size 'D
							   :double.left `(sel=man.plan.entry (quote ,object)
											     (quote ,taf.edges)
											     (quote ,mod)))))
				    plan))
		      nil)
    width height)
   'boxed 1 "LightGrey" 3))


(defun sel=pr.modification.new (object taf.edges modification actual.no width &optional actual.plan)
  
  (let (tree modifier (no -1))
    (setq tree (nconc (mapcan #'(lambda (mod.tail)
				  (incf no)
				  (setq modifier (sel=mod.modifier mod.tail))
				  (cond ((not (member modifier '("Instantiation" "No operation" "Recoloring terms")
						      :test 'equal))
					 (list (sel=pr.sequel.buttom object taf.edges no actual.no
								     (- (length modification) no)
								     (member actual.plan (rl=mod.plans mod.tail)
									     :test 'equal))
					       (sel=pr.sequel.edge mod.tail)))))
			      modification)
		      (list (sel=pr.sequel.buttom object taf.edges (length modification) actual.no 0
						  (and modification
						       (member actual.plan (rl=mod.plans (car (last modification)))
							       :test 'equal))))))
    (pr-parse.sequel tree width)))


(defun sel=pr.sequel.buttom (object taf.edges no actual.no further.nodes highlighted)

  (pr-parse.closure 
   (pr-parse.string (format nil "~d" (1+ no)) 
		    :font 'bold :size 'S :colour (cond ((neq actual.no no) "Black") (t "White")))
   'circle 1 (cond ((eq actual.no no) "DarkRed") (highlighted "LightRed") (t "LightBlue"))  0
   :double.left `(sel=man.modification.entry (quote ,object) (quote ,taf.edges) (quote ,no) (quote ,highlighted))
   :right `(sel=mod.undo (quote ,object) (quote ,taf.edges) (quote ,further.nodes))
   ))


(defun sel=pr.sequel.edge (modification)

  (let ((modifier (sel=mod.modifier modification)))
    (pr-parse.string 
     (cond ((da-gterm.is modifier)
	    (da-gterm.pname
	     (cond ((getf (da-gterm.attributes modifier) 'TOP.LEVEL.GTERM))
		 (t modifier))))
	   ((typep modifier 'da*modifier)
	  (da-modifier.pname modifier))
	   ((stringp modifier) modifier)
	   (t  ""))
     :font 'italic :size 'S
     :double.left `(sel=pr.mod (quote ,modification) "Displaying modifier"))))


(defun sel=man.modification.entry (object taf.edges no highlighted)

  (setf (getf (getf (sel=object.attributes object) 'actual.mods) (car taf.edges)) no)
  (cond ((not highlighted)
	 (setf (getf (getf (sel=object.attributes object) 'actual.plan) (car taf.edges)) nil)))
  nil)


(defun sel=man.plan.entry (object taf.edges plan)

  (setf (getf (getf (sel=object.attributes object) 'actual.plan) (car taf.edges)) plan)
  nil)


(defun sel=man.change.representation (object)
  
  (let (result)
    (cond ((setq result (win-mn.popup (win-window 'description_1)
				      '(("Pretty Print " . nil)
					("Tree Representation" . T))))
	   (setf (getf (sel=object.attributes object) 'actual.representation) (car result))))
    nil))


(defun sel=pr.colour.of.term (gterm taf colour.key tafs)

  (let ((colour (da-gterm.colour gterm colour.key))
	(inside (or (null tafs) (some #'(lambda (other.taf) (da-taf.is.subtaf other.taf taf)) tafs))))
    (list :colour (cond ((null colour) "Black")
			((da-colour.is.fade colour)
			 (cond (inside "DarkRed") (t "Black")))
			((eq colour 'sink) "DarkGreen")
			((eq colour 'selected.to.blow.up) "DarkPink")
			((eq colour 'blow.up) "DarkPink")
			(inside "DarkBlue")
			(t "Black")))))


(defun sel=pr.mod (mod heading)

  (pr-parse.headline
   heading
   (pr-parse.itemize
    (nconc (list (pr-parse.string "Using: " :font 'bold)
		 (pr-parse.string "")
		 (pr-parse.closure
		  (pr-parse.itemize
		   (mapcar #'(lambda (string)
			       (pr-parse.string string))
			   (cond ((da-gterm.is (sel=mod.modifier mod))
				  (pr-print.gterm
				   (cond ((getf (da-gterm.attributes (sel=mod.modifier mod))
						'TOP.LEVEL.GTERM))
					 (t (sel=mod.modifier mod)))))
				 ((typep  (sel=mod.modifier mod) 'da*modifier)
				  (pr-print.modifier (sel=mod.modifier mod)))
				 ((stringp (sel=mod.modifier mod)) (list (sel=mod.modifier mod)))
				 (t (list "?"))))
		   nil)
		  'boxed 3))
	   (cond ((sel=mod.subproblem mod)
		  (list (pr-parse.string "")
			(pr-parse.string "with proving side conditions" :font 'bold
					 :double.left `(sel=pr.proof.tree (quote ,(sel=mod.subproblem mod))
									  "Verifying Side Conditions"))))))
    nil :font 'roman :size 'D)))


(defun sel=pr.object (object no &optional selection)
  (let ((gterm (sel=object.gterm.compute object)))
    (pr-parse.headline (format nil "Formula No. ~D" no)
		       (pr-parse.itemize 
			(nconc (cond (selection
				      (list (pr-parse.closure (pr-parse.string "Save Settings")
							      'boxed 2 "LightGrey" 3
							      :double.left `(sel=man.literals.selection
									     (quote ,object) 
									     (pr-selected.items))))))
			       (list (pr-parse.closure 
				      (cond ((sel=pr.object.gterm gterm object nil nil))
					    (t (pr-parse.string "False")))
				      'boxed 1 "LightGrey" 0)))
			nil
			:font 'bold :size 'D))))



(defun sel=pr.object.gterm (gterm object &optional taf selection?)
  (let (new.taf)
    (cond ((da-literal.is gterm)
	   (cond ((not (da-literal.is.false gterm))
		  (let* ((taf.edges (assoc taf (sel=object.succs object) :test 'equal)))
		    (cond (selection? (pr-parse.gterm gterm nil nil
						      :selection (cons taf taf.edges)
						      :selected (eq 'output (second taf.edges))))
			  (t (pr-parse.gterm gterm nil nil)))))))
	  ((and (sel=object.edge object)
		(da-taf.is.subtaf taf (sel=edge.taf (sel=object.edge object)))
		(eq (da-gterm.symbol gterm) 'and))
	   (setq new.taf (lastn (sel=edge.taf (sel=object.edge object)) (1+ (length taf))))
	   (sel=pr.object.gterm (nth (1- (car new.taf)) (da-gterm.termlist gterm)) object new.taf selection?))
	  (t (setq taf (da-taf.create.zero taf))
	     (let ((parsed.termlist (mapcar #'(lambda (subterm)
						(setq taf (da-taf.create.next taf))
						(sel=pr.object.gterm subterm object taf selection?))
					    (da-gterm.termlist gterm))))
	       (cond ((and (eq 'and (da-gterm.symbol gterm))
			   (member nil parsed.termlist))
		      nil)
		     (t (setq parsed.termlist (delete nil parsed.termlist))
			(cond ((null (cdr parsed.termlist)) (car parsed.termlist))
			      (t (pr-parse.tree (pr-parse.string (pr-junctor.char (da-gterm.symbol gterm))
								 :font 'symbol)
						(make-list (length parsed.termlist))
						parsed.termlist))))))))))



;;;;;-------------------------------------------------------------------------------------------------------------------
;;;;;
;;;;;   Chapter ? :    Introducting case-analysis and copying of objects
;;;;;
;;;;;--------------------------------------------------------------------------------------------------------------------



(defrule sel=case.split.by.induction (&others case)
  
  (EQ 0 ("trying induction"))
  
  (let* ((object (sel=object.simplified.formula (sel=case.proof case)))
	 (formula (sel=object.gterm.compute object))
	 case.analysis suggested.gterms)
    (cond ((multiple-value-setq (case.analysis suggested.gterms) 
	     (ind-induction formula (getf (sel=case.information case) :gterms.suggested)
			    (sel=case.condition case)))
	   (sel=case.split.by.induction.2 case case.analysis object formula suggested.gterms)))))


(defun sel=case.split.by.induction.2 (case case.analysis object formula suggested.gterms)
  
  (let (condition)
    (setf (sel=case.sub.cases case)
	  (reverse
	   (mapcar #'(lambda (cond.hypotheses)
		       (setq formula (da-gterm.copy formula))
		       (setq condition (append (car cond.hypotheses) (sel=case.condition case)))
		       (make-sel*case :type (cond ((null (second cond.hypotheses)) 'base.case)
						  (t 'induction.step))
				      :proof (make-sel*object
					      :gterm formula
					      :substs (list nil)
					      :type (cond ((second cond.hypotheses) 'induction)
							  (t 'simplification))
					      :status 'connected
					      :hints (cond ((second cond.hypotheses))))
				      :information (list :gterms.suggested (append suggested.gterms
										   (getf (sel=case.information case) :gterms.suggested)))
				      :instances (fourth cond.hypotheses)
				      :condition (mapcar #'da-gterm.copy condition)
				      :name (cond ((second cond.hypotheses) "Induction Step")
						  (t "Base Case"))
				      :prev.case case
				      :status 'initial))
		   case.analysis)))
    (sel=object.undo.all.edges object nil)
    (sel=object.undo.edge object nil) 
    (setf (sel=case.status case) 'finished)))


(defun sel=object.simplified.formula (object &optional edge)
  
  (let (taf.edges)
    (cond ((member (sel=object.type object) '(simplification simplification.cases modification))
	   (setq taf.edges (assoc nil (sel=object.succs object)))
	   (cond ((and (eq (second taf.edges) 'output)
		       (third taf.edges)
		       (eq 'finished (sel=edge.status (third taf.edges))))
		  (sel=object.simplified.formula (sel=edge.succ.object (third taf.edges)) (third taf.edges)))
		 (t (values object edge))))
	  (t (values object edge)))))



(defun sel=case.introduce.case.analysis (object taf modifications add.condition)
  
  ;;;

  (let (cases (first t) (status (sel=object.status object))
	      (old.condition (second (car (rl=mod.inverse.mod (car (last add.condition))))))
	      (type (sel=object.type object)) (succs (sel=object.succs object))
	      (counter 0) new.formula new.object copied.object)
    (cond (add.condition
	   (setf (sel=object.type object) 'simplification)
	   (setf (sel=object.status object) 'connected)
	   (setf (sel=object.succs object) nil)
	   (cond (modifications
		  (setf (sel=object.gterm object)
			(sel=object.change.edge.modification (sel=object.gterm object)
							     modifications t taf))))
	   (multiple-value-setq (new.object copied.object)
				(sel=object.simplified.objects (sel=case.proof sel*case.actual)))
	   (setq new.formula (sel=object.gterm.compute new.object))
	   (setq cases (mapcar #'(lambda (condition)
				   (prog1 (make-sel*case :proof (cond (first new.object)
								      (t (setq sel*stored nil)
									 (make-sel*object
									  :gterm (da-gterm.copy new.formula)
									  :hints (sel=object.hints (sel=case.proof 
												    sel*case.actual))
									  :substs (list nil)
									  :type (case (sel=object.type (sel=case.proof 
													sel*case.actual))
										  (induction 'induction)
										  (t 'simplification))
									  :status 'connected)))
							 :condition (cond (first (sel=case.condition sel*case.actual))
									  (t (mapcar #'da-gterm.copy condition)))
							 :prev.case sel*case.actual
							 :status 'initial
							 :name (format nil "~A.~D" (sel=case.name sel*case.actual) 
								       (incf counter))
							 :type (sel=case.type sel*case.actual))
				     (setq first nil)))
			       (sel=case.compute.cases add.condition)))
	   (setf (sel=case.proof sel*case.actual) copied.object)
	   (setf (sel=case.condition sel*case.actual) old.condition)
	   (cond (modifications
		  (setf (sel=object.gterm object)
			(sel=object.change.edge.modification (sel=object.gterm object) modifications nil taf))))
	   (setf (sel=object.type object) type)
	   (setf (sel=object.status object) status)
	   (setf (sel=object.succs object) succs)
	   (setf (sel=case.sub.cases sel*case.actual) cases)
	   (setf (sel=case.status sel*case.actual) 'finished)
	   (setq sel*case.actual (car cases))))))


(defun sel=object.simplified.objects (object)
  
  (let (taf.edges new.object last.object sub.object)
    (setq new.object (make-sel*object :gterm (da-gterm.copy (sel=object.gterm object)) :substs (sel=object.substs object)
				      :type (sel=object.type object) :status (sel=object.status object)
				      :hints (sel=object.hints object)))
    (cond ((member (sel=object.type object) '(simplification simplification.cases modification))
	   (setq taf.edges (assoc nil (sel=object.succs object)))
	   (cond ((and (eq (second taf.edges) 'output)
		       (third taf.edges)
		       (eq 'finished (sel=edge.status (third taf.edges))))
		  (multiple-value-setq (last.object sub.object)
				       (sel=object.simplified.objects (sel=edge.succ.object (third taf.edges))))
		  (setf (sel=object.succs new.object) 
			(list (list nil 'output (make-sel*edge :type (sel=edge.type (third taf.edges))
							       :succ.object sub.object
							       :modification (sel=edge.modification (third taf.edges))
							       :status (sel=edge.status (third taf.edges))
							       :modifier (sel=edge.modifier (third taf.edges))
							       :taf (sel=edge.taf (third taf.edges))
							       :input.subst (sel=edge.input.subst (third taf.edges))))))
		  (values last.object new.object))
		 (t (values object new.object))))
	  (t (values object new.object)))))


(defun sel=case.insert.case.analysis (case literal &optional start.again)
  
  (let (cases (counter 0) (formula (sel=object.gterm.compute (sel=object.simplified.formula (sel=case.proof case)))))
    (setq cases (mapcar #'(lambda (condition)
			    (setq sel*stored nil)
			    (prog1 (make-sel*case :proof (cond (start.again
								(make-sel*object
								 :gterm (da-gterm.copy formula)
								 :substs (list nil)
								 :hints (sel=object.hints (sel=case.proof case))
								 :type (case (sel=object.type (sel=case.proof case))
									 (induction 'induction)
									 (t 'simplification))
								 :status 'connected))
							       (t (sel=object.copy.proof (sel=case.proof case))))
						  :condition (mapcar #'da-gterm.copy condition)
						  :prev.case case
						  :status 'initial
						  :name (format nil "Case ~D" (incf counter))
						  :type (sel=case.type case))))			   
			(sel=clause.negate literal (sel=case.condition case))))
    (setf (sel=case.sub.cases case) cases)
    (setf (sel=case.status case) 'finished)))


(defun sel=case.insert.generalization (case new.gterm.list)
  (let ((counter 0))
    (setf (sel=case.sub.cases case)
	  (mapcar #'(lambda (new.gterm)
		      (make-sel*case :type (sel=case.type case)
				     :proof (make-sel*object
					     :gterm new.gterm
					     :substs (list nil)
					     :type (case (sel=object.type (sel=case.proof case))
							 (induction 'induction)
							 (t 'simplification))
					     :hints (sel=object.hints (sel=case.proof case))
					     :status 'connected)
				     :condition (mapcar #'da-gterm.copy (sel=case.condition case))
				     :name (cond ((> (length new.gterm.list) 1)
						  (format nil "Generalization Case ~D" (incf counter)))
						 (t "Generalization"))
				     :prev.case case
				     :status 'initial))
		  new.gterm.list))
    (setf (sel=case.status case) 'finished)
    0))


(defun sel=case.compute.cases (add.condition)

  (let (cases)
    (mapc #'(lambda (condition)
	    (setq cases (nconc cases (mapcan #'(lambda (clause)
						 (sel=clause.negate
						  clause (second (car (rl=mod.inverse.mod condition)))))
					       (set-difference (second (car (rl=mod.mod condition)))
							       (second (car (rl=mod.inverse.mod condition))))))))
	  (reverse add.condition))
    cases))


(defun sel=clause.negate (clause org.condition)
  
  (let (left.term)
    (cond ((and (da-literal.is clause)
		(da-literal.is.normalized.match clause))
	   (setq left.term (da-term.copy (eg-eval (car (da-gterm.termlist clause)))))
	   (cons (cons clause org.condition)
		 (mapcar #'(lambda (term)
			     (cons (da-literal.create '+ (da-predicate.equality) (list left.term term))
				   org.condition))
			 (DA-SORT.CREATE.ALL.STRUCTURE.TERMS left.term
							     (list (da-term.symbol (second (da-gterm.termlist clause))))))))
	  (t (list (cons clause org.condition)
		   (append (da-formula.junction.open 'and (da-gterm.copy (norm-normalization
									  (eg-eval (da-formula.negate clause)))))
			   org.condition))))))


;;;;;================================================================================================================
;;;;;
;;;;; Copy a total sub-proof
;;;;; ----------------------
;;;;;
;;;;;================================================================================================================


(defun sel=object.copy.proof (object)
  
  (let (entry)
    (cond ((null object) nil)
	  ((setq entry (assoc object sel*stored))
	   (cdr entry))
	  (t (setq entry (make-sel*object :gterm (cond ((member (sel=object.status object) '(sketch sketch.prop))
							(sel=object.gterm object))
						       (t (da-gterm.copy (sel=object.gterm object))))
					  :substs (mapcar #'copy-tree (sel=object.substs object))
					  :type (sel=object.type object)
					  :status (sel=object.status object)
					  :hints (copy-tree (sel=object.hints object))))
	     (push (cons object entry) sel*stored)
	     (setf (sel=object.edge entry) (cond ((sel=object.edge object) (sel=edge.copy.proof (sel=object.edge object)))))
	     (setf (sel=object.succs entry) (mapcar #'(lambda (taf.edges)
							(sel=taf.edges.copy.proof taf.edges))
						    (sel=object.succs object)))
	     (setf (sel=object.prev.object entry) (sel=object.copy.proof (sel=object.prev.object object)))
	     entry))))


(defun sel=taf.edges.copy.proof (taf.edges)
  
  (cons (car taf.edges)
	(cons (second taf.edges)
	      (mapcar #'(lambda (edge)
			  (sel=edge.copy.proof edge))
		      (cddr taf.edges)))))


(defun sel=edge.copy.proof (edge)
  (cond (edge
	 (make-sel*edge :type (sel=edge.type edge)
			:succ.object (sel=object.copy.proof (sel=edge.succ.object edge))
			:modification (sel=modification.copy.proof (sel=edge.modification edge))
			:status (copy-tree (sel=edge.status edge))
			:modifier (sel=modifier.copy.proof (sel=edge.modifier edge))
			:taf (sel=edge.taf edge)
			:input.subst (copy-tree (sel=edge.input.subst edge))))
	(t nil)))


(defun sel=modifier.copy.proof (modifier)
  
  (cond ((typep modifier 'da*modifier) modifier)
	((typep modifier 'sel*object) (sel=object.copy.proof modifier))
	((stringp modifier) modifier)
	((atom modifier) modifier)
	((and (consp modifier) (eq (car modifier) 'factor))
	 (list 'factor
	       (sel=object.copy.proof (second modifier))
	       (cond ((third modifier) (DA-GTERM.COPY (third modifier))) (t nil))
	       (sel=edge.copy.proof (fourth modifier))))
	(t modifier)))


(defun sel=modification.copy.proof (modification)
  (mapcar #'(lambda (single.mod)
	      (make-rl*mod :object nil
			   :mod (copy-tree (rl=mod.mod single.mod))
			   :inverse.mod (copy-tree (rl=mod.inverse.mod single.mod))
			   :inverted (rl=mod.inverted single.mod)
			   :information (rl=mod.information single.mod)
			   :validation (rl=mod.validation single.mod)
			   :alternatives (copy-tree (rl=mod.alternatives single.mod))))
	  modification))


(defun sel=object.copy.and.rename.gterm (object &optional taf new.term)
  
  (let* ((gterm (cond ((da-gterm.is (sel=object.gterm object)) (sel=object.gterm object))
		     (t (da-access (cdr (sel=object.gterm object)) (sel=object.gterm (car (sel=object.gterm object)))))))
	(name (da-gterm.pname gterm)) termsubst vars unifier)
    (cond ((null (getf (sel=object.attributes object) 'initial.value))
	   (setf (getf (sel=object.attributes object) 'initial.value) gterm)))
    (setq vars (set-difference (da-gterm.variables gterm) sel*variables))
    (setq termsubst (da-gterm.compute.match.binding gterm taf))
    (mapc #'(lambda (var)
	      (setq var (da-term.create var))
	      (setq new.term (uni-termsubst.apply termsubst var))
	      (cond ((not (uni-gterm.are.equal new.term var))
		     (setq unifier (car (uni-subst.merge unifier (car (uni-term.unify var new.term))))))
		    (t (setq unifier (car (uni-subst.merge unifier (UNI-CREATE.VAR.RENAMING (list (da-term.symbol var)))))))))
	  vars)
    (setf (sel=object.gterm object) (uni-subst.apply unifier gterm))
    (setf (da-gterm.pname gterm) name)))



(defun sel=refutation.environment (object taf.edges)
  
  (let (clauses vars preds)
    (cond ((sel=object.prev.object object)
	   (multiple-value-setq (clauses vars preds)
	       (sel=refutation.environment (sel=object.prev.object object)
					   (find-if #'(lambda (t.e)
							(and (third t.e)
							     (eq (sel=edge.succ.object (third t.e)) object)))
						    (sel=object.succs (sel=object.prev.object object)))))))
    (setq clauses (nconc (sel=object.conjunctive.parts object (car taf.edges)) clauses))
    (setq vars (union vars (DA-GTERM.VARIABLES.ALONG.TAF
			    (sel=object.gterm object) (car taf.edges))))
    (setq preds (union preds (da-gterm.predicates (sel=object.gterm object))))
    (values clauses vars preds)))


;;;;;=========================================================================================================
;;;;;
;;;;;  Saving proof graphs for later examining
;;;;;  ---------------------------------------
;;;;;
;;;;;  Note:  proof trees are saved in all details. substitutions, failed alternatives etc. are missing
;;;;;         modifiers are generated (uncoloured) instead of searching for the pointers to the existing ones.
;;;;;
;;;;;=========================================================================================================


(defun sel=case.store (case file)
  
  (setq sel*stored nil sel*no.stored 0)
  (with-open-file (stream file :direction :output)
		  (princ "(in-package 'inka)" stream)
		  (terpri stream)
		  (princ "(setq sel*stored.proof " stream)
		  (sel=case.save case stream)
		  (princ ")" stream)))


(defun sel=gterm.save (gterm stream &optional colour?)
  
  (cond ((da-term.is gterm)
	 (princ "(da-term.create " stream)
	 (sel=function.save (da-term.symbol gterm) stream)
	 (sel=termlist.save (da-term.termlist gterm) stream colour?)
	 (cond (colour? (sel=colours.save (da-term.colours gterm) stream)))
	 (princ ")" stream))
	((da-literal.is gterm)
	 (princ "(da-literal.create " stream)
	 (format stream "(quote ~S)" (da-literal.sign gterm))
	 (sel=predicate.save (da-literal.symbol gterm) stream)
	 (sel=termlist.save (da-literal.termlist gterm) stream colour?)
	 (cond (colour? (sel=colours.save (da-literal.colours gterm) stream))
	       (t (format stream " nil ")))
	 (format stream "(quote ~S)" (da-literal.pname gterm))
	 (princ ")" stream))
	((da-gterm.is gterm)
	 (princ "(da-gterm.create " stream)
	 (format stream "(quote ~S)" (da-gterm.symbol gterm))
	 (sel=termlist.save (da-gterm.termlist gterm) stream colour?)
	 (Format stream " nil nil (quote ~S)" (da-gterm.pname gterm))
					; (sel=attributes.save (da-gterm.attributes gterm) stream)
	 (princ ")" stream))))


(defun sel=case.save (case stream)
  
  (princ "(sel=load.case " stream)
  (format stream "(quote ~S)" (sel=case.status case))
  (format stream "(quote ~S)" (sel=case.type case))
  (prin1 (sel=case.name case) stream)
  (princ "(list " stream)
  (mapc #'(lambda (sub.case) (sel=case.save sub.case stream)) (sel=case.sub.cases case))
  (princ ")" stream)
  (sel=object.save (sel=case.proof case) stream)
  (sel=termlist.save (sel=case.condition case) stream)
  (princ ")" stream))


(defun sel=load.case (status type name sub.cases gterm condition)
  
  (make-sel*case :status status :type type :name name :sub.cases sub.cases :proof gterm
		 :condition condition))



(defun sel=object.save (object stream)
  
  (let (entry)
    (cond ((null object) (princ " NIL " stream))
	  ((setq entry (assoc object sel*stored))
	   (format stream "(cassoc ~S sel*stored)" (cdr entry)))
	  (T (push (cons object sel*no.stored) sel*stored)
	     (princ "(sel=load.object " stream)
	     (format stream " ~D " (incf sel*no.stored))
	     (sel=gterm.save (sel=object.gterm object) stream T)
	     (sel=taf.edges.save (sel=object.succs object) stream)
	     (format stream "(quote ~S)" (sel=object.status object))
	     (format stream "(quote ~S)" (sel=object.type object))
	     (sel=edge.save (sel=object.edge object) stream)
	     (princ ")" stream)))))


(defun sel=load.object (no gterm succs status type edge)
  
  (push (cons no 
	      (make-sel*object :gterm gterm :succs succs :type type :status status :edge edge))
	sel*stored)
  (cdr (car sel*stored)))


(defun sel=taf.edges.save (edges stream)
  
  (princ "(list " stream)
  (mapc #'(lambda (taf.edges)
	    (cond ((eq (second taf.edges) 'output)
		   (princ "(list" stream)
		   (format stream "(quote ~S)" (car taf.edges))
		   (format stream "(quote ~S)" (second taf.edges))
		   (sel=edge.save (third taf.edges) stream)
		   (princ ")" stream))))
	edges)
  (princ ")" stream))


(defun sel=edge.save (edge stream)
  
  (cond (edge (princ "(sel=load.edge " stream)
	      (format stream "(quote ~S)" (sel=edge.type edge))
	      (sel=object.save (sel=edge.succ.object edge) stream)
	      (sel=modification.save (sel=edge.modification edge) stream)
	      (format stream "(quote ~S)" (sel=edge.status edge))
	      (sel=modifier.save (sel=edge.modifier edge) stream)
	      (format stream "(quote ~S)" (sel=edge.taf edge))
	      (princ ")" stream))
	(t (princ " NIL " stream))))


(defun sel=load.edge (type object modification status modifier taf)
  
  (make-sel*edge :type type :succ.object object :modification modification :status status :modifier modifier
		 :taf taf))


(defun sel=modification.save (modification stream)
  
  (princ "(list " stream)
  (mapc #'(lambda (mod.step)
	    (cond ((neq (car mod.step) 'choice)
		   (princ "(list " stream)
		   (format stream "(quote ~S)" (car mod.step))
		   (sel=modifier.save (second mod.step) stream)
		   (format stream "(quote ~S)" (third mod.step))
		   (sel=gterm.save (fourth mod.step) stream T)
		   (format stream " nil ")
		   (cond ((sixth mod.step) (sel=object.save (sixth mod.step) stream)))
		   (princ ")" stream))))
	modification)
  (princ ")" stream))


(defun sel=modifier.save (modifier stream)
  
  (cond ((typep modifier 'da*modifier)
	 (princ "(sel=load.MODIFIER " stream)
	 (sel=gterm.save (da-modifier.input modifier) stream nil)
	 (sel=gterm.save (da-modifier.value modifier) stream nil)
	 (sel=termlist.save (da-modifier.condition modifier) stream nil)
	 (format stream "(quote ~S)" (da-modifier.pname modifier))
	 (princ ")" stream))
	((typep modifier 'object)
	 (sel=object.save modifier stream))
	((stringp modifier) (prin1 modifier stream))
	((da-gterm.is modifier) (sel=gterm.save modifier stream))
	((typep modifier 'sel*object) (sel=object.save modifier stream))
	((and (consp modifier) (eq (car modifier) 'factor))
	 (princ "(list 'factor " stream)
	 (sel=object.save (second modifier) stream)
	 (sel=gterm.save (third modifier) stream)
	 (sel=edge.save (fourth modifier) stream)
	 (princ ")" stream))
	(t (format stream "(quote  ~S)" modifier))))


(defun sel=load.MODIFIER (INPUT VALUE CONDITION PNAME)
  
  (make-da*modifier :modframe (make-da*modframe :INPUT INPUT :VALUE VALUE :CONDITION CONDITION :PNAME PNAME)))


(defun sel=variable.save (symbol stream)
  
  (let (entry)
    (cond ((setq entry (assoc symbol sel*stored))
	   (format stream "(cassoc ~S sel*stored)" (cdr entry)))
	  (t (princ "(sel=load.var " stream)
	     (prin1 (da-variable.pname symbol) stream)
	     (sel=sort.save (da-variable.sort symbol) stream)
	     (princ (incf sel*no.stored) stream)
	     (princ ")" stream)
	     (push (cons symbol sel*no.stored) sel*stored)))))

(defun sel=colours.save (colours stream)
  
  (princ "(list " stream)
  (mapcf #'(lambda (solution colour)
	     (sel=solution.save solution stream)
	     (sel=colour.save  colour stream))
	 colours)
  (princ ")" stream))


(defun sel=solution.save (solution stream)
  
  (let (entry)
    (cond ((atom solution) (format stream "(quote ~S)" solution))
	  ((setq entry (assoc solution sel*stored))
	   (format stream "(cassoc ~S sel*stored)" (cdr entry)))
	  (t (format stream "(sel=solution.load  (quote ~S) ~D)" solution (incf sel*no.stored))
	     (push (cons solution sel*no.stored) sel*stored)))))


(defun sel=colour.save (colour stream)
  
  (let (entry)
    (cond ((setq entry (assoc colour sel*stored))
	   (format stream "(cassoc ~S sel*stored)" (cdr entry)))
	  ((da-xvariable.is colour)
	   (format stream "(sel=xcolour.load ~D)" (incf sel*no.stored))
	   (push (cons colour sel*no.stored) sel*stored))
	  (T (format stream "(quote ~S)" colour)))))


(defun sel=skolem.function.save (symbol stream)
  
  (let (entry)
    (cond ((setq entry (assoc symbol sel*stored))
	   (format stream "(cassoc ~S sel*stored)" (cdr entry)))
	  (t (princ "(sel=load.fct " stream)
	     (prin1 (da-function.pname symbol) stream)
	     (sel=sort.save (da-function.sort symbol) stream)
	     (sel=domain.list.save (da-function.domain.sorts symbol) stream)
	     (princ (incf sel*no.stored) stream)
	     (princ ")" stream)
	     (push (cons symbol sel*no.stored) sel*stored)))))


(defun sel=predicate.save (symbol stream)
  
  (princ "(db-name.predicate " stream)
  (prin1 (da-predicate.pname symbol) stream)
  (sel=domain.list.save (da-predicate.domain.sorts symbol) stream)
  (princ ")" stream))


(defun sel=function.save (symbol stream)
  
  (cond ((da-variable.is symbol) (sel=variable.save symbol stream))
	((da-function.skolem symbol) (sel=skolem.function.save symbol stream))
	(t (princ "(db-name.function " stream)
	   (prin1 (da-function.pname symbol) stream)
	   (sel=domain.list.save (da-function.domain.sorts symbol) stream)
	   (sel=sort.save (da-function.sort symbol) stream)
	   (princ ")" stream))))


(defun sel=termlist.save (sorts stream &optional colour?)
  
  (princ "(list " stream)
  (mapcar #'(lambda (sort) (sel=gterm.save sort stream colour?)) sorts)
  (princ ")" stream))


(defun sel=sort.save (sort stream)
  
  (princ " (db-name.sort " stream)
  (prin1 (da-sort.pname sort) stream)
  (princ ")" stream))


(defun sel=domain.list.save (sorts stream)
  
  (princ "(list " stream)
  (mapcar #'(lambda (sort) (sel=sort.save sort stream)) sorts)
  (princ ")" stream))



(defun sel=load.fct (name domain range no)
  (let ((fct (da-function.create name domain range t)))
    (push (cons no fct) sel*stored)
    fct))


(defun sel=load.var (name range no)
  (let ((var (da-variable.create range name)))
    (push (cons no var) sel*stored)
    var))


(defun sel=solution.load (name no)
  
  (push (cons no name) sel*stored)
  name)


(defun sel=xcolour.load (no)
  
  (push (cons no (DA-COLOUR.CREATE.VARIABLE)) sel*stored)
  (cdr (car sel*stored)))



;;;;;==============================================================================================================
;;;;;
;;;;; Definition of selection windows for database and modifier entries:
;;;;;
;;;;;==============================================================================================================



(defun sel=pr.select.database.entry (gterm types &optional bridge.lemma)
  
  (let ((sel*choice nil)) 
    (pr-graphic.interact (win-window 'description_3)
			 `(sel=pr.select.database.entry.1 (quote ,gterm) (quote ,types) (quote ,bridge.lemma)))
    sel*choice))


(defun sel=pr.select.modifier (term types &optional bridge.lemma)
  
  (let ((sel*choice nil)) 
    (pr-graphic.interact (win-window 'description_3)
			 `(sel=pr.select.modifier.1 (quote ,term) (quote ,types) (quote ,bridge.lemma)))
    sel*choice))



(defun sel=pr.select.database.entry.1 (gterm types &optional bridge.lemma no.active)
  
  (let (items)
    (cond ((eq (type-of gterm) 'da*sort) 
	   (setq gterm (da-literal.create (da-sign.plus) (da-predicate.equality)
					  (list (da-term.create (da-variable.create gterm))
						(da-term.create (da-variable.create gterm)))))))
    (setq items (mapcan #'(lambda (type)
			    (db-predicate.database.collection gterm
			     type
			     #'(lambda (item)
				 (cond ((or bridge.lemma (uni-literal.unify (car item) gterm 'opposite))
					(list (cons (third item)
						    (pr-parse.string
						     (da-gterm.pname (third item)) 
						     :font 'bold :size 'B
						     :double.left `(sel=pr.database.entry (quote ,item))
						     :right `(progn (setq sel*choice (quote ,item))
								    1)))))))))
			types))
    (cond (no.active
	   (setq items (remove-duplicates
			items :test #'(lambda (item1 item2)
					(uni-gterm.are.equal (car item1) (car item2)))))))
    (setq items (mapcar #'cdr items))			
    (pr-parse.headline "Please choose an item"
		       (cond (items (pr-parse.table items 3))
			     (t (pr-parse.string "No possible choices" :font 'bold :size 'B))))))


(defun sel=pr.select.modifier.1 (term types &optional bridge.lemma)
  
  ;;; symbol.or.occ is either an gterm
  
  (let (items)
    (setq items (mapcan #'(lambda (type)
			    (db-modifier.collection 
			     term type nil
			     #'(lambda (item)
				 (cond ((or bridge.lemma (sel=modifier.test.unify item term nil nil nil))
					(list (pr-parse.string
					       (da-modifier.pname item) :font 'bold :size 'B
					       :double.left `(sel=pr.modifier.entry (quote ,item))
					       :right `(progn (setq sel*choice (quote ,item)) 1))))))))
			types))
    (pr-parse.headline "Please choose an item"
		       (cond (items (pr-parse.table items 3))
			     (t (pr-parse.string "No possible choices" :font 'bold :size 'B))))))



(defun sel=pr.modifier.entry (modifier)
  
  (pr-parse.headline (format nil "Lemma ~A:" (da-modifier.pname modifier))
		     (pr-parse.closure
		      (pr-parse.itemize (mapcar #'(lambda (x) (pr-parse.string x :font 'fixbold :size 'D))
						(pr-print.modifier modifier))
					nil)
		      'boxed 3)))


(defun sel=pr.database.entry (entry)
  
  (pr-parse.headline (format nil "Lemma ~A:" (da-gterm.pname (third entry)))
		     (pr-parse.gterm (third entry) nil
				     #'(lambda (gterm taf)
					 (declare (ignore gterm))
					 (cond ((equal (fourth entry) taf)
						(list :font 'bold)))))))


(defun sel=mod.activate.by.function ()

  (LET (INPUT gterm (sel*choice nil))
    (COND ((SETQ INPUT (sel=general.select.function (WIN-WINDOW 'DESCRIPTION_1)))
	   (PR-GRAPHIC.INTERACT (WIN-WINDOW 'DESCRIPTION_3) 
				`(sel=pr.select.modifier.1 (da-term.create ,(CAR INPUT) nil)
							   '(pumping top.level changing) t))))
    (cond (sel*choice
	   (setq gterm (da-gterm.copy (da-modifier.gterm sel*choice)))
	   (uni-subst.apply (uni-create.var.renaming (set-difference (da-gterm.variables gterm) sel*variables))
			    gterm)))))


(defun sel=mod.activate.by.predicate ()

  (LET (INPUT gterm (sel*choice nil))
    (COND ((SETQ INPUT (sel=general.select.predicate (WIN-WINDOW 'DESCRIPTION_1)))
	   (PR-GRAPHIC.INTERACT (WIN-WINDOW 'DESCRIPTION_3)
				`(sel=pr.select.database.entry.1 (da-literal.create (da-sign.plus) (QUOTE ,(CAR INPUT)) nil)
								 '(+ - ++ --) t t))))
    (cond (sel*choice 
	   (setq gterm (third sel*choice))
	   (uni-subst.apply (uni-create.var.renaming (set-difference (da-gterm.variables gterm) sel*variables))
			    gterm)))))



(defun sel=general.select.function (window)

  (WIN-MN.choose WINDOW
		(MAPCAR #'(LAMBDA (FCT)
			      (CONS (FORMAT nil "~A ( ~{~A ~} ) : ~A" (DA-FUNCTION.PNAME FCT)
					    (DA-FUNCTION.DOMAIN.SORTS FCT) (DA-FUNCTION.SORT FCT))
				    FCT))
			  (DB-FUNCTION.ALL))))


(defun sel=general.select.predicate (window)

  (WIN-MN.choose WINDOW
		(MAPCAN #'(LAMBDA (FCT)
			    (COND ((DA-PREDICATE.IS.EQUALITY FCT)
				   (MAPCAR #'(LAMBDA (SORT)
					       (CONS (FORMAT nil "= on ~A" (DA-SORT.PNAME SORT))
						     SORT))
					   (DB-SORT.ALL)))
				  (T (LIST (CONS (FORMAT nil "~A ( ~{~A ~} )" (DA-predicate.PNAME FCT)
							 (DA-predicate.DOMAIN.SORTS FCT))
						 FCT)))))
			(DB-predicate.all))))


(defun sel=man.prs (case)

  (let (result)
    (cond ((setq result (win-mn.popup (win-window 'description_1)
				      '(("Print Proof " . nil))))
	   (cond ((eq (car result) 1)
		  case			; (sel=prs.proof case)
		  ))))
    nil))


(defun sel=prs.proof (case)

  (pr-ps.page (sel=prs.theorem case) "~/test.ps"))


(defun sel=prs.theorem (case)

  (pr-parse.itemize
   (list (pr-parse.string "Proof of the theorem" :font 'bold :size 'B)
	 (pr-parse.string "" :size 'BB)
	 (pr-parse.closure (pr-parse.gterm (sel=object.gterm.compute (sel=case.proof case))
					   60 nil :font 'italic :size 'D)
			   'boxed 1 "LightGrey" 3)
	 (pr-parse.string "" :size 'BB)
	 (pr-parse.string "Using the axiomization:" :font 'bold :size 'D)
	 (pr-parse.string "" :size 'D)
	 (sel=prs.axiomation))
   nil :font 'italic :size 'D))


(defun sel=prs.axiomation ()

  (pr-parse.string "unspec"))


(defun sel=prs.cases (case)

  (cond ((sel=case.sub.cases case)
	 (nconc (list (sel=prs.case case)
		      (pr-parse.string "In order to prove this theorem we do a case analysis:" :font 'bold :size 'B)
		      (pr-parse.string "" :size 'B))
		(mapcar #'(lambda (case)
			    (sel=prs.case case))
			(sel=case.all.cases case))))
	(t (sel=prs.case case))))


(defun sel=prs.case (case)

  (list (pr-parse.string "Case ~A" (sel=case.name case) :font 'bold :size 'B)
	(pr-parse.string "" :size 'BB)
	(pr-parse.string "Assume the following conditions:" :font 'bold :size 'D)
	(sel=prs.condition case)
	(pr-parse.string "We do the following modifications:" :font 'bold :size 'D)
	(sel=prs.top.object (sel=case.proof case))))


(defun sel=prs.condition (case)

  (declare (ignore case))
  nil)


(defun sel=prs.top.object (case)

  (sel=prs.object (sel=case.proof case)
		  (sel=object.gterm.compute (sel=case.proof case))
		  nil))


(defun sel=prs.object (object gterm taf)

  (let (next.proof.print proof.print)
    (mapcan #'(lambda (taf.edges)
		(cond ((eq (second taf.edges) 'output)
		       (multiple-value-setq (gterm proof.print)
			  (sel=prs.mods (sel=edge.modification (third taf.edges)) gterm taf))
		       (multiple-value-setq (gterm next.proof.print)
		     	  (sel=prs.object (sel=edge.succ.object (third taf.edges))
					  (append (second taf.edges) taf) 
					  gterm))
		       (list (nconc proof.print next.proof.print)))))
	    (sel=object.succs object))))


(defun sel=prs.mods (modification gterm taf)

  (let (proof.print)
    (mapcan #'(lambda (modifier)
		(multiple-value-setq (gterm proof.print)
				     (sel=prs.modification modifier gterm taf))
		proof.print)
	    modification)))


(defun sel=prs.modification (modifier gterm taf)

  (declare (ignore modifier gterm taf))

  nil)


(defun sel=gterm.simplify.by.internal.equations (gterm subst)

  ;;; Simplifies the gterm, respecting the following semantics:
  ;;; When the simplified gterm is refutable, then the original gterm was refutable

  (let (result)
    (multiple-value-setq (result subst)
       (sel=gterm.apply.simplification.literals gterm subst))
    (sel=gterm.remove.marks result)
    (values result subst)))


(defun sel=gterm.apply.simplification.literals (gterm subst &optional taf)

  (let ((sub.gterm (da-access taf gterm)) term symbol sign termsubst left right rem)
    (cond ((da-literal.is sub.gterm)
	   (MULTIPLE-VALUE-SETQ (TERM SYMBOL SIGN) (DA-LITERAL.DENOTES.MATCH sub.gterm (DA-SIGN.MINUS)))
	   (cond (term
		  (SEL=LITERAL.set.MARK sub.gterm (cond (sign 'and.origin) (T 'or.origin)))
		  (setq termsubst (uni-termsubst.create nil (da-term.copy term)
							(DA-SORT.CONSTRUCTOR.TERM TERM SYMBOL)))
		  (cond (sign
			 (setq gterm (sel=termsubst.apply.on.conjunctive.parts gterm taf termsubst)))
			(T (setq gterm (sel=termsubst.apply.on.disjunctive.parts gterm taf termsubst))
			   (sel=literal.remove.mark (da-access taf gterm) 'or.origin)))))
	   (multiple-value-setq (left right sign rem) (sel=literal.is.simplification.rule sub.gterm))
	   (cond (left
		  (sel=literal.set.mark sub.gterm (cond ((da-sign.is.positive sign) 'and.origin)
							(T 'or.origin)))
		  (setq termsubst (uni-termsubst.create nil left right))
		  (cond ((da-sign.is.positive sign)
			 (setq gterm (sel=termsubst.apply.on.conjunctive.parts gterm taf termsubst)))
			(rem (setq subst (uni-termsubst.create subst left right))
			     (setq gterm (uni-termsubst.apply termsubst 
							      (da-replace taf gterm (da-literal.false)))))
			(T (setq gterm (sel=termsubst.apply.on.disjunctive.parts gterm taf termsubst))
			   (sel=literal.remove.mark (da-access taf gterm) 'or.origin))))))
	  (T (setq taf (da-taf.create.zero taf))
	     (mapc #'(lambda (term) 
		       (setq taf (da-taf.create.next taf))
		       (multiple-value-setq (gterm subst)
					    (sel=gterm.apply.simplification.literals gterm subst taf)))
		   (da-gterm.termlist sub.gterm))))
    (values gterm subst)))


(defun sel=literal.is.simplification.rule (literal)
  (cond ((da-literal.is.equality literal)
	 (cond ((and (or (da-variable.is (da-gterm.symbol (car (da-gterm.termlist literal))))
			 (da-function.is.selector (da-gterm.symbol (car (da-gterm.termlist literal)))))
		     (null (da-gterm.variables (second (da-gterm.termlist literal))))
		     (null (da-gterm.constants (second (da-gterm.termlist literal)) 'skolem)))
		(values (car (da-gterm.termlist literal))
			(second (da-gterm.termlist literal)) 
			(da-literal.sign literal)
			(da-variable.is (da-gterm.symbol (car (da-gterm.termlist literal))))))
	       ((and (or (da-variable.is (da-gterm.symbol (second (da-gterm.termlist literal))))
			 (da-function.is.selector (da-gterm.symbol (second (da-gterm.termlist literal)))))
		     (null (da-gterm.variables (car (da-gterm.termlist literal))))
		     (null (da-gterm.constants (car (da-gterm.termlist literal)) 'skolem)))
		(values (second (da-gterm.termlist literal))
			(car (da-gterm.termlist literal))
			(da-literal.sign literal)
			(da-variable.is (da-gterm.symbol (second (da-gterm.termlist literal))))))))))
	       


(defun sel=termsubst.apply.on.conjunctive.parts (gterm taf termsubst)
  (cond ((or (null taf) (eq 'or (da-gterm.symbol (da-access (da-taf.super.taf taf) gterm))))
	 (cond ((null taf) 
		(setq gterm (sel=termsubst.apply.ON.FREE.LITERALS gterm termsubst 'and.origin)))
	       (T (da-replace taf gterm
			      (SEL=TERMSUBST.apply.ON.FREE.LITERALS 
			       (da-access taf gterm) termsubst 'and.origin)))))
	(t (setq gterm (sel=termsubst.apply.on.conjunctive.parts gterm (da-taf.super.taf taf) termsubst))))
  gterm)


(defun sel=termsubst.apply.on.disjunctive.parts (gterm taf termsubst)
  (cond ((or (null taf) (eq 'and (da-gterm.symbol (da-access (da-taf.super.taf taf) gterm))))
	 (cond ((null taf)
		(setq gterm (sel=termsubst.apply.ON.FREE.LITERALS gterm termsubst 'or.origin)))
	       (t (da-replace taf gterm 
			      (SEL=TERMSUBST.apply.ON.FREE.LITERALS 
			       (da-access taf gterm) termsubst 'OR.ORIGIN)))))
	(t (setq gterm (sel=termsubst.apply.on.disjunctive.parts gterm (da-taf.super.taf taf)
								 termsubst))))
  gterm)


(defun SEL=TERMSUBST.apply.ON.FREE.LITERALS (gterm termsubst type)
  (cond ((da-literal.is gterm)
	 (cond ((not (SEL=LITERAL.IS.marked gterm type)) 
		(setq gterm (da-gterm.copy (EG-EVAL (uni-termsubst.apply termsubst gterm)))))))
	(T (setf (da-gterm.termlist gterm)
		 (mapcar #'(lambda (subgterm) 
			     (SEL=TERMSUBST.apply.ON.FREE.LITERALS subgterm termsubst type))
			 (da-gterm.termlist gterm)))))
  gterm)
	

(DEFUN SEL=LITERAL.set.MARK (LITERAL TYPE)
  (SETF (GETF (DA-LITERAL.ATTRIBUTES LITERAL) Type) T))

(defun sel=literal.remove.mark (literal type)
  (REMF (DA-LITERAL.ATTRIBUTES literal) type))

(DEFUN SEL=LITERAL.IS.marked (LITERAL type)
  (GETF (DA-LITERAL.ATTRIBUTES LITERAL) type))


(DEFUN SEL=GTERM.REMOVE.MARKS (gterm)
  (cond ((da-literal.is gterm)
	 (SEL=LITERAL.remove.mark gterm 'or.origin)
	 (SEL=LITERAL.remove.mark gterm 'and.origin))
	(T (mapc #'(lambda (subgterm) (SEL=GTERM.REMOVE.MARKS subgterm)) 
		 (da-gterm.termlist gterm)))))


;;; Auswertung von ground Literalen

(DEFUN SEL=GTERM.EVALUATE.GROUND.LITERALS.WITH.COMPLEX.ARGUMENTS (GTERM)

  ;;; Input  : a gterm
  ;;; Effect : evaluates ground literals with non constants arguments
  ;;; Value  : the evaluated GTERM

  (COND ((DA-LITERAL.IS GTERM) (SETQ GTERM (SEL=GROUND.LITERAL.EVALUATE.IF.ARGUMENTS.ARE.COMPLEX GTERM)))
	(T (SETF (DA-FORMULA.TERMLIST GTERM)
		 (MAPCAR #'(LAMBDA (SUBFORMULA)
			     (COND ((DA-LITERAL.IS SUBFORMULA)
				    (SEL=GROUND.LITERAL.EVALUATE.IF.ARGUMENTS.ARE.COMPLEX SUBFORMULA))
				   (T (SEL=GTERM.EVALUATE.GROUND.LITERALS.WITH.COMPLEX.ARGUMENTS SUBFORMULA))))
			 (DA-GTERM.TERMLIST GTERM)))))
  GTERM)


(DEFUN SEL=GROUND.LITERAL.EVALUATE.IF.ARGUMENTS.ARE.COMPLEX (LITERAL)

  ;;; Input  : a literal
  ;;; Effect : replaces the literal by an equivalent formula resulting from the definition gterm of
  ;;;          the predicate symbol of 
  ;;;          the literal, iff the literal is ground and every argument is a non-constant
  ;;; Value  : the equivalent formula or the literal himself.

  (COND ((AND (not (da-literal.is.equality literal))
	      (NULL (DA-GTERM.VARIABLES LITERAL))
	      (DA-LITERAL.TERMLIST LITERAL)
	      (EVERY #'(lambda (term) 
			 (and (da-gterm.termlist term)
			      (sel=term.is.constructor.term term)))
		     (DA-LITERAL.TERMLIST LITERAL)))
	 (SEL=LITERAL.EVALUATE.BY.PREDICATE.DEFINITION LITERAL))
	(T LITERAL)))


(defun sel=term.is.constructor.term (term)

  (let ((symbol (da-term.symbol term)))
    (and (da-function.is symbol)
	 (or (da-prefun.is.constant symbol)
	     (and (da-function.is.constructor symbol)
		  (every #'sel=term.is.constructor.term (da-term.termlist term)))))))


(DEFUN SEL=LITERAL.EVALUATE.BY.PREDICATE.DEFINITION (LITERAL)

  ;;; Input  : a literal P(t_1 ... t_n)
  ;;; Effect : computes out of the definition of the P an equivalent formula to P(t_1 ... t_n)
  ;;; Value  : the equivalent formula.

  (LET ((EQUIVALENCES (da-predicate.definition.body (da-literal.symbol literal) (da-literal.sign literal))))
    (COND (EQUIVALENCES
	   (eg-eval
	    (UNI-SUBST.APPLY 
	     (CAR (UNI-LITERAL.MATCH 
		   (DA-LITERAL.CREATE (DA-LITERAL.SIGN LITERAL) (DA-LITERAL.SYMBOL LITERAL)
				      (MAPCAR #'(LAMBDA (VAR)
						  (DA-TERM.CREATE VAR))
					      (DA-PREDICATE.FORMAL.PARAMETERS (DA-LITERAL.SYMBOL LITERAL))))
		   LITERAL))
	     EQUIVALENCES))))))






;;;; this should be part of a future generalization!!!


(defun sel=generalize.case (case)

  (let* ((condition (sel=case.condition case))
	 (formula (da-formula.junction.open 'and (sel=object.gterm.compute (sel=object.simplified.formula (sel=case.proof case)))))
	 new.case changed)
    (cond ((neq 'induction.step (sel=case.type sel*case.actual))
	   (setq formula (da-formula.junction.open 
			  'and (sel=object.gterm.compute (sel=object.simplified.formula (sel=case.proof case))))))
	  (t (multiple-value-setq (condition formula changed)
	       (sel=generalize.induction.step (sel=case.proof case) condition))))
    (cond (formula
	   (multiple-value-setq (condition formula changed)
	     (sel=generalize.non.needed.equations condition formula changed))
	   (multiple-value-setq (condition formula changed)
	     (sel=generalize.invert.term condition formula changed))
	   (multiple-value-setq (condition formula changed)
	     (sel=generalize.surjective.terms condition formula changed))
	   (cond (changed 
		  (setq new.case (sel=generalize.create.case condition formula changed case))
		  (setf (sel=case.sub.cases case) (list new.case))
		  t))))))


(defun sel=generalize.induction.step (object condition)

  (let ((edge (third (car (sel=object.succs object)))) formula termsubst)
    (cond (edge
	   (setq formula (da-formula.junction.closure
			  'or
			  (mapcar #'(lambda (problem)
				      (multiple-value-setq (problem termsubst)
					(sel=generalize.ind.subterms (da-formula.junction.open 'and problem) termsubst))
				      problem)
				  (da-formula.junction.open 'or (sel=object.gterm.compute (sel=edge.succ.object edge))))))
	   (cond (termsubst (setq condition (remove-if #'(lambda (x) (da-formula.is.true x))
						       (mapcar #'(lambda (x) 
								   (eg-eval (uni-termsubst.apply termsubst x)))
							       condition)))
			    (setq formula (uni-termsubst.apply termsubst formula))
			    (values condition (list formula) (list termsubst))))))))


(defun sel=generalize.ind.subterms (gtermlist termsubst)
  
  (let ((gterm (car gtermlist)) side hypo.tafs sub.term)
    (cond ((and (da-literal.is.negated.equation gterm)
		(setq hypo.tafs (da-gterm.coloured.terms gterm 'hypo 'induction)))  ;;; hypo has been applied.
	   (setq side (last (car hypo.tafs)))
	   (mapcan #'(lambda (ind.taf)
		       (setq sub.term (da-access ind.taf (da-access (da-taf.otherside side) gterm)))
		       (cond ((and (da-gterm.termlist sub.term)
				   (da-gterm.is.coloured sub.term 'induction)
				   (some #'(lambda (hypo.taf)
					     (da-gterm.occurs.in.gterm sub.term (da-access hypo.taf (car gtermlist))))
					 hypo.tafs))
			      (setq termsubst (uni-termsubst.create termsubst sub.term
								    (da-term.create 
								     (da-function.create nil (da-term.sort sub.term)
											 nil t)
								     nil)))
			      (setq gtermlist (list gterm)))))
		   (DA-GTERM.MAX.COLOURED.GTERMS (da-access (da-taf.otherside side) gterm) 'induction))))
    (values (da-formula.junction.closure 'and gtermlist) termsubst)))
	   
	


(defun sel=generalize.create.case (condition formulas changed org.case)

  (make-sel*case :type 'generalization
		 :proof (make-sel*object
			 :gterm (da-gterm.copy (da-formula.junction.closure 'and formulas))
			 :substs (list nil)
			 :type 'simplification
			 :status 'connected)
		 :information nil
		 :instances nil
		 :condition (mapcar #'(lambda (x) (da-gterm.copy x)) condition)
		 :name (format nil "Gen. of ~A" changed)
		 :prev.case org.case
		 :status 'initial))



(defun sel=generalize.surjective.tafs (gterm tafs)

  (cond (tafs 
	 (setq tafs (mapcar #'(lambda (x) (cdr x)) tafs))
	 (let* ((first.taf (car tafs))
		     (term (da-access first.taf gterm)))
	   (cond ((and (da-function.is (da-gterm.symbol term))
		       (sel=term.is.surjective term)
		       (every #'(lambda (taf)
				  (uni-gterm.are.equal term (da-access taf gterm)))
			      (cdr tafs)))
		  (cond ((sel=generalize.surjective.tafs gterm tafs))
			(t tafs))))))))


(defun sel=term.is.surjective (term &optional used.skolems)

  (let ((symbol (da-term.symbol term)) pos)
    (cond ((da-function.is symbol)
	   (cond ((and (null (da-term.termlist term))
		       (da-function.skolem symbol)
		       (not (member symbol used.skolems)))
		  (cons symbol used.skolems))
		 ((setq pos (da-function.is.surjective symbol))
		  (every #'(lambda (pos)
			     (setq used.skolems (sel=term.is.surjective (nth pos (da-term.termlist term)) used.skolems)))
			 pos)))))))



(defun sel=generalize.non.needed.equations (condition formula changed)

  (let* ((ass.formula (da-formula.junction.closure 'and (append condition formula)))
	 gterm)
    (mapc #'(lambda (skolem.const)
	      (setq tafs (da-symbol.occurs.in.gterm skolem.const ass.formula))
	      (cond ((and (car tafs) (null (cdr tafs)))
		     (setq gterm (da-access (cdr (car tafs)) ass.formula))
		     (cond ((and (da-literal.is gterm) (da-literal.is.equation gterm))
			    (setq condition (remove gterm condition))
			    (setq formula (remove gterm formula)))))))
	  (remove-if #'(lambda (fct) (da-function.domain.sorts fct))
		     (da-gterm.functions ass.formula 'skolem)))
    (values condition formula changed)))



(defun sel=generalize.surjective.terms (condition formula changed)

  (let* ((ass.formula (da-formula.junction.closure 'and (append condition formula)))
	 (skolem.consts (remove-if #'(lambda (fct) (da-function.domain.sorts fct))
				   (da-gterm.functions ass.formula 'skolem)))
	 tafs gen.term termsubst)
    (mapc #'(lambda (skolem.const)
	      (setq tafs (da-symbol.occurs.in.gterm skolem.const ass.formula))
	      (setq tafs (sel=generalize.surjective.tafs ass.formula tafs))
	      (cond (tafs (setq gen.term (da-access (car tafs) ass.formula))
			  (setq termsubst (uni-termsubst.create termsubst gen.term
								(da-term.create 
								 (da-function.create nil (da-term.sort gen.term)
										     nil t)
								 nil))))))
	  skolem.consts)
    (cond (termsubst 
	   (setq condition (mapcar #'(lambda (x) (uni-termsubst.apply termsubst x)) condition))
	   (setq formula (mapcar #'(lambda (x) (uni-termsubst.apply termsubst x)) formula))
	   (setq changed (cons termsubst changed))))
    (values condition formula changed)))


(defun sel=generalize.invert.term (condition formulas changed)

  (let (repl termsubst)
    (mapc #'(lambda (formula)
	      (cond ((and (da-literal.is formula)
			  (da-literal.is.equation formula))
		     (setq repl (cond ((sel=generalize.is.invert.equation (da-gterm.termlist formula)))
				      (t (sel=generalize.is.invert.equation (reverse (da-gterm.termlist formula))))))
		     (cond (repl (setq termsubst (append repl termsubst)))))))
	  (append condition formulas))
    (cond (termsubst (setq condition (remove-if #'(lambda (x) (da-formula.is.true x))
						(mapcar #'(lambda (x) 
							    (eg-eval (uni-termsubst.apply termsubst x)))
							condition)))
		     (setq formulas (remove-if #'(lambda (x) (da-formula.is.true x))
					       (mapcar #'(lambda (x) (uni-termsubst.apply termsubst x))
						       formulas)))
		     (multiple-value-setq (condition formulas changed)
		       (sel=generalize.invert.term condition formulas changed))
		     (values condition formulas (cons termsubst changed)))
	  (t (values condition formulas changed)))))
		     


(defun sel=generalize.is.invert.equation (termlist)

  (let ((left (car termlist)) (right (second termlist)) (counter 0) new.termlist)
    (cond ((and (da-function.is (da-term.symbol left))
		(da-function.skolem (da-term.symbol left))
		(da-function.is (da-term.symbol right))
		(da-term.termlist right)
		(every #'(lambda (term)
			   (incf counter)
			   (and (da-function.is (da-term.symbol term))
				(eql 1 (length (da-term.termlist term)))
				(uni-term.are.equal left (car (da-term.termlist term)))
				(sel=generalize.functions.are.inverse (da-term.symbol right) (da-term.symbol term) counter)))
		       (da-term.termlist right)))
	   (setq new.termlist (mapcar #'(lambda (term) (da-term.create (da-function.create nil (da-term.sort term) nil t) nil))
				      (da-term.termlist right)))
	   (uni-termsubst.create.parallel (cons left (da-term.termlist right)) 
					  (cons (da-term.create (da-term.symbol right) new.termlist)
						new.termlist))))))



(defun sel=generalize.functions.are.inverse (function1 function2 index)

  ;;; Input :  two functions $s$ and $p$ and an index $i$
  ;;; Effect:  checks whether $p(s(x_1,\ldots, x_n)) = x_i$ holds.
  ;;; Value:   T, if this property holds.

  (and (da-function.is.constructor function1)
       (eq (nth (1- index) (da-sort.selectors.of.constructor function1)) function2)
       (da-sort.is.free.structure (da-function.sort function1))))

