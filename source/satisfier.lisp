
(in-package :INKA)


;;; This a totally new implementation of the satisfier module of inka.
;;;
;;; This module tries to instantiate symbols, which satisfy the test sat=variable.is
;;; in order to to generate an instance of a formula which is true wrt. the given 
;;; axioms.


(defvar sat*max.depth 25)



(defun sat-satisfy.neg.gterm (gterm)

  (cond ((null (da-gterm.variables gterm))
	 (let ((skolems (da-gterm.functions gterm 'skolem)) replacement result tafs new.gterm eval.list)
	   (cond ((every #'(lambda (skolem)
			     (null (da-function.domain.sorts skolem)))
			 skolems)
		  (setq replacement (mapcar #'(lambda (skolem)
						(cons skolem (da-term.create (da-variable.create (da-function.sort skolem)))))
					    skolems))
		  (catch 'sat*abort
		    (setq result (sat=satisfy.formula
				  (list (sat=gterm.replace.skolems gterm replacement))
				  nil)))
		  (cond (result (setq result (sat=beautify.result (car result) replacement))
				(setq tafs (da-gterm.tafs gterm #'(lambda (subterm) (assoc (da-gterm.symbol subterm) result))))
				(setq new.gterm (sat=gterm.replace.skolems gterm result))
				(multiple-value-bind (x y) (eg-eval new.gterm)
				  (cond ((da-formula.is.true x)
					 (push (cons nil new.gterm) eval.list)
					 (while (car tafs)
					   (setq new.gterm (da-gterm.copy new.gterm))
					   (setq tafs (remove-duplicates (mapcar #'(lambda (taf) (cdr taf)) tafs) :test 'equal))
					   (mapc #'(lambda (taf)
						     (setq new.gterm (da-replace taf new.gterm (eg-eval (da-access taf new.gterm)))))
						 (da-taf.botton.tafs tafs))
					   (push (cons (da-taf.botton.tafs tafs) new.gterm) eval.list))
					 (values result (remove-duplicates y) eval.list))))))))))))


(defun sat-satisfy.gterm (gterm)
  
  ;;; Input:  a gterm and a boolean. Gterm has to be a quantifier-free gterm with only AND and OR as junctions.
  ;;;         free variables occurring in gterm are considered as ex-quantified while skolem-functions are not allowed.
  ;;; Effect: it is tested, whether there is an assignment to the variables of \verb$GTERM$ such that \verb$GTERM$ is valid.
  ;;;         If comment is non-NIL the result of this call is documented.
  ;;; Value:  a multiple-value \verb$(SUBSTITUTION CUTS)$:
  ;;;         if assignment has been found, \verb$SUBSTITUTION$ represents it/is T and \verb$CUTS$ is undefined;
  ;;;         if no assignment has been found \verb$SUBSTITUTION$ is NIL and
  ;;;         \verb$CUTS$ is NIL, if it is sure, that no assignment exists
  ;;;         \verb$CUTS$ is non-NIL otherwise

  (let ((result (sat=satisfy.formula (list gterm) nil)))
    (cond (result (mapc #'(lambda (var.term)
			    (format t "~A : ~A ~%" (car var.term) (sat=gterm.insert.bindings (cdr var.term))))
			(car result))
		  result))))



;;; =========================================================================================================
;;;
;;; This is a framework for an AND-OR-TREE mechanism.
;;;
;;;   AND - OR trees are implemented in the following way:
;;;
;;;   and -branches are lists  (AND P1 ... Pn) with Pi being the specific problems
;;;   or - branches are (OR binding P1 ... Pm) with Pi being the specific problems



(defun sat=merge.problems (n1 n2) 
  
  (cond ((cdr n1) 
	 (let (l1 l2)
	   (mapc #'(lambda (formula)
		     (cond ((and (da-literal.is formula)
				 (da-predicate.is.equality (da-literal.symbol formula))
				 (da-sign.is.positive (da-literal.sign formula))
				 (or (da-variable.is (da-gterm.symbol (car (da-literal.termlist formula))))
				     (da-variable.is (da-gterm.symbol (second (da-literal.termlist formula))))))
			    (push formula l1))
			   (t (push formula l2))))
		 n1)
	   (append l1 l2 n2)))
	(t (append n1 n2))))
			    


(defun sat=satisfy.formula (problems &optional inst)
  
;;; Input:  LITERAL to be solved, maximum and actual pointer to SAT*LITERAL.STACK
;;; Effect: a deduction step of the calculus is executed
;;; Value:  list of alternative gterms or alternatives or the atoms 'SOLVED or 'CONTRA
  
  (cond ((null problems) (sat=solution inst))
	(sel*suspend   
	 (SEL-SUSPEND NIL)
	 (rl-suspend nil)
	 (throw 'sat*abort nil))
	(t (let ((formula (car problems)) old.formula)
	     (cond ((eq (da-gterm.symbol formula) 'and)
		    (sat=satisfy.formula (sat=merge.problems (da-gterm.termlist formula) (cdr problems)) inst))
		   ((eq (da-gterm.symbol formula) 'or)
		    (some #'(lambda (sub.formula)
			      (sat=satisfy.formula (cons sub.formula (cdr problems)) inst))
			  (da-gterm.termlist formula)))
		   ((> (sat=literal.depth formula) sat*max.depth) nil)
		   (t (setq old.formula formula)
		      (setq formula (sat=literal.insert.depth (NORM-NORMALIZE.GTERM (eg-eval (sat=gterm.insert.bindings formula))) old.formula))
		      (cond ((da-formula.is.false formula) nil)
			    ((da-formula.is.true formula) 
			     (sat=satisfy.formula (cdr problems) inst))
			    ((not (da-literal.is formula)) 
			     (sat=satisfy.formula (cons formula (cdr problems)) inst))
			    ((not (da-predicate.is.equality (da-gterm.symbol formula)))
			     (some #'(lambda (case)
				       (sat=satisfy.formula (sat=merge.problems case (cdr problems)) inst))
				   (sat=rule.predicate.definition formula)))
			    (t (sat=satisfy.equation formula (cdr problems) inst)))))))))



(defun sat=solution (inst)

  (list (mapcar #'(lambda (var) (cons var (getf (da-variable.attributes var) 'sat.binding))) inst)))


(defun sat=satisfy.equation (formula other.problems inst)

  (let (instantiation sols ok)
    (cond ((setq instantiation (sat=rule.unification formula))
	   (cond ((sat=satisfy.formula other.problems (cons instantiation inst)))
		 (t (sat=binding.delete instantiation)
		    nil)))
	  ((setq sols (cond ((sat=rule.instantiate.vars formula))
			    ((sat=rule.selector formula))
			    ((sat=rule.function.definition formula))))
	   (some #'(lambda (new.problems)
		     (setq new.problems (sat=merge.problems new.problems other.problems))
		     (sat=satisfy.formula new.problems inst))
		 sols)))))



;;; Rules of the calculus
;;; ---------------------


(defun sat=rule.unification (equation)

  ;;; Input:  a literal with the equality symbol
  ;;; Effect: implements the unification rule: if both sides can be unified then 
  ;;;         the binding is computed. Note that both sides of the equation will
  ;;;         not be equal !
  ;;; Value:  the binding

  (cond ((da-sign.is.positive (da-literal.sign equation))
	 (cond ((sat=term.check.and.insert.binding (car (da-gterm.termlist equation)) (second (da-gterm.termlist equation)))
		(da-term.symbol (car (da-gterm.termlist equation))))
	       ((sat=term.check.and.insert.binding (second (da-gterm.termlist equation)) (car (da-gterm.termlist equation)))
		(da-term.symbol (second (da-gterm.termlist equation))))))))


(defun sat=rule.selector (equation)
  
  ;; Input:  a literal with the equality symbol
  ;; Effect: implements the selector rule:
  ;; Value:  an or.tree
  
  (let ((l.symbol (da-gterm.symbol (car (da-gterm.termlist equation))))
	(r.symbol (da-gterm.symbol (second (da-gterm.termlist equation)))))
    (cond ((and (da-function.is l.symbol)
		(da-function.is.selector l.symbol))
	   (sat=decompose.selector.terms (car (da-gterm.termlist equation)) 
					 (second (da-gterm.termlist equation)) 
					 equation))
	  ((and (da-function.is r.symbol)
		(da-function.is.selector r.symbol))
	   (sat=decompose.selector.terms (second (da-gterm.termlist equation)) 
					 (car (da-gterm.termlist equation)) 
					 equation)))))


(defun sat=decompose.selector.terms (term1 term2 equation)

  (let* ((selector (da-term.symbol term1))
	 (refl (member (da-function.sort selector) (da-function.domain.sorts selector)))
	 (sign (da-literal.sign equation))
	 new.lit new.term term)
    (mapcar #'(lambda (constructor)
		(setq new.lit (da-literal.create (da-sign.plus)(da-predicate.equality)
						 (list (car (da-term.termlist term1))
						       (da-term.create constructor
								       (mapcar #'(lambda (sort sel)
										   (setq term (da-term.create 
												   (da-variable.create sort)))
										   (cond ((eq sel selector) (setq new.term term)))
										   term)
									       (da-function.domain.sorts constructor)
									       (DA-SORT.SELECTORS.OF.CONSTRUCTOR constructor))))))
		(list (sat=literal.insert.depth new.lit equation)
		      (sat=literal.insert.depth (da-literal.create sign (da-predicate.equality)
								   (list (cond (new.term)
									       (refl (second (da-gterm.termlist new.lit)))
									       (t (DA-SORT.EXCEPTION.VALUE (da-term.sort term2))))
									 term2))
						equation)))
	    (da-sort.constructor.fcts (car (da-function.domain.sorts selector))))))


(defun sat=rule.function.definition (equation)

  (let ((sign (da-literal.sign equation))
	(left (car (da-literal.termlist equation)))
	(right (second (da-literal.termlist equation))))
    (cond ((and (da-function.is (da-gterm.symbol left))
		(da-function.definition (da-gterm.symbol left)))
	   (sat=rule.function.definition.1 sign left right equation))
	  ((and (da-function.is (da-gterm.symbol right))
		(da-function.definition (da-gterm.symbol right)))
	   (sat=rule.function.definition.1 sign right left equation)))))


(defun sat=rule.function.definition.1 (sign term constant.term equation)

  ;;; Input:  a sign and two terms
  ;;; Effect: all alternatives to make TERM and CONSTANT.TERM equal (resp. different) are generated,
  ;;;         where TERM is expanded according to the definition of its leading symbol
  ;;; Value:  a list of alternatives
  
  (LET ((symbol (da-term.symbol term)) alternatives result)
    (COND ((and (da-prefun.is symbol) (da-prefun.definition symbol))
	   (sat=bind.formal.parameters (da-function.formal.parameters symbol) (da-gterm.termlist term))
	   (da-gterm.def.map.with.conds 
	    (da-prefun.definition symbol)
	    #'(lambda (value conditions)
		(setq conditions (sat=insert.bindings.in.condition conditions equation))
		(cond ((neq conditions 'fail)
		       (setq result (cons (sat=literal.insert.depth 
					   (da-literal.create sign (da-predicate.equality)
							      (list constant.term
								    (sat=gterm.insert.bindings (second (da-gterm.termlist value)))))
					   equation)
					  conditions))
		       (setq alternatives (cond ((da-symbol.occurs.in.gterm symbol (second (da-gterm.termlist value)))
						 (nconc alternatives (list result)))
						(t (cons result alternatives))))))))					     
	   (sat=bindings.delete (da-function.formal.parameters symbol))
	   alternatives))))


(defun sat=rule.predicate.definition (literal)
  
  ;; Input:  a literal with predicate different from equality
  ;; Effect: all alternatives to solve LITERAL are generated
  ;; Value:  a list of alternatives
  
  (let ((sign (da-literal.sign literal))
	(symbol (da-literal.symbol literal))
	alternatives result rec)
    (cond ((and (da-prefun.is symbol) (da-prefun.definition symbol))
	   (sat=bind.formal.parameters (da-predicate.formal.parameters symbol) (da-gterm.termlist literal))
	   (da-gterm.def.map.with.conds 
	    (da-prefun.definition symbol)
	    #'(lambda (value conditions)
		(setq conditions (sat=insert.bindings.in.condition conditions literal))
		(cond ((neq conditions 'fail)
		       (cond ((da-literal.is value)
			      (cond ((eq sign (da-literal.sign value))
				     (push conditions alternatives))))
			     (t (setq rec (da-symbol.occurs.in.gterm 
					   symbol (second (da-gterm.termlist (second (da-gterm.termlist value))))))
				(setq result (sat=literal.insert.depth 
					      (sat=gterm.insert.bindings
					       (cond ((da-sign.is.positive sign)
						      (second (da-gterm.termlist (second (da-gterm.termlist value)))))
						     (T (second (da-gterm.termlist (car (da-gterm.termlist value)))))))
					      literal))
				(setq alternatives (cond (rec (nconc alternatives (list (cons result conditions))))
							 (t (cons (cons result conditions) alternatives))))))))))
	   (sat=bindings.delete (da-predicate.formal.parameters symbol))
	   alternatives))))


(defun sat=insert.bindings.in.condition (litlist literal)

  (let (result new.lit term constr)
    (cond ((every #'(lambda (lit)
		      (setq new.lit (NORM-NORMALIZE.GTERM (eg-eval (sat=gterm.insert.bindings (da-formula.negate lit)))))
		      (cond ((da-formula.is.false new.lit) nil)
			    ((da-formula.is.true new.lit) t)
			    ((and (da-literal.is new.lit)
				  (multiple-value-setq (term constr) (DA-LITERAL.IS.NORMALIZED.MATCH new.lit)))
			     (push (sat=literal.insert.depth 
				    (da-literal.create (da-sign.plus) (da-predicate.equality)
						       (list term
							     (da-term.create constr
									     (mapcar #'(lambda (sort)
											 (da-term.create (da-variable.create sort)))
										     (da-function.domain.sorts constr)))))
				    literal)
				   result))
			    (t (push (sat=literal.insert.depth new.lit literal) result))))
		  litlist)
	   result)
	  (t 'fail))))


(defun sat=rule.instantiate.vars (equation)
  
  ;; Input:  a variable, a constructor.term and a pointer to SAT*LITERAL.STACK
  ;; Effect: all occurences of VAR are substituted with an term cu*, where c is the leading symbol 
  ;;         of CONS.TERM and all ui are new variables
  ;; Value:  undefined
  
  (let ((l.symbol (da-gterm.symbol (car (da-literal.termlist equation))))
	(r.symbol (da-gterm.symbol (second (da-literal.termlist equation))))
	(sign (da-literal.sign equation)))
    (cond ((da-variable.is l.symbol)
	   (sat=instantiate.var.with.all.constructors (car (da-literal.termlist equation))
						      (second (da-literal.termlist equation))
						      sign equation))
	  ((da-variable.is r.symbol)
	   (sat=instantiate.var.with.all.constructors (second (da-literal.termlist equation))
						      (car (da-literal.termlist equation))
						      sign equation)))))



(DEFUN SAT=INSTANTIATE.VAR.WITH.ALL.CONSTRUCTORS (var TERM sign equation)
  
  ;; Input:  a variable and a TERM
  ;; Effect: all alternatives are generated, to assign an constructor term to VAR, which is different 
  ;;         from TERM
  ;; Value:  a list of alternatives
  
  (MAPCAR #'(LAMBDA (CONSTRUCTOR)
	      (let ((new.term (da-term.create constructor (mapcar #'(lambda (sort)
								      (da-term.create (da-variable.create sort)))
								  (da-function.domain.sorts constructor)))))
		(LIST (sat=literal.insert.depth (DA-LITERAL.CREATE '+ (DA-PREDICATE.EQUALITY) (LIST var new.term))
						equation)
		      (sat=literal.insert.depth (DA-LITERAL.CREATE sign (DA-PREDICATE.EQUALITY)
								   (LIST new.term TERM))
						equation))))
	  (DA-SORT.CONSTRUCTOR.FCTS (da-term.sort var))))





;;; Misc. functions
;;; ===============



(defun sat=create.function.with.new.vars (symbol)
  
;;; Input:  a constructor symbol 
;;; Effect: a term with leading symbol SYMBOL and new variables is created.
;;; Value:  the created term
  
  (cond ((da-function.is symbol)
	 (da-term.create symbol (mapcar #'(lambda (sort)
					    (da-term.create (da-variable.create sort)))
					(da-function.domain.sorts symbol))))
 	(t symbol)))


;;; =======================================
;;; Macros, etc.
;;; =======================================


(defun sat=formula.is.trivially.solvable (lit)

  (cond ((da-formula.is.false lit) 'true)
	((da-formula.is.true lit) 'false)
	((and (da-literal.is lit)
	      (da-literal.is.equation lit))
	 (let ((left (car (da-gterm.termlist lit))) (right (second (da-gterm.termlist lit))))
	   (cond ((uni-term.are.equal left right)
		  (cond ((da-sign.is.positive (da-literal.sign lit)) 'true)
			(t 'false)))
		 ((and (da-function.is (da-gterm.symbol left))
		       (da-function.is (da-gterm.symbol right))
		       (da-function.is.constructor (da-gterm.symbol left))
		       (da-function.is.constructor (da-gterm.symbol right))
		       (neq (da-gterm.symbol left) (da-gterm.symbol right)))
		  (cond ((da-sign.is.positive (da-literal.sign lit)) 'false)
			(t 'true))))))))


(defun sat=bindings.delete (symbols)

  (mapc #'(lambda (symbol) 
	    (sat=binding.delete symbol))
	symbols))


(defun sat=binding.delete (symbol)

  (remf (da-variable.attributes symbol) 'sat.binding))



(defun sat=term.binding (term)

  (let ((symbol (da-gterm.symbol term)))
    (cond ((and (null (da-term.termlist term))
		(da-variable.is symbol))
	   (getf (da-variable.attributes symbol) 'sat.binding)))))



(defun SAT=BIND.FORMAL.PARAMETERS (t1 t2)

  (mapc #'(lambda (var term) 
	    (setf (getf (da-variable.attributes var) 'sat.binding) term))
	t1 t2))


(defun sat=term.check.and.insert.binding (term binding)

  (let ((symbol (da-gterm.symbol term)))
    (cond ((and (null (da-term.termlist term))
		(da-variable.is symbol)
		(not (da-symbol.occurs.in.gterm symbol binding)))
	   (setf (getf (da-variable.attributes symbol) 'sat.binding) binding)))))



(defun sat=term.are.equal (term1 term2)
  
  ;;; input:  two terms
  ;;; value:  t, if both terms are equal under the given bindings, else nil.

  (let ((symbol1 (da-gterm.symbol term1)) (symbol2 (da-gterm.symbol term2)))
    (cond ((and (da-variable.is symbol1) (da-variable.binding symbol1))
	   (sat=term.are.equal (da-variable.binding symbol1) term2))
	  ((and (da-variable.is symbol2) (da-variable.binding symbol2)
	   (sat=term.are.equal term1 (da-variable.binding symbol2))))
	  ((and (eq symbol1 symbol2)
		(or (every #'(lambda (s1 s2)
			       (sat=term.are.equal s1 s2))
			   (da-gterm.termlist term1) (da-gterm.termlist term2))
		    (and (da-symbol.has.attribute symbol1 'commutative)
			 (every #'(lambda (s1 s2)
			       (sat=term.are.equal s1 s2))
			   (da-gterm.termlist term2) (da-gterm.termlist term1)))))))))



(defun sat=gterm.insert.bindings (term)

  ;;; Input:  a  gterm
  ;;; Effect: inserts bindings without destroying term but incorporating structure
  ;;;         sharing.
  ;;; Value:  the gterm with inserted bindings and a flag, which is T iff changes have been
  ;;;         made to term

  (let (binding)
    (cond ((setq binding (sat=term.binding term))
	   (values (sat=gterm.insert.bindings binding) t))
	  (t (multiple-value-bind (termlist changes)
		 (sat=gtermlist.insert.bindings (da-gterm.termlist term))
	       (cond ((null changes) (values term t))
		     ((da-literal.is term)
		      (values (da-literal.create (da-literal.sign term) (da-literal.symbol term) termlist) t))
		     ((da-term.is term)
		      (values (da-term.create (da-term.symbol term) termlist) t))
		     (t (values (da-gterm.create (da-term.symbol term) termlist) t))))))))


(defun sat=gtermlist.insert.bindings (termlist)

  ;;; Input:  a gtermlist
  ;;; Effect: inserts bindings without destroying termlist but incorporating structure
  ;;;         sharing.
  ;;; Value:  the gtermlist with inserted bindings and a flag, which is T iff changes have been
  ;;;         made to termlist

  (cond ((null termlist) (values nil t))
	(t (multiple-value-bind (new.termlist termlist.copied) (sat=gtermlist.insert.bindings (cdr termlist))
	     (multiple-value-bind (new.term term.copied) (sat=gterm.insert.bindings (car termlist))
	       (cond ((or termlist.copied term.copied) 
		      (values (cons new.term new.termlist) t))
		     (t termlist)))))))




(defun sat=literal.depth (literal)

  (cond ((da-literal.is literal)
	 (cond ((da-literal.is.true literal) 0)
	       ((da-literal.is.false literal) 0)
	       ((getf (da-literal.attributes literal) 'sat_depth))
	       (t  0)))
	((member (da-gterm.symbol literal) '(or and))
	 (sat=literal.depth (car (da-gterm.termlist literal))))))


(defun sat=literal.insert.depth (literal old.literal)

  (cond ((da-literal.is literal)
	 (cond ((and (not (da-literal.is.true literal)) 
		     (not (da-literal.is.false literal)))
		(setf (getf (da-literal.attributes literal) 'sat_depth)
		      (1+ (sat=literal.depth old.literal))))))
	((member (da-gterm.symbol literal) '(or and))
	 (mapc #'(lambda (gterm)
		   (sat=literal.insert.depth gterm old.literal))
	       (da-gterm.termlist literal))))
  literal)


(defun sat=gterm.replace.skolems (gterm replacement)

  (let ((symbol (da-gterm.symbol gterm)) binding)
    (cond ((member symbol '(and or eqv impl))
	   (da-gterm.create symbol 
			    (mapcar #'(lambda (subterm) 
					(sat=gterm.replace.skolems subterm replacement))
				    (da-gterm.termlist gterm))))
	  ((da-literal.is gterm)
	   (da-literal.create (da-literal.sign gterm) symbol
			      (mapcar #'(lambda (subterm) 
					(sat=gterm.replace.skolems subterm replacement))
				    (da-gterm.termlist gterm))))
	  ((da-function.is symbol)
	   (cond ((setq binding (cdr (assoc symbol replacement))) (da-term.copy binding))
		 (t (da-term.create symbol
				    (mapcar #'(lambda (subterm) 
						(sat=gterm.replace.skolems subterm replacement))
					    (da-gterm.termlist gterm)))))))))


(defun sat=beautify.result (result replacement)

  (let ((var.names '("X" "Y" "Z" "U" "V" "W")) vars)
    (setq result (mapcar #'(lambda (skolem.var)
			     (cons (car skolem.var) (sat=expand.binding (cdr skolem.var) result)))
			 replacement))
    (mapc #'(lambda (skolem.var)
	      (setq vars (union (da-gterm.variables (cdr skolem.var)) vars)))
	  result)
    (mapc #'(lambda (var)
	      (setf (da-variable.pname var) (cond ((consp var.names) (pop var.names))
						  ((numberp var.names) (format nil "X:~D" (incf var.names)))
						  (t (setq var.names 1) "X:1"))))
	  vars)
    result))


(defun sat=expand.binding (term replacement)

  (cond ((da-variable.is (da-gterm.symbol term))
	 (cond ((setq entry (assoc (da-term.symbol term) replacement))
		(sat=expand.binding (cdr entry) replacement))
	       (t term)))
	(t (da-term.create (da-term.symbol term)
			   (mapcar #'(lambda (subterm)
				       (sat=expand.binding subterm replacement))
				   (da-term.termlist term))))))