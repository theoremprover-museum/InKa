;; -*- Syntax: Common-lisp; Package: INKA; Mode: LISP -*-


(IN-PACKAGE :inka)

(DEFVAR EG*BINDING NIL)
(DEFVAR EG*NON.SYMBOLIC NIL)

(DEFVAR EG*USED.AXIOMS NIL)



(DEFUN EG-EQUAL(ARG1 ARG2 ATTR)
  ;;; Input : two terms and a list of attributes
  ;;; Value : the result of simplifying the equation \verb$ARG1$ = \verb$ARG2$
  
  (EG=EQUAL arg1 arg2 attr))


					

;;;;;==========================================================================================================
;;;;;
;;;;;
;;;;;
;;;;;==========================================================================================================

(DEFUN EG-DEFINITION.INSERT (FORMULA)

  ;;; Edited :  12.8.87 by DH
  ;;; Input  :  \verb$FORMULA$ defines a function or predicate definition 
  ;;; Effect :  a LISP function for the input definition is generated and compiled.
  ;;; Value  :  undefined.

  (MULTIPLE-VALUE-BIND (DEFINITION SYMBOL PARAMETERS) (VALUES-LIST FORMULA)
    (LET* (LISP.FCT FUNC)
      (SETQ LISP.FCT (EG=CREATE.LISP.NAME SYMBOL))
      (COND ((SETQ FUNC (CATCH 'EG*NO.FORMULA.POSSIBLE 
			  (EG=CREATE.FUNCTION.DEFINITION SYMBOL LISP.FCT PARAMETERS DEFINITION)))
	     (EVAL FUNC)
	 ;    (COMPILE LISP.FCT)
	     (SETF (DA-PREFUN.LISPFCT SYMBOL) LISP.FCT))))))


(DEFUN EG-DECL.DEFINITION.INSERT (PREFUN)

  ;;; Input:   a function or predicate-symbol
  ;;; Effect:  creates a dummy-lisp-function which evaluates to its call.
  ;;; Value:   undefined.

  (LET ((LISP.FCT (EG=CREATE.LISP.NAME PREFUN)) FUNC)
       (COND ((SETQ FUNC (CATCH 'EG*NO.FORMULA.POSSIBLE 
				(EG=DECL.DEFINITION.CREATE PREFUN LISP.FCT)))
	      (EVAL FUNC)
	;      (COMPILE LISP.FCT)
	      (SETF (DA-PREFUN.LISPFCT PREFUN) LISP.FCT)))))


(DEFUN EG=DECL.DEFINITION.CREATE (PREFUN LISP.FCT)
  
  ;;; Input:   a function or predicate-symbol and the name of its lisp-function
  ;;; Effect:  creates a dummy-lisp-function which evaluates to its call.
  ;;; Value:   the created lisp-function
  
  (LET* ((PARAMETERS (MAPCAR #'(LAMBDA (X) (DA-VARIABLE.CREATE X)) (DA-PREFUN.DOMAIN.SORTS PREFUN)))
	 (SUBSTITUTION (ACONS PREFUN LISP.FCT (EG=RENAME.PARAMETERS PARAMETERS))))
       `(DEFUN ,LISP.FCT
	  ,(COND ((DA-FUNCTION.IS PREFUN)
		  (MAPCAR #'CDR (CDR SUBSTITUTION)))
		 (T (NCONC (MAPCAR #'CDR (CDR SUBSTITUTION)) (LIST '&OPTIONAL 'ATTRIBUTES))))
	  (COND (EG*NON.SYMBOLIC NIL)
		(T ,(COND ((DA-FUNCTION.IS PREFUN)
			   `(DA-TERM.CREATE (QUOTE ,PREFUN) (LIST ,@(SUBLIS SUBSTITUTION PARAMETERS))))
			  (T `(DA-LITERAL.CREATE '+ (QUOTE ,PREFUN)
						 (LIST ,@(SUBLIS SUBSTITUTION PARAMETERS))
						 ATTRIBUTES))))))))


(DEFUN EG-INSERT.SORT (SORT)

  ;;; Input :  a sort
  ;;; Effect:  creates LISP functions for all selector and index-functions of \verb$SORT$ and adds them
  ;;;          into the database.
  ;;; Value:   undefined.

  (LET (COUNTER FUNC LISP.FCT)
    (MAPC #'(LAMBDA (CONSTRUCTOR SELECTOR.FCTS)
	      (SETQ COUNTER 0)
	      (MAPC #'(LAMBDA (SELECTOR)
			(INCF COUNTER)
			(SETQ LISP.FCT (EG=CREATE.LISP.NAME SELECTOR))
			(COND ((SETQ FUNC (CATCH 'EG*NO.FORMULA.POSSIBLE 
					    (EG=CREATE.SELECTOR.DEFINITION LISP.FCT CONSTRUCTOR SELECTOR COUNTER)))
			       (EVAL FUNC)
			  ;     (COMPILE LISP.FCT)
			       (SETF (DA-PREFUN.LISPFCT SELECTOR) LISP.FCT))))
		    SELECTOR.FCTS))
	  (DA-SORT.CONSTRUCTOR.FCTS SORT)
	  (DA-SORT.SELECTOR.FCTS SORT))))


(DEFUN EG=CREATE.SELECTOR.DEFINITION (LISP.FCT CONSTRUCTOR SELECTOR POS)
  `(DEFUN ,LISP.FCT (X)
     (COND ((NULL X) NIL)
	   (,(EG=CREATE.SELECTOR.CASES CONSTRUCTOR SELECTOR POS))
	   (T (DA-TERM.CREATE (QUOTE ,SELECTOR) (LIST X))))))


(DEFUN EG=CREATE.SELECTOR.CASES (CONSTRUCTOR SELECTOR POS)
  `(COND ((EQ (DA-TERM.SYMBOL X) (QUOTE ,CONSTRUCTOR)) (EG=NTH ,POS X))
	 ((OR (NEQ (DA-TERM.SORT X) (QUOTE ,(DA-FUNCTION.SORT CONSTRUCTOR)))
	      (DA-SYMBOL.HAS.ATTRIBUTE (DA-TERM.SYMBOL X) 'STRUCTURE))
	  (QUOTE ,(DA-SORT.EXCEPTION.VALUE (DA-FUNCTION.SORT SELECTOR))))))


(DEFUN EG=CREATE.FUNCTION.DEFINITION (SYMBOL LISP.FCT PARAMETERS DEFINITION)

  ;;; Edited :  10.3.88
  ;;; Input  :  SYMBOL - a function (as decribed in DT) with formal parameters: PARAMETERS, 
  ;;;           LISP.FCT - name of the lisp function denoting SYMBOL.
  ;;;           IF.THEN.CASES - list of all if-then-cases as described in EXP.
  ;;; Effect :  computes an s-expression, which denotes a lisp function definition of SYMBOL
  ;;; Value  :  the computed definition.

  (LET ((SUBSTITUTION (ACONS SYMBOL LISP.FCT (EG=RENAME.PARAMETERS PARAMETERS))))
    `(DEFUN ,LISP.FCT ,(COND ((DA-FUNCTION.IS SYMBOL)
			      (MAPCAR #'CDR (CDR SUBSTITUTION)))
			     (T (NCONC (MAPCAR #'CDR (CDR SUBSTITUTION)) (LIST '&OPTIONAL 'ATTRIBUTES))))
       (LET ((USED.AXIOMS EG*USED.AXIOMS))
	 (COND ((AND EG*NON.SYMBOLIC (NOT (AND ,@(MAPCAR #'CDR (CDR SUBSTITUTION))))) NIL)
	       (,(EG=CREATE.FUNCTION.CASES (EG=MINIMIZE.DEFINITION SYMBOL DEFINITION) SUBSTITUTION SYMBOL))
	       (EG*NON.SYMBOLIC NIL)
	       (T (SETQ EG*USED.AXIOMS USED.AXIOMS)
		  ,(COND ((DA-FUNCTION.IS SYMBOL)
			  `(DA-TERM.CREATE (QUOTE ,SYMBOL) (LIST ,@(SUBLIS SUBSTITUTION PARAMETERS))))
			 (T `(DA-LITERAL.CREATE '+ (QUOTE ,SYMBOL)
						(LIST ,@(SUBLIS SUBSTITUTION PARAMETERS))
						ATTRIBUTES)))))))))


(DEFUN EG=CREATE.FUNCTION.CASES (DEFINITION SUBSTITUTION SYMBOL)
  (COND ((DA-GTERM.DEF.IS.VALUE DEFINITION)
	 `(PROGN (PUSH (QUOTE ,SYMBOL) EG*USED.AXIOMS)
		 ,(COND ((DA-TERM.IS DEFINITION) (EG=TRANSFER.TERM DEFINITION SUBSTITUTION))
			(T (EG=TRANSFER.FORMULA DEFINITION SUBSTITUTION)))))
	(T (CONS 'COND (MAPCAR #'(LAMBDA (DEF.TERM)
				   `((LET ((EG*NON.SYMBOLIC T)) 
				     ,(EG=TRANSFER.CONDITIONS (DA-GTERM.DEF.CONDITION DEF.TERM) SUBSTITUTION))
				     ,(EG=CREATE.FUNCTION.CASES (DA-GTERM.DEF.VALUE DEF.TERM) SUBSTITUTION SYMBOL)))
			       (DA-GTERM.TERMLIST DEFINITION))))))	       


(DEFUN EG=MINIMIZE.DEFINITION (SYMBOL DEFINITION)

  ;;; Input:  a predicate or function symbol and its definition
  ;;; Effect: tries to simplify the definition according to some simplification rules
  ;;;         (see EG=MINIMIZE.BY.AND.OR.SIMPLIFICATION and EG=MINIMIZE.BY.TRUE.FALSE.VALUE for details)
  ;;; Value:  the modified defintion.

  (COND ((DA-GTERM.DEF.IS.VALUE DEFINITION) DEFINITION)
	(T (COND ((EG=MINIMIZE.BY.AND.OR.SIMPLIFICATION DEFINITION))
		 ((AND (DA-PREDICATE.IS SYMBOL) 
		       (EG=MINIMIZE.BY.TRUE.FALSE.VALUE DEFINITION)))
		 (T DEFINITION)))))


(DEFUN EG=MINIMIZE.BY.AND.OR.SIMPLIFICATION (DEFINITION)

  ;;; Input:  a predicate or function symbol and its definition
  ;;; Effect: tries to a simplify its definition by the following rule:
  ;;;         let definition be a tree with n cases there n-1 cases return the value r and
  ;;;         the other case (with conditions C) splits up into m subcases. For each subcase
  ;;;         - which returns the value r - the govering condition C can be neglected, since
  ;;;         (NOT C) OR (C AND D) is implied by (NOT C) OR D.
  ;;; Value:  the simplified definition iff there is one, else nil.
  
  (LET (SUB.CASE STANDARD.CASE CASES.WITH.STANDARD.VALUE)
    (COND ((AND (NULL (GETF (DA-GTERM.ATTRIBUTES DEFINITION) 'UNSPEC.CASES))
		(EVERY #'(LAMBDA (DEF.TERM)
			   (COND ((DA-GTERM.DEF.IS.VALUE (DA-GTERM.DEF.VALUE DEF.TERM))
				  (COND ((NULL STANDARD.CASE) (SETQ STANDARD.CASE DEF.TERM))))
				 ((NULL SUB.CASE)
				  (SETQ SUB.CASE DEF.TERM))))
		       (DA-GTERM.TERMLIST DEFINITION)))
	   (COND ((AND STANDARD.CASE SUB.CASE)
		  (MAPC #'(LAMBDA (DEF.TERM)
			    (COND ((AND (DA-GTERM.DEF.IS.VALUE (DA-GTERM.DEF.VALUE DEF.TERM))
					(UNI-GTERM.ARE.EQUAL (DA-GTERM.DEF.VALUE DEF.TERM)
							     (DA-GTERM.DEF.VALUE STANDARD.CASE)))
				   (PUSH DEF.TERM CASES.WITH.STANDARD.VALUE))))
			(DA-GTERM.TERMLIST (DA-GTERM.DEF.VALUE SUB.CASE)))
		  (COND (CASES.WITH.STANDARD.VALUE
			 (DA-GTERM.DEFINITION.CREATE
			  (APPEND (REMOVE SUB.CASE (DA-GTERM.TERMLIST DEFINITION))
				  CASES.WITH.STANDARD.VALUE
				  (MAPCAR #'(LAMBDA (DEF.TERM)
					      (DA-GTERM.DEF.CREATE (DA-GTERM.DEF.VALUE DEF.TERM)
								   (APPEND (DA-GTERM.DEF.CONDITION SUB.CASE)
									   (DA-GTERM.DEF.CONDITION DEF.TERM))))
					  (SET-DIFFERENCE (DA-GTERM.TERMLIST (DA-GTERM.DEF.VALUE SUB.CASE))
							  CASES.WITH.STANDARD.VALUE))))))))))))



(DEFUN EG=MINIMIZE.BY.TRUE.FALSE.VALUE (DEFINITION)

  ;;; Input:  a definition of a predicate symbol
  ;;; Effect: simplifies the given definition - if each case of definition is a leaf of the case analysis -
  ;;;         according to the following rules:
  ;;;         - if each case returns either true or false then the conjunction of all negated conditions of
  ;;;           the cases which return false.
  ;;;         - if there is one and only one case which returns a value non-equal to true or false
  ;;;             - and all other cases return true, then the disjunction of value and negated conjunction
  ;;;               of this case
  ;;;             - and all other cases return false, then the conjunction of the negated conjunction of all
  ;;;               cases which return false and of the disjunction of value and negated conjunction of
  ;;;               the case mentioned above.
  ;;; Value:  the simplified definition, iff possible, else nil

  (LET (TRUE.DEF.TERMS FALSE.DEF.TERMS OTHER.DEF.TERM)
    (COND ((AND (NOT (DA-GTERM.DEF.HOLDS.TERMINATION DEFINITION))
		(NULL (GETF (DA-GTERM.ATTRIBUTES DEFINITION) 'UNSPEC.CASES))
		(EVERY #'(LAMBDA (DEF.TERM)
			   (COND ((DA-GTERM.DEF.IS.VALUE (DA-GTERM.DEF.VALUE DEF.TERM))
				  (COND ((DA-FORMULA.IS.TRUE (DA-GTERM.DEF.VALUE DEF.TERM))
					 (PUSH DEF.TERM TRUE.DEF.TERMS))
					((DA-FORMULA.IS.FALSE (DA-GTERM.DEF.VALUE DEF.TERM))
					 (PUSH DEF.TERM FALSE.DEF.TERMS))
					((NULL OTHER.DEF.TERM)
					 (SETQ OTHER.DEF.TERM DEF.TERM))))))
		       (DA-GTERM.TERMLIST DEFINITION)))
	   (COND ((AND (NULL FALSE.DEF.TERMS) TRUE.DEF.TERMS OTHER.DEF.TERM)
		  (DA-GTERM.DEF.VALUE.CREATE 
		    (DA-FORMULA.JUNCTION.CLOSURE 'OR (CONS (DA-GTERM.DEF.VALUE OTHER.DEF.TERM)
							   (DA-GTERM.DEF.CONDITION OTHER.DEF.TERM)))))
		 ((AND (OR (NULL TRUE.DEF.TERMS) (NULL OTHER.DEF.TERM)) FALSE.DEF.TERMS)
		  (DA-GTERM.DEF.VALUE.CREATE
		    (DA-FORMULA.JUNCTION.CLOSURE 
		      'AND (NCONC (COND (OTHER.DEF.TERM 
					 (LIST (DA-FORMULA.JUNCTION.CLOSURE 
						 'OR (CONS (DA-GTERM.DEF.VALUE OTHER.DEF.TERM)
							   (DA-GTERM.DEF.CONDITION OTHER.DEF.TERM))))))
				  (MAPCAR #'(LAMBDA (DEF.TERM)
					      (DA-FORMULA.JUNCTION.CLOSURE 'OR
									   (DA-GTERM.DEF.CONDITION DEF.TERM)))
					  FALSE.DEF.TERMS))))))))))


(DEFUN EG=TRANSFER.CONDITIONS (CONDITION SUBSTITUTION)
  (COND (CONDITION
	 `(LET ((USED.AXIOMS EG*USED.AXIOMS))
	    (COND ((AND ,@(MAPCAR #'(LAMBDA (LIT)
				      (COND ((DA-LITERAL.IS.MATCH LIT)
					     (EG=TRANSFER.MATCH.LITERAL LIT SUBSTITUTION))
					    (T `(EG=LITERAL.IS.TRUE ,(EG=TRANSFER.FORMULA 
								      (DA-FORMULA.NEGATE (DA-GTERM.COPY LIT))
								      SUBSTITUTION NIL)))))
				  CONDITION)))
		  (T (SETQ EG*USED.AXIOMS USED.AXIOMS)
		     NIL))))
	(T T)))


(DEFUN EG=TRANSFER.MATCH.LITERAL (LITERAL SUBSTITUTION)

  ;;; Input  :  a match literal and a substitution list for all variables.
  ;;; Effect :  computes lisp code for LITERAL
  ;;; Value  :  a multiple value: the generated code for LITERAL and the updated substitution list.

  (LET ((TERMLIST (DA-LITERAL.TERMLIST LITERAL)) TERM)
    (SETQ TERM (EG=TRANSFER.TERM (CAR TERMLIST) SUBSTITUTION))
    (COND ((DA-SYMBOL.HAS.ATTRIBUTE (DA-TERM.SYMBOL (SECOND TERMLIST)) 'STRUCTURE)
	   `(EQ (DA-TERM.SYMBOL ,TERM) (QUOTE ,(DA-TERM.SYMBOL (SECOND TERMLIST)))))
	  (T `(EQ (QUOTE ,(DA-TERM.SORT (SECOND TERMLIST))) (DA-TERM.SORT ,TERM))))))


(DEFUN EG=TRANSFER.FORMULA (FORMULA SUBSTITUTION &OPTIONAL (add.attributes? T))
  
  ;;; Input  :  a prefix formula , an assoc-list denoting a variable-substitution and two parameters of all lisp functions.
  ;;; Effect :  computes a lisp sexpression, which computes the value of the given formula.
  ;;; Value  :  the computed sexpression.
  
  (COND ((DA-TERM.IS FORMULA) (EG=TRANSFER.TERM FORMULA SUBSTITUTION))
	((DA-LITERAL.IS FORMULA) (EG=TRANSFER.LITERAL FORMULA SUBSTITUTION add.attributes?))
	(T  (CONS (CASE (DA-GTERM.SYMBOL FORMULA)
		    (AND 'EG=AND) (OR 'EG=OR) (IMPL 'EG=IMPL) (EQV 'EG=EQV) (NOT 'EG=NOT) (ALL 'EG=ALL) (EX 'EG=EX))
		  (MAPCAR #'(LAMBDA (ARG)
			      (EG=TRANSFER.FORMULA ARG SUBSTITUTION add.attributes?))
			  (DA-GTERM.TERMLIST FORMULA))))))


(DEFUN EG=TRANSFER.LITERAL (LITERAL SUBSTITUTION add.attributes?)

  ;;; Input  :  a literal, an assoc-list denoting a variable-substitution and two parameters of all lisp functions.
  ;;; Effect :  computes a lisp sexpression, which computes the value of the given literal.
  ;;; Value  :  the computed sexpression.

  (LET ((SYMBOL (COND ((CASSOC (DA-LITERAL.SYMBOL LITERAL) SUBSTITUTION))
		      ((NULL (DA-PREDICATE.LISPFCT (DA-LITERAL.SYMBOL LITERAL))) NIL)
		      (T (EG=TRANSFER.SYMBOL (DA-LITERAL.SYMBOL LITERAL)))))
	VALUE)
    (COND ((OR (EG=LITERAL.IS.TRUE LITERAL) (EG=LITERAL.IS.FALSE LITERAL)) LITERAL)
	  (T (SETQ VALUE (COND (SYMBOL
				(CONS SYMBOL
				      (MAPCAR #'(LAMBDA (SUBTERM) (EG=TRANSFER.TERM SUBTERM SUBSTITUTION))
					      (DA-LITERAL.TERMLIST LITERAL))))
			       (T `(DA-LITERAL.CREATE
				    (QUOTE ,(DA-LITERAL.SYMBOL LITERAL))
				    (LIST ,@(MAPCAR #'(LAMBDA (SUBTERM) 
							(EG=TRANSFER.TERM SUBTERM SUBSTITUTION))
						    (DA-LITERAL.TERMLIST LITERAL)))))))
	     (COND (ADD.ATTRIBUTES? (SETQ VALUE (NCONC1 VALUE 'ATTRIBUTES))))
	     (COND ((DA-SIGN.IS.NEGATIVE (DA-LITERAL.SIGN LITERAL))
		     (SETQ VALUE `(EG=NOT ,VALUE))))
	     VALUE))))


(DEFUN EG=TRANSFER.TERM (TERM SUBSTITUTION)

  ;;; Input  :  a term, an assoc-list denoting a variable-substitution and two parameters of all lisp functions.
  ;;; Effect :  computes a lisp sexpression, which computes the value of the given term.
  ;;; Value  :  the computed sexpression.

  (LET ((SYMBOL (DA-TERM.SYMBOL TERM)))
    (COND ((DA-VARIABLE.IS SYMBOL)
	   (COND ((CDR (ASSOC SYMBOL SUBSTITUTION)))
		 ((EG=TRANSFER.TERM (DA-VARIABLE.BINDING SYMBOL) SUBSTITUTION))
		 (T `(QUOTE ,TERM))))
	  ((DA-FUNCTION.IS SYMBOL)
	   (COND ((AND (DA-TERM.TERMLIST TERM) 
		       (NOT (EQL (LENGTH (DA-TERM.TERMLIST TERM)) (DA-FUNCTION.ARITY SYMBOL))))
		  (SETQ TERM (EG=CREATE.NORMAL.FORM SYMBOL (DA-TERM.TERMLIST TERM)))))
	   (COND ((AND (DA-PREFUN.IS SYMBOL) (NULL (DA-PREFUN.LISPFCT SYMBOL)) (NULL (CASSOC SYMBOL SUBSTITUTION)))
		  `(DA-TERM.CREATE (QUOTE ,SYMBOL)
				   (LIST ,@(MAPCAR #'(LAMBDA (SUBTERM) 
						       (EG=TRANSFER.TERM SUBTERM SUBSTITUTION))
						   (DA-TERM.TERMLIST TERM)))))
		 (T (CONS (COND ((CASSOC SYMBOL SUBSTITUTION))
				(T (EG=TRANSFER.SYMBOL SYMBOL)))
			  (MAPCAR #'(LAMBDA (SUBTERM) 
				      (EG=TRANSFER.TERM SUBTERM SUBSTITUTION))
				  (DA-TERM.TERMLIST TERM)))))))))


(DEFUN EG=TRANSFER.SYMBOL (SYMBOL)

  ;;; Input  :  a function or predicate symbol.
  ;;; Value  :  the corresponding lisp function.

  (COND	((DA-FUNCTION.IS SYMBOL)
	 (COND ((DA-FUNCTION.LISPFCT SYMBOL))
	       (T (THROW 'EG*NO.FORMULA.POSSIBLE NIL))))	 
	((DA-PREDICATE.IS SYMBOL)
	 (COND ((DA-PREDICATE.IS.EQUALITY SYMBOL) 'EG=EQUAL)
	       ((DA-PREDICATE.IS.FALSE SYMBOL) `(QUOTE ,(DA-LITERAL.FALSE)))
	       ((DA-PREDICATE.IS.TRUE SYMBOL) `(QUOTE ,(DA-LITERAL.TRUE)))
	       ((DA-PREDICATE.LISPFCT SYMBOL))
	       (T (THROW 'EG*NO.FORMULA.POSSIBLE NIL))))
	(T (CASE SYMBOL
	     (NOT 'EG=NOT)
	     (AND 'EG=AND) 
	     (OR 'EG=OR) 
	     (IMPL 'EG=IMPL)
	     (EQV 'EG=EQV) 
	     (ALL 'EG=ALL) 
	     (EX 'EG=EX)))))



(DEFUN EG=CREATE.NORMAL.FORM (SYMBOL TERMLIST)
  (LET ((NEW.TERM (CAR TERMLIST)))
    (WHILE (CDR TERMLIST)
      (SETQ TERMLIST (CDR TERMLIST))
      (SETQ NEW.TERM (DA-TERM.CREATE SYMBOL (LIST NEW.TERM (CAR TERMLIST)))))
    NEW.TERM))


;;;;;=========================================================================================================================
;;;;;
;;;;;  Definition of the junctors AND, OR, IMPL, EQV, NOT and NTH.
;;;;;
;;;;;=========================================================================================================================


(DEFUN EG=COUNT (TERM SORT)
  (LET ((S.SIZE 0))
    (COND ((AND (CONSP TERM)
		(EQ (DA-FUNCTION.SORT (CAR TERM)) SORT)
		(MEMBER 'SORT.REFLEXIVE (DA-FUNCTION.ATTRIBUTES (CAR TERM))))
	   (MAPC #'(LAMBDA (SUBTERM) (INCF S.SIZE (EG=COUNT SUBTERM SORT))) (CDR TERM))
	   (INCF S.SIZE)))
    S.SIZE))
		

(DEFUN EG=NTH (POS SEXPR)
  (COND ((DA-TERM.TERMLIST SEXPR) (NTH (1- POS) (DA-TERM.TERMLIST SEXPR)))
	(T SEXPR)))
 

(DEFUN EG=AND (&rest ARGS)
  (COND ((SOME #'(LAMBDA (ARG) (COND ((DA-FORMULA.IS.FALSE ARG) ARG))) ARGS))
	(T (LET ((RESULT (REMOVE-IF #'(LAMBDA (ARG) (DA-FORMULA.IS.TRUE ARG)) ARGS)))
	     (COND ((NULL RESULT) (DA-LITERAL.TRUE))
		   (EG*NON.SYMBOLIC NIL)
		   ((NULL (CDR RESULT)) (CAR RESULT))
		   (T (DA-GTERM.CREATE 'AND RESULT)))))))


(DEFUN EG=OR (&rest ARGS)
  (COND ((SOME #'(LAMBDA (ARG) (COND ((DA-FORMULA.IS.TRUE ARG) ARG))) ARGS))
	(T (LET ((RESULT (REMOVE-IF #'(LAMBDA (ARG) (DA-FORMULA.IS.FALSE ARG)) ARGS)))
	     (COND ((NULL RESULT) (DA-LITERAL.FALSE))
		   (EG*NON.SYMBOLIC NIL)
		   ((NULL (CDR RESULT)) (CAR RESULT))
		   (T (DA-GTERM.CREATE 'OR RESULT)))))))



(DEFUN EG=EQV (ARG1 ARG2)
  (COND ((AND (NULL ARG1) (NULL ARG2)) NIL)
	((EQUAL ARG1 ARG2) (DA-LITERAL.TRUE))
	(EG*NON.SYMBOLIC NIL)
	(T (DA-FORMULA.CREATE 'EQV (LIST ARG1 ARG2)))))


(DEFUN EG=IMPL (ARG1 ARG2)
  (COND ((EG=LITERAL.IS.FALSE ARG1) (DA-LITERAL.TRUE))
	((EG=LITERAL.IS.TRUE ARG1) ARG2)
	((EG=LITERAL.IS.FALSE ARG2) (EG=NOT ARG1))
	((EG=LITERAL.IS.TRUE ARG2) (DA-LITERAL.TRUE))
	(EG*NON.SYMBOLIC NIL)
	(T (DA-FORMULA.CREATE 'IMPL (LIST ARG1 ARG2)))))


(DEFUN EG=NOT (ARG &OPTIONAL IGNORE)
  (declare (ignore ignore))
  (COND ((EG=LITERAL.IS.TRUE ARG) (DA-LITERAL.FALSE))
	((EG=LITERAL.IS.FALSE ARG) (DA-LITERAL.TRUE))
	(EG*NON.SYMBOLIC NIL)
	((DA-LITERAL.IS ARG) (DA-LITERAL.NEGATE ARG))
	(T (DA-FORMULA.NEGATE ARG))))


(DEFUN EG=ALL (VAR ARG)
  (COND ((EG=LITERAL.IS.FALSE ARG) (DA-LITERAL.FALSE))
	((EG=LITERAL.IS.TRUE ARG) (DA-LITERAL.TRUE))
	(EG*NON.SYMBOLIC NIL)
	(T (DA-FORMULA.CREATE 'ALL (LIST VAR ARG)))))


(DEFUN EG=EX (VAR ARG)
  (COND ((EG=LITERAL.IS.FALSE ARG) (DA-LITERAL.FALSE))
	((EG=LITERAL.IS.TRUE ARG) (DA-LITERAL.TRUE))
	(EG*NON.SYMBOLIC NIL)
	(T (DA-FORMULA.CREATE 'EX (LIST VAR ARG)))))



(DEFUN EG=EQUAL (ARG1 ARG2 &OPTIONAL ATTRIBUTES)
  (COND ((OR (NULL ARG1) (NULL ARG2)) NIL)
	((AND (NEQ (DA-TERM.SORT ARG1) (DA-TERM.SORT ARG2))
	      (EVERY #'DA-SORT.IS.FREE.STRUCTURE
		    (REMOVE (DP-SORT.TOP.LEVEL.SORT)
			    (DA-SORT.COMMON.SUPERSORTS (DA-TERM.SORT ARG1) (DA-TERM.SORT ARG2)))))
	 (DA-LITERAL.FALSE))
	((DA-SORT.COMMON.SUPERSORTS (DA-TERM.SORT ARG1) (DA-TERM.SORT ARG2))
	 (COND ((AND (DP-SORT.SET (DA-TERM.SORT ARG1))
		     (DP-SORT.SET (DA-TERM.SORT ARG2))
		     (EQ (DA-TERM.SORT ARG1) (DA-TERM.SORT ARG2)))
		(EG=SET.EQUAL ARG1 ARG2 ATTRIBUTES))
	       ((AND (DP-SORT.ARRAY (DA-TERM.SORT ARG1))
		     (DP-SORT.ARRAY (DA-TERM.SORT ARG2))
		     (EQ (DA-TERM.SORT ARG1) (DA-TERM.SORT ARG2)))
		(EG=ARRAY.EQUAL ARG1 ARG2 ATTRIBUTES))
	       ((EG=INVALID.SORTS ARG1 ARG2)
		(DA-LITERAL.FALSE))
	       ((EQ (DA-TERM.SYMBOL ARG1) (DA-TERM.SYMBOL ARG2))
		(LET ((INJECT (AND (DA-FUNCTION.IS (DA-TERM.SYMBOL ARG1))
				   (EQL (LENGTH (DA-SYMBOL.HAS.ATTRIBUTE (DA-TERM.SYMBOL ARG1) 'INJECTIVE))
					(DA-FUNCTION.ARITY (DA-TERM.SYMBOL ARG1)))))
		      RESULT FINAL.RESULT)
		  (COND ((EVERY #'(LAMBDA (SUB1 SUB2)
				    (SETQ RESULT (EG=EQUAL SUB1 SUB2 ATTRIBUTES))
				    (COND ((AND INJECT (EG=LITERAL.IS.FALSE RESULT))						
					   (SETQ FINAL.RESULT (DA-LITERAL.FALSE))
					   NIL)
					  ((EG=LITERAL.IS.TRUE RESULT))
					  (EG*NON.SYMBOLIC (SETQ FINAL.RESULT NIL))
					  (INJECT (PUSH RESULT FINAL.RESULT))
					  (T (SETQ FINAL.RESULT (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DA-PREDICATE.EQUALITY)
										   (LIST ARG1 ARG2) ATTRIBUTES))
					     NIL)))
				(DA-TERM.TERMLIST ARG1) (DA-TERM.TERMLIST ARG2))
			 (DA-FORMULA.JUNCTION.CLOSURE 'AND FINAL.RESULT))
			(T FINAL.RESULT))))
	       ((AND (EQ (DA-TERM.SORT ARG1) (DA-TERM.SORT ARG2))
		     (DA-SORT.IS.FREE.STRUCTURE (DA-TERM.SORT ARG1))
		     (OR (AND (DA-FUNCTION.IS (DA-TERM.SYMBOL ARG2))
			      (DA-FUNCTION.IS.CONSTRUCTOR (DA-TERM.SYMBOL ARG2))
			      (DA-FUNCTION.IS (DA-TERM.SYMBOL ARG1))
			      (DA-FUNCTION.IS.SELECTOR (DA-TERM.SYMBOL ARG1))
			      (EQ (DA-TERM.SYMBOL ARG2) (DA-SORT.CONSTRUCTOR.OF.SELECTOR (DA-TERM.SYMBOL ARG1)))
			      (EG=TERM.OCCURS.IN.TERM (FIRST (DA-TERM.TERMLIST ARG1)) ARG2))
			 (AND (DA-FUNCTION.IS (DA-TERM.SYMBOL ARG2))
			      (DA-FUNCTION.IS (DA-TERM.SYMBOL ARG1))
			      (DA-FUNCTION.IS.CONSTRUCTOR (DA-TERM.SYMBOL ARG1))
			      (DA-FUNCTION.IS.SELECTOR (DA-TERM.SYMBOL ARG2))
			      (EQ (DA-TERM.SYMBOL ARG1) (DA-SORT.CONSTRUCTOR.OF.SELECTOR (DA-TERM.SYMBOL ARG2)))
			      (EG=TERM.OCCURS.IN.TERM (FIRST (DA-TERM.TERMLIST ARG2)) ARG1))
			 (EG=TERM.OCCURS.IN.TERM ARG1 ARG2)
			 (EG=TERM.OCCURS.IN.TERM ARG2 ARG1)))
		(DA-LITERAL.FALSE))
	       ((AND (DA-FUNCTION.IS (DA-TERM.SYMBOL ARG2))
		     (DA-FUNCTION.IS (DA-TERM.SYMBOL ARG1))
		     (DA-FUNCTION.IS.CONSTRUCTOR (DA-TERM.SYMBOL ARG1))
		     (DA-FUNCTION.IS.CONSTRUCTOR (DA-TERM.SYMBOL ARG2))
		     (member 'DISJUNCT.RANGE (da-sort.attributes (da-term.sort arg1))))
		(DA-LITERAL.FALSE))
	       (EG*NON.SYMBOLIC NIL)
	       (T (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DA-PREDICATE.EQUALITY)
				     (LIST ARG1 ARG2) ATTRIBUTES))))
	(EG*NON.SYMBOLIC NIL)
	(T (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DA-PREDICATE.EQUALITY)
			      (LIST ARG1 ARG2) ATTRIBUTES))))


(DEFUN EG=INVALID.SORTS (ARG1 ARG2)
  (LET ((S1 (DA-TERM.SYMBOL ARG1)) (S2 (DA-TERM.SYMBOL ARG2)))
    (COND ((NEQ S1 S2)
	   (COND ((AND (DA-FUNCTION.IS S1)
		       (DA-FUNCTION.IS.CONSTRUCTOR S1)
		       (DA-FUNCTION.HAS.DISJUNCT.RANGE S1))		       
		  (OR (AND (DA-FUNCTION.IS S2) (DA-FUNCTION.IS.CONSTRUCTOR S2))
		      (AND (NEQ (DA-TERM.SORT ARG1) (DA-TERM.SORT ARG2))
			   (NOT (DA-SORT.IS.SUBSORT (DA-TERM.SORT ARG1) (DA-TERM.SORT ARG2))))))
		 ((AND (DA-FUNCTION.IS S2)
		       (DA-FUNCTION.IS.CONSTRUCTOR S2)
		       (DA-FUNCTION.HAS.DISJUNCT.RANGE S2))
		  (AND (NEQ (DA-TERM.SORT ARG1) (DA-TERM.SORT ARG2))
		       (NOT (DA-SORT.IS.SUBSORT (DA-TERM.SORT ARG2) (DA-TERM.SORT ARG1))))))))))


 


(DEFUN EG=TERM.OCCURS.IN.TERM (ARG1 ARG2)
  (and arg1 arg2
       (OR (UNI-TERM.ARE.EQUAL ARG1 ARG2)
	   (AND (DA-SYMBOL.HAS.ATTRIBUTE (DA-TERM.SYMBOL ARG2) 'STRUCTURE)
		(FIND-IF #'(LAMBDA (S.ARG) (EG=TERM.OCCURS.IN.TERM ARG1 S.ARG))
			 (DA-TERM.TERMLIST ARG2))))))

;;;;;=========================================================================================================================
;;;;;
;;;;;  Misc. functions
;;;;;
;;;;;=========================================================================================================================

(DEFUN EG=RENAME.PARAMETERS (PARAMETERS)

  (let (subst (no -1))
    (while parameters
      (setq subst (nconc subst (eg=rename.parameters.1 (subseq parameters 0 (min 6 (length parameters))) (incf no))))
      (setq parameters (nthcdr 6 parameters)))
    subst))


(defun eg=rename.parameters.1 (parameters no)

  (MAPCAR #'(LAMBDA (VAR TERM) (CONS VAR (INTERN (FORMAT NIL "~A~D" term NO)))) PARAMETERS '(X Y Z U V W)))


(DEFUN EG=CREATE.LISP.NAME (SYMBOL)

  ;;; Input:   a function or predicate
  ;;; Effect:  creates a list atom used to name the corresponding lisp-function
  ;;; Value:   the generated atom
  
  (LET ((NAME (INTERN (FORMAT NIL "INKA-~A" (STRING-UPCASE (DA-PNAME SYMBOL))))))
   (COND ((FBOUNDP NAME)
	  (LET ((COUNTER 0))
	    (WHILE (FBOUNDP (SETQ NAME (INTERN (FORMAT NIL "INKA-~A-~D" (STRING-UPCASE (DA-PNAME SYMBOL)) COUNTER))))
		   (INCF COUNTER)))))
   NAME))


(DEFUN EG-EVAL (FORM &OPTIONAL ASSUMPTIONS)
  ;;; Input : either a term, a literal or a formula and a list of literals
  ;;; Value : result of applying Symbolic Evaluation to \verb$FORM$ under the assumptions \verb$ASSUMPTIONS$

  (SETQ EG*NON.SYMBOLIC NIL EG*USED.AXIOMS NIL)
  (COND ((DA-LITERAL.IS FORM) (VALUES (eg=simplify (EG=EVAL.LITERAL FORM) ASSUMPTIONS) EG*USED.AXIOMS))
	((DA-TERM.IS FORM) (VALUES (EG=EVAL.TERM FORM) EG*USED.AXIOMS))
	(t  (VALUES (eg=simplify (EG=EVAL.FORMULA FORM) ASSUMPTIONS) EG*USED.AXIOMS))))


(DEFUN EG=EVAL.TERM (TERM &OPTIONAL ASSIGNMENT)
  (COND ((NOT (DA-TERM.IS TERM)) NIL)
	((NULL (DA-TERM.TERMLIST TERM)) (COND ((CASSOC (DA-TERM.SYMBOL TERM) ASSIGNMENT)) (T TERM)))
	((DA-FUNCTION.IS.CONSTRUCTOR (DA-TERM.SYMBOL TERM))
	 (COND ((DP-SORT.SET (DA-TERM.SORT TERM))
		(EG=EVAL.SET.CONSTRUCTOR.TERM TERM ASSIGNMENT))
	       ((DP-SORT.ARRAY (DA-TERM.SORT TERM))
		(EG=EVAL.ARRAY.CONSTRUCTOR.TERM TERM ASSIGNMENT))
	       (T (DA-TERM.CREATE (DA-TERM.SYMBOL TERM)
				  (MAPCAR #'(LAMBDA (SUBTERM) (EG=EVAL.TERM SUBTERM ASSIGNMENT))
					  (DA-TERM.TERMLIST TERM))))))
	((DA-FUNCTION.LISPFCT (DA-TERM.SYMBOL TERM))
	 (APPLY (DA-FUNCTION.LISPFCT (DA-TERM.SYMBOL TERM))
		(MAPCAR #'(LAMBDA (SUBTERM) (EG=EVAL.TERM SUBTERM ASSIGNMENT)) (DA-TERM.TERMLIST TERM))))
	(T (DA-TERM.CREATE (DA-TERM.SYMBOL TERM) (MAPCAR #'(LAMBDA (SUBTERM) (EG=EVAL.TERM SUBTERM ASSIGNMENT))
							 (DA-TERM.TERMLIST TERM))))))


(DEFUN EG=EVAL.LITERAL (FORMULA)
 (LET ((RESULT (COND ((DA-PREDICATE.LISPFCT (DA-LITERAL.SYMBOL FORMULA))
		       (apply (DA-PREDICATE.LISPFCT (DA-LITERAL.SYMBOL FORMULA))
				(nconc (MAPCAR #'(LAMBDA (TERM) (EG=EVAL.TERM TERM)) (DA-LITERAL.TERMLIST FORMULA))
				       (list (da-literal.attributes formula)))))
		      (T (DA-LITERAL.CREATE '+ (DA-LITERAL.SYMBOL FORMULA)
					     (MAPCAR #'(LAMBDA (TERM) (EG=EVAL.TERM TERM)) 
						     (DA-LITERAL.TERMLIST FORMULA))
					     (da-literal.attributes formula))))))
    (COND ((EQ '- (DA-LITERAL.SIGN FORMULA))
	   (SETQ RESULT (EG=NOT RESULT)))
	  (T RESULT))))


(DEFUN EG=EVAL.FORMULA (FORMULA)
  (COND ((DA-LITERAL.IS FORMULA) (EG=EVAL.LITERAL FORMULA))
	(T (CASE (DA-GTERM.SYMBOL FORMULA)
	     (OR (APPLY 'EG=OR (MAPCAR #'EG=EVAL.FORMULA (DA-GTERM.TERMLIST FORMULA))))
	     (AND (APPLY 'EG=AND (MAPCAR #'EG=EVAL.FORMULA (DA-GTERM.TERMLIST FORMULA))))
             (NOT (EG=NOT (EG=EVAL.FORMULA (CAR (DA-GTERM.TERMLIST FORMULA)))))
	     (IMPL (EG=IMPL (EG=EVAL.FORMULA (CAR (DA-GTERM.TERMLIST FORMULA)))
			    (EG=EVAL.FORMULA (SECOND (DA-GTERM.TERMLIST FORMULA)))))
	     (EQV (EG=EQV (EG=EVAL.FORMULA (CAR (DA-GTERM.TERMLIST FORMULA)))
			  (EG=EVAL.FORMULA (SECOND (DA-GTERM.TERMLIST FORMULA)))))
	     (ALL (EG=ALL (CAR (DA-GTERM.TERMLIST FORMULA)) 
			  (EG=EVAL.FORMULA (SECOND (DA-GTERM.TERMLIST FORMULA)))))
	     (EX (EG=EX (CAR (DA-GTERM.TERMLIST FORMULA)) 
			(EG=EVAL.FORMULA (SECOND (DA-GTERM.TERMLIST FORMULA)))))))))


(DEFUN EG=SIMPLIFY (FORMULA ASSUMPTIONS)
  (COND ((DA-LITERAL.IS FORMULA)
	 (EG=CHECK.ASSUMPTIONS FORMULA ASSUMPTIONS))
	(T (CASE (DA-GTERM.SYMBOL FORMULA)
	     (OR (EG=SIMPLIFY.OR (DA-GTERM.TERMLIST FORMULA) ASSUMPTIONS))
	     (AND (EG=SIMPLIFY.AND (DA-GTERM.TERMLIST FORMULA) ASSUMPTIONS))
             (NOT (EG=SIMPLIFY.NOT (CAR (DA-GTERM.TERMLIST FORMULA)) ASSUMPTIONS))
	     (IMPL (EG=SIMPLIFY.IMPL (CAR (DA-GTERM.TERMLIST FORMULA)) (SECOND (DA-GTERM.TERMLIST FORMULA)) ASSUMPTIONS))
	     (EQV (EG=SIMPLIFY.EQV (CAR (DA-GTERM.TERMLIST FORMULA)) (SECOND (DA-GTERM.TERMLIST FORMULA)) ASSUMPTIONS))
	     (ALL (EG=SIMPLIFY.QUANTIFIER 'ALL (CAR (DA-GTERM.TERMLIST FORMULA)) (SECOND (DA-GTERM.TERMLIST FORMULA)) ASSUMPTIONS))
	     (EX (EG=SIMPLIFY.QUANTIFIER 'EX (CAR (DA-GTERM.TERMLIST FORMULA)) (SECOND (DA-GTERM.TERMLIST FORMULA)) ASSUMPTIONS))))))


(DEFUN EG=CHECK.ASSUMPTIONS (FORMULA ASSUMPTIONS)
  (COND (EG*NON.SYMBOLIC FORMULA)
	((MEMBER-IF #'(LAMBDA (FOR)
                        (UNI-GTERM.MATCH FOR FORMULA))
                    ASSUMPTIONS) 
         (DA-LITERAL.TRUE))
        ((LET ((NEG.FOR (COND ((DA-LITERAL.IS FORMULA) (DA-FORMULA.NEGATE FORMULA))
                              ((EQ (DA-GTERM.SYMBOL FORMULA) 'NOT) (CAR (DA-GTERM.TERMLIST FORMULA)))
                              (T (DA-FORMULA.CREATE 'NOT (LIST FORMULA))))))
           (COND ((MEMBER-IF #'(LAMBDA (FOR)
                                 (UNI-GTERM.MATCH FOR NEG.FOR))
                             ASSUMPTIONS)
                  (DA-LITERAL.FALSE)))))
        (T FORMULA)))


(DEFUN EG=ASSUME.FORMULA.AS (VALUE FORMULA)
  (COND ((EQ VALUE 'TRUE)
         (COND ((DA-LITERAL.IS FORMULA) (LIST FORMULA))
               (T (CASE (DA-GTERM.SYMBOL FORMULA)
                    (AND (MAPCAN #'(LAMBDA (FOR)
				     (EG=ASSUME.FORMULA.AS 'TRUE FOR))
                                 (DA-GTERM.TERMLIST FORMULA)))
                    (NOT (EG=ASSUME.FORMULA.AS 'FALSE (CAR (DA-GTERM.TERMLIST FORMULA))))
                    (OTHERWISE (LIST FORMULA))))))
        (T (COND ((DA-LITERAL.IS FORMULA ) (LIST (DA-FORMULA.NEGATE FORMULA)))
                 (T (CASE (DA-GTERM.SYMBOL FORMULA)
                      (OR (MAPCAN #'(LAMBDA (FOR) (EG=ASSUME.FORMULA.AS 'FALSE FOR))
				  (DA-GTERM.TERMLIST FORMULA)))
                      (IMPL (NCONC (EG=ASSUME.FORMULA.AS 'TRUE (CAR (DA-GTERM.TERMLIST FORMULA)))
                                   (EG=ASSUME.FORMULA.AS 'FALSE (SECOND (DA-GTERM.TERMLIST FORMULA)))))
                      (NOT (EG=ASSUME.FORMULA.AS 'TRUE (CAR (DA-GTERM.TERMLIST FORMULA))))
                      (OTHERWISE (LIST (DA-FORMULA.CREATE 'NOT (LIST FORMULA))))))))))


(DEFUN EG=SIMPLIFY.AND (ARGS ASSUMPTIONS)
  (LET ((SUB.ASSUMPTIONS ASSUMPTIONS))
    (SETQ ARGS (MAPCAR #'(LAMBDA (FOR)
			   (PROG1 (EG=SIMPLIFY FOR SUB.ASSUMPTIONS)
			     (SETQ SUB.ASSUMPTIONS (APPEND (EG=ASSUME.FORMULA.AS 'TRUE FOR) SUB.ASSUMPTIONS))))
		       ARGS))
    (COND ((SOME #'(LAMBDA (FOR) (COND ((DA-FORMULA.IS.FALSE FOR) FOR))) ARGS))
          (T (SETQ ARGS (REMOVE-IF #'DA-FORMULA.IS.TRUE ARGS))
	     (COND ((NULL ARGS) (DA-LITERAL.TRUE))
		   ((NULL (CDR ARGS)) (CAR ARGS))
		   (T (EG=CHECK.ASSUMPTIONS (DA-FORMULA.CREATE 'AND ARGS) ASSUMPTIONS)))))))


(DEFUN EG=SIMPLIFY.NOT (ARG ASSUMPTIONS)
  (LET ((LEFT (EG=SIMPLIFY ARG ASSUMPTIONS)))
    (COND ((EG=LITERAL.IS.TRUE LEFT) (DA-LITERAL.FALSE))
          ((EG=LITERAL.IS.FALSE LEFT) (DA-LITERAL.TRUE))
          (T (EG=CHECK.ASSUMPTIONS (DA-FORMULA.NEGATE LEFT) ASSUMPTIONS)))))


(DEFUN EG=SIMPLIFY.OR (ARGS ASSUMPTIONS)
  (LET ((SUB.ASSUMPTIONS ASSUMPTIONS))
    (SETQ ARGS (MAPCAR #'(LAMBDA (FOR)
			   (PROG1 (EG=SIMPLIFY FOR SUB.ASSUMPTIONS)
			     (SETQ SUB.ASSUMPTIONS (APPEND (EG=ASSUME.FORMULA.AS 'FALSE FOR) SUB.ASSUMPTIONS))))
		       ARGS))
    (COND ((SOME #'(LAMBDA (FOR) (COND ((DA-FORMULA.IS.TRUE FOR) FOR))) ARGS))
          (T (SETQ ARGS (REMOVE-IF #'DA-FORMULA.IS.FALSE ARGS))
	     (COND ((NULL ARGS) (DA-LITERAL.FALSE))
		   ((NULL (CDR ARGS)) (CAR ARGS))
		   (T (EG=CHECK.ASSUMPTIONS (DA-FORMULA.CREATE 'OR ARGS) ASSUMPTIONS)))))))


(DEFUN EG=SIMPLIFY.IMPL (ARG1 ARG2 ASSUMPTIONS)
  (LET* ((LEFT (EG=SIMPLIFY ARG1 (APPEND (EG=ASSUME.FORMULA.AS 'FALSE ARG2) ASSUMPTIONS)))
         (RIGHT (EG=SIMPLIFY ARG2 (APPEND (EG=ASSUME.FORMULA.AS 'TRUE LEFT) ASSUMPTIONS))))
    (COND ((EG=LITERAL.IS.TRUE LEFT) RIGHT)
          ((EG=LITERAL.IS.FALSE LEFT) (DA-LITERAL.TRUE))
          ((EG=LITERAL.IS.TRUE RIGHT) RIGHT)
          ((EG=LITERAL.IS.FALSE RIGHT) (DA-FORMULA.JUNCTION.CLOSURE 'AND (EG=ASSUME.FORMULA.AS 'FALSE LEFT)))
          (T (EG=CHECK.ASSUMPTIONS (DA-FORMULA.CREATE 'IMPL (LIST LEFT RIGHT)) ASSUMPTIONS)))))


(DEFUN EG=SIMPLIFY.EQV (ARG1 ARG2 ASSUMPTIONS)
  (LET ((LEFT (EG=SIMPLIFY ARG1 ASSUMPTIONS))
        (RIGHT (EG=SIMPLIFY ARG2 ASSUMPTIONS)))
    (COND ((EG=LITERAL.IS.TRUE LEFT) RIGHT)
          ((EG=LITERAL.IS.FALSE LEFT) (DA-FORMULA.JUNCTION.CLOSURE 'AND (EG=ASSUME.FORMULA.AS 'FALSE RIGHT)))
          ((EG=LITERAL.IS.TRUE RIGHT) LEFT)
          ((EG=LITERAL.IS.FALSE RIGHT) (DA-FORMULA.JUNCTION.CLOSURE 'AND (EG=ASSUME.FORMULA.AS 'FALSE LEFT)))
          ((UNI-GTERM.ARE.EQUAL LEFT RIGHT) (DA-LITERAL.TRUE))
          (T (EG=CHECK.ASSUMPTIONS (DA-FORMULA.CREATE 'EQV (LIST LEFT RIGHT)) ASSUMPTIONS)))))


(DEFUN EG=SIMPLIFY.QUANTIFIER (QUANTIFIER VAR ARG ASSUMPTIONS)
  (LET ((RIGHT (EG=SIMPLIFY ARG ASSUMPTIONS)))
        (COND ((OR (EG=LITERAL.IS.TRUE RIGHT) (EG=LITERAL.IS.FALSE RIGHT)) RIGHT)
              (T (EG=CHECK.ASSUMPTIONS (DA-FORMULA.QUANTIFICATION.CLOSURE QUANTIFIER (LIST VAR) RIGHT) ASSUMPTIONS)))))


(DEFUN EG=LITERAL.IS.TRUE (LITERAL)

  (AND (DA-LITERAL.IS LITERAL)
       (DA-LITERAL.IS.TRUE LITERAL)))


(DEFUN EG=LITERAL.IS.FALSE (LITERAL)

  (AND (DA-LITERAL.IS LITERAL)
       (DA-LITERAL.IS.FALSE LITERAL)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                                                       ;;;
;;;                              ARRAY AND SET SIMPLIFICATION                             ;;;
;;;                                                                                       ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(DEFUN EG=EVAL.SET.CONSTRUCTOR.TERM (TERM ASSIGNMENT)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a term and an environment
  ;;; Effect : simplifies each set constructor term due to its structural behaviour:
  ;;;          elem(x, y) impl insert(x, y) = y
  ;;; Value  : if term could be simplified the simplified term, else either the
  ;;;          original term or NIL depending on EG*NON.SYMBOLIC
  
  (COND ((AND EG*NON.SYMBOLIC (NOT TERM)) NIL)
	(T (LET ((SORT (DA-TERM.SORT TERM))
		 ELEMENT SET)
	     (COND ((EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.SET.EMPTY SORT)) TERM)
		   ((EG=LITERAL.IS.TRUE (EG=EVAL.SET.ELEM (SETQ ELEMENT (EG=EVAL.TERM (FIRST (DA-TERM.TERMLIST TERM)) ASSIGNMENT))
							    (SETQ SET (EG=EVAL.TERM (SECOND (DA-TERM.TERMLIST TERM)) ASSIGNMENT))))
		    SET)
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SORT) (LIST ELEMENT SET))))))))
	



(DEFUN EG=EVAL.SET.ELEM (ELEMENT SET &OPTIONAL ATTRIBUTES)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : two terms, an element term and a set term, and optionally a list of attributes
  ;;; Effect : simplification of the literal elem(element, set) due to the following simplification rules:
  ;;;          not elem(element, empty)
  ;;;          elem(element, insert(element, y))
  ;;;          (not x = element) impl (elem(element, insert(x, y)) eqv elem(element, y))
  ;;;          not elem(element(x), subset(x))
  ;;;          elem(element, y) impl elem(element, insert(x, y))
  ;;; Value  : if simplification of elem(element, set) was successful the simplified literal, else either the
  ;;;          original literal or NIL depending on EG*NON.SYMBOLIC
  
  (COND ((AND EG*NON.SYMBOLIC (NOT (AND ELEMENT SET))) NIL)
	(T (LET ((SORT (DA-TERM.SORT SET))
		 RESULT)
	     (COND ((LET ((EG*NON.SYMBOLIC T))
		      (EQ (DA-TERM.SYMBOL SET) (DP-FUNCTION.SET.EMPTY SORT)))
		    (DP-LITERAL.FALSE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.TRUE (SETQ RESULT (EG=EQUAL ELEMENT (FIRST (DA-TERM.TERMLIST SET)) ATTRIBUTES)))))
		    (DP-LITERAL.TRUE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.FALSE RESULT)))
		    (EG=EVAL.SET.ELEM ELEMENT (SECOND (DA-TERM.TERMLIST SET)) ATTRIBUTES))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET) (DP-FUNCTION.SET.SUBSET SORT))
			   (EQ (DA-TERM.SYMBOL ELEMENT) (DP-FUNCTION.SET.ELEMENT SORT))
			   (EG=LITERAL.IS.TRUE (EG=SET.EQUAL (FIRST (DA-TERM.TERMLIST ELEMENT))
							     (FIRST (DA-TERM.TERMLIST SET))
							     ATTRIBUTES))))
		    (DA-LITERAL.FALSE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.TRUE (EG=EVAL.SET.ELEM ELEMENT (SECOND (DA-TERM.TERMLIST SET)) ATTRIBUTES))))
		    (DA-LITERAL.TRUE))
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.ELEM SORT)
					 (LIST ELEMENT SET) ATTRIBUTES)))))))

(DEFUN EG=EVAL.SET.DELETE (ELEMENT SET)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : two terms, an element term and a set term
  ;;; Effect : simplification of the term delete(element, set) due to the following simplification rules:
  ;;;          delete(element, empty) = empty
  ;;;          delete(element, insert(element, y)) = delete(element, y)
  ;;;          (not x = element) impl delete(element, insert(x, y)) = insert(x, delete(element, y))
  ;;; Value  : if simplification of delete(element, set) was successful the simplified term, else either the
  ;;;          original term or NIL depending on EG*NON.SYMBOLIC

  (COND ((AND EG*NON.SYMBOLIC (NOT (AND ELEMENT SET))) NIL)
	(T (LET ((SORT (DA-TERM.SORT SET))
		 RESULT)
	     (COND ((LET ((EG*NON.SYMBOLIC T))
		      (EQ (DA-TERM.SYMBOL SET) (DP-FUNCTION.SET.EMPTY SORT)))
		    SET)
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.TRUE (SETQ RESULT (EG=EQUAL ELEMENT (FIRST (DA-TERM.TERMLIST SET)))))))
		    (EG=EVAL.SET.DELETE ELEMENT (SECOND (DA-TERM.TERMLIST SET))))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.FALSE RESULT)))
		    (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SORT)
				    (LIST (FIRST (DA-TERM.TERMLIST SET))
					  (EG=EVAL.SET.DELETE ELEMENT (SECOND (DA-TERM.TERMLIST SET))))))
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-TERM.CREATE (DP-FUNCTION.SET.DELETE SORT)
				      (LIST ELEMENT SET))))))))


(DEFUN EG=EVAL.SET.UNION (SET1 SET2)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : two sets
  ;;; Effect : simplification of the term union(set1, set2) due to the following simplification rules
  ;;;          union(empty, set2) = set2
  ;;;          elem(x, union(y, set2)) impl union(insert(x, y), set2) = union(y, set2)
  ;;;          (not elem(x, union(y, set2))) impl union(insert(x, y), set2) = insert(x, union(y, set2))
  ;;; Value  : if simplification of union(set1, set2) was successful the simplified term, else either the
  ;;;          original term or NIL depending on EG*NON.SYMBOLIC

  (COND ((AND EG*NON.SYMBOLIC (NOT (AND SET1 SET2))) NIL)
	(T (LET ((SORT (DA-TERM.SORT SET1))
		 RESULT RESULT.SET)
	     (COND ((LET ((EG*NON.SYMBOLIC T))
		      (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.EMPTY SORT)))
		    SET2)
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.TRUE
			    (SETQ RESULT (EG=EVAL.SET.ELEM (FIRST (DA-TERM.TERMLIST SET1))
							     (SETQ RESULT.SET (EG=EVAL.SET.UNION
									       (SECOND (DA-TERM.TERMLIST SET1))
									       SET2)))))))
		    RESULT.SET)
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.FALSE RESULT)))
		    (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SORT)
				    (LIST (FIRST (DA-TERM.TERMLIST SET1))
					  RESULT.SET)))
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-TERM.CREATE (DP-FUNCTION.SET.UNION SORT)
				      (LIST SET1 SET2))))))))


(DEFUN EG=EVAL.SET.INTERSECTION (SET1 SET2)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : two sets
  ;;; Effect : simplification of the term intersection(set1, set2) due to the following simplification rules
  ;;;          intersection(empty, set2) = empty
  ;;;          elem(x, y) impl intersection(insert(x, y), set2) = intersection(y, set2)
  ;;;          ((not elem(x, y)) and elem(x, set2)) impl intersection(insert(x, y), set2) = insert(x, intersection(y, set2))
  ;;;          ((not elem(x, y)) and (not elem(x, set2))) impl intersection(insert(x, y), set2) = intersection(y, set2)
  ;;; Value  : if simplification of intersection(set1, set2) was successful the simplified term, else either the
  ;;;          original term or NIL depending on EG*NON.SYMBOLIC

  (COND ((AND EG*NON.SYMBOLIC (NOT (AND SET1 SET2))) NIL)
	(T (LET ((SORT (DA-TERM.SORT SET1))
		 RESULT1 RESULT2)
	     (COND ((LET ((EG*NON.SYMBOLIC T))
		      (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.EMPTY SORT)))
		    SET1)
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.TRUE
			    (SETQ RESULT1 (EG=EVAL.SET.ELEM (FIRST (DA-TERM.TERMLIST SET1))
							      (SECOND (DA-TERM.TERMLIST SET1)))))))
		    (EG=EVAL.SET.INTERSECTION (SECOND (DA-TERM.TERMLIST SET1)) SET2))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.FALSE RESULT1)
			   (EG=LITERAL.IS.TRUE
			    (SETQ RESULT2 (EG=EVAL.SET.ELEM (FIRST (DA-TERM.TERMLIST SET1))
							      SET2)))))
		    (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SORT)
				    (LIST (FIRST (DA-TERM.TERMLIST SET1))
					  (EG=EVAL.SET.INTERSECTION (SECOND (DA-TERM.TERMLIST SET1)) SET2))))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.FALSE RESULT1)
			   (EG=LITERAL.IS.FALSE RESULT2)))
		    (EG=EVAL.SET.INTERSECTION (SECOND (DA-TERM.TERMLIST SET1)) SET2))
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-TERM.CREATE (DP-FUNCTION.SET.INTERSECTION SORT)
				      (LIST SET1 SET2))))))))


(DEFUN EG=EVAL.SET.DIFFERENCE (SET1 SET2)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : two sets
  ;;; Effect : simplification of the term difference(set1, set2) due to the following simplification rules
  ;;;          difference(empty, set2) = empty
  ;;;          elem(x, set2) impl difference(insert(x, y), set2) = difference(y, set2)
  ;;;          (not elem(x, set2)) impl difference(insert(x, y), set2) = insert(x, difference(y, set2))
  ;;; Value  : if simplification of difference(set1, set2) was successful the simplified term, else either the
  ;;;          original term or NIL depending on EG*NON.SYMBOLIC

  (COND ((AND EG*NON.SYMBOLIC (NOT (AND SET1 SET2))) NIL)
	(T (LET ((SORT (DA-TERM.SORT SET1))
		 RESULT)
	     (COND ((LET ((EG*NON.SYMBOLIC T))
		      (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.EMPTY SORT)))
		    SET1)
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.TRUE
			    (SETQ RESULT (EG=EVAL.SET.ELEM (FIRST (DA-TERM.TERMLIST SET1)) SET2)))))
		    (EG=EVAL.SET.DIFFERENCE (SECOND (DA-TERM.TERMLIST SET1)) SET2))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.FALSE RESULT)))
		    (DA-TERM.CREATE (DP-FUNCTION.SET.INSERT SORT)
				    (LIST (FIRST (DA-TERM.TERMLIST SET1))
					  (EG=EVAL.SET.DIFFERENCE (SECOND (DA-TERM.TERMLIST SET1)) SET2))))
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-TERM.CREATE (DP-FUNCTION.SET.DIFFERENCE SORT)
				      (LIST SET1 SET2))))))))


(DEFUN EG=EVAL.SET.SYM.DIFFERENCE (SET1 SET2)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : two sets
  ;;; Effect : simplification of the term sym.difference(set1, set2) due to the following simplification rule
  ;;;          sym.difference(set1, set2) = union(difference(set1, set2), difference(set2, set1))
  ;;; Value  : the result of the simplification of union and difference

  (EG=EVAL.SET.UNION (EG=EVAL.SET.DIFFERENCE SET1 SET2) (EG=EVAL.SET.DIFFERENCE SET2 SET1)))


(DEFUN EG=EVAL.SET.<= (SET1 SET2 &OPTIONAL ATTRIBUTES)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : two sets and optionally a list of attributes
  ;;; Effect : simplification of the literal <=(set1, set2) due to the following simplification rules
  ;;;          <=(empty, set2)
  ;;;          elem(x, set2) impl (<=(insert(x, y), set2) eqv <=(y, set2))
  ;;;          (not elem(x, set2)) impl (not <=(insert(x, y), set2))
  ;;; Value  : if simplification of <=(set1, set2) was successful the simplified literal, else either the
  ;;;          original literal or NIL depending on EG*NON.SYMBOLIC

  (COND ((AND EG*NON.SYMBOLIC (NOT (AND SET1 SET2))) NIL)
	(T (LET ((SORT (DA-TERM.SORT SET1))
		 RESULT)
	     (COND ((LET ((EG*NON.SYMBOLIC T))
		      (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.EMPTY SORT)))
		    (DA-LITERAL.TRUE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.TRUE
			    (SETQ RESULT (EG=EVAL.SET.ELEM (FIRST (DA-TERM.TERMLIST SET1)) SET2 ATTRIBUTES)))))
		    (EG=EVAL.SET.<= (SECOND (DA-TERM.TERMLIST SET1)) SET2 ATTRIBUTES))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.FALSE RESULT)))
		    (DA-LITERAL.FALSE))
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.<= SORT)
					 (LIST SET1 SET2) ATTRIBUTES)))))))


(DEFUN EG=EVAL.SET.>= (SET1 SET2 &OPTIONAL ATTRIBUTES)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : two sets and optionally a list of attributes
  ;;; Effect : simplification of the literal >=(set1, set2) due to the following simplification rule
  ;;;          >=(set1, set2) eqv <=(set2, set1)
  ;;; Value  : the result of the simplification of union and difference

  (EG=EVAL.SET.<= SET2 SET1 ATTRIBUTES))




(DEFUN EG=EVAL.SET.SUBSET (SET)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set
  ;;; Effect : simplification of the term subset(set) due to the following simplification rule
  ;;;          subset(empty) = empty
  ;;; Value  : if simplification of subset(set) was successful the simplified term, else either the
  ;;;          original term or NIL depending on EG*NON.SYMBOLIC

  (COND ((AND EG*NON.SYMBOLIC (NOT SET)) NIL)
	(T (LET ((SORT (DA-TERM.SORT SET)))
	     (COND ((LET ((EG*NON.SYMBOLIC T))
		      (EQ (DA-TERM.SYMBOL SET) (DP-FUNCTION.SET.EMPTY SORT)))
		    SET)
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-TERM.CREATE (DP-FUNCTION.SET.SUBSET SORT) (LIST SET))))))))
	

(DEFUN EG=EVAL.SET.DELTA.SUBSET (SET &OPTIONAL ATTRIBUTES)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set and optionally a list of attributes
  ;;; Effect : simplification of the literal delta.subset(set) due to the following simplification rules
  ;;;          (not delta.subset(empty))
  ;;;          delat.subset(insert(x, y))
  ;;; Value  : if simplification of delta.subset(set) was successful the simplified literal, else either the
  ;;;          original literal or NIL depending on EG*NON.SYMBOLIC

  (COND ((AND EG*NON.SYMBOLIC (NOT SET)) NIL)
	(T (LET ((SORT (DA-TERM.SORT SET)))
	     (COND ((LET ((EG*NON.SYMBOLIC T))
		      (EQ (DA-TERM.SYMBOL SET) (DP-FUNCTION.SET.EMPTY SORT)))
		    (DA-LITERAL.FALSE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (EQ (DA-TERM.SYMBOL SET) (DP-FUNCTION.SET.INSERT SORT)))
		    (DA-LITERAL.TRUE))
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.DELTA.SUBSET SORT)
					 (LIST SET) ATTRIBUTES)))))))


(DEFUN EG=EVAL.SET.DELTA.DELETE (ELEMENT SET &OPTIONAL ATTRIBUTES)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an element, a set, and optionally a list of attributes
  ;;; Effect : simplification of the literal delta.delete(element, set) due to the following simplification rule
  ;;;          delta.delete(element, set) eqv elem(element, set)
  ;;; Value  : if simplification of delta.delete was successful the simplified literal, else either the
  ;;;          original literal or NIL depending on EG*NON.SYMBOLIC

  (EG=EVAL.SET.ELEM ELEMENT SET ATTRIBUTES))


(DEFUN EG=EVAL.SET.DELTA.INTERSECTION.1 (SET1 SET2 &OPTIONAL ATTRIBUTES)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : two sets and optionally a list of attributes
  ;;; Effect : simplification of the literal delta.intersection.1(set) due to the following simplification rules
  ;;;          (not delta.intersection.1(empty, set2))
  ;;;          elem(x, set2) impl (delta.intersection.1(insert(x, y), set2) eqv delta.intersection.1(y, set2))
  ;;;          (not elem(x, set2)) impl delta.intersection.1(insert(x, y), set2)
  ;;; Value  : if simplification of delta.intersection.1(set1, set2) was successful the simplified literal, else either the
  ;;;          original literal or NIL depending on EG*NON.SYMBOLIC

  (COND ((AND EG*NON.SYMBOLIC (NOT (AND SET1 SET2))) NIL)
	(T (LET ((SORT (DA-TERM.SORT SET1))
		 RESULT)
	     (COND ((EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.EMPTY SORT))
		    (DA-LITERAL.FALSE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.FALSE (SETQ RESULT (EG=EVAL.SET.ELEM (FIRST (DA-TERM.TERMLIST SET1)) SET2 ATTRIBUTES)))))
		    (DA-LITERAL.TRUE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.TRUE RESULT)))
		    (EG=EVAL.SET.DELTA.INTERSECTION.1 (SECOND (DA-TERM.TERMLIST SET1)) SET2 ATTRIBUTES))
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.DELTA.INTERSECTION.1 SORT)
					 (LIST SET1 SET2) ATTRIBUTES)))))))

(DEFUN EG=EVAL.SET.DELTA.INTERSECTION.2 (SET1 SET2 &OPTIONAL ATTRIBUTES)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : two sets and optionally a list of attributes
  ;;; Effect : simplification of the literal delta.intersection.2(set1, set2) due to the following simplification rule
  ;;;          delta.intersection.2(set1, set2) eqv delta.intersection.1(set2, set1)
  ;;; Value  : if simplification of delta.intersection.2 was successful the simplified literal, else either the
  ;;;          original literal or NIL depending on EG*NON.SYMBOLIC

  (EG=EVAL.SET.DELTA.INTERSECTION.1 SET2 SET1 ATTRIBUTES))


(DEFUN EG=EVAL.SET.DELTA.DIFFERENCE (SET1 SET2 &OPTIONAL ATTRIBUTES)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : two sets and optionally a list of attributes
  ;;; Effect : simplification of the literal delta.difference(set1, set2) due to the following simplification rules
  ;;;          (not delta.difference(empty, set2))
  ;;;          elem(x, set2) impl delta.difference(insert(x, y), set2)
  ;;;          (not elem(x, set2)) impl (delta.difference(insert(x, y), set2) eqv delta.difference(y, set2))
  ;;; Value  : if simplification of delta.difference(set1, set2) was successful the simplified literal, else either the
  ;;;          original literal or NIL depending on EG*NON.SYMBOLIC

  (COND ((AND EG*NON.SYMBOLIC (NOT (AND SET1 SET2))) NIL)
	(T (LET ((SORT (DA-TERM.SORT SET1))
		 RESULT)
	     (COND ((EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.EMPTY SORT))
		    (DA-LITERAL.FALSE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.TRUE (SETQ RESULT (EG=EVAL.SET.ELEM (FIRST (DA-TERM.TERMLIST SET1)) SET2 ATTRIBUTES)))))
		    (DA-LITERAL.TRUE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.FALSE RESULT)))
		    (EG=EVAL.SET.DELTA.DIFFERENCE (SECOND (DA-TERM.TERMLIST SET1)) SET2 ATTRIBUTES))
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.SET.DELTA.DIFFERENCE SORT)
					 (LIST SET1 SET2) ATTRIBUTES)))))))


(DEFUN EG=EVAL.SET.ELEMENT (SET)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a set
  ;;; Effect : simplification of the term element(set) to the following simplification rule
  ;;;          ---
  ;;; Value  : if simplification of element(set) was successful the simplified term, else either the
  ;;;          original term or NIL depending on EG*NON.SYMBOLIC

  (COND (EG*NON.SYMBOLIC NIL)
	(T (DA-TERM.CREATE (DP-FUNCTION.SET.ELEMENT (DA-TERM.SORT SET)) (LIST SET)))))


(DEFUN EG=SET.EQUAL (SET1 SET2 &OPTIONAL ATTRIBUTES)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : two sets and optionally a list of attributes
  ;;; Effect : simplification of the literal set1 = set2 
  ;;; Value  : if simplification of set1 = set2 was successful the simplified literal, else either the
  ;;;          original literal or NIL depending on EG*NON.SYMBOLIC

  (COND ((AND EG*NON.SYMBOLIC (NOT (AND SET1 SET2))) NIL)
	(T (LET ((SORT (DA-TERM.SORT SET1))
		 RESULT)
	     (COND ((AND (EQ (DA-TERM.SYMBOL SET1) (DA-TERM.SYMBOL SET2))
			 (NULL (DA-TERM.TERMLIST SET1))
			 (NULL (DA-TERM.TERMLIST SET2)))
		    (DA-LITERAL.TRUE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET1) (DA-TERM.SYMBOL SET2))
			   (EVERY #'(LAMBDA (SUBTERM1 SUBTERM2)
				      (EG=LITERAL.IS.TRUE (EG=EQUAL SUBTERM1 SUBTERM2 ATTRIBUTES)))
				  (DA-TERM.TERMLIST SET1) (DA-TERM.TERMLIST SET2))))
		    (DA-LITERAL.TRUE))
		   ((AND (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.EMPTY SORT))
			 (EQ (DA-TERM.SYMBOL SET2) (DP-FUNCTION.SET.INSERT SORT)))
		    (DA-LITERAL.FALSE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.TRUE (SETQ RESULT (EG=EVAL.SET.ELEM (FIRST (DA-TERM.TERMLIST SET1)) SET2 ATTRIBUTES)))))
		    (EG=SET.EQUAL (EG=EVAL.SET.DELETE (FIRST (DA-TERM.TERMLIST SET1)) (SECOND (DA-TERM.TERMLIST SET1)))
				  (EG=EVAL.SET.DELETE (FIRST (DA-TERM.TERMLIST SET1)) SET2)
				  ATTRIBUTES))
		   ((LET ((EG*NON.SYMBOLIC T))	     
		      (AND (EQ (DA-TERM.SYMBOL SET1) (DP-FUNCTION.SET.INSERT SORT))
			   (EG=LITERAL.IS.FALSE RESULT)))
		    (DA-LITERAL.FALSE))
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.EQUALITY)
					 (LIST SET1 SET2) ATTRIBUTES)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DEFUN EG=EVAL.ARRAY.CONSTRUCTOR.TERM (TERM ASSIGNMENT &OPTIONAL INDICES)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : a term and an environment
  ;;; Effect : simplifies each array constructor term due to its structural behaviour
  ;;;          update(update(A, i, x), i, y) = update(A, i, y)
  ;;;          update(init(x), i, x) = init(x)
  ;;; Value  : if term could be simplified the simplified term, else either the
  ;;;          original term or NIL depending on EG*NON.SYMBOLIC
  
  (COND ((AND EG*NON.SYMBOLIC (NOT TERM)) NIL)
	(T (LET ((SORT (DA-TERM.SORT TERM))
		 ARR INDEX ENTRY)
	     (COND ((EQ (DA-TERM.SYMBOL TERM) (DP-FUNCTION.ARRAY.INIT SORT))
		    (DA-TERM.CREATE (DA-TERM.SYMBOL TERM) (LIST (EG=EVAL.TERM (FIRST (DA-TERM.TERMLIST TERM)) ASSIGNMENT))))
		   (T (SETQ INDEX (EG=EVAL.TERM (SECOND (DA-TERM.TERMLIST TERM)) ASSIGNMENT))
		      (SETQ ENTRY (EG=EVAL.TERM (THIRD (DA-TERM.TERMLIST TERM)) ASSIGNMENT))
		      (COND ((AND (FIRST (DA-TERM.TERMLIST TERM))
				  (DA-FUNCTION.IS (DA-TERM.SYMBOL (FIRST (DA-TERM.TERMLIST TERM))))
				  (DA-FUNCTION.IS.CONSTRUCTOR (DA-TERM.SYMBOL (FIRST (DA-TERM.TERMLIST TERM)))))
			     (SETQ ARR (EG=EVAL.ARRAY.CONSTRUCTOR.TERM (FIRST (DA-TERM.TERMLIST TERM)) ASSIGNMENT (CONS INDEX INDICES))))
			    (T (SETQ ARR (EG=EVAL.TERM (FIRST (DA-TERM.TERMLIST TERM)) ASSIGNMENT))))
		      (COND ((FIND-IF #'(LAMBDA (SUBTERM)
					  (EG=LITERAL.IS.TRUE (EG=EQUAL SUBTERM INDEX)))
				      INDICES)
			     ARR)
			    ((EG=LITERAL.IS.TRUE (EG=EQUAL ENTRY (EG=EVAL.ARRAY.DEFAULT ARR)))
			     ARR)
			    (T (DA-TERM.CREATE (DP-FUNCTION.ARRAY.UPDATE SORT)
					       (LIST ARR INDEX ENTRY))))))))))


(DEFUN EG=EVAL.ARRAY.DEFAULT (ARR)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array term
  ;;; Effect : simplifies the term default(arr) due to the following simplification rules
  ;;;          default(init(x)) = x
  ;;;          default(update(A, i, x)) = default(A)
  ;;; Value  : if default(arr) could be simplified the simplified term, else either the
  ;;;          original term or NIL depending on EG*NON.SYMBOLIC
  
  (COND ((AND EG*NON.SYMBOLIC (NOT ARR)) NIL)
	(T (LET ((SORT (DA-TERM.SORT ARR)))
	     (COND ((LET ((EG*NON.SYMBOLIC T))
		      (EQ (DA-TERM.SYMBOL ARR) (DP-FUNCTION.ARRAY.INIT SORT)))
		    (FIRST (DA-TERM.TERMLIST ARR)))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (EQ (DA-TERM.SYMBOL ARR) (DP-FUNCTION.ARRAY.UPDATE SORT)))
		    (EG=EVAL.ARRAY.DEFAULT (FIRST (DA-TERM.TERMLIST ARR))))
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-TERM.CREATE (DP-FUNCTION.ARRAY.DEFAULT SORT) (LIST ARR))))))))
	   

(DEFUN EG=EVAL.ARRAY.INDEX (ARR)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array term
  ;;; Effect : simplifies the term index(arr) due to the following simplification rules
  ;;;          ---
  ;;; Value  : if index(arr) could be simplified the simplified term, else either the
  ;;;          original term or NIL depending on EG*NON.SYMBOLIC
  
  (COND ((AND EG*NON.SYMBOLIC (NOT ARR)) NIL)
	(EG*NON.SYMBOLIC NIL)
	(T (DA-TERM.CREATE (DP-FUNCTION.ARRAY.INDEX (DA-TERM.SORT ARR)) (LIST ARR)))))


(DEFUN EG=EVAL.ARRAY.ENTRY (ARR)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array term
  ;;; Effect : simplifies the term entry(arr) due to the following simplification rules
  ;;;          ---
  ;;; Value  : if entry(arr) could be simplified the simplified term, else either the
  ;;;          original term or NIL depending on EG*NON.SYMBOLIC
  
  (COND ((AND EG*NON.SYMBOLIC (NOT ARR)) NIL)
	(EG*NON.SYMBOLIC NIL)
	(T (DA-TERM.CREATE (DP-FUNCTION.ARRAY.ENTRY (DA-TERM.SORT ARR)) (LIST ARR)))))


(DEFUN EG=EVAL.ARRAY.SUBARRAY (ARR)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array term
  ;;; Effect : simplifies the term subarray(arr) due to the following simplification rules
  ;;;          subarray(init(x)) = init(x)
  ;;; Value  : if subarray(arr) could be simplified the simplified term, else either the
  ;;;          original term or NIL depending on EG*NON.SYMBOLIC
  
  (COND ((AND EG*NON.SYMBOLIC (NOT ARR)) NIL)
	(T (LET ((SORT (DA-TERM.SORT ARR)))
	     (COND ((LET ((EG*NON.SYMBOLIC T))
		      (EQ (DA-TERM.SYMBOL ARR) (DP-FUNCTION.ARRAY.INIT SORT)))
		    ARR)
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-TERM.CREATE (DP-FUNCTION.ARRAY.SUBARRAY SORT) (LIST ARR))))))))


(DEFUN EG=EVAL.ARRAY.SELECT (ARR INDEX)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array term and an index term
  ;;; Effect : simplifies the term select(arr, index) due to the following simplification rules
  ;;;          select(init(x), index) = x
  ;;;          select(update(A, index, x), index) = x
  ;;;          (not index = i) impl select(update(A, i, x), index) = select(A, index)
  ;;; Value  : if select(arr, index) could be simplified the simplified term, else either the
  ;;;          original term or NIL depending on EG*NON.SYMBOLIC
  
  (COND ((AND EG*NON.SYMBOLIC (NOT ARR)) NIL)
	(T (LET ((SORT (DA-TERM.SORT ARR))
		 RESULT)
	     (COND ((LET ((EG*NON.SYMBOLIC T))
		      (EQ (DA-TERM.SYMBOL ARR) (DP-FUNCTION.ARRAY.INIT SORT)))
		    (FIRST (DA-TERM.TERMLIST ARR)))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR) (DP-FUNCTION.ARRAY.UPDATE SORT))
			   (EG=LITERAL.IS.TRUE (SETQ RESULT (EG=EQUAL INDEX (SECOND (DA-TERM.TERMLIST ARR)))))))
		    (THIRD (DA-TERM.TERMLIST ARR)))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR) (DP-FUNCTION.ARRAY.UPDATE SORT))
			   (EG=LITERAL.IS.FALSE RESULT)))
		    (EG=EVAL.ARRAY.SELECT (FIRST (DA-TERM.TERMLIST ARR)) INDEX))
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-TERM.CREATE (DP-FUNCTION.ARRAY.SELECT SORT) (LIST ARR INDEX))))))))


(DEFUN EG=EVAL.ARRAY.ELEM (INDEX ARR &OPTIONAL ATTRIBUTES)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an index term, an array term, and optionally a list of attributes
  ;;; Effect : simplifies the literal elem(index, arr) due to the following simplification rules
  ;;;          (not elem(index, init(x)))
  ;;;          (not default(A) = x) impl elem(index, update(A, index, x))
  ;;;          default(A) = x impl (not elem(index, update(A, index, x)))
  ;;;          (not index = i) impl (elem(index, update(A, i, x)) eqv elem(index, A))
  ;;; Value  : if elem(index, arr) could be simplified the simplified literal, else either the
  ;;;          original literal or NIL depending on EG*NON.SYMBOLIC
  
  (COND ((AND EG*NON.SYMBOLIC (NOT ARR)) NIL)
	(T (LET ((SORT (DA-TERM.SORT ARR))
		 RESULT1 RESULT2)
	     (COND ((LET ((EG*NON.SYMBOLIC T))
		      (EQ (DA-TERM.SYMBOL ARR) (DP-FUNCTION.ARRAY.INIT SORT)))
		    (DA-LITERAL.FALSE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR) (DP-FUNCTION.ARRAY.UPDATE SORT))
			   (EG=LITERAL.IS.TRUE (SETQ RESULT1 (EG=EQUAL INDEX (SECOND (DA-TERM.TERMLIST ARR)) ATTRIBUTES)))
			   (EG=LITERAL.IS.FALSE (SETQ RESULT2 (EG=EQUAL (THIRD (DA-TERM.TERMLIST ARR))
									(EG=EVAL.ARRAY.DEFAULT ARR) ATTRIBUTES)))))
		    (DA-LITERAL.TRUE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR) (DP-FUNCTION.ARRAY.UPDATE SORT))
			   (EG=LITERAL.IS.TRUE RESULT1)
			   (EG=LITERAL.IS.TRUE RESULT2)))
		    (DA-LITERAL.FALSE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR) (DP-FUNCTION.ARRAY.UPDATE SORT))
			   (EG=LITERAL.IS.FALSE RESULT1)))
		    (EG=EVAL.ARRAY.ELEM INDEX (FIRST (DA-TERM.TERMLIST ARR)) ATTRIBUTES))
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.ARRAY.ELEM SORT)
					 (LIST INDEX ARR) ATTRIBUTES)))))))


(DEFUN EG=EVAL.ARRAY.DELTA.SUBARRAY (ARR &OPTIONAL ATTRIBUTES INDICES)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : an array term and optionally a list of attributes and a list of indices which
  ;;;          were already being investigated
  ;;; Effect : simplifies the literal delta.subarray(arr) due to the following simplification rule
  ;;;          delta.subarray(arr) eqv (not arr = init(default(arr)))
  ;;; Value  : if delta.subarray(arr) could be simplified the simplified literal, else either the
  ;;;          original literal or NIL depending on EG*NON.SYMBOLIC
  
  (COND ((AND EG*NON.SYMBOLIC (NOT ARR)) NIL)
	(T (LET ((SORT (DA-TERM.SORT ARR))
		 INDEX RESULT1 RESULT2)
	     (COND ((LET ((EG*NON.SYMBOLIC T))
		      (EQ (DA-TERM.SYMBOL ARR) (DP-FUNCTION.ARRAY.INIT SORT)))
		    (DA-LITERAL.FALSE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR) (DP-FUNCTION.ARRAY.UPDATE SORT))
			   (SETQ INDEX (SECOND (DA-TERM.TERMLIST ARR)))
			   (SETQ RESULT1 (EVERY #'(LAMBDA (SUBTERM)
						    (EG=LITERAL.IS.FALSE (EG=EQUAL SUBTERM INDEX ATTRIBUTES)))
						INDICES))
			   (EG=LITERAL.IS.FALSE (SETQ RESULT2 (EG=EQUAL (THIRD (DA-TERM.TERMLIST ARR))
									(EG=EVAL.ARRAY.DEFAULT ARR) ATTRIBUTES)))))
		    (DA-LITERAL.TRUE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR) (DP-FUNCTION.ARRAY.UPDATE SORT))
			   RESULT1
			   (EG=LITERAL.IS.TRUE RESULT2)))
		    (EG=EVAL.ARRAY.DELTA.SUBARRAY (FIRST (DA-TERM.TERMLIST ARR)) ATTRIBUTES (CONS INDEX INDICES)))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR) (DP-FUNCTION.ARRAY.UPDATE SORT))
			   (EG=LITERAL.IS.TRUE (EG=EVAL.ARRAY.DELTA.SUBARRAY (FIRST (DA-TERM.TERMLIST ARR)) ATTRIBUTES (CONS INDEX INDICES)))))
		    (DA-LITERAL.TRUE))
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.ARRAY.DELTA.SUBARRAY SORT)
					 (LIST ARR) ATTRIBUTES)))))))
	  
		  


(DEFUN EG=ARRAY.EQUAL (ARR1 ARR2 &OPTIONAL ATTRIBUTES INDICES.ARR1 INDICES.ARR2)
  ;;; Edited : 21.04.94 by CS
  ;;; Input  : two array sets and optionally a list of attributes and two lists of indices which
  ;;;          were already being investigated
  ;;; Effect : simplification of the literal arr1 = arr2
  ;;; Value  : if simplification of arr1 = arr2 was successful the simplified literal, else either the
  ;;;          original literal or NIL depending on EG*NON.SYMBOLIC

  (COND ((AND EG*NON.SYMBOLIC (NOT (AND ARR1 ARR2))) NIL)
	(T (LET ((SORT (DA-TERM.SORT ARR1))
		 RESULT1 RESULT2 RESULT3 INDEX)
	     (COND ((AND (EQ (DA-TERM.SYMBOL ARR1) (DA-TERM.SYMBOL ARR2))
			 (NULL (DA-TERM.TERMLIST ARR1))
			 (NULL (DA-TERM.TERMLIST ARR2)))
		    (DA-LITERAL.TRUE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR1) (DP-FUNCTION.ARRAY.INIT SORT))
			   (EQ (DA-TERM.SYMBOL ARR2) (DP-FUNCTION.ARRAY.INIT SORT))
			   (EG=LITERAL.IS.TRUE (SETQ RESULT1 (EG=EQUAL (FIRST (DA-TERM.TERMLIST ARR1))
								       (FIRST (DA-TERM.TERMLIST ARR2)) ATTRIBUTES)))))
		    (DA-LITERAL.TRUE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR1) (DP-FUNCTION.ARRAY.INIT SORT))
			   (EQ (DA-TERM.SYMBOL ARR2) (DP-FUNCTION.ARRAY.INIT SORT))
			   (EG=LITERAL.IS.FALSE RESULT1)))
		    (DA-LITERAL.FALSE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR1) (DP-FUNCTION.ARRAY.UPDATE SORT))
			   (SETQ INDEX (SECOND (DA-TERM.TERMLIST ARR1)))
			   (SOME #'(LAMBDA (SUBTERM)
				     (EG=LITERAL.IS.TRUE (EG=EQUAL SUBTERM INDEX ATTRIBUTES)))
				 INDICES.ARR1)))
		    (EG=ARRAY.EQUAL (FIRST (DA-TERM.TERMLIST ARR1)) ARR2 ATTRIBUTES INDICES.ARR1 INDICES.ARR2))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR1) (DP-FUNCTION.ARRAY.UPDATE SORT))
			   (SETQ RESULT1 (EVERY #'(LAMBDA (SUBTERM)
						    (EG=LITERAL.IS.FALSE (EG=EQUAL SUBTERM INDEX ATTRIBUTES)))
						INDICES.ARR1))
			   (EG=LITERAL.IS.TRUE (SETQ RESULT2 (EG=EQUAL (EG=EVAL.ARRAY.SELECT ARR2 INDEX) (THIRD (DA-TERM.TERMLIST ARR1))
								       ATTRIBUTES)))))
		    (EG=ARRAY.EQUAL (FIRST (DA-TERM.TERMLIST ARR1)) ARR2 ATTRIBUTES (CONS INDEX INDICES.ARR1) INDICES.ARR2))

		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR1) (DP-FUNCTION.ARRAY.UPDATE SORT))
			   RESULT2
			   (EG=LITERAL.IS.FALSE RESULT2)))
		    (DA-LITERAL.FALSE))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR1) (DP-FUNCTION.ARRAY.INIT SORT))
			   (EQ (DA-TERM.SYMBOL ARR2) (DP-FUNCTION.ARRAY.UPDATE SORT))
			   (SETQ INDEX (SECOND (DA-TERM.TERMLIST ARR2)))
			   (SOME #'(LAMBDA (SUBTERM)
				     (EG=LITERAL.IS.TRUE (EG=EQUAL SUBTERM INDEX ATTRIBUTES)))
				 INDICES.ARR2)))
		    (EG=ARRAY.EQUAL ARR1 (FIRST (DA-TERM.TERMLIST ARR2)) ATTRIBUTES INDICES.ARR1 INDICES.ARR2))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR1) (DP-FUNCTION.ARRAY.INIT SORT))
			   (EQ (DA-TERM.SYMBOL ARR2) (DP-FUNCTION.ARRAY.UPDATE SORT))
			   (SETQ RESULT1 (EVERY #'(LAMBDA (SUBTERM)
						    (EG=LITERAL.IS.FALSE (EG=EQUAL SUBTERM INDEX ATTRIBUTES)))
						INDICES.ARR2))
			   (SOME #'(LAMBDA (SUBTERM)
				     (EG=LITERAL.IS.TRUE (EG=EQUAL INDEX SUBTERM ATTRIBUTES)))
				 INDICES.ARR1)))
		    (EG=ARRAY.EQUAL ARR1 (FIRST (DA-TERM.TERMLIST ARR2)) ATTRIBUTES INDICES.ARR1 (CONS INDEX INDICES.ARR2)))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR1) (DP-FUNCTION.ARRAY.INIT SORT))
			   (EQ (DA-TERM.SYMBOL ARR2) (DP-FUNCTION.ARRAY.UPDATE SORT))
			   RESULT1
			   (SETQ RESULT2 (EVERY #'(LAMBDA (SUBTERM)
						    (EG=LITERAL.IS.FALSE (EG=EQUAL INDEX SUBTERM ATTRIBUTES)))
						INDICES.ARR1))
			   (EG=LITERAL.IS.TRUE (SETQ RESULT2 (EG=EQUAL (FIRST (DA-TERM.TERMLIST ARR1))
								       (THIRD (DA-TERM.TERMLIST ARR2)) ATTRIBUTES)))))
		    (EG=ARRAY.EQUAL ARR1 (FIRST (DA-TERM.TERMLIST ARR2)) ATTRIBUTES INDICES.ARR1 (CONS INDEX INDICES.ARR2)))
		   ((LET ((EG*NON.SYMBOLIC T))
		      (AND (EQ (DA-TERM.SYMBOL ARR1) (DP-FUNCTION.ARRAY.INIT SORT))
			   (EQ (DA-TERM.SYMBOL ARR2) (DP-FUNCTION.ARRAY.UPDATE SORT))
			   RESULT1
			   RESULT2
			   (EG=LITERAL.IS.FALSE RESULT3)))
		    (DA-LITERAL.FALSE))
		   (EG*NON.SYMBOLIC NIL)
		   (T (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DP-PREDICATE.EQUALITY)
					 (LIST ARR1 ARR2) ATTRIBUTES)))))))
		  
	  
	   
