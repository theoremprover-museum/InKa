;;; -*- Package: INKA; Syntax: Common-lisp; -*-

;;; 22.11.92 dh EXP=NORMALIZE.LITERAL                baseconstants eliminated
;;; 25.01.93 DH EXP=IDENTIFY.STRUCTURE.PARTS         non-free datatypes considered.


(IN-PACKAGE :INKA)

;;;;;========================================================================================================
;;;;; Chapter One
;;;;; -----------
;;;;;
;;;;; Top-level-functions of the expression analyzer.
;;;;;========================================================================================================


(DEFUN EXP-DEFINITION.ANALYZE (FORMULA)
  
  ;;; Edited:  28-Jan-87 by DH
  ;;; Input:   a definition-task specified by the deduction module.
  ;;; Effect:  the definition is checked for completeness and uniqueness.
  ;;; Value:   the modified task, if the definition is leftcomplete and unique or
  ;;;          NIL else.

  (LET (FORMULAS)
    (MULTIPLE-VALUE-BIND (DEFINITION SYMBOL PARAMETERS) (VALUES-LIST FORMULA)
      (SETQ DEFINITION (EXP=CREATE.CASE.ANALYSIS.TREE DEFINITION (MAPCAR #'(LAMBDA (X) (DA-TERM.CREATE X)) PARAMETERS)))
      (MULTIPLE-VALUE-SETQ (DEFINITION FORMULAS)
	(EXP=EXAMINE.DEFINITION DEFINITION FORMULAS))
      (COND ((EXP=CREATE.AND.PROVE.NEW.TASKS FORMULAS SYMBOL PARAMETERS)
	     (LIST (EXP=DEFINITION.DELETE.UNSPEC.CASES DEFINITION) SYMBOL PARAMETERS))
	    (T (VALUES NIL (LIST 1 0 (FORMAT NIL
					     "The algorithm ~A is not correct, i.e., it is not unique or not complete. ~%Hence, the algorithm is refused."
					     SYMBOL)) NIL))))))


(DEFUN EXP-INDUCTION.ANALYZE (PARAMETERS DEFINITION)
  
  ;;; Edited:  28-Jan-87 by DH
  ;;; Input:   a list of parameterts and a definition task
  ;;; Effect:  \verb$DEFINITION$ is checked for completeness and uniqueness.
  ;;; Value:   the modified task, if \verb$DEFINITION$ is leftcomplete and unique or
  ;;;          NIL else.

  (LET (FORMULAS)
    (SETQ DEFINITION (EXP=CREATE.CASE.ANALYSIS.TREE DEFINITION 
						    (MAPCAR #'(LAMBDA (X) (DA-TERM.CREATE X))
							    PARAMETERS)))
    (MULTIPLE-VALUE-SETQ (DEFINITION FORMULAS) (EXP=EXAMINE.DEFINITION DEFINITION NIL))
    (COND ((NULL FORMULAS) DEFINITION))))


(DEFUN EXP=DEFINITION.DELETE.UNSPEC.CASES (DEFINITION)

  (COND ((null definition) nil)
	((DA-GTERM.DEF.IS.VALUE DEFINITION) DEFINITION)
	(T (LET (NEW.VALUE DEF.TERMS)
	     (SETQ DEF.TERMS (MAPCAN #'(LAMBDA (DEF.TERM)
					 (COND ((NULL (DA-GTERM.DEF.VALUE DEF.TERM)) NIL)
					       ((SETQ NEW.VALUE (EXP=DEFINITION.DELETE.UNSPEC.CASES (DA-GTERM.DEF.VALUE DEF.TERM)))
						(SETF (DA-GTERM.DEF.VALUE DEF.TERM) NEW.VALUE)
						(LIST DEF.TERM))))
				     (DA-GTERM.TERMLIST DEFINITION)))
	     (COND ((NULL DEF.TERMS) NIL)
		   (T (DA-GTERM.CREATE 'AND DEF.TERMS NIL (DA-GTERM.ATTRIBUTES DEFINITION))))))))


(DEFUN EXP=CREATE.CASE.ANALYSIS.TREE (DEFINITION PARAMETER.BOUND.TERMS)

  ;;; Edited  :  11-4-89
  ;;; Input   :  a definition, a list of literals, a list of variables,
  ;;;            a function/predicate symbol and a list of its formal parameters.
  ;;; Effect  :  Builds up a case analysis for the given definition.
  ;;; Value   :  a multiple value (definition . tasks), where definition is the modified definition 
  ;;;            structured by a case analysis and tasks is a property list of of formulas, which have
  ;;;            to be proven, if the definition is correct, or denote missing cases.

  (LET (DIFF ALTS)
    (COND				   ; no def.terms anymore or there is one with empty conditions
      ((EXP=DEFINITION.IS.BASE.CASE DEFINITION)
       DEFINITION)
      ((SETQ DIFF (EXP=REPRESENTIVE.DEF.TERM (DA-GTERM.TERMLIST DEFINITION)))
       (SETQ ALTS (REMOVE-IF #'(LAMBDA (DEF.TERM) 
				 (OR (EQ (DA-GTERM.DEF.VALUE DEF.TERM) DIFF)
				     (EQ (DA-GTERM.DEF.CONDITION DEF.TERM) 'OTHERWISE)))
			     (DA-GTERM.TERMLIST DEFINITION)))
       (SETQ DIFF (EXP=CREATE.CASE.ANALYSIS.TREE DIFF PARAMETER.BOUND.TERMS))
       (COND (ALTS (SETQ DIFF (LIST 'ALTERNATIVES DIFF ALTS))))
       DIFF)

					   ; structural analysis of the def.terms
      ((SETQ DIFF (EXP=IDENTIFY.STRUCTURE.PARTS DEFINITION PARAMETER.BOUND.TERMS))
       (EXP=INSERT.STRUCTURAL DEFINITION DIFF PARAMETER.BOUND.TERMS NIL))

					   ; analysis of tautologies.
      ((SETQ DIFF (EXP=IDENTIFY.NEGATED.LITERALS DEFINITION))
       (EXP=INSERT.NON.STRUCTURAL DEFINITION DIFF PARAMETER.BOUND.TERMS))
	  
					   ; structural analysis of non parameter bound terms
      ((SETQ DIFF (EXP=IDENTIFY.STRUCTURE.PARTS DEFINITION 'IGNORE))
       (EXP=INSERT.STRUCTURAL DEFINITION DIFF PARAMETER.BOUND.TERMS 'IGNORE))

      (T (MAPC #'(LAMBDA (DEF.TERM)
		   (SETF (DA-GTERM.DEF.VALUE DEF.TERM)
			 (EXP=CREATE.CASE.ANALYSIS.TREE (DA-GTERM.DEF.VALUE DEF.TERM) PARAMETER.BOUND.TERMS)))
	       (DA-GTERM.TERMLIST DEFINITION))
	 DEFINITION))))



;;;;;========================================================================================================
;;;;; Chapter Two
;;;;; -----------
;;;;;
;;;;; Functions to detect different equivalence classes of if.then.cases.
;;;;;========================================================================================================


(DEFUN EXP=IDENTIFY.STRUCTURE.PARTS (DEFINITION PARAMETER.BOUND.TERMS)
  
  ;;; Edited:     27-Jan-87
  ;;; Input:      a definition and a list of parameter bound terms or the atom IGNORE
  ;;; Effect:     if there is a match-literal in the condition-slot of one def.terms then the 
  ;;;             case analysis is split up into the cases denoted by the structure definition of the 
  ;;;             sort of the left side of the match-literal.
  ;;; Value:      the term, which is the left term of the match literal.
  
  (SOME #'(LAMBDA (DEF.TERM)
	     (COND ((NEQ 'OTHERWISE (DA-GTERM.DEF.CONDITION DEF.TERM))
		    (CAR (EXP=SOME.FORMULA (DA-GTERM.DEF.CONDITION DEF.TERM)
					   #'(LAMBDA (LITERAL)
					       (COND ((AND (DA-LITERAL.IS LITERAL)
							   (DA-LITERAL.TERMLIST LITERAL)
							   (MEMBER 'DISJUNCT.RANGE 
								   (DA-SORT.ATTRIBUTES 
								    (DA-TERM.SORT (CAR (DA-LITERAL.TERMLIST 
											LITERAL)))))
							   (DA-LITERAL.DENOTES.MATCH LITERAL)
							   (OR (AND (EQ PARAMETER.BOUND.TERMS 'IGNORE)
								    (NEQ (DA-TERM.SYMBOL (CAR (DA-LITERAL.TERMLIST LITERAL)))
									 (DA-TERM.SYMBOL (SECOND (DA-LITERAL.TERMLIST LITERAL)))))
							       (AND (NEQ PARAMETER.BOUND.TERMS 'IGNORE)
								    (MEMBER (CAR (DA-LITERAL.TERMLIST LITERAL)) PARAMETER.BOUND.TERMS
									    :TEST 'UNI-TERM.ARE.EQUAL))))
						      (CAR (DA-LITERAL.TERMLIST LITERAL))))))))))
	(DA-GTERM.TERMLIST DEFINITION)))


(DEFUN EXP=IDENTIFY.NEGATED.LITERALS (DEFINITION)

  ;;; Edited:     27-Jan-87
  ;;; Input:      a definition
  ;;; Effect:     if there are at least two def.terms, condition-slots of which contain complementary 
  ;;;             literals, then the case analysis is split up into the cases denoted by these literals.
  ;;; Value:      the literal.

  (LET (RESULT)
    (SMAPL #'(LAMBDA (DEF.TERMS)
	       (COND ((NEQ 'OTHERWISE (DA-GTERM.DEF.CONDITION (CAR DEF.TERMS)))
		      (SOME #'(LAMBDA (LITERAL)
				(COND ((DA-LITERAL.IS LITERAL)
				       (SETQ RESULT (EXP=IDENTIFY.NEGATED.LITERALS.1 LITERAL (CDR DEF.TERMS))))))
			    (DA-GTERM.DEF.CONDITION (CAR DEF.TERMS))))))
	   #'(LAMBDA (DEF.TERMS) (COND ((NULL RESULT) (CDR DEF.TERMS))))
	   (DA-GTERM.TERMLIST DEFINITION))
    RESULT))


(DEFUN EXP=IDENTIFY.NEGATED.LITERALS.1 (LITERAL DEF.TERMS)
  
  ;;; Edited:     27-Jan-87
  ;;; Input:      a literal and a list of def.terms
  ;;; Effect:     searches for a def.term, which condition-slot contains a literal complementary
  ;;;             to LITERAL.
  ;;; Value:      this literal.

  (SOME #'(LAMBDA (DEF.TERM.2)
	    (COND ((NEQ 'OTHERWISE (DA-GTERM.DEF.CONDITION DEF.TERM.2))
		   (FIND-IF #'(LAMBDA (LITERAL.2)
			        (UNI-LITERAL.ARE.EQUAL LITERAL LITERAL.2 NIL 'OPPOSITE))
			    (DA-GTERM.DEF.CONDITION DEF.TERM.2)))))
        DEF.TERMS))


;;;;;========================================================================================================
;;;;; Chapter Three:
;;;;; --------------
;;;;;
;;;;; Functions to divide the if.then.cases into the different equivalence classes.
;;;;;========================================================================================================


(DEFUN EXP=INSERT.STRUCTURAL (DEFINITION TERM PARAMETER.BOUND.TERMS FLAG)

  ;; Effect: the definition is divided into sublists according to ALTERNATIVES.
  ;;         Matchliterals for TERM are removed from the def.terms conditions and normalized,
  ;; Value:  a multiple value ALTERNATIVES / parameter.bound.terms, where ALTERNATIVES is a list of 
  ;;         lists (CONDITION.IF.THEN.CASES) and parameter.bound.terms is a list of currently bound
  ;;         variables (as in COMPILE)

  (DA-GTERM.CREATE 'AND
		   (MAPCAR #'(LAMBDA (STRUC.TERM)
			       (LET (DEF.TERMS)
				 (MAPC #'(LAMBDA (DEF.TERM)
					   (cond ((setq def.term (EXP=INSERT.STRUCTURAL.IN.DEF.TERM DEF.TERM TERM STRUC.TERM))
						  (push def.term DEF.TERMS))))
				       (DA-GTERM.TERMLIST DEFINITION))
				 (DA-GTERM.DEF.CREATE
				   (EXP=CREATE.CASE.ANALYSIS.TREE (EXP=REPRESENTIVE.DEF.CREATE DEF.TERMS)
								  (APPEND (COND ((NULL FLAG) (DA-TERM.TERMLIST STRUC.TERM)))
									  PARAMETER.BOUND.TERMS))
				   (LIST (DA-LITERAL.CREATE (DA-SIGN.MINUS)
							    (DA-PREDICATE.EQUALITY)
							    (LIST (DA-TERM.COPY TERM) STRUC.TERM)
							    (COND ((NULL FLAG) (LIST 'KIND (LIST 'MATCH)))))))))
			   (DA-SORT.CREATE.ALL.STRUCTURE.TERMS TERM NIL))
		   NIL (cond ((member 'disjunct.range (da-sort.attributes (da-term.sort term)))
			      (list 'up.checked t 'cp.checked t))
			     (t (list 'cp.checked t)))))


(DEFUN EXP=INSERT.STRUCTURAL.IN.DEF.TERM (DEF.TERM TERM CONS.TERM)

  (LET (RESULT VALUE CONDITION)
    (COND ((EQ (DA-GTERM.DEF.CONDITION DEF.TERM) 'OTHERWISE)
	   (COND ((EXP=DEFINITION.IS.BASE.CASE (DA-GTERM.DEF.VALUE DEF.TERM)) 
		  (DA-GTERM.DEF.CREATE (da-gterm.copy (DA-GTERM.DEF.VALUE DEF.TERM)) 'OTHERWISE))
		 ((SETQ VALUE (MAPCAN #'(LAMBDA (SUB.DEF.TERM)
					  (COND ((SETQ RESULT (EXP=INSERT.STRUCTURAL.IN.DEF.TERM SUB.DEF.TERM TERM CONS.TERM))
						 (LIST RESULT))))
				      (DA-GTERM.TERMLIST (DA-GTERM.DEF.VALUE DEF.TERM))))
		  (DA-GTERM.DEF.CREATE (EXP=REPRESENTIVE.DEF.CREATE VALUE)
				       (DA-GTERM.DEF.CONDITION DEF.TERM)))))
	  (T (SETQ CONDITION (EXP=INSERT.STRUCTURAL.REPLACE.TERM (DA-GTERM.DEF.CONDITION DEF.TERM) TERM CONS.TERM))
	     (COND ((NEQ CONDITION 'FAIL)
		    (cond ((EXP=DEFINITION.IS.BASE.CASE (DA-GTERM.DEF.VALUE DEF.TERM))
			   (DA-GTERM.DEF.CREATE (DA-GTERM.DEF.VALUE DEF.TERM) CONDITION))
			  ((setq value (MAPCAN #'(LAMBDA (SUB.DEF.TERM)
						   (COND ((SETQ RESULT (EXP=INSERT.STRUCTURAL.IN.DEF.TERM 
									SUB.DEF.TERM TERM CONS.TERM))
							  (LIST RESULT))))
					       (DA-GTERM.TERMLIST (DA-GTERM.DEF.VALUE DEF.TERM))))
			   (DA-GTERM.DEF.CREATE (EXP=REPRESENTIVE.DEF.CREATE VALUE) CONDITION)))))))))


(DEFUN EXP=INSERT.STRUCTURAL.REPLACE.TERM (CONDITION TERM CONS.TERM)

  (LET (RESULT)
    (SOME #'(LAMBDA (GTERM)
	      (SETQ GTERM (EG-EVAL (UNI-TERMSUBST.APPLY
				    (UNI-termsubst.create.parallel (cons term (da-gterm.termlist cons.term))
								   (cons CONS.TERM (da-gterm.termlist cons.term)))
				    GTERM)))
	      (COND ((DA-FORMULA.IS.FALSE GTERM) NIL)
		    ((DA-FORMULA.IS.TRUE GTERM) (SETQ RESULT 'FAIL))
		    (T (SETQ RESULT (APPEND RESULT (DA-FORMULA.JUNCTION.OPEN 'OR (EXP=NORMALIZE.GTERM GTERM)))) NIL)))
	  CONDITION)
    RESULT))


(DEFUN EXP=REPRESENTIVE.DEF.CREATE (DEF.TERMS)

  ;;; Input:  a list of definition cases
  ;;; Effect: see value.
  ;;; Value:  a partial definition. If there is only one case with no conditions then the value of that case. If
  ;;;         only an OTHERWISE-case is specified the value of that case. Otherwise, the conjunction of all cases.

  (LET (POS.DEF.TERMS OTHERWISE.DEF.TERM)
       (SETQ POS.DEF.TERMS (REMOVE-IF #'(LAMBDA (DEF.TERM)
						(COND ((EQ (DA-GTERM.DEF.CONDITION DEF.TERM) 'OTHERWISE)
						       (SETQ OTHERWISE.DEF.TERM DEF.TERM))))
				      DEF.TERMS))
       (COND ((AND POS.DEF.TERMS (NULL (CDR POS.DEF.TERMS))
		   (NULL (DA-GTERM.DEF.CONDITION (CAR POS.DEF.TERMS))))
	      (DA-GTERM.DEF.VALUE (CAR POS.DEF.TERMS)))
	     ((AND OTHERWISE.DEF.TERM (NULL POS.DEF.TERMS))
	      (DA-GTERM.DEF.VALUE OTHERWISE.DEF.TERM))
	     ((NULL POS.DEF.TERMS) (DA-GTERM.CREATE 'NOT.SPECIFIED NIL))
	     (T (DA-GTERM.CREATE 'AND DEF.TERMS)))))


(DEFUN EXP=INSERT.NON.STRUCTURAL (DEFINITION LITERAL PARAMETER.BOUND.TERMS)

  ;; Effect: the definition is divided into sublists according to ALTERNATIVES.
  ;;         Matchliterals for TERM are removed from the def.terms conditions and normalized,
  ;; Value:  a multiple value ALTERNATIVES / parameter.bound.terms, where ALTERNATIVES is a list of 
  ;;         lists (CONDITION.IF.THEN.CASES) and parameter.bound.terms is a list of currently bound
  ;;         variables (as in COMPILE)

  (DA-GTERM.CREATE 'AND
		   (MAPCAR #'(LAMBDA (LITERAL)
			       (LET (DEF.TERMS)
				 (MAPC #'(LAMBDA (DEF.TERM)
					   (cond ((setq def.term (EXP=INSERT.NON.STRUCTURAL.IN.DEF.TERM DEF.TERM LITERAL))
						  (push def.term DEF.TERMS))))
				       (DA-GTERM.TERMLIST DEFINITION))
				 (DA-GTERM.DEF.CREATE
				   (EXP=CREATE.CASE.ANALYSIS.TREE (EXP=REPRESENTIVE.DEF.CREATE DEF.TERMS)
								  PARAMETER.BOUND.TERMS)
				   (LIST LITERAL))))
			   (LIST LITERAL (DA-LITERAL.NEGATE (DA-LITERAL.COPY LITERAL))))
		   NIL (LIST 'cp.CHECKED T 'up.checked t)))



(DEFUN EXP=INSERT.NON.STRUCTURAL.IN.DEF.TERM (DEF.TERM LITERAL)

  (LET (RESULT VALUE CONDITION)
    (COND ((EQ (DA-GTERM.DEF.CONDITION DEF.TERM) 'OTHERWISE)
	   (COND ((EXP=DEFINITION.IS.BASE.CASE (DA-GTERM.DEF.VALUE DEF.TERM)) DEF.TERM)
		 ((SETQ VALUE (MAPCAN #'(LAMBDA (SUB.DEF.TERM)
					  (COND ((SETQ RESULT (EXP=INSERT.NON.STRUCTURAL.IN.DEF.TERM SUB.DEF.TERM LITERAL))
						 (LIST RESULT))))
				      (DA-GTERM.TERMLIST (DA-GTERM.DEF.VALUE DEF.TERM))))
		  (DA-GTERM.DEF.CREATE (EXP=REPRESENTIVE.DEF.CREATE VALUE)
				       (DA-GTERM.DEF.CONDITION DEF.TERM)))))
	  (T (SETQ CONDITION (EXP=INSERT.NON.STRUCTURAL.REPLACE.LITERAL (DA-GTERM.DEF.CONDITION DEF.TERM) LITERAL))
	     (COND ((NEQ CONDITION 'FAIL)
		    (cond ((EXP=DEFINITION.IS.BASE.CASE (DA-GTERM.DEF.VALUE DEF.TERM))
			   (DA-GTERM.DEF.CREATE (DA-GTERM.DEF.VALUE DEF.TERM) CONDITION))
			  ((setq value (MAPCAN #'(LAMBDA (SUB.DEF.TERM)
						   (COND ((SETQ RESULT (EXP=INSERT.NON.STRUCTURAL.IN.DEF.TERM SUB.DEF.TERM LITERAL))
							  (LIST RESULT))))
					       (DA-GTERM.TERMLIST (DA-GTERM.DEF.VALUE DEF.TERM))))
			   (DA-GTERM.DEF.CREATE (EXP=REPRESENTIVE.DEF.CREATE VALUE) CONDITION)))))))))


(DEFUN EXP=INSERT.NON.STRUCTURAL.REPLACE.LITERAL (CONDITION LITERAL)

  (LET (RESULT SUB.TERM)
    (SOME #'(LAMBDA (GTERM)
	      (MAPC #'(LAMBDA (TAF)
			(SETQ SUB.TERM (DA-ACCESS TAF GTERM))
			(SETQ GTERM (DA-REPLACE TAF GTERM
						(COND ((EQ (DA-LITERAL.SIGN LITERAL)
							   (DA-LITERAL.SIGN SUB.TERM))
						       (DA-LITERAL.FALSE))
						      (T (DA-LITERAL.TRUE))))))
		    (DA-GTERM.LITERALS.WITH.PROPERTY GTERM
		     #'(LAMBDA (OTHER.LIT) (UNI-LITERAL.ARE.EQUAL OTHER.LIT LITERAL NIL 'IGNORE))))
	      (SETQ GTERM (EG-EVAL GTERM))
	      (COND ((DA-FORMULA.IS.FALSE GTERM) NIL)
		    ((DA-FORMULA.IS.TRUE GTERM) (SETQ RESULT 'FAIL))
		    (T (SETQ RESULT (APPEND RESULT (DA-FORMULA.JUNCTION.OPEN 'OR (EXP=NORMALIZE.GTERM GTERM)))) NIL)))
	  CONDITION)
    RESULT))

  

;;;;;========================================================================================================
;;;;; Chapter Four:
;;;;; -------------
;;;;;
;;;;; Examination of the leaves of the generated tree.
;;;;;========================================================================================================


(DEFUN EXP=EXAMINE.DEFINITION (DEFINITION CONDITION &OPTIONAL FORMULAS)

  (LET (NEW.DEF)
    (COND ((AND (CONSP DEFINITION) (EQ (CAR DEFINITION) 'ALTERNATIVES))
	   (mapc #'(lambda (def)
		     (push (cons (append condition (DA-GTERM.DEF.CONDITION DEF))
				 (da-literal.false))
			   (getf formulas 'UP)))
		 (third definition))
	   (MULTIPLE-VALUE-SETQ (DEFINITION FORMULAS)
	     (EXP=EXAMINE.DEFINITION (SECOND DEFINITION) CONDITION FORMULAS)))
	  ((EQ (DA-GTERM.SYMBOL DEFINITION) 'UNSPEC))
	  ((OR (EQ (DA-GTERM.SYMBOL DEFINITION) 'NOT.SPECIFIED) (NULL DEFINITION))
	   (PUSH (CONS CONDITION (DA-LITERAL.FALSE)) (GETF FORMULAS 'CP))
	   (SETQ DEFINITION NIL))
	  ((DA-GTERM.DEF.IS.VALUE DEFINITION))
	  (T (MAPC #'(LAMBDA (DEF.TERM)
		       (MULTIPLE-VALUE-SETQ (NEW.DEF FORMULAS)
					    (EXP=EXAMINE.DEFINITION
					     (DA-GTERM.DEF.VALUE DEF.TERM)
					     (APPEND CONDITION
						     (COND ((EQ 'OTHERWISE (DA-GTERM.DEF.CONDITION DEF.TERM))
							    (exp=expand.otherwise.case DEFINITION))
							   (T  (DA-GTERM.DEF.CONDITION DEF.TERM))))
					     FORMULAS))
		       (SETF (DA-GTERM.DEF.VALUE DEF.TERM) NEW.DEF))
		   (DA-GTERM.TERMLIST DEFINITION))
	     (MULTIPLE-VALUE-SETQ (DEFINITION FORMULAS) (EXP=EXAMINE.CASE.ANALYSIS DEFINITION CONDITION FORMULAS))))
    (VALUES DEFINITION FORMULAS)))


(defun exp=expand.otherwise.case (definition)

  ;;; Input:  a definition
  ;;; Value:  returns a condition for the otherwise-case.

  (mapcan #'(lambda (def.value)
	      (cond ((consp (da-gterm.def.condition def.value))
		     (mapcar #'(lambda (gterm)
				 (da-formula.negate gterm))
			     (da-gterm.def.condition def.value)))))
	  (DA-GTERM.TERMLIST definition)))


(DEFUN EXP=EXAMINE.CASE.ANALYSIS (DEFINITION CONDITION FORMULAS)

  ;;; Input:   a definition-case analysis, a list of literals and a list of formulas (gterms)
  ;;; Effect:  checks whether the top-level case analysis of DEFINITION is complete and unique.
  ;;;          In case these properties are not decidable tasks are generated that postulate
  ;;;          the desired properties.
  ;;;          Also, the meta-symbols OTHERWISE and UNSPEC are removed from the definition.
  ;;; Value:   the modified definition and the list of generated tasks (including FORMULAS).

  (LET ((OTHERWISE.CASE (FIND-IF #'(LAMBDA (DEF.TERM)
				     (EQ 'OTHERWISE (DA-GTERM.DEF.CONDITION DEF.TERM)))
				 (DA-GTERM.TERMLIST DEFINITION)))
	def.terms)
    (cond ((not (getf (da-gterm.attributes definition) 'cp.checked))
           ;;; Check for completeness:
	   (COND ((NOT OTHERWISE.CASE)
		  (PUSH (CONS CONDITION
			      (DA-FORMULA.JUNCTION.CLOSURE
			       'OR (MAPCAR #'(LAMBDA (DEF.TERM) 
					       (DA-FORMULA.JUNCTION.CLOSURE
						'AND (MAPCAR #'(LAMBDA (LIT)
								 (DA-FORMULA.NEGATE (DA-GTERM.COPY LIT)))
							     (DA-GTERM.DEF.CONDITION DEF.TERM))))
					   (DA-GTERM.TERMLIST DEFINITION))))
			(GETF FORMULAS 'CP))))))
    (cond ((not (getf (da-gterm.attributes definition) 'up.checked))
	    ;;; Check for uniqueness:
	   (SETQ DEF.TERMS (REMOVE OTHERWISE.CASE (DA-GTERM.TERMLIST DEFINITION)))
	   (COND ((CDR DEF.TERMS)
		  (MAPL #'(LAMBDA (DEF.TERMS)
			    (MAPC #'(LAMBDA (DEF.TERM)
				      (PUSH (CONS CONDITION
						  (DA-FORMULA.JUNCTION.CLOSURE 
						   'OR (LIST
							(DA-FORMULA.JUNCTION.CLOSURE 
							 'OR (MAPCAR #'DA-GTERM.COPY
								     (DA-GTERM.DEF.CONDITION (CAR DEF.TERMS))))
							(DA-FORMULA.JUNCTION.CLOSURE
							 'OR (MAPCAR #'DA-GTERM.COPY
								     (DA-GTERM.DEF.CONDITION DEF.TERM))))))
					    (GETF FORMULAS 'UP)))
				  (CDR DEF.TERMS)))
			DEF.TERMS)))
	   (COND (OTHERWISE.CASE (SETQ DEFINITION (EXP=EXPAND.OTHERWISE DEFINITION DEF.TERMS OTHERWISE.CASE))))))
    (SETQ DEFINITION (EXP=REMOVE.UNSPEC.CASES DEFINITION))
    (VALUES DEFINITION FORMULAS)))


(DEFUN EXP=EXPAND.OTHERWISE (DEFINITION DEF.TERMS OTHERWISE.CASE)

  ;;; Input:   a definition-case analysis, the list of cases exept the OTHERWISE-case and that OTHERWISE-case
  ;;; Effect:  replaces the OTHERWISE-case in DEFINITION by a set of cases denoting the complement of the
  ;;;          conditions of DEF.TERMS.
  ;;; Value:   the modified DEFINITION.

  (LET ((CASES (DA-FORMULA.JUNCTION.CLOSURE
		'AND (MAPCAR #'(LAMBDA (DEF.TERM)
			        (DA-FORMULA.JUNCTION.CLOSURE 'OR (DA-GTERM.DEF.CONDITION DEF.TERM)))
			    DEF.TERMS)))
	(OTHERWISE.VALUE (DA-GTERM.DEF.VALUE OTHERWISE.CASE)))
       (SETQ CASES (NORM-NORMALIZE.TO.DNF (DA-GTERM.COPY CASES)))
       (SETF (DA-GTERM.TERMLIST DEFINITION)
	     (NCONC DEF.TERMS (MAPCAR #'(LAMBDA (CASE)
					  (DA-GTERM.DEF.CREATE (DA-GTERM.COPY OTHERWISE.VALUE)
							       (MAPCAR #'(LAMBDA (LIT) 
									   (NORM-NORMALIZE.WITHOUT.QUANTIFIER
									    (DA-FORMULA.NEGATE LIT)))
								       CASE)))
				      CASES)))
       DEFINITION))


(DEFUN EXP=REMOVE.UNSPEC.CASES (DEFINITION)

  ;;; Input:   a definition-case analysis
  ;;; Effect:  removes all cases with UNSPEC-value from the set of cases and
  ;;;          collects the corresponding conditions of those cases in an attribute
  ;;;          'UNSPEC.CASES of DEFINITION.
  ;;; Value:   the modified DEFINITION.

  (SETF (DA-GTERM.TERMLIST DEFINITION)
	(REMOVE-IF #'(LAMBDA (DEF.TERM)
		       (COND ((AND (DA-GTERM.DEF.VALUE DEF.TERM)
				   (EQ 'UNSPEC (DA-GTERM.SYMBOL (DA-GTERM.DEF.VALUE DEF.TERM))))
			      (PUSH (DA-GTERM.DEF.CONDITION DEF.TERM)
				    (GETF (DA-GTERM.ATTRIBUTES DEFINITION) 'UNSPEC.CASES)))))
		   (DA-GTERM.TERMLIST DEFINITION)))
  DEFINITION)



;;;;;========================================================================================================
;;;;; Chapter Five:
;;;;; -------------
;;;;;
;;;;; Functions for normalizing match literals.
;;;;;========================================================================================================



(DEFUN EXP=NORMALIZE.LITERAL (LITERAL)
  
  ;;; Edited:    13-feb-89 mp
  ;;; Input:     a match literal s = t and a list of parameter bound terms
  ;;; Effect:    s = t is normalized according to the following rules:
  ;;;            1. the sort of t is not equal to the sort of s:
  ;;;               if t is not the index term t' of s then t is replaced by t' and t' = t is created,
  ;;;       or   2. the sort of t is equal to the sort of x and t is a term built up with a constructor 
  ;;;               function c, then if t is not the constructor term t' of s then t is replaced by t'
  ;;;               and a list of literals gi(t') = gi(t) for all i is generated
  ;;; Value:     a multiple value (literal new_literals)
  
  (LET* ((TERM (SECOND (DA-LITERAL.TERMLIST LITERAL)))
	 (BOUND.TERM (CAR (DA-LITERAL.TERMLIST LITERAL)))
	 (SYMBOL (DA-TERM.SYMBOL TERM)) NEW.LITS WISHED.TERM
	 (BOUND.TERM.SORT (DA-TERM.SORT BOUND.TERM)) (TERMSORT (DA-TERM.SORT TERM)))
    (COND ((NEQ BOUND.TERM.SORT TERMSORT)
	   (SETQ WISHED.TERM (DA-SORT.INDEX.TERM BOUND.TERM (DA-SORT.FIND.SUPER.SORT (DA-SORT.BASE.SORTS BOUND.TERM.SORT) TERMSORT)))
	   (COND ((NOT (UNI-TERM.ARE.EQUAL WISHED.TERM TERM))
		  (PUSH (EXP=EXCHANGE.TERM LITERAL WISHED.TERM TERM) NEW.LITS))))
	  ((MEMBER SYMBOL (DA-SORT.CONSTRUCTOR.FCTS BOUND.TERM.SORT))
	   (SETQ WISHED.TERM (DA-SORT.CONSTRUCTOR.TERM BOUND.TERM SYMBOL))
	   (MAPC #'(LAMBDA (SUB.TERM WISHED.SUB.TERM)
		     (COND ((NOT (UNI-TERM.ARE.EQUAL SUB.TERM WISHED.SUB.TERM))
			    (PUSH (EXP=EXCHANGE.TERM LITERAL WISHED.SUB.TERM SUB.TERM)
				  NEW.LITS))))
		 (DA-TERM.TERMLIST TERM)
		 (DA-TERM.TERMLIST WISHED.TERM))))
    NEW.LITS))


(DEFUN EXP=EXCHANGE.TERM (LITERAL NEW.TERM OLD.TERM)

  ;;; Edited:    26-Jan-87 by DH
  ;;; Input:     a literal as described in DA-LITERAL.CREATE, a variable and a term
  ;;;            ACTUAL.VARIABLES: a list of already considered variable symbols.
  ;;; Effect:    all occurrences of VARIABLE in literal are substituted by NEW.TERM and a new
  ;;;            literal NEW.TERM = VARIABLE is generated.
  ;;; Value:     the generated literal.

  (LET ((SUBST (UNI-TERMSUBST.CREATE NIL OLD.TERM NEW.TERM)))
    (SETF (DA-LITERAL.TERMLIST LITERAL)
	  (MAPCAR #'(LAMBDA (TERM)
		      (UNI-TERMSUBST.APPLY SUBST TERM))
		  (DA-LITERAL.TERMLIST LITERAL)))
    (DA-LITERAL.CREATE (DA-SIGN.MINUS)
		       (DA-PREDICATE.EQUALITY)
		       (LIST (DA-TERM.COPY NEW.TERM) (DA-TERM.COPY OLD.TERM)) 
		       (LIST 'KIND (COND ((OR (DA-SYMBOL.IS.STRUCTURE (DA-TERM.SYMBOL OLD.TERM))
					      (NEQ (DA-TERM.SORT NEW.TERM) (DA-TERM.SORT OLD.TERM)))
					  (LIST 'MATCH))
					 (T (LIST 'CONDITION 'NOT.NEEDED)))))))


(DEFUN EXP=NORMALIZE.GTERM (GTERM &OPTIONAL NEGATE.FLAG)

  (COND ((MEMBER (DA-GTERM.SYMBOL GTERM) '(AND OR))
	 (DA-GTERM.CREATE (COND (NEGATE.FLAG (COND ((EQ (DA-GTERM.SYMBOL GTERM) 'AND) 'OR)
						   (T 'AND)))
				(T (DA-GTERM.SYMBOL GTERM)))
			  (MAPCAR #'(LAMBDA (SUBTERM)
				      (EXP=NORMALIZE.GTERM SUBTERM NEGATE.FLAG))
				  (DA-GTERM.TERMLIST GTERM))))
	((EQ (DA-GTERM.SYMBOL GTERM) 'NOT)
	 (EXP=NORMALIZE.GTERM (CAR (DA-GTERM.TERMLIST GTERM)) (NOT NEGATE.FLAG)))
	(NEGATE.FLAG (DA-FORMULA.NEGATE GTERM))
	(T GTERM)))
	 


;;;;;========================================================================================================
;;;;; Chapter six
;;;;; -----------
;;;;;
;;;;; Generation of the new tasks.
;;;;;========================================================================================================

;;; all errors and theorems to be proved are stored in the parameter TASKS.
;;; This is a property list with the properties 'UP (uniqueness to be proven), 'UF (function is not unique)
;;; 'CP (completeness to be proven) and 'CF (function is not complete).
;;; The values of these properties are as follows:
;;;
;;; 'UP : a list of lists (conditions.formula)
;;;
;;; 'CP : a list of lists (conditions.OR(formula_1 ... formula_n)), where condition is a list of literals, 
;;;       describing the actual subtree and the formula_i describe the case 
;;;       analysis to be proven to be complete.


(DEFUN EXP=CREATE.AND.PROVE.NEW.TASKS (TASKS SYMBOL PARAMETERS)

  ;; Effect: Tests the completeness resp. uniqueness formuals of symbol.
  ;; Value:  T, iff SYMBOL is proven to be complete and unique, NIL else.
  
  (AND (NOT (EXP=FORMULA.IS.NOT.COMPLETE TASKS SYMBOL PARAMETERS))
       (NOT (SOME #'(LAMBDA (NEW.TASK)
		      (setq new.task (eg-eval new.task))
		      (COND ((DA-FORMULA.IS.FALSE NEW.TASK))
			    ((or (da-formula.is.true new.task)
				 (NOT (SEL-THEOREM.PROVE NEW.TASK)))
			      (win-io.FORMAT (win-window 'proof) "I.e. the definition of ~A is not correct !~%" SYMBOL)
			      T)))
		  (NCONC (EXP=GENERATE.PROOF.FORMULAS (GETF TASKS 'CP) SYMBOL "complete")
			 (EXP=GENERATE.PROOF.FORMULAS (GETF TASKS 'UP) SYMBOL "unique"))))))


(DEFUN EXP=FORMULA.IS.NOT.COMPLETE (TASKS SYMBOL PARAMETER)
  
  ;;; 'CF : a list of conditions, describing the missing case.

  (MAPC #'(LAMBDA (CASE)
	    (MULTIPLE-VALUE-BIND (CONDITIONS SUBST) (EXP=SEPERATE.MATCH.AND.CONDITIONS (CAR CASE))
	      (win-io.FORMAT (win-window 'proof) "The definition of ~A is not correct:~%~%" SYMBOL)
	      (win-io.FORMAT (win-window 'proof)
		      "~@[In case of ~A ~] ~A is not defined,~%~%therefore the definition of ~A"
		      (COND (CONDITIONS (MAPCAN #'(LAMBDA (CONDS)
						    (PR-PRINT.FORMULA 
						      (DA-FORMULA.JUNCTION.CLOSURE 
							'AND 
							(MAPCAR #'(LAMBDA (LIT)
								    (DA-FORMULA.NEGATE LIT))
								CONDS))))
						CONDITIONS)))
		      (PR-PRINT.FORMULA (UNI-TERMSUBST.APPLY SUBST (DA-TERM.CREATE SYMBOL 
										   (MAPCAR #'DA-TERM.CREATE PARAMETER))))
		      SYMBOL)
	      (win-io.FORMAT (win-window 'proof) " is not leftcomplete.~%")))
	(GETF TASKS 'CF)))


(DEFUN EXP=GENERATE.PROOF.FORMULAS (TASKS SYMBOL TYPE)
  
  ;;; Input:   a list of (conditions.formula_list), a function/predicate symbol and a string
  ;;; Effect:  generates for each member of TASKS a DED-TASK of the form conditions -> formula_list
  ;;; Value :  a list of the generated formulas.

  (COND (TASKS
	 (LET (FORMULA)
	   (win-io.FORMAT (win-window 'proof) "~%To accept the definition of ~A we have to prove that ~A is ~A~%"
		   SYMBOL SYMBOL TYPE)
	   (MAPCAN #'(LAMBDA (CASE)			   
		       (MULTIPLE-VALUE-BIND (CONDITIONS SUBST) (EXP=SEPERATE.MATCH.AND.CONDITIONS (CAR CASE))
			 (SETQ FORMULA (COND (CONDITIONS (DA-FORMULA.JUNCTION.CLOSURE 
							   'OR (APPEND (MAPCAR #'(LAMBDA (LIT)
										   (UNI-TERMSUBST.APPLY SUBST LIT))
									       CONDITIONS)
								       (LIST (UNI-TERMSUBST.APPLY SUBST (CDR CASE))))))
					     (T (UNI-TERMSUBST.APPLY SUBST (CDR CASE)))))
			 (SETQ FORMULA (DA-FORMULA.QUANTIFICATION.CLOSURE 'ALL (DA-GTERM.VARIABLES FORMULA) 
									  (DA-GTERM.COPY FORMULA)))
			 (COND ((DA-LITERAL.IS.TRUE (EG-EVAL FORMULA))
				(win-io.FORMAT (win-window 'proof) "which is obviously true~%")
				NIL)
			       ((DA-LITERAL.IS.FALSE (EG-EVAL FORMULA))
				(win-io.FORMAT (win-window 'proof) "which is obviously false~%")
				(LIST (DA-LITERAL.FALSE)))
			       (T (LIST FORMULA)))))
		   TASKS)))))


;;;;;========================================================================================================
;;;;; Chapter seven
;;;;; -------------
;;;;;
;;;;; Misc. Functions.
;;;;;========================================================================================================


(DEFUN EXP=DEFINITION.IS.BASE.CASE (DEFINITION)

  ;;; Input:  a definition as defined in DA or a gterm constructed with symbols
  ;;;         \verb$UNSPEC$ or \verb$NOT.SPECIFIED$
  ;;; Value:  T, iff \verb$DEFINITION$ contains no further case analysis.

  (OR (EQ (DA-GTERM.SYMBOL DEFINITION) 'UNSPEC)
      (EQ (DA-GTERM.SYMBOL DEFINITION) 'NOT.SPECIFIED)
      (DA-GTERM.DEF.IS.VALUE DEFINITION)))


(DEFUN EXP=DEF.TERM.DELETE.CONDITION (DEF.TERM LITERAL)

  ;;; Input:   a definition term and a literal
  ;;; Effect:  removes LITERAL from the condition-slot of DEF.TERM.
  ;;; Value:   list of all literals in the condition-slot.

  (DA-GTERM.DEF.CREATE (DA-GTERM.DEF.VALUE DEF.TERM)
			(REMOVE LITERAL (DA-GTERM.DEF.CONDITION DEF.TERM))))


(DEFUN EXP=REPRESENTIVE.DEF.TERM (DEF.TERMS)

  ;;; Input:  a list of if-then-cases
  ;;; Effect: searches for one if-then-case with no conditions or
  ;;;         the otherwise-case if no other case is there.
  ;;; Value:  the value of this if-then-case
  
  (COND ((SOME #'(LAMBDA (DEF.TERM)
		   (COND ((NULL (DA-GTERM.DEF.CONDITION DEF.TERM))
			  (DA-GTERM.DEF.VALUE DEF.TERM))))
	       DEF.TERMS))
	((AND (EQL 1 (LENGTH DEF.TERMS))
	      (EQ 'OTHERWISE (DA-GTERM.DEF.CONDITION (CAR DEF.TERMS))))
	 (DA-GTERM.DEF.VALUE (CAR DEF.TERMS)))))



(DEFUN EXP=SEPERATE.MATCH.AND.CONDITIONS (LITERALS)
  (LET (SUBST OTHER.CONDS)
    (MAPC #'(LAMBDA (LITERAL)
	      (COND ((AND (DA-LITERAL.IS LITERAL) (DA-LITERAL.denotes.MATCH LITERAL)
			  (MEMBER 'DISJUNCT.RANGE 
				  (DA-SORT.ATTRIBUTES (DA-TERM.SORT (CAR (DA-LITERAL.TERMLIST LITERAL)))))
			  (uni-term.are.equal 
			   (car (da-literal.termlist literal))
			   (uni-termsubst.apply subst (car (da-literal.termlist literal)))))
		     (SETQ SUBST (UNI-TERMSUBST.CREATE SUBST (CAR (DA-LITERAL.TERMLIST LITERAL)) 
						       (DA-TERM.COPY (SECOND (DA-LITERAL.TERMLIST LITERAL))))))
		    (T (PUSH LITERAL OTHER.CONDS))))
	  LITERALS)
    (VALUES OTHER.CONDS SUBST)))


(DEFUN EXP=PROVE.DISJUNCTION (LIT.LIST &OPTIONAL PARAMETER.BOUND.TERMS)
  
  (LET (SUBST LIT SYMBOL INVERSE.FLAG LEFT)
    (SETQ LIT.LIST (REMOVE-IF #'DA-LITERAL.IS.FALSE
			      (MAPCAN #'(LAMBDA (LIT) 
					  (DA-FORMULA.JUNCTION.OPEN 'OR (EG-EVAL LIT)) (LIST LIT))
				      LIT.LIST)))
    (COND ((SOME #'(LAMBDA (FORM) 
		     (DA-FORMULA.IS.TRUE FORM))
		 LIT.LIST))
	  ((SOME #'(LAMBDA (FORMULA)
		     (AND (DA-LITERAL.IS FORMULA)
			  (SETQ LIT (MEMBER FORMULA LIT.LIST
					    :TEST #'(LAMBDA (X Y) 
						      (AND (DA-LITERAL.IS X)
							   (DA-LITERAL.IS Y)
							   (UNI-LITERAL.ARE.EQUAL X Y NIL 'OPPOSITE)))))))
		 LIT.LIST))
	  ((SOME #'(LAMBDA (FORM) 
		     (COND ((EQ (DA-GTERM.SYMBOL FORM) 'AND)
			    (EVERY #'(LAMBDA (ALT.FORM)
				       (EXP=PROVE.DISJUNCTION (CONS ALT.FORM (REMOVE FORM LIT.LIST)) 
							      PARAMETER.BOUND.TERMS))
				   (DA-FORMULA.JUNCTION.OPEN 'AND FORM)))))
		 LIT.LIST))
	  ((SETQ LIT (FIND-IF #'(LAMBDA (LIT)
				  (COND ((MULTIPLE-VALUE-SETQ (LEFT SYMBOL INVERSE.FLAG)
					   (DA-LITERAL.DENOTES.MATCH LIT))
					 (OR (NULL PARAMETER.BOUND.TERMS)
					     (MEMBER LEFT PARAMETER.BOUND.TERMS :TEST 'UNI-TERM.ARE.EQUAL)))))
			      LIT.LIST))
	   (COND (INVERSE.FLAG (EVERY #'(LAMBDA (STRUC.TERM)
					  (SETQ SUBST (UNI-TERMSUBST.CREATE NIL LEFT STRUC.TERM))
					  (EXP=PROVE.DISJUNCTION 
					    (MAPCAN #'(LAMBDA (FORM)
							(LIST (UNI-TERMSUBST.APPLY SUBST FORM)))
						    LIT.LIST)
					    (APPEND PARAMETER.BOUND.TERMS (DA-TERM.TERMLIST STRUC.TERM))))
				      (DA-SORT.CREATE.ALL.STRUCTURE.TERMS LEFT (LIST SYMBOL))))
		 (T (SETQ SUBST (UNI-TERMSUBST.CREATE NIL LEFT (SECOND (DA-LITERAL.TERMLIST LIT))))
		    (EXP=PROVE.DISJUNCTION (MAPCAN #'(LAMBDA (FORM)
								(UNI-TERMSUBST.APPLY SUBST FORM))
							    LIT.LIST)
						    (APPEND PARAMETER.BOUND.TERMS 
							    (DA-TERM.TERMLIST (SECOND (DA-LITERAL.TERMLIST LIT))))))))
	  (PARAMETER.BOUND.TERMS (EXP=PROVE.DISJUNCTION LIT.LIST NIL)))))



(DEFUN EXP=SOME.FORMULA (FORMULA.LIST FCT &OPTIONAL TAF)

  (LET (FORM)
    (SETQ TAF (DA-TAF.CREATE.ZERO TAF))
    (SOME #'(LAMBDA (FORMULA)
	      (SETQ TAF (DA-TAF.CREATE.NEXT TAF))
	      (COND ((MEMBER (DA-GTERM.SYMBOL FORMULA) '(AND OR))
		     (EXP=SOME.FORMULA (DA-GTERM.TERMLIST FORMULA) FCT TAF))
		    ((SETQ FORM (FUNCALL FCT FORMULA))
		     (CONS FORM TAF))))
	  FORMULA.LIST)))

