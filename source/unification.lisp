;;; -*- Package: INKA; Mode: LISP; Syntax: Common-Lisp -*-
;;; $Header: /home/inka/system-4-0/source/RCS/unification.lisp,v 1.6 1999/06/29 12:23:34 inka Exp $


;;; 2.8.93 DH  UNI-WITHOUT.THEORY   new function inserted


(IN-PACKAGE :INKA)

(DEFVAR UNI*STACK (MAKE-ARRAY '(100 4)))

(DEFVAR UNI*NO.OF.BINDINGS 0)
(DEFVAR UNI*COLOUR.BINDINGS NIL)

(DEFVAR UNI*THEORY.UNIFICATION T)


(defvar uni*weakening.decisions nil)



;;; substitutions are lists of the form  (var(1) (colour(1) term(1) ... colour(n) term(n)) ...


(DEFUN UNI-RESET ()
 
  ;;; Effect:  initializes the unification module
  ;;; Value:   undefined
  
  (UNI=RESET.BINDINGS 0)
  (SETQ UNI*NO.OF.BINDINGS 0)
  (SETQ UNI*COLOUR.BINDINGS NIL))


(DEFMACRO UNI-CREATE.VAR.RENAMING (VARIABLES)
  
  ;;; Input:  a list of variables 
  ;;; Value:  a copy of this list with renamed variables
  
  `(MAPCAN #'(LAMBDA (VAR)
	       (LIST VAR (LIST NIL (DA-TERM.CREATE (DA-VARIABLE.CREATE (DA-VARIABLE.SORT VAR))))))
	   ,VARIABLES))


(DEFMACRO UNI-WITH.BINDINGS (SUBSTITUTION &BODY BODY)
  
  ;;; Input:  a substitution (but no coloured substitution !) and a piece of program
  ;;; Effect: sets the bindings of the \verb$SUBSTITUTION$ and executes the \verb$BODY$ and resets the bindings
  ;;; Value:  the value of the execution of \verb$BODY$


  `(LET ((STACK.DEPTH UNI*NO.OF.BINDINGS)) 
     (UNWIND-PROTECT (PROGN (UNI=SET.BINDINGS ,SUBSTITUTION NIL 'SUBST)
			    (PROGN . ,BODY))
       (UNI=RESET.BINDINGS STACK.DEPTH))))


(DEFMACRO UNI-WITH.CONSTANTS (VARIABLES &BODY BODY)
  
  ;;; Input:  a list of variables and a piece of program
  ;;; Effect: sets the variables of \verb$VARIABLES$ to constants, executes the \verb$BODY$, and resets the constants
  ;;; Value:  the value of the execution of \verb$BODY$


  `(LET ((STACK.DEPTH UNI*NO.OF.BINDINGS)) 
     (UNWIND-PROTECT (PROGN (UNI=SET.CONSTANTS ,VARIABLES NIL)
			    (PROGN . ,BODY))
       (UNI=RESET.BINDINGS STACK.DEPTH))))


(DEFMACRO UNI-WITH.TAF.RESTRICTIONS (TERM1 TERM2 TAF.PAIRS &BODY BODY)

  ;;; is not used and will be removed in a future release

  `(LET ((T1 ,TERM1) (T2 ,TERM2) (TAF.P ,TAF.PAIRS))
	(UNWIND-PROTECT (PROGN (UNI=TAF.RESTRICTION.APPLY T1 T2 TAF.P T)
			       (PROGN . ,BODY))
	   (UNI=TAF.RESTRICTION.APPLY T1 T2 TAF.P NIL))))


(DEFMACRO UNI-WITHOUT.THEORY (&BODY BODY)

  ;;; Input:   a piece of program
  ;;; Effect:  evaluates \verb$BODY$ without any theory unification
  ;;; Value:   value of the evaluation of \verb$BODY$

  `(LET ((UNI*THEORY.UNIFICATION NIL))
     (PROGN . ,BODY)))


(DEFUN UNI-COLOUR.ARE.EQUAL (COLOUR1 COLOUR2)

  ;;; Input:  two colours
  ;;; Value:  T, if both colours coincide

  (OR (EQ COLOUR1 COLOUR2)
      (AND (DA-COLOUR.IS.FADE COLOUR1)
	   (DA-COLOUR.IS.FADE COLOUR2))))


;;;;;****************************************************************************************************
;;;;;
;;;;;  Functions to unify datastructures:
;;;;;
;;;;;****************************************************************************************************


(DEFUN UNI-GTERM.UNIFY (FOR1 FOR2 &OPTIONAL COL.KEY1 COL.KEY2 TAF.RESTRICTIONS SIGN)

  ;;; Input:   two gterms, optionally two colour keys, a list of dotted pairs, each
  ;;;          consisting of two tafs and a flag
  ;;; Effect:  tries to unify \verb$FOR1$ and \verb$FOR2$ under the given bindings (under the theory of commutativity),
  ;;;          however, \verb$TAF.RESTRICTIONS$ denote a set of subterms in \verb$FOR1$ and \verb$FOR2$
  ;;;          which will not be considered
  ;;; Value:   a list of substitutions denoting the most general unifiers of both gterms,or nil if none exists

  (COND ((AND (DA-TERM.IS FOR1) (DA-TERM.IS FOR2))
	 (UNI-TERM.UNIFY FOR1 FOR2 COL.KEY1 COL.KEY2 TAF.RESTRICTIONS))
	((AND (DA-LITERAL.IS FOR1)
	      (DA-LITERAL.IS FOR2))
	 (UNI-LITERAL.UNIFY FOR1 FOR2 SIGN COL.KEY1 COL.KEY2 TAF.RESTRICTIONS))))


(DEFUN UNI-LITERAL.UNIFY (LIT1 LIT2 &OPTIONAL SIGN COL.KEY1 COL.KEY2 TAF.RESTRICTIONS)
  
  ;;;  Input:  two arbitrary literals optionally an atom, two bindings and a list of dotted pairs,
  ;;;          each denoting two tafs
  ;;;  Effect: checks whether bot literals
  ;;;          - have the same sign if \verb$SIGN$ = NIL or opposite signs if \verb$SIGN$ = OPPOSITE or discards signs
  ;;;            if \verb$SIGN$ = IGNORE
  ;;;          - have the same predicate symbols
  ;;;          - both termlists are unifyable.
  ;;;  Value:  a list of most general unifiers for both literals under the specified bindings and under
  ;;;          the specified restrictions, or nil if none exists

  (LET ((STACK.DEPTH UNI*NO.OF.BINDINGS) SOLUTIONS
	(symmetric? (DA-SYMBOL.HAS.ATTRIBUTE (DA-GTERM.SYMBOL LIT1) 'SYMMETRIC)))
    (UNWIND-PROTECT (progn (cond ((AND (OR (EQ SIGN 'IGNORE)
					   (AND (EQ SIGN 'OPPOSITE) (NEQ (DA-LITERAL.SIGN LIT1) 
									 (DA-LITERAL.SIGN LIT2)))
					   (AND (NULL SIGN) (EQ (DA-LITERAL.SIGN LIT1) (DA-LITERAL.SIGN LIT2))))
				       (EQ (DA-GTERM.SYMBOL LIT1) (DA-GTERM.SYMBOL LIT2))
				       (UNI=COLOUR.UNIFY (UNI=TERM.COLOUR LIT1 COL.KEY1)
							 (UNI=TERM.COLOUR LIT2 COL.KEY2) NIL))
				  (UNI-WITH.TAF.RESTRICTIONS
				   LIT1 LIT2 TAF.RESTRICTIONS
				   (progn (setq solutions
						(UNI=TERMLIST.UNIFY (DA-LITERAL.TERMLIST LIT1)
								    (DA-LITERAL.TERMLIST LIT2)
								    COL.KEY1 COL.KEY2
								    (UNI=SOLUTION.CREATE nil symmetric?)))
					  (COND (symmetric?
						 (setq solutions
						       (nconc solutions
							      (UNI=TERMLIST.UNIFY 
							       (DA-LITERAL.TERMLIST LIT1)
							       (REVERSE (DA-LITERAL.TERMLIST LIT2))
							       COL.KEY1 COL.KEY2
							       (UNI=SOLUTION.CREATE nil symmetric?))))))))))
			   (cond (solutions (UNI=GENERATE.UNIFIERS SOLUTIONS STACK.DEPTH))))
      (UNI=RESET.BINDINGS STACK.DEPTH))))


(DEFUN UNI-TERM.UNIFY (TERM1 TERM2 &OPTIONAL COL.KEY1 COL.KEY2 TAF.RESTRICTIONS)
  
  ;;;  Input:  two arbitrary terms, optionally two bindings and a list of dotted pairs, each
  ;;;          consisting of two tafs
  ;;;  Effect: tries to unify \verb$TERM1$ and \verb$TERM2$ under the given bindings 
  ;;;          (under the theory of commutativity),
  ;;;          however, \verb$TAF.RESTRICTIONS$ denote a set of subterms in \verb$TERM1$ and \verb$TERM2$
  ;;;          which will not be considered
  ;;;  Value:  a list of substitutions denoting the most general unifiers of both terms,or nil if none exists
  
  (LET ((STACK.DEPTH UNI*NO.OF.BINDINGS)
	SOLUTIONS)
    (UNWIND-PROTECT
	(COND ((SETQ SOLUTIONS (UNI-WITH.TAF.RESTRICTIONS TERM1 TERM2 TAF.RESTRICTIONS
							  (UNI=TERM.UNIFY TERM1 TERM2 COL.KEY1 COL.KEY2)))
	       (UNI=GENERATE.UNIFIERS SOLUTIONS STACK.DEPTH)))
      (UNI=RESET.BINDINGS STACK.DEPTH))))


(DEFUN UNI-TERMLIST.UNIFY (TL1 TL2 &OPTIONAL COL.KEY1 COL.KEY2)
  
  ;;;  Input:  two arbitrary lists of terms, and optionally two bindings
  ;;;  Effect: tries to unify \verb$TL1$ and \verb$TL2$ under the given bindings (under the theory of commutativity).
  ;;;  Value:  a list of substitutions denoting the most general unifiers of both termlists, or nil if none exists
  
  (LET ((STACK.DEPTH UNI*NO.OF.BINDINGS)
	SOLUTIONS)
       (UNWIND-PROTECT (COND ((SETQ SOLUTIONS (UNI=TERMLIST.UNIFY TL1 TL2 COL.KEY1 COL.KEY2 NIL))
			      (UNI=GENERATE.UNIFIERS SOLUTIONS STACK.DEPTH)))
		       (UNI=RESET.BINDINGS STACK.DEPTH))))



;;;;;****************************************************************************************************
;;;;;
;;;;;  Functions to match datastructures:
;;;;;
;;;;;****************************************************************************************************



(DEFUN UNI-GTERM.MATCH (FOR1 FOR2)

  ;;; Input:   two formulas
  ;;; Effect:  Computes a substitution $\sigma$, such that $\sigma$(\verb$FOR1$) = \verb$FOR2$. Only such variables
  ;;;          which are ALL-quantified before any occurrence of a NOT, IMPL or EQV symbol
  ;;;          are regarded as variable symbols.
  ;;; Value:   The substitution $\sigma$, such that $\sigma$(\verb$FOR1$) = \verb$FOR2$, or if \verb$FOR1$ 
  ;;;          is not matchable with \verb$FOR2$ it returns NIL

  (UNI-WITH.CONSTANTS (UNION (UNI=VAR.TO.CONSTANT FOR1 NIL)
			     (UNI=VAR.TO.CONSTANT FOR2 T))
    (UNI=GTERM.MATCH FOR1 FOR2 (LIST NIL))))


(DEFUN UNI-GTERM.MATCH.LT (FOR1 FOR2 &OPTIONAL SIGN)

  ;;; Input:   two gterms
  ;;; Effect:  matches both formulas if they are either both literals or both terms
  ;;; Value:   a list of matchers

  (COND ((AND (DA-LITERAL.IS FOR1) (DA-LITERAL.IS FOR2))
	 (UNI-LITERAL.MATCH FOR1 FOR2 T SIGN))
	((AND (DA-TERM.IS FOR1) (DA-TERM.IS FOR2))
	 (UNI-TERM.MATCH FOR1 FOR2 T))))


(DEFUN UNI-LITERAL.MATCH (LIT1 LIT2 &OPTIONAL VARIABLES SIGN COL.KEY1 COL.KEY2)
  
  ;;;  Input:  two literals, optionally a list of variables, an atom, and two bindings
  ;;;  Effect: checks whether bot literals
  ;;;          - have the same sign if \verb$SIGN$ = NIL or opposite signs if \verb$SIGN$ = OPPOSITE or
  ;;;            discards signs if \verb$SIGN$ = IGNORE
  ;;;          - have the same predicate symbols
  ;;;          - there is a matcher for the termlists.
  ;;;  Value:  a list of matchers for both literals under the specified bindings, or nil if none exists.
  ;;;  Note:   \verb$VARIABLES$ have to be all variables of \verb$LIT2$ !

  (LET ((STACK.DEPTH UNI*NO.OF.BINDINGS))
    (COND ((EQ VARIABLES T)
	   (SETQ VARIABLES (UNI=FIND.VARIABLES (DA-LITERAL.TERMLIST LIT2) NIL))))
    (UNI=SET.CONSTANTS VARIABLES NIL)
    (PROG1 (UNI-LITERAL.UNIFY LIT1 LIT2 SIGN COL.KEY1 COL.KEY2)
      (UNI=RESET.BINDINGS STACK.DEPTH))))


(DEFUN UNI-TERM.MATCH (TERM1 TERM2 &OPTIONAL VARIABLES COL.KEY1 COL.KEY2 TAF.RESTRICTIONS)
  
  ;;; Input:   two terms, optionally a list of variables or T, two bindings and
  ;;;          a list of dotted pairs, each consisting of two tafs
  ;;; Effect:  if \verb$VARIABLES$ = T then the variables of \verb$TERM2$, else the variables in
  ;;;          the list will be set to constants. Then, both terms are unified (under the specified bindings) considering
  ;;;          the restrictions given by \verb$TAF.RESTRICTIONS$
  ;;; Value:   a list of matchers s with s(\verb$TERM1$)=\verb$TERM2$, or NIL if no matcher exists
  ;;; Note:    \verb$VARIABLES$ must contain all variables of \verb$TERM2$ !!!
  
  (COND ((EQ VARIABLES T)
	 (SETQ VARIABLES (UNI=FIND.VARIABLES TERM2 NIL))))
  (LET ((STACK.DEPTH UNI*NO.OF.BINDINGS))
    (UNI=SET.CONSTANTS VARIABLES NIL)
    (UNWIND-PROTECT
	(UNI-TERM.UNIFY TERM1 TERM2 COL.KEY1 COL.KEY2 TAF.RESTRICTIONS)
      (UNI=RESET.BINDINGS STACK.DEPTH))))


(DEFUN UNI-TERMLIST.MATCH (TL1 TL2 &OPTIONAL VARIABLES COL.KEY1 COL.KEY2)
  
  ;;; Input:   two termlists, optionally a list of variables or T, and two bindings
  ;;; Effect:  if \verb$VARIABLES = T$ then the variables of \verb$TL2$, else the variables in
  ;;;          the list will be set to constants. Then, both lists of terms are unified under the given bindings. 
  ;;; Value:   a list substitutions denoting the matchers of both termlists or NIL if none exists.
  ;;; Note:    \verb$VARIABLES$ must contain all variables of \verb$TL2$ !!!

  (LET ((STACK.DEPTH UNI*NO.OF.BINDINGS) SOLUTIONS)
    (COND ((EQ VARIABLES T)
	   (SETQ VARIABLES (UNI=FIND.VARIABLES TL2 NIL))))
    (UNI=SET.CONSTANTS VARIABLES NIL)
    (UNWIND-PROTECT
	(COND ((SETQ SOLUTIONS (UNI=TERMLIST.UNIFY TL1 TL2 COL.KEY1 COL.KEY2 NIL))
	       (UNI=GENERATE.UNIFIERS SOLUTIONS STACK.DEPTH)))
      (UNI=RESET.BINDINGS STACK.DEPTH))))



(DEFUN UNI=GTERM.MATCH (FOR1 FOR2 MATCHERS)

  ;;; Input:   two formulas, and a unifier
  ;;; Effect:  computes, whether where is an extension of MATCHERS, such that
  ;;;          FOR1 is an instanve of FOR2. 
  ;;; Value:   a list of matchers

  (COND ((NULL MATCHERS) MATCHERS)
	((AND (DA-LITERAL.IS FOR1)
	      (DA-LITERAL.IS FOR2))
	 (UNI-MATCHER.LIST.MERGE MATCHERS (UNI-LITERAL.MATCH FOR1 FOR2 T)))
	((AND (DA-FORMULA.IS FOR2) (MEMBER (DA-FORMULA.SYMBOL FOR2) '(ALL EX)))
	 (UNI=GTERM.MATCH FOR1 (SECOND (DA-FORMULA.TERMLIST FOR2)) MATCHERS))
	((AND (DA-FORMULA.IS FOR1) (MEMBER (DA-FORMULA.SYMBOL FOR1) '(ALL EX)))
	 (UNI=GTERM.MATCH (SECOND (DA-FORMULA.TERMLIST FOR1)) FOR2 MATCHERS))
	((AND (DA-FORMULA.IS FOR1) (DA-FORMULA.IS FOR2)
	      (EQ (DA-FORMULA.SYMBOL FOR1) (DA-FORMULA.SYMBOL FOR2)))
	 (SETQ MATCHERS (UNI=GTERM.MATCH (CAR (DA-FORMULA.TERMLIST FOR1))
					 (CAR (DA-FORMULA.TERMLIST FOR2))
					 MATCHERS))
	 (COND ((AND MATCHERS (NEQ (DA-FORMULA.SYMBOL FOR1) 'NOT))
		(UNI=GTERM.MATCH (SECOND (DA-FORMULA.TERMLIST FOR1))
				 (SECOND (DA-FORMULA.TERMLIST FOR2))
				 MATCHERS))
	       (T MATCHERS)))))



;;;;;****************************************************************************************************
;;;;;
;;;;;  Functions to test equality of datastructures:
;;;;;
;;;;;****************************************************************************************************



(DEFUN UNI-GTERM.ARE.EQUAL (FOR1 FOR2 &OPTIONAL COL.KEY1 COL.KEY2 SIGN)

  ;;; edited at 30-JUL-85 16:32:19
  ;;; Input:  two formulas in prefix-form and optionally two bindings
  ;;; Value:  T if \verb$FOR1$ is equal to \verb$FOR2$ modulo variable-renaming under the given bindings

  (COND ((AND (NEQ SIGN 'OPPOSITE) (EQ FOR1 FOR2)))
	((AND (DA-TERM.IS FOR1) (DA-TERM.IS FOR2))
	 (UNI-TERM.ARE.EQUAL FOR1 FOR2 COL.KEY1 COL.KEY2))
	((AND (DA-LITERAL.IS FOR1)
	      (DA-LITERAL.IS FOR2))
	 (UNI-LITERAL.ARE.EQUAL FOR1 FOR2 nil SIGN COL.KEY1 COL.KEY2))
	((AND (DA-FORMULA.IS FOR1) (DA-FORMULA.IS FOR2)
	      (UNI=JUNCTORS.ARE.EQUAL (DA-FORMULA.SYMBOL FOR1) (DA-FORMULA.SYMBOL FOR2) SIGN))
	 (COND ((MEMBER (DA-FORMULA.SYMBOL FOR1) '(ALL EX))
		(UNI-GTERM.ARE.EQUAL (uni-subst.apply (LIST (CAR (DA-FORMULA.TERMLIST FOR1))
							    (LIST NIL (da-term.create (CAR (DA-FORMULA.TERMLIST FOR2)))))
						      (SECOND (DA-FORMULA.TERMLIST FOR1)))
				     (SECOND (DA-FORMULA.TERMLIST FOR2))
				     COL.KEY1 COL.KEY2))
	       ((EVERY #'(LAMBDA (SUB1 SUB2) (UNI-GTERM.ARE.EQUAL SUB1 SUB2 COL.KEY1 COL.KEY2 SIGN))
		       (DA-GTERM.TERMLIST FOR1) (DA-GTERM.TERMLIST FOR2)))))	
	((AND (DA-GTERM.IS FOR1)
	      (DA-GTERM.IS FOR2)
	      (UNI=JUNCTORS.ARE.EQUAL (DA-GTERM.SYMBOL FOR1) (DA-GTERM.SYMBOL FOR2) SIGN))
	 (EVERY #'(LAMBDA (SUB1 SUB2)
		    (UNI-GTERM.ARE.EQUAL SUB1 SUB2 COL.KEY1 COL.KEY2 SIGN))
		(DA-GTERM.TERMLIST FOR1) (DA-GTERM.TERMLIST FOR2)))))


(DEFUN UNI-LITERAL.ARE.EQUAL (LIT1 LIT2 &OPTIONAL ignore SIGN COL.KEY1 COL.KEY2)
  
  ;;;  Input:  two literals, optionally an atom, and two bindings
  ;;;  Effect: compares both literals (under the given bindings)
  ;;;  Value:  T, if \verb$LIT1$ and \verb$LIT2$ are equal under the given bindings

  (AND (OR (EQ SIGN 'IGNORE)
	   (AND (EQ SIGN 'OPPOSITE) (NEQ (DA-LITERAL.SIGN LIT1) (DA-LITERAL.SIGN LIT2)))
	   (AND (NULL SIGN) (EQ (DA-LITERAL.SIGN LIT1) (DA-LITERAL.SIGN LIT2))))
       (LET ((TL1 (DA-LITERAL.TERMLIST LIT1)) (TL2 (DA-LITERAL.TERMLIST LIT2)))
	 (COND ((OR (NEQ (DA-GTERM.SYMBOL LIT1) (DA-GTERM.SYMBOL LIT2))
		    (NOT (UNI-COLOUR.ARE.EQUAL (UNI=TERM.COLOUR LIT1 COL.KEY1) (UNI=TERM.COLOUR LIT2 COL.KEY2))))
		NIL)	
	       ((UNI-TERMLIST.ARE.EQUAL TL1 TL2 COL.KEY1 COL.KEY2))
	       ((DA-SYMBOL.HAS.ATTRIBUTE (DA-GTERM.SYMBOL LIT1) 'SYMMETRIC)
		(UNI-TERMLIST.ARE.EQUAL (REVERSE TL1) TL2 COL.KEY1 COL.KEY2))))))


(DEFUN UNI-TERM.ARE.EQUAL (TERM1 TERM2 &OPTIONAL COL.KEY1 COL.KEY2)
  
  ;;; Input:  two terms and optionally two bindings
  ;;; Value:  t, if both terms are equal under the given bindings, else nil.

  (AND (EQ (DA-TERM.SYMBOL TERM1) (DA-TERM.SYMBOL TERM2))
       (UNI-COLOUR.ARE.EQUAL (UNI=TERM.COLOUR TERM1 COL.KEY1) (UNI=TERM.COLOUR TERM2 COL.KEY2))
       (OR (UNI-TERMLIST.ARE.EQUAL (DA-GTERM.TERMLIST TERM1)
				   (DA-GTERM.TERMLIST TERM2)
				   COL.KEY1 COL.KEY2)
	   (AND UNI*THEORY.UNIFICATION
		(DA-SYMBOL.HAS.ATTRIBUTE (DA-TERM.SYMBOL TERM1) 'COMMUTATIVE)
		(UNI-TERMLIST.ARE.EQUAL (DA-GTERM.TERMLIST TERM1)
					(REVERSE (DA-GTERM.TERMLIST TERM2))
					COL.KEY1 COL.KEY2)))))


(DEFUN UNI-TERMLIST.ARE.EQUAL (TL1 TL2 &OPTIONAL COL.KEY1 COL.KEY2)
  
  ;;; Input:  two termlists and optionally two bindings
  ;;; Value:  t, if \verb$TL1$ = \verb$TL2$ under the given bindings else nil

  (COND ((NOT (EQ (LIST-LENGTH TL1) (LIST-LENGTH TL2))) NIL)
	(T (EVERY #'(LAMBDA (SUB1 SUB2)
		      (UNI-TERM.ARE.EQUAL SUB1 SUB2 COL.KEY1 COL.KEY2))
		  TL1 TL2))))


(DEFUN UNI=JUNCTORS.ARE.EQUAL (JUNCTOR1 JUNCTOR2 SIGN)

  (COND ((NEQ SIGN 'OPPOSITE) (EQ JUNCTOR1 JUNCTOR2))
	(T (EQ JUNCTOR2
	       (CASE JUNCTOR1
		     (OR 'AND)
		     (AND 'OR)
		     (IMPL 'IMPL)
		     (ALL 'EX)
		     (EX 'ALL))))))


(DEFUN UNI=VAR.TO.CONSTANT (FORMULA NEGATION &OPTIONAL VARIABLES)

  ;;; Input:  a formula and a flag
  ;;; Value:  a list of EX-quantified or free variables
  ;;; Note:   This function knows, that (NOT (ALL y ...)) is the same as (EX y ...)
  
  (COND ((DA-LITERAL.IS FORMULA)
         (SET-DIFFERENCE (DA-GTERM.VARIABLES FORMULA) VARIABLES))
	((EQ (DA-FORMULA.symbol FORMULA) 'NOT)
         (UNI=VAR.TO.CONSTANT (CAR (DA-FORMULA.TERMLIST FORMULA)) (NOT NEGATION) VARIABLES))
        ((MEMBER (DA-FORMULA.symbol FORMULA) '(AND OR))
         (UNION (UNI=VAR.TO.CONSTANT (CAR (DA-FORMULA.TERMLIST FORMULA)) NEGATION VARIABLES)
                (UNI=VAR.TO.CONSTANT (SECOND (DA-FORMULA.TERMLIST FORMULA)) NEGATION VARIABLES)))
        ((EQ (DA-FORMULA.symbol FORMULA) 'IMPL)
         (UNION (UNI=VAR.TO.CONSTANT (CAR (DA-FORMULA.TERMLIST FORMULA)) (NOT NEGATION) VARIABLES)
                (UNI=VAR.TO.CONSTANT (SECOND (DA-FORMULA.TERMLIST FORMULA)) NEGATION VARIABLES)))
        ((EQ (DA-FORMULA.symbol FORMULA) 'EQV)
         (UNION (UNI=VAR.TO.CONSTANT (CAR (DA-FORMULA.TERMLIST FORMULA)) (NOT NEGATION) VARIABLES)
                (UNI=VAR.TO.CONSTANT (SECOND (DA-FORMULA.TERMLIST FORMULA)) NEGATION VARIABLES)
                (UNI=VAR.TO.CONSTANT (CAR (DA-FORMULA.TERMLIST FORMULA)) NEGATION VARIABLES)
                (UNI=VAR.TO.CONSTANT (SECOND (DA-FORMULA.TERMLIST FORMULA))(NOT NEGATION) VARIABLES)))
        ((EQ (DA-FORMULA.symbol FORMULA) 'ALL)
         (COND (NEGATION (CONS (CAR (DA-FORMULA.TERMLIST FORMULA))
                               (UNI=VAR.TO.CONSTANT (SECOND (DA-FORMULA.TERMLIST FORMULA)) NEGATION 
                                                    (CONS (CAR (DA-FORMULA.TERMLIST FORMULA)) VARIABLES))))
               (T (UNI=VAR.TO.CONSTANT (SECOND (DA-FORMULA.TERMLIST FORMULA)) NEGATION 
                                       (CONS (CAR (DA-FORMULA.TERMLIST FORMULA)) VARIABLES)))))
        ((EQ (DA-FORMULA.symbol FORMULA) 'EX)
         (COND (NEGATION (UNI=VAR.TO.CONSTANT (SECOND (DA-FORMULA.TERMLIST FORMULA)) NEGATION 
                                              (CONS (CAR (DA-FORMULA.TERMLIST FORMULA)) VARIABLES)))
               (T (CONS (CAR (DA-FORMULA.TERMLIST FORMULA))
                        (UNI=VAR.TO.CONSTANT (SECOND (DA-FORMULA.TERMLIST FORMULA)) NEGATION 
                                             (CONS (CAR (DA-FORMULA.TERMLIST FORMULA)) VARIABLES))))))))


;;;;;****************************************************************************************************
;;;;;
;;;;;  misc. functions 
;;;;;
;;;;;****************************************************************************************************



(DEFUN UNI-TERM.FAILURE.LIST (TERM1 TERM2 &OPTIONAL TAF FAILURE.LIST)

  (COND ((OR (DA-VARIABLE.IS (DA-GTERM.SYMBOL TERM1))
	     (DA-VARIABLE.IS (DA-GTERM.SYMBOL TERM2)))
	 FAILURE.LIST)
	((EQ (DA-GTERM.SYMBOL TERM1) (DA-GTERM.SYMBOL TERM2))
	 (SETQ TAF (DA-TAF.CREATE.ZERO TAF))
	 (MAPC #'(LAMBDA (SUB.TERM1 SUB.TERM2)
		   (SETQ TAF (DA-TAF.CREATE.NEXT TAF))
		   (SETQ FAILURE.LIST (UNI-TERM.FAILURE.LIST SUB.TERM1 SUB.TERM2 TAF FAILURE.LIST)))
	       (DA-GTERM.TERMLIST TERM1) (DA-GTERM.TERMLIST TERM2))
	 FAILURE.LIST)
	(T  (PUSH (LIST TAF (DA-GTERM.SYMBOL TERM1) (DA-GTERM.SYMBOL TERM2))
		  FAILURE.LIST))))


;;;;;****************************************************************************************************
;;;;;
;;;;;  Functions for substitutions:
;;;;;
;;;;;****************************************************************************************************


(DEFUN UNI-SUBST.MERGE (UNI1 UNI2)

  ;;; Input:  two unifiers
  ;;; Value:  a list of unifiers merging \verb$UNI1$ and \verb$UNI2$, if there are some; nil otherwise

  (COND ((NULL UNI1) (LIST UNI2))
	((NULL UNI2) (LIST UNI1))
	(T (let ((DEPTH UNI*NO.OF.BINDINGS) (SOLUTIONS (LIST NIL))
		 (col.key (cons 'key NIL)))
	     (UNI=SET.BINDINGS UNI1 NIL 'SUBST)
	     (MAPCF #'(LAMBDA (VAR COLOUR.TERMS)
			(cond ((da-variable.is var)
			       (MAPCF #'(LAMBDA (COLOUR TERM)
					  (SETQ SOLUTIONS (MAPCAN #'(LAMBDA (SOLUTION)
								      (UNI=TERM.UNIFY (DA-TERM.CREATE VAR NIL COLOUR)
										      TERM COL.KEY COL.KEY SOLUTION))
								     SOLUTIONS)))
				      COLOUR.TERMS))
			      (t (setq solutions (remove-if-not #'(lambda (solution)
								    (uni=colour.unify var colour.terms solution))
								solutions)))))
		    UNI2)
	     (PROG1 (UNI=GENERATE.UNIFIERS SOLUTIONS DEPTH)
	       (UNI=RESET.BINDINGS DEPTH))))))


(DEFUN UNI-SUBST.APPLY.ON.SUBST (UNI1 UNI2)

  ;;; Input:  two unifiers
  ;;; Value:  a list of unifiers denoting the instantiation of \verb$UNI1$ by \verb$UNI2$

  (COND ((NULL UNI2) UNI1)
	(T (SMAPCON #'(LAMBDA (VAR.COLOUR.TERMS.LIST)
			(LIST (CAR VAR.COLOUR.TERMS.LIST)
			      (SMAPCON #'(LAMBDA (COLOUR.TERM.LIST)
					   (LIST (CAR COLOUR.TERM.LIST)
						 (UNI-SUBST.APPLY UNI2 (SECOND COLOUR.TERM.LIST))))
				       #'CDDR
				       (SECOND VAR.COLOUR.TERMS.LIST))))
		    #'CDDR
		    UNI1))))


(DEFUN UNI-SUBST.LIST.MERGE (L1 L2)
  
  ;;; Input: two lists of substitutions
  ;;; Value: a list of a unifier obtained by merging each unifier of \verb$L1$ with each of \verb$L2$
  
  (COND ((OR (NULL L1) (NULL L2)) NIL)
        (T (MAPCAN #'(LAMBDA (UNI1)
		       (MAPCAN #'(LAMBDA (UNI2)
				    (UNI-SUBST.MERGE UNI1 UNI2))
			       L2))
		   L1))))


(DEFMACRO UNI-SUBST.WITH.VARS (SUBST BODY)

  ;;; Input:  a substitution and a lambda expression with three arguments
  ;;; Effect: applies the given lambda expression \verb$BODY$ on each tupel (variable colour term) in \verb$SUBST$
  ;;; Value:  undefined.

  `(MAPCF #'(LAMBDA (VAR COLOUR.TERMS)
	      (MAPCF #'(LAMBDA (COLOUR TERM)
			 (FUNCALL ,BODY VAR TERM COLOUR))
		     COLOUR.TERMS))
	  ,SUBST))


(DEFUN UNI-MATCHER.MERGE (MATCHER1 MATCHER2)
  
  ;;; Input:  two matchers
  ;;; value:  a list of one unifier merging the two matchers,if it is possible; NIL otherwise

  (LET (VARIABLES)
    (MAPCF #'(LAMBDA (IGNORE COLOUR.TERMS)
	       (MAPCF #'(LAMBDA (IGNORE TERM)
			  (SETQ VARIABLES (NCONC (UNI=FIND.VARIABLES TERM) VARIABLES)))
		      COLOUR.TERMS))
	   (APPEND MATCHER1 MATCHER2))
    (UNI-WITH.CONSTANTS VARIABLES
      (UNI-SUBST.MERGE MATCHER1 MATCHER2))))


(DEFUN UNI-MATCHER.LIST.MERGE (L1 L2)
  
  ;;; Input: two lists of substitutions
  ;;; Value: a list of a unifier obtained by merging each unifier of \verb$L1$ with each of \verb$L2$
  
  (COND ((OR (NULL L1) (NULL L2)) NIL)
        (T (MAPCAN #'(LAMBDA (UNI1)
		       (MAPCAN #'(LAMBDA (UNI2)
				   (UNI-MATCHER.MERGE UNI1 UNI2))
			       L2))
		   L1))))


(DEFUN UNI-SUBST.APPLY (SUBSTITUTION GTERM &OPTIONAL ignore from.col.key to.colour.key)

  ;;;  Input:   an arbitrary substitution, a term or a substitution, a binding and a flag
  ;;;  Effect:  substitution is applied to a copy of \verb$GTERM$.
  ;;;  Value:   NIL, if \verb$GTERM$ = NIL, else \verb$SUBSTITUTION$(\verb$GTERM$)
  ;;;  Notice:  in case of coloured substitutions, \verb$SUBSTITUTION$ will be destructivly modified
  ;;;           in case of new colour-variables.

  (SETQ GTERM (UNI=SUBST.APPLY SUBSTITUTION GTERM FROM.COL.KEY to.colour.key))
  (cond (to.colour.key (UNI=GTERM.CHECK.COLOURS GTERM to.colour.key)))
  GTERM)


(DEFUN uni=GTERM.CHECK.COLOURS (GTERM COLOUR.KEY)

  (let (result)
    (COND ((AND (NOT (DA-LITERAL.IS GTERM)) (NOT (DA-TERM.IS GTERM)))
	   (MAPC #'(LAMBDA (SUB.TERM) (uni=GTERM.CHECK.COLOURS SUB.TERM COLOUR.KEY)) (DA-GTERM.TERMLIST GTERM)))
	  ((NULL (DA-GTERM.TERMLIST GTERM))
	   (NOT (DA-COLOUR.IS.FADE (da-gterm.colour gterm colour.key))))
	  ((DA-COLOUR.IS.FADE (da-gterm.colour gterm colour.key))
	   (SETQ RESULT NIL)
	   (MAPC #'(LAMBDA (SUB.TERM)
			   (SETQ RESULT (OR (uni=GTERM.CHECK.COLOURS SUB.TERM COLOUR.KEY) RESULT)))
		 (DA-GTERM.TERMLIST GTERM))
	   RESULT)
	  (T (SETQ RESULT T)
	     (MAPC #'(LAMBDA (SUB.TERM)
			     (SETQ RESULT (AND (uni=GTERM.CHECK.COLOURS SUB.TERM COLOUR.KEY) RESULT)))
		   (DA-GTERM.TERMLIST GTERM))
	     (COND ((NULL RESULT) 
		    (DA-GTERM.COLOURIZE gterm (DA-COLOUR.FADED) colour.key)
		    NIL)
		   (T T))))))


(DEFUN UNI=SUBST.APPLY (SUBSTITUTION GTERM &OPTIONAL FROM.COLOUR.key to.colour.key)
 
  ;;;  Input:   an arbitrary substitution, a term or a substitution and a flag
  ;;;  Effect:  substitution is applied to a copy of TERM.
  ;;;  Value:   NIL, if TERM = NIL, else substitution(term)
  ;;;  Notice:  in case of coloured substitutions, substitution will destructivly modified
  ;;;           in case of new colour-variables.
   
  (LET ((SYMBOL (DA-GTERM.SYMBOL GTERM)) (COLOUR (UNI=TERM.COLOUR GTERM FROM.COLOUR.KEY))
        BINDING TERMLIST NEW.GTERM new.colours)
    (COND ((DA-VARIABLE.IS SYMBOL)
	   (COND ((SETQ BINDING (GETF SUBSTITUTION SYMBOL))
		  (COND ((DA-XVARIABLE.IS COLOUR)
			 (COND ((SETQ NEW.GTERM (GETF BINDING COLOUR))
				(UNI=TERM.COPY NEW.GTERM NIL 'subst to.colour.key))
			       (T (SETQ NEW.GTERM (UNI=TERM.COPY (SECOND BINDING) T NIL to.COLOUR.KEY))
				  (SETF (GETF (GETF SUBSTITUTION SYMBOL) COLOUR) NEW.GTERM)
				  NEW.GTERM)))
			(T (UNI=TERM.COPY (SECOND BINDING) T NIL TO.COLOUR.KEY COLOUR))))
		 ((NEQ (DA-VARIABLE.SORT SYMBOL) (DA-TERM.SORT GTERM))
		  (SETQ NEW.GTERM (DA-TERM.CREATE (DA-VARIABLE.CREATE (DA-TERM.SORT GTERM)) NIL
						  (COND (TO.COLOUR.KEY (LIST TO.COLOUR.KEY COLOUR)))))
		  (SETQ SUBSTITUTION (NCONC SUBSTITUTION (LIST SYMBOL (LIST COLOUR NEW.GTERM))))
		  NEW.GTERM)
		 (T (UNI=TERM.COPY GTERM NIL from.COLOUR.KEY to.COLOUR.KEY))))
	  (T (COND ((AND (DA-XVARIABLE.IS COLOUR)
			 (SETQ BINDING (GETF SUBSTITUTION COLOUR)))
		    (SETQ COLOUR BINDING)))
	     (setq new.colours (cond (TO.COLOUR.KEY (LIST TO.COLOUR.KEY COLOUR))))
	     (COND ((MEMBER SYMBOL '(ALL EX))
		    (SETQ TERMLIST (DA-GTERM.TERMLIST GTERM))
		    (DA-FORMULA.CREATE SYMBOL
				       (LIST (CAR TERMLIST)
					     (UNI=SUBST.APPLY SUBSTITUTION (SECOND TERMLIST) from.COLOUR.KEY to.COLOUR.KEY))
				       new.colours))		     
		   (T (SETQ TERMLIST (MAPCAR #'(LAMBDA (SUBTERM)
						 (UNI=SUBST.APPLY SUBSTITUTION SUBTERM from.COLOUR.KEY to.COLOUR.KEY))
					     (DA-GTERM.TERMLIST GTERM)))
		      (CASE (TYPE-OF GTERM)
			    (TERM (DA-TERM.CREATE SYMBOL TERMLIST new.colours NIL))
			    (LITERAL (DA-LITERAL.CREATE (DA-LITERAL.SIGN GTERM) SYMBOL TERMLIST NIL new.colours))
			    (FORMULA (DA-FORMULA.CREATE SYMBOL TERMLIST new.colours))
			    (OTHERWISE (DA-GTERM.CREATE SYMBOL TERMLIST new.colours NIL)))))))))


(DEFUN UNI-SUBST.REPLACEMENTS (SUBSTITUTION GTERM &OPTIONAL from.COLOUR.KEY TO.COLOUR.KEY TAF)

  ;;;  Input:   an arbitrary substitution, a term or a substitution, a binding and a taf
  ;;;  Effect:  substitution is applied to a copy of \verb$GTERM$.
  ;;;  Value:   NIL, if \verb$GTERM$ = NIL, else \verb$SUBSTITUTION$(\verb$GTERM$)
   
  (LET ((SYMBOL (DA-GTERM.SYMBOL GTERM)) (COLOUR (UNI=TERM.COLOUR GTERM from.COLOUR.KEY))
        BINDING NEW.GTERM REPLACEMENTS)
    (COND ((DA-VARIABLE.IS SYMBOL)
	   (COND ((SETQ BINDING (GETF SUBSTITUTION SYMBOL))
		  (COND ((DA-XVARIABLE.IS COLOUR)
			 (COND ((SETQ NEW.GTERM (GETF BINDING COLOUR))
				(PUSH (CONS TAF (UNI=TERM.COPY NEW.GTERM NIL 'subst to.COLOUR.KEY))
				      REPLACEMENTS))
			       (T (SETQ NEW.GTERM (UNI=TERM.COPY (SECOND BINDING) T NIL TO.COLOUR.KEY))
				  (SETF (GETF (GETF SUBSTITUTION SYMBOL) COLOUR) NEW.GTERM)
				  (PUSH  (CONS TAF NEW.GTERM) REPLACEMENTS))))
			(T (PUSH (CONS TAF (UNI=TERM.COPY (SECOND BINDING) T NIL TO.COLOUR.KEY COLOUR))
				 REPLACEMENTS))))))
	  (T (COND ((AND (DA-XVARIABLE.IS COLOUR)
			 (SETQ BINDING (GETF SUBSTITUTION COLOUR)))
		    (PUSH (CONS (CONS (LIST 'COLOUR TO.colour.key) TAF) BINDING) REPLACEMENTS)))
	     (SETQ TAF (DA-TAF.CREATE.ZERO TAF))
	     (MAPCAN #'(LAMBDA (SUBTERM)
			 (SETQ TAF (DA-TAF.CREATE.NEXT TAF))
			 (UNI-SUBST.REPLACEMENTS SUBSTITUTION SUBTERM from.COLOUR.KEY TO.COLOUR.KEY TAF))
		     (DA-GTERM.TERMLIST GTERM))))))


(DEFUN UNI-SUBST.REPLACE (SUBSTITUTION GTERM &OPTIONAL from.COLOUR.KEY to.colour.key)

  ;;;  Input:   an arbitrary substitution, a term or a substitution and a binding
  ;;;  Effect:  substitution is applied to a copy of \verb$GTERM$.
  ;;;  Value:   NIL, if \verb$GTERM$ = NIL, else \verb$SUBSTITUTION$(\verb$GTERM$)
   
  (LET ((SYMBOL (DA-GTERM.SYMBOL GTERM)) (COLOUR (UNI=TERM.COLOUR GTERM from.COLOUR.KEY))
        BINDING NEW.GTERM)
    (COND ((DA-VARIABLE.IS SYMBOL)
	   (COND ((SETQ BINDING (GETF SUBSTITUTION SYMBOL))
		  (COND ((DA-XVARIABLE.IS COLOUR)
			 (COND ((SETQ NEW.GTERM (GETF BINDING COLOUR))
				(UNI=TERM.REPLACE GTERM (UNI=TERM.COPY NEW.GTERM NIL 'subst to.COLOUR.KEY)))
			       (T (SETQ NEW.GTERM (UNI=TERM.COPY (SECOND BINDING) T NIL to.COLOUR.KEY))
				  (SETF (GETF (GETF SUBSTITUTION SYMBOL) COLOUR) NEW.GTERM)
				  (UNI=TERM.REPLACE GTERM NEW.GTERM))))
			(T (UNI=TERM.REPLACE GTERM (UNI=TERM.COPY (SECOND BINDING) T NIL to.COLOUR.KEY COLOUR)))))))
	  (T (COND ((AND (DA-XVARIABLE.IS COLOUR)
			 (SETQ BINDING (GETF SUBSTITUTION COLOUR))
			 to.colour.key)
		    (SETF (GETF (DA-GTERM.COLOURS GTERM) to.colour.key) BINDING)))
	     (MAPC #'(LAMBDA (SUBTERM)
		       (UNI-SUBST.REPLACE SUBSTITUTION SUBTERM from.COLOUR.KEY to.colour.key))
		   (DA-GTERM.TERMLIST GTERM))))
    GTERM))


(DEFUN UNI=TERM.REPLACE (TERM NEW.TERM)

  (SETF (DA-GTERM.SYMBOL TERM) (DA-GTERM.SYMBOL NEW.TERM))
  (SETF (DA-TERM.TERMLIST TERM) (DA-TERM.TERMLIST NEW.TERM))
  (SETF (DA-TERM.COLOURS TERM) (DA-TERM.COLOURS NEW.TERM))
  (SETF (DA-TERM.ATTRIBUTES TERM) (DA-TERM.ATTRIBUTES NEW.TERM)))


(DEFUN UNI-SUBST.DOMAIN (SUBSTITUTION)
  
  ;;; Input:  an arbitrary substitution
  ;;; Value:  the domain of \verb$SUBSTITUTION$
  
  (SMAPCON #'(LAMBDA (VAR.COLOUR.TERMS)
	       (LIST (CAR VAR.COLOUR.TERMS)))
	   #'CDDR
	   SUBSTITUTION))



(DEFUN UNI-SUBST.VCOD (SUBSTITUTION)

  ;;; Input:  an arbitrary substitution
  ;;; Value:  the list of all variables occuring in the range of \verb$SUBSTITUTION$

  (SMAPCON #'(LAMBDA (VAR.COLOUR.TERMS)
	       (DA-GTERM.VARIABLES (SECOND (CAR VAR.COLOUR.TERMS))))
	   #'CDDR
	   (CDR SUBSTITUTION)))


(DEFUN UNI-SUBST.RESTRICTION (SUBSTITUTION APPLY.FCT)

  ;;; Input: an arbitrary substitution and a function
  ;;; Value: the substitution \verb$SUBSTITUTION$ without all those components which
  ;;;        are not satisfied by \verb$APPLY.FCT$ applied to the variable part

  (SMAPCON #'(LAMBDA (VAR.COLOUR.TERMS)
	       (COND ((FUNCALL APPLY.FCT (CAR VAR.COLOUR.TERMS))
		      (LIST (CAR VAR.COLOUR.TERMS) (SECOND VAR.COLOUR.TERMS)))))
	   #'CDDR
	   SUBSTITUTION))



(DEFUN UNI-SUBST.IS.VARIABLE.RENAMING (SUBSTITUTION)

  ;;; Input:  an arbitrary substitution
  ;;; Value:  T , if \verb$SUBSTITUTION$ is a variable renaming; NIL otherwise

  (LET (RIGHTHANDSIDES)
    (EVERYF #'(LAMBDA (IGNORE COLOUR.TERMS)
		(EVERYF #'(LAMBDA (COLOUR TERM)
			   (COND ((AND (DA-VARIABLE.IS (DA-GTERM.SYMBOL TERM))
				       (NOT (MEMBER TERM RIGHTHANDSIDES :TEST 'UNI-TERM.ARE.EQUAL))
				       (OR (NOT (DA-XVARIABLE.IS COLOUR))
					   (DA-XVARIABLE.IS (DA-GTERM.COLOUR TERM NIL))))
				  (PUSH TERM RIGHTHANDSIDES))))
			COLOUR.TERMS))
	    SUBSTITUTION)))


;;;;;****************************************************************************************************
;;;;;
;;;;;  Functions to generate and apply substitutions on terms
;;;;;
;;;;;****************************************************************************************************


(DEFUN UNI-TERMSUBST.CREATE (TERMSUBST OLD NEW)

  ;;; Input:  a term-substitution and two terms
  ;;; Effect: adds the pair \verb$OLD$ $\rightarrow$ \verb$NEW$ to \verb$TERMSUBST$ and also replaces all 
  ;;;         occurences of \verb$OLD$ in the codomain of \verb$TERMSUBST$ by \verb$NEW$.

  (LET ((SUBST (LIST OLD NEW)) FLAG)
    (CONS OLD (CONS NEW (MAPCAR #'(LAMBDA (ARG)
				    (COND ((SETQ FLAG (NOT FLAG)) ARG)             ; arg is domain
					  (T (UNI-TERMSUBST.APPLY SUBST ARG))))  ; arg is codomain
				TERMSUBST)))))

(DEFUN UNI-TERMSUBST.CREATE.PARALLEL (OLD.LIST NEW.LIST)

  ;;; Input:  two lists of terms
  ;;; Value:  a termsubstitution denoting the replacement of each element of \verb$OLD.LIST$ by its
  ;;;         corresponding element in \verb$NEW.LIST$.

  (MAPCAN #'(LAMBDA (OLD NEW)
		    (LIST OLD NEW))
	  OLD.LIST NEW.LIST))


(defun uni-termsubst.restriction (subst eval.function)

  ;;; Input:  a term-substitution and a lambda-expression
  ;;; Value:  the term-substitition with is restricted to those substitutions the domain
  ;;;         domain of which satisfies the test denoted by \verb$EVAL.FUNCTION$.

  (smapcon #'(lambda (rest.list)
	       (cond ((funcall eval.function (car rest.list))
		      (list (car rest.list) (second rest.list)))))
	   #'cddr
	   subst))


(DEFUN UNI-TERMSUBST.APPLY (TERMSUBST GTERM)

  ;;; Input:  a term-substitution and a gterm
  ;;; Effect: applies \verb$TERMSUBST$ to \verb$GTERM$ once and not recursively on changed terms (!!!)
  ;;; Value:  a copy of the changed \verb$GTERM$

  (LET ((SUBST TERMSUBST))
    (cond ((member (da-gterm.symbol gterm) '(all ex))
	   (da-GTERM.COPY.AND.CREATE 
	    GTERM :TERMLIST (list (car (DA-GTERM.TERMLIST GTERM))
				  (UNI-TERMSUBST.APPLY TERMSUBST (second (DA-GTERM.TERMLIST GTERM))))))
	  (t (WHILE (AND SUBST (NOT (UNI-GTERM.ARE.EQUAL (CAR SUBST) GTERM)))
	       (SETQ SUBST (CDDR SUBST)))
	     (COND (SUBST (DA-GTERM.COPY (SECOND SUBST)))
		   (T (DA-GTERM.COPY.AND.CREATE GTERM
						:TERMLIST (MAPCAR #'(LAMBDA (SUB)
								      (UNI-TERMSUBST.APPLY TERMSUBST SUB))
								  (DA-GTERM.TERMLIST GTERM)))))))))



(DEFUN UNI-TERMSUBST.DOMAIN (TERMSUBST)

  ;;; Input:  a term-substitution and a gterm
  ;;; Value:  a list of terms which will be substituted when applying the term-substitution

  (SMAPCON #'(LAMBDA (TERM1.TERM2)
	       (LIST (CAR TERM1.TERM2)))
	   #'CDDR
	   TERMSUBST))



;;;;;****************************************************************************************************
;;;;;
;;;;;  Functions to compute unifiers and matchers
;;;;;
;;;;;****************************************************************************************************


(defun uni=term.unify (TERM1 TERM2 &OPTIONAL COL.KEY1 COL.KEY2 SOLUTION inside.bindings)

  ;;;  Input:  two arbitrary terms
  ;;;  Effect: tries to unify TERM1 and TERM2 under the given bindings (under the theory of commutativity)
  ;;;          and in case of colored unification weakening may be applied to appropriate subterms
  ;;;  Value:  a list of abbreviations denoting the different solutions.

  (let* (new.key1 new.key2 solutions1 solutions2 new.sol
	 (left.decision (uni=weakening.decision TERM1 COL.KEY1 SOLUTION))
	 (right.decision (uni=weakening.decision TERM2 COL.KEY2 SOLUTION))
	 (branch (or (consp left.decision) (consp right.decision))))
    (cond ((or (neq 'standard left.decision) (neq 'standard right.decision))
	   (setq new.sol (uni=solution.create solution branch))
	   (cond ((neq 'standard left.decision) 
		  (setq new.key1 (cons 'colour (da-colour.faded)))
		  (cond ((consp left.decision) 
			 (push (cons new.sol left.decision) uni*weakening.decisions))))
		 (t (setq new.key1 COL.KEY1)))
	   (cond ((neq 'standard right.decision) 
		  (setq new.key2 (cons 'colour (da-colour.faded)))
		  (cond ((consp right.decision)
			 (push (cons new.sol right.decision) uni*weakening.decisions))))
		 (t (setq new.key2 COL.KEY2)))		 
	   (setq solutions1 (uni=term.unify.internal TERM1 TERM2 new.key1 new.key2 new.sol inside.bindings))))
   (setq new.sol (uni=solution.create solution branch))
   (setq solutions2  (uni=term.unify.internal TERM1 TERM2 COL.KEY1 COL.KEY2 new.sol inside.bindings))
   (nconc solutions1 solutions2)))


(defun uni=weakening.decision (term col.key solution)

  ;;; Input:  a gterm and indicators of a coloring and of a possible unifier.
  ;;; Effect: checks whether the actual term can / has to / or may not be weakened. A term 
  ;;;         is weakeable if \verb$uni*weakening$ is not empty and there is no prior 
  ;;;         decision to keep it not weakened.
  ;;;         UNI*WEAKENING.DECISION is a triple: (SOLUTION (var1 w.t1 ... varn wtn) (wt'1 ... wt'k))
  ;;;         with $wt_i$ a dotted pair of weakening indicator and actual weakening part number.
  ;;; Value:  either \verb$STANDARD$ if the term may not be weakend, \verb$WEAKENING$ if the
  ;;;         term has to be weakened, or a list \verb$(???)$ if the term can be weakened.

  (cond ((or (null col.key) (and (consp col.key) (eq (car col.key) 'colour))) 'standard)
	(t (let ((weakening (getf (getf (da-gterm.attributes term) 'uni*weakening) col.key))
		 decision var.conds)
	     (cond ((null weakening) 'standard)
		   (t (setq decision (find-if #'(lambda (decision)
						  (uni=solution.covers.solution (car decision) solution))
					      uni*weakening.decisions))
		      (cond ((cddr weakening)
			     (setq var.conds (append (second decision) (third weakening)))
			     (push (list solution var.conds (third decision)) uni*weakening.decisions))
			    (t (setq var.conds (second decision))))
		      (cond ((member (car weakening) (third decision)) 'weakening)
			    ((eql (1+ (count-if #'(lambda (id) (eq (car id) (caar weakening))) (third decision)))
				  (second weakening)) 'standard)
			    (t (list var.conds (cons (car weakening) (third decision)))))))))))



(DEFUN UNI=TERM.UNIFY.internal (TERM1 TERM2 &OPTIONAL COL.KEY1 COL.KEY2 SOLUTION inside.bindings)
  
  ;;;  Input:  two arbitrary terms
  ;;;  Effect: tries to unify TERM1 and TERM2 under the given bindings (under the theory of commutativity).
  ;;;  Value:  a list of abbreviations denoting the different solutions.
  
  (LET* ((SORT.OF.T1 (DA-TERM.SORT TERM1)) (SORT.OF.T2 (DA-TERM.SORT TERM2))
	 (SYMBOL1 (DA-TERM.SYMBOL TERM1)) (SYMBOL2 (DA-TERM.SYMBOL TERM2))
	 (COMMUTATIVE? (AND UNI*THEORY.UNIFICATION (DA-SYMBOL.HAS.ATTRIBUTE SYMBOL1 'COMMUTATIVE))))

    (COND ((AND (NOT inside.bindings) (UNI=GTERM.TAF.RELATION.FAILURE TERM1 TERM2)) NIL)
	  ((AND (EQ TERM1 TERM2) (EQ COL.KEY1 COL.KEY2)) (LIST SOLUTION))
	  ((AND (UNI=VARIABLE.IS SYMBOL1 SOLUTION)
		(DA-SORT.IS.SUBSORT SORT.OF.T2 SORT.OF.T1)
		(NOT (and (UNI=VARIABLE.IS SYMBOL2 SOLUTION) 
			  (UNI=GET.var.BINDING SYMBOL2 NIL SOLUTION)))
		(OR (NOT (UNI=VARIABLE.IS SYMBOL2 SOLUTION))
		    (uni=get.var.binding symbol1 nil solution)
		    (uni=variable.is (UNI=TERM.COLOUR TERM1 COL.KEY1) SOLUTION)))
	   (UNI=TERM.VARIABLE.UNIFY TERM1 TERM2 COL.KEY1 COL.KEY2 SOLUTION))
	  ((UNI=VARIABLE.IS SYMBOL2 SOLUTION)
	   (UNI=TERM.VARIABLE.UNIFY TERM2 TERM1 COL.KEY2 COL.KEY1 SOLUTION))
	  ((AND (EQ SYMBOL1 SYMBOL2)
		(UNI=COLOUR.UNIFY (UNI=TERM.COLOUR TERM1 COL.KEY1)
				  (UNI=TERM.COLOUR TERM2 COL.KEY2)
				  SOLUTION))
	   (NCONC (UNI=TERMLIST.UNIFY (DA-GTERM.TERMLIST TERM1) (DA-GTERM.TERMLIST TERM2)
				      COL.KEY1 COL.KEY2 (UNI=SOLUTION.CREATE SOLUTION COMMUTATIVE?)
				      inside.bindings)
		  (COND (COMMUTATIVE?
			 (UNI=TERMLIST.UNIFY (DA-GTERM.TERMLIST TERM1) (REVERSE (DA-GTERM.TERMLIST TERM2))
					     COL.KEY1 COL.KEY2 
					     (UNI=SOLUTION.CREATE SOLUTION COMMUTATIVE?)
					     inside.bindings))))))))


(DEFUN UNI=TERM.VARIABLE.UNIFY (TERM1 TERM2 COL.KEY1 COL.KEY2 SOLUTION)
  
  ;;;  Input:  a variable and a terms and an abbreviation
  ;;;  Effect: tries to bind TERM2 at the variable SYMBOL1 or if SYMBOL1 has already a binding
  ;;;          unifies this binding with TERM2.
  ;;;  Value:  a list of abbreviations denoting the different solutions.

  (LET* ((SYMBOL1 (DA-TERM.SYMBOL TERM1)) (SYMBOL2 (DA-TERM.SYMBOL TERM2))
	 (COLOUR1 (UNI=TERM.COLOUR TERM1 COL.KEY1)) (COLOUR2 (UNI=TERM.COLOUR TERM2 COL.KEY2))
	 TERM COL.KEY)
    (COND ((NOT (DA-SORT.IS.SUBSORT (da-term.sort term2) (da-term.sort term1))) nil)
	  ((AND (NOT (DA-XVARIABLE.IS COLOUR1)) (NOT (DA-XVARIABLE.IS COLOUR2)) 
		(NOT (UNI-COLOUR.ARE.EQUAL COLOUR1 COLOUR2)))
	   NIL)
	  ((AND (EQ SYMBOL1 SYMBOL2) (UNI-COLOUR.ARE.EQUAL COLOUR1 COLOUR2))
	   (LIST SOLUTION))
	  ((MULTIPLE-VALUE-SETQ (TERM COL.KEY) (UNI=GET.var.BINDING SYMBOL1 COLOUR1 SOLUTION))
	   (cond ((and (null col.key) col.key2)   ; this color has no binding, check term-compatibility
		  (UNI=SET.BINDING SYMBOL1 COLOUR1 SOLUTION TERM2 COL.KEY2)
		  (setq col.key2 nil)))
	   (UNI=WITH.VARIABLE.EXPANSION SYMBOL1 SYMBOL2
	       (UNI=TERM.UNIFY TERM TERM2 COL.KEY COL.KEY2 SOLUTION T)))
	  (T (UNI=SET.BINDING SYMBOL1 COLOUR1 SOLUTION TERM2 COL.KEY2)
	     (COND ((and colour1 (not (uni=variable.is colour1 SOLUTION)))
		    (UNI=term.unify term2 term2 (cons 'colour colour1) col.key2 solution t))
		   (T (LIST SOLUTION)))))))



(DEFMACRO UNI=WITH.VARIABLE.EXPANSION (SYMBOL SYMBOL2 &BODY BODY)

  `(COND ((DA-VARIABLE.EXPANSION ,SYMBOL) NIL)
	 (T (COND ((DA-FUNCTION.IS ,SYMBOL2) (SETF (DA-VARIABLE.EXPANSION ,SYMBOL) T)))
	    (PROG1 (PROGN ,@BODY)
	      (SETF (DA-VARIABLE.EXPANSION ,SYMBOL) NIL)))))



(DEFUN UNI=TERMLIST.UNIFY (TL1 TL2 COL.KEY1 COL.KEY2 SOLUTION &optional inside.bindings)
  
  ;;;  Input:  two arbitrary termlists and an abbreviation
  ;;;  Effect: tries to unify both termlists.
  ;;;  Value:  a list of abbreviations denoting the different solutions.
  
  (COND ((NULL TL1) (LIST SOLUTION))
	(T (MAPCAN #'(LAMBDA (SOLUTION)
		       (UNI=TERMLIST.UNIFY (CDR TL1) (CDR TL2) COL.KEY1 COL.KEY2 SOLUTION inside.bindings))
		   (UNI=TERM.UNIFY (CAR TL1) (CAR TL2) COL.KEY1 COL.KEY2 SOLUTION inside.bindings)))))


(DEFUN UNI=COLOUR.UNIFY (COLOUR1 COLOUR2 SOLUTION)

  (LET (BINDING)
    (COND ((OR (NULL COLOUR1) (UNI-COLOUR.ARE.EQUAL COLOUR1 COLOUR2)) T)
	  ((AND (DA-XVARIABLE.IS COLOUR1)
		(SETQ BINDING (UNI=GET.col.BINDING COLOUR1 SOLUTION)))
	   (UNI=COLOUR.UNIFY BINDING COLOUR2 SOLUTION))
	  ((AND (DA-XVARIABLE.IS COLOUR2)
		(SETQ BINDING (UNI=GET.col.BINDING COLOUR2 SOLUTION)))
	   (UNI=COLOUR.UNIFY COLOUR1 BINDING SOLUTION))
	  ((DA-XVARIABLE.IS COLOUR1)
	   (UNI=SET.BINDING COLOUR1 NIL SOLUTION COLOUR2)
	   T)
	  ((DA-XVARIABLE.IS COLOUR2)
	   (UNI=SET.BINDING COLOUR2 NIL SOLUTION COLOUR1)
	   T))))





;;;;;****************************************************************************************************
;;;;;
;;;;;  Functions to generate an explicit substitution:
;;;;;
;;;;;****************************************************************************************************


(DEFUN UNI=GENERATE.UNIFIERS (SOLUTIONS STACK.DEPTH)

  ;;;  Input:  a list of abbreviations and a number, denoting the depth of the actual binding stack

  (LET (UNIFIERS)
    (MAPC #'(LAMBDA (SOLUTION)
	      (CATCH 'UNI*OCCUR.CHECK.FAILED
		 (uni=unifier.insert.weakening solution)
		 (UNI=BINDINGS.EXPAND SOLUTION STACK.DEPTH)
		 (PUSH (UNI=UNIFIER.CREATE SOLUTION STACK.DEPTH)
		       UNIFIERS)))
	  SOLUTIONS)
     (UNI=VARIABLE.EXPANSION.RELEASE UNI*NO.OF.BINDINGS STACK.DEPTH)
     (setq uni*weakening.decisions  nil)
     (REVERSE UNIFIERS)))



(DEFUN UNI=UNIFIER.CREATE (SOLUTION STACK.DEPTH)

  (LET ((STACK.POINTER UNI*NO.OF.BINDINGS) UNIFIER VAR binding)
    (WHILE (> STACK.POINTER STACK.DEPTH)
      (DECF STACK.POINTER)
      (SETQ VAR (AREF UNI*STACK STACK.POINTER 0))
      (COND ((DA-VARIABLE.IS VAR)
	     (SOMEF #'(LAMBDA (SOLUTION2 ENTRY)
			(COND ((UNI=SOLUTION.COVERS.SOLUTION SOLUTION2 SOLUTION)
			       (COND ((AND ENTRY (NOT (GETF UNIFIER VAR)))
				      (setq binding nil)
				      (mapcf #'(lambda (colour term.col.key)
						 (push (car term.col.key) binding)
						 (push colour binding))
					     ENTRY)
				      (PUSH binding UNIFIER)
				      (PUSH VAR UNIFIER))))))
		    (DA-VARIABLE.BINDING VAR)))
	    (T (SOMEF #'(LAMBDA (SOLUTION2 ENTRY)
			(COND ((UNI=SOLUTION.COVERS.SOLUTION SOLUTION2 SOLUTION)
			       (PUSH ENTRY UNIFIER)
			       (PUSH VAR UNIFIER))))
		      (DA-XVARIABLE.BINDING VAR)))))
    unifier))


(defun uni=unifier.insert.weakening (solution)

  (let ((decision (find-if #'(lambda (entry) (uni=solution.covers.solution (car entry) solution)) 
			   uni*weakening.decisions)))
    (cond (decision
	   (mapcf #'(lambda (var weakening.terms)
		      (cond ((null (set-difference weakening.terms (third decision)))
			     (cond ((consp var)
				    (uni=set.binding (car var) (cdr var) solution
						     (da-term.create (car var) nil (list 'subst (da-colour.faded)))
						     'subst))
				   (t (uni=set.binding var nil solution (da-colour.faded) nil))))))
		  (second decision))))))



(DEFUN UNI=BINDINGS.EXPAND (SOLUTION STACK.DEPTH)
  
  ;;;  Input:  an abbreviation and a number, denoting the depth of the actual binding stack
  ;;;  Value:  a list of one substitution, generated by expanding the bindings
  ;;;  Note:   there is a THROW to UNI*OCCUR.CHECK.FAILED inside, which is called if the occur
  ;;;          check fails.
  
  (LET ((STACK.POINTER UNI*NO.OF.BINDINGS) VAR CONSIDERED.VARS)
    (WHILE (> STACK.POINTER STACK.DEPTH)
      (DECF STACK.POINTER)
      (SETQ VAR (AREF UNI*STACK STACK.POINTER 0))
      (COND ((NOT (MEMBER VAR CONSIDERED.VARS))
	     (PUSH VAR CONSIDERED.VARS)
	     (cond ((da-variable.is var)
		    (MAPCF #'(LAMBDA (SOLUTION2 COLOUR.TERMS)
			       (COND ((UNI=SOLUTION.COVERS.SOLUTION SOLUTION2 SOLUTION)
				      (SMAPL #'(LAMBDA (COLOUR.TERM.COLOUR.KEY)
						 (SETF (SECOND COLOUR.TERM.COLOUR.KEY)
						       (CONS (UNI=TERM.EXPAND
							      (CAR (SECOND COLOUR.TERM.COLOUR.KEY))
							      SOLUTION (CDR (SECOND COLOUR.TERM.COLOUR.KEY)))
							     'subst)))
					     #'CDDR
					     COLOUR.TERMS))))
			   (DA-VARIABLE.BINDING VAR)))
		   (t (MAPCF #'(LAMBDA (SOLUTION2 COLOUR.TERMS)
				 (COND ((UNI=SOLUTION.COVERS.SOLUTION SOLUTION2 SOLUTION)
					(UNI=COLOUR.EXPAND COLOUR.TERMS SOLUTION))))
			     (DA-XVARIABLE.BINDING VAR)))))))))


(DEFUN UNI=TERM.EXPAND (GTERM SOLUTION COL.KEY)
  
  ;;;  Input:   an arbitrary term
  ;;;  Effect:  expands the term by using its bindings
  ;;;  Value:   the expanded term
  ;;;  Note:    if the occur-check failed, it jumps to the label "UNI*OCCUR.CHECK.FAILED"
  ;;;           you will have to "CATCH" it

  (LET ((SYMBOL (DA-TERM.SYMBOL GTERM)) (COLOUR (UNI=TERM.COLOUR GTERM COL.KEY))
        BINDING NEW.COL.KEY)
    (COND ((NOT (DA-VARIABLE.IS SYMBOL))
	   (DA-TERM.CREATE SYMBOL
			   (MAPCAR #'(LAMBDA (SUBTERM)
				      (UNI=TERM.EXPAND SUBTERM SOLUTION COL.KEY))
				  (DA-GTERM.TERMLIST GTERM))
			   (COND (COLOUR (LIST 'SUBST (UNI=COLOUR.EXPAND COLOUR SOLUTION))))))

	  ((DA-VARIABLE.EXPANSION SYMBOL)                    ; occur-check fail, exit routine.
	   (THROW ' UNI*OCCUR.CHECK.FAILED 'FAIL))
	  
	  ((NOT (UNI=VARIABLE.IS SYMBOL SOLUTION))                    ; variable is assumed as constant. Copy var.
	   (UNI=TERM.COPY GTERM NIL COL.KEY 'SUBST))
	  
	  ((MULTIPLE-VALUE-SETQ (BINDING NEW.COL.KEY)        ; variable has a binding
	     (UNI=GET.VAR.BINDING SYMBOL COLOUR SOLUTION))
	   (COND ((AND (CONSP NEW.COL.KEY) (EQ (CAR NEW.COL.KEY) 'COLOUR))   ; make color-constant explicit!
		  (SETQ BINDING (UNI=TERM.COPY BINDING T NIL 'SUBST (CDR NEW.COL.KEY)))))
	   (COND ((OR (NEQ SYMBOL (DA-TERM.SYMBOL BINDING)) (NEQ COLOUR (UNI=TERM.COLOUR BINDING NEW.COL.KEY)))
		  (UNI=WITH.VARIABLE.EXPANSION SYMBOL (DA-TERM.SYMBOL BINDING)
		     (UNI=TERM.EXPAND BINDING SOLUTION NEW.COL.KEY)))
		 (T BINDING)))

	  (T (UNI=TERM.COPY GTERM NIL COL.KEY 'SUBST)))))     ; variable has no bindings


(DEFUN UNI=COLOUR.EXPAND (COLOUR SOLUTION)

  (LET (BINDING)
    (COND ((DA-XVARIABLE.IS COLOUR)
	   (COND ((NOT (UNI=VARIABLE.IS COLOUR SOLUTION)) COLOUR)
		 ((SETQ BINDING (UNI=GET.col.BINDING COLOUR SOLUTION))
		  (UNI=COLOUR.EXPAND BINDING SOLUTION))
		 (T COLOUR)))
	  (T COLOUR))))


(DEFUN UNI=VARIABLE.EXPANSION.RELEASE (CURSOR STACK.DEPTH)
  (WHILE (> CURSOR STACK.DEPTH)
    (DECF CURSOR)
    (COND ((DA-VARIABLE.IS (AREF UNI*STACK CURSOR 0))
	   (SETF (DA-VARIABLE.EXPANSION (AREF UNI*STACK CURSOR 0)) NIL))
	  (T (SETF (DA-XVARIABLE.EXPANSION (AREF UNI*STACK CURSOR 0)) NIL)))))



(DEFUN UNI=SOLUTION.COVERS.SOLUTION (SOL1 SOL2)

  (COND ((EQ SOL1 SOL2))
	((NULL SOL2) NIL)
	(T (UNI=SOLUTION.COVERS.SOLUTION SOL1 (CAR SOL2)))))


;;;;;****************************************************************************************************
;;;;;
;;;;;  auxiliary functions
;;;;;
;;;;;****************************************************************************************************


(DEFUN UNI=VARIABLE.IS (VAR &optional solution)
  
  ;;;  Input:  a s-expression
  ;;;  Value:  T, if VAR is a variable and not set to UNI.CONSTANT, otherwise NIL

  (cond ((DA-VARIABLE.IS VAR)
	 (NEQ (UNI=GET.var.BINDING VAR NIL solution) 'UNI.CONSTANT))
	((DA-XVARIABLE.IS VAR)
	 (NEQ (UNI=GET.col.BINDING VAR solution) 'UNI.CONSTANT))))


(DEFUN UNI=FIND.VARIABLES (EXPRESSION &OPTIONAL VARIABLES)

  ;;;  Input:  a term or termlist (with bindings) and a buffer
  ;;;  Value:  a list of all variables (not declared to constants !) in EXPRESSION

  (COND ((LISTP EXPRESSION)
	 (MAPC #'(LAMBDA (EXPRESSION)
		   (SETQ VARIABLES (UNI=FIND.VARIABLES EXPRESSION VARIABLES)))
	       EXPRESSION)
         VARIABLES)
	((DA-TERM.IS EXPRESSION)
	 (COND ((DA-XVARIABLE.IS (UNI=TERM.COLOUR EXPRESSION NIL))
		 (PUSH (UNI=TERM.COLOUR EXPRESSION NIL) VARIABLES)))
	 (COND ((DA-VARIABLE.IS (DA-TERM.SYMBOL EXPRESSION))
		(PUSH (DA-TERM.SYMBOL EXPRESSION) VARIABLES))
	       (T (UNI=FIND.VARIABLES (DA-TERM.TERMLIST EXPRESSION) VARIABLES))))))


;;;;;****************************************************************************************************
;;;;;
;;;;;  Functions for manipulating binding and expansion slots
;;;;;
;;;;;****************************************************************************************************


(DEFUN UNI=SET.CONSTANTS (VARIABLES &OPTIONAL SOLUTION)
  
  ;;; Input:   a list of variables
  ;;; Effect:  set each variable of VARIABLES to UNI.CONSTANT and pushes their names on
  ;;;          the UNI*STACK; pushes the old UNI*STACK.GLOBAL.POINTER to the UNI*POINTER-STACK
  ;;; Value:   undefined

  (MAPC #'(LAMBDA (VAR)
	    (UNI=SET.BINDING VAR NIL SOLUTION 'UNI.CONSTANT))
	VARIABLES))


(DEFUN UNI=SET.BINDINGS (SUBSTITUTION &OPTIONAL SOLUTION COL.KEY)

  ;;;  Input:   a list of substitutions
  ;;;  Effect:  binds each variable of a pair of SUBSTITUTION to its corresponding term and pushes
  ;;;           their names on the UNI*STACK; pushes the old UNI*STACK.GLOBAL.BINDING to the UNI*POINTER-STACK
  ;;;  Value:   undefined

  (MAPCF #'(LAMBDA (VAR SUB.LIST)
	     (COND ((DA-VARIABLE.IS VAR)
		    (MAPCF #'(LAMBDA (COLOUR TERM)
			       (UNI=SET.BINDING VAR COLOUR SOLUTION TERM COL.KEY))
			   SUB.LIST))
		   (T (UNI=SET.BINDING VAR NIL SOLUTION SUB.LIST))))
	 SUBSTITUTION))


(DEFUN UNI=SET.BINDING (VAR COLOUR SOLUTION TERM &OPTIONAL COL.KEY)

  ;;; Input:   a variable, its colour, a solution key, a term, and a colour key
  ;;; Effect:  inserts binding VAR -> TERM under the given environments.
  ;;; Value:   undefined.

  (COND ((NOT (DA-XVARIABLE.IS COLOUR)) (SETQ COLOUR NIL)))
  (SETF (AREF UNI*STACK UNI*NO.OF.BINDINGS 0) VAR)
  (SETF (AREF UNI*STACK UNI*NO.OF.BINDINGS 1) SOLUTION)
  (SETF (AREF UNI*STACK UNI*NO.OF.BINDINGS 2) COLOUR)
  (COND ((DA-VARIABLE.IS VAR)
	 (SETF (GETF (GETF (DA-VARIABLE.BINDING VAR) SOLUTION) COLOUR) (CONS TERM COL.KEY)))
	(T (SETF (GETF (DA-XVARIABLE.BINDING VAR) SOLUTION) TERM)))
  (INCF UNI*NO.OF.BINDINGS))


(DEFUN UNI=GET.VAR.BINDING (VAR COLOUR SOLUTION)

  ;;; Input:   a variable, a colour or nil, and a solution key
  ;;; Effect:  see value.
  ;;; Value:   a multiple value, the first value is the binding of the (colored) variable
  ;;;          while the second value is either a color key in case the colored variable has
  ;;;          a binding, or e.g. list (COLOUR red) overwriting the color information in the
  ;;;          binding, or nil specifying that only a non-colored binding is available and
  ;;;          any coloring is ok.

  (let (binding col.key sol)
    (SOMEF #'(LAMBDA (SOLUTION2 ENTRY)
	       (COND ((UNI=SOLUTION.COVERS.SOLUTION SOLUTION2 SOLUTION)
		      (cond ((DA-XVARIABLE.IS COLOUR)
			     (cond ((setq sol (getf entry colour))
				    (setq col.key (cdr sol) binding (car sol)))
				   ((second entry)
				    (setq col.key nil binding (car (second entry))))))
			    (colour (setq col.key (cons 'colour colour) binding (car (second entry))))
			    (t (setq col.key nil binding (car (second entry))))))))
	   (DA-VARIABLE.BINDING VAR))
    (values binding col.key)))


(DEFUN UNI=GET.COL.BINDING (VAR SOLUTION)

  ;;; Input:  a variable and an indicator of a solution
  ;;; Value:  the actual binding of that variable

  (SOMEF #'(LAMBDA (SOLUTION2 ENTRY)
	     (COND ((UNI=SOLUTION.COVERS.SOLUTION SOLUTION2 SOLUTION) 
		    ENTRY)))
	 (DA-XVARIABLE.BINDING VAR)))



(DEFUN UNI=RESET.BINDINGS (DEPTH)
  
  ;;;  Effect:  resets all bindings and expansions of variables
  ;;;           fond between UNI*STACK.LOCAL.BINDINGS and UNI*STACK.GLOBAL.BINDINGS
  ;;;   Value:  undefined
  ;;;    Note:  modifies UNI*STACK.LOCAL.BINDINGS

  (WHILE (> UNI*NO.OF.BINDINGS DEPTH)
    (UNI=RESET.NEXT.BINDING)))


(DEFUN UNI=RESET.NEXT.BINDING ()

  ;;; Input:   none
  ;;; Effect:  deletes the last entry of UNI*STACK and restores the old bindings.
  ;;; Value :  undefined

  (DECF UNI*NO.OF.BINDINGS)
  (LET ((VAR (AREF UNI*STACK UNI*NO.OF.BINDINGS 0)))
    (COND ((DA-VARIABLE.IS VAR)
	   (REMF (GETF (DA-VARIABLE.BINDING VAR) (AREF UNI*STACK UNI*NO.OF.BINDINGS 1))
		 (AREF UNI*STACK UNI*NO.OF.BINDINGS 2)))
	  (T (REMF (DA-XVARIABLE.BINDING VAR) (AREF UNI*STACK UNI*NO.OF.BINDINGS 1))))))


;;;;;========================================================================================================
;;;;;========================================================================================================
;;;;;
;;;;;  Colouring of gterms
;;;;;
;;;;;========================================================================================================
;;;;;========================================================================================================


(DEFUN UNI-GTERM.COLOURIZE (GTERM1 GTERM2 &OPTIONAL (COND1 T) (COND2 T) AC.ALLOWED)
  
  ;;; Input  : two gterms and two flags
  ;;; Effect : creates pairs of coloured terms t1, t2 such that $\chi$(t1) = $\chi$(t2) and  $\chi$(t1) is maximal.
  ;;; Value  : a list of solution indicators.
  
  (UNI=GTERM.COLOURIZE.MERGE GTERM1 GTERM2 
			     (UNI=GTERM.COLOURIZE GTERM1 GTERM2 NIL COND1 COND2 NIL NIL AC.ALLOWED)))



(DEFUN UNI-TERM.DIFF.MATCH (GTERM1 GTERM2 &OPTIONAL VARIABLES FIXED.COLOUR ac.allowed)
  
  ;;; Input  : two gterms and a list of variables and a flag
  ;;; Effect : creates a colouring of \verb$GTERM2$ such that its skeleton is an instance of \verb$GTERM1$
  ;;;          In case \verb$FIXED.COLOUR$ is non-NIL, \verb$GTERM2$ is coloured by a fixed colour 'COLOURED instead
  ;;;          of different colour-variables.
  ;;; value  : a list of numbers denoting the different solutions
  
  (LET* (SETS.OF.COLOURS NAMES (counter (FLOOR (/ (LENGTH (DA-GTERM.COLOURS GTERM1)) 2))))
	(MAPC #'(LAMBDA (VAR) (SETF (DA-VARIABLE.BINDING VAR) 'EMPTY)) VARIABLES)
	(UNWIND-PROTECT (PROGN (SETQ SETS.OF.COLOURS (UNI=GTERM.DIFF.MATCH GTERM1 GTERM2 ac.allowed))
			       (SETQ NAMES (MAPCAR #'(LAMBDA (X) (DECLARE (IGNORE X)) (LIST (incf COUNTER))) SETS.OF.COLOURS)))
	  (MAPC #'(LAMBDA (VAR) (SETF (DA-VARIABLE.BINDING VAR) NIL)) VARIABLES))
	(COND (SETS.OF.COLOURS
	       (UNI=GTERM.COLOURIZE.INSERT.COLOURS GTERM2
						   (mapcar #'(lambda (set)
							       (cons (uni=Gterm.colour.normalize.set set) nil))
							   SETS.OF.COLOURS)
						   NAMES FIXED.COLOUR)
	       NAMES))))


(DEFUN UNI=GTERM.COLOUR.NORMALIZE.SET (SET.OF.COLOURS)
  (MAPCAN #'(LAMBDA (COLOUR)
	      (COND ((CONSP COLOUR) (COPY-LIST (SECOND COLOUR)))
		    (T (LIST COLOUR))))
	  SET.OF.COLOURS))




;;;;;============================================================================================================
;;;;; Section:  Difference Matching
;;;;;
;;;;;============================================================================================================



(DEFMACRO UNI=GTERM.INT.COLOURS (GTERM)
  
  `(GETF (DA-GTERM.ATTRIBUTES ,GTERM) 'COLOUR))



(DEFUN UNI=GTERM.DIFF.MATCH (GTERM1 GTERM2 &optional ac.allowed)
  
  ;;; Input:  two terms, a list of list like (f i1 i2 ...)
  ;;; Effect: colourizes GTERM1 such that the skeleton of GTERM1 is an instance of GTERM2.
  ;;; Value:  
  
  (LET ((SYMBOL (DA-GTERM.SYMBOL GTERM1)))
       (COND ((AND (DA-VARIABLE.IS SYMBOL)
		   (DA-VARIABLE.BINDING SYMBOL))
	      (LIST (LIST (LIST SYMBOL (UNI=GTERM.COLOURIZE.TOTALLY GTERM2) GTERM2))))
	     (T (MAPCAN #'(LAMBDA (TAF)
				  (UNI=GTERM.TERMLIST.DIFF.MATCH GTERM1 (DA-ACCESS TAF GTERM2) ac.allowed))
			(DA-SYMBOL.OCCURS.IN.GTERM SYMBOL GTERM2))))))


(DEFUN UNI=GTERM.TERMLIST.DIFF.MATCH (GTERM1 GTERM2 &optional ac.allowed)
  
  ;;; Input:  two gterms, a term access function
  ;;; Effect: colourizeS GTERM1 such that the skeleton of GTERM1 is an instance of GTERM2
  ;;; Value:  a list of sets of colours with denotes the sets of compatible colourings
  
  (LET (LIST.OF.ALTERNATIVES)
       (NCONC (COND ((EVERY #'(LAMBDA (SUBTERM1 SUBTERM2)
				      (CAR (PUSH (UNI=GTERM.DIFF.MATCH SUBTERM1 SUBTERM2 ac.allowed)
						 LIST.OF.ALTERNATIVES)))
			    (DA-GTERM.TERMLIST GTERM1) (DA-GTERM.TERMLIST GTERM2))
		     (UNI=GTERM.COLOURIZE.MERGE.ALTERNATIVES LIST.OF.ALTERNATIVES GTERM2)))
	      (COND ((AND UNI*THEORY.UNIFICATION
			  (DA-SYMBOL.HAS.ATTRIBUTE (DA-GTERM.SYMBOL GTERM1) 'COMMUTATIVE)
			  (PROGN (SETQ LIST.OF.ALTERNATIVES NIL)
				 (EVERY #'(LAMBDA (SUBTERM1 SUBTERM2)
						  (CAR (PUSH (UNI=GTERM.DIFF.MATCH SUBTERM1 SUBTERM2 ac.allowed)
							     LIST.OF.ALTERNATIVES)))
					(REVERSE (DA-GTERM.TERMLIST GTERM1)) (DA-GTERM.TERMLIST GTERM2))))
		     (UNI=GTERM.COLOURIZE.MERGE.ALTERNATIVES LIST.OF.ALTERNATIVES GTERM2))))))


(DEFUN UNI=GTERM.COLOURIZE.MERGE.ALTERNATIVES (LIST.OF.ALTERNATIVES GTERM1 &OPTIONAL GTERM2 OLD.COL1 OLD.COL2)
  (LET (COLOUR (ALTERNATIVES (LIST NIL)))
       (MAPC #'(LAMBDA (SETS)
		       (SETQ ALTERNATIVES
			     (MAPCAN #'(LAMBDA (ALTS)
					       (MAPCAN #'(LAMBDA (COLOURS)
								 (UNI=GTERM.COLOURIZE.MERGE.COLS COLOURS ALTS))
						       SETS))
				     ALTERNATIVES)))
	     LIST.OF.ALTERNATIVES)
       (SETQ COLOUR (DA-COLOUR.CREATE.VARIABLE))
       (PUSH COLOUR (UNI=GTERM.INT.COLOURS GTERM1))
       (COND (GTERM2  (PUSH COLOUR (UNI=GTERM.INT.COLOURS GTERM2))))
       (COND (OLD.COL1 (PUSH COLOUR (GETF UNI*COLOUR.BINDINGS (CAR OLD.COL1)))))
       (COND (OLD.COL2 (PUSH COLOUR (GETF UNI*COLOUR.BINDINGS (CAR OLD.COL2)))))
       (MAPL #'(LAMBDA (COLOURS) (PUSH COLOUR (CAR COLOURS)))
	     ALTERNATIVES)
       ALTERNATIVES))


(DEFUN UNI=GTERM.COLOURIZE.TOTALLY (GTERM)
  (LET ((COLOUR  (DA-COLOUR.CREATE.VARIABLE)))
       (PUSH COLOUR (UNI=GTERM.INT.COLOURS GTERM))
       (CONS COLOUR (MAPCAN #'UNI=GTERM.COLOURIZE.TOTALLY (DA-GTERM.TERMLIST GTERM)))))


;;;;;=============================================================================================================
;;;;; Section:  COLOURING TERMS
;;;;;
;;;;;=============================================================================================================


(DEFUN UNI=GTERM.COLOURIZE (GTERM1 GTERM2 NON.MAX.PARTS STATE1 STATE2 COLOURS1 COLOURS2 &optional ac.allowed)
  
  ;;; Input:  two gterms, a list of list like (f i1 i2 ...) and two states (see UNI=COLOUR.PARSING)
  ;;; Effect: colourizes both terms according to their states such that w(GTERM1) = w(GTERM2) holds.
  ;;; Value:  a list of pairs of coloured versions of GTERM1 and GTERM2 with the property above.
  
  (LET* (NEW.STATE1 SUBTERM2 NON.MAX (COUNTER 0) (SYMBOL (DA-GTERM.SYMBOL GTERM1))
	 (OLD.COL1 (INTERSECTION COLOURS1 (UNI=GTERM.INT.COLOURS GTERM1))) OLD.COL2
	 (AC (AND (DA-FUNCTION.IS SYMBOL)
		  UNI*THEORY.UNIFICATION
		  ac.allowed
		  (DA-SYMBOL.HAS.ATTRIBUTE SYMBOL 'COMMUTATIVE)
		  (DA-SYMBOL.HAS.ATTRIBUTE SYMBOL 'ASSOCIATIVE))))
    (COND ((AND (NEQ STATE1 'FAIL) (NEQ STATE2 'FAIL))
	   (NCONC (COND ((OR (NULL COLOURS1) OLD.COL1)
			 (MAPCAN #'(LAMBDA (TAF)
					   (SETQ SUBTERM2  (DA-ACCESS TAF GTERM2))
					   (COND ((OR (NULL COLOURS2)
						      (SETQ OLD.COL2 (INTERSECTION (UNI=GTERM.INT.COLOURS SUBTERM2)
										   COLOURS2)))
						  (UNI=GTERM.TERMLIST.COLOURIZE 
						   GTERM1 SUBTERM2
						   STATE1 (COND (TAF (UNI=COLOUR.PARSING.TABLE STATE2 'C))
								(T STATE2))
						   COLOURS1 COLOURS2 OLD.COL1 OLD.COL2 ac.allowed))))
				 (COND (AC (LIST NIL))
				       (T (DA-SYMBOL.OCCURS.IN.GTERM SYMBOL GTERM2 NON.MAX.PARTS))))))
		  (COND ((NEQ 'FAIL (SETQ NEW.STATE1 (UNI=COLOUR.PARSING.TABLE STATE1 'C)))
			 (MAPCAN #'(LAMBDA (SUBTERM)
					   (INCF COUNTER)
					   (SETQ NON.MAX (COPY-TREE NON.MAX.PARTS))
					   (PUSH COUNTER (GETF NON.MAX SYMBOL))
					   (UNI=GTERM.COLOURIZE SUBTERM GTERM2 NON.MAX NEW.STATE1 STATE2 
								COLOURS1 COLOURS2 ac.allowed))
				 (DA-GTERM.TERMLIST GTERM1)))))))))


(DEFUN UNI=GTERM.TERMLIST.COLOURIZE (GTERM1 GTERM2 STATE1 STATE2 COLOURS1 COLOURS2 OLD.COL1 OLD.COL2 ac.allowed)
  
  ;;; Input:  two gterms, a term access function and two states (see UNI=COLOUR.PARSING)
  ;;; Effect: colourizes both GTERM1 and the GTERM2 according to their states such 
  ;;;         that both gterms coincide with their skeleton.
  ;;; Value:  a list of sets of colours with denotes the sets of compatible colourings
  
  (LET* ((NEW.S.STATE1 (UNI=COLOUR.PARSING.TABLE STATE1 'S)) (NEW.S.STATE2 (UNI=COLOUR.PARSING.TABLE STATE2 'S))
	 (SYMBOL (DA-GTERM.SYMBOL GTERM1))
	 (COMMUTATIVE? (COND (UNI*THEORY.UNIFICATION
			      (COND ((DA-FUNCTION.IS SYMBOL) (DA-SYMBOL.HAS.ATTRIBUTE SYMBOL 'COMMUTATIVE))
				    ((AND (DA-PREDICATE.IS SYMBOL) (NOT (DA-PREDICATE.IS.EQUALITY SYMBOL)))
				     (DA-SYMBOL.HAS.ATTRIBUTE SYMBOL 'SYMMETRIC))))))
	 (ASSOCIATIVE? (AND UNI*THEORY.UNIFICATION (DA-FUNCTION.IS SYMBOL)
			    (DA-SYMBOL.HAS.ATTRIBUTE SYMBOL 'ASSOCIATIVE)))
	 LIST.OF.ALTERNATIVES)
       (COND  ((AND (NEQ NEW.S.STATE1 'FAIL) (NEQ NEW.S.STATE2 'FAIL)
		    ac.allowed COMMUTATIVE?  ASSOCIATIVE?) 
	       (UNI=GTERM.TERMLIST.COLOURIZE.AC GTERM1 GTERM2 new.s.STATE1 STATE2 COLOURS1 COLOURS2
						(DA-GTERM.SYMBOL GTERM1)))
	      ((AND (NEQ NEW.S.STATE1 'FAIL) (NEQ NEW.S.STATE2 'FAIL)
		    (OR (DA-GTERM.TERMLIST GTERM1)
			(AND (UNI=COLOUR.STATE.IS.FINITE NEW.S.STATE1)
			     (UNI=COLOUR.STATE.IS.FINITE NEW.S.STATE2))))
	       (NCONC (COND ((EVERY #'(LAMBDA (SUBTERM1 SUBTERM2)
					      (CAR (PUSH (UNI=GTERM.COLOURIZE SUBTERM1 SUBTERM2 NIL 
									      NEW.S.STATE1 NEW.S.STATE2
									      COLOURS1 COLOURS2)
							 LIST.OF.ALTERNATIVES)))
				    (DA-GTERM.TERMLIST GTERM1) (DA-GTERM.TERMLIST GTERM2))
			     (UNI=GTERM.COLOURIZE.MERGE.ALTERNATIVES 
			      LIST.OF.ALTERNATIVES GTERM1 GTERM2 OLD.COL1 OLD.COL2)))
		      (COND ((AND COMMUTATIVE?
				  (NOT (UNI-GTERM.ARE.EQUAL (CAR (DA-GTERM.TERMLIST GTERM1))
							    (SECOND (DA-GTERM.TERMLIST GTERM1))))
				  (NOT (UNI-GTERM.ARE.EQUAL (CAR (DA-GTERM.TERMLIST GTERM2))
							    (SECOND (DA-GTERM.TERMLIST GTERM2))))
				  (PROGN (SETQ LIST.OF.ALTERNATIVES NIL)
					 (EVERY #'(LAMBDA (SUBTERM1 SUBTERM2)
							  (CAR (PUSH (UNI=GTERM.COLOURIZE 
								      SUBTERM1 SUBTERM2 
								      NIL NEW.S.STATE1 NEW.S.STATE2
								      COLOURS1 COLOURS2 ac.allowed)
								     LIST.OF.ALTERNATIVES)))
						(REVERSE (DA-GTERM.TERMLIST GTERM1)) (DA-GTERM.TERMLIST GTERM2))))
			      (UNI=GTERM.COLOURIZE.MERGE.ALTERNATIVES LIST.OF.ALTERNATIVES GTERM1 GTERM2 
								      OLD.COL1 OLD.COL2))))))))


(DEFUN UNI=GTERM.TERMLIST.COLOURIZE.AC (GTERM1 GTERM2 NEW.STATE1 NEW.STATE2 COLOURS1 COLOURS2 SYMBOL)

  ;;; Input: 

  (LET* ((RIGHT.COLOUR.SET (UNI=GTERM.COLOURIZE (SECOND (DA-GTERM.TERMLIST GTERM1))
						GTERM2 NIL NEW.STATE1 NEW.STATE2 COLOURS1 COLOURS2 t))
	 (RIGHT.SOLUTIONS (MAPCAR #'(LAMBDA (RIGHT.COLOURS)
					    (UNI=GTERM.TOP.LEVEL.AC.TERMS RIGHT.COLOURS GTERM2 SYMBOL))
				  RIGHT.COLOUR.SET))
	 (RIGHT.SINGLE.SOLS (COPY-LIST  RIGHT.COLOUR.SET))
	 POSITIONS COLOUR)
    (MAPCAN #'(LAMBDA (LEFT.COLOURS)
		(MAPCAN #'(LAMBDA (RIGHT.SOLUTION RIGHT.COLOURS)
			    (COND ((SETQ POSITIONS (UNI=GTERM.SOLUTION.ARE.AC.MERGEABLE
						    (UNI=GTERM.TOP.LEVEL.AC.TERMS LEFT.COLOURS GTERM2 SYMBOL)
						    RIGHT.SOLUTION
						    GTERM2 SYMBOL))
				   (SETQ RIGHT.SINGLE.SOLS (DELETE RIGHT.COLOURS RIGHT.SINGLE.SOLS))
				   (SETQ COLOUR (DA-COLOUR.CREATE.VARIABLE))
				   (MAPC #'(LAMBDA (TAF)
					     (PUSH COLOUR (UNI=GTERM.INT.COLOURS (DA-ACCESS TAF GTERM2))))
					 POSITIONS)
				   (PUSH COLOUR (UNI=GTERM.INT.COLOURS GTERM1))
				   (LIST (CONS COLOUR (APPEND LEFT.COLOURS RIGHT.COLOURS))))))
			RIGHT.SOLUTIONS RIGHT.COLOUR.SET))
	    (UNI=GTERM.COLOURIZE (CAR (DA-GTERM.TERMLIST GTERM1)) GTERM2 
				 NIL NEW.STATE1 NEW.STATE2 COLOURS1 COLOURS2 t))))
	


(DEFUN UNI=GTERM.TOP.LEVEL.AC.TERMS (COLOURS GTERM SYMBOL &OPTIONAL TAF)
  
  (LET (SUB.TAF)
       (COND ((AND (NEQ (DA-GTERM.SYMBOL GTERM) SYMBOL)
		   (INTERSECTION COLOURS (UNI=GTERM.INT.COLOURS GTERM)))
	      (LIST TAF))
	     (T (SETQ SUB.TAF (DA-TAF.CREATE.ZERO TAF))
		(MAPCAN #'(LAMBDA (SUBTERM) 
				  (UNI=GTERM.TOP.LEVEL.AC.TERMS
				   COLOURS SUBTERM SYMBOL
				   (SETQ SUB.TAF (DA-TAF.CREATE.NEXT SUB.TAF))))
			(DA-GTERM.TERMLIST GTERM))))))


(DEFUN UNI=GTERM.SOLUTION.ARE.AC.MERGEABLE (SOLUTION1 SOLUTION2 GTERM SYMBOL)
  
  ;;; Input:  two sets of tafs, a coloured term and a AC-function symbol
  ;;; Effect: tests, whether both solutions denote a common solution under AC, i.e. whether each taf of 
  ;;;         SOLUTION1 denotes no subterm of the denoted terms of SOLUTION2 and vice versa.
  ;;; Value:  the term access functions of the occurrences of SYMBOL where ...
  
  (LET (TAF COMMON.TAFS)
       (COND ((EVERY #'(LAMBDA (TAF1)
			       (EVERY #'(LAMBDA (TAF2)
						(SETQ TAF (DA-TAF.COMMON.TAF (LIST TAF1 TAF2)))
						(COND ((AND (NOT (EQUAL TAF TAF1)) (NOT (EQUAL TAF TAF2))
							    (EQ (DA-GTERM.SYMBOL (DA-ACCESS TAF GTERM)) SYMBOL))
						       (PUSH TAF COMMON.TAFS))))
				      SOLUTION2))
		     SOLUTION1)
	      COMMON.TAFS))))


(DEFUN UNI=GTERM.COLOURIZE.MERGE.COLS (COLOURS1 COLOURS2)
  
  (LET ((SOLUTIONS (LIST COLOURS2)))
       (COND ((EVERY #'(LAMBDA (COLOUR)
			       (COND ((DA-XVARIABLE.IS COLOUR)
				      (MAPL #'(LAMBDA (SOLUTION)
						      (PUSH COLOUR (CAR SOLUTION)))
					    SOLUTIONS))
				     (T (SETQ SOLUTIONS (MAPCAN #'(LAMBDA (SOLUTION)
								    (UNI=GTERM.COLOURIZE.VAR.MERGE COLOUR SOLUTION))
								SOLUTIONS)))))
		     COLOURS1)
	      SOLUTIONS))))


(DEFUN UNI=GTERM.COLOURIZE.VAR.MERGE (VAR.BINDING SOLUTION)
  
  ;;; Input:  a list (var numbers cterm1 ... cterm(n)) and a colouring
  ;;; Effect: incorporates the VAR.BINDING into the given colouring
  ;;; Value:  a list of new solutions, denoting the possible colourings.
  
  (LET (SOLUTIONS NEW.SOLUTION VAR.BINDING2)
    (COND ((SETQ VAR.BINDING2 (SOME #'(LAMBDA (ENTRY)
					      (COND ((AND (CONSP ENTRY) (EQ (CAR ENTRY) (CAR VAR.BINDING)))
						     ENTRY)))
				    SOLUTION))
	   (SETQ UNI*COLOUR.BINDINGS NIL)
	   (SETQ SOLUTIONS (UNI=GTERM.COLOURIZE (THIRD VAR.BINDING) (THIRD VAR.BINDING2) NIL 'S*C*S+ 'S*C*S+
					       (SECOND VAR.BINDING) (SECOND VAR.BINDING2)))
	   (MAPC #'(LAMBDA (TERM)
		     (UNI=GTERM.COLOURIZE.RENAME.COLOUR TERM UNI*COLOUR.BINDINGS))
		 (CDDDR VAR.BINDING))
	   (MAPC #'(LAMBDA (TERM)
		     (UNI=GTERM.COLOURIZE.RENAME.COLOUR TERM UNI*COLOUR.BINDINGS))
		 (CDDDR VAR.BINDING2))
	   (SETQ UNI*COLOUR.BINDINGS NIL)
	   (MAPCAR #'(LAMBDA (COLOURS)
		       (SETQ NEW.SOLUTION (COPY-TREE SOLUTION))
		       (SOME #'(LAMBDA (ENTRY)
				       (COND ((AND (CONSP ENTRY) (EQ (CAR ENTRY) (CAR VAR.BINDING)))
					      (SETF (CDR ENTRY)
						    (CONS COLOURS (APPEND (CDDR VAR.BINDING) 
									  (CDDR VAR.BINDING2)))))))
			     NEW.SOLUTION)
		       NEW.SOLUTION)
		   SOLUTIONS))
	  (T (LIST (CONS VAR.BINDING SOLUTION))))))

  
(DEFUN UNI=GTERM.COLOURIZE.RENAME.COLOUR (GTERM BINDINGS)

  (LET (ENTRY)
    (SOME #'(LAMBDA (COLOUR)
	      (SETQ ENTRY (GETF BINDINGS COLOUR))
	      (SETF (UNI=GTERM.INT.COLOURS GTERM)
		    (APPEND ENTRY (UNI=GTERM.INT.COLOURS GTERM))))
	  (UNI=GTERM.INT.COLOURS GTERM))
    (MAPC #'(LAMBDA (SUBTERM) (UNI=GTERM.COLOURIZE.RENAME.COLOUR SUBTERM BINDINGS))
	  (DA-GTERM.TERMLIST GTERM))))


(DEFUN UNI=COLOUR.PARSING.TABLE (STATE SYMBOL)

  ;;; Input:  a state, namely one of the atoms: s+, c*s+, c+s+, s*c+s+, s+c+s+ and a symbol namely c or s.
  ;;; effect: see value.
  ;;; value : implements the following parsing table:
  ;;;
  ;;;         --------------------------------------------------
  ;;;                   s+   c*s+  c+s+  s*c*s+  s+c*s+  ignore  
  ;;;         ==================================================
  ;;;         s         s+    s+   fail  s*c*s+  s*c*s+  ignore 
  ;;;         --------------------------------------------------
  ;;;         c        fail  c*s+  c*s+   c*s+    fail   ignore 
  ;;;         --------------------------------------------------

  (CASE SYMBOL
    (S (CASE STATE
	 ((S+ C*S+) 'S+)
	 (S+C+S+ 'S*C+S+)
	 (S++C*S+ 'S+C*S+)
	 ((S*C*S+ S+C*S+) 'S*C*S+)
	 (S*C+S+ 'S*C+S+)
	 (IGNORE 'IGNORE)
	 (C+S+ 'FAIL)
	 (FAIL 'FAIL)))
    (C (CASE STATE
	 ((S+ S+C*S+ S+C+S+ S++C*S+) 'FAIL)
	 ((C*S+ C+S+ S*C+S+ S*C*S+) 'C*S+)
	 (IGNORE 'IGNORE)
	 (FAIL 'FAIL)))))


(DEFUN UNI=COLOUR.STATE.IS.FINITE (STATE)
  (OR (EQ STATE 'S+) (EQ STATE 'C*S+) (EQ STATE 'S++C*S+) (EQ STATE 'S+C*S+)
      (EQ STATE 'S*C*S+) (EQ STATE 'IGNORE)))



(DEFUN UNI=GTERM.COLOURIZE.MERGE (GTERM1 GTERM2 SETS.OF.COLOURS)

  ;;; Input:    two gterms and a list of coloursets
  ;;; Effect:   computes a list of possible c-equation descriptions each as a dotted pair:
  ;;;             \begin{itemize}
  ;;;             \item the car is a list of colorsets denoting the different parts of the merged solution
  ;;;             \item the cdr is a list of colorsets denoting colourvariables to be joined.
  ;;;             \end{itemize}
  ;;; Value:   the list described above

  (let (solutions classes name (counter 0))
    (cond (sets.of.colours 
	   (setq solutions (uni=gterm.colour.classes gterm1 (list sets.of.colours)))
	   (setq solutions (uni=gterm.colour.classes gterm2 solutions))
	   (prog1 (mapcar #'(lambda (sets)
			      (setq name (list (incf counter)))
			      (setq classes (uni=gterm.merge.colour.classes 
					     sets gterm1 (uni=gterm.merge.colour.classes sets gterm2 nil)))
			      (UNI=GTERM.COLOURIZE.INSERT.COLOURS.1 sets classes gterm1 name t)
			      (UNI=GTERM.COLOURIZE.INSERT.COLOURS.1 sets classes gterm2 name t)
			      (uni=GTERM.WEAKENING.VARS gterm1 name)
			      (uni=GTERM.WEAKENING.VARS gterm2 name)
			      name)
			  solutions)
	     (uni=gterm.delete.internal.colours gterm1)
	     (uni=gterm.delete.internal.colours gterm2))))))


(defun uni=gterm.delete.internal.colours (gterm)

  ;;; Input:   a gterm
  ;;; Effect:  deletes the internal colours of gterm
  ;;; Value:   undefined.

  (setf (uni=gterm.int.colours gterm) nil)
  (mapc #'(lambda (subterm) (uni=gterm.delete.internal.colours subterm))
	(da-gterm.termlist gterm)))


(defun uni=gterm.merge.colour.classes (sets gterm classes)

  ;;; Input:   a list of sets of colours, denoting different colourings, the gterm to be coloured,
  ;;;          and a list of lists of equivalent classes of colours.
  ;;; Effect:  merges different equivalent classes if there are two colour variables in different
  ;;;          sets of colours that belong to the same occurrence of a symbol in \verb$gterm$.
  ;;; Value:   the equivalence classes

  (let (cols new.class)
    (setq cols (mapcan #'(lambda (set) (intersection set (uni=gterm.int.colours gterm)))
		       sets))
    (cond ((cdr cols)
	   (setq classes (remove-if #'(lambda (merge) (cond ((intersection merge cols)
							      (setq new.class (union merge new.class)))))
				     classes))
	   (push (union cols new.class) classes)))
    (mapc #'(lambda (subterm)
	      (setq classes (uni=gterm.merge.colour.classes sets subterm classes)))
	  (da-gterm.termlist gterm))
    classes))


(defun uni=gterm.colour.classes (gterm solutions)

  ;;; Input:   a gterm and a list of sets of coloursets
  ;;; Effect:  splits each list in \verb$solutions$ into different lists such that the 
  ;;;          colour-annotations of \verb$gterm$ is consistent with each solution. I.e. 
  ;;;          if there are two symbols in \verb$gterm$ which are coloured only in different 
  ;;;          sublists of a solution then they are not subterms of each other.
  ;;; Value:   the split solutions.

  (let (new.solutions)
    (mapc #'(lambda (solution)
	      (setq new.solutions (append (uni=gterm.colour.split gterm solution)
					  new.solutions)))
	  solutions)
    (mapc #'(lambda (subterm)
	      (setq new.solutions (uni=gterm.colour.classes subterm new.solutions)))
	  (da-gterm.termlist gterm))
    new.solutions))


(defun uni=gterm.colour.split (gterm sets.of.coloursets)

  (let ((colours (UNI=GTERM.INT.COLOURS GTERM))
	used.colours non.used.colours incomp.colours)
    (mapc #'(lambda (colour.set)
	      (cond ((intersection colour.set colours)
		     (push colour.set used.colours))
		    ((uni=gterm.is.fade gterm colour.set)
		     (push colour.set non.used.colours))
		    (t (push colour.set incomp.colours))))
	  sets.of.coloursets)
    (nconc (cond (used.colours 
		  (list (append used.colours non.used.colours))))
	   (cond (incomp.colours 
		  (list (append incomp.colours non.used.colours))))
	   (cond ((and (null used.colours) (null incomp.colours))
		  (list non.used.colours))))))


(defun uni=gterm.colourize.insert.colours.1 (sets classes gterm name skeleton)

  ;;; Input:  two gterms and a list of dotted pairs (colour . renaming) and a list of names
  ;;;         (with the same length like the first)
  ;;; Effect: stores the solutions into the colour attributes of the subterms of GTERM
  ;;; Value:  undefined.

  (let (colour tafs (counter 0) symbol)
    (setq colour (car (some #'(lambda (set)
				(intersection set (uni=gterm.int.colours gterm)))
			    sets)))
    (push (cond (colour (some #'(lambda (class) 
				  (cond ((member colour class) (setq colour (car class)))))
			      classes)
			colour)
		(t (da-colour.faded)))
	  (da-gterm.colours gterm))
    (push name (da-gterm.colours gterm))
    (mapc #'(lambda (sub.term) 
	      (uni=gterm.colourize.insert.colours.1 sets classes sub.term name colour))
	  (da-gterm.termlist gterm))
    (cond ((and skeleton (null colour) (cdr (setq tafs (da-gterm.colourful.terms gterm name))))
	   (setq symbol (gensym))
	   (mapc #'(lambda (taf) 
		     (setf (getf (getf (da-gterm.attributes (da-access taf gterm)) 'uni*weakening) name)
			   (list (cons symbol (incf counter)) (length tafs) nil)))
		 tafs)))))


(defun uni=gterm.colourize.get.names (colours solution.parts)

  (let ((counter 0) names colour cols)
    (mapc #'(lambda (part)
	      (incf counter)
	      (cond ((setq cols (intersection colours part))
		     (setq colour (car cols))
		     (push counter names))))
	  solution.parts)
    (values colour names)))


(DEFUN UNI=GTERM.COLOURIZE.INSERT.COLOURS (GTERM SET.OF.COLOURS.RENAMING NAMES FIXED.COLOUR)

  ;;; Input:  two gterms and a list of dotted pairs (colour . renaming) and a list of names
  ;;;         (with the same length like the first)
  ;;; Effect: stores the solutions into the colour attributes of the subterms of GTERM
  ;;; Value:  undefined.

  (LET (COLOUR)
    (MAPC #'(LAMBDA (COLOURS.RENAMING NAME)
	      (PUSH (COND ((SETQ COLOUR (SOME #'(LAMBDA (COLOUR)
						  (OR (GETF (CDR COLOURS.RENAMING) COLOUR)
						      (CAR (MEMBER COLOUR (CAR COLOURS.RENAMING)))))
					      (UNI=GTERM.INT.COLOURS GTERM)))
			   (COND (FIXED.COLOUR 'COLOURED)
				 (T COLOUR)))
			  (T (DA-COLOUR.FADED)))
		    (DA-GTERM.COLOURS GTERM))
	      (PUSH NAME (DA-GTERM.COLOURS GTERM)))
	  SET.OF.COLOURS.RENAMING NAMES)
    (SETF (UNI=GTERM.INT.COLOURS GTERM) NIL)
    (MAPC #'(LAMBDA (SUB.TERM) (UNI=GTERM.COLOURIZE.INSERT.COLOURS 
				SUB.TERM SET.OF.COLOURS.RENAMING NAMES FIXED.COLOUR))
	  (DA-GTERM.TERMLIST GTERM))))


(DEFUN UNI=GTERM.IS.FADE (GTERM COLOURS)
  (AND (NOT (INTERSECTION (UNI=GTERM.INT.COLOURS GTERM) COLOURS))
       (EVERY #'(LAMBDA (SUB.TERM)
		  (UNI=GTERM.IS.FADE SUB.TERM COLOURS))
	      (DA-GTERM.TERMLIST GTERM))))



(DEFMACRO UNI=GTERM.TAF.RELATION.FAILURE (TERM1 TERM2)
  `(NOT (EQUAL (GETF (DA-GTERM.ATTRIBUTES ,TERM1) 'COLOUR.UNIFICATION)
	       (GETF (DA-GTERM.ATTRIBUTES ,TERM2) 'COLOUR.UNIFICATION))))


(DEFUN UNI=TAF.RESTRICTION.APPLY (GTERM1 GTERM2 TAF.PAIRS FLAG)
  (LET ((COUNTER 0))
       (MAPC #'(LAMBDA (TAF.PAIR)
		       (INCF COUNTER)
		       (UNI=TAF.RESTRICTION.INSERT GTERM1 (REVERSE (CAR TAF.PAIR)) (COND (FLAG COUNTER)))
		       (UNI=TAF.RESTRICTION.INSERT GTERM2 (REVERSE (CDR TAF.PAIR)) (COND (FLAG COUNTER))))
	     TAF.PAIRS)))


(DEFUN UNI=TAF.RESTRICTION.INSERT (GTERM TAF FLAG)

  (COND (FLAG (PUSH FLAG (GETF (DA-GTERM.ATTRIBUTES GTERM) 'COLOUR.UNIFICATION)))
	(T (REMF (DA-GTERM.ATTRIBUTES GTERM) 'COLOUR.UNIFICATION)))
  (COND (TAF (UNI=TAF.RESTRICTION.INSERT (NTH (1- (CAR TAF)) (DA-GTERM.TERMLIST GTERM))
					 (CDR TAF) FLAG))))



(DEFUN UNI=TERM.COLOUR (TERM COLOUR.KEY)

  (COND ((NULL COLOUR.KEY) NIL)
	((AND (CONSP COLOUR.KEY)
	      (EQ (CAR COLOUR.KEY) 'COLOUR))
	 (CDR COLOUR.KEY))
	(T (DA-GTERM.COLOUR TERM COLOUR.KEY))))



(DEFUN UNI=SOLUTION.CREATE (SOLUTION FLAG)

  (COND ((NULL FLAG) SOLUTION)
	(T (LIST SOLUTION))))


(defun uni-environment (colour)

  ;;; Input: a colour, optionally a mapping of function symbols, and a history
  ;;; Value: a new environment
  ;;; Remark:  to be deleted soon !!!!

  (cond ((and (consp colour) (eq (car colour) 'key)) (cdr colour))
	(t colour)))


(DEFUN UNI=TERM.COPY (TERM &OPTIONAL REPLACE.COLOURS? SOURCE.KEY TARGET.KEY DEFAULT.COLOUR)

  (DA-TERM.CREATE (DA-TERM.SYMBOL TERM)
		  (MAPCAR #'(LAMBDA (SUBTERM)
			      (UNI=TERM.COPY SUBTERM REPLACE.COLOURS? SOURCE.KEY TARGET.KEY DEFAULT.COLOUR))
			  (DA-TERM.TERMLIST TERM))
		  (COND ((NULL TARGET.KEY) NIL)
			(REPLACE.COLOURS?
			 (LIST TARGET.KEY (COND (DEFAULT.COLOUR)
						(T (DA-COLOUR.CREATE.VARIABLE)))))
			((SETQ DEFAULT.COLOUR (DA-GTERM.COLOUR TERM SOURCE.KEY))
			 (LIST TARGET.KEY DEFAULT.COLOUR)))))


(defun uni=gterm.non.weakening.vars (gterm solution &optional vars weakening.terms)

  (let (colour)
    (cond ((getf (getf (da-gterm.attributes gterm) 'uni*weakening) solution)
	   (values vars (cons gterm weakening.terms)))
	  (t (setq colour (da-gterm.colour gterm solution))
	     (cond ((da-xvariable.is colour) (push colour vars)))
	     (mapc #'(lambda (subterm)
		       (multiple-value-setq (vars weakening.terms)
		          (uni=gterm.non.weakening.vars subterm solution vars weakening.terms)))
		   (da-gterm.termlist gterm))
	     (values vars weakening.terms)))))



(defun uni=gterm.weakening.vars (gterm solution)

  ;;; Input:   a gterm and a colour-indicator
  ;;; Effect:  inserts at top level of \verb$gterm$ a property list $(x_1 e_1 ... x_n e_n$)$ 
  ;;;          where $x_i$ is a colour variable and $e_i$ is a list of dotted pairs $(g . n)$ with
  ;;;          $g$ the indicator of the weakening case and $n$ the number of the actual term of 
  ;;;          this weakening case.
  ;;; Value:   undefined.    

  (let (vars weakening.terms weakening.var.list entry.list w.vars common.vars)
    (multiple-value-setq (vars weakening.terms) 
	(uni=gterm.non.weakening.vars gterm solution))
    (cond (weakening.terms
	   (setq weakening.var.list (mapcar #'(lambda (subgterm) (uni=gterm.var.colours subgterm solution vars))
					    weakening.terms))
	   (setq entry.list (mapcar #'(lambda (subgterm)
					(car (getf (getf (da-gterm.attributes subgterm) 'uni*weakening) solution)))
				    weakening.terms))
	   (setq common.vars (car weakening.var.list))
	   (mapc #'(lambda (weakening.vars) (setq common.vars (intersection common.vars weakening.vars :test 'equal)))
		 (cdr weakening.var.list))
	   (mapc #'(lambda (weakening.vars) 
		     (setq w.vars (union (set-difference weakening.vars common.vars :test 'equal) 
					 w.vars :test 'equal)))
		 weakening.var.list)
	   (setf (third (getf (getf (da-gterm.attributes (car (last weakening.terms))) 'uni*weakening) solution))
		 (mapcan #'(lambda (var)
			     (list var (mapcan #'(lambda (weakening.vars entry)
						   (cond ((member var weakening.vars :test 'equal) (list entry))))
					       weakening.var.list entry.list)))
			 w.vars))))))


(defun uni=gterm.var.colours (gterm solution ignore.xvars &optional vars)

  (let ((color (da-gterm.colour gterm solution)))
    (cond ((and (da-xvariable.is color) (not (member color ignore.xvars)))
	   (push (cond ((da-variable.is (da-gterm.symbol gterm)) 
			(cons (da-gterm.symbol gterm) color))
		       (t color))
		 vars)))
    (mapc #'(lambda (term) 
	    (setq vars (uni=gterm.var.colours term solution ignore.xvars vars)))
	  (da-gterm.termlist gterm))
    vars))

