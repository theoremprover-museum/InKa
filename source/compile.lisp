;;; $Header: /home/serge/inka/system-4-0/source/RCS/compile.lisp,v 1.2 1997/08/20 08:10:44 serge Exp $

(in-package :inka)

(DEFPARAMETER COM*KEYWORDS
      '("ALL" "EX" "<->" "->" "EQV" "IMPL" "OR" "AND" "NOT" ":" "," "ASSOCIATIVE" "COMMUTATIVE" "SYMMETRIC" "REFLEXIVE"
	"IRREFLEXIVE" "=" "ANY" ";" "STRUCTURE" "A-FUNCTION" "FUNCTION" "D-FUNCTION" "A-PREDICATE" "PREDICATE"
	"D-PREDICATE" "AXIOM" "USE"
	"LEMMA" "IF" "THEN" "OF" "?" "FREE" "NON-FREE" "UNSPEC" "ENUM" "GENERIC" "INSTANTIATE" "WITH" "END"
	"TO" "OTHERWISE" "SET" "ARRAY"))

(DEFVAR COM*BREAK.CHARACTERS (LIST #\( #\) #\Space  #\Newline #\: #\, #\; #\{ #\} #\[ #\] ))

(DEFVAR COM*INPUT.ARRAY NIL)
(DEFVAR COM*CURSOR.LINES NIL)
(DEFVAR COM*CURSOR-X NIL)
(DEFVAR COM*CURSOR-Y NIL)

(DEFVAR COM*SYMBOL)

(DEFVAR COM*ALL.VARIABLES NIL)
(DEFVAR COM*VARIABLE.STACK NIL)
(DEFVAR COM*SYMBOL.STACK NIL)
(DEFVAR COM*MAPPINGS NIL)

(DEFVAR COM*LEMMA.COUNTER (LIST 0))
(DEFVAR COM*AXIOM.COUNTER (LIST 0))

(DEFVAR COM*SOLVING.FORWARD.DECLARATION NIL)



(DEFUN COM-COMPILE (INPUT)
  
  ;;; Edited :  28.7.87 by DH
  ;;; Input  :  A list of strings
  ;;; Effect :  tests whether the sentence denoted by \verb$INPUT$ is a word member of the inka input language.
  ;;;           if so, updates the symboltable due to \verb$INPUT$.
  ;;; Value  :  a multiple value: 
  ;;;           NIL / x-pos / y-pos, if the denoted sentence is not member of the inka input language,
  ;;;               (x-pos, y-pos) denotes position of error,
  ;;;           else T / \verb$NAME$ / \verb$RESULTS$, where \verb$NAME$ represents a name for the given \verb$INPUT$ and
  ;;;                \verb$RESULTS$ is a list of lists, each starting with an atom like: COMMENT, TYPE, STRUCTURE, 
  ;;;                FUNCTION, PREDICATE, PROPERTY or QUANTIFICATION, and then following either an formula
  ;;;                in prefix notation or a definition description (\verb$TREE$ / \verb$LEAVES$ / \verb$NAME$ / \verb$PARAMETER.LIST$) 
  ;;;                as is used in the modules EXP and REC.
  
  (SETQ COM*VARIABLE.STACK NIL)
  (SETQ COM*ALL.VARIABLES NIL)
  (SETQ COM*CURSOR-X 0 COM*CURSOR-Y 0)
  (SETQ COM*INPUT.ARRAY INPUT)
  (SETQ COM*CURSOR.LINES INPUT)
  (CATCH 'COM*ERROR.TAG
    (COM=1=NEXT.SYMBOL)
    (MULTIPLE-VALUE-BIND (TYPE NAME FORMULA) (COM=2=STATEMENT)
      (VALUES NIL (LIST TYPE NAME FORMULA)))))




(DEFUN COM-COMPILE.INSTANTIATION (INPUT CONSTANTS VARIABLES)
  ;;; Input: a list of strings, a list of skolem-constants, and a list of variables
  ;;; effect: parses the input for being a substitution, meaning no single instantiation
  ;;;         is done more than once
  ;;; VAlue: a multiple-value: a flag which is NIL iff \verb$INPUT$ is syntactically correct
  ;;;          and the parsed substitution

  (SETQ COM*VARIABLE.STACK NIL)
  (SETQ COM*ALL.VARIABLES NIL)
  (SETQ COM*CURSOR-X 0 COM*CURSOR-Y 0)
  (SETQ COM*INPUT.ARRAY INPUT)
  (SETQ COM*CURSOR.LINES INPUT)
  (mapcar #'(lambda (var)
	      (setq com*all.variables (acons (da-variable.pname var) var com*all.variables)))
	  variables)
  (CATCH 'COM*ERROR.TAG
    (COM=1=NEXT.SYMBOL)
    (LET (RESULT)
      (UNWIND-PROTECT (PROGN (MAPC #'(LAMBDA (CONST) (DB-FUNCTION.INSERT CONST)) CONSTANTS)
			     (SETQ RESULT (com=2=lemma.instantiation)))
	(MAPC #'(LAMBDA (CONST) (DB-FUNCTION.DELETE CONST)) CONSTANTS))
      (VALUES NIL RESULT))))


(DEFUN COM-COMPILE.CASE.ANALYSIS (INPUT CONSTANTS)

  ;;; Input:   a list of strings and a list of skolem-constants
  ;;; Effect:  parses a literal with no variables and at least some
  ;;;          skolem-constants inside \verb$CONSTANTS$.
  ;;; Value:   a multiple-value:  a flag which is NIL iff \verb$INPUT$ is syntactically correct
  ;;;          and the parsed literal 

  (SETQ COM*VARIABLE.STACK NIL)
  (SETQ COM*ALL.VARIABLES NIL)
  (SETQ COM*CURSOR-X 0 COM*CURSOR-Y 0)
  (SETQ COM*INPUT.ARRAY INPUT)
  (SETQ COM*CURSOR.LINES INPUT)
  (CATCH 'COM*ERROR.TAG
    (COM=1=NEXT.SYMBOL)
    (LET (RESULT)
      (UNWIND-PROTECT (PROGN (MAPC #'(LAMBDA (CONST) (DB-FUNCTION.INSERT CONST)) CONSTANTS)
			     (SETQ RESULT (DA-LITERAL.NEGATE (COM=2=LITERAL))))
	(MAPC #'(LAMBDA (CONST) (DB-FUNCTION.DELETE CONST)) CONSTANTS))
      (VALUES NIL RESULT))))


(DEFUN COM-COMPILE.INDUCTION (INPUT CONSTANTS)
  
  ;;; Input  :  a list of strings
  ;;; Effect :  tests whether the sentence denoted by \verb$INPUT$ is an induction scheme
  ;;; Value  :  a multiple value:
  ;;;           the parameters of the scheme and a definition tree, denoting the wfo.
  
  (SETQ COM*VARIABLE.STACK NIL)
  (SETQ COM*ALL.VARIABLES NIL)
  (SETQ COM*CURSOR-X 0 COM*CURSOR-Y 0)
  (SETQ COM*INPUT.ARRAY INPUT)
  (SETQ COM*CURSOR.LINES INPUT)
  (CATCH 'COM*ERROR.TAG
    (LET (PARAMETERS ORDER INSTANCE SYMBOL)
      (COM=1=NEXT.SYMBOL)
      (UNWIND-PROTECT (PROGN (COM=3=VSTACK.PUSH)
			     (MAPC #'(LAMBDA (CONST) (DB-FUNCTION.INSERT CONST)) CONSTANTS)
			     (MULTIPLE-VALUE-SETQ (PARAMETERS ORDER INSTANCE SYMBOL) (COM=2=INDUCTION.SCHEME)))
	(MAPC #'(LAMBDA (CONST) (DB-FUNCTION.DELETE CONST)) CONSTANTS)
	(COM=3=VSTACK.POP))
      (VALUES NIL PARAMETERS ORDER INSTANCE SYMBOL))))


(defun com-compile.theorem (input)
  (SETQ COM*VARIABLE.STACK NIL)
  (SETQ COM*ALL.VARIABLES NIL)
  (SETQ COM*CURSOR-X 0 COM*CURSOR-Y 0)
  (SETQ COM*INPUT.ARRAY INPUT)
  (SETQ COM*CURSOR.LINES INPUT)
  (CATCH 'COM*ERROR.TAG
    (COM=1=NEXT.SYMBOL)
    (multiple-value-bind (type name formula) (COM=2=LEMMA)
      (declare (ignore type))
      (declare (ignore name))
      (values nil formula))))


(DEFUN COM-ACTUAL.MAPPING ()
  ;;; Input: none
  ;;; Value: the actual mapping
  
  COM*MAPPINGS)

(DEFUN COM-MAPPING.PUSH (MAPPING)
  ;;; Input:  a mapping
  ;;; Effect: activates mapping

  (PUSH MAPPING COM*MAPPINGS))


(DEFUN COM-MAPPING.POP ()
  ;;; Input:  none
  ;;; Effect: deactivates last mapping

  (POP COM*MAPPINGS))


(DEFMACRO COM=KEYWORD (SYMBOL)

  ;;; EDITED: 17-MAY-81 16:35:36
  ;;; INPUT:  COM*SYMBOL- A COM*SYMBOL OF A SENTENCE
  ;;; EFFECT: NONE.
  ;;; VALUE:  SEXPRESSION () NIL, IF SYMBOL IS A KEYWORD OF PLL - LANGUAGE
  ;;;         or break.character, ELSE NIL.

  `(OR (MEMBER ,SYMBOL COM*KEYWORDS :test #'string-equal)
       (AND (EQ (LENGTH ,SYMBOL) 1)
	    (COM-CHAR.IS.BREAK.CHARACTER (CHARACTER ,SYMBOL)))))


(DEFUN COM-CHAR.IS.BREAK.CHARACTER (CHAR)

  ;;; Input: A character
  ;;; Value: NIL iff character does not denote a delimiter of the input language
  
  (MEMBER CHAR COM*BREAK.CHARACTERS))


; ========================================================
;
; Part One: Lexical Analysis
;
; ========================================================


(DEFMACRO COM=1=INPUT.CHARACTER (X Y)
  `(AREF (NTH ,Y COM*INPUT.ARRAY) ,X))


(DEFMACRO COM=1=END.OF.TEXT.REACHED ()
  `(NULL COM*CURSOR.LINES))


(DEFMACRO COM=1=END.OF.LINE.REACHED (X-POS)
  `(>= ,X-POS (ARRAY-DIMENSION (CAR COM*CURSOR.LINES) 0)))


(DEFMACRO COM=1=ACTUAL.CHARACTER (X)
  `(AREF (CAR COM*CURSOR.LINES) ,X))


(DEFMACRO COM=1=NEXT.LINE ()
  `(PROGN
     (INCF COM*CURSOR-Y)
     (POP COM*CURSOR.LINES)
     (SETQ COM*CURSOR-X 0)))


(DEFUN COM=1=NEXT.SYMBOL ()

  ;;; EDITED: 11-MAR-81 09:48:34
  ;;; INPUT:  NONE
  ;;; EFFECT: REPLACES COM*SYMBOL BY THE NEXT SYMBOL FROM THE INPUT
  ;;; VALUE:  UNDEFINED

  (LET (X-POS ACT.CHAR SYMBOL.TYPE)
    ;; skip blanks
    (WHILE (AND (NOT (COM=1=END.OF.TEXT.REACHED))
                (OR (COM=1=END.OF.LINE.REACHED COM*CURSOR-X)
                    (EQL (COM=1=ACTUAL.CHARACTER COM*CURSOR-X) #\SPACE)
		    (EQL (COM=1=ACTUAL.CHARACTER COM*CURSOR-X) #\NEWLINE)
		    (EQL (COM=1=ACTUAL.CHARACTER COM*CURSOR-X) #\TAB)))
      (COND ((NOT (COM=1=END.OF.LINE.REACHED COM*CURSOR-X))
             (INCF COM*CURSOR-X))
            ((NOT (COM=1=END.OF.TEXT.REACHED))
	     (COM=1=NEXT.LINE))))
    (COND ((COM=1=END.OF.TEXT.REACHED) (SETQ COM*SYMBOL NIL))
	  ((EQ (COM=1=ACTUAL.CHARACTER COM*CURSOR-X) #\%)
	   (COM=1=NEXT.LINE))
          ((EQ  (COM=1=ACTUAL.CHARACTER COM*CURSOR-X) #\")
           (SETQ X-POS (1+ COM*CURSOR-X))
           (WHILE (NOT (OR (COM=1=END.OF.LINE.REACHED X-POS)
                           (EQ (COM=1=ACTUAL.CHARACTER X-POS) #\")))
               (INCF X-POS))
           (SETQ COM*SYMBOL (CONS "STRING" (SUBSEQ (CAR COM*CURSOR.LINES) COM*CURSOR-X (INCF X-POS))))
           (SETQ COM*CURSOR-X X-POS))
          ;; read symbol
	  (T (SETQ X-POS COM*CURSOR-X)
             (WHILE (NOT (OR (COM=1=END.OF.LINE.REACHED X-POS)
                             (MEMBER (COM=1=ACTUAL.CHARACTER X-POS) COM*BREAK.CHARACTERS)))
               (INCF X-POS))
             (COND ((EQ X-POS COM*CURSOR-X)
                    (SETQ COM*SYMBOL (SUBSEQ (CAR COM*CURSOR.LINES) COM*CURSOR-X (INCF X-POS))))
                   (T (SETQ COM*SYMBOL (SUBSEQ (CAR COM*CURSOR.LINES) COM*CURSOR-X X-POS))))
             (SETQ COM*CURSOR-X X-POS)
             ;; set symbol.type
             (SETQ ACT.CHAR (AREF COM*SYMBOL 0))
             (COND ((COM=KEYWORD COM*SYMBOL))
                   ((DIGIT-CHAR-P ACT.CHAR)
                    (SETQ SYMBOL.TYPE "NUMBER")
                    (DO* ((ACT 1 (1+ ACT))) ((EQ ACT (LENGTH COM*SYMBOL)))
                      (SETQ ACT.CHAR (AREF COM*SYMBOL ACT))
                      (COND ((AND (STRING= SYMBOL.TYPE "NUMBER")
                                  (NOT (DIGIT-CHAR-P ACT.CHAR)))
                             (SETQ COM*CURSOR-X (+ COM*CURSOR-X ACT))
                             (COM=ERROR 1 ACT.CHAR)))))
                   ((ALPHA-CHAR-P ACT.CHAR)
                    (SETQ SYMBOL.TYPE "IDENTIFIER"))
                   (T (SETQ SYMBOL.TYPE "NAME")))
             (COND ((NOT (COM=KEYWORD COM*SYMBOL))
                    (SETQ COM*SYMBOL (CONS SYMBOL.TYPE (COM=1=CORRESPONDENT.SYMBOL COM*SYMBOL)))))))
    COM*SYMBOL))


(DEFUN COM=1=CORRESPONDENT.SYMBOL (SYMBOL)

  (MAPC #'(LAMBDA (MAPPING)
	    (SETQ SYMBOL (COND ((cdr (Assoc SYMBOL mapping :test 'string-equal)))
			       (T SYMBOL))))
	com*mappingS)
  SYMBOL)


(DEFUN COM=1=PREV.POSITION (X-POS Y-POS)
  (LET (BACK ABORT)
    (COND ((NOT (ZEROP X-POS))
	   (DECF X-POS))
	  ((> Y-POS 0)
	    (SETQ Y-POS (DECF Y-POS))
	    (SETQ X-POS (1- (ARRAY-DIMENSION (NTH Y-POS COM*INPUT.ARRAY) 0)))))
    (WHILE (AND (NULL ABORT) (EQL (COM=1=INPUT.CHARACTER X-POS Y-POS) #\SPACE))
      (COND ((AND (ZEROP X-POS) (> Y-POS 0))
	      (SETQ Y-POS (DECF Y-POS))
	      (SETQ X-POS (1- (ARRAY-DIMENSION (NTH Y-POS COM*INPUT.ARRAY) 0))))
	    ((ZEROP X-POS) (SETQ ABORT T))
	    (T (DECF X-POS))))
    (WHILE (AND (NOT (ZEROP X-POS))
		(NOT (MEMBER (COM=1=INPUT.CHARACTER X-POS Y-POS) COM*BREAK.CHARACTERS)))
      (SETQ BACK T)
      (DECF X-POS))
    (COND ((AND (NOT (ZEROP X-POS)) BACK) (INCF X-POS)))
    (VALUES X-POS Y-POS)))


(DEFMACRO COM=1=SYMBOL.ACCEPTED (X)
  
  ;;; edited: 24-feb-81 12:50:00
  ;;; input:  a list of atoms member of com*keywords + (identifier name number)
  ;;; effect: replaces com*symbol by the next symbol, if current com*symbol was member of x
  ;;; value:  t, if the actual com*symbol is member of x,
  ;;;         else nil.
  
  `(COND ((MEMBER (COND ((CONSP COM*SYMBOL) (CAR COM*SYMBOL))
			(T COM*SYMBOL))
		  ,X :test #'string-equal)
	  (COM=1=NEXT.SYMBOL)
	  T)))

(DEFMACRO COM=1=SYMBOL.IS (X)
  
  ;;; edited: 24-feb-81 16:08:11
  ;;; input:  a list of valid symbols, i.e. symbols member of com*keywords + (identifier name number)
  ;;; effect: returns value
  ;;; value:  t,if the actual symbol is in x
  
  `(MEMBER (COND ((CONSP COM*SYMBOL) (CAR COM*SYMBOL))
		 (T COM*SYMBOL))
	   ,X :TEST 'STRING-EQUAL))


(DEFUN COM=ITERATION.WITH.SEPARATOR (APPLY.FUNCTION SEPARATE.WORDS &REST ARGS)
  
  ;;; Edited  : 29.7.87 
  ;;; Input   : APPLY.FUNCTION - A lisp function to accept a special word
  ;;;           SEPERATE.WORDS - A list of words, which are used to separate the single objects of the list.
  ;;;           ARGS           - The parameters of the acceptions.
  ;;; Value   : A list of the values returned by the single acceptions
  
  (LET ((CONTINUE T) RESULT SINGLE.RESULT)
    (WHILE (AND CONTINUE
		(SETQ SINGLE.RESULT (APPLY APPLY.FUNCTION ARGS)))
      (SETQ RESULT (NCONC1 RESULT SINGLE.RESULT))
      (SETQ CONTINUE (COM=1=SYMBOL.ACCEPTED SEPARATE.WORDS)))
    RESULT))



(DEFUN COM=ITERATION.WITHOUT.SEPARATOR (APPLY.FUNCTION RECOGNIZER &REST ARGS)
  
  (LET (RESULT SINGLE.RESULT)
    (WHILE (AND (COM=1=SYMBOL.IS RECOGNIZER)
		(SETQ SINGLE.RESULT (APPLY APPLY.FUNCTION ARGS)))
      (SETQ RESULT (NCONC1 RESULT SINGLE.RESULT)))
    RESULT))




 
; ========================================================
;
; Part Two: Syntactical Analysis
;
; ========================================================


(DEFUN COM=2=STATEMENT ()
  
  ;;; Edited:  22-FEB-82 13:18:00
  ;;; Effect:  <STATEMENT> ->  <LEMMA> | <AXIOM> | <COMMENT> | <STRUCTURE DECLARATION> |
  ;;;                          <ALGORITHMIC FUNCTION DEFINITION> | <ALGORITHMIC PREDICATE DEFINITION> |
  ;;;                          <DECLARATIVE FUNCTION DEFINITION> | <DECLARATIVE PREDICATE DEFINITION> |
  ;;;                          <PROPERTY DECLARATION>
  ;;; Value:   a multiple value NAME / RESULTS generated by the resp. rules
  
  (MULTIPLE-VALUE-BIND (TYPE NAME FORMULA) (COM=2=STATEMENT.1)
		       (COND ((AND COM*SYMBOL (NOT (EQ TYPE 'COMMENT)))
			      (COM=ERROR 0 "End of text expected.")))
		       (VALUES TYPE NAME FORMULA)))


(DEFUN COM=2=STATEMENT.1 ()

  (COND ((COM=1=SYMBOL.IS '("ASSOCIATIVE" "SYMMETRIC" "REFLEXIVE" "IRREFLEXIVE" "COMMUTATIVE"))
	   (COM=2=PROPERTY.DECLARATION))
	  ((COM=1=SYMBOL.IS
	    '("STRUCTURE" "FREE" "NON-FREE" "UNSPEC" "ENUM" "GENERIC" "INSTANTIATE" "SET" "ARRAY"))
	   (COM=2=STRUCTURE.DECLARATION))
	  ((COM=1=SYMBOL.IS '("A-FUNCTION" "FUNCTION"))
	   (COM=2=ALGORITHMIC.FUNCTION.DEFINITION))
	  ((COM=1=SYMBOL.IS '("D-FUNCTION"))
	   (COM=2=DECLARATIVE.FUNCTION.DEFINITION))
	  ((COM=1=SYMBOL.IS '("A-PREDICATE" "PREDICATE"))
	   (COM=2=ALGORITHMIC.PREDICATE.DEFINITION))
	  ((COM=1=SYMBOL.IS '("D-PREDICATE"))
	   (COM=2=DECLARATIVE.PREDICATE.DEFINITION))
	  ((COM=1=SYMBOL.IS '("WITH"))
	   (COM=2=MAPPING))
	  ((COM=1=SYMBOL.IS '(";"))
	   (VALUES 'COMMENT NIL NIL))
	  ((COM=1=SYMBOL.IS '("AXIOM"))
	   (COM=2=AXIOM))
	  ((COM=1=SYMBOL.IS '("LEMMA" "ALL" "EX" "NOT" "(" "IDENTIFIER" "NAME" "NUMBER"))
	   (COM=2=LEMMA))))


(DEFUN COM=2=PROPERTY.DECLARATION ()

  ;;; Edited: 11-MAR-82 15:09:02
  ;;; Effect: <PROPERTY DECLARATION> -> ASSOCIATIVE ( <IDENTIFIER> ) or COMMUTATIVE ( <IDENTIFIER> ) 
  ;;;                                   IRREFLEXIVE ( <IDENTIFIER> ) | REFLEXIVE ( <IDENTIFIER> ) |
  ;;;                                   SYMMETRIC ( <IDENTIFIER> )
  ;;; Value:  a multiple value NAME / RESULTS, where RESULTS is a list containing a single list,
  ;;;         first element of which is the atom 'PROPERTY and rest of which is a formula in prefix notation.

  (LET (VAR1 VAR2 VAR3 IDENTIFIER SYMBOL DOMAIN FORMULA (PROPERTY COM*SYMBOL))
    (COND ((AND (COM=1=SYMBOL.ACCEPTED '("ASSOCIATIVE" "SYMMETRIC" "REFLEXIVE" "IRREFLEXIVE" "COMMUTATIVE"))
		(COM=1=SYMBOL.ACCEPTED '("("))
		(SETQ IDENTIFIER (COM=2=IDENTIFIER.OR.NAME))
		(COM=1=SYMBOL.ACCEPTED '(")")))
	   (COND ((MEMBER (AREF PROPERTY 0) '(#\A #\C #\a #\c))
		  (SETQ SYMBOL (COM=3=CHECK.SYMBOL IDENTIFIER 'FUNCTION))
		  (SETQ DOMAIN (DA-FUNCTION.DOMAIN.SORTS SYMBOL))
		  (COND ((OR (NEQ (LENGTH DOMAIN) 2)
			     (NEQ (CAR DOMAIN) (SECOND DOMAIN)))
			 (COM=ERROR 26 IDENTIFIER DOMAIN (DA-FUNCTION.SORT SYMBOL)
				    (LIST (CAR DOMAIN) (CAR DOMAIN)))))
		  (SETQ VAR1 (DA-VARIABLE.CREATE (CAR DOMAIN)))
		  (SETQ VAR2 (DA-VARIABLE.CREATE (CAR DOMAIN)))
		  (COND ((MEMBER (AREF PROPERTY 0) '(#\A #\a))
			 (COND ((NEQ (CAR DOMAIN) (DA-FUNCTION.SORT SYMBOL))
				(COM=ERROR 27 IDENTIFIER (DA-FUNCTION.DOMAIN.SORTS SYMBOL)
					   (DA-FUNCTION.SORT SYMBOL) (CAR DOMAIN))))
			 (SETQ VAR3 (DA-VARIABLE.CREATE (CAR DOMAIN)))
			 (SETQ FORMULA (DA-LITERAL.CREATE '+ (DA-PREDICATE.EQUALITY)
							   (LIST (DA-TERM.CREATE SYMBOL 
										 (LIST (DA-TERM.CREATE SYMBOL
												       (LIST (DA-TERM.CREATE VAR1) 
													     (DA-TERM.CREATE VAR2)))
										       (DA-TERM.CREATE VAR3)))
								 (DA-TERM.CREATE SYMBOL 
										 (LIST (DA-TERM.CREATE VAR1)
										       (DA-TERM.CREATE SYMBOL
												       (LIST (DA-TERM.CREATE VAR2) 
													     (DA-TERM.CREATE VAR3)))))))))
			(T (SETQ FORMULA (DA-LITERAL.CREATE '+ (DA-PREDICATE.EQUALITY)
							     (LIST (DA-TERM.CREATE SYMBOL (LIST (DA-TERM.CREATE VAR1)
												(DA-TERM.CREATE VAR2)))
								   (DA-TERM.CREATE SYMBOL (LIST (DA-TERM.CREATE VAR2) 
												(DA-TERM.CREATE VAR1)))))))))
		 (T (SETQ SYMBOL (COM=3=CHECK.SYMBOL IDENTIFIER 'PREDICATE))
		    (SETQ DOMAIN (DA-PREDICATE.DOMAIN.SORTS SYMBOL))
		    (COND ((OR (NEQ (LENGTH DOMAIN) 2)
			       (NEQ (CAR DOMAIN) (SECOND DOMAIN)))
			   (COM=ERROR 36 IDENTIFIER DOMAIN (LIST (CAR DOMAIN) (CAR DOMAIN)))))
		    (SETQ VAR1 (DA-VARIABLE.CREATE (CAR DOMAIN)))
		    (COND ((MEMBER (AREF PROPERTY 0) '(#\R #\r))
			   (SETQ FORMULA (DA-LITERAL.CREATE '+ SYMBOL (LIST (DA-TERM.CREATE VAR1) (DA-TERM.CREATE VAR1)))))
			  ((MEMBER (AREF PROPERTY 0) '(#\I #\i))
			   (SETQ FORMULA (DA-LITERAL.CREATE '- SYMBOL (LIST (DA-TERM.CREATE VAR1) (DA-TERM.CREATE VAR1)))))
			  ((MEMBER (AREF PROPERTY 0) '(#\S #\s))
			   (SETQ VAR2 (DA-VARIABLE.CREATE (CAR DOMAIN)))
			   (SETQ FORMULA (DA-FORMULA.JUNCTION.CLOSURE
					  'EQV (LIST (DA-LITERAL.CREATE '+ SYMBOL (LIST (DA-TERM.CREATE VAR1) (DA-TERM.CREATE VAR2)))
						     (DA-LITERAL.CREATE '+ SYMBOL (LIST (DA-TERM.CREATE VAR2)
											(DA-TERM.CREATE VAR1))))))))))
	   (VALUES 'PROPERTY 
		   (FORMAT NIL "~A ~A"
			   (CASE (AREF PROPERTY 0)
			     ((#\a #\A) "Assoc. of") ((#\c #\C) "Commut. of")
			     ((#\s #\S) "Symmetry of") ((#\r #\R) "Reflexivity of")
			     ((#\i #\I) "Irrefl. of"))
			   (DA-PNAME SYMBOL))
		   (DA-FORMULA.QUANTIFICATION.CLOSURE
		     'ALL (DA-GTERM.VARIABLES FORMULA) FORMULA)))
	  (T (COM=ERROR 0 "Correct syntax is: Property (Symbol)")))))



;;;================================================
;;; AXIOMS AND LEMMATA
;;;================================================


(DEFUN COM=2=AXIOM ()
  (LET (NAME)
    (INCF (CAR COM*AXIOM.COUNTER))
    (COM=1=SYMBOL.ACCEPTED '("AXIOM"))
    (COND ((COM=1=SYMBOL.IS '("STRING"))
	   (SETQ NAME (COM=2=STRING))
           (IF (NOT (COM=1=SYMBOL.ACCEPTED '(":"))) (COM=ERROR 0 "colon expected"))))
    (COND (NAME
	   (VALUES 'AXIOM NAME (COM=2=QUANTIFICATION '(AXIOM T))))
	  (T (VALUES 'AXIOM (FORMAT NIL "AXIOM ~D" (CAR COM*AXIOM.COUNTER)) (COM=2=QUANTIFICATION '(AXIOM T)))))))



(DEFUN COM=2=LEMMA ()

  ;;; Value:  multiple-value: 'LEMMA , the name of the formula, and the formula itself.

  (LET (NAME)
       (INCF (CAR COM*LEMMA.COUNTER))
       (COND ((COM=1=SYMBOL.ACCEPTED '("LEMMA"))
	      (SETQ NAME (COM=2=STRING))
	      (IF (NOT (COM=1=SYMBOL.ACCEPTED '(":"))) (COM=ERROR 0 "colon expected"))))
       (COND (NAME
	      (VALUES 'LEMMA NAME (COM=2=QUANTIFICATION '(LEMMA T))))
	     (T (VALUES 'LEMMA (FORMAT NIL "Lemma ~D" (CAR COM*LEMMA.COUNTER)) (COM=2=QUANTIFICATION '(LEMMA T)))))))



(DEFUN COM=2=QUANTIFICATION (&OPTIONAL ATTRIBUTES)
  
  ;;; EDITED:  3-SEP-81 14:18:31
  ;;; INPUT:   ATTRIBUTES - a list of atoms.
  ;;; EFFECT:  <QUANTIFICATION> -> <EQUIVALENCE> |  ALL <QUANTOR.LIST> <QUANTIFICATION> |
  ;;;                              EX <QUANTOR.LIST> <QUANTIFICATION>
  ;;; Value:   the code generated by this rule, i.e. a formula in prefix notation
  
  (LET (VAR.LIST FORMULA)
    (COND ((COM=1=SYMBOL.IS '("ALL" "EX"))
	   (COM=3=VSTACK.PUSH)
	   (SETQ VAR.LIST (COM=2=QUANTOR.LIST ATTRIBUTES))
	   (SETQ FORMULA (COM=2=EQUIVALENCE ATTRIBUTES))
	   (COM=3=VSTACK.POP)
	   (MAPC #'(LAMBDA (QUANTOR.VARLIST)
		     (SETQ FORMULA (DA-FORMULA.QUANTIFICATION.CLOSURE
				    (CAR QUANTOR.VARLIST) (CDR QUANTOR.VARLIST) FORMULA)))
		 (NREVERSE VAR.LIST))
	   FORMULA)
	  (T (COM=2=EQUIVALENCE ATTRIBUTES)))))


(DEFUN COM=2=QUANTOR.LIST (ATTRIBUTES)
  
  ;;; Edited:   2.8.87
  ;;; Effect:   <QUANTOR LIST> -> {<QUANTOR>}*
  ;;; Value:    A list of values of COM=2=QUANTOR
  
  (COM=ITERATION.WITHOUT.SEPARATOR #'COM=2=QUANTOR '("ALL" "EX") ATTRIBUTES))


(DEFUN COM=2=QUANTOR (ATTRIBUTES)
  
  ;;; Edited:   2.8.87
  ;;; Effect:   <QUANTOR> -> ALL <VARIABLE DECLARATION> or EX <VARIABLE DECLARATION>
  ;;; Value:    a dotted pair of quantor and variable list.
  ;;;       soll aus der ganzen Aufrufkette ATTRIBUTES raus, oder soll es in COM=2=VARIABLE.DECLARATION wieder rein ????
  
  (LET ((ALLEX COM*SYMBOL))
    (COM=1=SYMBOL.ACCEPTED '("ALL" "EX"))
    (CONS (COND ((STRING-EQUAL ALLEX "ALL") 'ALL) (T 'EX))
	  (COM=2=VARIABLE.DECLARATION ATTRIBUTES))))


(DEFUN COM=2=EQUIVALENCE (&OPTIONAL ATTRIBUTES)
  
  ;;; Edited:  26-FEB-81 16:12:20
  ;;; Input:   ATTRIBUTES - a list of atoms.
  ;;; Effect:  <EQUIVALENCE> -> <IMPLICATION> {EQV <IMPLICATION>}*
  ;;; Value:   the code generated by this rule, i.e. a formula in prefix notation
  
  (DA-FORMULA.JUNCTION.CLOSURE 'EQV (COM=ITERATION.WITH.SEPARATOR #'COM=2=IMPLICATION '("EQV" "<->") ATTRIBUTES)))



(DEFUN COM=2=IMPLICATION (&OPTIONAL ATTRIBUTES)
  
  ;;; Edited:  26-FEB-81 14:44:25
  ;;; Input:   ATTRIBUTES - A LIST OF ATOMS.
  ;;; Effect:  <IMPLICATION> -> <DISJUNCTION> {IMPL <DISJUNCTION>}*
  ;;; Value:   the code generated by this rule, i.e. a formula in prefix notation
  
  (DA-FORMULA.JUNCTION.CLOSURE
   'IMPL (COM=ITERATION.WITH.SEPARATOR #'COM=2=DISJUNCTION '("IMPL" "->") ATTRIBUTES)))



(DEFUN COM=2=DISJUNCTION (&OPTIONAL ATTRIBUTES)
  
  ;;; Edited:  26-FEB-81 14:44:25
  ;;; Input:   ATTRIBUTES - A LIST OF ATOMS.
  ;;; Effect:  <DISJUNCTION> -> <CONJUNCTION> {OR <CONJUNCTION>}*
  ;;; Value:   the code generated by this rule, i.e. a formula in prefix notation
  
  (DA-FORMULA.JUNCTION.CLOSURE 'OR (COM=ITERATION.WITH.SEPARATOR #'COM=2=CONJUNCTION '("OR") ATTRIBUTES)))


(DEFUN COM=2=CONJUNCTION (&OPTIONAL ATTRIBUTES)
  
  ;;; Edited:  26-FEB-81 14:44:25
  ;;; Input:   ATTRIBUTES - A LIST OF ATOMS.
  ;;; Effect:  <CONJUNCTION> -> <NEGATION> {AND <NEGATION>}*
  ;;; Value:   the code generated by this rule, i.e. a formula in prefix notation
  
  (DA-FORMULA.JUNCTION.CLOSURE 'AND (COM=ITERATION.WITH.SEPARATOR #'COM=2=NEGATION '("AND") ATTRIBUTES)))


(DEFUN COM=2=NEGATION (&OPTIONAL ATTRIBUTES)
  
  ;;; Edited:  26-FEB-81 16:38:07
  ;;; Input:   ATTRIBUTES - a list of atoms.
  ;;; Effect:  <NEGATION> -> <ATOMAR FORMULA> or NOT <ATOMAR FORMULA> 
  ;;; Value:   the code generated by this rule, i.e. a formula in prefix notation
  
  (COND ((COM=1=SYMBOL.ACCEPTED '("NOT"))
	 (DA-FORMULA.NEGATE (COM=2=ATOMAR.FORMULA ATTRIBUTES)))
	(T (COM=2=ATOMAR.FORMULA ATTRIBUTES))))


(DEFUN COM=2=ATOMAR.FORMULA (&OPTIONAL ATTRIBUTES)
  
  ;;; Edited:  5-MAR-81 12:07:56
  ;;; Input:   ATTRIBUTES - a list of atoms.
  ;;; Effect:  <ATOMAR FORMULA> -> <ATOM> or ( <QUANTIFICATION> ) 
  ;;; Value:   the code generated by this rule, i.e. a formula in prefix notation
  
  (COND ((COM=1=SYMBOL.ACCEPTED '("("))
	 (PROG1 (COM=2=QUANTIFICATION ATTRIBUTES)
	   (COND ((NOT (COM=1=SYMBOL.ACCEPTED '(")")))
		  (COM=ERROR 0 "Missing right bracket")))))
	(T (COM=2=ATOM ATTRIBUTES))))



;;;=========================================================
;;; STRUCTURES
;;;=========================================================


(DEFUN COM=2=STRUCTURE.DECLARATION ()
  
  ;;; Edited:  14-JUL-81 17:59:12
  ;;; Effect:  <STRUCTURE DECLARATION> -> [FREE] STRUCTURE <FREE STRUCTURE DEFINITION> or
  ;;;                                     NON-FREE STRUCTURE <NON-FREE STRUCTURE DEFINITION> or
  ;;;                                     UNSPEC STRUCTURE <UNSPEC STRUCTURE DEFINITION> or
  ;;;                                     ENUM STRUCTURE <ENUM STRUCTURE DEFINITION> or
  ;;;                                     SET <SET DEFINITION> or
  ;;;                                     ARRAY <ARRAY DEFINITION> or
  ;;;                                     GENERIC <GENERIC DEFINITION> or INSTANTIATE <INSTANCE DEFINITION>
  ;;; Value:   the code generated by <... DEFINITION>, i.e. a multiple value TYPE / NAME / RESULTS,
  ;;;          where RESULTS is a list of lists, each of which represents a formula.
   
    (COND ((COM=1=SYMBOL.IS '("STRUCTURE"))
	   (COM=2=FREE.STRUCTURE.DEFINITION))
	  ((COM=1=SYMBOL.ACCEPTED '("FREE"))
	   (COM=2=FREE.STRUCTURE.DEFINITION))
	  ((COM=1=SYMBOL.ACCEPTED '("NON-FREE"))
	   (COM=2=NON-FREE.STRUCTURE.DEFINITION))
	  ((COM=1=SYMBOL.ACCEPTED '("UNSPEC"))
           (COM=2=UNSPEC.STRUCTURE.DEFINITION))
	  ((COM=1=SYMBOL.ACCEPTED '("ENUM"))
	   (COM=2=ENUM.STRUCTURE.DEFINITION))
	  ((COM=1=SYMBOL.IS '("SET"))
	   (COM=2=SET.DEFINITION))
          ((COM=1=SYMBOL.IS '("ARRAY"))
	   (COM=2=ARRAY.DEFINITION))
          ((COM=1=SYMBOL.ACCEPTED '("GENERIC"))
           (COM=2=GENERIC.DEFINITION))
	  ((COM=1=SYMBOL.ACCEPTED '("INSTANTIATE"))
	   (COM=2=INSTANCE.DEFINITION))))


(DEFUN COM=2=UNSPEC.STRUCTURE.DEFINITION ()

  ;;; Edited : 01-OCT-92
  ;;; Effect : <UNSPEC.STRUCTURE.DEFINITION> -> UNSPEC STRUCTURE <IDENTIFIER>
  ;;;          a new DT-SORT is introduced.
  ;;; Value  : the code generated by this rule, i.e. a multiple value TYPE / NAME / RESULTS

  (LET (SORT.SYMBOL) 
    (COM=1=SYMBOL.ACCEPTED '("STRUCTURE"))
    (COND ((NOT (COM=1=SYMBOL.IS '("IDENTIFIER" "NAME")))
	   (COM=ERROR 0 "Datatype-Identifier expected"))
	  (T (SETQ SORT.SYMBOL (COM=2=SORT.SYMBOL))))
    (SETQ SORT.SYMBOL (COM=3=INTRODUCE.SORT SORT.SYMBOL NIL (LIST 'UNSPEC.STRUCTURE T)))
    (VALUES 'UNSPEC.STRUCTURE SORT.SYMBOL 'TRUE)))


(DEFUN COM=2=ENUM.STRUCTURE.DEFINITION ()

  ;;; Edited : 19-OCT-92
  ;;; Effect : <ENUM.STRUCTURE.DEFINITION> -> ENUM STRUCTURE <ENUM.DECLARATION> : <IDENTIFIER> [WITH <IDENTIFIER> END]
  ;;; Value  : the code generated by this rule, i.e. a multiple value TYPE / NAME / RESULTS.

  (LET (ENUM.LIST SORT.SYMBOL PREFIX LEFT)
       (COM=1=SYMBOL.ACCEPTED '("STRUCTURE"))
       (COND ((COM=1=SYMBOL.IS '("IDENTIFIER" "NUMBER"))
	      (SETQ ENUM.LIST (COM=2=CONSTANT.LIST))))
       (COND ((NOT (COM=1=SYMBOL.ACCEPTED '(":")))
	      (COM=ERROR 0 "Colon expected"))
	     (T (SETQ SORT.SYMBOL (COM=2=SORT.SYMBOL))))
       (COND ((SETQ LEFT (COM=2=LEFT.BRACKET))
	      (SETQ PREFIX (COM=2=IDENTIFIER.OR.NAME))
	      (COM=2=RIGHT.BRACKET LEFT)))
       ;;; insert structure-information
       (SETQ SORT.SYMBOL (COM=INSERT.ENUM.INFORMATION ENUM.LIST SORT.SYMBOL))
       ;;; generate code
       (COM=GENERATE.ENUM.CODE SORT.SYMBOL PREFIX)))

(DEFUN COM=2=GENERIC.DEFINITION ()

  ;;; Edited : 01-OCT-92
  ;;; Effect : <GENERIC.DEFINITION> -> GENERIC <IDENTIFIER>
  ;;;          a new dt-sort is introduced.
  ;;; Value  : the code generated by this rule, i.e. a multiple value TYPE / NAME / RESULTS.

  (LET (SORT.SYMBOL LEFT DEFINITION)
     (COND ((NOT (COM=1=SYMBOL.IS '("IDENTIFIER" "NAME")))
	   (COM=ERROR 0 "Datatype-Identifier expected"))
	  (T (SETQ SORT.SYMBOL (COM=2=SORT.SYMBOL))))
     (SETQ SORT.SYMBOL (COM=3=INTRODUCE.SORT SORT.SYMBOL NIL (LIST 'GENERIC T 'USE () 'HAS.INSTANCE ())))
     (COND ((SETQ LEFT (COM=2=LEFT.BRACKET))
	    (COND ((NOT (SETQ DEFINITION (COM=2=DEFINITIONS)))
		   (COM=ERROR 0 "missing definition between WITH and END")))
	    (COM=2=RIGHT.BRACKET LEFT)))
     (VALUES 'GENERIC SORT.SYMBOL DEFINITION)))


(DEFUN COM=2=INSTANCE.DEFINITION ()

  ;;; Edited : 19-OCT-92
  ;;; Effect : <INSTANCE.DEFINITION> -> INSTANTIATE <IDENTIFIER> TO <IDENTIFIER> WITH (<IDENTIFIER> = <IDENTIFIER>)+ END
  ;;; Value  : the code generated by this rule, i.e. a multiple value TYPE / NAME / RESULTS.

  (LET (INSTANCE.LIST NEW.NAME.LIST LEFT)
     (SETQ INSTANCE.LIST (COM=2=INSTANCE.LIST))
     (IF (NOT (SETQ LEFT (COM=2=LEFT.BRACKET))) (COM=ERROR 0 "WITH equations END expected"))
     (SETQ NEW.NAME.LIST (COM=2=EQUATION.LIST))
     (IF (NOT NEW.NAME.LIST) (COM=ERROR 0 "equation-list expected"))
     (COM=2=RIGHT.BRACKET LEFT)
     (VALUES 'INSTANCES (COM=2=INSTANCE.OVERLOADING INSTANCE.LIST NEW.NAME.LIST))))


(DEFUN COM=2=INSTANCE.LIST ()
  (COM=ITERATION.WITH.SEPARATOR #'COM=2=INSTANCE '(",")))


(DEFUN COM=2=INSTANCE ()
  (LET (SORT1 SORT2 GEN.SORT INST.SORT)
    (COND ((SETQ SORT1 (COM=2=IDENTIFIER.OR.NAME))
	   (IF (NOT (SETQ GEN.SORT (COM=5=NAME.OBJECT SORT1 NIL '(SORT))))
	       (COM=ERROR 4 "sort" SORT1))
	   (SETQ GEN.SORT (COM=3=CHECK.SORT GEN.SORT))
	   (IF (NOT (MEMBER 'GENERIC (DA-SORT.ATTRIBUTES GEN.SORT)))
	       (COM=ERROR 80 GEN.SORT))
	   (COND ((NOT (COM=1=SYMBOL.ACCEPTED '("TO")))
		  (COM=ERROR 0 "TO expecting")))
	   (COND ((SETQ SORT2 (COM=2=IDENTIFIER.OR.NAME))
		  (IF (NOT (SETQ INST.SORT (COM=5=NAME.OBJECT SORT2 NIL '(SORT))))
		      (COM=ERROR 4 "sort" SORT2))
		  (SETQ INST.SORT (COM=3=CHECK.SORT INST.SORT))))
	   (COND ((MEMBER INST.SORT (GETF (DA-SORT.ATTRIBUTES GEN.SORT) 'HAS.INSTANCE))
		  (COM=ERROR 84 GEN.SORT INST.SORT)))
	   (CONS GEN.SORT INST.SORT))
          (T (COM=ERROR 0 "Invalid Instantiate-Declaration")))))
				

(DEFUN COM=2=EQUATION.LIST ()

  ;;; Edited : 19-OCT-92
  ;;; Effect : a list of equations is transformed into a list containing the left and right sides of the equations
  ;;; Value  : the new list

  (COM=ITERATION.WITH.SEPARATOR #'COM=2=EQUATION '(",")))


(DEFUN COM=2=EQUATION ()

  ;;; Edited : 19-OCT-92
  ;;; Effect : transforms an equation into a list representing the left and right side.
  
 (LET (IDENT1 IDENT2)
      (COND ((SETQ IDENT1 (COM=2=IDENTIFIER.OR.NAME))
	     (COND ((NOT (COM=1=SYMBOL.ACCEPTED '("=")))
		    (COM=ERROR 0 "Missing equality-sign")))
	     (SETQ IDENT2 (COM=2=IDENTIFIER.OR.NAME))
	     (CONS IDENT1 IDENT2))
	    (T (COM=ERROR 0 "Identifier or Name expected")))))


(DEFUN COM=2=SET.DEFINITION ()
  ;;; Edited : 04.01.94 by CS
  ;;; Effect : <SET.DEFINITION> -> SET <IDENTIFIER> OF <IDENTIFIER> or
  ;;;                                  ... WITH (<IDENTIFIER> = <IDENTIFIER>)+ END

  (LET (SET.SORT.SYMBOL ELEMENT.SORT.SYMBOL INSTANTIATION.LIST SET.INSTANTIATIONS LEFT)
    (COM=1=SYMBOL.ACCEPTED '("SET"))
    (SETQ SET.SORT.SYMBOL (COM=2=SORT.SYMBOL))
    (COND ((COM=1=SYMBOL.ACCEPTED '("OF"))
	   (SETQ ELEMENT.SORT.SYMBOL (COM=2=SORT.SYMBOL)))
	  (T (COM=ERROR 0 "OF expected")))
    (COM=3=CHECK.SET.SORTS SET.SORT.SYMBOL ELEMENT.SORT.SYMBOL)
    (SETQ SET.INSTANTIATIONS (DP-SET.INSTANTIATIONS SET.SORT.SYMBOL))
    (SETQ INSTANTIATION.LIST SET.INSTANTIATIONS)
    (COND ((SETQ LEFT (COM=2=LEFT.BRACKET))
	   (COND ((SETQ INSTANTIATION.LIST (COM=2=EQUATION.LIST)))
		 (T (COM=ERROR 0 "instantiation list expected")))
	   (SETQ INSTANTIATION.LIST (COM=2=MERGE.INSTANTIATIONS INSTANTIATION.LIST SET.INSTANTIATIONS))
	   (COM=3=CHECK.INSTANTIATION.LIST INSTANTIATION.LIST (DP-SET.CONSTRUCTOR.NAMES) (DP-SET.NAMES))
	   (COM=2=RIGHT.BRACKET LEFT)))
    (VALUES 'SET SET.SORT.SYMBOL (LIST SET.SORT.SYMBOL ELEMENT.SORT.SYMBOL INSTANTIATION.LIST))))


(DEFUN COM=2=ARRAY.DEFINITION ()
  ;;; Edited : 04.01.94 by CS
  ;;; Effect : <ARRAY.DEFINITION> -> ARRAY <IDENTIFIER> [ <IDENTIFIER> ] OF <IDENTIFIER>
  ;;;                                ARRAY <IDENTIFIER> [ <IDENTIFIER> ] OF <IDENTIFIER> or
  ;;;                                      ...WITH (<IDENTIFIER> = <IDENTIFIER>)+ END
  
  (LET (ARRAY.SORT.SYMBOL INDEX.SORT.SYMBOL ENTRY.SORT.SYMBOL INSTANTIATION.LIST ARRAY.INSTANTIATIONS LEFT)
    (COM=1=SYMBOL.ACCEPTED '("ARRAY"))
    (SETQ ARRAY.SORT.SYMBOL (COM=2=SORT.SYMBOL))
    (COND ((COM=1=SYMBOL.ACCEPTED '("["))
	   (SETQ INDEX.SORT.SYMBOL (COM=2=SORT.SYMBOL))
	   (COND ((AND (COM=1=SYMBOL.ACCEPTED '("]"))
		       (COM=1=SYMBOL.ACCEPTED '("OF")))
		  (SETQ ENTRY.SORT.SYMBOL (COM=2=SORT.SYMBOL)))
		 (T (COM=ERROR 0 "] OF expected"))))
	  (T (COM=ERROR 0 "[ expected")))
    (COM=3=CHECK.ARRAY.SORTS ARRAY.SORT.SYMBOL INDEX.SORT.SYMBOL ENTRY.SORT.SYMBOL)
    (SETQ ARRAY.INSTANTIATIONS (DP-ARRAY.INSTANTIATIONS ARRAY.SORT.SYMBOL))
    (SETQ INSTANTIATION.LIST ARRAY.INSTANTIATIONS)
    (COND ((SETQ LEFT (COM=2=LEFT.BRACKET))
	   (COND ((SETQ INSTANTIATION.LIST (COM=2=EQUATION.LIST)))
		 (T (COM=ERROR 0 "instantiation list expected")))
	   (SETQ INSTANTIATION.LIST (COM=2=MERGE.INSTANTIATIONS INSTANTIATION.LIST ARRAY.INSTANTIATIONS))
	   (COM=3=CHECK.INSTANTIATION.LIST INSTANTIATION.LIST (DP-ARRAY.CONSTRUCTOR.NAMES) (DP-ARRAY.NAMES))
	   (COM=2=RIGHT.BRACKET LEFT)))
    (VALUES 'ARRAY ARRAY.SORT.SYMBOL (LIST ARRAY.SORT.SYMBOL INDEX.SORT.SYMBOL ENTRY.SORT.SYMBOL
					   INSTANTIATION.LIST))))



(DEFUN COM=2=MERGE.INSTANTIATIONS (COM.INSTANTIATIONS INSTANTIATIONS)
  ;;; Edited : 10.01.94 by CS
  ;;; Input  : a list of instantiations from COM=2=EQUATION.LIST, i.e., each element is of the
  ;;;          form "cons left right", and a list of predefined instantiations, i.e., each element is
  ;;;          of the form "(list left right liste)" 
  ;;; Value  : an instantiation list of the second form, where each element of INSTANTIATIONS is replaced
  ;;;          by its counterpart in COM.INSTANTIATIONS

  (LET (INSTANCE)
    (MAPC #'(LAMBDA (INSTANCE1)
	      (COND ((SETQ INSTANCE (FIND-IF #'(LAMBDA (INSTANCE2)
						 (STRING-EQUAL (CAR INSTANCE1) (FIRST INSTANCE2)))
					     INSTANTIATIONS))
		     (SETQ INSTANTIATIONS (SUBSTITUTE-IF (LIST (CAR INSTANCE1) (CDR INSTANCE1) (THIRD INSTANCE))
							 #'(LAMBDA (INSTANCE2)
							     (STRING-EQUAL (CAR INSTANCE1) (FIRST INSTANCE2)))
							 INSTANTIATIONS)))
		    (T (SETQ INSTANTIATIONS (CONS (LIST (CAR INSTANCE1) (CDR INSTANCE1) NIL) INSTANTIATIONS)))))
	  COM.INSTANTIATIONS)
  INSTANTIATIONS))


(DEFUN COM=2=FREE.STRUCTURE.DEFINITION ()
  
  ;;; Edited:  19-APR-82 14:01:59
  ;;; Effect:  <FREE.STRUCTURE DEFINITION> ->  <FREE CONSTRUCTORS> : <IDENTIFIER>
  ;;; value:   the code generated by this rule , i.e. a multiple value TYPE / NAME / RESULTS where RESULTS is a list
  ;;;          of lists each representing a formula.
  
  (LET (SORT.SYMBOL CONSTR.DEFS)
    ;;; parse structure definition
    (COM=1=SYMBOL.ACCEPTED '("STRUCTURE"))
    (SETQ CONSTR.DEFS (COM=2=CONSTRUCTORS))
    (COND ((COM=1=SYMBOL.ACCEPTED '(":"))
	   (SETQ SORT.SYMBOL (COM=2=SORT.SYMBOL)))
	  (T (COM=ERROR 0 "colon expected")))
    ;;; insert structure information
    (SETQ SORT.SYMBOL (COM=INSERT.STRUCTURE.INFORMATION CONSTR.DEFS SORT.SYMBOL
							(LIST 'STRUCTURE T 'FREE.STRUCTURE T 'DISJUNCT.RANGE T)))
    ;;; generate code
    (COM=GENERATE.FREE.CODE SORT.SYMBOL)))


(DEFUN COM=2=CONSTRUCTORS ()

  (COND ((COM=1=SYMBOL.IS '("IDENTIFIER" "NAME" "NUMBER" "("))
	 (COM=ITERATION.WITH.SEPARATOR #'COM=2=CONSTRUCTOR.FUNCTION '(",")))))


(DEFUN COM=2=CONSTRUCTOR.FUNCTION ()
  (LET (CONSTRUCTOR SELECTOR.SORT.LIST BASE.SORT SORT.SYMBOL)
    (COND ((COM=1=SYMBOL.IS '("IDENTIFIER" "NAME"))
	   (SETQ CONSTRUCTOR (COM=2=CONSTANT))
           (COND ((AND (COM=1=SYMBOL.ACCEPTED '("("))
		       (SETQ SELECTOR.SORT.LIST (COM=2=SELECTOR.SORT.LIST))
		       (COM=1=SYMBOL.ACCEPTED '(")"))
	          (CONS CONSTRUCTOR SELECTOR.SORT.LIST)))
		 (T (CONS CONSTRUCTOR NIL))))
       	  ((COM=1=SYMBOL.IS '("NUMBER"))
	   (SETQ CONSTRUCTOR (COM=2=CONSTANT))
	   (COND ((COM=1=SYMBOL.ACCEPTED '("("))
		  (COM=ERROR 0 "instead of constructor function is base constant expected"))
		 (T (CONS CONSTRUCTOR NIL))))
	  ((COM=1=SYMBOL.ACCEPTED '("("))
	   (SETQ BASE.SORT (COM=2=CONSTANT))
	   (COND ((COM=1=SYMBOL.ACCEPTED '(":"))
		  (SETQ SORT.SYMBOL (COM=2=SORT.SYMBOL))))
	   (IF (NOT (COM=1=SYMBOL.ACCEPTED '(")"))) (COM=ERROR 0 "missing right bracket"))
	   (COND (SORT.SYMBOL
		  (LIST NIL (CONS BASE.SORT SORT.SYMBOL)))
		 (T (LIST NIL (CONS NIL BASE.SORT)))))
	  (T (COM=ERROR 0 "Identifier, name or number expected")))))


(DEFUN COM=2=SELECTOR.SORT.LIST ()
  
  ;;; Edited:  24-JUL-81 16:17:28
  ;;; Effect:  <SORT.SELECTOR.LIST> -> { <SORT.SELECTOR.SYMBOL> }*
  ;;; Value:   the code generated by this rule, i.e. a list of code generated by <SORT.SELECTOR.SYMBOL>.
  
  (COM=ITERATION.WITH.SEPARATOR #'COM=2=SELECTOR.SORT.SYMBOL '(",")))


(DEFUN COM=2=SELECTOR.SORT.SYMBOL ()
  
  ;;; Edited:  17-JUL-81 11:38:08
  ;;; Effect:  <SORT.SELECTOR.SYMBOL> -> <IDENTIFIER> :<SORT> or <NAME>:<SORT> 
  ;;; Value:   a string, denoting a sort or a selector and a sort
  
  (LET ((SORT COM*SYMBOL) SELECTOR)
    (COND ((COM=1=SYMBOL.IS '("NAME")) (SETQ SELECTOR (COM=2=NAME))
	   (COND ((COM=1=SYMBOL.ACCEPTED '(":")) (CONS SELECTOR (COM=2=SORT.SYMBOL)))
                 (T (COM=ERROR 0 "colon expected"))))
          ((COM=1=SYMBOL.IS '("IDENTIFIER")) (SETQ SELECTOR (COM=2=IDENTIFIER))
           (COND ((COM=1=SYMBOL.ACCEPTED '(":")) (CONS SELECTOR (COM=2=SORT.SYMBOL)))
                 (T (CONS NIL (CDR SORT)))))
          ((COM=1=SYMBOL.IS '("ANY")) (COM=ERROR 0 "ANY is not an allowed sort")))))


(DEFUN COM=2=NON-FREE.STRUCTURE.DEFINITION ()
  
  ;;; Edited: 19-OCT-92
  ;;; Effect: <NON-FREE.STRUCTURE DEFINITION> -> <NON-FREE CONSTRUCTORS> : <IDENTIFIER>
  ;;;         a new dt-sort is introduced.
  ;;; Value:  the code generated by this rule , i.e. a multiple value TYPE / NAME / RESULTS where RESULTS is a list 
  ;;;         of lists each representing a formula.
  
  (LET (SORT.SYMBOL CONSTR.DEFS LIST.OF.CONSTRAINS LEFT)
    ;;; parse structure definition
    (COM=1=SYMBOL.ACCEPTED '("STRUCTURE"))
    (SETQ CONSTR.DEFS (COM=2=CONSTRUCTORS))
    (COND ((COM=1=SYMBOL.ACCEPTED '(":"))
	   (SETQ SORT.SYMBOL (COM=2=SORT.SYMBOL)))
	  (T (COM=ERROR 0 "colon expected")))
    (SETQ SORT.SYMBOL (COM=INSERT.STRUCTURE.INFORMATION CONSTR.DEFS SORT.SYMBOL (LIST 'STRUCTURE T 'NON-FREE T)))
    (COND ((SETQ LEFT (COM=2=LEFT.BRACKET))
	   (COND ((NOT (SETQ LIST.OF.CONSTRAINS (COM=2=DEFINITIONS)))
		  (COM=ERROR 0 "missing definition between WITH and END")))
	   (COM=2=RIGHT.BRACKET LEFT)))
    (COM=GENERATE.NON-FREE.CODE SORT.SYMBOL LIST.OF.CONSTRAINS)))


(DEFUN COM=2=DEFINITIONS ()

  ;;; Edited : 14-OCT-92
  ;;; Value:   a list of tripels: type of a formula, its name, and the formula itself.

  (COM=ITERATION.WITHOUT.SEPARATOR
   #'(LAMBDA ()
       (MULTIPLE-VALUE-BIND (TYPE NAME FORMULA) (COM=2=DEFINITION)
	 (LIST TYPE NAME FORMULA)))
   '("D-PREDICATE" "D-FUNCTION" "AXIOM")))


(DEFUN COM=2=DEFINITION ()
  (COND ((COM=1=SYMBOL.ACCEPTED '("AXIOM"))
         ;;;;(VALUES 'AXIOM NIL (COM=2=QUANTIFICATION))
	 (COM=2=AXIOM)
	 )
	((COM=1=SYMBOL.IS '("D-FUNCTION"))
         (COM=2=DECLARATIVE.FUNCTION.DEFINITION))
        ((COM=1=SYMBOL.IS '("D-PREDICATE"))
         (COM=2=DECLARATIVE.PREDICATE.DEFINITION))
	(T (COM=ERROR 0 "definition or END expected"))))


(DEFUN COM=2=SORT.SYMBOL ()
  
  ;;; Edited:  17-JUL-81 11:38:08
  ;;; Effect:  <SORT.SYMBOL> -> <IDENTIFIER>
  ;;; Value:   a string, denoting a sort.
  
  (LET ((SORT COM*SYMBOL))
    (COND ((COM=1=SYMBOL.ACCEPTED '("IDENTIFIER"))
	   (CDR SORT))
	  ((COM=1=SYMBOL.ACCEPTED '("ANY"))
	   (COM=ERROR 0 "ANY is not an allowed sort"))
	  (T (COM=ERROR 0 "a sort name expected")))))


;;;======================================================================================================
;;; These functions store all occurences of a sort parameterin a use.list and create instantiated copies
;;; of all objects in the use.list when the user gives (in INSTANTIATE) a value for the parameter
;;;=====================================================================================================


(DEFUN COM=2=USE.LIST.INSERT (GEN.SORT.LIST FUNPRED &OPTIONAL SORT)

  ;;; Edited : 06-APR-93
  ;;; Input  : GEN.SORT.LIST: a list containing structures defined by generic types
  ;;;          FUNPRED: a predicate/function which has a generic data type as domain/domain or range 
  ;;;          SORT: a structure which was declared over a generic data type
  ;;; Effect : the USE.LISTs of GEN.SORTs are extended by the occurences of the generic sorts in FUNPRED and
  ;;;          SORT
  ;;; Value  : the updated USE.LISTs

  (MAPC #'(LAMBDA (GEN.SORT)
	    (LET (SORT.LIST FUNPRED.LIST)
	      (SETQ FUNPRED.LIST (COM=2=UPDATE.USE.LIST (COM=2=USED.IN.FUNPREDS GEN.SORT) FUNPRED))
	      (SETQ SORT.LIST (COM=2=USED.IN.SORTS GEN.SORT))
	      (if sort (SETQ SORT.LIST (COM=2=UPDATE.USE.LIST SORT.LIST (LIST SORT))))
	      (SETF (GETF (DA-SORT.ATTRIBUTES GEN.SORT) 'USE) (LIST SORT.LIST FUNPRED.LIST))))
	  GEN.SORT.LIST))


(DEFUN COM=2=USED.IN.SORTS (GEN.SORT)
  (CAR (GETF (DA-SORT.ATTRIBUTES GEN.SORT) 'USE)))


(DEFUN COM=2=USED.IN.FUNPREDS (GEN.SORT)
  (CADR (GETF (DA-SORT.ATTRIBUTES GEN.SORT) 'USE)))


(DEFUN COM=2=UPDATE.USE.LIST (USE.LIST INSERT.LIST)

  ;;; Edited : APR-93
  ;;; Input  : USE.LIST is a USE.LIST of a generic sort
  ;;;          INSERT.LIST is a list of sorts or funpreds which are to be added to USE.LIST
  ;;; Value  : the updated USE.LIST
  
  (MAPC #' (LAMBDA (INS)
	     (COND ((NOT (MEMBER INS USE.LIST))
		    (SETQ USE.LIST (CONS INS USE.LIST)))))
	   INSERT.LIST)
  USE.LIST)


(DEFUN COM=2=CHECK.SORT.FOR.PARAMETER (SORT GEN.INDEX)

  ;;; Edited : JUL-93
  ;;; Input  : SORT is a sort, GEN.INDEX is a list of generic sorts
  ;;; Effect : if SORT is defined over a generic type and GEN.INDEX does not contain this generic type, then it is
  ;;;          added to GEN.INDEX
  ;;; Value  : the list GEN.INDEX

  (COND ((MEMBER 'GENERIC (DA-SORT.ATTRIBUTES SORT))
         (IF (NOT (MEMBER SORT GEN.INDEX)) (SETQ GEN.INDEX (CONS SORT GEN.INDEX))))
        ((MEMBER 'PARAMS (DA-SORT.ATTRIBUTES SORT))
	 (MAPC #'(LAMBDA (GEN.SORT)
		   (IF (NOT (MEMBER GEN.SORT GEN.INDEX)) (SETQ GEN.INDEX (CONS GEN.SORT GEN.INDEX))))
	       (GETF (DA-SORT.ATTRIBUTES SORT) 'PARAMS))))
  GEN.INDEX)


(DEFUN COM=2=CHECK.PREFUN.FOR.PARAMETER (PREFUN GEN.LIST)

  ;;; Edited : APR-93
  ;;; Input  : a predicate or function
  ;;; Value  : a list of all parameters that concern PREFUN 

  (MAPC #'(LAMBDA (DOMAIN)
	     (SETQ GEN.LIST (COM=2=CHECK.SORT.FOR.PARAMETER DOMAIN GEN.LIST)))
	 (DA-PREFUN.DOMAIN.SORTS PREFUN))
  (COND ((DA-FUNCTION.IS PREFUN)
         (SETQ GEN.LIST (COM=2=CHECK.SORT.FOR.PARAMETER (DA-FUNCTION.SORT PREFUN) GEN.LIST))))
  GEN.LIST)


(DEFUN PRINT=USE.LIST (GEN)
  ;;; nur zur Kontrolle
  
  (LET (USE.LIST)
    (SETF USE.LIST (GETF (DA-SORT.ATTRIBUTES GEN) 'USE))
    (FORMAT *terminal-io* "~%~% USE.LIST ~A ~%" GEN)
    (MAPC #'(LAMBDA (L)
	      (FORMAT *Terminal-io* "~A ~%" L))
	  USE.LIST)
    (FORMAT *terminal-io* "~%")))


(DEFUN COM=2=INSTANCE.OVERLOADING (INSTANTIATION NEW.NAME.LIST)

  ;;; Edited : MAY-93
  ;;; Input  : INSTANTIATION.LIST is a list of generic sorts and instance sorts of the form
  ;;;          ((generic sort1 . instance sort 1) (generic sort2 . instance sort2)...)
  ;;;          NEW.NAME.LIST is the equation list provided by COM=2=INSTANCE.DEFINITION
  ;;; Effect : all functions and predicates depending on the generic sort are overloaded,
  ;;;          the overloading is tested for completeness
  ;;; Value  : ???? der Wert von INSTANZ.OF muss eine Liste sein, +:e1, pl:e2, bei Inst. von beiden auf nat wird plus
  ;;;          Instanz von beiden

  (LET (INSTANCE.LIST)
    (SETQ INSTANCE.LIST (COM=2=INSTANTIATION INSTANTIATION NEW.NAME.LIST))
    (MAPC #'(LAMBDA (SORT)
	      (COND ((MEMBER 'GENERIC (DA-SORT.ATTRIBUTES (CAR SORT)))
		     (COND ((GETF (DA-SORT.ATTRIBUTES (CAR SORT)) 'HAS.INSTANCE)
			    (SETF (GETF (DA-SORT.ATTRIBUTES (CAR SORT)) 'HAS.INSTANCE)
				  (CONS (CDR INSTANTIATION) (GETF (DA-SORT.ATTRIBUTES (CAR SORT)) 'HAS.INSTANCE))))
			   (T (SETF (GETF (DA-SORT.ATTRIBUTES (CAR SORT)) 'HAS.INSTANCE) (LIST (CDR SORT))))))
		    (T (SETF (GETF (DA-SORT.ATTRIBUTES (CAR SORT)) 'HAS.INSTANCE) T)
		       (COM=2=USE.LIST.INSERT (COM=2=CHECK.SORT.FOR.PARAMETER (CDR SORT) NIL) NIL (CDR SORT)))))
          (CAR INSTANCE.LIST))
    (MAPC #'(LAMBDA (PREFUN)
	      (COM=2=USE.LIST.INSERT (COM=2=CHECK.PREFUN.FOR.PARAMETER (CDR PREFUN) NIL) (LIST (CDR PREFUN))))
          (SECOND INSTANCE.LIST))
    INSTANCE.LIST))
  

(DEFUN COM=2=SEARCH.NEW.NAME.LIST (NAME NEW.NAME.LIST)

  ;;; Edited : June-93
  ;;; Input  : the name of a sort, function or predicate
  ;;; Effect : searches the list NEW.NAME.LIST with the renamings given by the user in INSTANTIATE, until it finds a name for the
  ;;;          new instance ofthe object with name NAME
  ;;; Value  : the new name, if found; else nil

  (LET (NEW.NAME)
    (SETQ NEW.NAME (FIND NAME NEW.NAME.LIST :KEY #'CAR :TEST #'STRING-EQUAL))
    (CDR NEW.NAME)))


(DEFUN COM=2=INSTANTIATION (INSTANTIATION NEW.NAME.LIST)

  ;;; Edited : JUNE-93
  ;;; Input  : INSTANTIATION is a list of conses such that the car of each element is a generic type and the cdr
  ;;;          is a sort
  ;;;          NEW.NAME.LIST is the list with the renamings for the new instances
  ;;; Effect : for all sorts, predicates and functions containing a sort parameter in INSTANTIATION, an instance is created
  ;;;          where each sort parameter is replaced by the connected sort
  ;;; Value  : a list of conses such that the car of each element is a SORT or PREFUN, defined over the sort parameter GEN.SORT,
  ;;;          and the cdr is an instance of the car with GEN.SORT = INST.SORT
  ;;; ???? falls hier irgendwo ein Fehler auftritt, dann sind einige Sorten- und Prefun - Instanzen schon erzeugt,
  ;;; (und stehen in der Hash-table). die muss man doch noch streichen !
  
  (LET (SORT.INST.LIST PREFUN.INST.LIST SORT.LIST PREFUN.LIST)
    (SETQ SORT.LIST (MAPCAN #'(LAMBDA (INST)
				 (REVERSE (COM=2=USED.IN.SORTS (CAR INST))))
			    INSTANTIATION))
    (SETQ SORT.LIST (MAPCAR #'(LAMBDA (SORT)
				(LET (NEW.NAME)
				  (COND ((SETQ NEW.NAME (COM=2=SEARCH.NEW.NAME.LIST (DA-SORT.PNAME SORT) NEW.NAME.LIST))
					 (SETQ NEW.NAME.LIST (DELETE NEW.NAME NEW.NAME.LIST :KEY #'CDR :TEST #'EQ))
				         (CONS SORT NEW.NAME))
				        (T (COM=ERROR 81 "sort" (DA-SORT.PNAME SORT))))))
			    (REMOVE-DUPLICATES SORT.LIST)))
    (SETQ PREFUN.LIST (MAPCAN #'(LAMBDA (INST)
				(REVERSE (COM=2=USED.IN.FUNPREDS (CAR INST))))
			    INSTANTIATION))
    (SETQ PREFUN.LIST (MAPCAR #'(LAMBDA (PREFUN)
				   (LET (NEW.NAME)
				     (SETQ NEW.NAME (COM=2=SEARCH.NEW.NAME.LIST (DA-PREFUN.PNAME PREFUN) NEW.NAME.LIST))
				     (SETQ NEW.NAME.LIST (DELETE NEW.NAME NEW.NAME.LIST :KEY #'CDR :TEST #'EQ))
				     (CONS PREFUN NEW.NAME)))
			      (REMOVE-DUPLICATES PREFUN.LIST)))
    (IF NEW.NAME.LIST (COM=ERROR 82 (MAPCAR #'CAR NEW.NAME.LIST)))
    (SETQ SORT.INST.LIST (COM=2=SORT.INSTANTIATION INSTANTIATION SORT.LIST))
    (SETQ PREFUN.INST.LIST (COM=2=PREFUN.INSTANTIATION PREFUN.LIST SORT.INST.LIST))
    (LIST (COM=2=INSERT.INSTANCE.INFORMATION SORT.INST.LIST PREFUN.INST.LIST) PREFUN.LIST)))

    

(DEFUN COM=2=SORT.INSTANTIATION (INSTANTIATION SORT.LIST)

  ;;; Edited : JUNE-93
  ;;; Input  : INSTANTIATION is a list of conses like in COM=2=INSTANTIATION
  ;;;          SORT.LIST is a list of conses such that the car of each element is a sort containing a parameter in 
  ;;;          INSTANTIATION and the cdr is the new name for the instance of sort
  ;;; Effect : creates the instances for all sorts in SORT.LIST such that for each pair in INSTANTIATION, every occurence of
  ;;;          the car is replaced by the cdr
  ;;; Value  : a list of conses such that the car of each element is a paramtric sort and the cdr is an instance
  ;;;          of that sort 

  (LET (NEW.SORT SORT.INST.LIST NEW.SUB ATTRIBUTES SUB.SORTS SORT NAME PARAMETER)
    (SETQ SORT.INST.LIST INSTANTIATION)
    (MAPC #'(LAMBDA (SORT.NAME)
	        (SETQ SORT (CAR SORT.NAME)
		      NAME (CDR SORT.NAME))
                (SETQ SUB.SORTS (MAPCAR #'(LAMBDA (SUB.SORT)
	                                    (COND ((SETQ NEW.SUB (FIND SUB.SORT SORT.INST.LIST :KEY #'CAR))
						   (CDR NEW.SUB))
						  (T SUB.SORT)))
				        (COPY-LIST (DA-SORT.DIRECT.SUBSORTS SORT))))
	        (SETQ ATTRIBUTES (COPY-TREE (DA-SORT.ATTRIBUTES SORT)))
                (SETQ PARAMETER (GETF ATTRIBUTES 'PARAMS))
  	        (MAPC #'(LAMBDA (INSTANCE)
			  (COND ((MEMBER (CAR INSTANCE) PARAMETER)
				 (SETQ PARAMETER (APPEND (REMOVE (CAR INSTANCE) PARAMETER)
							 (GETF (DA-SORT.ATTRIBUTES (CDR INSTANCE)) 'PARAMS))))))
		      INSTANTIATION)
		(SETF (GETF ATTRIBUTES 'INSTANCE.OF) (LIST SORT))
                (COND (PARAMETER
	               (SETF (GETF ATTRIBUTES 'PARAMS) (REMOVE-DUPLICATES PARAMETER))
	               (SETQ NEW.SORT (COM=3=INTRODUCE.SORT NAME SUB.SORTS ATTRIBUTES)))
	              (T (REMF ATTRIBUTES 'PARAMS)
  	               (SETQ NEW.SORT (COM=3=INTRODUCE.SORT NAME SUB.SORTS ATTRIBUTES))))
              (SETQ SORT.INST.LIST (CONS (CONS SORT NEW.SORT) SORT.INST.LIST)))
	  SORT.LIST)
     SORT.INST.LIST))


(DEFUN COM=2=PREFUN.INSTANTIATION (PREFUN.LIST SORT.INST.LIST)

  ;;; Edited : JUNE-93
  ;;; Input  : SORT.INST.LIST is a list of dotted pairs such that each pair consists of a parametric sort and it's instance 
  ;;;          PREFUN.LIST is a list of dotted pairs such that the car of each element is a function or predicate defined over
  ;;;          a parametric data type, and the cdr is the user-given new name for the new instance of prefun
  ;;; Effect : every prefun in PREFUN.LIST is defined over parametric sorts; for every prefun, an instance is created such that
  ;;;          the parametric sorts are replaced by their instance sorts
  ;;; Value  : a list of dotted pairs such that the car of each element is a prefun defined over parametric sorts and the cdr
  ;;;          is an instance of prefun
  ;;; ????  GIBT ES NULL STELLIGE PRAEDIKATE ??? muss ich hier testen, ob sich funktionen nur in RANGE unterscheiden ??

  (MAPC #'(LAMBDA (PREFUN.NAME)
	    (LET ((PREFUN (CAR PREFUN.NAME)) (NAME (CDR PREFUN.NAME)) DOMAIN.SORTS RANGE)
	      (SETQ DOMAIN.SORTS (MAPCAR #'(LAMBDA (DOMAIN)
					     (LET (NEW.DOMAIN)
					       (COND ((SETQ NEW.DOMAIN (FIND DOMAIN SORT.INST.LIST :KEY #'CAR :TEST #'EQ))
						      (CDR NEW.DOMAIN))
						     (T DOMAIN))))
				         (COPY-LIST (DA-PREFUN.DOMAIN.SORTS PREFUN))))
              (COND ((DA-FUNCTION.IS PREFUN)
		     (SETQ RANGE (COND ((CDR (FIND (DA-FUNCTION.SORT PREFUN) SORT.INST.LIST :KEY #'CAR)))
			               (T (DA-FUNCTION.SORT PREFUN))))
	             (COND ((DA-FUNCTION.IS.CONSTRUCTOR PREFUN)
			    (COND (NAME
				   (SETF (CDR PREFUN.NAME) (COM=3=INTRODUCE.CONSTRUCTOR NAME DOMAIN.SORTS RANGE
								  (LIST 'STRUCTURE T 'INJECTIVE T))))
				  (T (COM=ERROR 81 "constructor (constant)" (DA-FUNCTION.PNAME PREFUN)))))
			   ((DA-FUNCTION.IS.SELECTOR PREFUN)
			    (COND (NAME 
			           (SETF (CDR PREFUN.NAME) (COM=3=INTRODUCE.SYMBOL NAME 'FUNCTION DOMAIN.SORTS RANGE
								  (LIST 'SEL.STRUCTURE T))))
				  (T (SETF (CDR PREFUN.NAME) (COM=3=INTRODUCE.SYMBOL (DA-FUNCTION.PNAME PREFUN) 'FUNCTION
								    DOMAIN.SORTS RANGE (LIST 'SEL.STRUCTURE T))))))
			   ((DA-FUNCTION.IS.INDEX PREFUN)
			    (COND (NAME
				   (SETF (CDR PREFUN.NAME) (COM=3=INTRODUCE.SYMBOL NAME 'FUNCTION DOMAIN.SORTS RANGE
								 (LIST 'INDEX.FCT T))))
				  (T (SETF (CDR PREFUN.NAME) (COM=3=INTRODUCE.SYMBOL
							      (FORMAT NIL "~A_~A" (CAR DOMAIN.SORTS) RANGE)
							      'FUNCTION DOMAIN.SORTS RANGE (LIST 'INDEX.FCT T))))))
                           ((MEMBER 'DEFINED (DA-FUNCTION.ATTRIBUTES PREFUN))
			    (COND (NAME
				   (SETF (CDR PREFUN.NAME) (COM=3=CHECK.OR.INTRODUCE.SYMBOL NAME 'FUNCTION DOMAIN.SORTS RANGE
										   (LIST 'DEFINED T))))
				  (T (COND ((NULL (DA-FUNCTION.DOMAIN.SORTS PREFUN))
					    (COM=ERROR 81 "constant" (DA-FUNCTION.PNAME PREFUN)))
					   (T (SETF (CDR PREFUN.NAME) (COM=3=CHECK.OR.INTRODUCE.SYMBOL (DA-FUNCTION.PNAME PREFUN)
									     'FUNCTION DOMAIN.SORTS RANGE (LIST 'DEFINED T))))))))
			   (T (COND (NAME
				     (SETF (CDR PREFUN.NAME) (COM=3=CHECK.OR.INTRODUCE.SYMBOL NAME 'FUNCTION DOMAIN.SORTS RANGE
										     (LIST 'DECLARED T))))
				    (T (COND ((NULL (DA-FUNCTION.DOMAIN.SORTS PREFUN))
					      (COM=ERROR 81 "constant" (DA-FUNCTION.PNAME PREFUN)))
					     (T (SETF (CDR PREFUN.NAME) (COM=3=CHECK.OR.INTRODUCE.SYMBOL (DA-FUNCTION.PNAME PREFUN)
									       'FUNCTION DOMAIN.SORTS RANGE
									       (LIST 'DECLARED T))))))))))
                    ((DA-PREDICATE.IS PREFUN)
		     (COND ((MEMBER 'DEFINED (DA-PREDICATE.ATTRIBUTES PREFUN))
		            (COND (NAME
			           (SETF (CDR PREFUN.NAME) (COM=3=CHECK.OR.INTRODUCE.SYMBOL NAME 'PREDICATE DOMAIN.SORTS NIL
										   (LIST 'DEFINED T))))
			          (T (COND ((NULL (DA-PREDICATE.DOMAIN.SORTS PREFUN))
					    (COM=ERROR 81 "constant" (DA-PREDICATE.PNAME PREFUN)))
				           (T (SETF (CDR PREFUN.NAME) (COM=3=CHECK.OR.INTRODUCE.SYMBOL (DA-PREDICATE.PNAME PREFUN)
									     'PREDICATE DOMAIN.SORTS NIL (LIST 'DEFINED T))))))))
			   (T (COND (NAME
			             (SETF (CDR PREFUN.NAME) (COM=3=CHECK.OR.INTRODUCE.SYMBOL NAME 'PREDICATE DOMAIN.SORTS NIL
										     (LIST 'DECLARED T))))
			            (T (COND ((NULL (DA-PREDICATE.DOMAIN.SORTS PREFUN))
					      (COM=ERROR 81 "constant" (DA-PREDICATE.PNAME PREFUN)))
					     (T (SETF (CDR PREFUN.NAME) (COM=3=CHECK.OR.INTRODUCE.SYMBOL (DA-PREDICATE.PNAME PREFUN)
													 'PREDICATE DOMAIN.SORTS NIL
													 (LIST 'DECLARED T)))))))))))
	      (SETF (GETF (DA-PREFUN.ATTRIBUTES (CDR PREFUN.NAME)) 'INSTANCE.OF)
		    (CONS PREFUN (GETF (DA-PREFUN.ATTRIBUTES (CDR PREFUN.NAME)) 'INSTANCE.OF)))))
        PREFUN.LIST))


(DEFUN COM=2=INSERT.INSTANCE.INFORMATION (SORT.INST.LIST PREFUN.INST.LIST)

  ;;; Edited : JUL-93
  ;;; Input  : SORT.LIST is a list of conses such that the car of each is a parametric sort, and the cdr is an instance of
  ;;;          this sort
  ;;;          PREFUN.LIST is a list of conses such that the car of each is a function or predicate defined over a parametric
  ;;;          sort (which must be in SORT.LIST) and the cdr is an instance of this function or predicate
  ;;; Effect : fills the slots DA-SORT.BASE.SORTS, -.CONSTRUCTOR.FCTS, -.SELECTOR.FCTS, -.INDEX.FCTS of each sort instance
  ;;;          according to the parent sort.

  (MAPC #'(LAMBDA (SORT.INST)
	    (LET ((SORT (CAR SORT.INST)) (INST (CDR SORT.INST))
		  BASE.SORTS NEW.BASE CONSTR.FCTS NEW.CONSTR SELECT.FCTS NEW.SELECT INDEX.FCTS NEW.INDEX)
	      (SETQ BASE.SORTS (MAPCAR #'(LAMBDA (BASE.SORT)
	                                    (COND ((SETQ NEW.BASE (FIND BASE.SORT SORT.INST.LIST :KEY #'CAR))
						   (CDR NEW.BASE))
						  (T BASE.SORT)))
				       (DA-SORT.BASE.SORTS SORT)))
	      (SETQ CONSTR.FCTS (MAPCAR #'(LAMBDA (CONSTR.DEF)
					    (COND ((SETQ NEW.CONSTR (FIND CONSTR.DEF PREFUN.INST.LIST :KEY #'CAR))
						   (CDR NEW.CONSTR))
						  (T CONSTR.DEF)))
					(DA-SORT.CONSTRUCTOR.FCTS SORT)))
	      (SETQ SELECT.FCTS (MAPCAR #'(LAMBDA (SELECT.FCT)
					    (COND (SELECT.FCT
						   (COND ((SETQ NEW.SELECT (FIND SELECT.FCT PREFUN.INST.LIST :KEY #'CAR))
						          (CDR NEW.SELECT))
						         (T SELECT.FCT)))))
					 (DA-SORT.SELECTOR.FCTS SORT)))
	      (SETQ INDEX.FCTS (MAPCAR #'(LAMBDA (INDEX.FCT)
					    (COND ((SETQ NEW.INDEX (FIND INDEX.FCT PREFUN.INST.LIST :KEY #'CAR))
						   (CDR NEW.INDEX))
						  (T INDEX.FCT)))
					(DA-SORT.INDEX.FCTS SORT)))
              (SETF (DA-SORT.BASE.SORTS INST) BASE.SORTS)
              (SETF (DA-SORT.CONSTRUCTOR.FCTS INST) CONSTR.FCTS)
              (SETF (DA-SORT.INDEX.FCTS INST) INDEX.FCTS)
              (SETF (DA-SORT.SELECTOR.FCTS INST) SELECT.FCTS)))
	SORT.INST.LIST))

	
(DEFUN PRINT=INSTANCE.LIST (LIST)
  (LET (COUNTER)
    (SETQ COUNTER 0)
    (FORMAT T "~%prefun.inst.list ~%")
    (MAPC #'(LAMBDA (PAIR)
	      (COND ((EQ COUNTER 5)
		     (FORMAT *terminal-io* "~%~A " PAIR)
		     (SETQ COUNTER 0))
		    (T (FORMAT *terminal-io* "~A " PAIR)
		     (SETQ COUNTER (1+ COUNTER)))))
	  LIST)))


;;;====================================================================================================
;;;  These functions insert information about structures into the database and generate the structure code
;;;=====================================================================================================


(DEFUN COM=INSERT.ENUM.INFORMATION (ENUM.LIST STRUCTURE.SORT)

  ;;; Edited : OCT-92
  ;;; Effect : all information about the ENUM-Structure is entered into the according datastructures of DT
  ;;; Value  : the new introduced DT-SORT
  
  (SETQ STRUCTURE.SORT (COM=3=INTRODUCE.SORT STRUCTURE.SORT NIL
					     (LIST 'STRUCTURE T 'ENUMERATED T 'FREE.STRUCTURE T 'DISJUNCT.RANGE T)))
  (SETQ ENUM.LIST (MAPCAR #'(LAMBDA (CONST)
				    (COM=3=INTRODUCE.CONSTRUCTOR CONST NIL STRUCTURE.SORT (LIST 'STRUCTURE T 'DISJUNCT.RANGE T)))
			  ENUM.LIST))
  (SETF (DA-SORT.CONSTRUCTOR.FCTS STRUCTURE.SORT) ENUM.LIST)
  STRUCTURE.SORT)


(DEFUN COM=INSERT.STRUCTURE.INFORMATION (CONSTRUCTORS STRUCTURE.SORT ATTRIBUTES)
  
  ;;; edited  : 21-feb-89
  ;;; effect  : all information about newly introduced function- and constant symbols is entered
  ;;;           into the according datastructures of DT.
  ;;; value   : the new introduced DT-SORT
  
  (LET (ACCESS FCT SELECT.FCTS INDEX.FCTS GEN.INDEX SELECTOR.LIST BASE.SORTS CONSTR.DEFS)

    (MAPC #'(LAMBDA (CONSTRUCTOR)
	      (COND ((CAR CONSTRUCTOR)
		     (SETQ CONSTR.DEFS (CONS CONSTRUCTOR CONSTR.DEFS)))
		    (T (SETQ BASE.SORTS (CONS (CADR CONSTRUCTOR) BASE.SORTS)))))
	  CONSTRUCTORS)
    
    (COND ((AND (NULL BASE.SORTS)
	        (EVERY #'(LAMBDA (CONSTR)
			   (SOME #'(LAMBDA (SELECTOR.SORT)
			           (STRING-EQUAL (CDR SELECTOR.SORT) STRUCTURE.SORT))
			         (CDR CONSTR)))
		       CONSTR.DEFS))
	   (COM=ERROR 10)))

    (MAPC #'(LAMBDA (BASE.SORT) 
	      (SETF (CDR BASE.SORT) (COM=3=CHECK.OR.INTRODUCE.SORT (CDR BASE.SORT) NIL)))
	  BASE.SORTS)

    (COM=CHECK.DISJUNCTION BASE.SORTS STRUCTURE.SORT)

    (SETQ STRUCTURE.SORT (COM=3=INTRODUCE.SORT STRUCTURE.SORT (MAPCAR #'CDR BASE.SORTS) ATTRIBUTES))

    (MAPC #'(LAMBDA (CONSTR.DEF)
	      (MAPC #'(LAMBDA (SELECTOR.SORT)
			(SETF (CDR SELECTOR.SORT) (COM=3=CHECK.OR.INTRODUCE.SORT (CDR SELECTOR.SORT) NIL NIL NIL))
			(SETQ GEN.INDEX (COM=2=CHECK.SORT.FOR.PARAMETER (CDR SELECTOR.SORT) GEN.INDEX)))
		    (CDR CONSTR.DEF))
              (SETF (CAR CONSTR.DEF) (COM=3=INTRODUCE.CONSTRUCTOR
				      (CAR CONSTR.DEF) (MAPCAR #'CDR (CDR CONSTR.DEF))
				      STRUCTURE.SORT
				      (NCONC (LIST 'STRUCTURE T)
					     (COND ((GETF ATTRIBUTES 'FREE.STRUCTURE)
						    (LIST 'MONOTONIC T 'DISJUNCT.RANGE T
							  'INJECTIVE (LET ((POSITION 0))
								       (MAPCAR #'(LAMBDA (DOM)
										   (INCF POSITION))
									       (MAPCAR #'CDR (CDR CONSTR.DEF)))))))))))
					; disjunct.range new
	  CONSTR.DEFS)
    
    (SETQ SELECT.FCTS
	  (MAPCAR #'(LAMBDA (CONSTR.SELECTOR.SORT.LIST)
		      (SETQ ACCESS 0)
		      (MAPCAR #'(LAMBDA (SELECTOR.SORT)
				  (INCF ACCESS)
				  (SETQ FCT (COM=3=INTRODUCE.SYMBOL
					     (COND ((CAR SELECTOR.SORT))
						   (T (FORMAT NIL "~A_~D" (CAR CONSTR.SELECTOR.SORT.LIST) ACCESS)))
					     'FUNCTION
					     (LIST STRUCTURE.SORT) (CDR SELECTOR.SORT)
					     (LIST 'SEL.STRUCTURE T)))
				  (SETQ SELECTOR.LIST (CONS FCT SELECTOR.LIST))
				  FCT)
			      (CDR CONSTR.SELECTOR.SORT.LIST)))
		  CONSTR.DEFS))
    
    (SETQ INDEX.FCTS (MAPCAR #'(LAMBDA (SORT)
				 (COND ((CAR SORT)
					(COM=3=INTRODUCE.SYMBOL (CAR SORT) 'FUNCTION (LIST STRUCTURE.SORT) (CDR SORT)
								(LIST 'INDEX.FCT T)))
				       (T (COM=3=INTRODUCE.SYMBOL (FORMAT NIL "~A_~A" STRUCTURE.SORT (CDR SORT))
							          'FUNCTION (LIST STRUCTURE.SORT) (CDR SORT)
							          (LIST 'INDEX.FCT T)))))
			     BASE.SORTS))

    (SETF (DA-SORT.BASE.SORTS STRUCTURE.SORT) (MAPCAR #'CDR BASE.SORTS))
    (SETF (DA-SORT.CONSTRUCTOR.FCTS STRUCTURE.SORT) (MAPCAR #'CAR CONSTR.DEFS))
    (SETF (DA-SORT.INDEX.FCTS STRUCTURE.SORT) INDEX.FCTS)
    (SETF (DA-SORT.SELECTOR.FCTS STRUCTURE.SORT) SELECT.FCTS)
    (DA-SORT.GENERATE.EXAMPLES STRUCTURE.SORT)
    (COND (GEN.INDEX
	  (SETF (DA-SORT.ATTRIBUTES STRUCTURE.SORT) (APPEND (LIST 'PARAMS GEN.INDEX) (DA-SORT.ATTRIBUTES STRUCTURE.SORT)))
	  (COM=2=USE.LIST.INSERT GEN.INDEX (APPEND (MAPCAR #'CAR CONSTR.DEFS) SELECTOR.LIST INDEX.FCTS) STRUCTURE.SORT)))
    STRUCTURE.SORT))



(DEFUN COM=CHECK.DISJUNCTION (BASE.SORTS SORT)

  ;;; Edited : NOV-93
  ;;; Input  : a sort-name SORT, and the list of the BASE.SORTS of SORT
  ;;; Effect : signals ERROR if the subsorts of all sorts in BASE.SORT are not disjunct
  
  (LET (ALL.SUBSORTS)
    (SETQ ALL.SUBSORTS (MAPCAN #'(LAMBDA (SORT)
				   (COPY-LIST (DA-SORT.ALL.SUBSORTS (CDR SORT))))
			       BASE.SORTS))
    (MAPL #'(LAMBDA (SUBSORTS)
	      (COND ((FIND (CAR SUBSORTS) (REST SUBSORTS))
		     (COM=ERROR 15 SORT))))
	  ALL.SUBSORTS)))


(DEFUN COM=GENERATE.ENUM.CODE (STRUCTURE.SORT &OPTIONAL PREFIX)

  ;;; Edited : OCT-92
  ;;; Input  : a sort symbol and optionally a prefix for the generated less predicates
  ;;; Value  : the code generated by the ENUM structure definition rules, i.e. a multiple value TYPE / NAME / RESULTS
  ;;;          where RESULTS is a list of lists, each of which is a formula representing
  ;;;          - that every object appeared in the enumeration
  ;;;          - that the names of all objects are pairwise distinct
  
  (LET (COMPL.CODE UNIQUE.CODE)
       (SETQ COMPL.CODE (COM=COMPLETE.CODE STRUCTURE.SORT))
       (SETQ UNIQUE.CODE (COM=UNIQUE.CODE (DA-SORT.CONSTRUCTOR.FCTS STRUCTURE.SORT)))
       (VALUES 'ENUM.STRUCTURE STRUCTURE.SORT
	       (APPEND (COM=GENERATE.ENUM.LESS STRUCTURE.SORT PREFIX) ;; APPEND INSTEAD OF CONS 
		       (LIST (LIST 'STRUCTURE STRUCTURE.SORT
				   (DA-FORMULA.JUNCTION.CLOSURE 'AND (CONS COMPL.CODE UNIQUE.CODE))))))))


(DEFUN COM=GENERATE.ENUM.LESS (SYMBOL &OPTIONAL PREFIX)
  ;;; EDITED : 15.8.93 BY CS
  ;;; INPUT  : AN ENUMERATION SORT SYMBOL AND OPTIONALLY A PREFIX FOR THE PREDEFINED PREDICATES
  ;;; VALUE  : A LIST OF STRINGS DENOTING THE DEFINITION OF THE LESS RELATION ON THE ENUMERATION SORT
  
  (LET* ((P.SYMBOL.LESS (COND (PREFIX (COM=3=INTRODUCE.SYMBOL (FORMAT NIL "~A<" PREFIX) 'PREDICATE (LIST SYMBOL SYMBOL) NIL (LIST 'DEFINED T)))
			      (T (COM=3=INTRODUCE.SYMBOL "<" 'PREDICATE (LIST SYMBOL SYMBOL) NIL (LIST 'DEFINED T)))))
	 (P.SYMBOL.LESS.EQUAL (COND (PREFIX (COM=3=INTRODUCE.SYMBOL (FORMAT NIL "~A<=" PREFIX) 'PREDICATE (LIST SYMBOL SYMBOL) NIL (LIST 'DEFINED T)))
				    (T (COM=3=INTRODUCE.SYMBOL "<=" 'PREDICATE (LIST SYMBOL SYMBOL) NIL (LIST 'DEFINED T)))))
	 (P.SYMBOL.GREATER (COND (PREFIX (COM=3=INTRODUCE.SYMBOL (FORMAT NIL "~A>" PREFIX) 'PREDICATE (LIST SYMBOL SYMBOL) NIL (LIST 'DEFINED T)))
				 (T (COM=3=INTRODUCE.SYMBOL ">" 'PREDICATE (LIST SYMBOL SYMBOL) NIL (LIST 'DEFINED T)))))
	 (P.SYMBOL.GREATER.EQUAL (COND (PREFIX (COM=3=INTRODUCE.SYMBOL (FORMAT NIL "~A>=" PREFIX) 'PREDICATE (LIST SYMBOL SYMBOL) NIL (LIST 'DEFINED T)))
				       (T (COM=3=INTRODUCE.SYMBOL ">=" 'PREDICATE (LIST SYMBOL SYMBOL) NIL (LIST 'DEFINED T)))))
	 (VAR.X (DA-VARIABLE.CREATE SYMBOL))
	 (VAR.Y (DA-VARIABLE.CREATE SYMBOL))
	 (BODY.LESS (MAPCON #'(LAMBDA (CONSTRUCTORS)
			   (LET ((LEFT (FIRST CONSTRUCTORS))
				 (RIGHT (REST CONSTRUCTORS)))
			     (COND (RIGHT (COM=GENERATE.ENUM.LESS.LITERALS VAR.X LEFT VAR.Y RIGHT)))))
		       (DA-SORT.CONSTRUCTOR.FCTS SYMBOL)))
	 (BODY.LESS.EQUAL
	  (DA-FORMULA.CREATE 'OR (LIST (DA-LITERAL.CREATE (DA-SIGN.PLUS) P.SYMBOL.LESS
							  (LIST (DA-TERM.CREATE VAR.X) (DA-TERM.CREATE VAR.Y)))
				       (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DA-PREDICATE.EQUALITY)
							  (LIST (DA-TERM.CREATE VAR.X) (DA-TERM.CREATE VAR.Y))))))
	 (BODY.GREATER
	  (DA-LITERAL.CREATE (DA-SIGN.PLUS) P.SYMBOL.LESS (LIST (DA-TERM.CREATE VAR.Y) (DA-TERM.CREATE VAR.X))))
	 (BODY.GREATER.EQUAL
	  (DA-FORMULA.CREATE 'OR (LIST (DA-LITERAL.CREATE (DA-SIGN.PLUS) P.SYMBOL.LESS
							  (LIST (DA-TERM.CREATE VAR.Y) (DA-TERM.CREATE VAR.X)))
				       (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DA-PREDICATE.EQUALITY)
							  (LIST (DA-TERM.CREATE VAR.X) (DA-TERM.CREATE VAR.Y)))))))
    (COND ((CDR BODY.LESS) (SETQ BODY.LESS (DA-FORMULA.CREATE 'OR BODY.LESS)))
	  (BODY.LESS (SETQ BODY.LESS (CAR BODY.LESS))) ;;; NEW
	  (T (SETQ BODY.LESS (DA-LITERAL.COPY (DA-LITERAL.FALSE)))))
    (DA-GTERM.DEF.VALUE.CREATE BODY.LESS)
    (DA-GTERM.DEF.VALUE.CREATE BODY.LESS.EQUAL)
    (DA-GTERM.DEF.VALUE.CREATE BODY.GREATER)
    (DA-GTERM.DEF.VALUE.CREATE BODY.GREATER.EQUAL)
    (LIST (LIST 'PREDICATE P.SYMBOL.LESS (LIST BODY.LESS P.SYMBOL.LESS (LIST VAR.X VAR.Y)))
	  (LIST 'PREDICATE P.SYMBOL.LESS.EQUAL (LIST BODY.LESS.EQUAL P.SYMBOL.LESS.EQUAL (LIST VAR.X VAR.Y)))
	  (LIST 'PREDICATE P.SYMBOL.GREATER (LIST BODY.GREATER P.SYMBOL.GREATER (LIST VAR.X VAR.Y)))
	  (LIST 'PREDICATE P.SYMBOL.GREATER.EQUAL (LIST BODY.GREATER.EQUAL P.SYMBOL.GREATER.EQUAL (LIST VAR.X VAR.Y))))))



(DEFUN COM=GENERATE.ENUM.LESS.LITERALS (VAR.X X VAR.Y Y.LIST)
  (MAPCAR #'(LAMBDA (Y)
	  (DA-FORMULA.CREATE 'AND (LIST (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DA-PREDICATE.EQUALITY)
							 (LIST (DA-TERM.CREATE VAR.X) (DA-TERM.CREATE X)))
				      (DA-LITERAL.CREATE (DA-SIGN.PLUS) (DA-PREDICATE.EQUALITY)
							 (LIST (DA-TERM.CREATE VAR.Y) (DA-TERM.CREATE Y))))))
	  Y.LIST))


(DEFUN COM=GENERATE.FREE.CODE (STRUCTURE.SORT)

  ;;; Edited:  21-feb-89
  ;;; Effect:  see value
  ;;; Value:   the code generated by the free-structure definition rule ,i.e. a multiple value TYPE / NAME
  ;;;          / RESULTS where RESULTS is a list of lists, each representing a formula in prefix notation
  ;;;          with renamed variables representing:
  ;;;          - a formula expressing that every object is of the base sort or is in the
  ;;;            range of the constructor function
  ;;;          - a formula expressing that every object of the base sort is not in the range of the constructor
  ;;;            function
  ;;;          - the injectivity of the constructor function.
  ;;;          - a formula expressing that every object of a base sort or in the range of a constructor function
  ;;;            has a unique name
  
  (LET (COMPL.CODE INJECT.CODE SELECTOR.CODE UNIQUE.CODE PREV.CODE STRUCTURE.SCHEME STRUCTURE.SCHEME2)
    (SETQ COMPL.CODE (COM=COMPLETE.CODE STRUCTURE.SORT))
    (SETQ INJECT.CODE (MAPCAN #'(LAMBDA (CONSTR.FCT)
				  (COND ((DA-PREFUN.DOMAIN.SORTS CONSTR.FCT)
					 (SETQ STRUCTURE.SCHEME (COM=CREATE.STRUCTURE.SCHEME CONSTR.FCT))
					 (SETQ STRUCTURE.SCHEME2 (COM=CREATE.STRUCTURE.SCHEME CONSTR.FCT))
					 (SETQ PREV.CODE (DA-FORMULA.JUNCTION.CLOSURE
							  'AND (MAPCAR #'(LAMBDA (VAR1 VAR2)
									   (DA-LITERAL.CREATE '+ (DA-PREDICATE.EQUALITY)
											      (LIST (DA-TERM.COPY VAR1) (DA-TERM.COPY VAR2))))
								       (DA-TERM.TERMLIST STRUCTURE.SCHEME)
								(DA-TERM.TERMLIST STRUCTURE.SCHEME2))))
					 (LIST (DA-FORMULA.QUANTIFICATION.CLOSURE
						'ALL
						(APPEND (DA-GTERM.VARIABLES STRUCTURE.SCHEME) (DA-GTERM.VARIABLES STRUCTURE.SCHEME2))
						(DA-FORMULA.CREATE
						 'EQV
						 (LIST (DA-LITERAL.CREATE '+ (DA-PREDICATE.EQUALITY)
									  (LIST STRUCTURE.SCHEME STRUCTURE.SCHEME2)
								    (LIST 'KIND (LIST 'INJECTIVE)))
						       PREV.CODE)))))))
			      (DA-SORT.CONSTRUCTOR.FCTS STRUCTURE.SORT)))
    (SETQ SELECTOR.CODE (NCONC (COM=SELECTOR.CREATE.DEFINITION STRUCTURE.SORT)
			      (COM=INDEX.CREATE.DEFINITION STRUCTURE.SORT)))
   (SETQ UNIQUE.CODE (COM=UNIQUE.CODE (APPEND (DA-SORT.BASE.SORTS STRUCTURE.SORT) (DA-SORT.CONSTRUCTOR.FCTS STRUCTURE.SORT))))
   (VALUES 'STRUCTURE 
	    STRUCTURE.SORT 
	    (DA-FORMULA.JUNCTION.CLOSURE 'AND (NCONC (CONS COMPL.CODE INJECT.CODE) (NCONC SELECTOR.CODE UNIQUE.CODE))))))


(DEFUN COM=GENERATE.NON-FREE.CODE (STRUCTURE.SORT DEFINITION)

  ;;; Edited : NOV-92
  ;;; Value  : the code generated by the non-free-structure definition, i.e. a multiple value TYPE / NAME / RESULTS
  ;;;          where results is a list of lists representing
  ;;;          - a formula expressing that every object is of the base sort or is in the range of a constructor function
  ;;;          - a formula representing the definitions between WITH and END

 (LET (COMPL.CODE SELECTOR.CODE)
      (SETQ COMPL.CODE (COM=COMPLETE.CODE STRUCTURE.SORT))
      (SETQ  SELECTOR.CODE (COM=NON-FREE.SELECTOR.CODE STRUCTURE.SORT))
      (VALUES 'NON-FREE-STRUCTURE STRUCTURE.SORT
	      (CONS (LIST 'AXIOM "Completeness code" COMPL.CODE)
		    (CONS (LIST 'AXIOM "Selectors code" SELECTOR.CODE)
			  DEFINITION)))))


(DEFUN COM=NON-FREE.SELECTOR.CODE (STRUCTURE.SORT)

  (LET (VARS VAR)
    (DA-FORMULA.JUNCTION.CLOSURE 'AND
     (MAPCAN #'(LAMBDA (CONSTR SELECTORS)
		(COND (SELECTORS
		       (SETQ VARS (MAPCAR #'(LAMBDA (SORT) (DA-VARIABLE.CREATE SORT)) (DA-FUNCTION.DOMAIN.SORTS CONSTR)))
		       (SETQ VAR (DA-VARIABLE.CREATE STRUCTURE.SORT))
		       (LIST (DA-FORMULA.QUANTIFICATION.CLOSURE
			      'ALL (CONS VAR VARS)
			      (DA-FORMULA.IMPL.CLOSURE
			       (DA-LITERAL.CREATE '+ (DA-PREDICATE.EQUALITY)
						  (LIST (DA-TERM.CREATE VAR)
							(DA-TERM.CREATE CONSTR (MAPCAR #'(LAMBDA (VAR)
											   (DA-TERM.CREATE VAR NIL))
										       VARS))))
			       (DA-LITERAL.CREATE '+ (DA-PREDICATE.EQUALITY)
						  (LIST (DA-TERM.CREATE VAR)
							(DA-TERM.CREATE CONSTR (MAPCAR #'(LAMBDA (SEL)
									                   (DA-TERM.CREATE
											    SEL (LIST (DA-TERM.CREATE VAR))))
										       SELECTORS))))))))))
	    (DA-SORT.CONSTRUCTOR.FCTS STRUCTURE.SORT)
	    (DA-SORT.SELECTOR.FCTS STRUCTURE.SORT)))))



(DEFUN COM=COMPLETE.CODE (STRUCTURE.SORT)

  ;;; Value : a list representing the formula described first in COM=GENERATE.FREE.CODE
  
  (LET ((RANGE.VARIABLE (DA-VARIABLE.CREATE STRUCTURE.SORT)))
    (DA-FORMULA.QUANTIFICATION.CLOSURE 
	    'ALL (LIST RANGE.VARIABLE)
	    (DA-FORMULA.JUNCTION.CLOSURE
	      'OR (MAPCAR #'(LAMBDA (TERM)
 			      (DA-LITERAL.CREATE '+ (DA-PREDICATE.EQUALITY)
						  (LIST (DA-TERM.CREATE RANGE.VARIABLE) TERM) 
						  (LIST 'KIND (LIST 'COMPLETE))))
			  (DA-SORT.CREATE.ALL.STRUCTURE.TERMS (DA-TERM.CREATE RANGE.VARIABLE) NIL))))))


(DEFUN COM=UNIQUE.CODE (SORTS.AND.FCTS)

  ;;; Edited : NOV-92
  ;;; Input  : a list of all base sorts and constructor functions of a structure 
  ;;; Value  : the formula described last in COM=GENERATE.FREE.CODE
  
  (LET (TERM VAR RESULT VARLIST)
    (SETQ VARLIST (MAPCAR #'(LAMBDA (SORT.OR.FCT)
				    (COM=BASE.SORT.OR.CONSTR SORT.OR.FCT))
			  SORTS.AND.FCTS))  
    (MAPL #'(LAMBDA (VLIST)
	    (LET (PREV.CODE)
	      (MAPC #'(LAMBDA (TAIL)
			 (SETQ TERM (COND ((DA-GTERM.IS TAIL)
					   (COND ((SETQ VAR (DA-GTERM.VARIABLES TAIL))
			                          (LIST (DA-FORMULA.QUANTIFICATION.CLOSURE
				                            'ALL VAR
				                            (DA-LITERAL.CREATE (DA-SIGN.MINUS) (DA-PREDICATE.EQUALITY)
								               (LIST (CAR VLIST) TAIL)))))
						 (T (LIST (DA-LITERAL.CREATE (DA-SIGN.MINUS) (DA-PREDICATE.EQUALITY)
									     (LIST (CAR VLIST) TAIL))))))
				          (T (LIST (DA-LITERAL.CREATE (DA-SIGN.MINUS) (DA-PREDICATE.EQUALITY)
								      (LIST (CAR VLIST) (DA-GTERM.CREATE TAIL)))))))
			 (SETQ PREV.CODE (APPEND PREV.CODE TERM)))
		    (CDR VLIST))
	      (COND (PREV.CODE
	             (SETQ PREV.CODE (DA-FORMULA.JUNCTION.CLOSURE
			              'AND PREV.CODE))
	             (SETQ TERM (COND ((DA-GTERM.IS (CAR VLIST))
				       (COND ((SETQ VAR (DA-GTERM.VARIABLES (CAR VLIST)))
                                              (LIST (DA-FORMULA.QUANTIFICATION.CLOSURE
				                        'ALL VAR
				                        PREV.CODE)))
					      (T  (LIST PREV.CODE))))
				      (T (LIST (DA-FORMULA.QUANTIFICATION.CLOSURE
						  'ALL (LIST (CAR VLIST))
						  PREV.CODE)))))
		     (SETQ RESULT (APPEND RESULT TERM))))))
	  VARLIST)
     RESULT))


(DEFUN COM=BASE.SORT.OR.CONSTR (SORT.OR.CONSTR)

  ;;; Edited : nov-92
  ;;; Input  : a sort or a constructor function
  ;;; Value  : a variable of the type SORT if SORT.OR.CONSTR is a SORT
  ;;;          a term consisting of the function symbol and a matching variablelist if SORT.OR.CONSTR is a CONSTRUCTOR
  
  (COND ((DA-SORT.IS SORT.OR.CONSTR)
	 (DA-TERM.CREATE (DA-VARIABLE.CREATE SORT.OR.CONSTR)))
	((DA-FUNCTION.IS SORT.OR.CONSTR)
	 (COM=CREATE.STRUCTURE.SCHEME SORT.OR.CONSTR))))


(DEFUN COM=INDEX.CREATE.DEFINITION (SORT)
  
  ;;; Edited :  17-feb-89
  ;;; Effect :  generates representation axioms for INDEX.FCT 
  ;;; Value  :  a list of formulas denoting the definition of the index functions

  (MAPCAN #'(LAMBDA (INDEX.FCT)
	      (MAPCAR #'(LAMBDA (RIGHT.TERM)
			  (DA-FORMULA.QUANTIFICATION.CLOSURE
			    'ALL (DA-GTERM.VARIABLES RIGHT.TERM)
			    (DA-LITERAL.CREATE (DA-SIGN.PLUS)
					       (DA-PREDICATE.EQUALITY) 
					       (LIST (DA-TERM.CREATE INDEX.FCT (LIST RIGHT.TERM))
						     (COND ((EQ (DA-TERM.SORT RIGHT.TERM) (DA-FUNCTION.SORT INDEX.FCT))
							    RIGHT.TERM)
							   (T (DA-TERM.COPY (DA-SORT.EXCEPTION.VALUE
									     (DA-FUNCTION.SORT INDEX.FCT)))))))))
		      (DA-SORT.CREATE.ALL.STRUCTURE.TERMS.WITH.VAR SORT)))
	  (DA-SORT.INDEX.FCTS SORT)))


(DEFUN COM=SELECTOR.CREATE.DEFINITION (SORT)
  
  ;;; Edited :  21-feb-89 mp
  ;;; Effect :  generates representation axioms for Sort
  ;;; Value  :  a list of formula denoting the definitions of the selector functions.
  
  (LET (POS)
    (MAPCAN 
      #'(LAMBDA (SELECTORS CONSTRUCTOR)
	  (SETQ POS 0)
	  (MAPCAN
	    #'(LAMBDA (SELECTOR)
		(INCF POS)
		(MAPCAR #'(LAMBDA (RIGHT.TERM)
			    (DA-FORMULA.QUANTIFICATION.CLOSURE
			      'ALL (DA-GTERM.VARIABLES RIGHT.TERM)
			      (DA-LITERAL.CREATE (DA-SIGN.PLUS)
						 (DA-PREDICATE.EQUALITY)
						 (LIST (DA-TERM.CREATE SELECTOR (LIST RIGHT.TERM))			
						       (COND ((EQ (DA-TERM.SYMBOL RIGHT.TERM) CONSTRUCTOR)
							      (DA-TERM.COPY (NTH (1- POS) (DA-TERM.TERMLIST RIGHT.TERM))))
							     ((EQ SORT (DA-FUNCTION.SORT SELECTOR))
							      (DA-TERM.COPY RIGHT.TERM))
							     (T (DA-TERM.COPY (DA-SORT.EXCEPTION.VALUE
									       (DA-FUNCTION.SORT SELECTOR)))))))))
			(DA-SORT.CREATE.ALL.STRUCTURE.TERMS.WITH.VAR SORT)))
	    SELECTORS))
      (DA-SORT.SELECTOR.FCTS SORT) (DA-SORT.CONSTRUCTOR.FCTS SORT))))


(DEFUN COM=CREATE.STRUCTURE.SCHEME (CONSTR.FCT)
  
  ;;; Input:     CONSTR.FCT - a function symbol
  ;;; Effect
  ;;; Value:     a list (CONSTR.FCT VARIABLE.1 ... VARIABLE.N) where VARIABLE.I has the i-th domain sort
  ;;;            of CONSTR.FCT.
  
  (DA-TERM.CREATE CONSTR.FCT
		  (MAPCAR #'(LAMBDA (SORT) (DA-TERM.CREATE (DA-VARIABLE.CREATE SORT)))
			  (DA-FUNCTION.DOMAIN.SORTS CONSTR.FCT))))



;;;=====================================================
;;; MAPPINGS
;;;=====================================================


(DEFUN COM=2=MAPPING ()
  
  (LET (RESULT MAPPING)
    (COM=1=SYMBOL.ACCEPTED '("WITH"))
    (SETQ MAPPING (COM=2=MAPPING.TABLE))
    (LET ((COM*MAPPINGS (CONS MAPPING COM*MAPPINGS)))
      (COM=1=SYMBOL.ACCEPTED '("{"))
      (SETQ RESULT (COM=2=MAPPING.TAIL))
      (COM=1=SYMBOL.ACCEPTED '("}"))
      (VALUES 'MAPPING "Instantiation" RESULT))))


(DEFUN COM=2=MAPPING.TAIL ()

  (COND ((COM=1=SYMBOL.IS '("}")) NIL)
	(T (MULTIPLE-VALUE-BIND (TYPE NAME FORMULA) (COM=2=STATEMENT.1)
				(CONS (LIST TYPE NAME FORMULA)
				      (COM=2=MAPPING.TAIL))))))



(DEFUN COM=2=MAPPING.TABLE ()

  (COM=ITERATION.WITH.SEPARATOR #'COM=2=SINGLE.MAPPING '(",") nil))


(DEFUN COM=2=SINGLE.MAPPING (attr)

  (declare (ignore attr))
  (LET (ID1 ID2)
    (SETQ ID1 (COM=2=IDENTIFIER))
    (COM=1=SYMBOL.ACCEPTED '("="))
    (SETQ ID2 (COM=2=IDENTIFIER))
    (CONS ID1 ID2)))


;;;=====================================================
;;; Theorem Instantiations
;;;=====================================================

(defun com=2=lemma.instantiation ()
  ;;; effect : the rule <INSTANTIATION.LIST> -> "(" <INSTANTIATION>* ")"
  ;;; note:    <INSTANTIATION> are separated by comma
  ;;; value  : the denoted substitutioni
  
  (cond ((not (com=1=symbol.is '("(")))
	 (com=error 0 "lemma instantiation expected")))
  (com=2=lemma.instantiation.list))

(defun com=2=lemma.instantiation.list ()
  ;;; effect : the rule <INSTANTIATION.LIST> -> "(" <INSTANTIATION>* ")"
  ;;; note:    <INSTANTIATION> are separated by comma
  ;;; value  : the denoted substitutioni
  
  (LET (PARAMS variables terms subst)
      (COND ((AND (COM=1=SYMBOL.ACCEPTED '("("))
                  (SETQ PARAMS (APPLY #'NCONC (COM=ITERATION.WITH.SEPARATOR
					       #'COM=2=single.instantiation
					       '(","))))
		  (COM=1=SYMBOL.ACCEPTED '(")")))
	     (smaplist #'(lambda (paramlist)
			   (setq variables (cons (first paramlist) variables))
			   (setq terms (cons (second paramlist) terms)))
		       #'cddr
		       params)
	     (cond ((some #'(lambda (var term)
			      (cond ((not (da-variable.is (da-term.symbol var)))
				     (com=error 101 var))
				    ((> (list-length (da-symbol.occurs.in.gtermlist (da-term.symbol var) variables))
					1)
				     (com=error 102 var))
				    ((not (da-sort.is.subsort (da-term.sort term) (da-term.sort var)))
				     (com=error 103 term var))))
			  variables terms)))
	     (cond ((null (setq subst (uni-termlist.unify variables terms)))
		    (com=error 104)))
	     (car subst))
	    (T NIL))))


(defun com=2=single.instantiation ()
  ;;; effect : the rule <INSTANTIATION> -> <TERM> = <TERM>
  ;;; value  : a list containing the two terms
  
    (let (term1 term2)
    (setq term1 (com=2=term))
    (cond ((not (com=1=symbol.accepted '("=")))
	   (com=error 0 "= expected")))
    (setq term2 (com=2=term))
    (list term1 term2)))
  



;;;=====================================================
;;; INDUCTION SCHEMES
;;;=====================================================


(DEFUN COM=2=INDUCTION.SCHEME ()

  ;;; Effect:  <INDUCTION SCHEME> -> <SKOLEM.CONSTANT.LIST> = <INDUCTION BODY>
  ;;; Value:   the code generated by this rule , i.e. a multiple value parameters and
  ;;;          wfo-tree (encocded as definition)

  (LET (PARAMETER.LIST PARAM.SORTS BODY INSTANCE SYMBOL)
    (COND ((NOT (COM=1=SYMBOL.IS '("(")))
	   (COM=ERROR 0 "non-empty parameter list expected")))
    (SETQ PARAMETER.LIST (COM=2=PARAMETER.LIST))
    (SETQ SYMBOL (DA-FUNCTION.CREATE "DUMMY-REC" (DP-SORT.TOP.LEVEL.SORT)))
    (COND ((NOT (COM=1=SYMBOL.ACCEPTED '("=")))
	   (COM=ERROR 0 "equality-sign expected")))
    (SETQ PARAM.SORTS (MAPCAR #'(LAMBDA (TERM) (DA-VARIABLE.SORT TERM)) PARAMETER.LIST))
    (SETQ BODY (COM=2=INDUCTION.BODY PARAM.SORTS SYMBOL))
    (COND ((COM=1=SYMBOL.ACCEPTED '("WITH"))
	   (COM=1=SYMBOL.ACCEPTED '("("))
	   (SETQ INSTANCE (COM=2=TERMLIST))
	   (COM=1=SYMBOL.ACCEPTED '(")"))
	   (COND ((NOT (EQL (LENGTH INSTANCE) (LENGTH PARAMETER.LIST)))
		  (COM=ERROR 0 "invalid instantiation list")))
	   (SETF (DA-FUNCTION.DOMAIN.SORTS SYMBOL) (MAPCAR #'(LAMBDA (X) (DA-TERM.SORT X)) INSTANCE))
	   (VALUES PARAMETER.LIST BODY INSTANCE SYMBOL))
	  (T (COM=ERROR 0 "Instantiation of scheme missing")))))



(DEFUN COM=2=INDUCTION.BODY (PARAM.SORTS SYMBOL)

  ;;; Edited:  15-JAN-93
  ;;; Input:   a list of sort symbols
  ;;; Effect:  <INDUCTION BODY> -> <INDUCTION.PREDECESSORS> or { <INDUCTION.IF.CLAUSES> }*
  ;;; Value:   a list of codes generated by INDCUTION.PREDECESSORS, i.e. a list of DS-clause.def
  
  (LET (DEFINITION)
    (COND ((SETQ DEFINITION (COM=ITERATION.WITHOUT.SEPARATOR #'COM=2=INDUCTION.IF.CLAUSE '("IF") PARAM.SORTS SYMBOL))
	   (COND ((COM=1=SYMBOL.IS '("OTHERWISE"))
		  (SETQ DEFINITION (NCONC1 DEFINITION (COM=2=INDUCTION.IF.CLAUSE PARAM.SORTS SYMBOL)))))
	   (DA-GTERM.Definition.CREATE DEFINITION))
	  (T (DA-GTERM.DEF.VALUE.CREATE (COM=2=INDUCTION.PREDECESSORS PARAM.SORTS SYMBOL))))))


(DEFUN COM=2=INDUCTION.IF.CLAUSE (PARAM.SORTS SYMBOL)

  ;;; Edited:  18-JAN-93
  ;;; Effect:  <INDUCTION.IF.CLAUSE> -> IF <CONDITION> THEN
  ;;;                                    < INDUCTION.PREDECESSORS> | { <INDUCTION.IF.CLAUSE> }
  ;;; Value:   the code generated by this rule, i.e a list of local variables condition and value of
  ;;;          this if-clause.
  
  (LET (CONDITION TERM)
    (COND ((COM=1=SYMBOL.ACCEPTED '("IF"))
	   (SETQ CONDITION (COM=2=IF.CONJUNCTION NIL))
	   (COM=1=SYMBOL.ACCEPTED '("THEN")))
	  ((COM=1=SYMBOL.ACCEPTED '("OTHERWISE"))
	   (SETQ CONDITION 'OTHERWISE))
	  (T (COM=ERROR 0 "missing IF... THEN...")))
    (COND ((COM=1=SYMBOL.ACCEPTED '("{"))
	   (SETQ TERM (COM=2=INDUCTION.BODY PARAM.SORTS SYMBOL))
	   (COND ((NOT (COM=1=SYMBOL.ACCEPTED '("}")))
		  (COM=ERROR 0 "missing right bracket..."))))
	  (T (SETQ TERM (DA-GTERM.DEF.VALUE.CREATE (COM=2=INDUCTION.PREDECESSORS PARAM.SORTS SYMBOL)))))
    (DA-GTERM.DEF.CREATE TERM CONDITION)))


(DEFUN COM=2=INDUCTION.PREDECESSORS (SORTS SYMBOL)

  ;;; Input:   a list of sorts
  ;;; Effect:  < INDUCTION.PREDECESSORS > -> ? | < INDUCTION.PREDECESSOR >*

  (cond ((COM=1=SYMBOL.ACCEPTED '("?")) (DA-LITERAL.TRUE))
	(T (DA-FORMULA.JUNCTION.CLOSURE 'AND
					(COM=ITERATION.WITH.SEPARATOR #'COM=2=INDUCTION.PREDECESSOR '(",") SORTS SYMBOL)))))


(DEFUN COM=2=INDUCTION.PREDECESSOR (SORTS SYMBOL)

  (LET (PARAMS)
    (COND ((COM=1=SYMBOL.ACCEPTED '("("))
	   (SETQ PARAMS (COM=2=TERMLIST))
	   (COND ((AND (EQL (LENGTH PARAMS) (LENGTH SORTS))
		       (EVERY #'(LAMBDA (TERM SORT)
				  (DA-SORT.IS.SUBSORT (DA-TERM.SORT TERM) SORT))
			      PARAMS SORTS)
		       (COM=1=SYMBOL.ACCEPTED '(")")))
		  (DA-TERM.CREATE SYMBOL PARAMS))	 
		 (T (COM=ERROR 0 "invalid predecessor")))))))
		       


;;;=====================================================
;;; PREDICATES AND FUNCTIONS
;;;=====================================================



(DEFUN COM=2=ALGORITHMIC.FUNCTION.DEFINITION ()

  ;;; Edited:  18-JAN-93
  ;;; Effect:  <ALGORITHMIC FUNCTION DEFINITION> -> <ALGORITHMIC FUNCTION HEAD> = <ALGORITHMIC FUNCTION BODY>
  ;;; Value:   the code generated by this rule , i.e. a multiple value TYPE / NAME / RESULTS,
  ;;;          where RESULTS is a list of DEFINITIONS and DEFINITION is a quadrupel representing
  ;;;          the function definition as is used by EXP and REC.

  (LET (FUNCTION.SYMBOL PARAMETER.LIST RANGE.SORT F.SYMBOL BODY)
    (COM=1=SYMBOL.ACCEPTED '("A-FUNCTION" "FUNCTION"))
    (SETQ FUNCTION.SYMBOL (COM=2=IDENTIFIER.OR.NAME))
    (SETQ PARAMETER.LIST (COM=2=PARAMETER.LIST))
    (COND ((AND (COM=1=SYMBOL.ACCEPTED '(":"))
	        (SETQ RANGE.SORT (COM=2=SORT.SYMBOL)))
           (SETQ RANGE.SORT (COM=3=CHECK.OR.INTRODUCE.SORT RANGE.SORT NIL NIL
						       '(KNOWN.SYMBOL T)))
	   (IF (GETF (DA-SORT.ATTRIBUTES RANGE.SORT) 'HAS.INSTANCE) (COM=ERROR 83 RANGE.SORT)))
	  (T (COM=ERROR 0 "colon expected")))
    (SETQ F.SYMBOL (COM=3=INTRODUCE.SYMBOL FUNCTION.SYMBOL 'FUNCTION
			        (MAPCAR #'(LAMBDA (ENTRY) (DA-VARIABLE.SORT ENTRY))
				        PARAMETER.LIST)
			        RANGE.SORT (LIST 'DEFINED T)))
    (COND ((NOT (COM=1=SYMBOL.ACCEPTED '("=")))
	   (COM=ERROR 0 "equality-sign expected")))
    (SETQ BODY (COM=2=ALG.FUNCTION.BODY RANGE.SORT (LIST  'KNOWN.SYMBOL T)))  ; 'REC F.SYMBOL
    (COM=2=USE.LIST.INSERT (COM=2=CHECK.PREFUN.FOR.PARAMETER F.SYMBOL NIL) (LIST F.SYMBOL))
    (VALUES 'FUNCTION F.SYMBOL (LIST BODY F.SYMBOL PARAMETER.LIST))))



(DEFUN COM=2=PARAMETER.LIST ()

  ;;; Edited:  27-JUL-81 15:21:50
  ;;; Effect:  <PARAMETER LIST> -> ( { <VARIABLE DECLARATION> }* )
  ;;; Value:   the code generated by this rule, i.e. a list of code returned by <VARIABLE DECLARATION>
  ;;;          a list of variables.

    (LET (PARAMS)
      (COND ((AND (COM=1=SYMBOL.ACCEPTED '("("))
                  (SETQ PARAMS (APPLY #'NCONC (COM=ITERATION.WITH.SEPARATOR
					       #'COM=2=VARIABLE.DECLARATION
					       '(","))))
		  (COM=1=SYMBOL.ACCEPTED '(")")))
	      PARAMS)
	    (T NIL))))


(DEFUN COM=2=VARIABLE.DECLARATION (&OPTIONAL ATTRIBUTES)

  ;;; Edited:  27-JUL-81 15:24:42
  ;;; Input:   ATTRIBUTES - A LIST OF ATOMS 
  ;;; Effect:  <VARIABLE DECLARATION> -> <IDENTIFIERLIST> <VARIABLE TYPE>,
  ;;;          for each identifier in the list a DT-variable is created and entered into the list of
  ;;;          all variables.
  ;;; Value:   the code generated by this rule, i.e. a list of DT-variables.
  
  (LET (IDENTIFIER.LIST VAR.SORT VAR)
    (SETQ IDENTIFIER.LIST (COM=2=IDENTIFIER.LIST))
    (SETQ VAR.SORT (COM=3=CHECK.OR.INTRODUCE.SORT (COM=2=VARIABLE.TYPE) NIL NIL))
    (COND ((AND ATTRIBUTES
	        (NOT (MEMBER 'LEMMA ATTRIBUTES))
                (GETF (DA-SORT.ATTRIBUTES VAR.SORT) 'HAS.INSTANCE))
	   (COM=ERROR 83 VAR.SORT)))
    (MAPCAR #'(LAMBDA (IDENTIFIER)
		    (SETQ VAR (DA-VARIABLE.CREATE VAR.SORT IDENTIFIER))
		    (SETQ COM*ALL.VARIABLES (ACONS IDENTIFIER VAR COM*ALL.VARIABLES))
		    VAR)
	 IDENTIFIER.LIST)))


(DEFUN COM=2=VARIABLE.TYPE ()
  
  ;;; Edited:  8-SEP-81 12:46:50
  ;;; Effect:  <VARIABLE TYPE> -> () or : <SORT.SYMBOL>
  ;;; Value:   the code generated by this rule, i.e an atom which denotes a type symbol.
  
  (COND ((COM=1=SYMBOL.ACCEPTED '(":"))
	 (COM=2=SORT.SYMBOL))
	(T (COM=ERROR 0 "missing sort"))))


(DEFUN COM=2=ALG.FUNCTION.BODY (RANGE.SORT &OPTIONAL ATTRIBUTES)

  ;;; Edited:  15-JAN-93
  ;;; Input:   RANGE.SORT of a function and optional a list of ATTRIBUTES
  ;;; Effect:  <ALGORITHMIC FUNCTION BODY> -> TERM or { <FUNCTION.IF.CLAUSES> }*
  ;;; Value:   a list of codes generated by <FUNCTION IF CLAUSE>, i.e. a list of DS-clause.def
  
  (LET (DEFINITION TERM)
    (COND ((SETQ DEFINITION (COM=ITERATION.WITHOUT.SEPARATOR #'COM=2=FUNCTION.IF.CLAUSE '("IF") RANGE.SORT 
							     ATTRIBUTES))
	   (COND ((COM=1=SYMBOL.IS '("OTHERWISE"))
		  (SETQ DEFINITION (NCONC1 DEFINITION (COM=2=FUNCTION.IF.CLAUSE RANGE.SORT ATTRIBUTES)))))
	   (DA-GTERM.DEFINITION.CREATE DEFINITION))
	  (T (SETQ TERM (COM=2=TERM ATTRIBUTES))
	     (COND ((EQL (DA-TERM.SORT TERM) RANGE.SORT)
	            (DA-GTERM.DEF.VALUE.CREATE TERM))
		   (T (COM=ERROR 27 (DA-TERM.SYMBOL TERM) (DA-TERM.SORT TERM) RANGE.SORT)))))))

 
(DEFUN COM=2=FUNCTION.IF.CLAUSE (RANGE.SORT &OPTIONAL ATTRIBUTES)

  ;;; Edited:  18-JAN-93
  ;;; Effect:  <FUNCTION IF CLAUSE> -> IF <CONDITION> THEN ( <TERM> or { <FUNCTION.IF.CLAUSES> }* or "?")
  ;;; Value:   the code generated by this rule, i.e a list of local variables condition and value of
  ;;;          this if-clause.
  
  (LET (CONDITION TERM)
       (COND ((COM=1=SYMBOL.ACCEPTED '("IF"))
	      (SETQ CONDITION (COM=2=IF.CONJUNCTION ATTRIBUTES))
	      (COM=1=SYMBOL.ACCEPTED '("THEN")))
	     ((COM=1=SYMBOL.ACCEPTED '("OTHERWISE"))
	      (SETQ CONDITION 'OTHERWISE))
	     (T (COM=ERROR 0 "missing IF... THEN...")))
       (COND ((COM=1=SYMBOL.ACCEPTED '("{"))
	      (SETQ TERM (COM=2=ALG.FUNCTION.BODY RANGE.SORT ATTRIBUTES))
	      (COND ((NOT (COM=1=SYMBOL.ACCEPTED '("}")))
		     (COM=ERROR 0 "missing right bracket..."))))
	     ((COM=1=SYMBOL.ACCEPTED '("?"))
	      (SETQ TERM (DA-TERM.CREATE 'UNSPEC NIL)))
	     (T (SETQ TERM (COM=2=TERM '(CONSTRUCTIVE.SYMBOL T KNOWN.SYMBOL T)))
                (COND ((DA-SORT.IS.SUBSORT (DA-TERM.SORT TERM) RANGE.SORT)
		       (DA-GTERM.DEF.VALUE.CREATE TERM))
		      (T (COM=ERROR 27 (DA-TERM.SYMBOL TERM) (DA-FUNCTION.DOMAIN.SORTS (DA-TERM.SYMBOL TERM))
				       (DA-TERM.SORT TERM) RANGE.SORT)))))
       (DA-GTERM.DEF.CREATE TERM CONDITION)))


(DEFUN COM=2=IF.CONJUNCTION (&OPTIONAL ATTRIBUTES)
  
  ;;; EDITED:  9-JUL-81 11:03:29
  ;;; EFFECT:  <IF CONJUNCTION> -> <LITERAL> {LITERAL}*
  ;;; VALUE:   A LIST OF CODES GENERATED BY THE LITERAL RULE 
  
  (COM=ITERATION.WITH.SEPARATOR #'COM=2=LITERAL '("AND") ATTRIBUTES))


(DEFUN COM=2=LITERAL (&OPTIONAL ATTRIBUTES)
  
  ;;; Edited:  1-MAR-82 12:44:48
  ;;; Effect:  <LITERAL> -> NOT <ATOM> or <ATOM>
  ;;; Value:   the code generated by this rule , i.e. a FOR-LITERAL 
  
    (COND ((COM=1=SYMBOL.ACCEPTED '("NOT"))
	   (COND ((COM=1=SYMBOL.ACCEPTED '("("))
		  (LET ((RESULT (COM=2=ATOM ATTRIBUTES)))
		    (COND ((COM=1=SYMBOL.ACCEPTED '(")"))
			   RESULT)
			  (T (COM=ERROR 0 "Missing right bracket")))))
		 (T (COM=2=ATOM ATTRIBUTES))))
	  (T (DA-LITERAL.NEGATE (COM=2=ATOM ATTRIBUTES)))))


(DEFUN COM=2=DECLARATIVE.FUNCTION.DEFINITION ()

  ;;; Edited : 18-JAN-93
  ;;; Effect : <DECLARATIVE.FUNCTION DEFINITION> -> <DECALRATIVE FUNCTION HEAD> <DECLARATIVE FUNCTION BODY>
  ;;; Value  : the code generated by this rule
  
  (LET (FUNCTION.SYMBOL PARAMETER.LIST RANGE.SORT F.SYMBOL BODY LEFT)
    (COM=1=SYMBOL.ACCEPTED '("D-FUNCTION"))
    (SETQ FUNCTION.SYMBOL (COM=2=IDENTIFIER.OR.NAME))
    (SETQ PARAMETER.LIST (COM=2=SHORT.PARAMETER.LIST))
    (COND ((AND (COM=1=SYMBOL.ACCEPTED '(":"))
	        (SETQ RANGE.SORT (COM=2=SORT.SYMBOL)))
           (SETQ RANGE.SORT (COM=3=CHECK.OR.INTRODUCE.SORT RANGE.SORT NIL NIL
						           '(KNOWN.SYMBOL T CONSTRUCTIVE.SYMBOL T)))
	   (IF (GETF (DA-SORT.ATTRIBUTES RANGE.SORT) 'HAS.INSTANCE) (COM=ERROR 83 RANGE.SORT)))
	  (T (COM=ERROR 0 "colon expected")))
    (SETQ F.SYMBOL (COM=3=INTRODUCE.SYMBOL FUNCTION.SYMBOL 'FUNCTION PARAMETER.LIST
			                   RANGE.SORT (LIST 'DECLARED T)))
    (COND ((SETQ LEFT (COM=2=LEFT.BRACKET))
           (IF (NOT (SETQ BODY (COM=2=DECL.FUNCTION.BODY))) (COM=ERROR 0 "missing definition between WITH and END"))
           (COM=2=RIGHT.BRACKET LEFT)))
    (COM=2=USE.LIST.INSERT (COM=2=CHECK.PREFUN.FOR.PARAMETER F.SYMBOL NIL) (LIST F.SYMBOL))
    (VALUES 'DECL.FUNCTION  F.SYMBOL BODY)))


(DEFUN COM=2=SHORT.PARAMETER.LIST ()

  ;;; Edited : MAY-93
  ;;; Effect : <SHORT PARAMETER LIST> -> ( { <datatype_identifier ','> }* )
  ;;; Value  : the code generated by this rule

  (LET (IDENTIFIER.LIST )
    (COND ((COM=1=SYMBOL.ACCEPTED '("("))
           (SETQ IDENTIFIER.LIST (COM=2=IDENTIFIER.LIST))
	   (COND ((NOT (COM=1=SYMBOL.ACCEPTED '(")")))
		  (COM=ERROR 0 "missing right bracket")))
	   (MAPCAR #'(LAMBDA (IDENT)
		       (LET (SORT)
		         (SETQ SORT (COM=3=CHECK.OR.INTRODUCE.SORT IDENT NIL NIL NIL))
			 (IF (GETF (DA-SORT.ATTRIBUTES SORT) 'HAS.INSTANCE) (COM=ERROR 83 SORT))
			 SORT))
		   IDENTIFIER.LIST))
	  (T NIL))))


(DEFUN COM=2=DECL.FUNCTION.BODY ()

  ;;; Edited : 15-JAN-93
  ;;; Effect : <DECLARATIVE FUNCTION BODY> -> WITH { AXIOM }+ END
  ;;; Value  : a list of DS-Axiom definitions
  
  (LET (DEFINITION)
       (COND ((SETQ DEFINITION (COM=ITERATION.WITHOUT.SEPARATOR #'COM=2=DECL.FUNCTION '("AXIOM")))
	      (DA-FORMULA.JUNCTION.CLOSURE 'AND DEFINITION)))))


(DEFUN COM=2=DECL.FUNCTION ()
  (COM=1=SYMBOL.ACCEPTED '("AXIOM"))
  (COM=2=QUANTIFICATION))


(DEFUN COM=2=ALGORITHMIC.PREDICATE.DEFINITION ()

  ;;; Edited:  19-JAN-93
  ;;; Effect:  <ALGORITHMIC PREDICATE DEFINITION> -> <ALGORITHMIC PREDICATE HEAD> = <ALGORITHMIC PREDICATE BODY> 
  ;;; Value:   the code generated by this rule , i.e. a multiple value NAME RESULTS,
  ;;;          where RESULTS is a list of list of the form TYPE.DEFINITION and
  ;;;          DEFINITION is a quadrupel representing the predicate definition as is used by EXP and REC.

  (LET (PREDICATE.SYMBOL PARAMETER.LIST P.SYMBOL BODY)
    (COM=1=SYMBOL.ACCEPTED '("A-PREDICATE" "PREDICATE"))
    (SETQ PREDICATE.SYMBOL (COM=2=IDENTIFIER.OR.NAME))
    (SETQ PARAMETER.LIST (COM=2=PARAMETER.LIST))    
    (SETQ P.SYMBOL (COM=3=CHECK.OR.INTRODUCE.SYMBOL PREDICATE.SYMBOL 'PREDICATE
			         (MAPCAR #'(LAMBDA (ENTRY) (DA-VARIABLE.SORT ENTRY))
				         PARAMETER.LIST) NIL (LIST 'DEFINED T)))
    (IF (NOT (COM=1=SYMBOL.ACCEPTED '("=")))
	(COM=ERROR 0 "equality-sign expected"))
    (SETQ BODY (COM=2=ALG.PREDICATE.BODY (LIST 'KNOWN.SYMBOL T)))  ;; 'REC P.SYMBOL 
    (COM=2=USE.LIST.INSERT (COM=2=CHECK.PREFUN.FOR.PARAMETER P.SYMBOL NIL) (LIST P.SYMBOL))
    (VALUES 'PREDICATE P.SYMBOL (LIST BODY P.SYMBOL PARAMETER.LIST))))


(DEFUN COM=2=ALG.PREDICATE.BODY (&OPTIONAL ATTRIBUTES)

  ;;; Edited:  15-JAN-93
  ;;; Input:   a list of ATTRIBUTES
  ;;; Effect:  <ALGORITHMIC PREDICATE BODY> -> FORMULA or { <PREDICATE.IF.CLAUSES> }*
  ;;; Value:   a list of codes generated by <PREDICATE IF CLAUSE>, i.e. a list of DS-clause.def
  
  (LET (DEFINITION)
    (COND ((SETQ DEFINITION (COM=ITERATION.WITHOUT.SEPARATOR #'COM=2=PREDICATE.IF.CLAUSE '("IF") ATTRIBUTES))
	   (COND ((COM=1=SYMBOL.IS '("OTHERWISE"))
		  (SETQ DEFINITION (NCONC1 DEFINITION (COM=2=PREDICATE.IF.CLAUSE ATTRIBUTES)))))
	   (DA-GTERM.DEFINITION.CREATE DEFINITION))
	  (T (DA-GTERM.DEF.VALUE.CREATE (COM=2=QUANTIFICATION ATTRIBUTES))))))


(DEFUN COM=2=PREDICATE.IF.CLAUSE (&OPTIONAL ATTRIBUTES)

  ;;; Edited:  19-JAN-93
  ;;; Effect:  <PREDICATE IF CLAUSE> -> IF <CONDITION> THEN ( <FORMULA> or { <PREDICATE.IF.CLAUSES> }* or "?")
  ;;; Value:   the code generated by this rule, i.e a list of local variables condition and value of
  ;;;          this if-clause. 
  
  (LET (CONDITION FORMULA)
       (COND ((COM=1=SYMBOL.ACCEPTED '("IF"))
	      (SETQ CONDITION (COM=2=IF.CONJUNCTION ATTRIBUTES))
	      (COM=1=SYMBOL.ACCEPTED '("THEN")))
	     ((COM=1=SYMBOL.ACCEPTED '("OTHERWISE"))
	      (SETQ CONDITION 'OTHERWISE))
	     (T (COM=ERROR 0 "missing IF... THEN...")))
       (COND ((COM=1=SYMBOL.ACCEPTED '("{"))
	      (SETQ FORMULA (COM=2=ALG.PREDICATE.BODY ATTRIBUTES))
	      (COND ((NOT (COM=1=SYMBOL.ACCEPTED '("}")))
		     (COM=ERROR 0 "missing right bracket..."))))
	     ((COM=1=SYMBOL.IS '("?"))
	      (SETQ FORMULA (DA-GTERM.CREATE 'UNSPEC NIL)))
	     (T (SETQ FORMULA (DA-GTERM.DEF.VALUE.CREATE (COM=2=QUANTIFICATION '(CONSTRUCTIVE.SYMBOL KNOWN.SYMBOL))))))
       (DA-GTERM.DEF.CREATE FORMULA CONDITION)))


(DEFUN COM=2=DECLARATIVE.PREDICATE.DEFINITION ()

  ;;; Edited : 19-JAN-93
  ;;; Effect : <DECLARATIVE PREDICATE DEFINITION> -> <DECLARATIVE PREDICATE HEAD> <DECLARATIVE PREDICATE BODY>
  ;;; Value  : see Effect
  
  (LET (PREDICATE.SYMBOL PARAMETER.LIST P.SYMBOL BODY LEFT)
    (COM=1=SYMBOL.ACCEPTED '("D-PREDICATE"))
    (SETQ PREDICATE.SYMBOL (COM=2=IDENTIFIER.OR.NAME))
    (SETQ PARAMETER.LIST (COM=2=SHORT.PARAMETER.LIST))
    (SETQ P.SYMBOL (COM=3=INTRODUCE.SYMBOL PREDICATE.SYMBOL 'PREDICATE PARAMETER.LIST NIL
					   (LIST 'DECLARED T)))
    (COND ((SETQ LEFT (COM=2=LEFT.BRACKET))
           (IF (NOT (SETQ BODY (COM=2=DECL.PREDICATE.BODY))) (COM=ERROR 0 "missing definition between WITH AND end"))
           (COM=2=RIGHT.BRACKET LEFT)))
    (COM=2=USE.LIST.INSERT (COM=2=CHECK.PREFUN.FOR.PARAMETER P.SYMBOL NIL) (LIST P.SYMBOL))
    (VALUES 'DECL.PREDICATE P.SYMBOL BODY)))


(DEFUN COM=2=DECL.PREDICATE.BODY ()

  ;;; Edited : 19-JAN-93
  ;;; Effect : <DECLARATIVE PREDICATE BODY> -> WITH { AXIOM }+ END
  ;;; Value  : a list of DS-Axiom definitions
  
  (LET (DEFINITION)
       (COND ((SETQ DEFINITION (COM=ITERATION.WITHOUT.SEPARATOR #'COM=2=DECL.PREDICATE '("AXIOM")))
	      (DA-FORMULA.JUNCTION.CLOSURE 'AND DEFINITION)))))


(DEFUN COM=2=DECL.PREDICATE ()
  (COM=1=SYMBOL.ACCEPTED '("AXIOM"))
  (COM=2=QUANTIFICATION))



(DEFUN COM=2=ATOM (&OPTIONAL ATTRIBUTES)
  
  ;;; Edited:  6-MAR-81 14:14:51
  ;;; Input:   ATTRIBUTES - a list of atoms
  ;;; Effect:  <ATOM> -> <predicate.symbol> ( <TERMLIST> ) or <TERM> = <TERM>
  ;;; Value:   a FOR-LITERAL
  
  (LET (IDENTIFIER SYMBOL TERMLIST TYPE DOMAIN)
    (COND ((COM=1=SYMBOL.IS '("IDENTIFIER" "NAME"))
	   (SETQ IDENTIFIER (COM=2=IDENTIFIER.OR.NAME))
	   (COND ((COM=1=SYMBOL.ACCEPTED '("("))
		  (SETQ TERMLIST (COM=2=TERMLIST ATTRIBUTES))
		  (SETQ DOMAIN (MAPCAR #'(LAMBDA (FOO)
						 (DA-TERM.SORT FOO))
				       TERMLIST))
                  (IF (NULL (SETQ SYMBOL (COM=5=NAME.OBJECT IDENTIFIER DOMAIN '(PREDICATE FUNCTION))))
		      (COM=ERROR 28 IDENTIFIER DOMAIN))
		  (COND ((AND SYMBOL (NOT (MEMBER (COM=TYPE SYMBOL) '(PREDICATE FUNCTION))))
			 (COM=ERROR 2 (COM=TYPE SYMBOL) IDENTIFIER "function rsp. predicate")))
		  (COND ((NOT (COM=1=SYMBOL.ACCEPTED '(")"))) (COM=ERROR 0 "Missing right bracket"))))
		 ((NULL (SETQ SYMBOL (COM=5=NAME.OBJECT IDENTIFIER DOMAIN '(PREDICATE FUNCTION))))
		  (COM=ERROR 6 IDENTIFIER))))
	  ((COM=1=SYMBOL.IS '("NUMBER"))
	   (SETQ IDENTIFIER (COM=2=NUMBER))
	   (SETQ SYMBOL (COM=5=NAME.OBJECT IDENTIFIER NIL '(PREDICATE FUNCTION)))
	   (COND ((AND SYMBOL (OR (NOT (DA-FUNCTION.IS SYMBOL)) (DA-FUNCTION.DOMAIN.SORTS SYMBOL)))
		  (COM=ERROR 2 "constant" IDENTIFIER "function rsp. predicate"))))
	  (T (COM=ERROR 0 "Identifier, name or number expected")))
    (COND ((COM=1=SYMBOL.ACCEPTED '("="))
	   (IF (NOT SYMBOL) (SETQ SYMBOL (COM=5=NAME.OBJECT IDENTIFIER NIL '(FUNCTION))))
	   (COND ((AND SYMBOL (NOT (OR (DA-VARIABLE.IS SYMBOL) (DA-FUNCTION.IS SYMBOL))))
		  (COM=ERROR 2 (COM=TYPE SYMBOL) IDENTIFIER "variable, constant rsp. function")))
	   (SETQ SYMBOL (COM=3=CHECK.OR.INTRODUCE.SYMBOL IDENTIFIER
							 (COND ((AND SYMBOL (DA-VARIABLE.IS SYMBOL))
								'VARIABLE) 
							       (T 'FUNCTION))
							 (MAPCAR #'(LAMBDA (X) (DA-TERM.SORT X)) TERMLIST)
							 (DP-SORT.TOP.LEVEL.SORT) NIL ATTRIBUTES))
	   (DA-LITERAL.CREATE '+  (DA-PREDICATE.EQUALITY)
			       (LIST (DA-TERM.CREATE SYMBOL TERMLIST)
				     (COM=2=TERM ATTRIBUTES))))
	  ((COM=1=SYMBOL.ACCEPTED '("OF"))
	   (IF (NOT SYMBOL) (SETQ SYMBOL (COM=5=NAME.OBJECT IDENTIFIER NIL '(FUNCTION))))
	   (COND ((AND SYMBOL (NOT (OR (DA-VARIABLE.IS SYMBOL) (DA-FUNCTION.IS SYMBOL))))
		  (COM=ERROR 2 (COM=TYPE SYMBOL) IDENTIFIER "variable, constant rsp. function")))
	   (SETQ SYMBOL (COM=3=CHECK.SYMBOL IDENTIFIER (COND ((AND SYMBOL (DA-VARIABLE.IS SYMBOL))
							      'VARIABLE) 
							     (T 'FUNCTION))
							 (MAPCAR #'(LAMBDA (X) (DA-TERM.SORT X)) TERMLIST)
							 (DP-SORT.TOP.LEVEL.SORT) ATTRIBUTES))
	   (SETQ TYPE (COM=2=OF.TAIL (DA-SYMBOL.SORT SYMBOL)))
	   (DA-LITERAL.CREATE '+ (DA-PREDICATE.EQUALITY)
			      (LIST (DA-TERM.CREATE SYMBOL TERMLIST)
				    (CASE (DA-TYPE TYPE)
					  (DA*FUNCTION (DA-SORT.CONSTRUCTOR.TERM (DA-TERM.CREATE SYMBOL TERMLIST)
										 TYPE))
					  (DA*SORT (DA-SORT.INDEX.TERM (DA-TERM.CREATE SYMBOL TERMLIST) TYPE))))
			      '(KIND (MATCH))))
	  (T (COND ((AND SYMBOL (NOT (DA-PREDICATE.IS SYMBOL)))
		    (COM=ERROR 2 (COM=TYPE SYMBOL) IDENTIFIER "predicate")))
	     (SETQ SYMBOL (COM=3=CHECK.OR.INTRODUCE.SYMBOL IDENTIFIER 'PREDICATE
							   (MAPCAR #'(LAMBDA (X) (DA-TERM.SORT X)) TERMLIST)
							   NIL nil
							   ATTRIBUTES))
	     (DA-LITERAL.CREATE '+ SYMBOL TERMLIST)))))


(DEFUN COM=2=OF.TAIL (SORT)
  (LET* ((IDENTIFIER (COND ((COM=1=SYMBOL.IS '("IDENTIFIER" "NAME")) (COM=2=IDENTIFIER.OR.NAME))
			   (T (COM=2=NUMBER))))
	 (OBJECT (COM=5=NAME.OBJECT IDENTIFIER 'UNSPEC '(FUNCTION SORT))))
       (CASE (COM=TYPE OBJECT)
	     (FUNCTION (COM=3=CHECK.SYMBOL IDENTIFIER 'FUNCTION 'UNSPEC SORT `(LIST STRUCTURE)))
	     (SORT (COM=3=CHECK.SORT OBJECT NIL (LIST 'BASE.SORT SORT)))
	     (OTHERWISE (COM=ERROR 11 IDENTIFIER)))))


(DEFUN COM=2=TERMLIST (&OPTIONAL ATTRIBUTES)

  ;;; Edited:  6-MAR-81 16:33:12
  ;;; Input:   ATTRIBUTES - a list of atoms
  ;;; Effect:  <TERMLIST> -> {TERM}*
  ;;; Value:   a list of terms generated by COM=2=TERM

  (COM=ITERATION.WITH.SEPARATOR #'COM=2=TERM '(",") ATTRIBUTES))


(DEFUN COM=2=TERM (&OPTIONAL ATTRIBUTES)
  
  ;;; Edited:  9-MAR-81 16:28:53
  ;;; Input:   ATTRIBUTES - a list of atoms.
  ;;; Effect:  <TERM> -> <IDENTIFIER> or <IDENTIFIER> ( <TERMLIST> ) or <NUMBER> or <TERM> OP <TERM> 
  ;;; Value:   the code of the denoted term.
  
  (LET (IDENTIFIER SYMBOL TERMLIST TERM1 TERM2 VAR DOMAIN)
    (COND ((COM=1=SYMBOL.ACCEPTED '("("))
           (SETQ TERM1 (COM=2=TERM))
	   (SETQ IDENTIFIER (COM=2=IDENTIFIER.OR.NAME))
	   (SETQ TERM2 (COM=2=TERM))
	   (SETQ DOMAIN (LIST (DA-TERM.SORT TERM1) (DA-TERM.SORT TERM2)))
	   (SETQ SYMBOL (COM=5=NAME.OBJECT IDENTIFIER DOMAIN '(FUNCTION)))
	   (COND ((COM=1=SYMBOL.ACCEPTED '(")"))
		  (DA-TERM.CREATE SYMBOL (LIST TERM1 TERM2)))
		 (T (COM=ERROR 0 "Missing right bracket"))))
	  ((COM=1=SYMBOL.IS '("IDENTIFIER" "NAME"))
	   (SETQ IDENTIFIER (COM=2=IDENTIFIER.OR.NAME))
	   (COND ((SETQ VAR (COM=3=VSTACK.NEWNAME IDENTIFIER))
		  (DA-TERM.CREATE VAR))
	         ((COM=1=SYMBOL.ACCEPTED '("("))
                  (SETQ TERMLIST (COM=2=TERMLIST ATTRIBUTES))
		  (SETQ DOMAIN (MAPCAR #'(LAMBDA (FOO)
					   (DA-TERM.SORT FOO))
				       TERMLIST))
		  (COND ((NULL (SETQ SYMBOL (COM=5=NAME.OBJECT IDENTIFIER DOMAIN '(FUNCTION))))
			 (COM=ERROR 28 IDENTIFIER DOMAIN)))
		  (COND ((AND SYMBOL (NEQ (COM=TYPE SYMBOL) 'FUNCTION))
			 (COM=ERROR 2 (COM=TYPE SYMBOL) IDENTIFIER "function")))
		  (COND ((NULL TERMLIST) (COM=ERROR 0 "Identifier expected")))
		  (COND ((NOT (COM=1=SYMBOL.ACCEPTED '(")"))) (COM=ERROR 0 "Missing right bracket")))
		  (DA-TERM.CREATE SYMBOL TERMLIST))
		 (T (SETQ SYMBOL (COM=5=NAME.OBJECT IDENTIFIER NIL '(FUNCTION)))
		    (IF (NOT SYMBOL) (COM=ERROR 4 'FUNCTION IDENTIFIER))
		    (COND ((AND SYMBOL (NOT (DA-FUNCTION.IS SYMBOL)))
			   (COM=ERROR 2 (COM=TYPE SYMBOL) IDENTIFIER "A constant")))
		    (DA-TERM.CREATE SYMBOL))))
	  ((COM=1=SYMBOL.IS '("NUMBER"))
	   (SETQ IDENTIFIER (COM=2=NUMBER))
	   (SETQ SYMBOL (COM=5=NAME.OBJECT IDENTIFIER NIL '(FUNCTION)))   	   
	   (IF (NOT SYMBOL) (COM=ERROR 4 'FUNCTION IDENTIFIER))
	   (COND ((AND SYMBOL (NOT (DA-FUNCTION.IS SYMBOL)))
		  (COM=ERROR 2 (COM=TYPE SYMBOL) IDENTIFIER "constant")))
	   (DA-TERM.CREATE SYMBOL))
	  (T (COM=ERROR 0 "Identifier, name or number expected")))))


(DEFUN COM=2=IDENTIFIER.LIST ()
  
  ;;; Edited:  24-JUL-81 16:17:28
  ;;; Effect:  <IDENTIFIER LIST> -> <IDENTIFIER> { , <IDENTIFIER> }*
  ;;; Value:   the code generated by this rule, i.e  a list of code generated by <IDENTIFIER>
  
  (COM=ITERATION.WITH.SEPARATOR #'COM=2=IDENTIFIER '(",")))


(DEFUN COM=2=CONSTANT.LIST ()

  ;;; Effect:  <CONSTANT LIST> -> <CONSTANT> { , <CONSTANT> }*
  ;;; Value:   the code generated by this rule, i.e.  a list of code generated by <CONSTANT>

  (COM=ITERATION.WITH.SEPARATOR #'COM=2=CONSTANT '(",")))


(DEFUN COM=2=CONSTANT ()

  ;;; Edited:  1-OCT-81 15:57:51
  ;;; Effect:  <CONSTANT> -> <NAME> | <NUMBER> | <IDENTIFIER>
  ;;; Value:   The accepted string.
  
  (COND ((COM=1=SYMBOL.IS '("NUMBER"))
	 (COM=2=NUMBER))
	((COM=1=SYMBOL.IS '("NAME"))
	 (COM=2=NAME))
	((COM=1=SYMBOL.IS '("IDENTIFIER"))
	 (COM=2=IDENTIFIER))
	(T (COM=ERROR 0 "identifier, name or number expected"))))


(DEFUN COM=2=IDENTIFIER.OR.NAME ()

  ;;; Edited:  1-OCT-81 15:59:21
  ;;; Effect:  <IDENTIFIER OR NAME> -> <IDENTIFIER> or <NAME>
  ;;; Value:   The accepted string.

  (COND ((COM=1=SYMBOL.IS '("IDENTIFIER"))
	 (COM=2=IDENTIFIER))
	((COM=1=SYMBOL.IS '("NAME"))
	 (COM=2=NAME))
	(T (COM=ERROR 0 "identifier or name expected"))))


(DEFUN COM=2=IDENTIFIER ()

  ;;; EDITED:  17-JUL-81 11:38:08
  ;;; EFFECT:  <IDENTIFIER> -> ...
  ;;; Value:   The accepted string.
  
  (LET ((IDENTIFIER COM*SYMBOL))
    (COND ((COM=1=SYMBOL.ACCEPTED '("IDENTIFIER"))
	   (CDR IDENTIFIER))
	  (T (COM=ERROR 0 "identifier expected")))))


(DEFUN COM=2=NUMBER ()
  
  ;;; Edited:  6-MAR-81 11:29:21
  ;;; Effect:  <NUMBER> -> ...
  ;;; Value:   the accepted string.
  
  (COND ((COM=1=SYMBOL.IS '("NUMBER"))
	 (PROG1 (CDR com*SYMBOL) (COM=1=SYMBOL.ACCEPTED '("NUMBER"))))
	(T (COM=ERROR 0 "number expected"))))


(DEFUN COM=2=NAME ()

  ;;; Edited:  5-MAR-81 12:11:57
  ;;; Effect:  (NAME) -> ...
  ;;; Value:   the accepted string.

  (COND ((COM=1=SYMBOL.IS '("NAME"))
	 (PROG1 (CDR COM*SYMBOL) (COM=1=SYMBOL.ACCEPTED '("NAME"))))
	(T (COM=ERROR 0 "name expected"))))


(DEFUN COM=2=STRING ()

  ;;; Edited : 22-JAN-93
  ;;; Effect : <STRING> -> ...
  ;;; Value  : the accepted string

  (LET ((STRING COM*SYMBOL))
  (COND ((COM=1=SYMBOL.ACCEPTED '("STRING"))
	 (CDR STRING))
	(T (COM=ERROR 0 "String expected")))))


(DEFUN COM=2=LEFT.BRACKET ()

  ;;; Edited : JUNE-93
  ;;; Value  : LEFT.BRACKET -> WITH or {

  (COND ((COM=1=SYMBOL.ACCEPTED '("WITH"))
	 'WITH)
	((COM=1=SYMBOL.ACCEPTED '("{"))
	 '{)
	(T NIL)))

(DEFUN COM=2=RIGHT.BRACKET (LEFT)

  ;;; Edited : JUNE-93
  ;;; Value  : RIGHT.BRACKET -> END or } ; Error if left and right bracket don't match

  (COND ((EQ LEFT 'WITH)
	 (COND ((NOT (COM=1=SYMBOL.ACCEPTED '("END")))
		(COM=ERROR 0 "END expected"))))
	((EQ LEFT '{)
	 (COND ((NOT (COM=1=SYMBOL.ACCEPTED '("}")))
		(COM=ERROR 0 " } expected"))))))
		
	 


; ========================================
;
; Part Three: Managment of the symboltable
;
; ========================================

(DEFUN COM=3=CHECK.OR.INTRODUCE.SYMBOL (NAME KIND DOMAIN &OPTIONAL RANGE ATTRIBUTES SEM.ATTRIBUTES)
  (COND ((COM=5=NAME.OBJECT NAME DOMAIN (LIST KIND))
	 (COM=3=CHECK.SYMBOL NAME KIND DOMAIN RANGE SEM.ATTRIBUTES))
	(T (COND ((MEMBER 'KNOWN.SYMBOL SEM.ATTRIBUTES)
		  (COM=ERROR 4 KIND NAME)))
	   (COM=3=INTRODUCE.SYMBOL NAME KIND DOMAIN RANGE ATTRIBUTES))))


(DEFUN COM=3=INTRODUCE.SYMBOL (NAME KIND DOMAIN &OPTIONAL RANGE ATTRIBUTES)

  ;;; Value: the introduced symbol
  
  (LET (OBJECT)
       (COND ((SETQ OBJECT (COM=5=NAME.OBJECT NAME DOMAIN (LIST KIND)))
	      (COM=ERROR 3 (COM=TYPE OBJECT) NAME))
	     (T (SETQ NAME (COM=3=NORMALIZE.NAME NAME KIND))
	        (CASE KIND
		      (FUNCTION (DB-FUNCTION.INSERT (DA-FUNCTION.CREATE NAME RANGE DOMAIN NIL ATTRIBUTES)))
		      (PREDICATE (DB-PREDICATE.INSERT (DA-PREDICATE.CREATE NAME DOMAIN ATTRIBUTES))))))))


(DEFUN COM=3=INTRODUCE.CONSTRUCTOR (NAME DOMAIN RANGE &OPTIONAL ATTRIBUTES)

  ;;; Edited : March 93
  ;;; Value  : the introduced symbol

  (COND ((SOME #'(LAMBDA (OBJECT)
		   (AND (DA-FUNCTION.IS OBJECT)
			(DA-FUNCTION.IS.CONSTRUCTOR OBJECT)))
	       (DB-NAME.OBJECT NAME))
	 (COM=ERROR 7 NAME))
	(T (SETQ NAME (COM=3=NORMALIZE.NAME NAME 'FUNCTION))
	   (DB-FUNCTION.INSERT (DA-FUNCTION.CREATE NAME RANGE DOMAIN NIL ATTRIBUTES)))))


(DEFUN COM=3=CHECK.SYMBOL (NAME &OPTIONAL KIND DOMAIN RANGE SEM.ATTRIBUTES)

  ;;; Edited: 11-MAR-82 15:30:10
  ;;; Input:  NAME - an atom
  ;;;         KIND - one of the atoms: VARIABLE, FUNCTION or PREDICATE, denoting the kind
  ;;;                of SYMBOLNAME
  ;;;         DOMAIN - a linear list where each toplevelatom is a sortsymbol denoting the domain of
  ;;;                  SYMBOLNAME
  ;;;         RANGE - a sortsymbol denoting the range of SYMBOLNAME
  ;;;         ATTRIBUTE - a list of some atoms like : NIL, SYMMETRIC, DEFINED, STRUCTURE, REFLEXIVE,
  ;;;                     IRREFLEXIVE ETC.
  ;;;         SEM.ATTRIBUTES - a list of some atoms like : REC.SYMBOL, CONSTRUCTIVE.SYMBOL, KNOWN.SYMBOL ETC.
  ;;; Effect: performs a compatibility check between the arguments and the description of SYMBOLNAME in
  ;;;         the symboltable. In case of incompatibility an error message is emitted. The semantic checks
  ;;;         are controlled by the atoms of SEM.ATTRIBUTES:
  ;;;         REC.SYMBOL - indicates that the following atom of SEM.ATTRIBUTES denotes a function or
  ;;;                      predicate symbol which must not occur as SYMBOLNAME.
  ;;;         CONSTRUCTIVE.SYMBOL - indicates that in the context under analysis, each constant -,function -,
  ;;;                               and predicate-symbol has to be introduced by a structure-, function - or
  ;;;                               predicate-definition.
  ;;;         KNOWN.SYMBOL - indicates that every symbol different from a variable must be known in the
  ;;;                        context under analysis.
  ;;; Value:  the corresponding dataterm object of symbolname.

  (LET ((SYMBOL (COM=5=NAME.OBJECT NAME DOMAIN (LIST KIND))) DATA.KIND)
    (COND ((NULL SYMBOL) (COM=ERROR 5 KIND NAME))
	  (T (SETQ DATA.KIND (COM=TYPE SYMBOL))
	     (COND ((NEQ DATA.KIND KIND)
		    (COM=ERROR 2  NAME KIND))
		   (T (CASE KIND
			(VARIABLE (COND ((AND RANGE
					      (NOT (DA-SORT.IS.SUBSORT (DA-VARIABLE.SORT SYMBOL) RANGE)))
					 (COM=ERROR 71 NAME (DA-VARIABLE.SORT SYMBOL) RANGE))))
			(FUNCTION (COND ((AND RANGE
					      (NOT (DA-SORT.IS.SUBSORT (DA-FUNCTION.SORT SYMBOL) RANGE)))
					 (COM=ERROR 27 NAME DOMAIN (DA-FUNCTION.SORT SYMBOL) RANGE))
					((AND DOMAIN (NEQ DOMAIN 'UNSPEC) (NEQ (LENGTH DOMAIN) (DA-FUNCTION.ARITY SYMBOL)))
					 (COM=ERROR 23 (DA-FUNCTION.ARITY SYMBOL) NAME (LENGTH DOMAIN)))
					((AND DOMAIN (NEQ DOMAIN 'UNSPEC)
					      (NOT (EVERY #'(LAMBDA (SORT1 SORT2)
							      (DA-SORT.IS.SUBSORT SORT1 SORT2))
							  DOMAIN (DA-FUNCTION.DOMAIN.SORTS SYMBOL))))
					 (COM=ERROR 26 NAME (DA-FUNCTION.DOMAIN.SORTS SYMBOL) RANGE DOMAIN))
				        ((EQ (SECOND (MEMBER 'REC SEM.ATTRIBUTES)) SYMBOL)
					 (COM=ERROR 29 "function" NAME))
				        ((AND (MEMBER 'STRUCTURE SEM.ATTRIBUTES)
					      (NOT (DA-SYMBOL.HAS.ATTRIBUTE SYMBOL 'STRUCTURE)))
				        (COM=ERROR 12 SYMBOL))))
			(PREDICATE (COND ((AND DOMAIN (NEQ DOMAIN 'UNSPEC)
					       (NEQ (LENGTH DOMAIN) (LENGTH (DA-PREDICATE.DOMAIN.SORTS SYMBOL))))
					  (COM=ERROR 34 (LENGTH (DA-PREDICATE.DOMAIN.SORTS SYMBOL)) NAME
						        (LENGTH DOMAIN)))
					 ((AND DOMAIN (NEQ DOMAIN 'UNSPEC)
					       (NOT (EVERY #'(LAMBDA (SORT1 SORT2)
							       (DA-SORT.IS.SUBSORT SORT1 SORT2))
							   DOMAIN (DA-PREDICATE.DOMAIN.SORTS SYMBOL))))
					  (COM=ERROR 26 NAME (DA-PREDICATE.DOMAIN.SORTS SYMBOL) DOMAIN))
					 ((EQ (SECOND (MEMBER 'REC SEM.ATTRIBUTES)) SYMBOL)
					  (COM=ERROR 29 "predicate" NAME)))))
		      SYMBOL))))))


(DEFUN COM=3=CHECK.OR.INTRODUCE.SORT (NAME &OPTIONAL SUBSORTS ATTRIBUTES SEM.ATTRIBUTES)
  (LET (OBJECT)
    (COND ((SETQ OBJECT (COM=5=NAME.OBJECT NAME NIL '(SORT)))
	   (COM=3=CHECK.SORT OBJECT SUBSORTS SEM.ATTRIBUTES))
	  (T (COM=3=INTRODUCE.SORT NAME SUBSORTS ATTRIBUTES)))))


(DEFUN COM=3=INTRODUCE.SORT (NAME &OPTIONAL SUBSORTS ATTRIBUTES)
  (LET (SYMBOL SORT)
    (COND ((SETQ SYMBOL (COM=5=NAME.OBJECT NAME NIL '(SORT)))
	   (COM=ERROR 3 "sort" NAME))
          (T (SETQ SORT (DA-SORT.CREATE (COM=3=NORMALIZE.NAME NAME 'SORT) SUBSORTS))
             (SETF (DA-SORT.ATTRIBUTES SORT) ATTRIBUTES)
             (SETF (DA-SORT.EXAMPLES SORT)
	           (LIST (DA-TERM.CREATE 
			  (DB-FUNCTION.INSERT (DA-FUNCTION.CREATE (FORMAT NIL "System_~A" (DA-SORT.PNAME SORT))
								  SORT NIL)))))
             (SETF (GETF (DA-SYMBOL.ATTRIBUTES (da-term.symbol (CAR (DA-SORT.EXAMPLES SORT)))) 'DEFAULT) T)
             (DB-SORT.INSERT SORT)
             SORT))))


(DEFUN COM=3=CHECK.SORT (OBJECT &OPTIONAL SUBSORTS SEM.ATTRIBUTES)
  
  ;;; INPUT:  OBJECT represents a sort, SUBSORTS are sorts and SEM.ATTRIBUTES is a list of atoms
  ;;; EFFECT: all sorts are tested for consistency
  ;;; VALUE:  UNDEFINED.
  
  (LET (SORT)
       (COND ((NEQ (COM=TYPE OBJECT) 'SORT) (COM=ERROR 2 (COM=TYPE OBJECT) OBJECT "sort"))
	     ((SOME #'(LAMBDA (SORT) 
			      (COND ((NEQ (COM=TYPE SORT) 'SORT) (COM=ERROR 2 (COM=TYPE SORT) SORT "sort"))))
		    SUBSORTS))
	     ((AND (SETQ SORT (SECOND (MEMBER 'BASE.SORT SEM.ATTRIBUTES)))
		   (NOT (MEMBER OBJECT (DA-SORT.BASE.SORTS sort))))
	      (COM=ERROR 13 SORT OBJECT)))
       OBJECT))


(DEFUN COM=3=NORMALIZE.NAME (NAME KIND)
  (CASE KIND
    (FUNCTION (STRING-DOWNCASE NAME))
    (PREDICATE (STRING-CAPITALIZE NAME))
    (SORT (STRING-DOWNCASE NAME))
    (VARIABLE NAME)
    (OTHERWISE NAME)))



(DEFMACRO COM=3=VSTACK.PUSH ()
  
  ;;; edited: 11-mar-81 10:26:08
  ;;; input:  none
  ;;; effect: pushes variable stack.
  ;;; value:  undefined
  
  `(PUSH COM*ALL.VARIABLES COM*VARIABLE.STACK))


(DEFMACRO COM=3=VSTACK.POP ()

  ;;; INPUT:  NONE
  ;;; EFFECT: UNDOES THE LAST PUSH TO THE VARIABLE STACK.
  ;;; VALUE:  UNDEFINED
  
  `(SETQ COM*ALL.VARIABLES (POP COM*VARIABLE.STACK)))


(DEFMACRO COM=3=VSTACK.NEWNAME (ANYSYMBOL)

  ;;; Edited: 17-JUL-81 11:29:40
  ;;; Input:  ANYSYMBOL  - an atom
  ;;; Effect & Value:  if ANYSYMBOL is a variable symbol which is member of the variable stack
  ;;;                  the new name of ANYSYMBOL.

  `(CASSOC ,ANYSYMBOL COM*ALL.VARIABLES :TEST 'STRING-EQUAL))


(DEFMACRO COM=3=VSTACK.OLDNAME (ANYSYMBOL)

  ;;; Edited: 17-JUL-81 11:36:59
  ;;; Input:  ANYSYMBOL - an atom
  ;;; Effect & Value:  if ANYSYMBOL is a renamed variable the original variable name.

  `(CAR (FIND-IF #'(LAMBDA (ENTRY) (EQ ,ANYSYMBOL (CDR ENTRY))) COM*ALL.VARIABLES)))



(DEFUN COM=3=CHECK.SET.SORTS (SET.SORT ELEMENT.SORT)
  ;;; Edited : 04.01.94 by CS
  ;;; Input  : two strings denoting the set sort name and its element sort name
  ;;; Effect : checks whether the set sort name is new and its element sort name
  ;;;          is not the set sort name

  (COND ((COM=5=NAME.OBJECT SET.SORT NIL '(SORT))
	 (COM=ERROR 3 "sort" SET.SORT))
	((STRING-EQUAL SET.SORT ELEMENT.SORT)
	 (COM=ERROR 90 SET.SORT ELEMENT.SORT))))

(DEFUN COM=3=CHECK.ARRAY.SORTS (ARRAY.SORT INDEX.SORT ENTRY.SORT)
  ;;; Edited : 04.01.94 by CS
  ;;; Input  : three strings denoting the array sort name its index sort name and its entry sort name
  ;;; Effect : checks whether the array sort name is new and its index sort name and its
  ;;;          entry sort name are different from the array sort name

  (COND ((COM=5=NAME.OBJECT ARRAY.SORT NIL '(SORT))
	 (COM=ERROR 3 "sort" ARRAY.SORT))
	((OR (STRING-EQUAL ARRAY.SORT INDEX.SORT) (STRING-EQUAL ARRAY.SORT ENTRY.SORT))
	 (COM=ERROR 91 ARRAY.SORT INDEX.SORT ENTRY.SORT))))


(DEFUN COM=3=CHECK.INSTANTIATION.LIST (INSTANTIATIONS CONSTRUCTOR.NAMES NAMES)
  ;;; Edited : 10.01.94 by CS
  ;;; Input  : a list of instantiations, i.e. "(list left right LISTE)" where
  ;;;          the third component does not bother here, and two lists of names
  ;;; Effect : checks the instanitations for some criteria, see next function
  
  (COND ((NULL INSTANTIATIONS) T)
	(T (LET ((LEFT (FIRST (FIRST INSTANTIATIONS)))
		 (RIGHT (SECOND (FIRST INSTANTIATIONS)))
		 (REST.LIST (CDR INSTANTIATIONS)))
	     (AND (COM=3=CHECK.INSTANTIATION.LIST.1 LEFT RIGHT REST.LIST CONSTRUCTOR.NAMES NAMES)
		  (COM=3=CHECK.INSTANTIATION.LIST REST.LIST CONSTRUCTOR.NAMES NAMES))))))

(DEFUN COM=3=CHECK.INSTANTIATION.LIST.1 (LEFT RIGHT INSTANTIATIONS CONSTRUCTOR.NAMES NAMES)
  ;;; Edited : 10.01.94 by CS
  ;;; Input  : two strings, left and right, a list of instantiations, see previous function, and
  ;;;          two lists of names, a list of constructor names and a list of other names
  ;;; Effect : checks some criteria of the instantiations:
  ;;;          1. if right is already defined as constructor function, then overloading prohibits the definition of
  ;;;             left as a constructor function
  ;;;          2. left must be a member of either constructor.names or names
  ;;;          3. left is not to be instantiated twice
  ;;;          4. if right is to be used twice within this instantiation it must be fulfilled that the
  ;;;             corresponding lefts are not contained in the third component of INSTANTIATIONS, this
  ;;;             will ensure overloading restrictions
  
  (AND (COND ((NOT (AND (FIND LEFT CONSTRUCTOR.NAMES :TEST #'STRING-EQUAL)
			(SOME #'(LAMBDA (OBJECT)
				  (AND (DA-FUNCTION.IS OBJECT)
				       (DA-FUNCTION.IS.CONSTRUCTOR OBJECT)))
			      (DB-NAME.OBJECT RIGHT)))))
	     (T (COM=ERROR 7 RIGHT)))
       (COND ((FIND LEFT NAMES :TEST #'STRING-EQUAL))
	     (T (COM=ERROR 92 LEFT)))
       (EVERY #'(LAMBDA (INSTANCE)
		   (AND (COND ((NOT (STRING-EQUAL LEFT (FIRST INSTANCE))))
			      (T (COM=ERROR 94 LEFT)))
			(COND ((NOT (STRING-EQUAL RIGHT (SECOND INSTANCE))))
			      ((NOT (FIND LEFT (THIRD INSTANCE) :TEST #'STRING-EQUAL)))
			      (T (COM=ERROR 94 RIGHT)))))
	       INSTANTIATIONS)))


(DEFUN COM=5=NAME.OBJECT (NAME &OPTIONAL DOMAIN TYPES)

  ;;; Edited : March 93
  ;;; Input  : the name of a data object
  ;;;          the domain in case NAME is a function or a predicate
  ;;; Value  : the correspomnding data object
  
  (COND ((COM=3=VSTACK.NEWNAME NAME))
	((FIND-IF #'(LAMBDA (OBJECT)
		      (AND (DED-INPUT.IS.ACTIVE (DA-OBJECT.DEFINING.INPUT OBJECT))
			   (OR (EQ TYPES 'UNSPEC)
			       (AND (MEMBER 'SORT TYPES) (DA-SORT.IS OBJECT))
			       (AND (OR (MEMBER 'FUNCTION TYPES) (MEMBER 'PREDICATE TYPES))
				    (DA-PREFUN.IS OBJECT)
				    (LET ((OBJECT.DOMAIN (DA-PREFUN.DOMAIN.SORTS OBJECT)))
				      (OR (EQ DOMAIN 'UNSPEC)
					  (AND (EQ (LENGTH DOMAIN) (LENGTH OBJECT.DOMAIN))
					       (EVERY #'(LAMBDA (DOM1 DOM2)
							  (OR (DA-SORT.IS.SUBSORT DOM1 DOM2)
							      (DA-SORT.IS.SUBSORT DOM2 DOM1)))
						      DOMAIN OBJECT.DOMAIN))))))))
		    (DB-NAME.OBJECT NAME)))))


(DEFUN COM=ERROR (NUMBER &REST ARGLIST)
  
  ;;; INPUT:  NUMBER - AN ERROR NUMBER
  ;;;         ARGLIST - A LIST OF SEXPRESSIONS
  ;;; EFFECT: PRINTS THE ERROR MESSAGE SELECTED BY NUMBER ON FILE RETURNS TO THE TOP-LEVEL
  ;;;         OF COM-COMPILE.ARRAY.
  ;;; VALUE:  UNDEFINED
  
  (LET ((string (FORMAT nil
			(CASE NUMBER
			      (0 "syntactic error: ~A")
			      (1 "you have used an illegal sign: ~A is no admissible sign")
			      (2 "~A symbol ~A used as ~A")
			      (3 "attempt to redefine ~A symbol ~A")
			      (4 "unknown ~A-symbol ~A")
			      (5 "attempt to use the non constructive ~A symbol ~A")
			      (6 "symbol ~A is undefined")
			      (7 "attempt to redefined symbol ~A as constructor")
			      (10 "missing base constant, base sort, or irreflexive constructor")
			      (11 "constructor-function or sort expected instead of ~A ")
			      (12 "function ~A has to be a constructor")
			      (13 "~A is no base sort of ~A")
			      (14 "constant-symbol ~A nil -> ~A used with range ~A")
			      (15 "the base.sorts of sort ~A are not disjunct")
			      (23 "~D-ary function-symbol ~A used with ~D arguments.") 
			      (26 "function-symbol ~A ~A -> ~A applied to ~A")
			      (27 "function-symbol ~A ~A -> ~A used with range ~A.")
			      (28 "function-symbol ~A is not defined with domain ~A ")
			      (29 "recursive usage of ~A-symbol ~A")
			      (34 "~D-ary predicate-symbol ~A used with ~D arguments")
			      (36 "predicate-symbol ~A ~A applied to ~A")
			      (601 "attempt to use the announced sort-symbol") ;;
			      (70 "attempt to use the parameter unbound variable ~a")
			      (71 "variable-symbol ~A with sort ~A  used with sort ~A")
			      (80 "~A is not a generic sort, it can not be instantiated")
			      (81 "overloading not complete, missing new name for ~a ~a")
			      (82 "the following objects can not be renamed : ~A ")
			      (83 "attempt to modify specification of ~A although there are already instances")
			      (84 "attempt to re-insatntiate ~A to ~A ")
  			      (90 "set sort ~A must be different from element sort ~A")
 			      (91 "array sort ~A must be different from index sort ~A and entry sort ~A")
			      (92 "~A not a valid name")
			      (94 "attempt to redefine ~A")
			      (101 "~A is no variable")
			      (102 "~A instantiated twice")
			      (103 "sort of term ~A is not subsort of sort of variable ~A")
			      (104 "specified instantiation is no legal substitution here"))
			(CAR ARGLIST) (SECOND ARGLIST) (THIRD ARGLIST) (FOURTH ARGLIST)) )) 
    (COND ((> NUMBER 1) (MULTIPLE-VALUE-SETQ (COM*CURSOR-X COM*CURSOR-Y)
			  (COM=1=PREV.POSITION COM*CURSOR-X COM*CURSOR-Y))))
    (THROW 'COM*ERROR.TAG (VALUES (LIST COM*CURSOR-X COM*CURSOR-Y string) NIL))))


(DEFUN COM=TYPE (SYMBOL)
  (COND ((DA-FUNCTION.IS SYMBOL) 'FUNCTION)
	((DA-PREDICATE.IS SYMBOL) 'PREDICATE)
	((DA-VARIABLE.IS SYMBOL) 'VARIABLE)
	((DA-SORT.IS SYMBOL) 'SORT)))


(defun com-compile.ensures.cases (variables case.list)

  (LET (PARAMETER.LIST CASES)
    (SETQ COM*VARIABLE.STACK NIL)
    (SETQ COM*ALL.VARIABLES NIL)
    (setq variables (list variables))
    (UNWIND-PROTECT  (CATCH 'COM*ERROR.TAG
		       (SETQ COM*CURSOR-X 0 COM*CURSOR-Y 0)
		       (SETQ COM*INPUT.ARRAY variables)
		       (SETQ COM*CURSOR.LINES variables)
		       (COM=1=NEXT.SYMBOL)
		       (SETQ PARAMETER.LIST (COM=2=PARAMETER.LIST))
		       (SETQ CASES (COM=2=ENSURES.CASES case.list))
		       (VALUES PARAMETER.LIST CASES))
      (COM=3=VSTACK.POP))))
  

(DEFUN COM=2=ENSURES.CASES (CASE.LIST)

  (LET (CONDITION TERM OLD.TERM text)
    
    (setq text (list (CAR (CAR CASE.LIST))))
    (SETQ COM*CURSOR-X 0 COM*CURSOR-Y 0)
    (SETQ COM*INPUT.ARRAY text)
    (SETQ COM*CURSOR.LINES text)
    (COM=1=NEXT.SYMBOL)
    (setq CONDITION (COM=2=ENSURES.CONDITION))
    
    (setq text (list (CDR (CAR CASE.LIST))))
    (SETQ COM*CURSOR-X 0 COM*CURSOR-Y 0)
    (SETQ COM*INPUT.ARRAY text)
    (SETQ COM*CURSOR.LINES text)
    (COM=1=NEXT.SYMBOL)
    (setq term (COM=2=QUANTIFICATION))
    (COND ((NULL (CDR CASE.LIST))
	   (COND ((some #'(lambda (x) (DA-FORMULA.IS.FALSE x)) CONDITION) (DA-GTERM.DEF.VALUE.CREATE TERM))
		 (T (DA-GTERM.DEFINITION.CREATE (LIST (DA-GTERM.DEF.CREATE (DA-GTERM.DEF.VALUE.CREATE TERM) CONDITION)
						      (DA-GTERM.DEF.CREATE (DA-GTERM.DEF.VALUE.CREATE (DA-TERM.CREATE 'UNSPEC NIL))
									   'OTHERWISE))))))
	  (T (SETQ OLD.TERM (COM=2=ENSURES.CASES (CDR CASE.LIST)))
	     (DA-GTERM.DEFINITION.CREATE (LIST (DA-GTERM.DEF.CREATE (DA-GTERM.DEF.VALUE.CREATE TERM) CONDITION)
					       (DA-GTERM.DEF.CREATE OLD.TERM 'OTHERWISE)))))))


(DEFUN COM=2=ENSURES.CONDITION ()

  (COM=ITERATION.WITH.SEPARATOR #'COM=2=ENSURE.QUANTIFICATION '("AND") NIL))


(DEFUN COM=2=ENSURE.QUANTIFICATION (&OPTIONAL ATTRIBUTES)
  
  ;;; Edited:  1-MAR-82 12:44:48
  ;;; Effect:  <LITERAL> -> NOT <ATOM> or <ATOM>
  ;;; Value:   the code generated by this rule , i.e. a FOR-LITERAL 
  
    (COND ((COM=1=SYMBOL.ACCEPTED '("NOT"))
	   (COM=2=QUANTIFICATION ATTRIBUTES))
	  (T (DA-FORMULA.NEGATE.AND.NORMALIZE (COM=2=QUANTIFICATION ATTRIBUTES)))))

