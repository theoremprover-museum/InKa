;;; -*- Package: INKA; Mode: LISP; Syntax: Common-Lisp -*-

(IN-PACKAGE :INKA)


(DEFSTRUCT (DED*THEORY (:CONC-NAME DED=THEORY.) (:PRINT-FUNCTION DED=THEORY.PRINT))

  NAME                         ; the name of the theory
  TYPE                         ; either 'FILE, 'MAPPING, PREDEFINED or 'COMPOSED
  MAPPING                      ; a hashtable denoting the mapping between names and symbols
  SUB.THEORIES                 ; a list of DED*THEORY's
  AXIOMS                       ; a list of all axioms belonging to this theory
  LEMMATA                      ; a list of all lemmata belonging to this theory
  FILE                         ; name of the file or the formula in case of a predefined mapping
  DATE                         ; date of the generation of the specification
  STATUS                       ; either 'ACTIVE or 'PASSIVE
  )


(DEFSTRUCT (DED*INPUT (:CONC-NAME DED=INPUT.) (:PRINT-FUNCTION DED=INPUT.PRINT))
  
  PNAME                        ; a vector of strings describing the user input
  NAME                         ; a name of the formula
  TYPE                         ; an atom like e.g. LEMMA, AXIOM, FUNCTION, PREDICATE, PROPERTY
  FORMULAS                     ; a list of gterms denoting the predicate logical part of the input
  AXIOMS                       ; a list of gterms which had to be proved in order to add this input to the database
  HISTORY                      ; a list of sexpressions evaluating of which would make the input undone
  KIND                         ; an atom like PREDEFINED, LOADED or INSERTED
  STATUS                       ; either 'ACTIVE or 'PASSIVE
  PROOFS                       ; a list of filename, where proofs are stored
  THEORY                       ; the theory in which this datatype is defined
  PRED                         ; its predecessor
  )


(DEFVAR DED*THEORY.ACTUAL NIL)

(DEFVAR DED*THEORY.TOP NIL)

(DEFVAR DED*THEORIES.LOADED NIL)

(DEFVAR DED*THEORY.PREDEFINED NIL)


(DEFVAR DED*INPUT.ACTUAL NIL)

(DEFVAR DED*INPUT.ACTUAL.WAY NIL)


(DEFVAR DED*DEFAULT.PATHNAME NIL)


(DEFUN DED-RESET ()

  ;;; Input:  None.
  ;;; Effect: Clears the complete database of the inka-system and resets some modules
  ;;; Value:  undefined.

  (COND ((NOT (EDT-AXIOMS.PROHIBITED))
	 (SETQ DED*THEORY.TOP (MAKE-DED*THEORY :NAME "Top-level" :TYPE 'COMPOSED :STATUS 'ACTIVE))
	 (SETQ DED*THEORY.ACTUAL DED*THEORY.TOP)
	 (SETQ DED*THEORIES.LOADED NIL)
	 (SETQ DED*THEORY.PREDEFINED (MAKE-DED*THEORY :NAME "Predefined" :TYPE 'PREDEFINED :STATUS 'ACTIVE))
	 (SETQ DED*INPUT.ACTUAL.WAY NIL)
	 (SETQ DED*DEFAULT.PATHNAME (COND ((PRO-ENVIRONMENT-VARIABLE "PROOFDIR")
					   (FORMAT NIL "~A/" (ENVIRONMENT-VARIABLE "PROOFDIR")))))
	 (LET ((DED*THEORY.ACTUAL DED*THEORY.PREDEFINED)
	       (DED*INPUT.ACTUAL (MAKE-DED*INPUT :NAME 'PREDEFINED :STATUS 'ACTIVE :THEORY DED*THEORY.PREDEFINED)))
	   (DA-RESET)
	   (DB-RESET)
	   (DP-RESET))
	 (UNI-RESET))))


(DEFMACRO DED-WITH.MAPPING (MAPPING BODY)

  ;;; Input:   a list of dotted pairs of strings and a list of sexpressions.
  ;;; Effect:  evaluates \verb$BODY$ in the scope of the given \verb$MAPPING$.
  ;;; Value:   the result of the evaluation of \verb$BODY$.

  `(UNWIND-PROTECT (PROGN (COM-MAPPING.PUSH ,MAPPING)
			  (LET ((NEW.OBJECT (MAKE-DED*THEORY :TYPE 'MAPPING :MAPPING ,MAPPING
							     :FILE (COND (DED*THEORIES.LOADED
									  (DED=THEORY.FILE
									   (CAR (CAR DED*THEORIES.LOADED)))))
							     :STATUS 'ACTIVE)))
			    (PUSH NEW.OBJECT (DED=THEORY.SUB.THEORIES DED*THEORY.ACTUAL))
			    (LET ((DED*THEORY.ACTUAL NEW.OBJECT))
			      (PROGN ,@BODY))))
     (COM-MAPPING.POP)))


(DEFUN DED-EXPAND (FILE)

  ;;; Input:   a file 
  ;;; Effect:  \verb$FILE$ should be a file stored by DED-SAVE. The \verb$FILE$ is loaded (in case it is not
  ;;;          yet loaded) and thus, \verb$FILE$ is added to the actual database.
  ;;; Value:   T, if \verb$FILE$ is loaded or already been loaded. Nil, otherwise

  (DED-LOAD FILE T))

(DEFUN DED-FORMULA.INSERT (FORMULA &OPTIONAL AXIOMS STATUS PROOFS)
  
  ;;; Input:   a vector of strings denoting the user-input, a list of gterms, a flag,
  ;;;          and the name of proofs corresponing to \verb$AXIOMS$
  ;;; Effect:  \verb$FORMULA$ is syntactically and semantically analyzed. Neccessary proofs
  ;;;          for consistency are performed. If no errors occur the formula is added to
  ;;;          the database.
  ;;; Value:   a multiple value is returned:
  ;;;            NIL and name of function, if the current formula is inserted,
  ;;;            position of error and undefined else.
  
  (LET (ERROR.OCCURED COMPILED.FORMULA TYPE NAME FAIL)
    (COND ((NULL STATUS) (SETQ STATUS (COND (DED*INPUT.ACTUAL.WAY 'LOADED) (T 'INSERTED)))))
    (SETQ DED*INPUT.ACTUAL (MAKE-DED*INPUT :PNAME FORMULA :HISTORY NIL :AXIOMS NIL :KIND STATUS
					   :PRED DED*INPUT.ACTUAL :STATUS 'ACTIVE :THEORY DED*THEORY.ACTUAL))
    (UNWIND-PROTECT (COND ((MULTIPLE-VALUE-SETQ (ERROR.OCCURED COMPILED.FORMULA) (COM-COMPILE FORMULA))
			   (SETQ FAIL ERROR.OCCURED))
			  (T (MAPC #'(LAMBDA (FORM PROOF)
				       (COND ((NULL (MULTIPLE-VALUE-SETQ (ERROR.OCCURED FORM)
						      (COM-COMPILE FORM)))
					      (DED-INPUT.AXIOMS.INSERT (THIRD FORM) PROOF))))
				   AXIOMS PROOFS)
			     (MULTIPLE-VALUE-SETQ (TYPE NAME FORMULA) (VALUES-LIST COMPILED.FORMULA))
			     (SETF (DED=INPUT.TYPE DED*INPUT.ACTUAL) TYPE
				   (DED=INPUT.NAME DED*INPUT.ACTUAL) (FORMAT NIL "~A" NAME))
			     (COND ((SETQ FAIL (DED=FORMULA.INSERT TYPE NAME FORMULA)))
				   (T (DED=INPUT.INSERT.TO.THEORY DED*INPUT.ACTUAL)
				      (SETQ FAIL NIL)))))
		    (COND (FAIL (DED=INPUT.HISTORY.DELETE (DED=INPUT.HISTORY DED*INPUT.ACTUAL))
				(SETQ DED*INPUT.ACTUAL (DED=INPUT.PRED DED*INPUT.ACTUAL)))))
    (VALUES FAIL NAME)))


(DEFUN DED-FORMULA.DELETE (&OPTIONAL INPUT THEORY)

  ;;; Effect:  removes the actual input out of the database
  ;;;          also all inputs which depend on this input are also removed.
  ;;; Value:   if deletion was successfull the name of the deleted entry

  (LET (PRED)
    (COND ((NULL INPUT)
	   (COND ((SETQ INPUT DED*INPUT.ACTUAL)
		  (SETQ THEORY DED*THEORY.ACTUAL)
		  (SETQ PRED (DED=INPUT.PRED INPUT))))))
    (COND ((NULL INPUT) NIL)
	  ((AND (EDT-AXIOMS.PROHIBITED) (NEQ (DED=INPUT.TYPE INPUT) 'LEMMA))
	   NIL)
	  (T (COND ((EQ (DED=INPUT.TYPE INPUT) 'LEMMA)
		    (SETF (DED=THEORY.LEMMATA THEORY) (DELETE INPUT (DED=THEORY.LEMMATA THEORY) :COUNT 1)))
		   (T (SETF (DED=THEORY.AXIOMS THEORY) (DELETE INPUT (DED=THEORY.AXIOMS THEORY) :COUNT 1))))
	     (DED=INPUT.HISTORY.DELETE (DED=INPUT.HISTORY INPUT))
	     (SETQ DED*INPUT.ACTUAL PRED)
	     (DED=INPUT.NAME INPUT)))))


(DEFUN DED-FORMULA.PROVE (FORMULA &OPTIONAL QUIET FILE)
  
  ;;; Input:   a vector of strings denoting the user-input, a flag, and a filename
  ;;; Effect: \verb$FORMULA$ is syntactically and semantically analyzed. Neccessary proofs
  ;;;          for consistency are performed. If no errors occur the formula is added to
  ;;;          the database.
  ;;; Value:   a multiple value is returned:
  ;;;          NIL and name of function, if the current formula is inserted,
  ;;;          position of error and undefined else.
  
  
  (LET ((DED*INPUT.ACTUAL (MAKE-DED*INPUT :PNAME FORMULA :HISTORY NIL :AXIOMS NIL :STATUS 'ACTIVE :THEORY DED*THEORY.ACTUAL))
	ERROR.OCCURED COMPILED.FORMULA TYPE NAME RESULT)
    (UNWIND-PROTECT (COND ((MULTIPLE-VALUE-SETQ (ERROR.OCCURED COMPILED.FORMULA) (COM-COMPILE FORMULA)))
			  (T (MULTIPLE-VALUE-SETQ (TYPE NAME FORMULA)
			       (VALUES-LIST COMPILED.FORMULA))
			     (COND ((MEMBER TYPE '(LEMMA PROPERTY))
				    (SETQ RESULT (SEL-THEOREM.PROVE FORMULA QUIET FILE))))))
      (DED=INPUT.HISTORY.DELETE (DED=INPUT.HISTORY DED*INPUT.ACTUAL)))
    (VALUES RESULT ERROR.OCCURED)))


(DEFUN DED-SAVE (FILE &OPTIONAL (THEORY DED*THEORY.ACTUAL))

  ;;; Input:   a filename
  ;;; Effect:  stores the complete specification into a file $<$ \verb$FILE$ $>$.SPEC, loading
  ;;;          that file will restore the specification part of the database.
  ;;; Value:   undefined.

  (LET (ABORT LEMMA.THEORIES SPEC.THEORIES)
    (COND (FILE (SETF (DED=THEORY.FILE THEORY) (PATHNAME FILE))))
    (MULTIPLE-VALUE-SETQ (LEMMA.THEORIES SPEC.THEORIES) (DED=THEORIES.CHANGED THEORY NIL NIL))
    (COND ((SETQ ABORT (SOME #'(LAMBDA (THEORY)
				 (DED=THEORY.CHECK.FILENAME THEORY))
			     (UNION LEMMA.THEORIES SPEC.THEORIES)))
	   (WIN-IO.PRINT.STATUS (WIN-WINDOW 'MAIN) (FORMAT NIL "~A. Database not stored" ABORT)))
	  ((OR LEMMA.THEORIES SPEC.THEORIES)
	   (MAPC #'(LAMBDA (THEORY)
		     (DED=SAVE.THEORY THEORY 'SPEC)
		     (DED=SAVE.THEORY THEORY 'LEMMA))
		 SPEC.THEORIES)
	   (MAPC #'(LAMBDA (THEORY)
		     (DED=SAVE.THEORY THEORY 'LEMMA))
		 LEMMA.THEORIES)
	   (WIN-IO.print.status (WIN-WINDOW 'MAIN) "Database stored"))
	  (T (WIN-IO.PRINT.STATUS (WIN-WINDOW 'MAIN) "No changes. Nothing done.")))))


(DEFUN DED-LOAD (FILE &OPTIONAL NO.RESET)

  ;;; Input:   a file and a flag
  ;;; Effect:  \verb$FILE$ should be a file stored by DED-SAVE. The \verb$FILE$ is
  ;;;          (in case it is not yet loaded under the actual mapping) loaded and thus,
  ;;;          the former database is restored. If \verb$NO.RESET$ is true the database
  ;;;          is added to the exisiting one, otherwise the actual database is initialized first
  ;;; Value:   T, if \verb$FILE$ is loaded or already been loaded. Nil, otherwise

  (LET ((DED*DEFAULT.PATHNAME DED*DEFAULT.PATHNAME)
	SPEC.FILE LEMMA.FILE NAME OBJECT.MAPPING)
    (COND ((NOT NO.RESET) (DED-RESET)))
    (MULTIPLE-VALUE-SETQ (NAME FILE SPEC.FILE LEMMA.FILE) (DED=LOAD.PARSE.FILENAME FILE))
    (COND ((NULL (PROBE-FILE SPEC.FILE))
	   (WIN-IO.PRINT.STATUS (WIN-WINDOW 'MAIN) (FORMAT nil "loading of ~A ignored, file not existing" FILE))
	   NIL)
	  ((SETQ OBJECT.MAPPING (DED=THEORY.IS.LOADED FILE))
	   (WIN-IO.PRINT.STATUS (WIN-WINDOW 'MAIN) (FORMAT NIL "loading of ~A ignored, theory already loaded" NAME))
	   (PUSH (CAR OBJECT.MAPPING) (DED=THEORY.SUB.THEORIES DED*THEORY.ACTUAL))
	   T)
	  (T (LET* ((NEW.OBJECT (MAKE-DED*THEORY :NAME NAME :TYPE 'FILE
						 :FILE FILE :STATUS 'ACTIVE
						 :DATE (file-write-date SPEC.FILE)))
		    (DED*INPUT.ACTUAL.WAY (CONS NEW.OBJECT DED*INPUT.ACTUAL.WAY)))
	       (PUSH NEW.OBJECT (DED=THEORY.SUB.THEORIES DED*THEORY.ACTUAL))
	       (LET ((DED*THEORY.ACTUAL NEW.OBJECT))
		 (PUSH (CONS NEW.OBJECT (COM-ACTUAL.MAPPING)) DED*THEORIES.LOADED)
		 (LOAD SPEC.FILE)
		 (COND ((PROBE-FILE LEMMA.FILE)
			(COND ((>= (file-write-date LEMMA.FILE) (file-write-date spec.FILE))
			       (LOAD LEMMA.FILE))
			      (t (WIN-IO.PRINT.STATUS
				  (WIN-WINDOW 'MAIN)
				  (FORMAT NIL "loading of ~A ignored, lemma-file is older than spec. file" NAME))))))
		 T))))))



(DEFUN DED-DATABASE.DESCRIBE ()

  ;;; Input:   none
  ;;; Effect:  describes the database according to the user's activity
  ;;; Value :  undefined

  (DED=DATABASE.DESCRIBE))


(DEFUN DED-INPUT.HISTORY.INSERT (ENRTY)

  ;;; Input:   an sexpression
  ;;; Effect:  adds \verb$ENTRY$ into the history-slot of the actual input
  ;;; Value:   undefined
  
  (PUSH ENRTY (DED=INPUT.HISTORY DED*INPUT.ACTUAL)))


(DEFUN DED=INPUT.HISTORY.DELETE (INPUT.HISTORY)

  (MAPC #'(LAMBDA (SEXPR) (EVAL SEXPR)) INPUT.HISTORY))


(DEFUN DED-INPUT.HISTORY.DELETE (ENRTY)

  ;;; Input:   an sexpression
  ;;; Effect:  removes \verb$ENTRY$ from the history-slot of the actual input
  ;;; Value:   undefined

  (SETF (DED=INPUT.HISTORY DED*INPUT.ACTUAL)
	(DELETE ENRTY (DED=INPUT.HISTORY DED*INPUT.ACTUAL) :COUNT 1 :TEST #'EQUAL)))


(DEFUN DED-INPUT.AXIOMS.INSERT (GTERM FILE)

  ;;; Input:   a gterm and a filename
  ;;; Effect:  adds \verb$GTERM$  into the axioms-slot of the actual database and adds \verb$FILE$ into the proofs-slot
  ;;;          of the actual database
  ;;; Value:   undefined
  
  (PUSH GTERM (DED=INPUT.AXIOMS DED*INPUT.ACTUAL))
  (SETF (DED=INPUT.KIND DED*INPUT.ACTUAL) 'CHANGED)
  (PUSH FILE (DED=INPUT.PROOFS DED*INPUT.ACTUAL)))


(DEFUN DED=INPUT.INSERT.FORMULAS (FORMULAS)

  (SETF (DED=INPUT.FORMULAS DED*INPUT.ACTUAL)
	(APPEND FORMULAS (DED=INPUT.FORMULAS DED*INPUT.ACTUAL))))


(DEFUN DED-INPUT.AXIOMS ()

  ;;; Value:   the list of all gterms to be proved during the insertion of the actual input
  
  (DED=INPUT.AXIOMS DED*INPUT.ACTUAL))


(DEFUN DED-INPUT.FILE.STACK ()

  ;;; Value:  the actual number of nested \verb$INKA-EXPAND$s   -- da-module ???
  
  DED*INPUT.ACTUAL.WAY)


(DEFUN DED-INPUT.IS.ACTIVE (INPUT)

  (OR (NULL INPUT)
      (AND (EQ (DED=INPUT.STATUS INPUT) 'ACTIVE)
	   (EQ (DED=THEORY.STATUS (DED=INPUT.THEORY INPUT)) 'ACTIVE))))


(DEFMACRO DED-INPUT.ACTUAL.INPUT ()

  ;;; Input:   none
  ;;; Value:   the actual input
  
  `DED*INPUT.ACTUAL)


(DEFUN DED=INPUT.INSERT.TO.THEORY (INPUT)

  ;;; Input:  an input (\verb$DED*INPUT$)
  ;;; Effect: inserts the input in the actual theory
  ;;; Value:  undefined.
  
  (COND ((EQ (DED=INPUT.TYPE INPUT) 'LEMMA)
	 (PUSH INPUT (DED=THEORY.LEMMATA DED*THEORY.ACTUAL)))
	(T (PUSH INPUT (DED=THEORY.AXIOMS DED*THEORY.ACTUAL)))))


(DEFUN DED=THEORIES.CHANGED (THEORY &OPTIONAL LEMMA.STORED SPEC.STORED)

  ;;; Input:  a \verb$DED*THEORY$ and two lists of theories.
  ;;; Effect: adds theory in the first list iff there is a lemma in \verb$THEORY$ which is inserted or
  ;;;         changed since the last backup. Adds theory in the second list iff there is an axiom
  ;;;         in \verb$THEORY$ which is inserted or changed since the last backup.
  ;;; Value:  the multiple value consisting of both lists.

  (MAPC #'(LAMBDA (SUB.THEORY)
	    (COND ((NOT (EQ (DED=THEORY.TYPE SUB.THEORY) 'PREDEFINED))
		   (MULTIPLE-VALUE-SETQ (LEMMA.STORED SPEC.STORED)
		     (DED=THEORIES.CHANGED SUB.THEORY LEMMA.STORED SPEC.STORED)))))
	(DED=THEORY.SUB.THEORIES THEORY))
  (COND ((SOME #'(LAMBDA (INPUT)
		   (COND ((MEMBER (DED=INPUT.KIND INPUT) '(INSERTED CHANGED))
			  (PUSH THEORY SPEC.STORED))))
	       (DED=THEORY.AXIOMS THEORY)))
	(T (SOME #'(LAMBDA (INPUT)
		     (COND ((MEMBER (DED=INPUT.KIND INPUT) '(INSERTED CHANGED))
			    (PUSH THEORY LEMMA.STORED))))
		 (DED=THEORY.LEMMATA THEORY))))
  (VALUES LEMMA.STORED SPEC.STORED))



(DEFUN DED=THEORY.CHECK.FILENAME (THEORY)

  ;;; Input:  a  \verb$DED*THEORY$
  ;;; Effect: tests whether its specificied file is accessible. In case no file is
  ;;;         specified a filename is asked from the user.
  ;;; Value:  an error-string iff file is not accessible, \verb$NIL$ else.

  (LET ((FILE (WIN-IO.GET.FILENAME (COND ((NULL (DED=THEORY.FILE THEORY)) "")
					 (T (DED=THEORY.FILE THEORY)))
				   "specification")))
       (COND ((EQUAL FILE "")
	      "User aborted")
	     (T (SETF (DED=THEORY.FILE THEORY) FILE)
		NIL))))


(DEFUN DED=SAVE.THEORY (THEORY TYPE)

  (LET ((FILE (DED=THEORY.FILE THEORY)))
    (WITH-OPEN-FILE (OUTPUT.STREAM (COND ((EQ TYPE 'LEMMA) (FORMAT nil "~A.LEMMA" FILE))
					 (T (FORMAT nil "~A.SPEC" FILE)))
				   :DIRECTION :OUTPUT :IF-EXISTS :NEW-VERSION)
		    (FORMAT OUTPUT.STREAM "(IN-PACKAGE 'INKA)~%")
		    (COND ((DED=THEORY.MAPPING THEORY)
			   (DED=SAVE.MAPPING.START THEORY OUTPUT.STREAM)))
		    (MAPC #'(LAMBDA (OBJECT)
			      (DED=SAVE.DED.INPUT OBJECT OUTPUT.STREAM))
			  (REVERSE (COND ((EQ TYPE 'SPEC) (DED=THEORY.AXIOMS THEORY))
					 (T (DED=THEORY.LEMMATA THEORY)))))
		    (COND ((DED=THEORY.MAPPING THEORY)
			   (DED=SAVE.MAPPING.END OUTPUT.STREAM))))
    T))


(DEFUN DED=SAVE.DED.INPUT (INPUT STREAM)

  ;;; Input:   an object of DED*INPUT and a stream
  ;;; Effect:  writes a sexpression on stream which evaluted restores the same object
  ;;; Value:   undefined
  
  (FORMAT STREAM "(INKA-FORMULA.INSERT (LIST ~{~S~})" (DED=INPUT.PNAME INPUT))
  (princ "(LIST " stream)
  (MAPC #'(LAMBDA (THEOREM)
	    (FORMAT STREAM "  `(~{~4,2T~S~%~}   )~%" (PR-PRINT.FORMULA THEOREM)))
	(DED=INPUT.AXIOMS INPUT))
  (princ " ) " stream)
  (princ "(LIST " stream)
  (MAPC #'(LAMBDA (STRING) (FORMAT stream " ~S " STRING))
	(DED=INPUT.PROOFS INPUT))
  (princ " )" stream)
  (FORMAT STREAM ")~%"))


(DEFUN DED=SAVE.MAPPING.START (OBJECT STREAM)

  ;;; Input:   an object of type \verb$DED*THEORY$
  ;;; Effect:  \verb$OBJECT$ is considered as a mapping and a text is written
  ;;;          to \verb$STREAM$ which evaluated would reconstruct this mapping.
  ;;; Value:   undefined

  (FORMAT STREAM  "(INKA-WITH.MAPPING '(~{~A~}) ~%"
	  (MAPCAR #'(LAMBDA (S1.S2) (FORMAT NIL "(~S . ~S)" (CAR S1.S2) (CDR S1.S2)))
		  (DED=THEORY.MAPPING OBJECT))))


(DEFUN DED=SAVE.MAPPING.END (STREAM)

  ;;; Input:   an output-stream
  ;;; Effect:  write an closing bracket to the output-stream
  ;;; Value:   undefined

  (FORMAT STREAM ")~%"))


(DEFUN DED=LOAD.PARSE.FILENAME (FILE)

  ;;; Input:  a string
  ;;; Value:  a multiple-value: the name of the theory, the filename of the theory without extensions,
  ;;;         the specification-filename of the theory, and the lemma-filename of the theory

  (LET ((DIRECTORY (pathname-directory (pathname file)))
	NAME POS)
    (COND ((SETQ POS (COND ((POSITION "specifications" DIRECTORY :test #'string-equal))
			   ((POSITION "statespecs" DIRECTORY :test #'string-equal))))
	   (SETQ NAME (NTH (1+ POS) DIRECTORY))
	   (COND ((EQUAL (CAR DIRECTORY) :RELATIVE)
		  (SETQ FILE (MERGE-PATHNAMES FILE DED*DEFAULT.PATHNAME)))
		 (T (SETQ DED*DEFAULT.PATHNAME (MAKE-PATHNAME :HOST (PATHNAME-HOST (pathname file))
							      :DIRECTORY (SUBSEQ DIRECTORY 0 POS))))))
	  (T (SETQ NAME FILE)))
    (VALUES NAME FILE (format nil "~A.SPEC" FILE) (format nil "~A.LEMMA" FILE))))


(DEFUN DED=THEORY.IS.LOADED (FILE)

  ;;; Input:   a file
  ;;; Effect:  tests whether \verb$FILE$ is already loaded under the current mappings.
  ;;; Value:   T iff it is

  (find-if #'(LAMBDA (OBJECT.MAPPING)
	       (AND (EQUAL FILE (DED=THEORY.FILE (CAR OBJECT.MAPPING)))
		    (EQUAL (COM-ACTUAL.MAPPING) (CDR OBJECT.MAPPING))))
	   DED*THEORIES.LOADED))



(DEFUN DED=INPUT.PRINT (INPUT STREAM DEPTH)

  ;;; Input:   an input, a stream, and a natural number
  ;;; Effect:  prints input on stream.
  ;;; Value:   undefined

  (declare (ignore depth))
  (FORMAT STREAM "~A~%" (DED=INPUT.PNAME INPUT)))


;;;;;=========================================================================================================
;;;;;
;;;;;  Insertion of a formula
;;;;;
;;;;;=========================================================================================================


(DEFUN DED=FORMULA.INSERT (TYPE NAME FORMULA)
  
  ;;; Input:  an atom, like 'STRUCTURE, TYPEDECLARATION, AXIOM, PROPERTY, QUANTIFICATION, FUNCTION, PREDICATE,
  ;;;         SET, ARRAY, and a prefun or sort symbol and a formula
  ;;; Effect: depending on TYPE some consistency checks are performed and in case of success FORMULA
  ;;;         is inserted into the database.
  ;;; Value:  NIL iff no error occured

  (COND ((AND (EDT-AXIOMS.PROHIBITED)
	      (NEQ TYPE 'LEMMA)
	      (NEQ TYPE 'COMMENT)))
	(T (CASE TYPE
		 ((COMMENT GENERIC UNSPEC.STRUCTURE) NIL)
		 ((STRUCTURE)
		  (DED=FORMULA.INSERT.STRUCTURE NAME FORMULA))
		 ((ENUM.STRUCTURE)
		  (DED=FORMULA.INSERT.ENUM.STRUCTURE FORMULA))
		 (NON-FREE-STRUCTURE
		  (DED=FORMULA.INSERT.NON.FREE.STRUCTURE FORMULA))
		 ((TYPEDECLARATION AXIOM)
		  (DED=FORMULA.INSERT.AXIOM NAME FORMULA))
		 ((MAPPING)
		  (DED=FORMULA.INSERT.MAPPING FORMULA))
		 ((PROPERTY LEMMA)
		  (DED=FORMULA.INSERT.LEMMA NAME FORMULA))
		 ((FUNCTION PREDICATE)
		  (DED=FORMULA.INSERT.DEFINITION NAME FORMULA))
		 ((DECL.FUNCTION DECL.PREDICATE)
		  (DED=FORMULA.INSERT.DECL.DEFINITION NAME FORMULA))
		 ((SET ARRAY)
		  (DED=PREDEFINED.DT.INSTANTIATE TYPE FORMULA))))))


(DEFUN DED=PREDEFINED.DT.INSTANTIATE (TYPE ARGS)

  (LET* ((NEW.OBJECT (MAKE-DED*THEORY :NAME (FORMAT NIL "Mapping of ~A" TYPE)
				      :TYPE 'PREDEFINED
				      :FILE  nil :STATUS 'ACTIVE
				      :MAPPING (LIST 'PREDEFINED TYPE ARGS)))
	 NEW.INPUT)
    (SETQ NEW.INPUT (MAKE-DED*INPUT :TYPE 'PREDEFINED :STATUS 'ACTIVE :THEORY NEW.OBJECT))
    (PUSH NEW.OBJECT (DED=THEORY.SUB.THEORIES DED*THEORY.ACTUAL))
    (PUSH NEW.INPUT (DED=THEORY.AXIOMS NEW.OBJECT))
    (DED-INPUT.HISTORY.INSERT `(SETF (DED=THEORY.SUB.THEORIES (QUOTE ,DED*THEORY.ACTUAL))
				     (REMOVE (QUOTE ,NEW.OBJECT) (DED=THEORY.SUB.THEORIES (QUOTE ,DED*THEORY.ACTUAL)))))
    (DED-INPUT.HISTORY.INSERT `(MAPC #'(LAMBDA (INPUT) (DED-FORMULA.DELETE INPUT (QUOTE ,NEW.OBJECT)))
				     (DED=THEORY.AXIOMS (QUOTE ,NEW.OBJECT))))
    (DED-INPUT.HISTORY.INSERT `(MAPC #'(LAMBDA (INPUT) (DED-FORMULA.DELETE INPUT (QUOTE ,NEW.OBJECT)))
				     (DED=THEORY.LEMMATA (QUOTE ,NEW.OBJECT))))
    (LET ((DED*THEORY.ACTUAL NEW.OBJECT)
	  (DED*INPUT.ACTUAL NEW.INPUT))
      (CASE TYPE
	    (SET (DP-SET.INSTANTIATE (CAR ARGS) (SECOND ARGS) (THIRD ARGS)))
	    (ARRAY (DP-ARRAY.INSTANTIATE (CAR ARGS) (SECOND ARGS) (THIRD ARGS) (FOURTH ARGS)))))))


(DEFUN DED=FORMULA.INSERT.MAPPING (FORMULA)

  ;;; Input:  a string and a formula
  ;;; Value:  NIL iff no error occured.

  (SOME #'(LAMBDA (TYPE.NAME.FORMULA)
	    (DED=FORMULA.INSERT (CAR TYPE.NAME.FORMULA) (SECOND TYPE.NAME.FORMULA) (THIRD TYPE.NAME.FORMULA)))
	FORMULA))


(DEFUN DED=FORMULA.INSERT.STRUCTURE (NAME FORMULA)

  ;;; Input:  a sort symbol and a formula
  ;;; Effect: inserts FORMULA into the actual database and creates a sort definition in the
  ;;;         example-generator.
  ;;; Value:  NIL iff no error occured.

  (EG-INSERT.SORT NAME)
  (DED=INPUT.INSERT.FORMULAS (DB-FORMULA.INSERT FORMULA (DA-SORT.PNAME NAME) 'axiom))
  (MAPC #'(LAMBDA (DELTA.DIFF)
	    (DED=FORMULA.INSERT.DEFINITION "DEFS" DELTA.DIFF))
	(REC-INSERT.SORT NAME))
  NIL)


(DEFUN DED=FORMULA.INSERT.ENUM.STRUCTURE (FORMULAS)

  ;;; Input:  a sort symbol and a formula
  ;;; Effect: inserts FORMULA into the actual database and creates a sort definition in the
  ;;;         example-generator.
  ;;; Value:  NIL iff no error occured.

  (SOME #'(LAMBDA (ENTRY)
	    (MULTIPLE-VALUE-BIND (TYPE NAME FORMULA)
	      (VALUES-LIST ENTRY)
	      (DED=FORMULA.INSERT TYPE NAME FORMULA)))
	FORMULAS))


(DEFUN DED=FORMULA.INSERT.NON.FREE.STRUCTURE (FORMULAS)

  ;;; Input:  a sort symbol and a formula
  ;;; Effect: inserts FORMULAS into the actual database
  ;;; Value:  NIL iff no error occured.

  (SOME #'(LAMBDA (ENTRY)
	     (MULTIPLE-VALUE-BIND (TYPE NAME2 FORMULA)
	       (VALUES-LIST ENTRY)
	       (DED=FORMULA.INSERT TYPE NAME2 FORMULA)))
	 FORMULAS))


(DEFUN DED=FORMULA.INSERT.AXIOM (NAME FORMULA)
  
  ;;; Input: a symbol and a formula
  ;;; Effect: inserts FORMULA into the actual database regardless whether FORMULA is valid or not.
  ;;;         the consistency of the database is not guaranteed.
  ;;; Value:  NIL iff no error occurred.

  (DED=INPUT.INSERT.FORMULAS (DB-FORMULA.INSERT FORMULA NAME 'AXIOM))
  NIL)


(DEFUN DED=FORMULA.INSERT.LEMMA (NAME FORMULA)

  ;;; Input:  a symbol and a formula
  ;;; Effect: proves whether FORMULA is valid in the actual database and in case FORMULA is valid
  ;;;         inserts FORMULA into the database

  (COND ((SEL-THEOREM.PROVE FORMULA)
	 (DED=INPUT.INSERT.FORMULAS (DB-FORMULA.INSERT FORMULA NAME 'LEMMA))
	 NIL)
	(T (LIST 0 0 "Lemma could not be proven"))))


(DEFUN DED=FORMULA.INSERT.DEFINITION (NAME FORMULA)

  ;;; Input:  an algorithmic function or predicate definition
  ;;; Effect: checks whether the definition is complete, unique and terminating and
  ;;;         if so, inserts them into the actual database. In case of argument-limited
  ;;;         functions also the delta-difference-predicates are inserted.
  ;;; Value:  NIL iff no error occurred.

  (LET (DELTA.DIFFS ERROR.MESSAGE)
    (MULTIPLE-VALUE-SETQ (FORMULA ERROR.MESSAGE) (EXP-DEFINITION.ANALYZE FORMULA))
    (COND (FORMULA
	   (COND ((OR (EQ (DED=THEORY.TYPE DED*THEORY.ACTUAL) 'PREDEFINED)
		      (MULTIPLE-VALUE-SETQ (FORMULA DELTA.DIFFS) (REC-DEFINITION.ANALYZE FORMULA)))
		  (EG-DEFINITION.INSERT FORMULA)
		  (DED=INPUT.INSERT.FORMULAS (DB-DEFINITION.INSERT FORMULA NAME))
		  (MAPC #'(LAMBDA (DELTA.DIFF)
			    (EG-DEFINITION.INSERT DELTA.DIFF)
			    (DED=INPUT.INSERT.FORMULAS (DB-DEFINITION.INSERT DELTA.DIFF NAME)))
			DELTA.DIFFS)
		  NIL)
		 (T DELTA.DIFFS)))
	  (T ERROR.MESSAGE))))


(DEFUN DED=FORMULA.INSERT.DECL.DEFINITION (NAME FORMULA)

  ;;; Input:  a declarative function or predicate definition
  ;;; Effect: adds formula into the database and defines a dummy-lisp-function for NAME
  ;;; Value:  sexpr =/ NIL iff an error occured.

  (EG-DECL.DEFINITION.INSERT NAME)
  (COND (FORMULA (DED=INPUT.INSERT.FORMULAS (DB-FORMULA.INSERT FORMULA NAME 'AXIOM))))
  NIL)



;;;;;=========================================================================================================
;;;;;
;;;;;  Description of the database
;;;;;
;;;;;=========================================================================================================


(DEFUN DED=DATABASE.DESCRIBE ()

  (CASE (CAR (WIN-MN.CHOOSE (WIN-WINDOW 'DESCRIPTION_2)
			    `(("Show development graph" . INSERTED)
			      ("Describe function" . FUNCTION)
			      ("Describe predicate" . PREDICATE)
					; ("Describe sort" . SORT)
			      )))
	(INSERTED (DED=THEORIES.DESCRIBE))
	(FUNCTION (DED=FUNCTION.DESCRIBE))
	(PREDICATE (DED=PREDICATE.DESCRIBE))
	(SORT (DED=SORT.DESCRIBE))))



(DEFUN DED=THEORIES.DESCRIBE ()

  (PR-GRAPHIC.INTERACT (WIN-WINDOW 'DESCRIPTION_2) `(DED=THEORIES.DESCRIBE.1 (QUOTE ,DED*THEORY.TOP))))


(DEFUN DED=THEORIES.DESCRIBE.1 (THEORY)

  (PR-PARSE.HEADLINE (FORMAT NIL "Development graph of ~A :" (DED=THEORY.STRING THEORY))
		     (pr-parse.closure
		      (PR-PARSE.GRAPH (LIST THEORY)
				      #'(lambda (x) (remove-if #'(lambda (spec)
								   (EQ (TYPE-OF SPEC) 'DED*INPUT))
							       (DED=THEORY.SUB.THEORIES x)))
				      #'(lambda  (x)
					  (let ((status (ded=theory.status x)))
					    (pr-parse.closure 
					     (PR-PARSE.STRING (FORMAT NIL " ~A" (DED=THEORY.STRING x))
							     :font 'bold :size 'S
							     :colour (COND ((eq status 'passive) "DarkGrey")
									   ((DED=THEORY.MAPPING X) "DarkRed")
									   (T "DarkGreen")))
					     (cond ((DED=THEORY.MAPPING X) 'oval) (t 'boxed))
					     (cond ((eq status 'active) 2) (t -2))
					     "White" 3
					     :double.left `(DED=THEORY.DESCRIBE (quote ,x))
					     :right `(DED=THEORIES.ACT (QUOTE ,X))))))
		      'boxed 2 "LightGrey" 3 :font 'bold :size 'S)))
  

(DEFUN DED=THEORIES.ACT (THEORY)

  (case (car (WIN-MN.POPUP (win-window 'description_2)
			   '(("Select subgraph" . 1)
			     ("Replace Theory Specification" . 2)
			     ("Insert Axiom / Lemma" . 3)
			     ("Insert new subtheory" . 4)
			     ("Delete theory" . 5)
			     ("Rename theory" . 6))))
	(1 (DED=theory.act.activate THEORY))
	;(2 (ded=theory.act.get.theory THEORY))
	;(3 (ded=theory.act.insert.spec theory))
	;(4 (ded=theory.act.insert.theory theory))
	;(5 (ded=theory.act.delete.theory theory))
	; (6 (ded=theory.act.rename.theory))
	(otherwise nil)))



(DEFUN DED=THEORY.DESCRIBE (THEORY)

   (PR-PARSE.HEADLINE (FORMAT NIL "~A  (Specification and lemmatas):" (DED=THEORY.STRING THEORY))
		      (PR-PARSE.ITEMIZE
		       (NCONC (COND ((DED=THEORY.AXIOMS THEORY)
				     (CONS (PR-PARSE.STRING (FORMAT NIL "Specification of ~A:" (DED=THEORY.STRING THEORY)))
					   (MAPCAN #'(LAMBDA (SPEC)
						       (COND ((EQ (TYPE-OF SPEC) 'DED*INPUT)
							      (LIST (DED=FORMULA.DESCR SPEC)))))
						   (DED=THEORY.AXIOMS THEORY))))
				    (T (LIST (PR-PARSE.STRING "Theory has an empty specification"))))
			      (COND ((DED=THEORY.LEMMATA THEORY)
				     (CONS (PR-PARSE.STRING (FORMAT NIL "Lemmata of ~A:" (DED=THEORY.STRING THEORY)))
					   (MAPCAN #'(LAMBDA (SPEC)
						       (COND ((EQ (TYPE-OF SPEC) 'DED*INPUT)
							      (LIST (DED=FORMULA.DESCR SPEC)))))
						   (DED=THEORY.LEMMATA THEORY))))
				    (T  (LIST (PR-PARSE.STRING "Theory contains no lemmata")))))
		       nil :font 'bold :size 'D)))


(DEFUN DED=THEORY.STRING (OBJECT)

  ;;; Input:  a object of type \verb$DED*THEORY$
  ;;; Value:  a string representing the name or a description of the given \verb$OBJECT$

  (COND ((DED=THEORY.NAME OBJECT))
	((DED=THEORY.MAPPING OBJECT)
	 (COND ((AND (NULL (DED=THEORY.SUB.THEORIES OBJECT))
		     (DED=THEORY.SUB.THEORIES OBJECT)
		     (DED=THEORY.MAPPING (CAR (DED=THEORY.SUB.THEORIES OBJECT))))
		(DED=THEORY.STRING (CAR (DED=THEORY.SUB.THEORIES OBJECT))))
	       ((DED=THEORY.SUB.THEORIES OBJECT)
		(FORMAT NIL "a mapping of~{ ~A~}" (MAPCAR #'(LAMBDA (OBJ) (DED=THEORY.STRING OBJ))
							  (DED=THEORY.SUB.THEORIES OBJECT))))))))


(DEFUN DED=FORMULA.DESCR (POINTER)
  
  (PR-PARSE.ITEMIZE (CONS (COND ((SOME #'(LAMBDA (X) X) (DED=INPUT.PROOFS POINTER))
				 (pr-parse.float.text
				  (list (PR-PARSE.STRING (DED=INPUT.NAME POINTER))
					(PR-PARSE.STRING "     ")
					(PR-PARSE.Closure (PR-PARSE.STRING "Enter Proofs") 'boxed 1 "LightRed" 3
							  :double.left 
							  `(EDT-HANDLE.ENTER.PROOFS
							    (QUOTE ,(CAR (REMOVE NIL (DED=INPUT.PROOFS POINTER)))))))))
				(T (PR-PARSE.STRING (DED=INPUT.NAME POINTER) :style 'UNDERLINE)))
			  (MAPCAN #'(LAMBDA (STRING)
				      (MAPCAR #'(LAMBDA (STR) (PR-PARSE.STRING STR 'FIXROMAN 'S))
					      (DED=FORMULA.PRINT STRING)))
				  (DED=INPUT.PNAME POINTER)))
		    NIL
		    :font 'bold :size 'S))



(DEFUN DED=FORMULA.PRINT (STRING &OPTIONAL (OFFSET 0) ADD.FLAG)

  (COND ((< (LENGTH STRING) (+ 120 OFFSET))
	 (LIST (COND (ADD.FLAG (FORMAT NIL "   ~A" (SUBSEQ STRING OFFSET)))
		     (T (SUBSEQ STRING OFFSET)))))
	(T (LET ((POS (COND ((POSITION #\SPACE STRING :START (+ 100 OFFSET) :END (+ 120 OFFSET)))
			    ((POSITION #\SPACE STRING :START (+ 80 OFFSET) :END (+ 100 OFFSET)))
			    (T (+ 120 OFFSET)))))
	     (CONS (COND (ADD.FLAG (FORMAT NIL  "   ~A" (SUBSEQ STRING OFFSET POS)))
			 (T (SUBSEQ STRING OFFSET POS)))
		   (DED=FORMULA.PRINT STRING POS T))))))


(DEFUN DED=FUNCTION.DESCRIBE ()
  (LET (SYMBOLS INPUT)
    (SETQ SYMBOLS (SORT (MAPCAR #'(LAMBDA (FCT)
				    (CONS (FORMAT nil "~A ( ~{~A ~} ) : ~A" (DA-FUNCTION.PNAME FCT)
						  (DA-FUNCTION.DOMAIN.SORTS FCT) (DA-FUNCTION.SORT FCT))
					  FCT))
				(DB-FUNCTION.ALL))
			 'STRING-LESSP :KEY 'CAR))
    (COND ((SETQ INPUT (WIN-MN.CHOOSE (WIN-WINDOW 'DESCRIPTION_2) SYMBOLS))
	   (PR-GRAPHIC.INTERACT (WIN-WINDOW 'DESCRIPTION_2) `(DED=PREFUN.DESCRIBE (QUOTE ,(CAR INPUT))))))))


(DEFUN DED=PREDICATE.DESCRIBE ()

  (LET (SYMBOLS INPUT)
    (SETQ SYMBOLS (SORT (MAPCAN #'(LAMBDA (FCT)
				    (COND ((NOT (DA-PREDICATE.IS.EQUALITY FCT))
					   (LIST (CONS (FORMAT nil "~A ( ~{~A ~} )" (DA-PREDICATE.PNAME FCT)
							       (DA-PREDICATE.DOMAIN.SORTS FCT))
						       FCT)))))
				(DB-PREDICATE.ALL))
			'STRING-LESSP :KEY 'CAR))	  
    (COND ((SETQ INPUT (WIN-MN.CHOOSE (WIN-WINDOW 'DESCRIPTION_2) SYMBOLS))
	   (PR-GRAPHIC.INTERACT (WIN-WINDOW 'DESCRIPTION_2) `(DED=PREFUN.DESCRIBE (QUOTE ,(CAR INPUT))))))))
				     


(DEFUN DED=SORT.DESCRIBE ()

  (LET (SYMBOLS INPUT)
    (SETQ SYMBOLS (SORT (MAPCAR #'(LAMBDA (SORT)
				    (CONS (DA-SORT.PNAME SORT) SORT))
				(DA-SORT.ALL.SUBSORTS (DP-SORT.TOP.LEVEL.SORT)))
			'STRING-LESSP :KEY 'CAR))  
    (COND ((SETQ INPUT (WIN-MN.CHOOSE (WIN-WINDOW 'DESCRIPTION_2) SYMBOLS))
	   (PR-GRAPHIC.INTERACT (WIN-WINDOW 'DESCRIPTION_2) `(DED=SORT.DESCRIBE.SINGLE (QUOTE ,(CAR INPUT))))))))

  
(DEFUN DED=SORT.DESCRIBE.SINGLE (SORT)

  ;;; Input:   a sort 
  ;;; Effect:  describes the sort with all its subsorts.
  ;;; Value:   a print-object.

  (PR-PARSE.HEADLINE (FORMAT NIL "Sort lattice of the datastructure ~A" SORT)
		     (PR-PARSE.CLOSURE (DED=SORT.DESCR.TREE SORT) 'BOXED 3 "" 0 :font 'bold :size 'D)
		     'CENTERED))


(DEFUN DED=SORT.DESCR.TREE (SORT)

  ;;; Input:   a sort
  ;;; Effect:  describes the sort with all its subsorts.
  ;;; Value:   a print-object.
  
  (COND ((DA-SORT.DIRECT.SUBSORTS SORT)
	 (PR-PARSE.TREE (PR-PARSE.CLOSURE (PR-PARSE.STRING (DA-SORT.PNAME SORT)) 'BOXED 2)
			(MAPCAR #'(LAMBDA (EDGE)
				    (DECLARE (IGNORE EDGE)) NIL)
				(DA-SORT.DIRECT.SUBSORTS SORT))
			(MAPCAR #'(LAMBDA (EDGE)
				    (DED=SORT.DESCR.TREE EDGE))
				(DA-SORT.DIRECT.SUBSORTS SORT))))
	(T (PR-PARSE.CLOSURE (PR-PARSE.STRING (DA-SORT.PNAME SORT)) 'BOXED 2))))


(DEFUN DED=PREFUN.DESCRIBE (PREFUN)

  (LET ((ATTRIBUTES (DA-PREFUN.ATTRIBUTES PREFUN))
	(WFO.SUGS (DA-PREFUN.WFO.SUGGESTED PREFUN))
	(ARG.LIMITED (COND ((DA-FUNCTION.IS PREFUN) (DA-FUNCTION.ARG.LIMITED PREFUN))))
	(DEFINING.SYMBOLS (REMOVE PREFUN (DA-PREFUN.DEFINING.SYMBOLS PREFUN)))
	(HEADER (DED=PREFUN.HEADER PREFUN)))
    (PR-PARSE.HEADLINE
     HEADER
     (PR-PARSE.ITEMIZE
      (NCONC (LIST (PR-PARSE.STRING " ")
		   (PR-PARSE.STRING (FORMAT NIL "~A is a ~A~A ~A symbol"
					    PREFUN
					    (COND ((GETF ATTRIBUTES 'RECURSIVE) "recursive ") (t ""))
					    (COND ((GETF ATTRIBUTES 'SEL.STRUCTURE) "selector")
						  ((GETF ATTRIBUTES 'INDEX.FCT) "index")
						  ((GETF ATTRIBUTES 'DEFINED) "(user) defined")
						  ((GETF ATTRIBUTES 'STRUCTURE) "constructor")
						  (T "inconstructive"))
					    (COND ((DA-FUNCTION.IS PREFUN) "function")
						  (T "predicate"))))
		   (PR-PARSE.FLOAT.TEXT (MAPCAN #'(LAMBDA (WFO.SUG)
						    (MAPCAR #'(LAMBDA (STRING) (PR-PARSE.STRING STRING 'ROMAN 'D))
							    (GETF (DA-WFO.ATTRIBUTES (DA-WFOSUG.WFO WFO.SUG)) 'DESCRIPTION)))
						WFO.SUGS)))
	     (LIST (PR-PARSE.STRING (FORMAT NIL "It is defined in the theory ~A ~:[(which is currently not activated)~;~]"
					    (DED=THEORY.STRING (DED=INPUT.THEORY (DA-OBJECT.DEFINING.INPUT PREFUN)))
					    (DED-INPUT.IS.ACTIVE (DA-OBJECT.DEFINING.INPUT PREFUN)))))
	     (COND (ARG.LIMITED
		    (LIST (PR-PARSE.FLOAT.TEXT
			   (CONS (PR-PARSE.STRING (FORMAT NIL " - ~A is p-bounded " PREFUN))
				 (MAPCON #'(LAMBDA (ARG.LIMIT)
					     (LIST (PR-PARSE.STRING
						    (FORMAT NIL "on the ~:R argument with difference predicate "
							    (CAAR ARG.LIMIT)))
						   (PR-PARSE.STRING (DA-SYMBOL.PNAME (SECOND (CAR ARG.LIMIT)))
								    :double.left `(DED=PREFUN.DESCRIBE 
										   (QUOTE ,(SECOND (CAR ARG.LIMIT)))))
						   (PR-PARSE.STRING (COND ((NULL (CDR ARG.LIMIT)) ".")
									  (T " and ")))))
					 ARG.LIMITED))
			   (PR-DEFAULT.WIDTH)))))
	     (COND (DEFINING.SYMBOLS
		     (LIST (PR-PARSE.FLOAT.TEXT
			    (CONS (PR-PARSE.STRING
				   (FORMAT NIL " - ~A is defined with the help of the prefun~P "
					   PREFUN (LENGTH DEFINING.SYMBOLS)))
				  (MAPCON #'(LAMBDA (FUNC)
					      (LIST (PR-PARSE.STRING (DA-SYMBOL.PNAME (CAR FUNC))
								     :font 'BOLD
								     :double.left `(DED=PREFUN.DESCRIBE (quote ,(CAR FUNC))))
						    (PR-PARSE.STRING (COND ((NULL (CDR FUNC)) ".")
									   ((NULL (CDDR FUNC)) " and ")
									   (T ", ")))))
					  DEFINING.SYMBOLS))
			    (PR-DEFAULT.WIDTH)))))
	     (LIST (PR-PARSE.string " " :font 'bold)
		   (PR-PARSE.STRING "More informations are available about" :font 'ITALIC)
		   (pr-parse.itemize 
		    (nconc (list (PR-PARSE.STRING "its specification" :font 'BOLD
						  :double.left `(DED=PREFUN.DESCRIBE.DEFINITION
								 (QUOTE ,PREFUN)))
				 (PR-PARSE.STRING "its attributes" :font 'BOLD
						  :double.left `(DED=PREFUN.DESCRIBE.ATTRIBUTES
								 (QUOTE ,PREFUN) (QUOTE ,HEADER)))
				 (PR-PARSE.STRING "formulas using this symbol" :font 'BOLD
						  :double.left `(DED=PREFUN.DESCRIBE.FORMULAS
								 (QUOTE ,PREFUN))))
			   (cond ((da-predicate.is prefun)
				  (list (PR-PARSE.STRING "modifier using this symbol" :font 'BOLD
							 :double.left `(DED=PREFUN.DESCRIBE.MODIFIERS (QUOTE ,PREFUN)))))
				 ((da-function.is prefun)
				  (list (PR-PARSE.STRING 
					 "variable equations (x = ...) for the range sort of this symbol" 
					 :font 'bold :double.left `(DED=PREFUN.DESCRIBE.VARIABLE.EQUATIONS 
								    (QUOTE ,PREFUN))))))
			   (COND (WFO.SUGS
				  (LIST (PR-PARSE.STRING "its recursion/ induction ordering" :font 'bold
							 :double.left `(DED=PREFUN.DESCRIBE.RECURSION
									(QUOTE ,PREFUN)))))))
		    'itemize)))
      nil :font 'roman :size 'D))))


(DEFUN DED=PREFUN.DESCRIBE.DEFINITION (PREFUN)

  (PR-PARSE.HEADLINE
   (FORMAT NIL "Specification of ~A" PREFUN)
   (PR-PARSE.ITEMIZE
    (nconc (LIST (cond ((DA-PREFUN.DEFINING.INPUT PREFUN)
			(PR-PARSE.CLOSURE
			 (PR-PARSE.ITEMIZE (MAPCAR #'(LAMBDA (TEXT) (PR-PARSE.STRING TEXT))
						   (DED=INPUT.PNAME (DA-PREFUN.DEFINING.INPUT PREFUN)))
					   NIL)
			 'BOXED 2))
		       (t (PR-PARSE.STRING " ")))
		 (PR-PARSE.STRING " ")
		 (PR-PARSE.STRING " "))
	   (COND ((DA-PREFUN.DEFINITION PREFUN)
		  (LIST (PR-PARSE.string " ")
			(PR-PARSE.STRING "More informations are available about" :font 'ITALIC)
			(PR-PARSE.STRING "- its definition tree" :font 'BOLD
					:double.left `(DED=PREFUN.DESCR.DEF.TREE (QUOTE ,PREFUN)))))))
    NIL :font 'roman :size 'D)))


(DEFUN DED=PREFUN.DESCRIBE.FORMULAS (PREFUN)

  (LET ((FORMULAS (DB-PREFUN.FORMULAS.ALL PREFUN)))
    (setq formulas (cond ((da-function.is prefun)
			  (sort formulas #'(lambda (x y) (string< (da-modifier.pname x) (da-modifier.pname y)))))
			 ((da-predicate.is prefun)
			  (sort formulas #'(lambda (x y) (string< (da-gterm.pname x) (da-gterm.pname y)))))))
    (PR-PARSE.HEADLINE
     (FORMAT NIL "Formulas about ~A" PREFUN)
     (PR-PARSE.ITEMIZE
      (COND (FORMULAS
	     (MAPCAR #'(LAMBDA (FORMULA)
			 (cond ((da-function.is prefun)
				(pr-parse.modifier FORMULA nil))
			       ((da-predicate.is prefun)
				(pr-parse.gterm formula nil))))
		     FORMULAS))
	    (T (LIST (PR-PARSE.STRING (FORMAT NIL "No formulas known about ~A" PREFUN)))))
      (COND (FORMULAS (MAPCAR #'(LAMBDA (FORMULA) 
				  (FORMAT NIL "~A:"
					  (cond ((da-function.is prefun) (DA-MODIFIER.PNAME FORMULA))
						((da-predicate.is prefun) (da-gterm.pname formula)))))
			      FORMULAS)))
      :font 'roman :size 'D))))


(DEFUN DED=PREFUN.DESCRIBE.VARIABLE.EQUATIONS (PREFUN)
  
  (PR-PARSE.HEADLINE
   (FORMAT NIL "Variable equations for the range sort of the symbol ~A" PREFUN)
   (PR-PARSE.ITEMIZE (DB-MODIFIER.COLLECTION
		      (DA-SYMBOL.SORT PREFUN) 'VARIABLE NIL
		      #'(LAMBDA (FORMULA)
			  (LIST (pr-parse.modifier formula nil))))
		     (DB-MODIFIER.COLLECTION
		      (DA-SYMBOL.SORT PREFUN) 'VARIABLE NIL
		       #'(LAMBDA (FORMULA) (list (FORMAT NIL "~A:" (DA-MODIFIER.PNAME FORMULA)))))
		     :size 'D)))


(DEFUN DED=PREFUN.DESCRIBE.MODIFIERS (PREFUN)
  (LET ((MODIFIERS (DB-prefun.modifier.all prefun)))
    (setq modifiers (sort modifiers #'(lambda (x y) (string< (da-modifier.pname x) (da-modifier.pname y)))))
    (PR-PARSE.HEADLINE
     (FORMAT NIL "Modifiers about ~A" PREFUN)
     (PR-PARSE.ITEMIZE
      (COND (MODIFIERS
	     (MAPCAN #'(LAMBDA (FORMULA)
			 (LIST (PR-PARSE.STRING (FORMAT NIL "~A:" (DA-MODIFIER.PNAME FORMULA)))
			       (PR-PARSE.ITEMIZE (MAPCAR #'(LAMBDA (STRING)
							     (PR-PARSE.STRING STRING :font 'FIXROMAN))
							 (PR-PRINT.MODIFIER FORMULA))
						 NIL)))
		     MODIFIERS))
	    (T (LIST (PR-PARSE.STRING (FORMAT NIL "No modifiers known about ~A" PREFUN)))))
      'itemize :font 'bold :size 'D))))


(DEFUN DED=PREFUN.DESCR.DEF.TREE (PREFUN)

  (PR-PARSE.HEADLINE
   (FORMAT NIL "Definition tree of ~A" PREFUN)
   (PR-PARSE.CLOSURE (DED=PREFUN.DESCR.DEFINITION.BOX (DA-PREFUN.DEFINITION PREFUN))
		     'BOXED 2 "LightGrey" 3 :font 'roman :size 'D)))


(DEFUN DED=PREFUN.DESCR.DEFINITION.BOX (DEFINITION)
  
  (COND ((DA-GTERM.DEF.IS.VALUE DEFINITION)
	 (PR-PARSE.CLOSURE
	  (COND ((OR (NOT (DA-LITERAL.IS DEFINITION))
		     (DA-PREDICATE.IS.EQUALITY (DA-LITERAL.SYMBOL DEFINITION)))
		 (PR-parse.gterm (cond ((DA-LITERAL.IS DEFINITION)
					(SECOND (DA-GTERM.TERMLIST DEFINITION)))
				       (t (da-formula.junction.closure
					   'OR (CDR (DA-GTERM.TERMLIST
						     (SECOND (DA-GTERM.TERMLIST DEFINITION)))))))
				 50))
		((DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN DEFINITION))
		 (PR-PARSE.STRING "True"))
		(T (PR-PARSE.STRING "False")))
	  'BOXED 2 "White" 3))
	(T (PR-PARSE.TREE NIL
			  (MAPCAR #'(LAMBDA (DEF.TERM)
				      (PR-PARSE.ITEMIZE
				       (MAPCAR #'(LAMBDA (formula)
						   (PR-PARSE.gterm (da-formula.negate formula) 50))
						(DA-GTERM.DEF.CONDITION DEF.TERM))
				       nil))
				  (DA-GTERM.TERMLIST DEFINITION))
			  (MAPCAR #'(LAMBDA (DEF.TERM)
				      (DED=PREFUN.DESCR.DEFINITION.BOX (DA-GTERM.DEF.VALUE DEF.TERM)))
				  (DA-GTERM.TERMLIST DEFINITION))))))


(DEFUN DED=PREFUN.DESCRIBE.RECURSION (PREFUN)

  (PR-PARSE.HEADLINE
   (FORMAT NIL "Induction-Scheme(s) of ~A" PREFUN)
   (COND ((DA-PREFUN.WFO.SUGGESTED PREFUN) 
	  (PR-PARSE.closure
	   (pr-parse.itemize (MAPCAR #'(LAMBDA (WFO.SUG)
					 (DED=PREFUN.DESCR.REC.SCHEME (DA-WFO.TREE (DA-WFOSUG.WFO WFO.SUG))))
				     (DA-PREFUN.WFO.SUGGESTED PREFUN))
			     NIL)
	   'BOXED 2 "LightGrey" 0 :font 'bold))
	 (T (PR-PARSE.CLosure (PR-PARSE.STRING (FORMAT NIL "~A suggests no induction scheme" PREFUN))
			      'BOXED 2 "LightRed" 3 :font 'bold)))))


(DEFUN DED=PREFUN.DESCR.REC.SCHEME (TREE)

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
								    (PR-PARSE.gterm 
								     (da-formula.negate formula) 50 nil
								     :colour (cond ((DA-WFO.TREE.IS.ESSENTIAL tree)
										    "DarkBlue")
										   (T "DarkRed"))))
								(CDR CASE))
							nil :font 'roman))
				  (DA-WFO.TREE.SUBNODES TREE))
			  (MAPCAR #'(LAMBDA (CASE)
				      (DED=PREFUN.DESCR.REC.SCHEME (CAR CASE)))
				  (DA-WFO.TREE.SUBNODES TREE))))))


(DEFUN DED=PREFUN.DESCRIBE.ATTRIBUTES (PREFUN HEADER)

  (LET (STRINGS (pname (da-prefun.pname prefun)))
    (SMAPL #'(LAMBDA (INDICATOR)
	      (CASE (car INDICATOR)
		    (ASSOCIATIVE (PUSH (PR-PARSE.STRING (FORMAT NIL "~A is associative" pname))
				       STRINGS))
		    (COMMUTATIVE (PUSH (PR-PARSE.STRING (FORMAT NIL "~A is commutative" pname))
				       STRINGS))
		    (INVERSE (PUSH (PR-PARSE.STRING (FORMAT NIL "~A has an inverse function" pname))
				   STRINGS))
		    (NULL (PUSH (PR-PARSE.STRING 
				 (FORMAT NIL "~A has ~A as a null-element" pname
					 (DA-PREFUN.PNAME (car (da-attribute.arguments (car (second indicator)))))))
				STRINGS))
		    (IDENTITY (PUSH (PR-PARSE.STRING 
				     (FORMAT NIL "~A is the identity with respect to ~A" 
					 (DA-PREFUN.PNAME (car (da-attribute.arguments (car (second indicator)))))
					 pname))
				    STRINGS))))
	   #'CDDR
	  (DA-PREFUN.ATTRIBUTES PREFUN))
    (PR-PARSE.HEADLINE
     HEADER
     (COND (STRINGS (PR-PARSE.ITEMIZE STRINGS NIL :font 'roman))
	   (T (PR-PARSE.CLOSURE (PR-PARSE.STRING (FORMAT NIL "No attributes are known for ~A" (DA-PREFUN.PNAME PREFUN))
						 :font 'bold)
				'boxed 2))))))
		    
				 


(DEFUN DED=PREFUN.HEADER (PREFUN)

  (FORMAT NIL "~{~A~}"
	  (NCONC (LIST (DA-PREFUN.PNAME PREFUN))
		      (COND ((DA-PREFUN.DOMAIN.SORTS PREFUN)
			     (CONS "( " (MAPCON #'(LAMBDA (SORTS)
						    (LIST (COND ((CDR SORTS)
								 (FORMAT NIL "~A X "
									 (DA-SORT.PNAME (CAR SORTS))))
								(T (FORMAT NIL "~A )"
									   (DA-SORT.PNAME (CAR SORTS)))))))
						(DA-PREFUN.DOMAIN.SORTS PREFUN)))))
		      (COND ((DA-FUNCTION.IS PREFUN)
			     (LIST (FORMAT NIL " -> ~A" (DA-SORT.PNAME (DA-FUNCTION.SORT PREFUN)))))))))





(defun DED=THEORY.PRINT (object STREAM DEPTH)

  ;;; Input:   an object, a stream and a number
  ;;; Effect:  prints \verb$GTERM$ on the denoted \verb$STREAM$ until the gterm-depth do not
  ;;;          exceed \verb$DEPTH$.
  ;;; Value:   undefined
  
  (COND ((AND *PRINT-LEVEL* (> DEPTH *PRINT-LEVEL*)) (FORMAT STREAM "#"))
	(T (FORMAT STREAM "<~A" (COND ((ded=theory.name object))
				      ((ded=theory.mapping object) "inst-of")))
	   (let ((args (remove-if-not #'(lambda (x) (eq (type-of x) 'ded*theory))
				      (ded=theory.SUB.THEORIES object))))
	     (cond (args  (FORMAT STREAM "(~{~A ~})" args))))
	   (FORMAT STREAM ">"))))





(defun DED=THEORY.ACT.ACTIVATE (NEW.THEORY)

  (DED=THEORY.MARK NEW.THEORY 'REACHABLE 'REACHABLE #'(lambda (x y) (NEQ x y)))
  (DED=THEORY.MARK DED*THEORY.ACTUAL 'ACTIVE 'PASSIVE 'EQ)
  (DED=THEORY.MARK NEW.THEORY 'REACHABLE 'ACTIVE 'EQ)
  (SETQ DED*THEORY.ACTUAL NEW.THEORY)
  NIL)


(DEFUN DED=THEORY.MARK (THEORY OLD.ATTRIBUTE NEW.ATTRIBUTE TEST.FCT)

  (COND ((FUNCALL TEST.FCT (DED=THEORY.STATUS THEORY) OLD.ATTRIBUTE)
	 (SETF (DED=THEORY.STATUS THEORY) NEW.ATTRIBUTE)
	 (MAPC #'(LAMBDA (SUCC) (DED=THEORY.MARK SUCC OLD.ATTRIBUTE NEW.ATTRIBUTE TEST.FCT))
	       (DED=THEORY.SUB.THEORIES THEORY)))))


