;;; -*- Syntax: Common-lisp; Package: INKA; Mode: LISP; Base: 10 -*-

(IN-PACKAGE :inka)

;;;;;    **************************************************************
;;;;;    *                                                            *
;;;;;    * The EDITOR of the INKA-System.   (DIALOG-MANAGER)          *
;;;;;    * =================================================          *
;;;;;    *                                                            *
;;;;;    **************************************************************


(DEFVAR EDT*HARDCOPY NIL)
(DEFVAR EDT*DEBUGGING NIL)
(DEFVAR EDT*INVISIBLE NIL)

(DEFVAR EDT*DB.IN.PROCESS NIL)
(DEFVAR EDT*PROOF.RESULT NIL)
(DEFVAR EDT*ERROR.MESSAGES NIL)
(DEFVAR EDT*DESCRIPTION.IN.PROCESS NIL)

(DEFVAR EDT*WRITING.DISABLED NIL)

(DEFVAR EDT*INTERACTION.PROCESS NIL)
(DEFVAR EDT*DESCRIPTION.PROCESS NIL)
(DEFVAR EDT*MAIN.PROCESS NIL)

(DEFVAR EDT*AXIOMS.PROHIBITED NIL)

(DEFVAR EDT*SAVEPROOF NIL)
(DEFVAR EDT*EXAMINE.PROOF NIL)

(DEFVAR INKA*CORRUPTED NIL)


(DEFUN @INKA ()
  
  ;;;  edited at 20-07-87
  ;;;  Input:  -
  ;;;  Effect: top level function for the INKA-system. Necessary windows are created or reset if already 
  ;;;          existent. Enters the command loop of the INKA system. 
  ;;;  Value:  undefined.


  (EDT=WITH.EXIT
   (UNWIND-PROTECT (PROGN (EDT=INIT :INKA)
			  (SETQ EDT*AXIOMS.PROHIBITED NIL)
			  (DED-RESET)
			  (EDT=START))
     (PROGN (SETQ EDT*DB.IN.PROCESS NIL)
	    (COND ((NULL EDT*DEBUGGING)
		   (EDT=STOP)
		   (pro-QUIT)))))))

  
(DEFUN @ ()
  ;;; Input: none
  ;;; Effect: resets the inka system

    (EDT=WITH.EXIT
     (EDT=START)))


(DEFUN INKA-INIT ()
  
  ;;; Input: none
  ;;; Effect: initialization of the inka system

    (EDT=WITH.EXIT
     (LET ((*PACKAGE* (FIND-PACKAGE :INKA)))
       (EDT=INIT 'KIV)
       (SETQ EDT*AXIOMS.PROHIBITED T)
       (DED-RESET))))


(DEFUN INKA-STOP ()
  
  ;;; Input: none
  ;;; Effect: quits the inka system

    (EDT=WITH.EXIT
     (SETQ EDT*DB.IN.PROCESS NIL)
     (EDT=STOP)))


(DEFUN INKA-RESET ()
  
  ;;; Input: none
  ;;; Effect: resets the inka system

  (EDT=WITH.EXIT
   (LET ((EDT*AXIOMS.PROHIBITED NIL))
     (DED-RESET))))


(DEFUN INKA-ERRORS ()
  
  ;;; Input: none
  ;;; Effect: yiels all error messages since last call of this function

  (EDT=WITH.EXIT
   (PROG1 EDT*ERROR.MESSAGES
     (SETQ EDT*ERROR.MESSAGES NIL))))


(DEFMACRO INKA-WITH.MAPPINGS (MAPPING &REST BODY)

  ;;; Input:    a list of dotted pairs of strings denoting a replacements of strings
  ;;;           and a list of sexpressions
  ;;; Effect:   \verb$BODY$ is evaluated according to the given \verb$MAPPING$.
  ;;; Value:    the value of evaluation of \verb$BODY$.

  `(DED-WITH.MAPPING ,MAPPING ,BODY))


(DEFUN INKA-FORMULA.PROVE (FORMULA QUIET TIME)

  ;;; Input:   a formula, a flag and a natural number
  ;;; Effect:  tries to prove \verb$FORMULA$ wrt the actual database. If \verb$QUIET$ is t no
  ;;;          user interaction is done and the prover is started for almost \verb$TIME$
  ;;;          seconds
  ;;; Value:   T, iff \verb$FORMULA$ could be proven.

  (EDT=WITH.EXIT
   (let* ((*PACKAGE* (find-package :inka)) errors)
     (with-standard-io-syntax 
      (SETQ EDT*PROOF.RESULT NIL)
      (rl-prot.level.set -1)
      (COND ((NOT QUIET)
	     (LET ((EDT*INVISIBLE NIL))
	       (win-io.print.status (win-window 'main) "")
	       (WIN-WINDOW.WINDOWS.EXPOSE)
	       (EDT=START FORMULA)
	       (WIN-WINDOW.WINDOWS.SHADOW)))
	    (T (PRO-PROCESS.CREATE :NAME "STOP INKA" :FUNCTION #'(LAMBDA ()
								   (SLEEP (MAX 0 (- TIME 0.5)))
								   (EDT=DO.INTERRUPT 'NO.QUESTIONS)))
	       (MULTIPLE-VALUE-SETQ (EDT*PROOF.RESULT errors)
		 (DED-FORMULA.PROVE FORMULA T))
	       (COND (ERRORS (EDT=FORMULA.COMPILE.ERROR FORMULA errors))))))
     EDT*PROOF.RESULT)))
  

(DEFUN INKA-FORMULA.INSERT (FORMULA &OPTIONAL AXIOMS PROOFS)
  
  ;;; Input:  a vector of strings, a list of gterms, and a list of strings denoting the saved proofs of the specified axioms
  ;;; Effect: the object denoted by \verb$FORMULA$ is tried to be inserted into the database, for necessary proof \verb$AXIOMS$
  ;;;         can be used as axioms
  ;;; Value:  NIL, if \verb$FORMULA$ could be successfully inserted, an error message else

  (EDT=WITH.EXIT
   (LET* ((*PACKAGE* (find-package :inka)) (EDT*AXIOMS.PROHIBITED NIL) RESULT)
     (setq formula (edt=formula.replace.newlines formula))
     (COND ((and (NOT EDT*INVISIBLE) (not edt*writing.disabled))
	    (WIN-IO.CLEAR (WIN-WINDOW 'PROOF))
	    (win-io.print (format nil "Inserting Formula ..... ")
			  (win-window 'proof))
	    (mapcar #'(LAMBDA (STRING) 
			(win-io.print (format nil "~A" STRING)
				      (win-window 'proof)))
		    formula)))
     (SETQ RESULT (DED-FORMULA.INSERT (EDT=FORMULA.REMOVE.EMPTY.LINES FORMULA) AXIOMS NIL PROOFS))
     (cond ((AND (integerp (second result))
		 (NULL (COM-ACTUAL.MAPPING))) ; no error possible when INKA is called using
					; this function under a mapping
					; since then it is assumed the input is already loaded in INKA !!!
	    (EDT=FORMULA.COMPILE.ERROR FORMULA RESULT))))))
  

(DEFUN INKA-FORMULA.DELETE ()
  
  ;;; Input:  none
  ;;; Effect: the last object inserted into the database (using \verb$INKA-FORMULA.INSERT$) is deleted

  (EDT=WITH.EXIT
   (LET ((EDT*AXIOMS.PROHIBITED NIL))
     (WIN-IO.CLEAR (WIN-WINDOW 'PROOF))
     (DED-FORMULA.DELETE))))
  

(DEFUN INKA-EXPAND (FILE)
  
  ;;; Input:  a filename
  ;;; Effect: loads the specified database \verb$FILE$ without reseting the actual database
  
  (EDT=WITH.EXIT
   (LET ((EDT*AXIOMS.PROHIBITED NIL)
	 (EDT*WRITING.DISABLED T))
     (WIN-IO.CLEAR (WIN-WINDOW 'PROOF))
     (DED-EXPAND FILE))))


(DEFUN INKA-SAVE (FILE)
  
  ;;; Input:  a filename
  ;;; Effect: saves the actual database in \verb$FILE$

  (EDT=WITH.EXIT
   (LET ((EDT*AXIOMS.PROHIBITED NIL))
     (DED-SAVE FILE))))


(DEFUN INKA-LOAD (FILE)
  ;;; Input:  a filename
  ;;; Effect: loads the specified database \verb$FILE$ with reseting the actual database before

  (EDT=WITH.EXIT
   (LET ((EDT*AXIOMS.PROHIBITED NIL)
	 (EDT*WRITING.DISABLED T))
     (DED-LOAD FILE))))


(DEFUN EDT-INTERACTIVE ()
  ;;; Input: none
  ;;; Value: the number of the process which reads the command pipe
  
  EDT*INTERACTION.PROCESS)


(DEFUN EDT-AXIOMS.PROHIBITED ()

  ;;; Input: none
  ;;; Value: either T or NIL depending on whether inka is called within VSE, then axioms are not allowed to be deleted, or not

  EDT*AXIOMS.PROHIBITED)


(DEFUN EDT-ERROR.INSERT (FLAG STRING)
  
  ;;; Note: function will be removed in a future release
  
  (PUSH (CONS FLAG STRING) EDT*ERROR.MESSAGES))


(DEFUN EDT-INVISBLE ()

  ;;; Input: none
  ;;; Value: T or NIL, depending on whether INKA is called visible or not

  EDT*INVISIBLE)


(DEFUN EDT-HANDLE.ENTER.PROOFS (FILE)
  ;;; Edited : 23.06.94 by CS
  ;;; Input  : a file
  ;;; Effect : if there is no proof in process then the proof stored in \verb$FILE$ is examined
  ;;;          else a message is written to the status line

  (COND (EDT*DB.IN.PROCESS (WIN-IO.PRINT.STATUS (WIN-WINDOW 'DESCRIPTION_2) "Sorry, there is still a proof in process"))
	(T (PROG2 (SETQ EDT*EXAMINE.PROOF T)
		  (SEL-PROOF.EXAMINE FILE)
		  (SETQ EDT*EXAMINE.PROOF NIL)))))


(DEFUN EDT-SAVE.PROOF.FINISHED ()
  ;;; Edited : 23.06.94 by CS
  ;;; Input  : none
  ;;; Effect : save proof is finished, the variable denoting the filename of the proof
  ;;;          is set back to NIL

  (SETQ EDT*SAVEPROOF NIL))



(DEFUN EDT-PROOF.SAVE.FILE ()

  ;;; Input: none
  ;;; Value: the name of the file the actual proof is saved

  EDT*SAVEPROOF)


(DEFUN EDT-MAIN.PROCESS ()

  ;;; Value:  the process of the calling system.
  
  EDT*MAIN.PROCESS)



(DEFUN EDT-ERROR.OCCURED ()

  ;;; Effect:  stops immediately the INKA-processes

  (FORMAT T "Notice: ~%~%Window Manager died suddenly.~%Leaving INKA without restoring the database.~%")
  (FORMAT T "INKA - database  c o r r u p t e d ~%Exit the system !!!")
  (SETQ INKA*CORRUPTED T)
  (throw 'EDT*EMERGENCY.EXIT nil))
	 


(DEFUN EDT=RESET ()
  
  ;;; Edited :  14.8.87
  ;;; Input  :  None.
  ;;; Effect :  Clears all windows and input buffers
  ;;; Value  :  Undefined

  (SETQ EDT*ERROR.MESSAGES NIL)
  (COND (EDT*HARDCOPY (EDT=DO.HARDCOPY))))


(DEFUN EDT=INIT (TYPE)

  ;;; Input:   a flag
  ;;; Effect:  resets some global variables, resets the window manager. If VISIBLE? is T the
  ;;;          windows for user interaction are exposed.
  ;;; Value:   undefined.
  
  (SETQ *INKA-PATHNAME* (COND ((PRO-ENVIRONMENT-VARIABLE "INKA"))
			      (T *INKA-PATHNAME*)))
  (WIN-RESET TYPE)
  (SETQ EDT*INVISIBLE (EQ TYPE 'KIV))
  (SETQ EDT*INTERACTION.PROCESS (PRO-PROCESS.CREATE :NAME "COMMAND-INPUT"
						    :FUNCTION #'EDT=READ.AND.EXECUTE.COMMAND))
  (SETQ EDT*DESCRIPTION.PROCESS (PRO-PROCESS.CREATE :NAME "DESCRIPTION"
						    :FUNCTION #'EDT=HANDLE.DESCRIPTION)))


(DEFUN EDT=START (&OPTIONAL ARGUMENTS)

  ;;; Input:   none
  ;;; Effect:  starts the interaction process and performs the prover-commands until an
  ;;;          exit-command is given
  ;;; Value:   the result of the last performed command.

  (EDT=EXECUTE.DB.COMMANDS ARGUMENTS))


(DEFUN EDT=STOP ()

  (PRO-PROCESS.KILL EDT*INTERACTION.PROCESS)
  (PRO-PROCESS.KILL EDT*DESCRIPTION.PROCESS)
  (WIN-STOP (WIN-WINDOW 'MAIN))
  (WIN-DELETE))



(DEFMACRO EDT=WITH.EXIT (&REST BODY)

  `(COND (INKA*CORRUPTED
	  (FORMAT T "Inka-System aborted due to missing IDM")
	  NIL)
	 (T (SETQ EDT*MAIN.PROCESS (PRO-PROCESS.ACTUAL.PROCESS))
	    (CATCH 'EDT*EMERGENCY.EXIT
	      (PROGN ,@BODY)))))


;;;;; Functions to maintain the main command-menue. These functions are used by the command-process.


(DEFUN EDT=READ.AND.EXECUTE.COMMAND ()

  ;;; Input:   none
  ;;; Effect:  reads a sequence of command until the command EXIT is given.
  ;;;          the commands are performed by the corresponding processes.
  ;;; Value:   undefined

  (LET (COMMAND)
    (WHILE T
      (SETQ COMMAND (EDT=IO.READ.COMMAND))
      (with-simple-restart (inka-top "Ignoring last INKA-command")
			   (CASE (CAR COMMAND)
				 ((C CLEAR REFRESH HARDCOPYSTART HARDCOPYEND)
				  (EDT=HANDLE.DESCR.COMMAND.WITHOUT.DB COMMAND))
				 (DESCRIBE (EDT=HANDLE.DESCR.COMMAND COMMAND))
				 (PROTLEVEL (EDT=HANDLE.DESCR.COMMAND COMMAND))
				 (INTERRUPT (EDT=HANDLE.DESCR.COMMAND.WITH.DB COMMAND))
				 (SAVEPROOF (EDT=HANDLE.DESCR.COMMAND.WITH.DB COMMAND))
				 ((I INSERT D DELETE S SAVE W WRITE L LOAD R READ PROOF OK EXIT)
				  (EDT=HANDLE.DB.COMMAND COMMAND)))))))


(DEFUN EDT=HANDLE.DESCR.COMMAND.WITHOUT.DB (COMMAND)

  (COND (EDT*DB.IN.PROCESS
	 (WIN-IO.PRINT.STATUS (WIN-WINDOW 'MAIN) "Sorry, you have to wait until the proof is finished"))
	(T (CASE (CAR COMMAND)
		 ((C CLEAR) (EDT=DO.CLEAR))
		 (REFRESH (EDT=DO.REFRESH))
		 (HARDCOPYSTART (EDT=DO.HARDCOPY (SECOND COMMAND)))
		 (HARDCOPYEND (EDT=DO.HARDCOPY))))))


(DEFUN EDT=HANDLE.DESCR.COMMAND.WITH.DB (COMMAND)

  (COND (EDT*DB.IN.PROCESS
	 (CASE (CAR COMMAND)
	       (INTERRUPT (EDT=DO.INTERRUPT T))
	       (SAVEPROOF (EDT=DO.SAVEPROOF))))
	(T (WIN-IO.PRINT.STATUS (WIN-WINDOW 'MAIN) "Sorry, there is no proof in process"))))


(DEFUN EDT=HANDLE.DESCR.COMMAND (COMMAND)

  (CASE (CAR COMMAND)
	((PROTLEVEL) (EDT=DO.PROTLEVEL (SECOND COMMAND)))
	((DESCRIBE) (COND (EDT*DESCRIPTION.IN.PROCESS
			   (WIN-IO.PRINT.STATUS (WIN-WINDOW 'MAIN) "Sorry, there is already a description in process"))
			  (T (SETQ EDT*DESCRIPTION.IN.PROCESS T))))))


(DEFUN EDT=HANDLE.DESCRIPTION ()
  (WHILE T (PRO-PROCESS.WAIT "WAITING" #'(LAMBDA () EDT*DESCRIPTION.IN.PROCESS))
	 (EDT=DO.DESCRIBE)
	 (SETQ EDT*DESCRIPTION.IN.PROCESS NIL)))
  


(DEFUN EDT=HANDLE.DB.COMMAND (COMMAND)

  (COND (EDT*DB.IN.PROCESS (WIN-IO.PRINT.STATUS (WIN-WINDOW 'MAIN) "Sorry, there is still a proof in process"))
	(EDT*EXAMINE.PROOF (WIN-IO.PRINT.STATUS (WIN-WINDOW 'MAIN) "Sorry, but there are proofs being examined"))
	(EDT*DESCRIPTION.IN.PROCESS (WIN-IO.PRINT.STATUS (WIN-WINDOW 'MAIN) "Sorry, there is still a description in process"))
	(T (SETQ EDT*DB.IN.PROCESS COMMAND))))


			   

;;;;; Functions used by the database-process.


(DEFUN EDT=EXECUTE.DB.COMMANDS (&OPTIONAL ARGUMENTS)

  (LET (COMMAND)
    (WHILE (NEQ (CAR COMMAND) 'EXIT)
      (PRO-PROCESS.WAIT "WAITING" #'(LAMBDA () EDT*DB.IN.PROCESS))
      (SETQ COMMAND EDT*DB.IN.PROCESS)
      (EDT=EXECUTE.DB.COMMAND COMMAND ARGUMENTS)
      (SETQ EDT*DB.IN.PROCESS NIL))))


(DEFUN EDT=EXECUTE.DB.COMMAND (COMMAND &OPTIONAL ARGUMENTS)

  ;;; Input:  a list
  ;;; Effect: reads a command of the editor and the arguments. the arguments are read by several help
  ;;;         functions having the prefix EDT=io.read...
  ;;; Value:  undefined.
  
  (unwind-protect
      (with-simple-restart (inka-top-level "Return to INKA-top-level")
		       (CASE (CAR COMMAND)
			     ((EXIT OK) NIL)
			     ((I INSERT) (EDT=DO.INSERT (SECOND COMMAND)))
			     ((D DELETE) (EDT=DO.DELETE))
			     (PROOF (EDT=DO.PROOF (COND (ARGUMENTS) (T (SECOND COMMAND)))))
			     ((S SAVE W WRITE) (EDT=DO.WRITE.DB))
			     ((L LOAD R READ) (EDT=DO.READ.DB (SECOND COMMAND)))))
    (win-io.shadow (win-window 'description_1))
    (win-io.shadow (win-window 'description_3))))


(DEFUN EDT=DO.NULL.COMMAND ()

  (WIN-IO.print.status (WIN-WINDOW 'MAIN) "Command not available"))

	   
(DEFUN EDT=DO.INTERRUPT (FLAG)

  ;;; Input:   none
  ;;; Effect:  sets the suspend flag for the prover process
  ;;; Value:   undefined

  (SEL-SUSPEND FLAG)
  (RL-SUSPEND FLAG))


(DEFUN EDT=DO.INSERT (FORMULAS)
  
  ;;; edited at 19-08-87
  ;;; Input:  none.
  ;;; Effect: a formula is read, given to the compiler and redisplayed. If no errors occur, neccessary proofs
  ;;;         for consistency are performed, else a error message is given to the user.
  ;;; Value:  T, if the current formula is inserted, nil otherwise.
  
  (EDT=DO.INSERT.INTERNAL FORMULAS))


(DEFUN EDT=DO.PROOF (FORMULA)
  (LET (RESULT)
    (with-standard-io-syntax 
     (WIN-IO.CLEAR (WIN-WINDOW 'PROOF))
     (COND (FORMULA
	    (cond ((edt-interactive)
		   (win-io.print (format nil "Proving Formula ..... ~% ~A" Formula)
				 (win-window 'proof))))
	    (COND ((MULTIPLE-VALUE-SETQ (EDT*PROOF.RESULT RESULT) (DED-FORMULA.PROVE FORMULA))
		   (WIN-IO.PRINT.STATUS (WIN-WINDOW 'MAIN) "Proof successful"))
		  (T (EDT=FORMULA.COMPILE.ERROR FORMULA RESULT)
		     (WIN-IO.PRINT.STATUS (WIN-WINDOW 'MAIN) "Proof attempt not successful"))))
	   (T (WIN-IO.PRINT.STATUS (WIN-WINDOW 'MAIN) "No formula to prove available"))))))
  

(DEFUN EDT=DO.INSERT.INTERNAL (FORMULAS)
  
  ;;; edited at 19-08-87
  ;;; Input:  none.
  ;;; Effect: a formula is read, given to the compiler and redisplayed. If no errors occur, neccessary proofs
  ;;;         for consistency are performed, else a error message is given to the user.
  ;;; Value:  T, if the current formula is inserted, nil otherwise.

  (WIN-IO.CLEAR (WIN-WINDOW 'PROOF))
  (NULL (EVERY #'(LAMBDA (FORMULA)
		   (COND ((SETQ FORMULA (EDT=FORMULA.REMOVE.EMPTY.LINES (edt=formula.replace.newlines FORMULA)))
			  (cond ((and (edt-interactive)(not EDT*WRITING.DISABLED))
				 (win-io.print (format nil "Inserting Formula .....") (win-window 'proof))
				 (mapcar #'(LAMBDA (STRING) 
					     (win-io.print (format nil "~A" STRING) (win-window 'proof)))
					 formula)))
			  (LET ((RESULT (with-standard-io-syntax (DED-FORMULA.INSERT FORMULA))))
			    (COND ((and (edt-interactive)(not EDT*WRITING.DISABLED))
				    (WIN-IO.print.status
				     (WIN-WINDOW 'main)
				     (format nil (cond (result "Insertion of ~A... failed")
						       (t "Formula: ~A... inserted"))
					     (SUBSEQ (CAR FORMULA) 0 (MIN 60 (LENGTH (CAR FORMULA))))))))
			    (COND ((AND RESULT (integerp (second result)))
				   (EDT=FORMULA.COMPILE.ERROR FORMULA RESULT)))
			    (NULL RESULT)))
			 (T T)))
	       FORMULAS)))


(DEFUN EDT=DO.DELETE ()
  
  ;;; Edited at 18-08-87
  ;;; Input:  none.
  ;;; Effect: shifts the last formula of the the proved area to the scratchpad.
  ;;; Value:  Undefined.

  (LET (FORMULA)
    (setq formula (EDT=DO.DELETE.INTERNAL))
    (win-io.clear (win-window 'proof))
    (cond (formula (WIN-IO.print.status (WIN-WINDOW 'main)
					(format nil "~A deleted" formula))
		   nil))))


(DEFUN EDT=DO.DELETE.INTERNAL ()
  
  ;;; Edited at 18-08-87
  ;;; Input:  none.
  ;;; Effect: shifts the last formula of the the proved area to the scratchpad.
  ;;; Value:  Undefined.

  (DED-FORMULA.DELETE))


(DEFUN EDT=DO.CLEAR ()
  
  ;;; edited at 01-07-87
  ;;; Input :  none
  ;;; Effect: a total reset of the editor is executed. All input until now is lost.
  ;;; Value :  a ready-message

  (COND (EDT*AXIOMS.PROHIBITED (WIN-IO.print.status (WIN-WINDOW 'MAIN) "You cannot reset the specification"))
	(T (COND (EDT*HARDCOPY (EDT=DO.HARDCOPY)))
	   (win-io.clear (win-window 'PROOF))
	   (WIN-IO.print.status (WIN-WINDOW 'MAIN) "Database reset")
	   (DED-RESET))))


(DEFUN EDT=DO.REFRESH ()
  
  ;;; Input :  none
  ;;; Effect:  clears the proof-window if it exists.
  ;;; Value:   undefined.
  
  (WIN-IO.CLEAR (WIN-WINDOW 'PROOF)))


(DEFUN EDT=DO.PROTLEVEL (LEVEL)

  ;;; Input:   a number between 1 and 4
  ;;; Effect:  changes the degree of hardcopy the proof attempt
  ;;; Value:   undefined

  (sel-set.interactive (not (zerop level)))
  (rl-prot.level.set (cond ((eql level 1) -1)
			   ((eql level 2) 4)
			   ((eql level 3) 6)
			   ((eql level 4) 10))))


(DEFUN EDT=DO.SAVEPROOF ()
  ;;; Edited : 23.06.94 by CS
  ;;; Input  : none
  ;;; Effect : the user is asked for a new filename in which the actual proof is to be stored

  (LET ((FILE (WIN-IO.GET.FILENAME "" "proof")))
    (COND ((NOT (STRING-EQUAL FILE ""))
	   (SETQ EDT*SAVEPROOF (format nil "~A.PRV" FILE))))))


(DEFUN EDT=DO.WRITE.DB ()
  
  ;;; edited at 15-07-87
  ;;; Input:  none
  ;;; Effect: Stores the formulas of both areas (proved and scratchpad) on a file to be read from the user
  ;;; Value:  undefined

 (DED-SAVE NIL))


(DEFUN EDT=DO.READ.DB (FILE)
  
  ;;; Input:  none.
  ;;; Effect: If the given input stream is not a file, the input stream is set to a given file.
  ;;; Value:  Undefined.

  (cond ((NOT EDT*AXIOMS.PROHIBITED)
	 (cond ((DED-LOAD FILE T)
		(WIN-IO.print.status (WIN-WINDOW 'MAIN) "Database loaded"))
	       (T (WIN-IO.print.status (WIN-WINDOW 'MAIN) " Database does not exist"))))
	(T (WIN-IO.print.status (WIN-WINDOW 'MAIN) "Changing specifications is not available"))))


(DEFUN EDT=DO.DESCRIBE ()

  ;;; Input:  none
  ;;; Effect: enters descriptions mode of the actual database
  ;;; Value:  undefined

  (with-standard-io-syntax (DED-DATABASE.DESCRIBE))
  (WIN-IO.print.status (WIN-WINDOW 'MAIN) " "))


(DEFUN EDT=DO.HARDCOPY (&OPTIONAL FILE)
  
  ;;; Input:  a filename
  ;;; Effect: if EDT*HARDCOPY is nil a file is opened for hardcopy otherwise the file EDT*HARDCOPY
  ;;;         is closed and EDT*HARDCOPY is set to nil.
  ;;; Value:  undefined
  
  (COND (EDT*HARDCOPY
	 (CLOSE EDT*HARDCOPY)
	 (SETQ EDT*HARDCOPY NIL)
	 (WIN-HARDCOPY (WIN-WINDOW 'PROOF) NIL)
	 (WIN-IO.PRINT.STATUS (WIN-WINDOW 'MAIN) "Hardcopy switched off"))
	(T (SETQ EDT*HARDCOPY (OPEN FILE :DIRECTION :OUTPUT))
	   (WIN-HARDCOPY (WIN-WINDOW 'PROOF) EDT*HARDCOPY)
	   (WIN-IO.PRINT.STATUS (WIN-WINDOW 'MAIN) "Hardcopy switched on"))))


(DEFUN EDT=IO.READ.COMMAND ()
  
  ;;; Edited  :  14.8.87
  ;;; Input   :  none.
  ;;; Effect  :  reads the next command either from the EDT*MENUE.WINDOW or from an given execute-file.
  ;;; Value(?):  the given command, e.g. a list like ('INSERT 1), ('DELETE 2), ... etc.
  
  (WIN-IO.ANY.TYI (WIN-WINDOW 'MAIN)))


(DEFUN EDT=FORMULA.REMOVE.EMPTY.LINES (LINES)

  ;;; Input:   a list of strings
  ;;; Effect:  see value.
  ;;; Value:   a list of strings without leading of following empty lines

  (while (and lines (string-equal (string-trim '(#\Space #\tab) (car lines)) ""))
    (pop lines))
  (while (and lines (string-equal (string-trim '(#\Space #\tab) (car (last lines))) ""))
    (setq lines (butlast lines)))
  lines)


(DEFUN EDT=FORMULA.COMPILE.ERROR (FORMULA RESULT)

  (COND ((AND (EQL 0 (FIRST RESULT))
	      (EQL 0 (SECOND RESULT))
	      EDT*INVISIBLE)
	 (PUSH (CONS 'PARSE (THIRD RESULT)) EDT*ERROR.MESSAGES)) ;; NEUER FALL
	(EDT*INVISIBLE (LET ((STRING (WITH-OUTPUT-TO-STRING (STREAM)
							    (EDT=FORMULA.COMPILE.ERROR.1 FORMULA RESULT STREAM))))
			 (PUSH (CONS 'PARSE STRING) EDT*ERROR.MESSAGES)))
	(T (EDT=FORMULA.COMPILE.ERROR.1 FORMULA RESULT (win-window 'proof)))))


(DEFUN EDT=FORMULA.COMPILE.ERROR.1 (FORMULA RESULT STREAM)
  
  (let ((counter 0))
    (cond ((and (eql (car result) 0) (eql (second result) 0)))
	  (t (win-io.princ (third result) stream)
	     (win-io.terpri stream)
	     (mapc #'(lambda (string)
		       (win-io.princ string stream)
		       (win-io.terpri stream)
		       (cond ((eq counter (second result))
			      (win-io.princ (format nil "~A=" (make-string (car result) :initial-element #\space))
					    STREAM)
			      (win-io.terpri stream)))
		       (incf counter))
		   formula)))))


(defun edt=formula.replace.newlines (list)
  ;;; Input:   a formula as a list of strings
  ;;; Effect:  replaces newlines in a string to a list of string without newlines
  ;;; Value:   the list of strings

  (cond ((Null list) nil)
	(T (nconc (edt=string.replace.newlines (car list)) (edt=formula.replace.newlines (cdr list))))))


(defun edt=string.replace.newlines (string)
  (let* ((pos 0) (laenge (length string)) pos1 result text pos2)
    (while (< pos laenge)
	   (setq pos1 (cond ((position #\Newline string :start pos :end laenge))
			    (t laenge)))
	   (setq text (subseq string pos pos1))
	   (cond ((setq pos2 (position #\% text))
		  (setq text (subseq text 0 pos2))))
	   (setq result (nconc result (list text)))
	   (setq pos (1+ pos1))
	   )
    result)
  )
