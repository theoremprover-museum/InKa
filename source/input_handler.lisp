;;; -*- Package: inka; Syntax: Common-lisp; Mode: LISP -*-

;; 20.11.92 de ih-next.formula.from.border  does no longer call ih-push
;; 20.11.92 de --                           several addaptions for simple mode

(IN-PACKAGE 'inka)

;;;;; ======================================================================================================
;;;;;
;;;;;  INPUT HANDLER:
;;;;;
;;;;;  Following invariants:
;;;;;
;;;;;   IH*INPUT.ARRAY is the central array to store the input of the user.
;;;;;   IH*END-OF-STRING is an array with the same dimension as IH*INPUT.ARRAY and gives the next free 
;;;;;                    character for each line of IH*INPUT.ARRAY.
;;;;;                    therefore a line is empty, iff its corresponding entry is 0.
;;;;;                    and a line is full, iff its corresponding entry is IH*CHARS.PER.LINE.
;;;;;
;;;;; ======================================================================================================

(DEFVAR IH*WINDOW NIL)
(DEFVAR IH*PROCESS NIL)

(DEFVAR IH*GRAPHIC.MODE T)

(DEFVAR IH*INPUT.ARRAY NIL)
(DEFVAR IH*END-OF-STRING NIL)

(DEFVAR IH*CURSOR-X NIL)
(DEFVAR IH*CURSOR-Y NIL)

(DEFVAR IH*SEARCH.STRING "")

(DEFVAR IH*REGION (MAKE-ARRAY '(4)))
(DEFVAR IH*REGISTER (MAKE-ARRAY '(10)))

(DEFVAR IH*BLINKER NIL)

(DEFVAR IH*CHARS.PER.LINE 100)
(DEFVAR IH*LINES.ON.WINDOW 30)

(DEFVAR IH*DELTA-Y 0)

(DEFVAR IH*BORDER (list (LIST 0 NIL 0)))

(DEFVAR IH*UPPER.CHANGED NIL)
(DEFVAR IH*LOWER.CHANGED NIL)


(DEFUN IH-INIT (graphic.mode)
  
  ;;; Input:  a list of 4 coordinates corresponding to the upper left and lower right pixel of the
  ;;;         corresponding formula window.
  ;;; Effect: creates an instance of an editor with corresponding window and process.
  ;;; Value:  undefined
  ;;; Notice: non graphic mode is not implemented !!!
  
  (declare (ignore graphic.mode))
  (setq ih*graphic.mode graphic.mode)
  (cond (ih*graphic.mode
	 (let (ULX ULY LRX LRY)
	   (multiple-value-bind (x-length y-length) (win-screen.size)
	     (setq ulx 0 uly 70 lrx x-length lry (FLOOR (/ (- Y-LENGTH 70) 2))))
	   (SETQ IH*WINDOW (WIN-IO.WINDOW.CREATE 'input NIL ULX ULY LRX LRY))
	   (MULTIPLE-VALUE-SETQ (IH*CHARS.PER.LINE IH*LINES.ON.WINDOW) (WIN-IO.SIZE IH*WINDOW))
	   (SETQ IH*CHARS.PER.LINE (MIN (- IH*CHARS.PER.LINE 4) 100))
	   (SETQ IH*INPUT.ARRAY (MAKE-ARRAY IH*LINES.ON.WINDOW :ADJUSTABLE T))
	   (DOTIMES (I IH*LINES.ON.WINDOW)
		    (SETF (AREF IH*INPUT.ARRAY I) (MAKE-STRING IH*CHARS.PER.LINE :INITIAL-ELEMENT #\SPACE)))
	   (SETQ IH*BLINKER (WIN-IO.BLINKER.CREATE IH*WINDOW))
	   (WIN-IO.BLINKER.SHADOW IH*WINDOW IH*BLINKER)
	   (MULTIPLE-VALUE-BIND (WIDTH IGNORE) (WIN-IO.CHAR.SIZE.OVERALL IH*WINDOW)
				(DECLARE (IGNORE IGNORE))
				(WIN-IO.DRAW.LINE IH*WINDOW (* 3 WIDTH) 0 (* 3 WIDTH) 1000))  
	   (SETQ IH*END-OF-STRING (MAKE-ARRAY IH*LINES.ON.WINDOW :INITIAL-ELEMENT 0 :ADJUSTABLE T))
	   (IH=RESET)
	   (SETQ IH*PROCESS (PRO-PROCESS.CREATE :NAME "INPUT-EDITOR" :FUNCTION #'IH=WAIT.FOR.TYI))))
	(t (setq ih*window nil)
	   (setq ih*process nil)
	   (SETQ IH*CHARS.PER.LINE 100)
	   (SETQ IH*INPUT.ARRAY (MAKE-ARRAY IH*LINES.ON.WINDOW :ADJUSTABLE T))
	   (DOTIMES (I IH*LINES.ON.WINDOW)
		    (SETF (AREF IH*INPUT.ARRAY I) (MAKE-STRING IH*CHARS.PER.LINE :INITIAL-ELEMENT #\SPACE)))
	   (SETQ IH*END-OF-STRING (MAKE-ARRAY IH*LINES.ON.WINDOW :INITIAL-ELEMENT 0 :ADJUSTABLE T))
	   (IH=RESET))))


(DEFMACRO IH-DO (&REST FORM)
  
  ;;; Input:  an sexpression
  ;;; Effect: the IH-process is stopped, the FUNCTION is applied to its arguments, and the
  ;;;         IH-process is continued.
  ;;; Value:  the result of the application of FUNCTION.
  
  `(cond (ih*graphic.mode
	  (PROGN (PRO-PROCESS.DEACTIVATE IH*PROCESS)
		 (WIN-IO.BLINKER.SHADOW IH*window IH*blinker)
		 (multiple-value-prog1 (win-io.with.cursor.hidden ih*window (progn . ,form))
		   (PRO-PROCESS.ACTIVATE IH*PROCESS))))
         (t (progn (multiple-value-prog1 (progn . ,form))))))


(DEFUN IH-ACTIVATE ()
  
  ;;; Input:  none
  ;;; Effect: exposes the formula window, clears its input buffer and activates the input on the
  ;;;         formula window
  ;;; Value:  undefined
  
  (WIN-IO.EXPOSE IH*WINDOW)
  (WIN-IO.CLEAR.INPUT IH*WINDOW)
  (PRO-PROCESS.ACTIVATE IH*PROCESS))


(DEFUN IH-DEACTIVATE ()
  
  ;;; Input:  none
  ;;; Effect: shadows the formula window and deactivate any input on the formula window
  ;;; Value:  undefined
  
  (WIN-IO.SHADOW IH*WINDOW)
  (PRO-PROCESS.DEACTIVATE IH*PROCESS))


;;;;; Interface - Functions of the Input-Handler
;;;;; ==========================================
;;;;;
;;;;; if they are called in a multi-tasking enviroment you have to call these functions by the
;;;;; eval-function IH-DO to avoid dead-locks and inconsistent states.


(DEFUN IH-CLEAR ()
  
  ;;; Input  :  none
  ;;; Effect :  clears all informations stored in the input array, resets all global
  ;;;           values and restarts the IH-process.
  ;;; Value  :  undefined.
  
  (LET (LINE)
       (COND ((> (IH=FIND.LAST.LINE) 100) (ADJUST-ARRAY IH*INPUT.ARRAY 100)))
       (COND ((SETQ LINE (IH=FIND.LAST.FILLED.LINE))
	      (DOTIMES (Y-POS (1+ LINE))
		       (FILL (AREF IH*INPUT.ARRAY Y-POS) #\SPACE)
		       (SETF (AREF IH*END-OF-STRING Y-POS) 0))))
       (SETQ IH*BORDER (list (LIST 0 NIL 0)))
       (SETQ IH*DELTA-Y 0)
       (SETQ IH*CURSOR-X 0 IH*CURSOR-Y 0)
       (SETQ IH*SEARCH.STRING "")
       (cond (ih*graphic.mode
	      (IH=CLEAR.WRITING.AREA)
	      (IH=CLEAR.MARKED.REGION)
	      (IH=WRITE.LINES 0 'END)
	      (WIN-IO.BLINKER.SHADOW IH*WINDOW IH*BLINKER)
	      (WIN-IO.SET.CURSORPOS IH*WINDOW (+ 4 IH*CURSOR-X) (- IH*CURSOR-Y IH*DELTA-Y) :CHARACTER)))))



(DEFUN IH-PUSH.BORDER (&OPTIONAL NAME type)
  
  ;;; edited at 04-may-87 / changes 16.6.88 by mp 
  ;;; Input  : new border to be stored
  ;;; Effect : stores NEW.BORDER at first position in the list IH*border
  ;;; Value  : undefined.
  
  (LET ((NEW.BORDER (IH=FIND.END.OF.NEXT.BLOCK (IH=ACTUAL.BORDER))))
       (SETF (second (CAR IH*BORDER)) NAME)
       (PUSH (list NEW.BORDER NIL (if (eq type 'axiom) (1+ (third (car ih*border))) (third (car ih*border))))
	     IH*BORDER)
       (IH=INSERT.CHANGED.LINES (CAR (SECOND IH*BORDER)) (CAAR IH*BORDER))
       (IH=WRITE.CHANGES.TO.WINDOW)))


(defun ih-add.name.to.border (name)

  ;;; Input:  name of formula
  ;;; Effect: the given name of formula is entried to ih*border
  ;;; Value:  name of formula
  
  (SETF (second (second IH*BORDER)) NAME))


(DEFUN IH-POP.BORDER ()
  
  ;;; edited at 04-may-87
  ;;; Input  : none
  ;;; Effect : forgets the last border having been stored
  ;;; Value  : none
  
  (LET ((X (POP IH*BORDER)))
       (SETF (SECOND (CAR IH*BORDER)) NIL)
       (IH=INSERT.CHANGED.LINES (CAAR IH*BORDER) (CAR X))    
       (IH=WRITE.CHANGES.TO.WINDOW)))


(DEFUN IH-SHOW.POSITION (X-POS Y-POS &OPTIONAL INCREMENTAL)
  
  ;;; edited :  2.12.1987
  ;;; Input  :  X-POS, Y-POS denote a position in IH*INPUT.ARRAY
  ;;; Effect :  moves cursor to the specified position.
  ;;; Value  :  undefined.
  
  (SETQ IH*CURSOR-X X-POS
	IH*CURSOR-Y (COND (INCREMENTAL (+ (IH=FIND.NON.EMPTY.LINE (IH=ACTUAL.BORDER) 'down) Y-POS))
			  (T Y-POS)))
  (IH=WRITE.CHANGES.TO.WINDOW))


(DEFUN IH-SAVE (FILE)
  
  ;;; edited : 19. Oct. 87 by mp
  ;;; Input  : filename
  ;;; Effect : blocks are printed to file
  ;;; Value  : undefined
  
  (LET ((INDEX 0) (END.OF.TEXT (1+ (IH=FIND.LAST.LINE))))
       (WITH-OPEN-FILE (STREAM FILE :DIRECTION :OUTPUT)
		       (WHILE (< INDEX END.OF.TEXT)
			      (WRITE-LINE (STRING-RIGHT-TRIM '(#\SPACE) (AREF IH*INPUT.ARRAY INDEX)) STREAM)
			      (INCF INDEX))
		       (WRITE-LINE "OK" STREAM))))


(DEFUN IH-LOAD (FILE)
  
  ;;; Input:  a file
  ;;; Effect: inserts the text of the file exactly after the border.
  ;;; Value:  undefined
  
  (LET ((Y-POS (IH=ACTUAL.BORDER)) LINE LINE1 END.OF.FILE END.OF.LINE)
    (WITH-OPEN-FILE (STREAM FILE :DIRECTION :INPUT)
		       (WHILE (NOT END.OF.FILE)
			      (SETQ LINE (STRING-RIGHT-TRIM '(#\SPACE) (READ-LINE STREAM)))
			      (cond ((not ih*graphic.mode)
				     (write-line line)))
			      (COND ((STRING-EQUAL LINE "OK")
				     (SETQ END.OF.FILE T)
				     (IH=INSERT.NEW.LINES Y-POS 2)
				     (INCF Y-POS 2))
				    (T (WHILE (> (LENGTH LINE) IH*CHARS.PER.LINE)
					      (SETQ END.OF.LINE (POSITION #\SPACE LINE :FROM-END T
									  :END (1- IH*CHARS.PER.LINE)))
					      (SETQ LINE1 (SUBSEQ LINE 0 END.OF.LINE))
					      (IH=INSERT.NEW.LINES Y-POS 1)
					      (IH=INSERT.STRING 0 Y-POS LINE1)
					      (INCF Y-POS)
					      (SETQ LINE (DELETE-IF #'(LAMBDA (IGNORE)
									      (DECLARE (IGNORE IGNORE)) T)
								    LINE :END END.OF.LINE)))
				       (IH=INSERT.NEW.LINES Y-POS 1)
				       (IH=INSERT.STRING 0 Y-POS LINE)
				       (INCF Y-POS)))))
       (IH=WRITE.CHANGES.TO.WINDOW)))


(defun ih-show (argument)
  
  ;;; edited at 29.10.92
  ;;; Input:  The argument of the show command; 'all name 'short
  ;;; Effect: Shows formulas from ih*input.array in dependence of argument
  ;;; Value:  NIL if no error is occured, T else
  
  (case argument
    ((all a nil) (ih=show.all))
    ((short s) (ih=show.short))
    (otherwise (ih=show.definition argument))))


(defun ih=show.all ()
  
  ;;; edited at 29.10.92
  ;;; Input:  NONE
  ;;; Effect: Shows all formulas from ih*input.array
  ;;; Value:  NIL
  
  (let ((last.filled.line (ih=find.last.filled.line))
	(last.proved.line (ih=actual.border)))
    (cond ((> last.proved.line 0)
           (format t "Proved formulas~%")
	   (format t "===============~%")
	   (dotimes (i (+ 1 last.proved.line)) (write-line (aref ih*input.array i)))))
    (cond ((and last.filled.line (>= last.filled.line last.proved.line))
	   (format t "Following formulas are not proved~%")
	   (format t "=================================~%")
	   (do ((i last.proved.line (+ i 1)))
	       ((> i last.filled.line))
	     (write-line (aref ih*input.array i)))))
    (cond ((not last.filled.line)
	   (format t"   no formulas~%")))
    nil))


(defun ih=show.short ()
  
  ;;; edited at 29.10.92
  ;;; Input:  NONE
  ;;; Effect: Shows all names of formulas from ih*border
  ;;; Value:  NIL
  
  (format t "Names of proved formulas~%========================~%")
  (mapc #'(lambda (item) (format t "  ~A~%" (cadr item))) (reverse (cdr ih*border)))
  nil)


(defun ih=show.definition (name)
  
  ;;; edited at 29.10.92
  ;;; Input:  Definition-name
  ;;; Effect: Shows the formula denoted by name
  ;;; Value:  NIL if no error is occured, T else
  
  (let (border begin end string)
    (cond ((setq border (find-if #'(lambda (actual.border)
				     (string-equal (da-pname (second actual.border)) (string name)))
				 ih*border))
	   (setq begin (car border))
	   (cond ((neq begin 0) (incf begin)))
	   (setq end (ih=find.end.of.next.block begin))
	   (format t "Definition: ~S~%~%" name)
	   (do ((i begin (+ i 1)))
	       ((> i end))
	     (write-line (aref ih*input.array i)))
	   (values begin end)
	   nil)
	  (t t))))


(defun ih-edit (name)
  
  ;;; edited at 29.10.92
  ;;; Input:  Definition-name
  ;;; Effect: Simple-mode-editor
  ;;; Value:  NIL if no error is occured, T else
  
  (cond (name (ih=edit.definition name))
	(t (ih=get.new.definition))))


(defun ih=edit.definition (name)
  
  ;;; edited at 29.10.92
  ;;; Input:  Definition-name
  ;;; Effect: Edit definition name
  ;;; Value:  NIL if no error is occured, T else
  
  (let ((no.of.lines 0)
	string.list
	string
	(y-pos (ih=actual.border))
	begin end eof found)
    (cond ((neq y-pos 0) (incf y-pos)))
    (while (and (not found) (not eof))
      (cond ((setq found (cond ((aref ih*input.array y-pos)
				(search (string name) (aref ih*input.array y-pos) :test #'string-equal))
			       (t nil))))
	    ((<= (ih=find.last.line) y-pos)
	     (setq eof t))
	    (t (setq y-pos (1+ (ih=find.empty.line y-pos 'down))))))
    (cond (found
	   (setq begin y-pos)
	   (setq end (ih=find.end.of.next.block begin))
	   (do ((i begin (+ i 1)))
	       ((> i end))
	     (write-line (aref ih*input.array i)))
	   (ih=delete.lines begin (1- end))
	   (while (not (find #\. (setq string (read-line))))
	     (setq string.list (append string.list (list string)))
	     (incf no.of.lines))
	   (cond ((> no.of.lines 0)
		  (ih=insert.new.lines begin no.of.lines)
		  (mapc #'(lambda (line)
			    (ih=insert.string 0 begin line)
			    (incf begin))
			string.list)))
	   nil)
	  (t t))))


(defun ih=get.new.definition ()
  
  ;;; edited at 29.10.92
  ;;; Input:  NONE
  ;;; Effect: A new definition is inserted at the end of the border line
  ;;; Value:  NIL
  
  (let ((no.of.lines 0)
	(begin (ih=actual.border))
	string string.list)
    (while (not (find #\. (setq string (read-line))))
      (setq string.list (append string.list (list string)))
      (incf no.of.lines))
    (cond ((> no.of.lines 0)
	   (cond ((neq begin 0) (incf begin)))
	   (ih=insert.new.lines begin (1+ no.of.lines))
	   (mapc #'(lambda (line)
		     (ih=insert.string 0 begin line)
		     (incf begin))
		 string.list)))
    nil))


(DEFUN IH-NEXT.FORMULA.FROM.BORDER ()
  
  ;;; edited :  2.12.1987
  ;;; Input  :  none.
  ;;; Effect :  see value.
  ;;; Value  :  a list of strings, denoting the next formula beyond the border
  
  (LET ((START.LINE (IH=ACTUAL.BORDER)) COUNTER RESULT)
       (WHILE (AND (SETQ START.LINE (IH=FIND.NON.EMPTY.LINE START.LINE 'DOWN))
		   (NULL (POSITION-IF #'(LAMBDA (X) (NEQ X #\SPACE)) (AREF IH*INPUT.ARRAY START.LINE))))
	      (SETF (AREF IH*END-OF-STRING START.LINE) 0))
       (COND (START.LINE
	      (SETQ COUNTER (COND ((SETQ COUNTER (IH=FIND.EMPTY.LINE START.LINE 'DOWN)) (1- COUNTER))
				  (T (IH=FIND.LAST.LINE))))
	      (WHILE (>= COUNTER START.LINE)
		(PUSH (STRING-RIGHT-TRIM '(#\SPACE) (AREF IH*INPUT.ARRAY COUNTER)) RESULT)
		(DECF COUNTER))
	      RESULT))))


(DEFUN IH-NUMBER.OF.FORMULAS.TO.PROVE ()
  
  ;;; edited : 29. jan 88 by mp
  ;;; Effect : number of blocks below in the scratchpad is returned
  
  (LET* ((START.LINE (IH=ACTUAL.BORDER))
	 (COUNT (IF (EQL (AREF IH*END-OF-STRING START.LINE) 0) 0 1)))
	(WHILE (IH=FIND.NEXT.BLOCK START.LINE)
	       (SETQ START.LINE (IH=FIND.NEXT.BLOCK START.LINE))
	       (INCF COUNT))
	COUNT))


(DEFUN IH=WAIT.FOR.TYI ()
  (WHILE T
	 (IH=EXAMINE.TYI (win-with.active.cursor IH*window (WIN-IO.ANY.TYI IH*WINDOW)))))


(DEFUN IH=EXAMINE.TYI (CHAR)
  
  ;; Edited :  23-07-87 / changed 10.10.90 de
  ;; Input  :  key pad to be handled
  ;; Effect :  handles control-characters and signs to be shown on the screen
  ;; Value  :  undefined.
  
  (LET (RESULT)
       (IH=CLEAR.WRITING.AREA)
       (COND ((CONSP CHAR)
	      (MULTIPLE-VALUE-BIND (X-POS Y-POS) 
				   (WIN-CHARACTER.POSITION IH*WINDOW (SECOND CHAR) (THIRD CHAR))
				   (CASE (CAR CHAR)
					 (1 (IH=MOVE.CURSOR.NEAR (- X-POS 4) (+ Y-POS IH*DELTA-Y))
					    (IH=WRITE.CHANGES.TO.WINDOW))
					 (2 (IH=MARK.MOUSE.POSITION (- X-POS 4) (+ Y-POS IH*DELTA-Y)))
					 (3 (SETQ RESULT (IH=DESCRIBE.DENOTED.OBJECT
							  (- X-POS 4) (+ Y-POS IH*DELTA-Y)))))))
	     (T (CASE CHAR
		      ((#\SUPER-J #\CONTROL-B) (IH=MOVE.CURSOR.LEFT))
		      ((#\SUPER-K #\CONTROL-F) (IH=MOVE.CURSOR.RIGHT))
		      ((#\SUPER-I #\CONTROL-P) (IH=MOVE.CURSOR.UP))
		      ((#\SUPER-M #\CONTROL-N) (IH=MOVE.CURSOR.DOWN))
		      ((#\HYPER-B #\META-\p) (IH=MOVE.CURSOR.TO.PREVIOUS.BLOCK))
		      ((#\HYPER-F #\META-\n) (IH=MOVE.CURSOR.TO.NEXT.BLOCK))
		      ((#\HYPER-S #\META-\d) (IH=MOVE.CURSOR.TO.DEFINITION))
		      (#\CONTROL-A (IH=MOVE.CURSOR.BEGIN.OF.LINE))
		      (#\CONTROL-E (IH=MOVE.CURSOR.END.OF.LINE))
		      (#\META-< (IH=MOVE.CURSOR.HOME))
		      (#\META-> (IH=MOVE.CURSOR.END))
		      (#\CONTROL-X (IH=SAVE.REGION))
		      (#\CONTROL-S (IH=SEARCH.FORWARD))
		      (#\CONTROL-R (IH=SEARCH.BACKWARD))
		      (OTHERWISE 
		       (COND ((IH=BORDER.CHECK)
			      (CASE CHAR
				    (#\CONTROL-W (IH=DELETE.MARKED.REGION))
				    (#\CONTROL-G (IH=COPY.REGION))
				    ((#\RETURN) (IH=HANDLE.LINEFEED))
				    (#\CONTROL-L (IH=DELETE.LINES IH*CURSOR-Y IH*CURSOR-Y)) 
				    (#\CONTROL-D (IH=HANDLE.DELETE.CHAR))
				    (#\CONTROL-Y (IH=INSERT.MARKED.REGION IH*CURSOR-X IH*CURSOR-Y))
				    (#\RUBOUT (IH=HANDLE-RUBOUT))
				    (OTHERWISE (IF (AND (GRAPHIC-CHAR-P CHAR)
							(IH=INSERT.CHAR CHAR IH*CURSOR-X IH*CURSOR-Y))
						   (IH=MOVE.CURSOR.RIGHT))))))))
		(IH=CLEAR.MARKED.REGION)
		(IH=WRITE.CHANGES.TO.WINDOW)))
       RESULT))


(DEFUN IH=INITIALIZE.BLINKER ()
  
  ;;; edited :  2.12.1987
  ;;; Effect :  creates a blinker and makes it invisible.
  ;;; Value  :  undefined.
  
  (SETQ IH*BLINKER (WIN-IO.BLINKER.CREATE IH*WINDOW))
  (WIN-IO.BLINKER.SHADOW IH*WINDOW IH*BLINKER))


(DEFUN IH=WRITE.CHANGES.TO.WINDOW ()
  
  ;;; edited :  2.12.1987
  ;;; Input  :  none.
  ;;; Effect :  Computes the visible area of IH*INPUT.ARRAY according to the actual cursor position and
  ;;;           writes the relevant changings to the corresponding window.
  ;;;           If the last character before cursor-position is a closing bracket, a blinker is set to it's
  ;;;           corresponding opening bracket.
  ;;; Value  :  undefined.
  
  (cond (ih*graphic.mode
	 (WIN-IO.BLINKER.SHADOW IH*WINDOW IH*BLINKER)
	 (win-io.with.cursor.hidden
	  ih*window
	  (COND ((OR (< IH*CURSOR-Y IH*DELTA-Y)
		     (>= IH*CURSOR-Y (+ IH*DELTA-Y IH*LINES.ON.WINDOW)))
		 (SETQ IH*DELTA-Y (MAX 0 (- IH*CURSOR-Y (CEILING (/ IH*LINES.ON.WINDOW 2)))))
		 (IH=WRITE.LINES IH*DELTA-Y 'END))
		((EQ IH*LOWER.CHANGED 'CURSORPOS) (IH=WRITE.CHAR))
		(IH*LOWER.CHANGED (IH=WRITE.LINES IH*LOWER.CHANGED IH*UPPER.CHANGED)))
	  (SETQ IH*CURSOR-Y (MIN IH*CURSOR-Y (IH=FIND.LAST.LINE)))
	  (SETQ IH*CURSOR-X (MIN IH*CURSOR-X (IH=FIND.END.OF.LINE IH*CURSOR-Y)))
	  (WIN-IO.SET.CURSORPOS IH*WINDOW (+ 4 IH*CURSOR-X) (- IH*CURSOR-Y IH*DELTA-Y) :CHARACTER))
	 (IH=HANDLE.CORRESPONDING.BRACKET)
	 (IH=CLEAR.WRITING.AREA))))


(DEFUN IH=WRITE.CHAR ()
  (WIN-IO.SET.CURSORPOS IH*WINDOW (+ 4 IH*CURSOR-X) (- IH*CURSOR-Y IH*DELTA-Y) :CHARACTER)
  (WIN-IO.PRINT.CHAR IH*WINDOW
		     (AREF (AREF IH*INPUT.ARRAY IH*CURSOR-Y) (1- IH*CURSOR-X))
		     (+ 4 (1- IH*CURSOR-X)) (- IH*CURSOR-Y IH*DELTA-Y)))


(DEFUN IH=WRITE.LINES (Y-FROM Y-TO)
  
  ;;; edited :  2.12.1987
  ;;; Input  :  Y-FROM, Y-TO - two integer, denoting two lines of IH*INPUT.ARRAY or the atoms BEGIN rsp. END.
  ;;; Effect :  writes the specified lines to the corresponding window.
  ;;; Value  :  undefined.
  
  (LET (STYLE (LAST.LINE (IH=FIND.LAST.LINE)))
       (COND ((< Y-FROM IH*DELTA-Y) (SETQ Y-FROM IH*DELTA-Y)))
       (COND ((EQ Y-TO 'END) (SETQ Y-TO (1- (+ IH*DELTA-Y IH*LINES.ON.WINDOW))))
	     ((>= Y-TO (+ IH*DELTA-Y IH*LINES.ON.WINDOW))
	      (SETQ Y-TO (1- (+ IH*DELTA-Y IH*LINES.ON.WINDOW)))))
       (SETQ STYLE (IH=GET.BOX.STYLE Y-FROM))
       (WHILE (<= Y-FROM Y-TO)
	      (WIN-IO.SET.CURSORPOS IH*WINDOW 4 (- Y-FROM IH*DELTA-Y) :CHARACTER)
	      (IF (AND (<= Y-FROM (IH=ACTUAL.BORDER))
		       (EQL (AREF IH*END-OF-STRING Y-FROM) 0))
		  (SETQ STYLE (IH=GET.BOX.STYLE Y-FROM)))
	      (WIN-IO.PRINT.BOX IH*WINDOW 1 (- Y-FROM IH*DELTA-Y) STYLE)
	      (COND ((and (<= Y-FROM LAST.LINE) (not (eql (aref ih*end-of-string y-from) 0))) 
		     (WIN-IO.PRINT.STRING IH*WINDOW (AREF IH*INPUT.ARRAY Y-FROM)))
		    (t (WIN-IO.CLEAR.LINE IH*WINDOW)))
	      (INCF Y-FROM))))



(DEFUN IH=GET.BOX.STYLE (LINENO)
  
  ;;; edited :  16. jun 1988 by mp
  ;;; Input  :  linenumber
  ;;; Effect :  the style of the box is calculated according to the number of axioms so far
  ;;; Value  :  box.style
  
  (COND ((>= LINENO (IH=ACTUAL.BORDER)) 'WHITE)
	(T (CASE (THIRD (NTH (1- (POSITION-IF #'(LAMBDA (X) (<= X LINENO)) IH*BORDER :KEY #'CAR)) IH*BORDER))
		 (0 'BLACK)
		 (1 'DARK)
		 (2 'MEDIUM)
		 (OTHERWISE 'LIGHT)))))


(DEFUN IH=RESET ()
  
  ;;; edited :  2.12.1987
  ;;; Input  :  none.
  ;;; Effect :  clears all global variables and resets cursor.
  ;;; Value  :  undefined.
  
  (LET (LINE)
       (COND ((SETQ LINE (IH=FIND.LAST.FILLED.LINE))
	      (DOTIMES (Y-POS (1+ LINE))
		       (FILL (AREF IH*INPUT.ARRAY Y-POS) #\SPACE)
		       (SETF (AREF IH*END-OF-STRING Y-POS) 0))))
       (SETQ IH*BORDER (list (LIST 0 NIL 0)))
       (COND (IH*GRAPHIC.MODE
	      (SETQ IH*DELTA-Y 0)
	      (SETQ IH*CURSOR-X 0 IH*CURSOR-Y 0)
	      (IH=CLEAR.WRITING.AREA)
	      (IH=CLEAR.MARKED.REGION)
	      (IH=WRITE.LINES 0 'END)
	      (SETQ IH*SEARCH.STRING "")
	      (WIN-IO.SET.CURSORPOS IH*WINDOW (+ 4 IH*CURSOR-X) (- IH*CURSOR-Y IH*DELTA-Y) :CHARACTER)))))


(DEFMACRO IH=CLEAR.WRITING.AREA ()
  
  ;;; edited :  2.12.1987
  ;;; Input  :  none.
  ;;; Effect :  clears area to be printed on the corresponding window.
  
  `(SETQ IH*LOWER.CHANGED NIL IH*UPPER.CHANGED NIL))



(DEFUN IH=HANDLE.CORRESPONDING.BRACKET ()
  
  ;;; edited :  2.12.1987
  ;;; Input  :  none.
  ;;; Effect :  If the preceeding position of the cursor position is a closing bracket, the corresponding
  ;;;           opening bracket is shown by a blinker.
  ;;; Value  :  undefined.
  
  (LET (X-POS Y-POS)
    (COND ((AND (> IH*CURSOR-X 0)
		(EQL (AREF (AREF IH*INPUT.ARRAY IH*CURSOR-Y) (1- IH*CURSOR-X)) #\))
		(MULTIPLE-VALUE-SETQ (X-POS Y-POS)
		  (IH=FIND.CORRESPONDING.BRACKET (1- IH*CURSOR-X) IH*CURSOR-Y))
		(>= Y-POS IH*DELTA-Y))
	   (WIN-IO.SET.BLINKERPOS IH*WINDOW IH*BLINKER (+ 4 X-POS) (- Y-POS IH*DELTA-Y) :CHARACTER))
	  (T (WIN-IO.BLINKER.SHADOW IH*WINDOW IH*BLINKER)))))

;;;;; ======================================================================================================
;;;;;
;;;;;  Functions for handling cursor move.
;;;;;
;;;;; ======================================================================================================


(DEFMACRO IH=MOVE.CURSOR.LEFT ()
  
  ;; Input: none
  ;; Effect: handles button left-arrow
  
  `(COND ((/= 0 IH*CURSOR-X) (DECF IH*CURSOR-X))
    ((IH=MOVE.CURSOR.UP) (IH=MOVE.CURSOR.END.OF.LINE))))


(DEFMACRO IH=MOVE.CURSOR.RIGHT ()
  
  ;; Input:  none
  ;; Effect: handles button right-arrow
  
  `(COND ((/= IH*CURSOR-X (IH=FIND.END.OF.LINE IH*CURSOR-Y)) (INCF IH*CURSOR-X))
    ((IH=MOVE.CURSOR.DOWN) (IH=MOVE.CURSOR.BEGIN.OF.LINE))))


(DEFMACRO IH=MOVE.CURSOR.UP ()
  
  ;; Input: none
  ;; Effect: handles button arrow-up
  
  `(COND ((NOT (ZEROP IH*CURSOR-Y)) (decf IH*cursor-y))))



(DEFMACRO IH=MOVE.CURSOR.DOWN ()
  
  ;; Input :none
  ;; Effect :handles button arrow-down
  
  `(COND ((< IH*CURSOR-Y (1- (ARRAY-DIMENSION IH*INPUT.ARRAY 0)))
          (INCF IH*CURSOR-Y))))


(DEFMACRO IH=MOVE.CURSOR.BEGIN.OF.LINE ()
  
  ;;; Input  : none
  ;;; Effect : moves cursor to the begin of the actual line.
  
  `(SETQ IH*CURSOR-X 0))


(DEFUN IH=MOVE.CURSOR.END.OF.LINE ()
  
  ;;; Input  : none
  ;;; Effect : moves cursor to the last written character of the actual line.
  ;;; Notice : this denoted character may be also a space !
  
  (SETQ IH*CURSOR-X (IH=FIND.END.OF.LINE IH*CURSOR-Y))
  (COND ((EQ IH*CURSOR-X IH*CHARS.PER.LINE)
	 (DECF IH*CURSOR-X))))


(DEFMACRO IH=MOVE.CURSOR.NEXT.LINE ()
  
  ;;; Input  : none
  ;;; Effect : moves cursor to the begin of the following line.
  ;;; Value  : T, if the operation is terminated normally.
  
  `(COND ((IH=MOVE.CURSOR.DOWN)
	  (IH=MOVE.CURSOR.BEGIN.OF.LINE))))



(DEFMACRO IH=MOVE.CURSOR.TO.NEXT.BLOCK ()
  
  ;;; Input  : none
  ;;; Effect : moves cursor to the beigin of the following block.
  ;;; Value  : T, if the operation is terminated normally.
  
  `(LET ((NEW.LINE (IH=FIND.NEXT.BLOCK IH*CURSOR-Y)))
    (COND (NEW.LINE (SETQ IH*CURSOR-X 0 IH*CURSOR-Y NEW.LINE)))))


(DEFMACRO IH=MOVE.CURSOR.TO.PREVIOUS.BLOCK ()
  
  ;;; Input  : none
  ;;; Effect : moves cursor to the begin of the previous block.
  ;;; Value  : T, if the operation is terminated normally.
  
  `(LET ((NEW.LINE (IH=FIND.PREVIOUS.BLOCK IH*CURSOR-Y))) 
    (COND (NEW.LINE (SETQ IH*CURSOR-X 0 IH*CURSOR-Y NEW.LINE)))))


(DEFMACRO IH=MOVE.CURSOR.HOME ()
  
  ;; Edited at 23-07-87
  ;; Input :none
  ;; Effect :cursor home
  ;; Value :nil (returnp)
  
  `(SETQ IH*CURSOR-Y 0 IH*CURSOR-X 0))



(DEFMACRO IH=MOVE.CURSOR.END ()
  
  ;;; Edited   at 23-07-87
  ;;; Input   : none
  ;;; Effect  : cursor is positioned to the begin of the last not-empty line
  
  `(SETQ IH*CURSOR-X 0 IH*CURSOR-Y (IH=FIND.LAST.FILLED.LINE)))


(DEFUN IH=MOVE.CURSOR.TO.DEFINITION ()
  
  ;;; edited :  2.12.1987
  ;;; Input  :  none.
  ;;; Effect :  moves cursor to the user specified sort, function- or predicate definition.
  ;;; Value  :  undefined.
  
  (LET ((DEF (WIN-VL.CHOOSE IH*WINDOW "Please enter a sort, function or predicate name:" "")) 
	BORDER)
    (COND ((SETQ BORDER (FIND-IF #'(LAMBDA (ACTUAL.BORDER)
				     (STRING-EQUAL (DA-PNAME (second ACTUAL.BORDER)) DEF))
				 IH*BORDER))
	   (IH-SHOW.POSITION 0 (IH=FIND.NON.EMPTY.LINE (CAR BORDER) 'DOWN))))))


(DEFUN IH=MOVE.CURSOR.NEAR (X-POS Y-POS)
  
  ;;; Input  : X-POS, Y-POS denote a position in the IH*INPUT.ARRAY
  ;;; Effect : moves cursor nearest to the specified position 
  
  (SETQ IH*CURSOR-Y (MAX Y-POS 0))
  (SETQ IH*CURSOR-Y (MIN IH*CURSOR-Y (IH=FIND.LAST.LINE)))
  (SETQ IH*CURSOR-X (MAX X-POS 0))
  (SETQ IH*CURSOR-X (MIN IH*CURSOR-X (IH=FIND.END.OF.LINE IH*CURSOR-Y))))



(DEFMACRO IH=HANDLE.DELETE.CHAR ()
  
  ;;; Input  : none
  ;;; Effect : deletes the next character right to the cursor.
  ;;; Value  : undefined.
  
  `(COND ((IH=MOVE.CURSOR.RIGHT)
	  (IH=HANDLE-RUBOUT))))


(DEFUN IH=HANDLE-RUBOUT ()
  
  ;;; edited at 12-may-87
  ;;; Input  : none
  ;;; Effect : rubs out the character left of the cursor and an empty line above
  ;;; Value  : Undefined.
  
  (LET (END)
    (COND ((> IH*CURSOR-X (IH=FIND.END.OF.LINE IH*CURSOR-Y)))
	  ((NOT (ZEROP IH*CURSOR-X))
	   (IH=DELETE.CHAR (DECF IH*CURSOR-X) IH*CURSOR-Y))
	  ((AND (> IH*CURSOR-Y 0)
		(IH=MOVE.LINE 0 IH*CURSOR-Y
			      (SETQ END (IH=FIND.END.OF.LINE (1- IH*CURSOR-Y)))
			      (1- IH*CURSOR-Y)))
	   (IH=DELETE.LINES IH*CURSOR-Y IH*CURSOR-Y)
	   (DECF IH*CURSOR-Y) 
	   (SETQ IH*CURSOR-X END)))))


(DEFUN IH=HANDLE.LINEFEED  ()
  
  ;;; Edited at 18-08-87
  ;;; Input  : none
  ;;; Effect : shifts the text right of the cursor-position to the next line.
  
  (IH=INSERT.NEW.LINES (1+ IH*CURSOR-Y) 1)
  (IH=MOVE.LINE IH*CURSOR-X IH*CURSOR-Y 0 (1+ IH*CURSOR-Y))
  (IH=MOVE.CURSOR.NEXT.LINE))



;;;;;========================================================================================================
;;;;;
;;;;; Functions to delete part of the array. The cursor is not moved and all changes are notified for later 
;;;;; modification of the corresponding window.
;;;;;
;;;;;========================================================================================================

(DEFUN IH=DELETE.CHAR (X-POS Y-POS)
  
  ;;; edited :  2.12.1987
  ;;; Input  :  X-POS, Y-POS denote a position in IH*INPUT.ARRAY
  ;;; Effect :  the denoted character is deleted from the IH*INPUT.ARRAY
  ;;; Value  :  undefined.
  
  (REPLACE (AREF IH*INPUT.ARRAY Y-POS)
	   (AREF IH*INPUT.ARRAY Y-POS)
	   :START1 X-POS
	   :START2 (1+ X-POS))
  (IH=CHANGE.POSITION #\SPACE (1- (AREF IH*END-OF-STRING Y-POS)) Y-POS)
  (DECF (AREF IH*END-OF-STRING Y-POS))
  (IH=INSERT.CHANGED.LINE Y-POS))



(DEFUN IH=DELETE.STRING (X-BEGIN X-END Y-POS)
  
  ;;; edited :  2.12.1987 / changed 13.9.88 mp
  ;;; Input  :  X-BEGIN, Y-POS rsp. X-END, Y-POS denote two positions in IH*INPUT.ARRAY
  ;;; Effect :  the denoted string is deleted from the IH*INPUT.ARRAY
  ;;; Value  :  (values X-BEGIN Y-POS).
  
  (COND ((< X-END (MIN (LENGTH (AREF IH*INPUT.ARRAY Y-POS))
		       (IH=FIND.END.OF.LINE Y-POS)))
	 (REPLACE (AREF IH*INPUT.ARRAY Y-POS)
		  (AREF IH*INPUT.ARRAY Y-POS)
		  :START1 X-BEGIN
		  :START2 (1+ X-END))))
  (SETQ X-END (- (+ (IH=FIND.END.OF.LINE Y-POS) X-BEGIN) X-END))
  (FILL (AREF IH*INPUT.ARRAY Y-POS) #\SPACE :START X-END)
  (SETF (AREF IH*END-OF-STRING Y-POS) X-END)
  (IH=INSERT.CHANGED.LINE Y-POS)
  (VALUES X-BEGIN Y-POS))



(DEFUN IH=DELETE.LINES (BEGIN END)
  
  ;;; edited :  2.12.1987
  ;;; Input  :  BEGIN, END denote an area of IH*INPUT.AREA.
  ;;; Effect :  the denoted area is deleted from the IH*INPUT.ARRAY
  ;;; Value  :  a multiple value, denoting the begin of the deleted area.
  
  (REPLACE IH*INPUT.ARRAY IH*INPUT.ARRAY
	   :START1 BEGIN 
	   :START2 (1+ END))
  (REPLACE IH*END-OF-STRING IH*END-OF-STRING
	   :START1 BEGIN
	   :START2 (1+ END))
  (IH=CLEAR.LINES (- (IH=FIND.LAST.LINE) (- END BEGIN)) (IH=FIND.LAST.LINE))
  (cond (IH*GRAPHIC.MODE (IH=INSERT.CHANGED.LINES BEGIN 'END)))
  (VALUES 0 BEGIN))


(DEFUN IH=CLEAR.LINES (FROM-Y TO-Y)
  
  ;;; edited :  2.12.1987
  ;;; Input  :  FROM-Y, TO-Y denote an area of IH*INPUT.AREA.
  ;;; Effect :  the denoted area is cleared.
  ;;; Value  :  undefined.
  
  (WHILE (<= FROM-Y TO-Y)
    (SETF (AREF IH*INPUT.ARRAY FROM-Y) (IH=CREATE.NEW.LINE))
    (SETF (AREF IH*END-OF-STRING FROM-Y) 0)
    (INCF FROM-Y)))


(DEFUN IH=MOVE.LINE (FROM-X FROM-Y TO-X TO-Y)
  
  ;;; edited :  2.12.1987
  ;;; Input  :  FROM-X, FROM-Y rsp. TO-X, TO-Y denote two positions in IH*INPUT.ARRAY
  ;;; Effect :  moves string specified by FROM-X, FROM-Y and the end of line to the position
  ;;;           specified by TO-X and TO-Y.
  ;;; Value  :  undefined.
  
  (LET ((END-X (IH=FIND.END.OF.LINE FROM-Y)))
    (COND ((EQ FROM-Y TO-Y) NIL)
	  (T (COND ((> TO-Y (IH=FIND.LAST.LINE))
		    (IH=ADJUST.ARRAY TO-Y)))
	     (COND ((IH=MOVE.STRING.TO.RIGHT TO-X TO-Y (- END-X FROM-X))
		    (IH=COPY.STRING FROM-X END-X FROM-Y TO-X TO-Y)
		    (IH=DELETE.STRING FROM-X END-X FROM-Y)))))))


(DEFUN IH=MOVE.STRING.TO.RIGHT (X-POS Y-POS NO.OF.CHARS)
  
  ;;; edited :  2.12.1987
  ;;; Input  :  X-POS, Y-POS denote a position in IH*INPUT.ARRAY
  ;;; Effect :  moves string specified by FROM-X, FROM-Y and the end of line NO.OF.CHARS to the right.
  ;;; Value  :  T, if there is enough space to perform the specified move, else nil.
  
  (COND ((<= (+ (IH=FIND.END.OF.LINE Y-POS) NO.OF.CHARS) IH*CHARS.PER.LINE)
	 (REPLACE (AREF IH*INPUT.ARRAY Y-POS)
		  (AREF IH*INPUT.ARRAY Y-POS)
		  :START1 (+ X-POS NO.OF.CHARS)
		  :START2 X-POS)
	 (SETF (AREF IH*END-OF-STRING Y-POS) (+ NO.OF.CHARS (AREF IH*END-OF-STRING Y-POS)))
	 (IH=INSERT.CHANGED.LINE Y-POS)
	 T)))


(DEFUN IH=MOVE.LINES.DOWN (Y-POS NO.OF.LINES)
  
  ;;; edited :  2.12.1987
  ;;; Input  :  Y-POS - denotes a line number.
  ;;; Effect :  Beginning with Y-POS moves all lines of IH*INPUT.ARRAY NO.OF.LINES down.
  ;;;           Notice: No additional space is allocated, therefore the last NO.OF.LINES are deleted. 
  ;;; Value  :  undefined.
  
  (REPLACE IH*INPUT.ARRAY IH*INPUT.ARRAY
	   :START1 (+ Y-POS NO.OF.LINES) :START2 Y-POS)
  (REPLACE IH*END-OF-STRING IH*END-OF-STRING
	   :START1 (+ Y-POS NO.OF.LINES) :START2 Y-POS))


(DEFMACRO IH=COPY.STRING (BEGIN-X END-X FROM-Y TO-X TO-Y)
  
  ;;; edited :  2.12.1987
  ;;; Input  :  BEGIN-X, FROM-Y rsp. END-X, FROM-Y rsp. TO-X, TO-Y denote three positions in IH*INPUT.ARRAY
  ;;; Effect :  the denoted string is copied to the specified position.
  ;;; Value  :  undefined.
  
  `(PROGN (REPLACE (AREF IH*INPUT.ARRAY ,TO-Y)
	   (AREF IH*INPUT.ARRAY ,FROM-Y)
	   :START1 ,TO-X
	   :END2 ,END-X
	   :START2 ,BEGIN-X)
    (IH=INSERT.CHANGED.LINE TO-Y)))


;;;;;========================================================================================================
;;;;;
;;;;; Functions to insert chars, strings or lines.
;;;;;
;;;;;========================================================================================================


(DEFUN IH=INSERT.CHAR (CHAR X-POS Y-POS)
  
  ;;; edited :  2.12.1987 / 27.1.88 mp
  ;;; Input  :  X-POS, Y-POS denote a position in IH*INPUT.ARRAY
  ;;; Effect :  CHAR is inserted at the denoted position, if there is enough space to do so,
  ;;;           no action otherwise. If the cursor is at the end of a line, a new line is created,
  ;;;           and the character is moved to that line.
  ;;; Value  :  NIL, if there is not enough space to insert the character, CHAR else
  
  (COND ((EQ IH*CHARS.PER.LINE X-POS)
	 (IH=INSERT.NEW.LINES (1+ Y-POS) 1)
	 (IH=MOVE.CURSOR.NEXT.LINE)
	 (IH=MOVE.STRING.TO.RIGHT 0 (1+ Y-POS) 1)
	 (IH=CHANGE.POSITION CHAR 0 (1+ Y-POS)))
	((EQ IH*CURSOR-X (IH=FIND.END.OF.LINE IH*CURSOR-Y))
	 (IH=CHANGE.POSITION CHAR X-POS Y-POS)
	 (INCF (AREF IH*END-OF-STRING Y-POS))
	 (SETQ IH*LOWER.CHANGED 'CURSORPOS))
	((IH=MOVE.STRING.TO.RIGHT X-POS Y-POS 1)
	 (IH=CHANGE.POSITION CHAR X-POS Y-POS))))



(DEFUN IH=INSERT.NEW.LINES (Y-POS NO.OF.LINES)
  
  ;;; edited :  2.12.1987
  ;;; Input  :  Y-POS denotes a line.
  ;;; Effect :  Inserts NO.OF.LINES lines after Y-POS.
  ;;; Value  :  undefined.
  
  (COND ((AND (OR (NULL (IH=FIND.LAST.FILLED.LINE))
		  (> Y-POS (IH=FIND.LAST.FILLED.LINE)))
	      (<= (+ Y-POS (1- NO.OF.LINES)) (IH=FIND.LAST.LINE))))
	(T (IH=ADJUST.ARRAY (+ NO.OF.LINES (IH=FIND.LAST.LINE)))
	   (IH=MOVE.LINES.DOWN Y-POS NO.OF.LINES)
	   (DOTIMES (Y NO.OF.LINES)
	     (SETF (AREF IH*INPUT.ARRAY (+ Y Y-POS)) (IH=CREATE.NEW.LINE))
	     (SETF (AREF IH*END-OF-STRING (+ Y Y-POS)) 0))))
  (IH=INSERT.CHANGED.LINES Y-POS 'END))



(DEFMACRO IH=CREATE.NEW.LINE ()
  
  ;;; edited :  2.12.1987
  ;;; Value  :  a new line.
  
  `(MAKE-STRING IH*CHARS.PER.LINE :INITIAL-ELEMENT #\SPACE))



(DEFMACRO IH=CHANGE.POSITION (CHAR X-POS Y-POS)
  
  ;;; edited :  2.12.1987
  ;;; Effect :  changes specified position into CHAR.
  
  `(SETF (AREF (AREF IH*INPUT.ARRAY ,Y-POS) ,X-POS) ,CHAR))


;;;;;========================================================================================================
;;;;;
;;;;; Functions to handle regions and registers.
;;;;;
;;;;;========================================================================================================


(DEFMACRO IH=REGION.IS ()
  
  ;;; edited :  2.12.1987
  ;;; Input  :  none.
  ;;; Value  :  a sexpression =/ NIL, if a region is selected.
  
  `(AREF IH*REGION 2))


(DEFMACRO IH=CLEAR.MARKED.REGION ()
  
  ;;; edited :  2.12.1987
  ;;; Effect :  Clears all informations about former regions.
  
  `(COND ((AREF IH*REGION 0)
	  (DOTIMES (I 4) (SETF (AREF IH*REGION I) NIL)))))


(DEFMACRO IH=CLEAR.REGISTER ()
  
  ;;; edited :  2.12.1987
  ;;; Effect :  Clears all registers.
  
  `(DOTIMES (I 10) (SETF (AREF IH*REGISTER I) NIL)))


(DEFUN IH=UNDERLINE.REGION (LINE FROM TO)
  
  ;;; edited :  2.12.1987
  ;;; Input  :  LINE - a number specifying a line of IH*INPUT.ARRAY
  ;;;           FROM, TO - two numbers specifying the begin and the end of the selected substring.
  ;;; Effect :  The specified substring is underlined.
  
  (COND ((AND (>= LINE IH*DELTA-Y) (< LINE (+ IH*DELTA-Y IH*LINES.ON.WINDOW)))
	 (IH=INSERT.CHANGED.LINE LINE)
	 (WIN-IO.UNDERLINE IH*WINDOW (+ 4 FROM) (+ 4 TO) (- LINE IH*DELTA-Y)))))


(DEFUN IH=MARK.MOUSE.POSITION (X-POS Y-POS)
  
  ;;; edited :  2.12.1987
  ;;; Input  :  X-POS, Y-POS denote a position in IH*INPUT.ARRAY
  ;;; Effect :  stores position to select a region.
  ;;;           If no position is yet stored, the given position is considered as the begin of a region.
  ;;;           Otherwise it's considered as the end of the region and the selected region is copied into
  ;;;           register 0.
  
  (IH=MOVE.CURSOR.NEAR X-POS Y-POS)
  (COND ((AREF IH*REGION 0)
	 (SETF (AREF IH*REGION 2) IH*CURSOR-X) 
	 (SETF (AREF IH*REGION 3) IH*CURSOR-Y)
	 (SETF (AREF IH*REGISTER 0) (IH=COPY.LINE.LIST.TO.STRING (AREF IH*REGION 0) (AREF IH*REGION 1)
								 (AREF IH*REGION 2) (AREF IH*REGION 3) T)))
	(T (IH=WRITE.CHANGES.TO.WINDOW)
	   (SETF (AREF IH*REGION 0) IH*CURSOR-X) 
	   (SETF (AREF IH*REGION 1) IH*CURSOR-Y))))



(DEFUN IH=INSERT.MARKED.REGION (X-POS Y-POS)
  
  ;;; edited :  2.12.1987
  ;;; Input  :  X-POS, Y-POS denote a position in IH*INPUT.ARRAY
  ;;; Effect :  Inserts string list of register 0 at the specified position.
  ;;; Value  :  a multiple value, specifying the end of the inserted string.
  
  (SETQ Y-POS (MAX Y-POS 0))
  (SETQ Y-POS (MIN Y-POS (IH=FIND.LAST.LINE)))
  (SETQ X-POS (MAX X-POS 0))
  (SETQ X-POS (MIN X-POS (IH=FIND.END.OF.LINE Y-POS)))
  (MULTIPLE-VALUE-SETQ (IH*CURSOR-X IH*CURSOR-Y)
    (COND ((>= Y-POS (IH=ACTUAL.BORDER))
	   (IH=INSERT.STRING.LIST X-POS Y-POS (AREF IH*REGISTER 0)))
	  (T (VALUES X-POS Y-POS)))))


(DEFUN IH=DELETE.MARKED.REGION ()
  
  ;;; edited :  2.12.1987 / changed 13.9.88 mp
  ;;; Input  :  none.
  ;;; Effect :  Deletes the substring, specified by the marked region, in IH*INPUT.ARRAY
  ;;; Value  :  undefined !
  
  (COND ((IH=REGION.IS)
	 (LET ((X-BEGIN (AREF IH*REGION 0)) (Y-BEGIN (AREF IH*REGION 1))
	       (X-END (AREF IH*REGION 2)) (Y-END (AREF IH*REGION 3)))
	   (COND ((OR (> Y-BEGIN Y-END)
		      (AND (EQ Y-END Y-BEGIN) (> X-BEGIN X-END)))
		  (PSETQ X-BEGIN X-END X-END X-BEGIN
			 Y-BEGIN Y-END Y-END Y-BEGIN)))
	   (COND ((EQ Y-BEGIN Y-END)
		  (IH=DELETE.STRING X-BEGIN X-END Y-BEGIN)
		  (SETQ IH*CURSOR-X X-BEGIN))
		 (T (IH=DELETE.STRING X-BEGIN (IH=FIND.END.OF.LINE Y-BEGIN) Y-BEGIN)
		    (IH=DELETE.STRING 0 X-END Y-END)
		    (MULTIPLE-VALUE-SETQ (IH*CURSOR-X IH*CURSOR-Y)
		      (IH=DELETE.LINES (1+ Y-BEGIN) (1- Y-END)))
		    (IH=HANDLE-RUBOUT)))
	   (IH=CLEAR.MARKED.REGION)))))



(DEFUN IH=SAVE.REGION ()
  
  ;;; edited :  2.12.1987
  ;;; Input  :  none.
  ;;; Effect :  Saves the context of register 0 into an user-specified register.
  ;;; Value  :  undefined.
  
  (LET ((CHAR (win-with.active.cursor IH*window (WIN-IO.ANY.TYI IH*WINDOW))))
    (COND ((SETQ CHAR (DIGIT-CHAR-P CHAR))
	   (COND ((AND (> CHAR 0) (< CHAR 10))
		  (SETF (AREF IH*REGISTER CHAR) (AREF IH*REGISTER 0))))))))


(DEFUN IH=COPY.REGION ()
  
  ;;; edited :  2.12.1987
  ;;; Input  :  none.
  ;;; Effect :  Restores the context of register 0 by an user-specified register,
  ;;;           also the context is inserted at the current cursor position into IH*INPUT.ARRAY.
  ;;; Value  :  a multiple value, specifying the end of the inserted string.
  
  (LET ((CHAR (win-with.active.cursor IH*window (WIN-IO.ANY.TYI IH*WINDOW))))
    (COND ((SETQ CHAR (DIGIT-CHAR-P CHAR))
	   (COND ((AND (> CHAR 0) (< CHAR 10))
		  (SETF (AREF IH*REGISTER 0) (AREF IH*REGISTER CHAR))
		  (IH=INSERT.MARKED.REGION IH*CURSOR-X IH*CURSOR-Y)))))))


(DEFUN IH=INSERT.STRING.LIST (X-POS Y-POS LINE.LIST)
  
  ;;; edited :  2.12.1987
  ;;; Input  :  X-POS, Y-POS denote a position in IH*INPUT.ARRAY
  ;;;           LINE.LIST - a list of strings.
  ;;; Effect :  inserts LINE.LIST at the specified position into IH*INPUT.ARRAY.
  ;;; Value  :  a multiple value, specifying the end of the inserted string.
  
  (LET ((X-END X-POS) (Y-END Y-POS))
    (COND (LINE.LIST
	   (COND ((IH=MOVE.STRING.TO.RIGHT X-POS Y-POS (ARRAY-DIMENSION (CAR LINE.LIST) 0))
		  (MULTIPLE-VALUE-SETQ (X-END Y-END) (IH=INSERT.STRING X-POS Y-POS (CAR LINE.LIST)))
		  (SETQ LINE.LIST (CDR LINE.LIST))))
	   (MAPL #'(LAMBDA (LINES)
		     (INCF Y-POS)
		     (COND ((CDR LINES)
			    (IH=INSERT.NEW.LINES Y-POS 1))
			   ((OR (> Y-POS (IH=FIND.LAST.LINE))
				(NOT (IH=MOVE.STRING.TO.RIGHT 0 Y-POS (ARRAY-DIMENSION (CAR LINES) 0))))
			    (IH=INSERT.NEW.LINES Y-POS 1)))
		     (MULTIPLE-VALUE-SETQ (X-END Y-END) (IH=INSERT.STRING 0 Y-POS (CAR LINES))))
		 LINE.LIST)))
    (VALUES X-END Y-END)))



(DEFUN IH=COPY.LINE.LIST.TO.STRING (X-BEGIN Y-BEGIN X-END Y-END &OPTIONAL MARK)
  
  ;;; edited :  2.12.1987
  ;;; Input  :  X-BEGIN, Y-BEGIN, X-END, Y-END denote two positions in IH*INPUT.ARRAY
  ;;;           MARK - a flag T/ NIL.
  ;;; Effect :  copies the specified text into a list of strings.
  ;;; Value  :  the copied list of strings.
  
  (LET (LINE.LIST)
    (COND ((OR (> Y-BEGIN Y-END)
	       (AND (EQ Y-END Y-BEGIN) (> X-BEGIN X-END)))
	   (PSETQ X-BEGIN X-END X-END X-BEGIN
		  Y-BEGIN Y-END Y-END Y-BEGIN)))
    (WHILE (<= Y-BEGIN Y-END)
      (COND ((NEQ Y-BEGIN Y-END)
	     (SETQ LINE.LIST (NCONC1 LINE.LIST (SUBSEQ (AREF IH*INPUT.ARRAY Y-BEGIN) X-BEGIN 
						       (IH=FIND.END.OF.LINE Y-BEGIN))))
	     (COND (MARK (IH=UNDERLINE.REGION Y-BEGIN X-BEGIN (IH=FIND.END.OF.LINE Y-BEGIN))))
	     (SETQ X-BEGIN 0))
	    (T (SETQ LINE.LIST (NCONC1 LINE.LIST (SUBSEQ (AREF IH*INPUT.ARRAY Y-BEGIN) X-BEGIN (1+ X-END))))
	       (COND (MARK (IH=UNDERLINE.REGION Y-BEGIN X-BEGIN X-END)))))
      (INCF Y-BEGIN))
    LINE.LIST))


(DEFUN IH=INSERT.STRING (X-POS Y-POS STRING &OPTIONAL (STRING-BEGIN 0))
  
  ;;; edited :  2.12.1987
  ;;; Input  :  X-POS, Y-POS denote a position in IH*INPUT.ARRAY
  ;;; Effect :  STRING is inserted at the specified position.
  ;;; Value  :  a multiple value, specifying the end of the inserted string.
  
  (REPLACE (AREF IH*INPUT.ARRAY Y-POS) STRING :START1 X-POS :START2 STRING-BEGIN)
  (LET ((LINE.LENGTH (IH=FIND.END.OF.LINE Y-POS)) (STRING.LENGTH (LENGTH STRING)))
    (COND ((> (+ STRING.LENGTH X-POS) LINE.LENGTH)
	   (SETF (AREF IH*END-OF-STRING Y-POS) (+ STRING.LENGTH X-POS))))
    (IH=INSERT.CHANGED.LINE Y-POS)
    (VALUES (+ STRING.LENGTH X-POS) Y-POS)))


;;;;;========================================================================================================
;;;;;
;;;;; Functions to
;;;;;
;;;;;========================================================================================================


(DEFUN IH=INSERT.CHANGED.LINE (Y-POS)
  (COND ((OR (NULL IH*LOWER.CHANGED)
	     (< Y-POS IH*LOWER.CHANGED))
	 (SETQ IH*LOWER.CHANGED Y-POS)))
  (COND ((EQ IH*UPPER.CHANGED 'END))
	((OR (NULL IH*UPPER.CHANGED)
	     (> Y-POS IH*UPPER.CHANGED))
	 (SETQ IH*UPPER.CHANGED Y-POS))))


(DEFUN IH=INSERT.CHANGED.LINES (FROM-LINE TO-LINE)
  (COND ((OR (NULL IH*LOWER.CHANGED)
	     (< FROM-LINE IH*LOWER.CHANGED))
	 (SETQ IH*LOWER.CHANGED FROM-LINE)))
  (COND ((EQ IH*UPPER.CHANGED 'END))
	((EQ TO-LINE 'END) (SETQ IH*UPPER.CHANGED 'END))
	((OR (NULL IH*UPPER.CHANGED)
	     (> TO-LINE IH*UPPER.CHANGED))
	 (SETQ IH*UPPER.CHANGED TO-LINE))))


(DEFMACRO IH=INSERT.CHANGED.CHARACTER ()
  `(SETQ IH*LOWER.CHANGED 'CURSORPOS))

;;;;; ==================================================================================================
;;;;;
;;;;; Functions to find special positions in the array, they do not change either the cursor position
;;;;; nor the input array
;;;;;
;;;;; ===================================================================================================


(DEFUN IH=DESCRIBE.DENOTED.OBJECT (X-POS Y-POS)
  (LET* ((STRING (AREF IH*INPUT.ARRAY Y-POS))
         (BEGIN (POSITION-IF #'COM-CHAR.IS.BREAK.CHARACTER
                             STRING :START 0 :END X-POS :FROM-END T))
         (END (POSITION-IF #'COM-CHAR.IS.BREAK.CHARACTER
                           STRING :START (1+ X-POS) :END (LENGTH STRING))))
    (CONS 'DESCRIBE  (SUBSEQ STRING
                             (COND (BEGIN (1+ BEGIN)) (T 0))
                             (COND (END) (T (LENGTH STRING)))))))

(DEFUN IH=SEARCH.FORWARD ()
  
  ;;; edited :  2.12.1987 / addapted 10.10.90 mp
  ;;; Input  :  none
  ;;; Effect :  asks the user for a string to be searched for in IH*INPUT.ARRAY.
  ;;;           sets cursor position to the next occurrence of this string
  ;;; Value  :  undefined.
  
  (SETQ IH*SEARCH.STRING (WIN-VL.CHOOSE IH*WINDOW "Enter string to search" IH*SEARCH.STRING))
  (LET ((X-POS IH*CURSOR-X) (Y-POS IH*CURSOR-Y) EOF FOUND)
    (WHILE (AND (NOT FOUND) (NOT EOF))
      (COND ((SETQ FOUND (COND ((AREF IH*INPUT.ARRAY Y-POS)
				(SEARCH IH*SEARCH.STRING (AREF IH*INPUT.ARRAY Y-POS) 
					:END2 X-POS :TEST #'STRING-EQUAL))))
	     (IH-SHOW.POSITION FOUND Y-POS))	    
	    ((<= (ih=find.last.line) Y-POS) (SETQ EOF T))
	    (T (INCF Y-POS) (SETQ X-POS 0))))))


(DEFUN IH=SEARCH.BACKWARD ()
  
  ;;; edited :  2.12.1987
  ;;; Input  :  none
  ;;; Effect :  asks the user for a string to be searched for in IH*INPUT.ARRAY.
  ;;;           sets cursor position to the previous occurrence of this string
  ;;; Value  :  undefined.
  
  (SETQ IH*SEARCH.STRING (WIN-VL.CHOOSE IH*WINDOW "Enter string to search" IH*SEARCH.STRING))
  (LET ((X-POS IH*CURSOR-X) (Y-POS IH*CURSOR-Y) EOF FOUND)
    (WHILE (AND (NOT FOUND) (NOT EOF))
      (COND ((SETQ FOUND (COND ((AREF IH*INPUT.ARRAY Y-POS)
				(SEARCH IH*SEARCH.STRING (AREF IH*INPUT.ARRAY Y-POS) 
					:FROM-END T :END2 X-POS :TEST #'STRING-EQUAL))))
	     (IH-SHOW.POSITION FOUND Y-POS))
	    ((ZEROP Y-POS) (SETQ EOF T))
	    (T (DECF Y-POS) (SETQ X-POS (IH=FIND.END.OF.LINE Y-POS)))))))


(DEFMACRO IH=FIND.LAST.LINE ()
  
  ;;; Value  :  the last line number of IH*INPUT.ARRAY.
  
  `(1- (ARRAY-DIMENSION IH*INPUT.ARRAY 0)))


(DEFMACRO IH=FIND.END.OF.LINE (LINE)
  
  ;;; Value  :  the last character of the specified line.
  
  `(AREF IH*END-OF-STRING ,LINE))


(DEFUN IH=FIND.NEXT.BLOCK (LINE)
  
  ;;; Value  :  the first line number of the next block.
  
  (COND ((SETQ LINE (IH=FIND.EMPTY.LINE LINE 'DOWN))
	 (IH=FIND.NON.EMPTY.LINE LINE 'DOWN))))


(DEFUN IH=FIND.PREVIOUS.BLOCK (LINE)
  
  ;;; Value  :  the first line number of the previous block.
  
  (COND ((AND (SETQ LINE (IH=FIND.EMPTY.LINE LINE 'UP))
	      (SETQ LINE (IH=FIND.NON.EMPTY.LINE LINE 'UP))
	      (SETQ LINE (IH=FIND.EMPTY.LINE LINE 'UP))
	      (SETQ LINE (IH=FIND.NON.EMPTY.LINE LINE 'DOWN)))
	 LINE)
	(T 0)))


(DEFUN IH=FIND.END.OF.NEXT.BLOCK (START.LINE)

  ;;; edited :  2.12.1987
  ;;; Input  :  none.
  ;;; Effect :  see value.
  ;;; Value  :  a multiple value: IH*INPUT.ARRAY, the next non empty line below the border,
  ;;;           and the next following empty line.
  
  (WHILE (AND (SETQ START.LINE (IH=FIND.NON.EMPTY.LINE START.LINE 'DOWN))
	      (NULL (POSITION-IF #'(LAMBDA (X) (NEQ X #\SPACE)) (AREF IH*INPUT.ARRAY START.LINE))))
	 (SETF (AREF IH*END-OF-STRING START.LINE) 0))
  (COND (START.LINE 
	 (COND ((IH=FIND.EMPTY.LINE START.LINE 'DOWN))
	       (T (IH=FIND.LAST.LINE))))))


(DEFUN IH=FIND.NON.BLANK.LINE (LINE DIRECTION)
  
;;; Value  : index of the next line in the specified direction, which is neither empty nor contains
;;;          only spaces.
  
  (POSITION-IF  #'(LAMBDA (X) (position-if #'(lambda (y) (neq #\space y)) x)) IH*INPUT.ARRAY
		;;  #'(lambda (x) (> ih*chars.per.line (count #\space x))) IH*INPUT.ARRAY
		:FROM-END (EQ DIRECTION 'UP)
		:START (COND ((EQ DIRECTION 'UP) 0)
			     (T LINE))
		:END (COND ((EQ DIRECTION 'UP) LINE)
			   (T (IH=FIND.LAST.LINE)))))


(DEFUN IH=FIND.EMPTY.LINE (LINE DIRECTION)
  
;;; Value  : index of the next line in the specified direction, which is really empty,
;;;          i.e. doesn't even contain spaces.
  
  (POSITION-IF #'ZEROP IH*END-OF-STRING
	       :FROM-END (EQ DIRECTION 'UP)
	       :START (COND ((EQ DIRECTION 'UP) 0)
			    (T LINE))
	       :END (1+ (COND ((EQ DIRECTION 'UP) LINE)
			      (T (IH=FIND.LAST.LINE))))))


(DEFUN IH=FIND.NON.EMPTY.LINE (LINE DIRECTION)
  
;;; Value  : index of the next line in the specified direction, which contains any character.
  (POSITION-IF #'(LAMBDA (X) (NOT (ZEROP X))) IH*END-OF-STRING
	       :FROM-END (EQ DIRECTION 'UP)
	       :START (COND ((EQ DIRECTION 'UP) 0)
			    (T LINE))
	       :END (1+ (COND ((EQ DIRECTION 'UP) LINE)
			      (T (IH=FIND.LAST.LINE))))))

(DEFMACRO IH=FIND.LAST.FILLED.LINE ()
  `(IH=FIND.NON.EMPTY.LINE (IH=FIND.LAST.LINE) 'UP))


(DEFUN IH=FIND.CORRESPONDING.BRACKET (X-POS Y-POS)
  (LET ((COUNTER 1) ABORT)
    (WHILE (AND (NEQ COUNTER 0) (NULL ABORT))
      (COND ((NULL (SETQ ABORT (COND ((> X-POS 0) (DECF X-POS) NIL)
				     ((AND (> Y-POS 0) 
					   (NOT (ZEROP (IH=FIND.END.OF.LINE (DECF Y-POS)))))
				      (SETQ X-POS (IH=FIND.END.OF.LINE Y-POS))
				      NIL)
				     (T T))))
	     (COND ((EQL (AREF (AREF IH*INPUT.ARRAY Y-POS) X-POS) #\))
		    (INCF COUNTER))
		   ((EQL (AREF (AREF IH*INPUT.ARRAY Y-POS) X-POS) #\()
		    (DECF COUNTER))))))
    (COND ((EQL COUNTER 0) (VALUES X-POS Y-POS)))))


;;;;; =======================================================================================================
;;;;;
;;;;; Functions to modify the array
;;;;;
;;;;; =======================================================================================================


(DEFUN IH=ADJUST.ARRAY (MAX.NUMBER)
  (LET ((DIM (ARRAY-DIMENSION IH*INPUT.ARRAY 0)))
    (COND ((< MAX.NUMBER DIM))
	  (T (SETF IH*INPUT.ARRAY (ADJUST-ARRAY IH*INPUT.ARRAY (1+ MAX.NUMBER)))
	     (SETF IH*END-OF-STRING (ADJUST-ARRAY IH*END-OF-STRING (1+ MAX.NUMBER)))
	     (WHILE (<= DIM MAX.NUMBER)
	       (SETF (AREF IH*INPUT.ARRAY DIM) (IH=CREATE.NEW.LINE))
	       (SETF (AREF IH*END-OF-STRING DIM) 0)
	       (INCF DIM))))))


;;;;; =======================================================================================================
;;;;;
;;;;; Functions to modify or test the border between proved area and scratchpad.
;;;;;
;;;;; =======================================================================================================


(DEFMACRO IH=BORDER.CHECK ()
  
  ;;; edited at 12-may-87
  ;;; Input  : none
  ;;; Effect : decides,whether cursor is upper or lower of the border
  ;;; Value  : t,if lower,else nil
  
  `(>= IH*CURSOR-Y (CAAR IH*BORDER)))


(DEFMACRO IH=ACTUAL.BORDER ()
  
  ;;; edited at 04-may-87
  ;;; Input  : none
  ;;; Effect : returns actual border
  ;;; Value  : actual border
  
  `(CAAR IH*BORDER))


(DEFMACRO IH=FORMER.BORDER (NUMBER)
  
  ;;; Edited at 07-may-87
  ;;; Input  :number of the former border
  ;;; Effect :returns the nth former border
  ;;; Value  :nth former border
  
  
  `(COND ((NTH (1- ,NUMBER) IH*BORDER))
    (T 0)))




