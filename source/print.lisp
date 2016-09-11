;;; -*- Syntax: Common-lisp; Package: INKA; Mode: LISP -*-

(IN-PACKAGE :INKA)


(DEFSTRUCT (PR*OBJECT (:CONC-NAME PR=OBJ.) (:PRINT-FUNCTION PR=OBJ.PRINT))

  TYPE                                  ; 
  STYLE
  (X-POS       0   :TYPE FIXNUM)
  (Y-POS       0   :TYPE FIXNUM)
  (WIDTH       0   :TYPE FIXNUM)
  (HEIGHT      0   :TYPE FIXNUM)
  (CENTER      0   :TYPE FIXNUM)
  (OBJECTS     NIL :TYPE LIST)
  (ATTRIBUTES  NIL :TYPE LIST)
  )


(DEFSTRUCT (PR*GRAPH.NODE (:CONC-NAME PR=GRAPH.NODE.) (:PRINT-FUNCTION PR=GRAPH.NODE.PRINT))

  (TEXT        NIL :TYPE (OR NULL PR*OBJECT))   ; the printed representation of the node
  (SUCCS       NIL :TYPE LIST)          ; list of all successors
  (PREDS       NIL :TYPE LIST)          ; list of all predecessors
  BARY                                  ; the bary-center of all successors / predecessors
  (POS         0   :TYPE FIXNUM)        ; actual position of node in its graph-level
  (OLD.POS     0   :TYPE FIXNUM)        ; saved position of node in its graph-level
  (LEVEL       0   :TYPE FIXNUM)        ; graph-level of the node
  )


(defstruct (pr*buffer (:CONC-NAME PR=Buffer.) (:PRINT-FUNCTION PR=buffer.PRINT))

  (stack             (list 0)  :TYPE LIST)          ; stack of integers specifying the size of indents
  (actual.string     ""        :TYPE STRING)        ; the actual string in which the text is copied
  (actual.attributes nil       :type LIST)          ; the attributes of the characters in the actual string
  (actual.index      0         :type fixnum)        ; the first non-used position in the actual string
  (actual.width      0         :type FIXNUM)        ; the length of the actual line written so far
  (actual.y-pos      0         :type FIXNUM)        ; the y-pos of the actual string
  (actual.x-pos      0         :type FIXNUM)        ; the x-pos of the actual string
  (max.width         0         :TYPE FIXNUM)        ; the maximal length (in pixel) of a line
  (max.chars         0         :TYPE FIXNUM)        ; the maximal length (in chars) of a line
  (object.list       nil       :type LIST)          ; the list of pr*objects denoting the written lines
  )


;;; global variables for graphic purposes:


(DEFVAR PR*SCALING 1)

(DEFVAR PR*BASELINESTRETCH 1.5)

(DEFVAR PR*DISTANCE 2)

(defvar pr*actual.font 'roman)
(defvar pr*actual.size 'D)
(defvar pr*actual.colour "Black")
(defvar pr*actual.sizemetric 'D)

(defvar pr*symboltable.font 'symbol)
(DEFVAR PR*LOCAL.POS (CONS 0 0))

(defvar pr*hash.table (make-hash-table :rehash-size 1.5 :test #'equal))

;;; global variables for text purposes:

(DEFVAR PR*OUTPUT NIL)
(DEFVAR PR*LINELENGTH 80)
(DEFVAR PR*NEWLINE NIL)
(DEFVAR PR*INHIBIT.RENAMING)
(DEFVAR PR*SORTS NIL)

(DEFVAR PR*APPLY.FCT NIL)

(DEFVAR PR*X 0)
(DEFVAR PR*Y 0)

(DEFVAR PR*actual.object NIL)


(PROCLAIM '(TYPE FIXNUM PR*LINELENGTH))


(DEFUN PR-DEFAULT.WIDTH ()
  ;;; Input: None
  ;;; Value: a number denoting the default width of a text line
    
  800)


;;;;;==================================================================================================
;;;;; 
;;;;; Section I
;;;;;
;;;;; Interface - Funtion for Description Windows
;;;;;
;;;;;==================================================================================================


(defun pr-parse.gterm.as.tree (gterm &optional eval.function)

  (cond ((null eval.function) (setq eval.function #'(lambda (x y) (declare (ignore x y)) nil))))
  (cond ((pr=parse.gterm.as.tree gterm eval.function nil))
	(t (pr-parse.string "False"))))
	


(defmacro pr-parse.gterm (gterm char.length &optional eval.function &rest attributes)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.gterm.1 ,gterm ,char.length ,eval.function pr*attributes))))


(defmacro pr-parse.modifier (mod length &rest attributes)

  `(let* ((pr*attributes (list ,@attributes)) (modifier ,mod)
	  (gterm (da-gterm.create (cond ((da-term.is (da-modifier.input modifier)) (da-predicate.equality))
					(t 'impl))
				  (list (da-modifier.input modifier)
					(da-modifier.value modifier)))))
     (cond ((da-modifier.condition modifier)
	    (setq gterm (da-gterm.create 'impl 
					 (list 
					  (da-formula.junction.closure 
					   'and (mapcar #'(lambda (lit) (da-formula.negate lit))
							(da-modifier.condition modifier)))
					  gterm)))))
      (pr=with.attributes pr*attributes 
			  (pr=parse.gterm.1 gterm ,length nil pr*attributes))))




(defun pr=parse.gterm.1 (gterm char.length eval.function attributes)

  ;;; Input:   a gterm, a integer or nil, a functional with two arguments (gterm and taf)
  ;;;          and a property list of attributes
  ;;; Effect:  parses gterm and creates a printable object
  ;;; Value:   the printable object

  (cond ((null eval.function) (setq eval.function #'(lambda (x y) (declare (ignore x y)) nil))))
  (cond ((null char.length) (setq char.length 100))
	((and (consp char.length) (eq (car char.length) 'width)) 
	 (setq char.length (floor (/ (cdr char.length) (pr=string.width "l"))))))
  (let ((buffer (make-pr*buffer)))
       (pr=buffer.reset buffer char.length)
       (let ((length.list (pr=gterm.length.list gterm eval.function buffer nil nil))
	     (max.width 0))
	 (declare (type fixnum max.width))
	 (pr=gterm.parse buffer gterm length.list nil)
	 (cond ((neq 0 (pr=buffer.actual.width buffer)) (pr=buffer.newline buffer)))
	 (mapc #'(lambda (obj) 
		  (setq max.width (max max.width (+ (pr=obj.x-pos obj) (pr=obj.width obj)))))
	      (pr=buffer.object.list buffer))
	 (make-pr*object :CENTER (FLOOR (/ max.WIDTH 2)) :X-POS 0 :Y-POS 0
			 :WIDTH max.width :TYPE 'LIST.OF.OBJECTS :STYLE nil
			 :HEIGHT (pr=buffer.actual.y-pos buffer)
			 :OBJECTS (pr=buffer.object.list buffer)
			 :ATTRIBUTES attributes))))


(defmacro pr-parse.subst (subst length &rest attributes)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.subst ,subst ,length pr*attributes))))


(defun pr=parse.subst (subst length attributes)

  ;;; Input:   a gterm, a integer or nil, a functional with two arguments (gterm and taf)
  ;;;          and a property list of attributes
  ;;; Effect:  parses gterm and creates a printable object
  ;;; Value:   the printable object

  (let ((buffer (make-pr*buffer)))
    (pr=buffer.reset buffer length)
    (let ((length.list (pr=subst.length.list subst buffer)) (max.width 0))
      (declare (type fixnum max.width))
      (pr=subst.parse buffer subst length.list)
      (cond ((neq 0 (pr=buffer.actual.width buffer)) (pr=buffer.newline buffer)))
      (mapc #'(lambda (obj) 
		(setq max.width (max max.width (+ (pr=obj.x-pos obj) (pr=obj.width obj)))))
	    (pr=buffer.object.list buffer))
      (make-pr*object :CENTER (FLOOR (/ (pr=buffer.max.WIDTH buffer) 2)) :X-POS 0 :Y-POS 0
		      :WIDTH max.width :TYPE 'LIST.OF.OBJECTS :STYLE nil
		      :HEIGHT (pr=buffer.actual.y-pos buffer)
		      :OBJECTS (pr=buffer.object.list buffer)
		      :ATTRIBUTES attributes))))


(defmacro pr-parse.headline (LINE ITEM &OPTIONAL STYLE &REST ATTRIBUTES)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.headline ,line ,item ,style pr*attributes))))


(DEFUN PR=PARSE.HEADLINE (LINE ITEM STYLE ATTRIBUTES)

  ;;; Input : a string, a drawable item, and optionally an atom
  ;;; Value : a crawable is created with \verb$LINE$ as headline (underlined) and below the \verb$ITEM$,
  ;;;         \verb$STYLE$ indicates wheter \verb$ITEM$ is centered or not

  (DECLARE (IGNORE STYLE))
  (MAKE-PR*OBJECT :CENTER (PR=OBJ.CENTER ITEM)
		  :X-POS 0
		  :Y-POS 0
		  :WIDTH (PR=OBJ.WIDTH ITEM)
		  :HEIGHT (PR=OBJ.HEIGHT ITEM)
		  :TYPE 'HEADER
		  :OBJECTS (LIST LINE ITEM)
		  :ATTRIBUTES ATTRIBUTES))


(defmacro pr-parse.center (OBJECT WIDTH HEIGHT &REST ATTRIBUTES)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.center ,OBJECT ,WIDTH ,HEIGHT pr*attributes))))

 
(DEFUN PR=PARSE.CENTER (OBJECT WIDTH HEIGHT ATTRIBUTES)

  ;;; Input:  a printable object, width and height of the new object and a 
  ;;;         property list of attributes
  ;;; Value:  the prinable object
  
  (DECLARE (TYPE FIXNUM WIDTH HEIGHT))
  (SETQ WIDTH (MAX WIDTH (PR=OBJ.WIDTH OBJECT)))
  (SETQ HEIGHT (MAX HEIGHT (PR=OBJ.HEIGHT OBJECT)))
  (SETF (PR=OBJ.X-POS OBJECT) (FLOOR (/ (- WIDTH (PR=OBJ.WIDTH OBJECT)) 2)))
  (SETF (PR=OBJ.Y-POS OBJECT) (FLOOR (/ (- HEIGHT (PR=OBJ.HEIGHT OBJECT)) 2)))
  (MAKE-PR*OBJECT :CENTER (FLOOR (/ WIDTH 2))
		  :X-POS 0
		  :Y-POS 0
		  :WIDTH WIDTH
		  :HEIGHT HEIGHT
		  :TYPE 'TABLE
		  :OBJECTS (LIST OBJECT)
		  :ATTRIBUTES ATTRIBUTES))


(defmacro pr-parse.bitmap (bitmap.file size &rest attributes)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.bitmap ,bitmap.file ,size pr*attributes))))



(defun pr=parse.dot (colour)

  (pr=parse.bitmap (case colour
			 (red "redball")
			 (green "greenball")
			 (blue "blueball"))
		   0.7
		   nil))


(defun pr=parse.bitmap (bitmap.file size ATTRIBUTES)

  (multiple-value-bind (width height) 
      (win-bitmap.size bitmap.file)
    (declare (type fixnum width height))
    (cond (size (MULTIPLE-VALUE-BIND (CHAR.HEIGHT char.ascend)
				     (PR=ACTUAL.FONT.HEIGHT)
				     (declare (type fixnum char.height char.ascend))
				     (setq char.height (* char.height size))
				     (setq width (floor (* width (/ char.height height))))
				     (setq height (floor char.height)))))
    (MAKE-PR*OBJECT :CENTER (FLOOR (/ WIDTH 2))
		     :X-POS 0
		     :Y-POS 0
		     :WIDTH WIDTH
		     :HEIGHT HEIGHT
		     :TYPE 'BITMAP
		     :OBJECTS (list bitmap.file)
		     :ATTRIBUTES ATTRIBUTES)))


(defmacro pr-parse.itemize (ITEMS SEPARATOR &REST ATTRIBUTES)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.ITEMIZE ,ITEMS ,SEPARATOR pr*attributes))))


(DEFUN PR=PARSE.ITEMIZE (ITEMS SEPARATOR ATTRIBUTES)

  ;;; Input:  a list of strings, a description of an separator, and optionally a distance between the
  ;;;         items
  ;;; Value:  creates a drawable of the above specification
  
  (LET ((HEIGHT 0) (WIDTH 0) (ITEM.WIDTH 0) (COUNTER 0)
	   SEPARATORS ITEM LINES)
    (DECLARE (TYPE FIXNUM WIDTH ITEM.WIDTH HEIGHT)
	     (TYPE (OR NULL PR*OBJECT) ITEM))
    (MAPL #'(LAMBDA (ITEMS.TAIL)
	      (SETQ ITEM (CAR ITEMS.TAIL))
	      (COND ((eq 'line (pr=obj.type ITEM)))
		    ((EQ SEPARATOR 'NUMERATE) 
		     (PUSH (PR-PARSE.STRING (FORMAT NIL "~D." COUNTER)) SEPARATORS))
		    ((EQ SEPARATOR 'ITEMIZE) (PUSH (PR=PARSE.DOT 'red) SEPARATORS))
		    ((STRINGP SEPARATOR) (PUSH (PR-PARSE.STRING SEPARATOR) SEPARATORS))
		    ((CONSP SEPARATOR) 
		     (PUSH (PR-PARSE.STRING (CAR SEPARATOR) :font 'bold) SEPARATORS)
		     (POP SEPARATOR)))
	      (SETF (PR=OBJ.Y-POS ITEM) HEIGHT)
	      (cond ((neq 'line (pr=obj.type ITEM))
		     (SETQ ITEM.WIDTH (MAX ITEM.WIDTH (PR=OBJ.WIDTH ITEM)))
		     (cond (SEPARATORS (SETQ WIDTH (MAX WIDTH (PR=OBJ.WIDTH (CAR SEPARATORS))))
				       (SETF (PR=OBJ.Y-POS (CAR SEPARATORS)) HEIGHT)))
		     (INCF HEIGHT (FLOOR (COND ((CDR ITEMS.TAIL) (+ (PR=OBJ.HEIGHT ITEM) 
								    (* 0.5 (pr=actual.size))))
					       (T (PR=OBJ.HEIGHT ITEM))))))
		    (T (INCF HEIGHT (+ (PR=OBJ.objects ITEM) (FLOOR (/ (pr=actual.size) 2))))
		       (PUSH ITEM LINES))))
	  ITEMS)
    (COND (SEPARATORS (INCF WIDTH (PR=actual.size))))
    (MAPC #'(LAMBDA (LINE) (SETF (PR=OBJ.WIDTH LINE) (+ WIDTH ITEM.WIDTH))) LINES)
    (MAPC #'(LAMBDA (ITEM) (SETF (PR=OBJ.X-POS ITEM) WIDTH)) ITEMS)
    (MAKE-PR*OBJECT :CENTER (FLOOR (/ (+ WIDTH ITEM.WIDTH) 2)) :X-POS 0 :Y-POS 0
		    :WIDTH (+ WIDTH ITEM.WIDTH) :TYPE 'LIST.OF.OBJECTS :STYLE NIL
		    :HEIGHT HEIGHT :OBJECTS (NCONC SEPARATORS ITEMS) :ATTRIBUTES ATTRIBUTES)))


(defmacro pr-parse.closure (ITEM STYLE &OPTIONAL (LINE.THICKNESS 1) (FILL.COLOUR NIL)
				 (SHADOWED 0) &REST ATTRIBUTES)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.closure ,ITEM ,STYLE ,LINE.THICKNESS ,FILL.COLOUR ,SHADOWED pr*attributes))))


(DEFUN PR=PARSE.CLOSURE (ITEM STYLE LINE.THICKNESS FILL.COLOUR SHADOWED ATTRIBUTES)

  (LET ((HEIGHT (PR=OBJ.HEIGHT ITEM)) (WIDTH (PR=OBJ.WIDTH ITEM)) (SIZE 0) (X-OFFSET 0) (Y-OFFSET 0)
	(pr*distance (cond ((getf attributes :distance)) (t pr*distance))))
    (DECLARE (TYPE FIXNUM WIDTH HEIGHT SIZE X-OFFSET Y-OFFSET))
    (SETQ LINE.THICKNESS (MAX 1 (FLOOR (* LINE.THICKNESS PR*SCALING))))
    (CASE STYLE 
	  (BOXED (SETQ X-OFFSET (+ (PR=ACTUAL.DISTANCE) (ABS LINE.THICKNESS) SHADOWED))
		 (SETQ Y-OFFSET (+ (PR=ACTUAL.DISTANCE) (ABS LINE.THICKNESS) SHADOWED)))
	  (OVAL	   
	   (SETQ Y-OFFSET (CEILING (* HEIGHT 0.25)))
	   (SETQ X-OFFSET (FLOOR (+ (SQRT (+ (* WIDTH WIDTH 0.25) (* HEIGHT HEIGHT 1/16)))
				    (* HEIGHT 0.25) (* WIDTH -0.5) 2))))
	  (CIRCLE
	   (SETQ SIZE (MAX HEIGHT WIDTH))
	   (SETQ X-OFFSET (FLOOR (+ (PR=ACTUAL.DISTANCE) (ABS LINE.THICKNESS) (/ (- SIZE WIDTH) 2))))
	   (SETQ Y-OFFSET (FLOOR (+ (PR=ACTUAL.DISTANCE) (ABS LINE.THICKNESS) (/ (- SIZE HEIGHT) 2))))))
    (INCF (PR=OBJ.X-POS ITEM) X-OFFSET)
    (INCF (PR=OBJ.Y-POS ITEM) Y-OFFSET)
    (MAKE-PR*OBJECT :CENTER (FLOOR (/ (+ (* 2 X-OFFSET) WIDTH SHADOWED) 2)) :X-POS 0 :Y-POS 0
		    :WIDTH (+ (* 2 X-OFFSET) WIDTH SHADOWED)
		    :HEIGHT (+ (* 2 Y-OFFSET) HEIGHT SHADOWED)
		    :TYPE 'CLOSURE :STYLE (LIST STYLE LINE.THICKNESS FILL.COLOUR SHADOWED)
		    :OBJECTS (LIST ITEM)
		    :ATTRIBUTES ATTRIBUTES)))
  

(defmacro pr-parse.lines (ITEMS STYLE &REST ATTRIBUTES)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.lines ,ITEMS ,STYLE))))



(DEFUN PR=PARSE.LINES (ITEMS STYLE)
  
  ;;; Input: a list of strings, an atom (denoting the way the items are to be placed),
  ;;;        optionally a distance between the items, and a header
  ;;; Value: creates a drawable of the above specification

  (LET ((TREE (PR-PARSE.ITEMIZE ITEMS NIL)))
    (COND ((CAR STYLE)
	   (PR-PARSE.CLOSURE TREE (CAR STYLE) (SECOND STYLE) NIL 0))
	  (T TREE))))


(defmacro pr-parse.table (ENTRIES COLUMNS &REST ATTRIBUTES)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.table ,ENTRIES ,COLUMNS pr*attributes))))


(DEFUN PR=PARSE.TABLE (ENTRIES COLUMNS ATTRIBUTES)

  ;;; Input: a list of drawable items and a number
  ;;; Value: generates a drawable of the above specification where all items of \verb$ENTRIES$ are to
  ;;;        be drawn as a table where \verb$COLUMNS$ specifies the number of columns

  (LET* ((LINES (CEILING (/ (LENGTH ENTRIES) COLUMNS))) (WIDTH 0)
	 (ALL.ENTRIES ENTRIES) entry (X-POS 0) (INC (* 3 (PR=actual.distance))) (Y-POS INC)
	 ALL.COLUMNS (HEIGHT 0))
    (DECLARE (TYPE FIXNUM LINES WIDTH Y-POS HEIGHT))
    (WHILE ENTRIES
      (PUSH (SUBSEQ ENTRIES 0 (MIN LINES (length ENTRIES))) ALL.COLUMNS)
      (SETQ ENTRIES (NTHCDR LINES ENTRIES)))
    (SETQ ALL.COLUMNS (REVERSE ALL.COLUMNS))
    (MAPC #'(LAMBDA  (COLUMN)
	      (SETQ WIDTH 0)
	      (MAPC #'(LAMBDA (ITEM)
			(SETF (PR=OBJ.X-POS ITEM) (+ INC X-POS))
			(SETQ WIDTH (MAX WIDTH (PR=OBJ.WIDTH ITEM))))
		    COLUMN)
	      (INCF X-POS (+ (* 4 INC) WIDTH)))
	  ALL.COLUMNS)
    (DOTIMES (I LINES)
	     (SETQ HEIGHT 0)
	     (MAPC #'(LAMBDA (column)
		       (COND ((SETQ ENTRY (NTH I COLUMN))
			      (SETF (PR=OBJ.Y-POS entry) (+ INC Y-POS))
			      (SETQ HEIGHT (MAX HEIGHT (PR=OBJ.HEIGHT entry))))))
		   ALL.COLUMNS)
	     (INCF Y-POS (+ (* 2 INC) HEIGHT)))
    (MAKE-PR*OBJECT :CENTER (FLOOR (/ x-pos 2))  :X-POS 0 :Y-POS 0
		    :WIDTH (- X-POS (* 4 INC)) :HEIGHT (- Y-POS (* 2 INC)) :TYPE 'TABLE
		    :OBJECTS ALL.ENTRIES :ATTRIBUTES ATTRIBUTES)))
  

(defmacro pr-parse.string (string &REST ATTRIBUTES)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.string ,string pr*attributes))))


(DEFUN PR=PARSE.STRING (STRING ATTRIBUTES)

  ;;; Input: a string, an atom (specifying a font), and a number (specifying the font size)
  ;;; Value: generates a drawable of the above specification, that is \verb$STRING$ is drawn 
  ;;;        in font \verb$FONT$ with size \verb$SIZE$
  
  (LET (WIDTH CHAR.HEIGHT char.ascend index
	      (style (getf attributes :style)))
    (MULTIPLE-VALUE-SETQ (CHAR.HEIGHT char.ascend) (PR=ACTUAL.FONT.HEIGHT))
    (cond ((setq index (getf attributes :box))
	   (setf (getf attributes :box) (list (pr=char.width #\)) 
					      char.ascend (pr=string.width (subseq string 0 index))))))
    (COND ((EQ STYLE 'UNDERLINE) (INCF CHAR.HEIGHT 2)))
    (cond ((not (stringp string)) (setq string (format nil "~A" string))))
    (SETQ WIDTH (PR=string.width STRING))
    (MAKE-PR*OBJECT :CENTER (FLOOR (/ WIDTH 2)) :X-POS 0 :Y-POS 0
		    :WIDTH WIDTH :TYPE 'STRING :STYLE STYLE
		    :HEIGHT CHAR.HEIGHT :OBJECTS (list STRING)
		    :ATTRIBUTES (cons :ASCEND (cons char.ascend ATTRIBUTES)))))


(defmacro pr-parse.scripts (item &OPTIONAL item.list &REST ATTRIBUTES)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.scripts ,ITEM ,item.list
			   pr*attributes))))


(defun pr=parse.scripts (item item.list ATTRIBUTES)

  (let ((half.ascent (floor (/ (cond ((getf (pr=obj.attributes item) :ascend)) (t (pr=obj.height item))) 2)))
	(l.width 0) (r.width 0) (t.height 0) (b.height 0) total.width total.height overlap)
    (mapc #'(lambda (sub.item)
	      (cond ((member (car sub.item) '(LT LD))
		     (setq l.width (max l.width (pr=obj.width (cdr sub.item)))))
		    ((member (car sub.item) '(Top Down))
		     (setq overlap (floor (/ (- (pr=obj.width (cdr sub.item)) (pr=obj.width item)) 2)))
		     (setq l.width (max l.width overlap))
		     (setq r.width (max r.width overlap)))
		    ((member (car sub.item) '(RT RD))
		     (setq r.width (max r.width (pr=obj.width (cdr sub.item))))))
	      (cond ((member (car sub.item) '(LT RT)) (setq t.height (max t.height (pr=obj.height (cdr sub.item)))))
		    ((member (car sub.item) '(LD RD)) (setq b.height (max b.height (pr=obj.height (cdr sub.item)))))
		    ((eq (car sub.item) 'Top) (setq t.height (max t.height (+ (pr=obj.height (cdr sub.item)) half.ascent))))
		    ((eq (car sub.item) 'Down) (setq b.height (max b.height (+  (pr=obj.height (cdr sub.item)) 
										(- (pr=obj.height item) half.ascent)))))))
	  item.list)
    (setf (pr=obj.x-pos item) (1+ l.width))
    (setf (pr=obj.y-pos item) (max 0 (- t.height half.ascent)))
    (setf total.width (+ l.width (pr=obj.width item) r.width))
    (setq total.height (+ (pr=obj.y-pos item) (pr=obj.height item) (max 0 (- (+ b.height half.ascent) (pr=obj.height item)))))
    (mapc #'(lambda (sub.item)
	      (cond ((member (car sub.item) '(LT LD)) 
		     (setf (pr=obj.x-pos (cdr sub.item)) (- l.width (pr=obj.width (cdr sub.item)))))
		    ((member (car sub.item) '(RT RD)) 
		     (setf (pr=obj.x-pos (cdr sub.item)) (+ l.width (pr=obj.width item) 2)))
		    ((member (car sub.item) '(Top Down))
		     (setf (pr=obj.x-pos (cdr sub.item))
			   (- l.width (floor (/ (- (pr=obj.width (cdr sub.item)) (pr=obj.width item)) 2))))))	      
	      (cond ((member (car sub.item) '(LT RT))
		     (setf (pr=obj.y-pos (cdr sub.item)) (- t.height (pr=obj.height (cdr sub.item)))))
		    ((member (car sub.item) '(LD RD)) (setf (pr=obj.y-pos (cdr sub.item)) (1+ (max t.height half.ascent))))
		    ((eq (car sub.item) 'Top) 
		     (setf (pr=obj.y-pos (cdr sub.item))
			   (- t.height half.ascent (pr=obj.height (cdr sub.item)) )))
		    ((eq (car sub.item) 'Down) 
		     (setf (pr=obj.y-pos (cdr sub.item)) (+ (pr=obj.y-pos item) (pr=obj.height item))))))
	  item.list)
    (make-pr*object :x-pos 0 :y-pos 0 :type 'LIST.OF.OBJECTS 
		    :width total.width :center (floor (/ total.width 2))
		    :height total.height
		    :objects (cons item (mapcar #'(lambda (item) (cdr item)) item.list))
		    :attributes (CONS :ASCEND (cons (+ (* 2 half.ascent) (pr=obj.y-pos item)) ATTRIBUTES)))))
	  


(defmacro pr-parse.FLOAT.TEXT (ITEMS &OPTIONAL (MAX.WIDTH (PR-DEFAULT.WIDTH)) &REST ATTRIBUTES)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.FLOAT.TEXT ,ITEMS ,MAX.WIDTH pr*attributes))))


(DEFUN PR=PARSE.FLOAT.TEXT (ITEMS MAX.WIDTH ATTRIBUTES)

  ;;; Input: a list of drawables, and a number
  ;;; Value: generates a drawable where all \verb$ITEMS$ are to be drawn as floating text with
  ;;;       line-length \verb$MAX.WIDTH$

  (DECLARE (TYPE FIXNUM MAX.WIDTH) (TYPE LIST ITEMS))
  (LET ((OBJECTS (LIST (MAKE-PR*OBJECT :CENTER 0 :X-POS 0 :Y-POS 0 :TYPE 'LIST.OF.OBJECTS
				       :WIDTH 0 :HEIGHT 0 :OBJECTS NIL
				       :ATTRIBUTES (CONS :ASCEND (CONS 0 ATTRIBUTES)))))
	LINES)
    (MAPC #'(LAMBDA (ITEM)
	      (COND ((EQ 'LINE (PR=OBJ.TYPE ITEM))
		     (SETF (PR=OBJ.X-POS ITEM) 
			   (+ (PR=OBJ.WIDTH (CAR OBJECTS)) (FLOOR (/ (PR=actual.size) 2))))
		     (INCF (PR=OBJ.WIDTH (CAR OBJECTS))
			   (+ (FLOOR (/ (PR=actual.size) 2)) (PR=OBJ.OBJECTS ITEM)))
		     (PUSH item LINES))
		    (T (COND ((> (+ (PR=OBJ.WIDTH (CAR OBJECTS)) (PR=OBJ.WIDTH ITEM)) MAX.WIDTH)
			      (MAPC #'(LAMBDA (LINE)
					(SETF (PR=OBJ.HEIGHT LINE) (PR=OBJ.HEIGHT (CAR OBJECTS))))
				    LINES)
			      (setf (PR=OBJ.OBJECTS (CAR OBJECTS))
				    (APPEND LINES (PR=OBJ.OBJECTS (CAR OBJECTS))))
			      (SETQ LINES NIL)
			      (PUSH (MAKE-PR*OBJECT :CENTER 0 :X-POS 0
						    :Y-POS (+ (PR=OBJ.HEIGHT (CAR OBJECTS))
							      (PR=OBJ.Y-POS (CAR OBJECTS))) 
						    :TYPE 'LIST.OF.OBJECTS :WIDTH 0 :HEIGHT 0 
						    :OBJECTS NIL 
						    :ATTRIBUTES (CONS :ASCEND (CONS 0 ATTRIBUTES)))
				    OBJECTS)))
		       (SETF (CAR OBJECTS) (PR=OBJECT.APPEND (CAR OBJECTS) ITEM 0 0)))))
	  ITEMS)
    (MAPC #'(LAMBDA (LINE)
	      (SETF (PR=OBJ.HEIGHT LINE) (PR=OBJ.HEIGHT (CAR OBJECTS))))
	  LINES)
    (setf (PR=OBJ.OBJECTS (CAR OBJECTS))
	  (APPEND LINES (PR=OBJ.OBJECTS (CAR OBJECTS))))
    (COND ((CDR OBJECTS)
	   (MAKE-PR*OBJECT :CENTER (FLOOR (/ MAX.WIDTH 2)) :WIDTH MAX.WIDTH
			   :HEIGHT (+ (PR=OBJ.HEIGHT (CAR OBJECTS))
						    (PR=OBJ.Y-POS (CAR OBJECTS))) 
					 :Y-POS 0 :X-POS 0 :TYPE 'LIST.OF.OBJECTS
					 :OBJECTS (REVERSE OBJECTS) :ATTRIBUTES ATTRIBUTES))
	  (T (CAR OBJECTS)))))


(DEFUN PR=OBJECT.APPEND (OBJECT SUB.OBJECT &OPTIONAL (X.OFF 0) (Y.OFF 0))

  (LET ((WIDTH (PR=OBJ.WIDTH OBJECT)) (HEIGHT (PR=OBJ.HEIGHT OBJECT)))
    (SETQ Y.OFF (- (+ (COND ((GETF (PR=OBJ.ATTRIBUTES OBJECT) :ASCEND))
			    (T (PR=OBJ.HEIGHT OBJECT)))
		      Y.OFF)
		   (COND ((GETF (PR=OBJ.ATTRIBUTES SUB.OBJECT) :ASCEND))
			 (T (PR=OBJ.HEIGHT SUB.OBJECT)))))
    (SETF (PR=OBJ.X-POS SUB.OBJECT) (+ WIDTH X.OFF))
    (INCF (PR=OBJ.WIDTH OBJECT) (+ X.OFF (PR=OBJ.WIDTH SUB.OBJECT)))
    (SETF (PR=OBJ.CENTER SUB.OBJECT) (FLOOR (/ (PR=OBJ.WIDTH OBJECT) 2)))
    (COND ((>= Y.OFF 0)
	   (SETF (PR=OBJ.Y-POS SUB.OBJECT)  Y.OFF)
	   (SETF (PR=OBJ.HEIGHT OBJECT) (MAX HEIGHT (+ Y.OFF (PR=OBJ.HEIGHT SUB.OBJECT)))))
	  (T (MAPC #'(LAMBDA (ITEM) (DECF (PR=OBJ.Y-POS ITEM) Y.OFF)) (PR=OBJ.OBJECTS OBJECT))
	     (COND ((GETF (PR=OBJ.ATTRIBUTES OBJECT) :ASCEND)
		    (SETF (GETF (PR=OBJ.ATTRIBUTES OBJECT) :ASCEND)
			  (DECF (GETF (PR=OBJ.ATTRIBUTES OBJECT) :ASCEND) Y.OFF))))
	     (SETF (PR=OBJ.HEIGHT OBJECT) (MAX (- HEIGHT Y.OFF) (PR=OBJ.HEIGHT SUB.OBJECT)))))
    (SETF (PR=OBJ.CENTER OBJECT) (FLOOR (/ (PR=OBJ.WIDTH OBJECT) 2)))
    (PUSH SUB.OBJECT (PR=OBJ.OBJECTS OBJECT))
    OBJECT))


(DEFUN PR-PARSE.EXPLANATION (ITEM EVAL.FORM)

  ;;; Input: a drawable and a lisp function
  ;;; Value: generates a drawable of \verb$ITEM$ which is mouse sensitive and
  ;;;        \verb$EVAL.FORM$ denotes the result of clicking in the area of \verb$ITEM$

  ;;; NOTE : THIS FUNCTION WILL BE REMOVED IN A FUTURE RELEASE !
  
  (COND ((CAR EVAL.FORM)
	 (SETF (GETF (PR=OBJ.ATTRIBUTES ITEM) :DOUBLE.LEFT) (CAR EVAL.FORM))))
  (COND ((SECOND EVAL.FORM)
	 (SETF (GETF (PR=OBJ.ATTRIBUTES ITEM) :DOUBLE.MIDDLE) (SECOND EVAL.FORM))))
  (COND ((THIRD EVAL.FORM) 
	 (SETF (GETF (PR=OBJ.ATTRIBUTES ITEM) :RIGHT) (THIRD EVAL.FORM))))
  (COND ((FOURTH EVAL.FORM)
	 (SETF (GETF (PR=OBJ.ATTRIBUTES ITEM) :ENVIRONMENT) (FOURTH EVAL.FORM))))
  ITEM)



(defmacro pr-parse.sequel (sequel max.width &rest attributes)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.sequel ,sequel ,max.width pr*attributes))))


(defun pr=parse.sequel (sequel max.width attributes)

  (let ((buttom t) x-pos (height 0) (width 0) objects add.x)
    (setq x-pos 0)
    (mapc #'(lambda (buttom.or.edge)
	      (setq add.x (cond (buttom 0)
				(t (+ (pr=actual.distance)
				      (max 0 (floor (- (* 1.5 (pr=actual.size)) 
						       (pr=obj.width buttom.or.edge)) 2))))))
	      (cond ((> (+ add.x x-pos (pr=obj.width buttom.or.edge)) max.width)
		     (setq width (max width x-pos))
		     (setq x-pos 0)
		     (setq height (pr=parse.sequel.height objects height (not buttom)))
		     (setq objects nil)))
	      (setf (pr=obj.x-pos buttom.or.edge) (+ x-pos add.x))
	      (push buttom.or.edge objects)
	      (incf x-pos (+ (* 2 add.x) (pr=obj.width buttom.or.edge)))
	      (setq buttom (not buttom)))
	  sequel)
    (setq height (pr=parse.sequel.height objects height (not buttom)))
    (MAKE-PR*OBJECT :X-POS 0 :Y-POS 0 :WIDTH width :HEIGHT height
		    :CENTER (floor (/ width 2))
		    :TYPE 'sequel
		    :OBJECTS sequel
		    :ATTRIBUTES ATTRIBUTES)))


(defun pr=parse.sequel.height (objects y.offset buttom)

  (let ((height 0) (copy.buttom buttom))
    (mapc #'(lambda (buttom.or.edge)
	      (setq height (max (cond (buttom (pr=obj.height buttom.or.edge))
				      (t (floor (* 2.5 (pr=obj.height buttom.or.edge)))))
				height))
	      (setq buttom (not buttom)))
	  objects)
    (mapc #'(lambda (buttom.or.edge)
	      (setf (pr=obj.y-pos buttom.or.edge)
		    (+ y.offset (floor (/ (- height (cond (copy.buttom (pr=obj.height buttom.or.edge))
							  (t (* 2.5 (pr=obj.height buttom.or.edge)))))
					  2))))
	      (setq copy.buttom (not copy.buttom)))
	  objects)
    (+ y.offset height (floor (* 1.5 (pr=actual.size))))))


(defmacro pr-parse.page (object window page.no &rest attributes)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes (pr=parse.page ,object ,window ,page.no pr*attributes))))


(defun pr=parse.page (object window page.no attributes)

  (let ((page.no (pr-parse.string (format nil "~D" page.no) :font 'bold :size 'normal))
	width height)
    (multiple-value-setq (width height) (win-io.size window))
    (decf height 50) (decf width 20)
    (setf (pr=obj.x-pos page.no) (floor (/ (- width (pr=obj.width page.no)) 2)))
    (setf (pr=obj.y-pos page.no) (- height 20))
    (setf (pr=obj.y-pos object) (floor (/ (- height 40 (pr=obj.height object)) 2)))
    (MAKE-PR*OBJECT :X-POS 0 :Y-POS 0 :WIDTH width :HEIGHT height
		    :CENTER (floor (/ width 2))
		    :TYPE 'page
		    :OBJECTS (list page.no object)
		    :ATTRIBUTES ATTRIBUTES)))


(defmacro pr-parse.TREE (HEADER ALL.EDGES ALL.SUBTREES &OPTIONAL NO.MERGE &REST ATTRIBUTES)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.tree ,HEADER ,ALL.EDGES ,ALL.SUBTREES ,NO.MERGE pr*attributes))))



(DEFUN PR=PARSE.TREE (HEADER ALL.EDGES ALL.SUBTREES NO.MERGE ATTRIBUTES)
  
  ;;; Input: a drawable denoting the root of a tree, a list of drawables denoting edges, and a 
  ;;;        list of drawables denoting subtrees
  ;;; Value: generates a drawable of a tree, where \verb$HEADER$ is the root, \verb$ALL.EDGES$ are the 
  ;;;        edges of the root, and \verb$ALL.SUBTREES$ are the subtrees of the corresponding edges in 
  ;;;        \verb$ALL.EDGES$
  
  (LET ((EDGE.HEIGHT 0) (SUB.TREE.HEIGHT 0) (X-POS 0) (Y-POS 0) (CENTER 0)
	FIRST.ELEM LAST.ELEM PREV.TREES (y-inc 0))
    (DECLARE (TYPE FIXNUM EDGE.HEIGHT SUB.TREE.HEIGHT X-POS Y-POS CENTER y-inc))
    (SETQ Y-POS (COND (HEADER (PR=OBJ.HEIGHT HEADER)) (T 0)))
    
	     ;;; compute all edges and subtrees:
    
    (MAPC #'(LAMBDA (EDGE SUB.TREE)
	      (COND (EDGE (SETQ EDGE.HEIGHT (MAX EDGE.HEIGHT (PR=OBJ.HEIGHT EDGE)))))
	      (SETQ SUB.TREE.HEIGHT (MAX SUB.TREE.HEIGHT (PR=OBJ.HEIGHT SUB.TREE))))
	  ALL.EDGES ALL.SUBTREES)
    
    (setq y-inc (COND ((> EDGE.HEIGHT 0) (FLOOR (* 2.5 EDGE.HEIGHT)))
		      (t (* 2 (MIN (PR=ACTUAL.SIZE) (COND (HEADER (PR=OBJ.HEIGHT HEADER)) (T 0)))))))
    
    (incf y-pos y-inc)
    
	     ;;; compute positions of the subtrees:
    
	    ; (COND ((CAR ALL.EDGES) (SETQ X-POS (FLOOR (/ (PR=OBJ.WIDTH (CAR ALL.EDGES)) 2)))))
    (MAPL #'(LAMBDA (SUB.TREES EDGES)
	      (SETF (PR=OBJ.X-POS (CAR SUB.TREES)) X-POS)
	      (SETF (PR=OBJ.Y-POS (CAR SUB.TREES)) Y-POS)
	      (PUSH (CAR SUB.TREES) PREV.TREES)
	      (INCF X-POS (+ (PR=MAX.WIDTH PREV.TREES (COND ((second SUB.TREES) (LIST (SECOND SUB.TREES))))
					   (MAX (- (+ (COND ((CAR EDGES) (PR=OBJ.WIDTH (CAR EDGES))) (T 0))
						      (COND ((SECOND EDGES) (PR=OBJ.WIDTH (SECOND EDGES)))
							    (T 0))
						      (PR=OBJ.CENTER (CAR SUB.TREES)))
						   (COND ((SECOND SUB.TREES) (PR=OBJ.CENTER (SECOND SUB.TREES))) 
							 (T 0)))
						0)
					   0 0 X-POS Y-POS NO.MERGE)
			     (* 3 (pr=actual.size))))
	      (PUSH (CAR SUB.TREES) PREV.TREES)
	      (SETQ X-POS (MAX 0 X-POS)))       ;;; don't move right subtree out of left border !!!
	  ALL.SUBTREES ALL.EDGES)
    
    (cond (header (setq x-pos (pr=obj.width header)))
	  (t (setq x-pos 0)))
    (mapc #'(lambda (sub.tree)
	      (setq x-pos (max x-pos (+ (pr=obj.width sub.tree) (pr=obj.x-pos sub.tree)))))
	  all.subtrees)
    
    ;;; compute center of new tree:
    
    (COND ((CAR ALL.SUBTREES)
	   (SETQ FIRST.ELEM (CAR ALL.SUBTREES) LAST.ELEM (CAR (LAST ALL.SUBTREES)))
	   (SETQ CENTER (FLOOR (/ (+ (PR=OBJ.X-POS FIRST.ELEM) (PR=OBJ.CENTER FIRST.ELEM) 
				     (PR=OBJ.X-POS LAST.ELEM) (PR=OBJ.CENTER LAST.ELEM)) 2))))
	  (T (SETQ CENTER (FLOOR (/ X-POS 2)))))
    
    (COND ((AND HEADER (< CENTER (/ (PR=OBJ.WIDTH HEADER) 2)))
	   (PR=OBJ.MOVE ALL.SUBTREES (- CENTER (FLOOR (/ (PR=OBJ.WIDTH HEADER) 2))))
	   (SETQ CENTER (FLOOR (/ (PR=OBJ.WIDTH HEADER) 2)))))
    
    
    ;;; compute positions of the edges:
    
    (MAPC #'(LAMBDA (EDGE SUB.TREE) 
	      (COND (EDGE (SETF (PR=OBJ.X-POS EDGE) 
				(FLOOR (/ (- (+ CENTER (PR=OBJ.X-POS SUB.TREE) (PR=OBJ.CENTER SUB.TREE))
					     (PR=OBJ.WIDTH EDGE)) 
					  2)))
			  (SETF (PR=OBJ.Y-POS EDGE)
				(- y-pos (floor (/ (+ y-inc (PR=OBJ.HEIGHT EDGE)) 2)))))))
	  ALL.EDGES ALL.SUBTREES)
    
    ;;; compute position of the header if one exists:
    
    (COND (HEADER (SETF (PR=OBJ.X-POS HEADER) (- CENTER (FLOOR (/ (PR=OBJ.WIDTH HEADER) 2))))))
    
    ;;; in case the edges are wider than the subnodes we have to adjust the size of the
    ;;; object:
    
    (COND ((AND (CAR ALL.EDGES)
		(< (PR=OBJ.X-POS (CAR ALL.EDGES)) 0))
	   (DECF CENTER (PR=OBJ.X-POS (CAR ALL.EDGES)))
	   (decf x-pos (pr=obj.x-pos (car all.edges)))
	   (PR=OBJ.MOVE (COND (HEADER (CONS HEADER (APPEND ALL.EDGES ALL.SUBTREES)))
			      (T (APPEND ALL.EDGES ALL.SUBTREES)))
			(PR=OBJ.X-POS (CAR ALL.EDGES)))))
    (COND ((AND (CAR (last ALL.EDGES))
		(> (+ (PR=OBJ.X-POS (CAR (LAST ALL.EDGES))) (PR=OBJ.WIDTH (CAR (LAST ALL.EDGES)))) X-POS))
	   (SETQ X-POS (+ (PR=OBJ.X-POS (CAR (LAST ALL.EDGES))) (PR=OBJ.WIDTH (CAR (LAST ALL.EDGES)))))))
    
    
    ;;; update left and right margins of new tree:
    
    (MAKE-PR*OBJECT :X-POS 0 :Y-POS 0 :WIDTH X-POS :HEIGHT (+ Y-POS SUB.TREE.HEIGHT)
		    :CENTER CENTER :TYPE 'TREE
		    :OBJECTS (LIST HEADER ALL.EDGES ALL.SUBTREES)
		    :ATTRIBUTES ATTRIBUTES)))


(defmacro pr-parse.graph (TOP.NODES SUCCESS.FCT PRINT.FCT &REST ATTRIBUTES)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.graph ,TOP.NODES ,SUCCESS.FCT ,PRINT.FCT pr*attributes))))

  

(DEFUN PR=PARSE.GRAPH (TOP.NODES SUCCESS.FCT PRINT.FCT ATTRIBUTES)

  ;;; Input:   a list of top nodes of a graph, a lisp-function which computes the successors
  ;;;          of a node and a lisp-function computing the printed-representation of a node
  ;;; Effect:  computes the printed representation of the graph.
  ;;; Value:   the printed representation.

  (DECLARE (TYPE LIST TOP.NODES))
  
  (LET ((HASH.TABLE (MAKE-HASH-TABLE)) ARRAY)
    (SETQ ARRAY (PR=GRAPH.GRAPHLIST.CREATE TOP.NODES HASH.TABLE SUCCESS.FCT PRINT.FCT))
    (PR=GRAPH.BC.PHASES ARRAY)
    (PR=GRAPH.LAYOUT ARRAY)
    (PR=GRAPH.COLLECT ARRAY ATTRIBUTES)))



(defmacro pr-parse.line (LINE.WIDTH &REST ATTRIBUTES)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.line ,LINE.WIDTH pr*attributes))))


(DEFUN PR=PARSE.line (LINE.WIDTH ATTRIBUTES)

  (MAKE-PR*OBJECT :X-POS 0 :Y-POS 0 :WIDTH 0 :HEIGHT 0
		  :CENTER 0 :TYPE 'LINE
		  :OBJECTS (list LINE.WIDTH)
		  :ATTRIBUTES attributes))


(defmacro pr-parse.symboltable (FONT &REST ATTRIBUTES)

  `(let ((pr*attributes (list ,@attributes)))
     (pr=with.attributes pr*attributes
	 (pr=parse.symboltable ,font pr*attributes))))


(DEFUN PR=PARSE.SYMBOLTABLE (FONT ATTRIBUTES)

  (MAKE-PR*OBJECT :X-POS 0 :Y-POS 0 :WIDTH 330 :HEIGHT 310
		  :CENTER 165 :TYPE 'SYMBOLTABLE
		  :OBJECTS (list FONT)
		  :ATTRIBUTES attributes))



;;;;;==================================================================================================
;;;;; 
;;;;; Section II
;;;;;
;;;;; Print-functions for Description Windows
;;;;;
;;;;;==================================================================================================



(DEFUN PR-PRINT.TREE (TREE WINDOW X-POS Y-POS VIS &OPTIONAL ACTIVE.REGIONS)

  ;;; Input:  an representation of a picture, a window-specification, the offset for drawing the
  ;;;         picture and a list of mouse-sensitive regions
  ;;; Effect: draws the given picture on the window
  ;;; Value:  undefined
  
  (DECLARE (TYPE FIXNUM X-POS Y-POS) 
	   (TYPE LIST ACTIVE.REGIONS VIS))
  (INCF X-POS (PR=OBJ.X-POS TREE))
  (INCF Y-POS (PR=OBJ.Y-POS TREE))
  (COND ((PR=OBJ.IS.ACTIVE TREE)
	 (PUSH (LIST X-POS Y-POS TREE) ACTIVE.REGIONS)))
  (COND ((AND (<= X-POS (SECOND VIS))
	      (>= (+ X-POS (PR=OBJ.WIDTH TREE)) (CAR VIS))
	      (<= Y-POS (FOURTH VIS))
	      (>= (+ Y-POS (PR=OBJ.HEIGHT TREE)) (THIRD VIS)))
	 (pr=with.active.attributes window (pr=obj.attributes tree)
				    (eq (third (car active.regions)) tree)
	  (SETQ ACTIVE.REGIONS
		(CASE (PR=OBJ.TYPE TREE)
		      (SYMBOLTABLE (PR=PRINT.SYMBOLTABLE WINDOW X-POS Y-POS TREE ACTIVE.REGIONS))
		      (HEADER (PR=PRINT.HEADER WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS))
		      (LINE (PR=PRINT.LINE WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS))
		      (BITMAP (PR=PRINT.BITMAP WINDOW X-POS Y-POS TREE ACTIVE.REGIONS))
		      (SEQUEL (PR=PRINT.SEQUEL WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS))
		      (CLOSURE (PR=PRINT.CLOSURE WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS))
		      (PAGE (PR=PRINT.PAGE WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS))
		      ((LIST.OF.OBJECTS TABLE)
		       (PR=PRINT.LIST.OF.OBJECTS WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS))
		      (STRING (PR=PRINT.STRING WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS))
		      (TREE (PR=PRINT.TREE WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS))
		      (GRAPH (PR=PRINT.GRAPH WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS)))))))
  ACTIVE.REGIONS)


(DEFUN PR=OBJ.IS.ACTIVE (ITEM)

  (SOMEF #'(LAMBDA (NAME IGNORE)
	     (DECLARE (IGNORE IGNORE))
	     (MEMBER NAME '(:DOUBLE.LEFT :DOUBLE.MIDDLE :DOUBLE.RIGHT :LEFT :MIDDLE 
					 :RIGHT :SELECTION :SELECTED :PARTIAL)))
	 (PR=OBJ.ATTRIBUTES ITEM)))


(DEFUN PR=PRINT.PAGE (WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS)

  (DECLARE (TYPE FIXNUM X-POS Y-POS)
	   (TYPE LIST VIS ACTIVE.REGIONS))
  (LET* ((X.START (+ X-POS (PR=OBJ.X-POS TREE))) (Y.START (+ Y-POS (PR=OBJ.Y-POS TREE)))
	 (X.END (+ X.START (PR=OBJ.WIDTH TREE))) (Y.END (+ Y.START (PR=OBJ.HEIGHT TREE))))
    (pr=with.active.attributes window '(:colour "DarkRed") nil
			       (progn
				 (PR=CLIP.LINE WINDOW VIS X.START (+ Y.START 40) (- X.END 100) (+ Y.START 40) 5)
				 (PR=CLIP.LINE WINDOW VIS (- X.END 50) (+ Y.START 40) X.END (+ Y.START 40) 5)
				 (PR=CLIP.LINE WINDOW VIS X.START (- Y.END 30) X.END (- Y.END 30) 5)))
    (pr=with.active.attributes window '(:colour "DarkBlue" :font bold :size 'normal) nil
			       (WIN-IO.DRAW.STRING WINDOW (- X.END 90) (+ Y.START 30) "INKA"))
    (MAPC #'(LAMBDA (ITEM)
	      (SETQ ACTIVE.REGIONS (PR-PRINT.TREE ITEM WINDOW X-POS Y-POS VIS ACTIVE.REGIONS)))
	  (PR=OBJ.OBJECTS TREE))
    ACTIVE.REGIONS))


(DEFUN PR=PRINT.HEADER (WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS)

  (DECLARE (TYPE FIXNUM X-POS Y-POS)
	   (TYPE LIST VIS ACTIVE.REGIONS))
  (win-io.print.top window (car (PR=OBJ.OBJECTS TREE)))
  (PR-PRINT.TREE (SECOND (PR=OBJ.OBJECTS TREE)) WINDOW X-POS Y-POS VIS ACTIVE.REGIONS))


(DEFUN PR=PRINT.BITMAP (WINDOW X-POS Y-POS TREE ACTIVE.REGIONS)

  (DECLARE (TYPE FIXNUM X-POS Y-POS)
	   (TYPE LIST ACTIVE.REGIONS))
  (WIN-IO.DRAW.BITMAP WINDOW (PR=OBJ.width tree) (pr=obj.height tree)
		      (floor x-pos) (floor y-pos)
		      (car (pr=obj.objects tree)))
  ACTIVE.REGIONS)


(DEFUN PR=PRINT.LINE (WINDOW X-POS Y-POS vis TREE ACTIVE.REGIONS)

  (DECLARE (TYPE FIXNUM X-POS Y-POS)
	   (TYPE LIST ACTIVE.REGIONS))
  (WIN-IO.DRAW.LINE WINDOW X-POS Y-POS (+ X-POS (PR=OBJ.width tree)) (+ Y-POS (pr=obj.height tree))
		    (car (PR=OBJ.objects TREE)))
  ACTIVE.REGIONS)


(DEFUN PR=PRINT.SYMBOLTABLE (WINDOW X-POS Y-POS ITEM ACTIVE.REGIONS)

  (DECLARE (TYPE FIXNUM X-POS Y-POS)
	   (TYPE LIST ACTIVE.REGIONS))
  (LET ((STRING " "))
    (WIN-IO.DRAW.RECTANGLE WINDOW 330 310 (FLOOR X-POS) (FLOOR Y-POS) 2 "LightGrey")
    (pr=with.active.attributes window `(:colour "DarkBlue" :font ,(car (pr=obj.objects item)) :size 'normal) nil
       (DOTIMES (I 15)
		(DOTIMES (J 16)
			 (SETF (AREF STRING 0) (CODE-CHAR (+ 16 (* 16 I) J)))
			 (WIN-IO.DRAW.STRING WINDOW (+ X-POS 5 (* J 20)) (+ Y-POS (* I 20)) STRING))))
    ACTIVE.REGIONS))
  

(DEFUN PR=PRINT.CLOSURE (WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS)

  (DECLARE (TYPE FIXNUM X-POS Y-POS)
	   (TYPE LIST VIS ACTIVE.REGIONS))
  (LET ((STYLE (PR=OBJ.STYLE TREE)))     ; STYLE is a tuple (STYLE LINE.THICKNESS FILL.COLOUR SHADOWED)
    (CASE (CAR STYLE)
	  ((DBOXED BOXED)
	   (COND ((> (FOURTH STYLE) 0)
		  (WIN-IO.DRAW.RECTANGLE WINDOW
					 (FLOOR (PR=OBJ.WIDTH TREE)) (FLOOR (PR=OBJ.HEIGHT TREE))
					 (+ (FOURTH STYLE) (FLOOR X-POS)) (+ (FOURTH STYLE) (FLOOR Y-POS))
					 0 "DarkGrey")))
	   (WIN-IO.DRAW.RECTANGLE WINDOW
				  (FLOOR (PR=OBJ.WIDTH TREE)) (FLOOR (PR=OBJ.HEIGHT TREE))
				  (FLOOR X-POS) (FLOOR Y-POS)
				  (SECOND STYLE) (THIRD STYLE)))
	  (OVAL
	   (COND ((> (FOURTH STYLE) 0)
		  (WIN-IO.DRAW.OVAL WINDOW
			     (+ (FLOOR X-POS) (FOURTH STYLE)) (+ (FLOOR Y-POS) (FOURTH STYLE))
			     (PR=OBJ.WIDTH TREE) (PR=OBJ.HEIGHT TREE) 0
			     "DarkGrey")))
	   (WIN-IO.DRAW.OVAL WINDOW
			     (FLOOR X-POS) (FLOOR Y-POS)
			     (PR=OBJ.WIDTH TREE) (PR=OBJ.HEIGHT TREE) (SECOND STYLE)
			     (THIRD STYLE)))
	  (CIRCLE
	   (COND ((FOURTH STYLE)
		  (WIN-IO.DRAW.CIRCLE WINDOW
				      (FLOOR (/ (PR=OBJ.WIDTH TREE) 2))
				      (+ (FOURTH STYLE) (FLOOR X-POS) (FLOOR (/ (PR=OBJ.WIDTH TREE) 2)))
				      (+ (FOURTH STYLE) (FLOOR Y-POS) (FLOOR (/ (PR=OBJ.HEIGHT TREE) 2)))
				      (SECOND STYLE) "DarkGrey")))
	   (WIN-IO.DRAW.CIRCLE WINDOW
			       (FLOOR (/ (PR=OBJ.WIDTH TREE) 2))
			       (+ (FLOOR X-POS) (FLOOR (/ (PR=OBJ.WIDTH TREE) 2))) 
			       (+ (FLOOR Y-POS) (FLOOR (/ (PR=OBJ.HEIGHT TREE) 2))) 
			       (SECOND STYLE)
			       (THIRD STYLE))))
    (MAPC #'(LAMBDA (ITEM)
	      (SETQ ACTIVE.REGIONS (PR-PRINT.TREE ITEM WINDOW X-POS Y-POS VIS ACTIVE.REGIONS)))
	  (PR=OBJ.OBJECTS TREE))
    ACTIVE.REGIONS))


(DEFUN PR=PRINT.LIST.OF.OBJECTS (WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS)

  (MAPC #'(LAMBDA (ITEM)
	    (SETQ ACTIVE.REGIONS (PR-PRINT.TREE ITEM WINDOW X-POS Y-POS VIS ACTIVE.REGIONS)))
	(PR=OBJ.OBJECTS TREE))
  ACTIVE.REGIONS)


(DEFUN PR=PRINT.sequel (WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS)

  (let (line.y.pos line.start.x.pos line.end.x.pos actual.item)
    (SMAPL #'(LAMBDA (ITEMS)
	       (SETQ ACTIVE.REGIONS (PR-PRINT.TREE (CAR ITEMS) WINDOW X-POS Y-POS VIS ACTIVE.REGIONS))
	       (cond ((cdr items)
		      (SETQ ACTIVE.REGIONS (PR-PRINT.TREE (second ITEMS) WINDOW X-POS Y-POS VIS ACTIVE.REGIONS))
		      (setq actual.item (cond ((> (+ (pr=obj.x-pos (car items)) (pr=obj.width (car items)))
						  (pr=obj.x-pos (second items)))
					       (third items))
					      (t (car items))))
		      (setq line.start.x.pos (cond ((> (+ (pr=obj.x-pos (car items)) (pr=obj.width (car items)))
						       (pr=obj.x-pos (second items)))
						    x-pos)
						   (t (+ x-pos (pr=obj.x-pos (car items))
							 (pr=obj.width (car items))))))
		      (setq line.end.x.pos (cond ((> (pr=obj.x-pos (third items))
						     (+ (pr=obj.x-pos (second items)) 
							(pr=obj.width (second items))))
						  (+ x-pos (pr=obj.x-pos (third items))))
						 (t (+ x-pos (pr=obj.width tree)))))
		      (setq line.y.pos (+ y-pos (pr=obj.y-pos actual.item)
					  (floor (/ (pr=obj.height actual.item) 2))))
		      (PR=CLIP.LINE WINDOW VIS line.start.x.pos line.y.pos line.end.x.pos line.y.pos 
				    (MAX 1 (FLOOR (* 2 PR*SCALING)))))))
	   #'CDDR
	   (PR=OBJ.OBJECTS TREE))
    ACTIVE.REGIONS))


(DEFUN PR=PRINT.STRING (WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS)

  (DECLARE (TYPE FIXNUM X-POS Y-POS)
	   (TYPE LIST VIS ACTIVE.REGIONS))
  (WIN-IO.DRAW.STRING WINDOW (floor X-POS) (floor Y-POS)
		      (car (PR=OBJ.OBJECTS TREE)))
  (let ((cursor (getf (PR=OBJ.ATTRIBUTES TREE) :BOX)))
    (COND (CURSOR (WIN-IO.DRAW.LINE WINDOW (+ (floor x-pos) (third cursor)) y-pos (+ (floor x-pos) (third cursor))
				    (+ y-pos (second cursor)) 2))))
  (COND ((EQ (PR=OBJ.STYLE TREE) 'UNDERLINE)
	 (PR=CLIP.LINE WINDOW VIS X-POS (+ (- Y-POS 1) (PR=OBJ.HEIGHT TREE))
		       (+ X-POS (PR=OBJ.WIDTH TREE)) (+ (- Y-POS 1) (PR=OBJ.HEIGHT TREE)))))
  ACTIVE.REGIONS)


(DEFUN PR=PRINT.TREE (WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS)

  (DECLARE (TYPE FIXNUM X-POS Y-POS)
	   (TYPE LIST VIS ACTIVE.REGIONS))
  (LET (HEADER (CENTER.X-POS 0) (CENTER.Y-POS 0) (TARGET.X-POS 0) (TARGET.Y-POS 0)
	       GRADIENT (X.START 0) (X.END 0) (Y.START 0) (Y.END 0)
	       (line.width (MAX 1 (FLOOR (/ (pr=actual.size) 5)))))
    (DECLARE (TYPE FIXNUM CENTER.X-POS CENTER.Y-POS TARGET.X-POS TARGET.Y-POS X.START X.END Y.START Y.END))
    (COND ((SETQ HEADER (CAR (PR=OBJ.OBJECTS TREE)))
	   (SETQ ACTIVE.REGIONS (PR-PRINT.TREE HEADER WINDOW X-POS Y-POS VIS ACTIVE.REGIONS))
	   (SETQ CENTER.X-POS (+ X-POS (PR=OBJ.X-POS HEADER) (PR=OBJ.CENTER HEADER)))
	   (SETQ CENTER.Y-POS (+ Y-POS (PR=OBJ.Y-POS HEADER) (PR=OBJ.HEIGHT HEADER))))
	  (T (SETQ CENTER.X-POS (+ X-POS (PR=OBJ.CENTER TREE)) CENTER.Y-POS Y-POS)))
    (MAPC #'(LAMBDA (EDGE SUB.TREE)
	      (SETQ TARGET.X-POS (+ X-POS (PR=OBJ.X-POS SUB.TREE) (PR=OBJ.CENTER SUB.TREE)))
	      (SETQ TARGET.Y-POS (+ Y-POS (PR=OBJ.Y-POS SUB.TREE)))
	    (COND (EDGE (SETQ GRADIENT (/ (- TARGET.X-POS CENTER.X-POS)
					  (- TARGET.Y-POS CENTER.Y-POS)))
			(SETQ Y.START (+ Y-POS (PR=OBJ.Y-POS EDGE)))
			(SETQ Y.END (+ Y-POS (PR=OBJ.Y-POS EDGE) (PR=OBJ.HEIGHT EDGE)))
			(SETQ X.START (FLOOR (+ (* GRADIENT (- Y.START CENTER.Y-POS))
						CENTER.X-POS)))
			(SETQ X.END (+ (FLOOR (* GRADIENT (- Y.END CENTER.Y-POS)))
				       CENTER.X-POS))
			(COND ((< X.START (+ (PR=OBJ.X-POS EDGE) X-POS))
			       (SETQ GRADIENT (/ (- TARGET.Y-POS CENTER.Y-POS)
						 (- TARGET.X-POS CENTER.X-POS)))
			       (SETQ X.START (+ X-POS (PR=OBJ.X-POS EDGE)))
			       (SETQ X.END (+ X-POS (PR=OBJ.X-POS EDGE) (PR=OBJ.WIDTH EDGE)))
			       (SETQ Y.START (+ (FLOOR (* GRADIENT (- X.START CENTER.X-POS)))
						CENTER.Y-POS))
			       (SETQ Y.END (+ (FLOOR (* GRADIENT (- X.END CENTER.X-POS)))
					      CENTER.Y-POS)))
			      ((> X.START (+ (PR=OBJ.X-POS EDGE) X-POS (PR=OBJ.WIDTH EDGE)))
			       (SETQ GRADIENT (/ (- TARGET.Y-POS CENTER.Y-POS)
								      (- TARGET.X-POS CENTER.X-POS)))
			       (SETQ X.START (+ X-POS (PR=OBJ.X-POS EDGE) (PR=OBJ.WIDTH EDGE)))
			       (SETQ X.END (+ X-POS (PR=OBJ.X-POS EDGE)))
			       (SETQ Y.START (+ (FLOOR (* GRADIENT (- X.START CENTER.X-POS)))
						CENTER.Y-POS))
			       (SETQ Y.END (+ (FLOOR (* GRADIENT (- X.END CENTER.X-POS)))
					      CENTER.Y-POS))))
			(PR=CLIP.LINE WINDOW VIS CENTER.X-POS CENTER.Y-POS X.START Y.START line.width)
			(SETQ ACTIVE.REGIONS (PR-PRINT.TREE EDGE WINDOW X-POS Y-POS VIS ACTIVE.REGIONS))
			(PR=CLIP.LINE WINDOW VIS X.END Y.END TARGET.X-POS TARGET.Y-POS line.width))
		  (T (PR=CLIP.LINE WINDOW VIS CENTER.X-POS CENTER.Y-POS TARGET.X-POS TARGET.Y-POS line.width)))
	    (SETQ ACTIVE.REGIONS (PR-PRINT.TREE SUB.TREE WINDOW X-POS Y-POS VIS ACTIVE.REGIONS)))
	  (SECOND (PR=OBJ.OBJECTS TREE)) (THIRD (PR=OBJ.OBJECTS TREE)))
    ACTIVE.REGIONS))



(DEFUN PR=PRINT.GRAPH (WINDOW X-POS Y-POS VIS TREE ACTIVE.REGIONS)

  (DECLARE (TYPE FIXNUM X-POS Y-POS)
	   (TYPE LIST VIS ACTIVE.REGIONS))
  (LET ((ARRAY (CAR (PR=OBJ.OBJECTS TREE))) (CENTER.X-POS 0) (CENTER.Y-POS 0)
	(TARGET.X-POS 0) (TARGET.Y-POS 0) item
	(line.width (MAX 1 (FLOOR (/ (pr=actual.size) 5)))))
    (DECLARE (TYPE (SIMPLE-ARRAY LIST 1) ARRAY)
	     (TYPE FIXNUM CENTER.X-POS CENTER.Y-POS TARGET.X-POS TARGET.Y-POS line.width))
    (dotimes (I (ARRAY-DIMENSION ARRAY 0))
      (DECLARE (TYPE FIXNUM I))
      (mapc #'(lambda (node)
		(DECLARE (TYPE PR*GRAPH.NODE NODE))
		(setq item (pr=graph.node.text node))
		(SETQ CENTER.X-POS (+ X-POS (PR=OBJ.X-POS item) (PR=OBJ.CENTER item)))
		(SETQ CENTER.Y-POS (+ Y-POS (PR=OBJ.Y-POS item) (PR=OBJ.HEIGHT item)))
		(cond ((not (pr=graph.node.invisible node))
		       (SETQ ACTIVE.REGIONS (PR-PRINT.TREE item WINDOW X-POS Y-POS VIS ACTIVE.REGIONS)))      
		      (t (PR=CLIP.LINE WINDOW VIS CENTER.X-POS CENTER.Y-POS 
				       CENTER.X-POS (- CENTER.Y-POS (PR=OBJ.HEIGHT item)) line.width)))
		(mapc #'(lambda (succ)
			  (SETQ TARGET.X-POS (+ X-POS (PR=OBJ.X-POS (pr=graph.node.text succ))
						(PR=OBJ.CENTER (pr=graph.node.text succ))))
			  (SETQ TARGET.Y-POS (+ Y-POS (PR=OBJ.Y-POS (pr=graph.node.text succ))))
			  (PR=CLIP.LINE WINDOW VIS CENTER.X-POS CENTER.Y-POS 
					TARGET.X-POS TARGET.Y-POS line.width))
		      (pr=graph.node.succs node)))
	    (aref ARRAY I)))
    ACTIVE.REGIONS))



;;;;;==================================================================================================
;;;;; 
;;;;; Section III
;;;;;
;;;;; Parsing Gterms
;;;;;
;;;;;==================================================================================================


(defun pr=parse.gterm.as.tree (gterm attr.function &optional taf)

  (let (subtaf)
    (cond ((null (da-gterm.termlist gterm))
	   (pr=parse.gterm.symbol gterm (funcall attr.function gterm taf)))
	  (t (setq subtaf (da-taf.create.zero taf))
	     (let ((parsed.termlist (mapcar #'(lambda (subterm)
						(setq subtaf (da-taf.create.next subtaf))
						(pr=parse.gterm.as.tree subterm attr.function subtaf))
					    (da-gterm.termlist gterm))))
	       (cond ((and (eq 'and (da-gterm.symbol gterm)) (member nil parsed.termlist))
		      nil)
		     (t (setq parsed.termlist (delete nil parsed.termlist))
			(cond ((and (member (da-gterm.symbol gterm) '(and or))
				    (null (cdr parsed.termlist)))
			       (car parsed.termlist))
			      (t (pr-parse.tree (pr=parse.gterm.symbol gterm (funcall attr.function gterm taf))
						(make-list (length parsed.termlist))
						parsed.termlist))))))))))


(defun pr=parse.gterm.symbol (gterm attributes)

  (let (result (symbol (da-gterm.symbol gterm)))
    (setq result (cond ((da-symbol.is symbol)
			(cond ((and (da-literal.is gterm) (da-sign.is.negative (da-literal.sign gterm)))
			       (pr-parse.float.text
				(list (pr-parse.string (make-string 1 :initial-element 
								    (pr=junctor.char 'not))
						       :font 'symbol)
				      (pr-parse.string " ")
				      (pr-parse.string (da-symbol.pname symbol)))))
			      (t (pr-parse.string (da-symbol.pname symbol)))))
		       (t (pr-parse.string (make-string 1 :initial-element (pr=junctor.char symbol))
					   :font 'symbol))))
    (setf (pr=obj.attributes result) (append (pr=obj.attributes result) attributes))
    result))


(defun pr=buffer.print (buffer STREAM DEPTH)
 
  (COND ((AND *PRINT-LEVEL* (> DEPTH *PRINT-LEVEL*)) (FORMAT STREAM "&"))
	(t (FORMAT STREAM "Buffer ~A" (pr=buffer.actual.string buffer)))))


(defmacro pr=buffer.newline (buffer)

  `(pr=buffer.save ,buffer t))


(defun pr=buffer.save (buffer &optional newline)

  (let ((object (make-pr*object :x-pos (pr=buffer.actual.x-pos buffer)
				:y-pos (pr=buffer.actual.y-pos buffer)
				:width (- (pr=buffer.actual.width buffer) (pr=buffer.actual.x-pos buffer))
				:height (floor (* (pr=actual.size) pr*baselinestretch))
				:center (floor (/ (- (pr=buffer.actual.width buffer) 
						     (pr=buffer.actual.x-pos buffer)) 2))
				:type 'string
				:attributes (copy-list (pr=buffer.actual.attributes buffer))
				:objects (list (string-right-trim '(#\Space) (pr=buffer.actual.string buffer))))))
    (push object (pr=buffer.object.list buffer))
    (setf (pr=buffer.actual.index buffer) 0)
    (setf (pr=buffer.actual.attributes buffer) nil)
    (cond (newline (setf (pr=buffer.actual.x-pos buffer) (car (pr=buffer.stack buffer)))
		   (incf (pr=buffer.actual.y-pos buffer) (floor (* (pr=actual.size) pr*baselinestretch)))
		   (setf (pr=buffer.actual.width buffer) (car (pr=buffer.stack buffer))))
	  (t (setf (pr=buffer.actual.x-pos buffer) (pr=buffer.actual.width buffer))))
    (setf (pr=buffer.actual.string buffer)
	  (make-string (- (pr=buffer.max.chars buffer) (pr=buffer.actual.index buffer))
		       :initial-element #\Space))))



(defmacro pr=buffer.remaining.length (buffer)

  `(max 0 (- (pr=buffer.max.width ,buffer)
	     (pr=buffer.actual.width ,buffer))))


(defmacro pr=buffer.push (buffer &optional (offset 0))

  `(push (+ ,offset (pr=buffer.actual.width ,buffer))  
	 (pr=buffer.stack ,buffer)))


(defmacro pr=buffer.pop (buffer)

  `(pop (pr=buffer.stack ,buffer)))


(defun pr=buffer.format.char (buffer char length)

  (setf (aref (pr=buffer.actual.string buffer) (pr=buffer.actual.index buffer))
	char)
  (incf (pr=buffer.actual.index buffer))
  (incf (pr=buffer.actual.width buffer) length))


(defun pr=buffer.format.string (buffer string length)

  (replace (pr=buffer.actual.string buffer) string :start1 (pr=buffer.actual.index buffer))
  (incf (pr=buffer.actual.index buffer) (length string))
  (incf (pr=buffer.actual.width buffer) length))


(defun pr=buffer.format.command (buffer text)
  
  (case text
	(left.bracket (pr=buffer.format.char buffer #\( (pr=char.width #\))))
	(right.bracket (pr=buffer.format.char buffer #\) (pr=char.width #\))))
	(comma (pr=buffer.format.char buffer #\, (pr=char.width #\,)))
	(space (pr=buffer.format.char buffer #\Space (pr=char.width #\Space)))))


(defun pr=buffer.format.symbol (buffer symbol length)

  (cond ((typep symbol 'da*symbol)
	 (pr=buffer.format.string buffer (da-symbol.pname symbol) length))
	(t (pr=buffer.format.junctor buffer symbol length))))


(defun pr=buffer.format.junctor (buffer symbol length)

  (pr=buffer.save buffer)
  (pr=with.attributes '(:font symbol)
     (pr=buffer.format.char buffer (pr=junctor.char symbol) length)
     (setf (pr=buffer.actual.attributes buffer) '(:font symbol))
     (pr=buffer.save buffer)))


(defun pr=symbol.notion (symbol)

  (cond ((da-predicate.is symbol)
	 (cond ((or (da-predicate.is.equality symbol)
		    (da-symbol.has.attribute symbol 'infix))
		'infix)
	       (t 'prefix)))
	((da-function.is symbol)
	 (cond ((da-symbol.has.attribute symbol 'infix) 'infix)
	       (t 'prefix)))
	((member symbol '(all ex)) 'junctor)
	((member symbol '(or and impl eqv)) 'infix)
	((member symbol '(not)) 'prefix_without_bracket)
	(t 'prefix)))


(defun pr=buffer.reset (buffer &optional char.length)

  (setf (pr=buffer.max.width buffer) (* char.length (pr=string.width "l")))
  (setf (pr=buffer.max.chars buffer) char.length)
  (setf (pr=buffer.actual.string buffer)
	(make-string (pr=buffer.max.chars buffer) :initial-element #\Space))
  (setf (pr=buffer.actual.attributes buffer) nil)
  (setf (pr=buffer.actual.index buffer) 0)
  (setf (pr=buffer.actual.width buffer) 0)
  (setf (pr=buffer.actual.x-pos buffer) 0)
  (setf (pr=buffer.actual.y-pos buffer) 0)
  (setf (pr=buffer.object.list buffer) nil)
  (setf (pr=buffer.stack buffer) (list 0)))


;;;; Internal representation of prints
;;;;
;;;;  Infix:                   total length, length of op, lengths of arguments
;;;;  Prefix:                  total length, length of op, lengths of arguments
;;;;  prefix_without_bracket : total length, length of op, lengths of arguments
;;;;  junctor:                 total length, length of junctor, length of varlists, length argument


(defun pr=gterm.parse (buffer gterm length.list &optional surrounding)

  (let (notion newline buffer.check)
    (pr=with.attributes (fifth length.list)
        (setq buffer.check (pr=buffer.check.attributes buffer (fifth length.list)))
	(setq notion (pr=symbol.notion (da-gterm.symbol gterm)))
	(cond ((and (da-literal.is gterm)
		    (da-sign.is.negative (da-literal.sign gterm)))
	       (pr=buffer.format.junctor buffer 'not (pr=junctor.length 'not))
	       (pr=buffer.format.command buffer 'space)))
	(case notion
	      (infix (cond ((and (member surrounding '(infix junctor))
				 (not (da-literal.is gterm)))
			    (pr=buffer.format.command buffer 'left.bracket)))
		     (pr=buffer.push buffer)
		     (setq newline (pr=gterm.list.parse buffer (da-gterm.termlist gterm) (third length.list)
							(da-gterm.symbol gterm) (second length.list)
							'infix))
		     (pr=buffer.pop buffer)
		     (cond ((and (member surrounding '(infix junctor))
				 (not (da-literal.is gterm)))
			    (pr=buffer.format.command buffer 'right.bracket))))
	      (prefix (cond ((da-gterm.termlist gterm) (pr=buffer.push buffer 2)))
		      (pr=buffer.format.symbol buffer (da-gterm.symbol gterm) (second length.list))
		      (cond ((da-gterm.termlist gterm)
			     (cond ((and (> (- (car length.list) (second length.list))
					(pr=buffer.remaining.length buffer))
					 (> (* 2 (second length.list)) (pr=buffer.remaining.length buffer)))
				    (pr=buffer.newline buffer)))
			     (pr=buffer.format.command buffer 'left.bracket)
			     (pr=buffer.push buffer)
			     (setq newline (pr=gterm.comma.list.parse 
					    buffer (da-gterm.termlist gterm) (third length.list)
					    'prefix))
			     (pr=buffer.pop buffer)
			     (pr=buffer.pop buffer)
			     (pr=buffer.format.command buffer 'right.bracket))))
	      (prefix_without_bracket (cond ((da-gterm.termlist gterm) (pr=buffer.push buffer 2)))
		      (pr=buffer.format.symbol buffer (da-gterm.symbol gterm) (second length.list))
		      (cond ((da-gterm.termlist gterm)
			     (cond ((and (> (- (car length.list) (second length.list))
					(pr=buffer.remaining.length buffer))
					 (> (* 2 (second length.list)) (pr=buffer.remaining.length buffer)))
				    (pr=buffer.newline buffer)))
			     (pr=buffer.format.command buffer 'space)
			     (pr=buffer.push buffer)
			     (setq newline (pr=gterm.comma.list.parse 
					    buffer (da-gterm.termlist gterm) (third length.list)
					    'prefix))
			     (pr=buffer.pop buffer)
			     (pr=buffer.pop buffer))))
	      (junctor (pr=buffer.push buffer 2)
		       (pr=buffer.format.junctor buffer (da-gterm.symbol gterm) (second length.list))
		       (pr=buffer.format.command buffer 'space)
		       (pr=buffer.push buffer)
		       (setq newline (pr=gterm.comma.list.parse 
				      buffer (car (da-gterm.termlist gterm)) (third length.list)
				      'junctor))
		       (pr=buffer.pop buffer)
		       (cond ((> (* 2 (second length.list)) (pr=buffer.remaining.length buffer))
			      (pr=buffer.newline buffer)))
		       (pr=gterm.parse buffer (second (da-gterm.termlist gterm)) 'junctor)
		       (pr=buffer.pop buffer))))
    (pr=buffer.recheck.attributes buffer buffer.check (fifth length.list))
    newline))


(defun pr=gterm.list.parse (buffer gterm.list length.lists separator separator.length &optional surrounding)

  (let (inside.newline newline)
    (mapl #'(lambda (sub.gterms sub.length.lists)
	      (setq inside.newline (pr=gterm.parse buffer (car sub.gterms) (car sub.length.lists) surrounding))
	      (cond ((cdr sub.gterms)
		     (cond ((or inside.newline
				(< (pr=buffer.remaining.length buffer)
				   (+ (* 2 (pr=char.width #\Space))
				      separator.length
				      (car (second sub.length.lists)))))
			    (pr=buffer.newline buffer)
			    (setq newline t))
			   (t (pr=buffer.format.command buffer 'space)))
		     (pr=buffer.format.symbol buffer separator separator.length)
		     (pr=buffer.format.command buffer 'space))))	    
	  gterm.list length.lists)
    newline))


(defun pr=gterm.comma.list.parse (buffer gterm.list length.lists &optional surrounding)

  (let (inside.newline newline)
    (mapl #'(lambda (sub.gterms sub.length.lists)
	      (setq inside.newline (pr=gterm.parse buffer (car sub.gterms) (car sub.length.lists) surrounding))
	      (cond ((cdr sub.gterms)
		     (pr=buffer.format.command buffer 'comma)
		     (cond ((or inside.newline
				(< (pr=buffer.remaining.length buffer)
				   (+ (* 2 (pr=char.width #\Space))
				      (car (second sub.length.lists)))))
			    (pr=buffer.newline buffer)
			    (setq newline t))
			   (t (pr=buffer.format.command buffer 'space))))))	    
	  gterm.list length.lists)
    newline))
 

(defun pr=buffer.check.attributes (buffer attributes)

  (cond (attributes
	 (pr=buffer.save buffer)
	 (setf (pr=buffer.actual.attributes buffer) attributes)
	 (pr=buffer.object.list buffer))))


(defun pr=buffer.recheck.attributes (buffer object.list attributes)

  (cond (attributes
	 (pr=buffer.save buffer)
	 (cond ((neq object.list (cdr (pr=buffer.object.list buffer)))	 
		(pr=buffer.merge.objects buffer object.list))))))


(defun pr=buffer.merge.objects (buffer object.list)

  (let (objects considered.objects new.obj)
    (setq objects (pr=buffer.object.list buffer))
    (while (and objects (neq objects object.list))
      (push (pop objects) considered.objects))
    (let ((min-x-pos 1000000) (min-y-pos 1000000) (max-x-pos 0) (max-y-pos 0))
      (mapc #'(lambda (obj)
		(setq min-x-pos (min min-x-pos (pr=obj.x-pos obj)))
		(setq min-y-pos (min min-y-pos (pr=obj.y-pos obj)))
		(setq max-x-pos (max max-x-pos (+ (pr=obj.width obj) (pr=obj.x-pos obj))))
		(setq max-y-pos (max max-y-pos (+ (pr=obj.height obj) (pr=obj.y-pos obj)))))
	    considered.objects)
      (mapc #'(lambda (obj)
		(setf (pr=obj.x-pos obj) (- (pr=obj.x-pos obj) min-x-pos))
		(setf (pr=obj.y-pos obj) (- (pr=obj.y-pos obj) min-y-pos)))
	    considered.objects)
      (setq new.obj (make-pr*object :type 'list.of.objects :x-pos min-x-pos :y-pos min-y-pos
				    :width (- max-x-pos min-x-pos) :height (- max-y-pos min-y-pos)
				    :center (floor (/ (- max-x-pos min-x-pos) 2))
				    :objects considered.objects
				    :attributes (pr=obj.attributes (car considered.objects))))
      (setf (pr=obj.attributes (car considered.objects)) nil)
      (setf (pr=buffer.object.list buffer) (cons new.obj object.list)))))
	       
  

;;;;; Parse 1 :  Parsing length of formula and deciding the fonts and colours:

 
(defun pr=gterm.length.list (gterm eval.function buffer surrounding taf)
  (let (notion termlist (length 0) symb.length add.length total.length attributes)
    (setq attributes (cond (eval.function (funcall eval.function gterm taf))))
    (pr=with.attributes attributes
       (setq notion (pr=symbol.notion (da-gterm.symbol gterm)))
       (prog1 (cond ((member (da-gterm.symbol gterm) '(all ex))
		     (pr=gterm.junction.length.list gterm eval.function buffer surrounding taf))
		    (T (setq taf (da-taf.create.zero taf))
		       (setq termlist (mapcar #'(lambda (sub.gterm)
						  (setq taf (da-taf.create.next taf))
						  (pr=gterm.length.list sub.gterm eval.function buffer notion taf))
					      (da-gterm.termlist gterm)))
		       (mapc #'(lambda (item) (incf length (car item))) termlist)
		       (setq symb.length (pr=op.length (da-gterm.symbol gterm)))
		       (setq add.length 
			     (cond ((and (da-literal.is gterm) (da-sign.is.negative (da-literal.sign gterm)))
				    (+ (pr=junctor.length 'not) (pr=char.width #\Space)))
				   (t 0)))
		       (case notion
			     (infix (setq total.length (+ (cond ((member surrounding '(prefix junctor)) 0)
								(t (* 2 (pr=char.width #\)))))
							  length add.length
							  (* (1- (length termlist))
							     (+ symb.length (* 2 (pr=char.width #\Space))))))
				    (list total.length symb.length termlist nil attributes))
			     (prefix_without_bracket
			      (setq total.length 
				    (+ symb.length add.length
				       (cond (termlist
					      (+ (pr=char.width #\Space)
						 length
						 (* (1- (length termlist))
						    (+ (pr=char.width #\,) (pr=char.width #\Space)))))
					     (t 0))))
			      (list total.length symb.length termlist nil attributes))
			     (prefix (setq total.length 
					   (+ symb.length add.length
					      (cond (termlist
						     (+ (* 2 (pr=char.width #\)))
							length
							(* (1- (length termlist))
							   (+ (pr=char.width #\,) (pr=char.width #\Space)))))
						    (t 0))))
				     (list total.length symb.length termlist nil attributes)))))))))



(defun pr=gterm.junction.length.list (gterm eval.function buffer surrounding taf)

  (let (attributes total.length symb.length sub.form.length var.length)
    (setq attributes (cond (eval.function (funcall eval.function gterm taf))))
    (pr=with.attributes attributes
       (setq symb.length (pr=op.length (da-gterm.symbol gterm)))
       (setq sub.form.length (pr=gterm.length.list (second (da-gterm.termlist gterm)) 
						   eval.function buffer surrounding
						   (cons 2 taf)))
       (setq var.length (pr=op.length (car (da-gterm.termlist gterm))))
       (setq total.length (+ symb.length (* 2 (pr=char.width #\Space))
			     sub.form.length var.length)))
    (list total.length symb.length var.length sub.form.length attributes)))



(defun pr=subst.length.list (subst buffer)

  (cond ((null subst) (list 0 nil))
	(t (let ((op.length (pr=junctor.length 'gets)) var.length.list value.length.list total.length
		 (total.list.length 0) length.list)
	     (mapcf #'(lambda (var value)
			(setq var.length.list (pr=gterm.length.list var #'(lambda (x y)
									    (declare (ignore x y)) nil)
								    buffer 'infix nil))
			(setq value.length.list (pr=gterm.length.list value #'(lambda (x y)
										(declare (ignore x y)) nil) 
								      buffer 'infix nil))
			(setq total.length (+ op.length (* 2 (pr=char.width #\Space))
					      (car var.length.list) (car value.length.list)))
			(push (list total.length op.length var.length.list value.length.list)
			      length.list)
			(incf total.list.length (+ total.length (pr=char.width #\,) (pr=char.width #\Space))))
		    subst)
	     (list (- total.list.length (+ (pr=char.width #\,) (pr=char.width #\Space)))
		   (reverse length.list))))))


(defun pr=subst.parse (buffer subst length.list)

  (let ((s.length.list (second length.list)) length.entry)
    (pr=buffer.push buffer)
    (mapcf #'(lambda (var value)
	       (setq length.entry (car s.length.list))
	       (cond ((and (> (car length.entry) (pr=buffer.remaining.length buffer))
			   (not (eql 0 (pr=buffer.actual.width buffer))))
		      (pr=buffer.newline buffer)))
	       (pr=gterm.parse buffer var (third length.entry) 'prefix)
	       (pr=buffer.format.command buffer 'space)
	       (pr=buffer.format.junctor buffer 'gets (pr=junctor.length 'gets))
	       (pr=buffer.format.command buffer 'space)
	       (pr=gterm.parse buffer value (fourth length.entry) 'prefix)
	       (pop s.length.list))
	   subst)
    (pr=buffer.pop buffer)))


(defun pr=op.length (symbol)

  (cond ((da-symbol.is symbol)
	 (PR=STRING.WIDTH (da-symbol.pname symbol)))
	(t (pr=junctor.length symbol))))


(defun pr=junctor.length (junctor)

  (pr=with.attributes '(:font symbol)
      (pr=char.width (pr=junctor.char junctor))))


(defun pr=junctor.char (junctor)

  (code-char (case junctor
		   (gets 172)
		   (and 217)
		   (or 218)
		   (impl 174)
		   (eqv 171)
		   (not 216)
		   (all 34)
		   (ex 36)
		   (otherwise 36))))


(defun pr-junctor.char (junctor) 
  
  (pr=junctor.char junctor))


;;;;;==================================================================================================
;;;;; 
;;;;; Section IV
;;;;;
;;;;; Parsing Trees
;;;;;
;;;;;==================================================================================================


(DEFUN PR=OBJ.MOVE (OBJECTS X-OFFSET)

  (DECLARE (TYPE FIXNUM X-OFFSET) (TYPE LIST OBJECTS))
  (MAPC #'(LAMBDA (OBJECT)
	    (cond (object (DECF (PR=OBJ.X-POS OBJECT) X-OFFSET))))
	 OBJECTS))


(DEFUN PR=MAX.WIDTH (LEFTS RIGHTS DIST L.X.POS L.Y.POS R.X.POS R.Y.POS &OPTIONAL NO.MERGE)

  (DECLARE (TYPE FIXNUM L.X.POS L.Y.POS R.X.POS R.Y.POS))
  (LET ((NEW.L.X.POS 0) (NEW.L.Y.POS 0) (NEW.R.X.POS 0) (NEW.R.Y.POS 0) new.lefts new.rights)
    (DECLARE (TYPE FIXNUM NEW.L.X.POS NEW.L.Y.POS NEW.R.X.POS NEW.R.Y.POS))
    (MAPC #'(LAMBDA (LEFT.OBJ)
	      (MAPC #'(LAMBDA (RIGHT.OBJ)
			(COND (NO.MERGE (SETQ DIST (PR=OBJECTS.DIST LEFT.OBJ RIGHT.OBJ DIST L.X.POS R.X.POS)))
			      ((PR=OBJECTS.CLASH LEFT.OBJ RIGHT.OBJ DIST L.X.POS L.Y.POS R.X.POS R.Y.POS)
			       (SETQ DIST (COND ((OR (EQ 'TREE (PR=OBJ.TYPE LEFT.OBJ))
						     (EQ 'TREE (PR=OBJ.TYPE RIGHT.OBJ)))
						 (multiple-value-setq (new.lefts new.l.x.pos new.l.y.pos)
						     (PR=SEPARATE.OBJECT LEFT.OBJ L.X.POS L.Y.POS))
						 (multiple-value-setq (new.rights new.r.x.pos new.r.y.pos)
						     (PR=SEPARATE.OBJECT right.OBJ R.X.POS R.Y.POS))
						 (PR=MAX.WIDTH new.lefts new.rights DIST
							       NEW.L.X.POS NEW.L.Y.POS NEW.R.X.POS NEW.R.Y.POS))
						(T (PR=OBJECTS.DIST LEFT.OBJ RIGHT.OBJ DIST L.X.POS R.X.POS)))))))
		    RIGHTS))
	  LEFTS)
    DIST))


(defun PR=SEPARATE.OBJECT (object x.pos y.pos)

  (DECLARE (TYPE FIXNUM x.pos y.pos) (TYPE PR*OBJECT object))
  (let (objects (NEW.X.POS 0) (NEW.Y.POS 0) OBJ)
    (DECLARE (TYPE FIXNUM NEW.x.pos NEW.y.pos))
    (setq objects (COND ((EQ 'TREE (PR=OBJ.TYPE OBJECT))
			 (SETQ NEW.X.POS (+ X.POS (PR=OBJ.X-POS OBJECT)))
			 (SETQ NEW.Y.POS (+ Y.POS (PR=OBJ.Y-POS OBJECT)))
			 (delete nil (append (COND ((SETQ OBJ (CAR (PR=OBJ.OBJECTS OBJECT))) (LIST OBJ)))
					     (SECOND (PR=OBJ.OBJECTS OBJECT))
					     (THIRD (PR=OBJ.OBJECTS OBJECT)))))
			(T (SETQ NEW.X.POS X.POS NEW.Y.POS Y.POS)
			   (LIST OBJECT))))
    (values objects NEW.X.POS NEW.Y.POS)))


(DEFUN PR=OBJECTS.DIST (LEFT RIGHT DIST L.X.POS R.X.POS)

  (DECLARE (TYPE FIXNUM DIST L.X.POS R.X.POS) (TYPE PR*OBJECT LEFT RIGHT))
  (MAX DIST (- (+ L.X.POS (PR=OBJ.X-POS LEFT) (PR=OBJ.WIDTH LEFT))
	       (+ (PR=OBJ.X-POS RIGHT) R.X.POS))))


(DEFUN PR=OBJECTS.CLASH (LEFT RIGHT DISTANCE L.X.POS L.Y.POS R.X.POS R.Y.POS)

  (DECLARE (TYPE FIXNUM DISTANCE L.X.POS L.Y.POS R.X.POS R.Y.POS) (TYPE PR*OBJECT LEFT RIGHT))
  (AND (<= (+ R.Y.POS (PR=OBJ.Y-POS RIGHT)) (+ L.Y.POS (PR=OBJ.Y-POS LEFT) (PR=OBJ.HEIGHT LEFT)))
       (>= (+ R.Y.POS (PR=OBJ.Y-POS RIGHT) (PR=OBJ.HEIGHT RIGHT)) (+ L.Y.POS (PR=OBJ.Y-POS LEFT)))
       (<= (+ R.X.POS DISTANCE (PR=OBJ.X-POS RIGHT)) (+ L.X.POS (PR=OBJ.X-POS LEFT) (PR=OBJ.WIDTH LEFT)))))



;;;;;==================================================================================================
;;;;; 
;;;;; Section V
;;;;;
;;;;; Parsing Graphs (Algorithm of Kozo Sugiyama)
;;;;;
;;;;;====================================================================================================


(DEFUN PR=GRAPH.GRAPHLIST.CREATE (TOP.NODES HASH.TABLE SUCCESS.FCT PRINT.FCT)

  ;;; Input:   a list of top nodes of a graph, a hash table containing the relation between nodes
  ;;;          and their internal representation as \verb$PR*GRAPH.NODE$, a lisp-function which
  ;;;          computes the successors of a node and a lisp-function computing the printed
  ;;;          representation of a node.
  ;;; Effect:  creates an array of levels, computes the internal representation of each node,
  ;;;          inserts them into the hash table and into the array at appropriate level.
  ;;; Value:   the array

  (DECLARE (TYPE LIST TOP.NODES))
  
  (LET (ARRAY (DEPTH 0))
    (DECLARE (TYPE (OR NULL (SIMPLE-ARRAY LIST 1)) ARRAY) (TYPE FIXNUM DEPTH))
    (SETQ TOP.NODES (PR=GRAPH.GRAPHLIST.FIND.DEPTH TOP.NODES 0 HASH.TABLE SUCCESS.FCT PRINT.FCT))
    (SETQ DEPTH (PR=GRAPH.GRAPHLIST.FIND.LOWEST.LEVEL TOP.NODES))
    (SETQ ARRAY (MAKE-ARRAY (1+ DEPTH) :ELEMENT-TYPE 'LIST :INITIAL-ELEMENT NIL))
    (MAPC #'(LAMBDA (NODE)
	      (DECLARE (TYPE PR*GRAPH.NODE NODE))
	      (PR=GRAPH.GRAPHLIST.ADD.TO.LEVELS NODE ARRAY -1))
	  TOP.NODES)
    (PR=GRAPH.GRAPHLIST.INSERT.POS ARRAY)
    ARRAY))


(DEFUN PR=GRAPH.GRAPHLIST.FIND.DEPTH (NODES DEPTH HASH.TABLE SUCC.FCT PRINT.FCT)

  ;;; Input:  a list of nodes and their level of a graph, a hash table, and both lisp-functions as
  ;;;         described above.
  ;;; Effect: computes for each node its internal representation and its maximal depth in the graph.
  ;;; Value:  a list of all internal representations of nodes.

  (DECLARE (TYPE LIST NODES) (TYPE FIXNUM DEPTH) (TYPE HASH-TABLE HASH.TABLE))
  
  (LET (ENTRY ALL.ENTRIES)
    (DECLARE (TYPE (OR NULL PR*GRAPH.NODE) ENTRY) (TYPE LIST ALL.ENTRIES))
    (MAPC #'(LAMBDA (NODE)
	      (DECLARE (TYPE PR*GRAPH.NODE NODE))
	      (COND ((SETQ ENTRY (GETHASH NODE HASH.TABLE))
		     (COND ((> DEPTH (PR=GRAPH.NODE.LEVEL ENTRY))
			    (SETF (PR=GRAPH.NODE.LEVEL ENTRY) DEPTH)
			    (PR=GRAPH.GRAPHLIST.ADJUST.DEPTH (PR=GRAPH.NODE.SUCCS ENTRY) (1+ DEPTH)))))
		    (T (SETQ ENTRY (MAKE-PR*GRAPH.NODE :TEXT (FUNCALL PRINT.FCT NODE) :LEVEL DEPTH))
		       (SETF (PR=GRAPH.NODE.SUCCS ENTRY)
			     (PR=GRAPH.GRAPHLIST.FIND.DEPTH (FUNCALL SUCC.FCT NODE) (1+ DEPTH) HASH.TABLE SUCC.FCT PRINT.FCT))
		       (SETF (GETHASH NODE HASH.TABLE) ENTRY)))
	      (PUSH ENTRY ALL.ENTRIES))
	  NODES)
    (NREVERSE ALL.ENTRIES)))


(DEFUN PR=GRAPH.GRAPHLIST.ADJUST.DEPTH (NODES DEPTH)

  ;;; Input:   a list of nodes and their level of a graph.
  ;;; Effect:  sets the depth of each node of the graphs (specified by \verb$NODES$) to
  ;;;          their maximal depths
  ;;; Value:   undefined

  (DECLARE (TYPE LIST NODES) (TYPE FIXNUM DEPTH))
  
  (MAPC #'(LAMBDA (NODE)
	    (DECLARE (TYPE PR*GRAPH.NODE NODE))
	    (COND ((> DEPTH (PR=GRAPH.NODE.LEVEL NODE))
		   (SETF (PR=GRAPH.NODE.LEVEL NODE) DEPTH)
		   (PR=GRAPH.GRAPHLIST.ADJUST.DEPTH (PR=GRAPH.NODE.SUCCS NODE) (1+ DEPTH)))))
	NODES))


(DEFUN PR=GRAPH.GRAPHLIST.FIND.LOWEST.LEVEL (NODES)

  ;;; Input:   a list of nodes of a graph (\verb$PR*GRAPH.NODE$)
  ;;; Effect:  decreases the level of each node in the graph as far as possible without
  ;;;          loosing the property that each node has a higher level as its predecessors.
  ;;; Value:   the deepest level in the graph

  (DECLARE (TYPE LIST NODES))
  
  (LET ((LEVEL 0) (NODE.LEVEL 0) (DEEPEST.LEVEL 0))
    (DECLARE (TYPE FIXNUM DEEPEST.LEVEL NODE.LEVEL LEVEL))
    (MAPC #'(LAMBDA (NODE)
	      (DECLARE (TYPE PR*GRAPH.NODE NODE))
	      (COND ((PR=GRAPH.NODE.SUCCS NODE)
		     (COND ((NOT (NUMBERP (PR=GRAPH.NODE.BARY NODE)))
			    (SETF (PR=GRAPH.NODE.BARY NODE)
				  (PR=GRAPH.GRAPHLIST.FIND.LOWEST.LEVEL (PR=GRAPH.NODE.SUCCS NODE))))))
		    (T (SETF (PR=GRAPH.NODE.BARY NODE) (PR=GRAPH.NODE.LEVEL NODE))))
	      (SETQ LEVEL (1+ (PR=GRAPH.NODE.LEVEL NODE))
		    NODE.LEVEL 1000000)
	      (COND ((AND (PR=GRAPH.NODE.SUCCS NODE)
			  (EVERY #'(LAMBDA (SUB.NODE)
				     (DECLARE (TYPE PR*GRAPH.NODE SUB.NODE))
				     (COND ((< LEVEL (PR=GRAPH.NODE.LEVEL SUB.NODE))
					    (SETQ NODE.LEVEL (MIN NODE.LEVEL (PR=GRAPH.NODE.LEVEL SUB.NODE))))))
				 (PR=GRAPH.NODE.SUCCS NODE)))
		     (SETF (PR=GRAPH.NODE.LEVEL NODE) (1- NODE.LEVEL))))
	      (SETQ DEEPEST.LEVEL (MAX DEEPEST.LEVEL (PR=GRAPH.NODE.BARY NODE))))
	  NODES)
    DEEPEST.LEVEL))


(DEFUN PR=GRAPH.GRAPHLIST.ADD.TO.LEVELS (NODE ARRAY &OPTIONAL (LEVEL -1))

  ;;; Input:   a node of a graph (\verb$PR*GRAPH.NODE$), an array and a number
  ;;; Effect:  inserts node to the array at level \verb$LEVEL$ and inserts for
  ;;;          each long term arc an additional (invisible) node.
  ;;; Value:   undefined  

  (DECLARE (TYPE PR*GRAPH.NODE NODE) (TYPE (SIMPLE-ARRAY LIST 1) ARRAY) (TYPE FIXNUM LEVEL))
  
  (LET (SUCC SUCC.SUCCS)
    (DECLARE (TYPE LIST SUCC.SUCCS) (TYPE (or null PR*GRAPH.NODE) SUCC))
    (COND ((EQL -1 LEVEL) (SETQ LEVEL (PR=GRAPH.NODE.LEVEL NODE))))
    (COND ((NOT (MEMBER NODE (AREF ARRAY LEVEL)))
	   (PUSH NODE (AREF ARRAY LEVEL))
	   (SETF (PR=GRAPH.NODE.SUCCS NODE)
		 (DELETE-IF #'(LAMBDA (SUB.NODE)
				(DECLARE (TYPE PR*GRAPH.NODE SUB.NODE))
				(COND ((NOT (EQL (1+ LEVEL) (PR=GRAPH.NODE.LEVEL SUB.NODE)))
				       (PUSH SUB.NODE SUCC.SUCCS))
				      (T (PUSH NODE (PR=GRAPH.NODE.PREDS SUB.NODE))
					 NIL)))
			    (PR=GRAPH.NODE.SUCCS NODE)))
	   (COND (SUCC.SUCCS (SETQ SUCC (MAKE-PR*GRAPH.NODE :TEXT (MAKE-PR*OBJECT :ATTRIBUTES (LIST 'INVISIBLE T))
							    :LEVEL (1+ LEVEL) :SUCCS SUCC.SUCCS))
			     (PUSH SUCC (PR=GRAPH.NODE.SUCCS NODE))
			     (PUSH NODE (PR=GRAPH.NODE.PREDS SUCC))))
	   (MAPC #'(LAMBDA (SUB.NODE)
		     (DECLARE (TYPE PR*GRAPH.NODE SUB.NODE))
		     (PR=GRAPH.GRAPHLIST.ADD.TO.LEVELS SUB.NODE ARRAY (1+ LEVEL)))
		 (PR=GRAPH.NODE.SUCCS NODE))))))


(DEFUN PR=GRAPH.GRAPHLIST.INSERT.POS (ARRAY)

  ;;; Input:   an array representing the graph
  ;;; Effect:  sets the \verb$POS$-slot of each node in \verb$ARRAY$ to its actual position
  ;;;          in its level.
  ;;; Value:   undefined

  (DECLARE (TYPE (SIMPLE-ARRAY LIST 1) ARRAY))
  
  (DOTIMES (I (ARRAY-DIMENSION ARRAY 0))
    (LET ((COUNTER 0))
      (DECLARE (TYPE FIXNUM COUNTER))
      (MAPC #'(LAMBDA (NODE)
		(DECLARE (TYPE PR*GRAPH.NODE NODE))
		(SETF (PR=GRAPH.NODE.POS NODE) (INCF COUNTER)))
	    (AREF ARRAY I)))))


(DEFUN PR=GRAPH.NODE.PRINT (NODE OUTPUT IGNORE)

  ;;; Input:   a node, an output-stream and a  number
  ;;; Effect:  prints \verb$NODE$ to \verb$OUTPUT$.
  
  (DECLARE (IGNORE IGNORE))
  
  (FORMAT OUTPUT "~A" (PR=GRAPH.NODE.TEXT NODE)))


(DEFUN PR=GRAPH.BARY (NODE TYPE)

  ;;; Input:  a node and an atom like \verb$R$ or \verb$C$
  ;;; Effect: Computes the barycenter $B^R$ resp. $B^C$ for \verb$NODE$.
  ;;; Value:  the barycenter

  (DECLARE (TYPE PR*GRAPH.NODE NODE))
  
  (LET ((SUM 0) (COUNTER 0))
    (DECLARE (TYPE FIXNUM SUM COUNTER))
    (MAPC #'(LAMBDA (SUCC)
	      (DECLARE (TYPE PR*GRAPH.NODE SUCC))
	      (INCF SUM (PR=GRAPH.NODE.POS SUCC))
	      (INCF COUNTER))
	  (COND ((EQ TYPE 'R) (PR=GRAPH.NODE.SUCCS NODE))
		(T (PR=GRAPH.NODE.PREDS NODE))))
    (COND ((NOT (EQL COUNTER 0))  (/ SUM COUNTER))
	  (T 100000))))


(DEFUN PR=GRAPH.CROSSING.OF.LISTS (NODE.LIST)

  ;;; Input:   a list of nodes
  ;;; Effect:  computes all crossings between the arcs of the nodes to their successors.
  ;;; Value:   the number of crossings

  (DECLARE (TYPE LIST NODE.LIST))
  
  (LET ((SUM 0) NODE1)
    (DECLARE (TYPE FIXNUM SUM))
    (MAPL #'(LAMBDA (NODE.TAIL)
	      (SETQ NODE1 (CAR NODE.TAIL))
	      (MAPC #'(LAMBDA (NODE2)
			(MAPC #'(LAMBDA (SUCC1)
				  (MAPC #'(LAMBDA (SUCC2)
					    (COND ((> (PR=GRAPH.NODE.POS SUCC1) (PR=GRAPH.NODE.POS SUCC2))
						   (INCF SUM))))
					(PR=GRAPH.NODE.SUCCS NODE2)))
			      (PR=GRAPH.NODE.SUCCS NODE1)))
		    (CDR NODE.TAIL)))
	  NODE.LIST)
    SUM))


(DEFUN PR=GRAPH.BETA (NODE.LIST LABEL)

  ;;; Input:   a list of nodes and an atom like \verb$R$ or \verb$C$
  ;;; Effect:  sorts the nodes according their barycenter $B^R$ resp. $B^C$
  ;;; Value:   a multiple-value: the sorted list of nodes and a flag indicating that
  ;;;          some positions have changed

  (DECLARE (TYPE LIST NODE.LIST))
  
  (LET ((COUNTER 0) CHANGED RESULT)
    (MAPC #'(LAMBDA (NODE)
	      (SETF (PR=GRAPH.NODE.BARY NODE) (PR=GRAPH.BARY NODE LABEL)))
	  NODE.LIST)
    (SETQ RESULT (MAPC #'(LAMBDA (NODE)
			   (DECLARE (TYPE PR*GRAPH.NODE NODE))
			   (INCF COUNTER)
			   (COND ((NOT (EQL COUNTER (PR=GRAPH.NODE.POS NODE)))
				  (SETF (PR=GRAPH.NODE.POS NODE) COUNTER)
				  (SETQ CHANGED T))))
		       (STABLE-SORT (copy-list NODE.LIST) #'< :KEY #'(LAMBDA (NODE) (PR=GRAPH.NODE.BARY NODE)))))
    (VALUES RESULT CHANGED)))


(DEFUN PR=GRAPH.RHO (NODE.LIST TYPE)

  ;;; Input:   a list of nodes and an atom like \verb$R$ or \verb$C$
  ;;; Effect:  reverts the positions of all nodes with equal barycenters
  ;;; Value:   a multiple-value: the sorted list of nodes and a flag indicating that
  ;;;          some positions have changed

  (DECLARE (TYPE LIST NODE.LIST))
  
  (LET ((BARY -1) (FIRST.POS 0) ALL.NODES CHANGED)
    (DECLARE (TYPE FIXNUM BARY FIRST.POS))
    (COND ((> (PR=GRAPH.CROSSING.OF.LISTS NODE.LIST) 0)
	   (MAPC #'(LAMBDA (NODE)
		     (DECLARE (TYPE PR*GRAPH.NODE NODE))
		     (SETF (PR=GRAPH.NODE.BARY NODE) (PR=GRAPH.BARY NODE TYPE)))
		 NODE.LIST)
	   (MAPC #'(LAMBDA (NODE)
		     (DECLARE (TYPE PR*GRAPH.NODE NODE))
		     (COND ((NOT (EQL (PR=GRAPH.NODE.BARY NODE) BARY))
			    (COND ((CDR ALL.NODES)
			    (MAPC #'(LAMBDA (M.NODE)
				      (DECLARE (TYPE PR*GRAPH.NODE M.NODE))
				      (SETF (PR=GRAPH.NODE.POS M.NODE) FIRST.POS)
				      (INCF FIRST.POS))
				  ALL.NODES)
			    (SETQ CHANGED T)))
			    (SETQ ALL.NODES (LIST NODE))
			    (SETQ BARY (PR=GRAPH.NODE.BARY NODE))
			    (SETQ FIRST.POS (PR=GRAPH.NODE.POS NODE)))
			   (T (PUSH NODE ALL.NODES))))
		 NODE.LIST)
	   (COND ((CDR ALL.NODES)
		  (MAPC #'(LAMBDA (M.NODE)
			    (DECLARE (TYPE PR*GRAPH.NODE M.NODE))
			    (SETF (PR=GRAPH.NODE.POS M.NODE) FIRST.POS)
			    (INCF FIRST.POS))
			ALL.NODES)
		  (SETQ CHANGED T)))))
    (COND (CHANGED (VALUES (SORT NODE.LIST #'< :KEY #'(LAMBDA (NODE) (PR=GRAPH.NODE.POS NODE)))
			   T))
	  (T (VALUES NODE.LIST NIL)))))


(DEFUN PR=GRAPH.NODE.LIST.SAVE.POS (NODE.LIST)

  ;;; Input:   a list of nodes
  ;;; Effect:  stores the actual position of each node in the \verb$OLD.POS$ slot.

  (DECLARE (TYPE LIST NODE.LIST))
  
  (MAPC #'(LAMBDA (NODE)
	    (DECLARE (TYPE PR*GRAPH.NODE NODE))
	    (SETF (PR=GRAPH.NODE.OLD.POS NODE) (PR=GRAPH.NODE.POS NODE)))
	NODE.LIST))


(DEFUN PR=GRAPH.NODE.LIST.RESTORE.POS (NODE.LIST)

  ;;; Input:   a list of nodes
  ;;; Effect:  restores the saved position of each node in the \verb$OLD.POS$ slot.
  ;;; Value:   the resorted list

  (DECLARE (TYPE LIST NODE.LIST))
  
  (MAPC #'(LAMBDA (NODE)
	    (DECLARE (TYPE PR*GRAPH.NODE NODE))
	    (SETF (PR=GRAPH.NODE.POS NODE) (PR=GRAPH.NODE.OLD.POS NODE)))
	NODE.LIST)
  (SORT NODE.LIST #'< :KEY #'(LAMBDA (NODE) (PR=GRAPH.NODE.POS NODE))))


(DEFUN PR=GRAPH.BC.PHASES (ARRAY)

  ;;; Input:   an array representing the graph
  ;;; Effect:  applies the BC-algorithm to the graph in order to determine the
  ;;;          relative position of each node in \verb$ARRAY$.
  ;;; Value:   undefined

  (DECLARE (TYPE (SIMPLE-ARRAY LIST 1) ARRAY))
  
  (PR=GRAPH.BC.PHASE.1.DOWN ARRAY)
  (PR=GRAPH.BC.PHASE.1.UP ARRAY)
  (PR=GRAPH.BC.PHASE.2.DOWN ARRAY)
  (PR=GRAPH.BC.PHASE.2.UP ARRAY))


(DEFUN PR=GRAPH.BC.PHASE.1.DOWN (ARRAY.OF.LEVELS &OPTIONAL (START 0))

  ;;; Input:   an array representing the graph and a number
  ;;; Effect:  applies the BC-phase 1 (down) to each level of \verb$ARRAY$ starting at \verb$START$.
  ;;; Value:   T, iff some positions have changed

  (DECLARE (TYPE (SIMPLE-ARRAY LIST 1) ARRAY.OF.LEVELS) (TYPE FIXNUM START))
  
  (LET (SOMETHING.HAPPEND LEVEL1 CHANGED NEW.CROSS.NOS OLD.CROSS.NO)
    (DO ((I START (+ I 1)))
	((= I (1- (ARRAY-DIMENSION ARRAY.OF.LEVELS 0))))
      (PR=GRAPH.NODE.LIST.SAVE.POS (AREF ARRAY.OF.LEVELS (1+ I)))
      (SETQ OLD.CROSS.NO (PR=GRAPH.CROSSING.OF.LISTS (AREF ARRAY.OF.LEVELS I)))
      (MULTIPLE-VALUE-SETQ (LEVEL1 CHANGED) (PR=GRAPH.BETA (AREF ARRAY.OF.LEVELS (1+ I)) 'C))
      (COND (CHANGED
	     (SETQ NEW.CROSS.NOS (PR=GRAPH.CROSSING.OF.LISTS (AREF ARRAY.OF.LEVELS I)))
	     (COND ((< NEW.CROSS.NOS OLD.CROSS.NO)
		    (SETQ SOMETHING.HAPPEND T)
		    (SETQ OLD.CROSS.NO NEW.CROSS.NOS)
		    (SETF (AREF ARRAY.OF.LEVELS (1+ I)) LEVEL1))
		   (T (SETF (AREF ARRAY.OF.LEVELS (1+ I))
			    (PR=GRAPH.NODE.LIST.RESTORE.POS (AREF ARRAY.OF.LEVELS (1+ I)))))))))
    SOMETHING.HAPPEND))


(DEFUN PR=GRAPH.BC.PHASE.2.DOWN (ARRAY.OF.LEVELS)

  ;;; Input:   an array representing the graph
  ;;; Effect:  applies the BC-phase 2 (down) to each level of \verb$ARRAY$
  ;;; Value:   T, iff some positions have changed

  (DECLARE (TYPE (SIMPLE-ARRAY LIST 1) ARRAY.OF.LEVELS))
  
  (LET (SOMETHING.HAPPEND LEVEL1 CHANGED)
    (DO ((I 0 (+ I 1)))
	((= I (1- (ARRAY-DIMENSION ARRAY.OF.LEVELS 0))))
      (PR=GRAPH.NODE.LIST.SAVE.POS (AREF ARRAY.OF.LEVELS I))
      (MULTIPLE-VALUE-SETQ (LEVEL1 CHANGED) (PR=GRAPH.RHO (AREF ARRAY.OF.LEVELS (1+ I)) 'C))
      (COND (CHANGED (SETF (AREF ARRAY.OF.LEVELS (1+ I)) LEVEL1)
		     (PR=GRAPH.BC.PHASE.1.DOWN ARRAY.OF.LEVELS (1+ I))
		     (PR=GRAPH.BC.PHASE.1.UP ARRAY.OF.LEVELS I)
		     (SETQ SOMETHING.HAPPEND T))))
    SOMETHING.HAPPEND))

    
(DEFUN PR=GRAPH.BC.PHASE.1.UP (ARRAY.OF.LEVELS &OPTIONAL START)

  ;;; Input:   an array representing the graph and a number
  ;;; Effect:  applies the BC-phase 1 (up) to each level of \verb$ARRAY$ starting at \verb$START$.
  ;;; Value:   T, iff some positions have changed

  (DECLARE (TYPE (SIMPLE-ARRAY LIST 1) ARRAY.OF.LEVELS))
  
  (LET (SOMETHING.HAPPEND LEVEL1 CHANGED NEW.CROSS.NOS OLD.CROSS.NO)
    (DO ((I (COND (START) (T (- (ARRAY-DIMENSION ARRAY.OF.LEVELS 0) 2)))
	    (- I 1)))
	((= I -1))
      (PR=GRAPH.NODE.LIST.SAVE.POS (AREF ARRAY.OF.LEVELS I))
      (SETQ OLD.CROSS.NO (PR=GRAPH.CROSSING.OF.LISTS (AREF ARRAY.OF.LEVELS I)))
      (MULTIPLE-VALUE-SETQ (LEVEL1 CHANGED) (PR=GRAPH.BETA (AREF ARRAY.OF.LEVELS I) 'R))
      (COND (CHANGED
	     (SETQ NEW.CROSS.NOS (PR=GRAPH.CROSSING.OF.LISTS LEVEL1))
	     (COND ((< NEW.CROSS.NOS OLD.CROSS.NO)
		    (SETQ SOMETHING.HAPPEND T)
		    (SETQ OLD.CROSS.NO NEW.CROSS.NOS)
		    (SETF (AREF ARRAY.OF.LEVELS I) LEVEL1))
		   (T (SETF (AREF ARRAY.OF.LEVELS I)
			    (PR=GRAPH.NODE.LIST.RESTORE.POS (AREF ARRAY.OF.LEVELS I))))))))
    SOMETHING.HAPPEND))


(DEFUN PR=GRAPH.BC.PHASE.2.UP (ARRAY.OF.LEVELS)

  ;;; Input:   an array representing the graph
  ;;; Effect:  applies the BC-phase 2 (up) to each level of \verb$ARRAY$
  ;;; Value:   T, iff some positions have changed

  (DECLARE (TYPE (SIMPLE-ARRAY LIST 1) ARRAY.OF.LEVELS))
  
  (LET (SOMETHING.HAPPEND LEVEL1 CHANGED)
    (DO ((I (- (ARRAY-DIMENSION ARRAY.OF.LEVELS 0) 2) (- I 1)))
	((= I -1))
      (PR=GRAPH.NODE.LIST.SAVE.POS (AREF ARRAY.OF.LEVELS I))
      (MULTIPLE-VALUE-SETQ (LEVEL1 CHANGED) (PR=GRAPH.RHO (AREF ARRAY.OF.LEVELS I) 'R))
      (COND (CHANGED (SETF (AREF ARRAY.OF.LEVELS I) LEVEL1)
		     (PR=GRAPH.BC.PHASE.1.UP ARRAY.OF.LEVELS (1- I))
		     (PR=GRAPH.BC.PHASE.1.DOWN ARRAY.OF.LEVELS I)
		     (SETQ SOMETHING.HAPPEND T))))
    SOMETHING.HAPPEND))


(DEFUN PR=GRAPH.LAYOUT (ARRAY.OF.LEVELS)

  ;;; Input:   an array representing the graph
  ;;; Effect:  computes the absolute positions of each node in the graph
  ;;; Value:   undefined

  (DECLARE (TYPE (SIMPLE-ARRAY LIST 1) ARRAY.OF.LEVELS))
  
  (LET (REV.LEVELS LEVELS REV.ORG.LEVELS ORG.LEVELS)
    (DECLARE (TYPE LIST REV.LEVELS LEVELS REV.ORG.LEVELS ORG.LEVELS))
    (MULTIPLE-VALUE-SETQ (REV.LEVELS REV.ORG.LEVELS) (PR=GRAPH.LAYOUT.INIT ARRAY.OF.LEVELS))
    (SETQ LEVELS (REVERSE REV.LEVELS) ORG.LEVELS (REVERSE REV.ORG.LEVELS))
    (MAPC #'(LAMBDA (LEVEL ORG.LEVEL)
	      (PR=GRAPH.LAYOUT.LEVEL LEVEL ORG.LEVEL 'UPPER))
	  (CDR LEVELS) (CDR ORG.LEVELS))
    (MAPC #'(LAMBDA (LEVEL ORG.LEVEL)
	      (PR=GRAPH.LAYOUT.LEVEL LEVEL ORG.LEVEL 'LOWER))
	  (CDR REV.LEVELS) (CDR REV.ORG.LEVELS))
   ))
   

(DEFUN PR=GRAPH.LAYOUT.INIT (ARRAY.OF.LEVELS)

  ;;; Input:   an array representing the graph
  ;;; Effect:  computes the initial x-position of each node such that
  ;;;          each node has a distance to its neighbour
  ;;;          nodes. Also each level is sorted according to the visibility
  ;;;          and number of predecessor nodes of the nodes.
  ;;; Value:   a mulitple value: a list of all sorted levels and a list of all 
  ;;;          original levels.
  
  (DECLARE (TYPE (SIMPLE-ARRAY LIST 1) ARRAY.OF.LEVELS))
  
  (LET ((X.POS 0) ALL.LEVELS ORG.LEVELS)
    (DECLARE (TYPE FIXNUM X.POS) (TYPE LIST ALL.LEVELS ORG.LEVELS))
    (DOTIMES (I (ARRAY-DIMENSION ARRAY.OF.LEVELS 0))
      (SETQ X.POS 0)
      (MAPC #'(LAMBDA (NODE)
		(DECLARE (TYPE PR*GRAPH.NODE NODE))
		(SETF (PR=OBJ.X-POS (PR=GRAPH.NODE.TEXT NODE)) X.POS)
		(COND ((ZEROP (PR=OBJ.WIDTH (PR=GRAPH.NODE.TEXT NODE)))
		       (SETF (PR=OBJ.WIDTH (PR=GRAPH.NODE.TEXT NODE)) 1)
		       (SETF (PR=OBJ.CENTER (PR=GRAPH.NODE.TEXT NODE)) 1)))
		(INCF X.POS (+ (FLOOR (PR=OBJ.WIDTH (PR=GRAPH.NODE.TEXT NODE))) (* 3 (pr=actual.size)))))
	    (AREF ARRAY.OF.LEVELS I))
      (PUSH (SORT (COPY-LIST (AREF ARRAY.OF.LEVELS I))
		  #'(LAMBDA (X Y)
		      (DECLARE (TYPE PR*GRAPH.NODE X Y))
		      (OR (PR=GRAPH.NODE.INVISIBLE X)
			  (AND (NOT (PR=GRAPH.NODE.INVISIBLE Y))
			       (> (LENGTH (PR=GRAPH.NODE.PREDS X))
				  (LENGTH (PR=GRAPH.NODE.PREDS Y)))))))
	    ALL.LEVELS)
      (PUSH (AREF ARRAY.OF.LEVELS I) ORG.LEVELS))
    (VALUES ALL.LEVELS ORG.LEVELS)))


(DEFUN PR=GRAPH.LAYOUT.LEVEL (LEVEL ORG.LEVEL DIRECTION)

  ;;; Input:   a list of nodes, the original list of these nodes, and two flags
  ;;; Effect:  rearranges the x-position of each node in \verb$LEVEL$ according
  ;;;          to their barycenters.
  ;;; Value:   undefined.

  (DECLARE (TYPE LIST LEVEL ORG.LEVEL))
  
  (LET (BARYCENTER CONSIDERED.NODES (DIFF 0) CLASS (REV.LEVEL (REVERSE ORG.LEVEL)))
    (DECLARE (TYPE FIXNUM DIFF) (TYPE LIST REV.LEVEL CONSIDERED.NODES))
    (MAPC #'(LAMBDA (NODE)
	      (DECLARE (TYPE PR*GRAPH.NODE NODE))
	      (SETQ CLASS (PR=GRAPH.LAYOUT.NODE.CLASS NODE DIRECTION))
	      (COND ((SETQ BARYCENTER (PR=GRAPH.NODE.BARYCENTER NODE DIRECTION))
		     (SETQ DIFF (- BARYCENTER (FLOOR (+ (PR=OBJ.X-POS (PR=GRAPH.NODE.TEXT NODE))
							(PR=OBJ.CENTER (PR=GRAPH.NODE.TEXT NODE))))))
		     (PR=GRAPH.LAYOUT.MAX.POSSIBLE.DIFF
		      DIFF NODE ORG.LEVEL REV.LEVEL CONSIDERED.NODES (LIST NODE DIFF CLASS))
		     (SETQ DIFF (- BARYCENTER
				   (FLOOR (+ (PR=OBJ.X-POS (PR=GRAPH.NODE.TEXT NODE))
					     (PR=OBJ.CENTER (PR=GRAPH.NODE.TEXT NODE)))))))
		    (T (SETQ DIFF 0)))
	      (PUSH (LIST NODE DIFF CLASS) CONSIDERED.NODES))
	  LEVEL)))


(DEFUN PR=GRAPH.LAYOUT.NODE.CLASS (NODE TYPE)

  ;;; Input:  a node and an atom indicating the direction
  ;;; Value:  either NIL iff \verb$NODE$ is invisible or the number of edges to the next level.

  (DECLARE (TYPE PR*GRAPH.NODE NODE))

  (LET ((LENGTH (LENGTH (COND ((EQ TYPE 'UPPER) (PR=GRAPH.NODE.PREDS NODE))
			      (T (PR=GRAPH.NODE.SUCCS NODE))))))
  (COND ((AND (PR=GRAPH.NODE.INVISIBLE NODE) (EQL LENGTH 1))
	 NIL)
	(T LENGTH))))



(DEFUN PR=GRAPH.NODE.BARYCENTER (NODE TYPE)

  ;;; Input:  a node, an atom like \verb$UPPER$ or \verb$LOWER$, and a flag
  ;;; Effect: Computes the barycenter $B^U$ resp. $B^L$ for \verb$NODE$ if \verb$INITIAL$
  ;;;         is $T$ or \verb$NODE$ has more (or equal) successors (resp. predecessors)
  ;;;         than each successor (resp. predecessor) has predecessors (resp. successors).
  ;;; Value:  the barycenter

  (DECLARE (TYPE PR*GRAPH.NODE NODE))
  
  (LET ((SUM 0) (COUNTER 0)
	(SUCCS (COND ((EQ TYPE 'UPPER) (PR=GRAPH.NODE.PREDS NODE))
		     (T (PR=GRAPH.NODE.SUCCS NODE)))))
    (DECLARE (TYPE FIXNUM SUM COUNTER) (TYPE LIST SUCCS))
    (COND (SUCCS
	   (MAPC #'(LAMBDA (SUCC)
		     (INCF COUNTER)
		     (INCF SUM (+ (PR=OBJ.X-POS (PR=GRAPH.NODE.TEXT SUCC))
				  (PR=OBJ.CENTER (PR=GRAPH.NODE.TEXT SUCC)))))
		 SUCCS)
	   (FLOOR (/ SUM COUNTER))))))


(DEFUN PR=GRAPH.LAYOUT.MAX.POSSIBLE.DIFF (DIFF NODE ORG.LEVEL REV.LEVEL CONSIDERED.NODES MOVE.SPEC)

  ;;; Input:   a distance, a node, its original and the reversed level, a list of nodes, and a specification
  ;;;          of the orignal node initiating this move
  ;;; Effect:  tries to move all nodes left (resp. right) of \verb$NODE$ \verb$DIFF$ points
  ;;;          to the left (resp. right)
  ;;; Value:   difference between wished and actual move

  (DECLARE (TYPE PR*GRAPH.NODE NODE) (TYPE LIST ORG.LEVEL REV.LEVEL CONSIDERED.NODES)
	   (TYPE FIXNUM DIFF))
  
  (LET ((SPACE 0) NEXT (ENTRY (ASSOC NODE CONSIDERED.NODES)))
    (DECLARE (TYPE FIXNUM SPACE))
    (COND ((AND ENTRY (OR (NULL (THIRD ENTRY)) (NULL (THIRD MOVE.SPEC))
			  (> (THIRD  ENTRY) (THIRD MOVE.SPEC)))))
	  ((> DIFF 0)
	   (SETQ DIFF (PR=GRAPH.LAYOUT.ADJUSTED.DIFF DIFF ENTRY MOVE.SPEC))
	   (COND ((SETQ NEXT (SECOND (MEMBER NODE ORG.LEVEL)))
		  (SETQ SPACE (PR=GRAPH.LAYOUT.NODE.DIFFS NODE NEXT))
		  (COND ((> DIFF SPACE)
			 (decf (second move.spec) space)
			 (PR=GRAPH.LAYOUT.MAX.POSSIBLE.DIFF (- DIFF SPACE) NEXT ORG.LEVEL
							    REV.LEVEL CONSIDERED.NODES MOVE.SPEC)
			 (SETQ SPACE (PR=GRAPH.LAYOUT.NODE.DIFFS NODE NEXT))))
		  (COND ((> SPACE 0)
			 (INCF (PR=OBJ.X-POS (PR=GRAPH.NODE.TEXT NODE)) (MIN SPACE DIFF))
			 (COND (ENTRY (INCF (SECOND ENTRY) (MIN SPACE DIFF)))))))
		 (T (INCF (PR=OBJ.X-POS (PR=GRAPH.NODE.TEXT NODE)) DIFF))))
	  ((< DIFF 0)
	   (SETQ DIFF (PR=GRAPH.LAYOUT.ADJUSTED.DIFF DIFF ENTRY MOVE.SPEC))
	   (COND ((SETQ NEXT (SECOND (MEMBER NODE REV.LEVEL)))
		  (SETQ SPACE (PR=GRAPH.LAYOUT.NODE.DIFFS NEXT NODE))
		  (COND ((> (ABS DIFF) SPACE)
			 (incf (second move.spec) SPACE)
			 (PR=GRAPH.LAYOUT.MAX.POSSIBLE.DIFF (+ DIFF SPACE) NEXT ORG.LEVEL
							    REV.LEVEL CONSIDERED.NODES MOVE.SPEC)
			 (SETQ SPACE (PR=GRAPH.LAYOUT.NODE.DIFFS NEXT NODE))))
		  (COND ((> SPACE 0)
			 (DECF (PR=OBJ.X-POS (PR=GRAPH.NODE.TEXT NODE)) (MIN (ABS DIFF) SPACE))
			 (COND (ENTRY (DECF (SECOND ENTRY) (MIN (ABS DIFF) SPACE)))))))
		 (T (INCF (PR=OBJ.X-POS (PR=GRAPH.NODE.TEXT NODE)) DIFF)))))))


(DEFUN PR=GRAPH.LAYOUT.ADJUSTED.DIFF (DIFF ENTRY1 ENTRY2)

  (COND ((NULL ENTRY1) DIFF)
	(T (LET ((MAX.DIFF (FLOOR  (/ (+ (SECOND ENTRY1) (SECOND ENTRY2)) 2))))
	     (COND ((> DIFF 0) (COND ((> MAX.DIFF 0) (MIN DIFF MAX.DIFF))
				     (T 0)))
		   (T (COND ((< MAX.DIFF 0) (MAX DIFF MAX.DIFF))
			    (T 0))))))))


(DEFUN PR=GRAPH.LAYOUT.NODE.DIFFS (NODE1 NODE2)

  ;;; Input:   two nodes
  ;;; Value:   space between both nodes.

  (DECLARE (TYPE PR*GRAPH.NODE NODE1 NODE2))
  
  (- (PR=OBJ.X-POS (PR=GRAPH.NODE.TEXT NODE2))
     (PR=OBJ.X-POS (PR=GRAPH.NODE.TEXT NODE1))
     (PR=OBJ.WIDTH (PR=GRAPH.NODE.TEXT NODE1))
     (* 3 (pr=actual.size))))


(DEFMACRO PR=GRAPH.NODE.INVISIBLE (NODE)

  ;;; Input:   a node
  ;;; Value:  T iff \verb$NODE$ is invisible.

  `(GETF (PR=OBJ.ATTRIBUTES (PR=GRAPH.NODE.TEXT ,NODE)) 'INVISIBLE))


(DEFUN PR=GRAPH.COLLECT (LEVELS ATTRIBUTES)

  ;;; Input:   an array of levels representing a graph
  ;;; Effect:  computes the y-position of each node and computes the final
  ;;;          printed representation of the graph
  ;;; Value:   the printed representation of the graph

  (DECLARE (TYPE (SIMPLE-ARRAY LIST 1) LEVELS))
  
  (LET ((SUM.WIDTH 0) (SUM.HEIGHT 0) (MIN.WIDTH 0) NODE.LIST (HEIGHT 0) LAST.ELEM)
    (DECLARE (TYPE FIXNUM SUM.WIDTH SUM.HEIGHT MIN.WIDTH HEIGHT) (TYPE LIST NODE.LIST))
    (DOTIMES (I (ARRAY-DIMENSION LEVELS 0))
      (SETQ NODE.LIST (AREF LEVELS I))
      (SETQ HEIGHT 0)
      (MAPC #'(LAMBDA (NODE)
		(DECLARE (TYPE PR*GRAPH.NODE NODE))
		(SETQ MIN.WIDTH (MIN MIN.WIDTH (PR=OBJ.X-POS (PR=GRAPH.NODE.TEXT NODE))))
		(SETF (PR=OBJ.Y-POS (PR=GRAPH.NODE.TEXT NODE)) SUM.HEIGHT)
		(SETQ HEIGHT (MAX HEIGHT (COND ((PR=OBJ.HEIGHT (PR=GRAPH.NODE.TEXT NODE)))
					       (T 0)))))
	    NODE.LIST)
      (MAPC #'(LAMBDA (NODE)
		(DECLARE (TYPE PR*GRAPH.NODE NODE))
		(COND ((EQL (PR=OBJ.HEIGHT (PR=GRAPH.NODE.TEXT NODE)) 0)
		       (SETF (PR=OBJ.HEIGHT (PR=GRAPH.NODE.TEXT NODE)) HEIGHT))))
	    NODE.LIST)
      (SETQ LAST.ELEM (PR=GRAPH.NODE.TEXT (CAR (LAST NODE.LIST))))
      (SETQ SUM.WIDTH (MAX SUM.WIDTH (+ (PR=OBJ.X-POS LAST.ELEM) (PR=OBJ.WIDTH LAST.ELEM))))
      (INCF SUM.HEIGHT (+ HEIGHT (FLOOR (* 2.5 (PR=ACTUAL.SIZE))))))
    (COND ((< MIN.WIDTH 0)
	   (SETQ MIN.WIDTH (ABS MIN.WIDTH))
	   (DOTIMES (I (ARRAY-DIMENSION LEVELS 0))
	     (MAPC #'(LAMBDA (NODE)
		       (INCF (PR=OBJ.X-POS (PR=GRAPH.NODE.TEXT NODE)) MIN.WIDTH))
		   (AREF LEVELS I)))
	   (SETF SUM.WIDTH (+ SUM.WIDTH MIN.WIDTH))))
    (MAKE-PR*OBJECT :CENTER (FLOOR (/ SUM.WIDTH 2))
		    :X-POS 0
		    :Y-POS 0
		    :WIDTH SUM.WIDTH
		    :HEIGHT SUM.HEIGHT
		    :TYPE 'GRAPH
		    :OBJECTS (LIST LEVELS)
		    :ATTRIBUTES ATTRIBUTES)))



;;;;;====================================================================================================
;;;;;
;;;;; Section VI
;;;;;
;;;;; Handling the description windows
;;;;;
;;;;;====================================================================================================


(defun pr-graphic.interact (window function &optional keystroke.handler)

  ;;; Input:   a window specification and an sexpression which can be evaluated to a print-object
  ;;; Effect:  activates window, and draws the evaluated function on the specified window. Also, it handles
  ;;;          user-inputs which can be either a left-mouse click specifying some mouse-sensitive parts
  ;;;          (which generate new graphics) or middle- and right-mouse-clicks specifying the vector
  ;;;          the graphic has to be moved inside the window.
  ;;;          the keystroke q exits the window.
  ;;; Value:   undefined.

  (win-io.cursor.wait window)
  (pr=print.graphic.stack function WINDOW keystroke.handler)
  (win-io.shadow WINDOW))


(defun pr-graphic.show (window function)

  ;;; Input:   a window specification and an sexpression which can be evaluated to a print-object
  ;;; Effect:  same as in \verb$PR-GRAPHIC.INTERACT$ with the exception that only left-mouse
  ;;;          clicks are accepted, middle- and right-mouse clicks are ignored
  ;;; Value:   undefined.

  (win-io.cursor.wait window)
  (pr=print.graphic.stack function WINDOW)
  (win-io.shadow window))


(defun pr=print.graphic.stack (object.desc window &optional keystroke.handler)
  
  (let (back object active.regions activity INPUT NEW.OBJECT type draw.picture same.picture? offset)
    (setq object (eval object.desc))
    (cond ((null object) (setq back 0))
	  ((numberp object) (setq back object))
	  (t (setq draw.picture t)))
    (setq offset (list 0 0))
    (WHILE (not back)
      (cond (draw.picture
	     (setq draw.picture nil)
	     (setq active.regions (pr=print.graphic object window active.regions 
						    same.picture? offset))))
      (setq input (PR=HANDLE.INPUT WINDOW))
      (setq offset (pr=canvas.offset window))
      (let ((pr*actual.object object))
	(COND ((eq (CAR INPUT) 'mouse)
	       (SETQ type (pr=mouse.convert.type (cdr INPUT)))
	       (cond ((SETQ NEW.OBJECT (PR=POSITION.IS.active TYPE (Third INPUT) (fourth INPUT) active.regions))
		      (LET ((PR*LOCAL.POS (FOURTH NEW.OBJECT)))
			(cond ((setq activity (getf (pr=obj.attributes (THIRD new.object)) type))
			       (cond ((member type '(:middle :right)) (PR=POSITION.HIGHLIGHT new.object window)))
			       (setq back (pr=eval.under.fct 
					   (cond ((member type '(:left :double.left))
						  (getf (pr=obj.attributes (THIRD new.object)) :environment)))
					   `(pr=print.graphic.stack (quote ,activity) (quote ,WINDOW) 
								    (quote ,keystroke.handler))))
			       (cond ((null back) 
				      (setq object (eval object.desc) draw.picture t))))				      
			      ((setq activity (getf (pr=obj.attributes (THIRD new.object)) :selection))
			       (cond ((eql type :left) (pr=print.select.item window NEW.OBJECT active.regions))
				     ((eql type :middle) (pr=print.toggle.item window NEW.OBJECT)))))))
		     (t (win-io.print.status window "Region is not mouse-sensitive"))))
	      ((eq (car input) 'redraw)
	       (setq active.regions (pr=print.graphic.redraw object window nil)))
	      ((eq (car input) 'scale)
	       (setq pr*scaling (pr=print.compute.scaling object (second input)))
	       (setq object (eval object.desc) draw.picture t back nil))
	      ((eq (car input) 'print)
	       (pr=print.picture object (second input) (third input) (fourth input)))
	      ((and keystroke.handler (eq (car INPUT) 'key))
	       (multiple-value-setq (back same.picture? new.object) (funcall keystroke.handler input))
	       (cond ((and same.picture? (neq same.picture? t))
		      (setq draw.picture t))
		     (t (setq back (pr=print.graphic.stack NEW.OBJECT WINDOW keystroke.handler))
			(cond ((null back) (setq object (eval object.desc) draw.picture t))))))
	      ((or (eq (car INPUT) 'OK) (and (eq (car INPUT) 'key) (eq (second input) #\q)))
	       (setq back 0))
	      ((or (eq (car INPUT) 'ABORT) (and (eq (car INPUT) 'key) (eq (second INPUT) #\a)))
	       (setq back 10000))
	      (t (win-io.print.status window "Input ignored")))))
    (cond ((zerop back) nil)
	  (t (1- back)))))



(defun pr=canvas.offset (window)

  (multiple-value-bind (x-offset y-offset) 
		       (win-io.get.offset window)
    (list x-offset y-offset)))


(DEFUN pr=mouse.convert.type (INPUT)

  ;;;     1 -> SHIFT, 2-> CAPSLOCK, 4 -> CONTROL, 8 -> META,  16 -> ALTGRAPH, 32 -> ALT.

  (LET ((CLICK (CAR INPUT)))
    (VALUES (COND ((EQL CLICK 1) :LEFT)
		  ((EQL CLICK 2) :MIDDLE)
		  ((EQL CLICK 3) :RIGHT)
		  ((EQL CLICK 4) :DOUBLE.LEFT)
		  ((EQL CLICK 5) :DOUBLE.MIDDLE)
		  ((EQL CLICK 6) :DOUBLE.RIGHT))
	    (COND ((EQL (FOURTH INPUT) 1) :SHIFT)
		  ((EQL (FOURTH INPUT) 4) :CONTROL)
		  ((EQL (FOURTH INPUT) 8) :META)))))
		  
  

(DEFUN PR=HANDLE.INPUT (WINDOW)

  (LET (INPUT)
    (win-io.cursor.normal window)
    (setq INPUT (win-io.any.tyi window))
    (win-io.cursor.wait window)
    (win-io.print.status window "")
    input))
		  

(DEFUN PR=POSITION.IS.ACTIVE (TYPE X-POS Y-POS ACTIVE.REGIONS)

  ;;; Input:  a point in a window, the specification of this window and a list of mouse-sensitive objects
  ;;; Effect: checks whether the given point is within some mouse-sensitive object
  ;;; Value:  the mouse-sensitive object in which the point is, NIL else.

  (DECLARE (TYPE FIXNUM X-POS Y-POS) (TYPE LIST ACTIVE.REGIONS))
  (LET ((ACTIVE.REG (FIND-IF #'(LAMBDA (REGION)
				 (AND (<= (CAR REGION) X-POS)
				      (<= (SECOND REGION) Y-POS)
				      (<= X-POS (+ (PR=OBJ.WIDTH (THIRD REGION)) (CAR REGION)))
				      (<= Y-POS (+ (PR=OBJ.HEIGHT (THIRD REGION)) (SECOND REGION)))
				      (cond ((GETF (PR=OBJ.ATTRIBUTES (THIRD REGION)) TYPE))
					    ((member type '(:left :middle))
					     (GETF (PR=OBJ.ATTRIBUTES (THIRD REGION)) :selection)))))
			     ACTIVE.REGIONS)))
    (COND (ACTIVE.REG (APPEND ACTIVE.REG (LIST (CONS (- X-POS (CAR ACTIVE.REG)) 
						     (- Y-POS (SECOND ACTIVE.REG)))))))))


(DEFUN pr=position.with.name (TYPE active.regions) 
  
  (LET ((region (FIND-IF #'(LAMBDA (REGION)
			     (EQ TYPE (GETF (PR=OBJ.ATTRIBUTES (THIRD REGION)) :PARTIAL)))
			 ACTIVE.REGIONS)))
    (values (CAR REGION) (SECOND REGION)
	    (remove-if #'(lambda (old.region)
			   (AND (<= (CAR REGION) (CAR OLD.REGION))
				(<= (SECOND REGION) (SECOND OLD.REGION))
				(<= (+ (PR=OBJ.WIDTH (THIRD old.REGION)) (CAR OLD.REGION))
				    (+ (PR=OBJ.WIDTH (THIRD REGION)) (CAR REGION)))
				(<= (+ (PR=OBJ.HEIGHT (THIRD OLD.REGION)) (SECOND OLD.REGION))
				    (+ (PR=OBJ.HEIGHT (THIRD REGION)) (SECOND REGION)))))
		       active.regions))))


(DEFUN PR=POSITION.HIGHLIGHT (object window)

  (pr=io.invert window (pr=obj.width (THIRD object)) (pr=obj.height (THIRD object))
		(CAR object) (SECOND object))
  (win-io.draw window))


(defun pr=object.selected.items (object)

  (cond (object
	 (let ((sub.objs (pr=obj.objects object)))
	   (nconc (case (pr=obj.type object) 
			(header (pr=object.selected.items (second sub.objs)))
			((sequel list.of.objects table closure page)
			 (mapcan #'(lambda (sub.obj) (pr=object.selected.items sub.obj)) sub.objs))
			((string bitmap) nil)
			(tree (nconc (pr=object.selected.items (car sub.objs))
			
				     (mapcan #'(lambda (sub.obj) (pr=object.selected.items sub.obj)) (third sub.objs))))
			(graph (let ((array (car sub.objs)) selections)
				 (dotimes (i (array-dimension array 0))
					  (setq selections (nconc (mapcan #'(lambda (sub.obj) 
									      (pr=object.selected.items 
									       (pr=graph.node.text sub.obj)))
									  (aref array i))
								  selections)))
				 selections)))
		  (cond ((getf (pr=obj.attributes object) :selected)
			 (list (getf (pr=obj.attributes object) :selection)))))))))
	

(defun pr=print.compute.scaling (object scale.advice)

  (cond ((numberp scale.advice) (/ scale.advice 100))
	((null scale.advice) 1.0)
	((consp scale.advice) (min (/ (car scale.advice) (pr=obj.width object))
				   (/ (second scale.advice) (pr=obj.height object))))))


(defun pr=print.toggle.item (window object)

  (win-io.invert window (pr=obj.width (THIRD object)) (pr=obj.height (THIRD object))
		 (CAR OBJECT) (SECOND object))
  (win-io.draw window)
  (setf (getf (pr=obj.attributes (THIRD object)) :selected)
	(not (getf (pr=obj.attributes (THIRD object)) :selected))))


(defun pr=print.select.item (window object active.regions)

  (mapc #'(lambda (item)
	    (cond ((getf (pr=obj.attributes (THIRD item)) :selected)
		   (pr=print.toggle.item window item))))		   
	active.regions)
  (setf (getf (pr=obj.attributes (THIRD object)) :selected) t)
  (win-io.invert window (pr=obj.width (THIRD object)) (pr=obj.height (THIRD object))
		 (CAR object) (SECOND object))
  (win-io.draw window))


(defun pr=print.graphic.redraw (object window &optional active.regions)

  (let (vis_x1 vis_x2 vis_y1 vis_y2 x.size y.size x-off y-off)
    (multiple-value-setq (vis_x1 vis_x2 vis_y1 vis_y2) (win-io.canvas.coordinates window))
    (multiple-value-setq (x.size y.size) (win-io.size window))
    (cond ((< (+ 40 (pr=obj.width object)) x.size)
	   (setq x-off (floor (/ (- x.size (pr=obj.width object)) 2))))
	  (t (setq x-off 20)))
    (cond ((< (+ 40 (pr=obj.height object)) y.size)
	   (setq y-off (floor (/ (- y.size (pr=obj.height object)) 2))))
	  (t (setq y-off 20)))
    (setq active.regions (pr-print.tree object window x-off y-off (list vis_x1 vis_x2 vis_y1 vis_y2) 
					active.regions))
    (mapc #'(lambda (obj)
	      (cond ((getf (pr=obj.attributes (third obj)) :selected)
		     (win-io.invert window (pr=obj.width (third obj)) (pr=obj.height (third obj))
				    (car obj) (second obj)))))
	  active.regions)
    (win-io.draw window)
    (win-io.actualize.scrollbars window)
    active.regions))


(defun pr=print.graphic (graphic window former.active.regions &optional part.index offset)

  ;;; Input:   a list of: a sexpression, an io-window, and two integers specifying the x- and y-offset.
  ;;; Effect:  draws the graphic specified by (car graphic.window.spec) onto the window relative to the
  ;;;          given offset.
  ;;; Value:   undefined.

  (let (active.regions (x-off 0) (y-off 0) 
	vis_x1 vis_x2 vis_y1 vis_y2 x.size y.size inc-x-off inc-y-off)
    (WIN-IO.EXPOSE WINDOW)
    (multiple-value-setq (x.size y.size) (win-io.size window))
    (cond ((< (+ 40 (pr=obj.width graphic)) x.size)
	   (setq x-off (floor (/ (- x.size (pr=obj.width graphic)) 2))))
	  (t (setq x-off 20)))
    (cond ((< (+ 40 (pr=obj.height graphic)) y.size)
	   (setq y-off (floor (/ (- y.size (pr=obj.height graphic)) 2))))
	  (t (setq y-off 20)))
    (cond (part.index
	   (multiple-value-setq (inc-x-off inc-y-off former.active.regions)
				(pr=position.with.name part.index former.active.regions))
	   (incf x-off inc-x-off)
	   (incf y-off inc-y-off))
	  (t (setq former.active.regions nil)
	     (WIN-IO.INITIALIZE.WINDOW window (max x.size (+ 40 (PR=OBJ.WIDTH GRAPHIC)))
				       (max y.size (+ 40 (PR=OBJ.HEIGHT GRAPHIC)))
				       (cond (offset (car offset)) (t 0))
				       (cond (offset (second offset)) (t 0)))))
    (multiple-value-setq (vis_x1 vis_x2 vis_y1 vis_y2) (win-io.canvas.coordinates window))
    (win-without.forced.output
     (setq active.regions (nconc former.active.regions
				 (pr-print.tree graphic window x-off y-off (list vis_x1 vis_x2 vis_y1 vis_y2))))
     (mapc #'(lambda (obj)
	       (cond ((getf (pr=obj.attributes (third obj)) :selected)
		       (win-io.invert window (pr=obj.width (third obj)) (pr=obj.height (third obj))
				      (car obj) (second obj)))))
	   active.regions))
    (WIN-IO.DRAW window)
    active.regions))


(defun pr=io.invert (window width height x y)

  (cond ((or (< width 50) (< height 50))
	 (win-io.invert window width height x y))
	(t (win-io.invert window 3 height x y)
	   (win-io.invert window 3 height (- (+ x width) 3) y)
	   (win-io.invert window (- width 6) 3 (+ x 3) y)
	   (win-io.invert window (- width 6) 3 (+ x 3) (- (+ height y) 3)))))


(defun pr=eval.under.fct (environ.fct apply.fct)

  (let ((pr*apply.fct apply.fct))
    (cond ((null environ.fct) (eval apply.fct))
	  (t (eval environ.fct)
	     (values pr*x pr*y)))))


(defun pr-apply ()
  ;;; Input: none
  ;;; Effect: evaluates the acutal apply function returning some coordinates

  (eval `(multiple-value-setq (pr*x pr*y) ,pr*apply.fct)))


(defmacro pr=with.attributes (attributes &rest body)

  `(let ((pr*actual.font (cond ((getf ,attributes :font)) (t pr*actual.font)))
	 (pr*actual.size (cond ((getf ,attributes :size)) (t pr*actual.size)))
	 (pr*actual.colour (cond ((getf ,attributes :colour)) (t pr*actual.colour)))
	 (pr*actual.sizemetric (PR=SIZE.NEW.METRIC (getf ,attributes :sizemetric))))
     ,@body))


(defmacro pr=with.active.attributes (window attributes active? &rest body)

  `(prog1 (let ((pr*actual.font (cond ((getf ,attributes :font)) (t pr*actual.font)))
		(pr*actual.size (cond ((getf ,attributes :size)) (t pr*actual.size)))
		(pr*actual.sizemetric (PR=SIZE.NEW.METRIC (getf ,attributes :sizemetric)))
		(pr*actual.colour (cond ((getf ,attributes :colour))
					(,active? "DarkBlue") 
					(t pr*actual.colour))))
	    (cond ((or (getf ,attributes :font) (getf ,attributes :size) (getf ,attributes :sizemetric))
		   (win-io.set.font ,window (cons pr*actual.font (pr=actual.size)))))
	    (cond ((or (getf ,attributes :colour) ,active?)
		   (win-io.set.colour ,window pr*actual.colour)))
	    ,@body)
     (cond ((or (getf ,attributes :font)
		(getf ,attributes :size)
		(getf ,attributes :sizemetric))
	    (win-io.set.font ,window (cons pr*actual.font (pr=actual.size)))))
     (cond ((or (getf ,attributes :colour) ,active?)
	    (win-io.set.colour ,window pr*actual.colour)))))


(defun pr=string.width (string)

  (let ((entry (gethash string pr*hash.table)))
    (cond ((getf (getf entry pr*actual.font) (pr=actual.size)))
	  (t (setq entry (win-io.string.width (cons pr*actual.font (pr=actual.size)) string)) 
	     (setf (getf (getf (gethash string pr*hash.table) pr*actual.font) (pr=actual.size)) entry)
	     entry))))


(defun pr=char.width (char)
  
  (let ((entry (gethash char pr*hash.table)))
    (cond ((getf (getf entry pr*actual.font) (pr=actual.size)))
	  (t (setq entry (win-io.string.width (cons pr*actual.font (pr=actual.size))
					      (make-string 1 :initial-element char)))
	     (setf (getf (getf (gethash char pr*hash.table) pr*actual.font) (pr=actual.size)) entry)
	     entry))))


(defun pr=actual.font.height ()
  
  (let (entry)
    (cond ((setq entry (getf (gethash pr*actual.font pr*hash.table) (pr=actual.size)))
	   (values-list entry))
	  (t (multiple-value-bind (ignore height ascend) (win-font.size pr*actual.font (pr=actual.size))
	       (setf (getf (gethash pr*actual.font pr*hash.table) (pr=actual.size)) (list height ascend))
	       (values height ascend))))))
  

(defun pr-selected.items ()

  (pr=object.selected.items pr*actual.object))

      

(DEFUN PR=OBJ.PRINT (OBJECT STREAM DEPTH)

  (declare (IGNORE DEPTH))
  (FORMAT STREAM "PR-~A-~D-~D-~D-~D" (PR=OBJ.TYPE OBJECT)
	  (PR=OBJ.X-POS OBJECT)
	  (PR=OBJ.Y-POS OBJECT)
	  (PR=OBJ.WIDTH OBJECT)
	  (PR=OBJ.HEIGHT OBJECT)))


(DEFUN PR=CLIP.TEST (P Q U1 U2)
  (DECLARE (TYPE RATIONAL P Q U1 U2))
  (LET ((RESULT T) R)
       (COND ((< P 0)
	      (COND ((> (SETQ R (/ Q P)) U2) (SETQ RESULT NIL))
		    ((> R U1) (SETQ U1 R))))
	     ((> P 0)
	      (COND ((< (SETQ R (/ Q P)) U1) (SETQ RESULT NIL))
		    ((< R U2) (SETQ U2 R))))
	     ((< Q 0) (SETQ RESULT NIL)))
       (VALUES RESULT U1 U2)))


(DEFUN PR=CLIP.LINE (WINDOW VIS FROM_X FROM_Y TO_X TO_Y &OPTIONAL (LINE.WIDTH -1))

  (DECLARE (TYPE FIXNUM FROM_X FROM_Y TO_X TO_Y LINE.WIDTH))
  (LET ((U1 0) (U2 1) (DX (- TO_X FROM_X)) DY (NEW_FROM_X FROM_X) 
	(NEW_FROM_Y FROM_Y) (NEW_TO_X TO_X) (NEW_TO_Y TO_Y)
	result (VIS_X1 (CAR VIS)) (VIS_X2 (SECOND VIS)) (VIS_Y1 (THIRD VIS)) (VIS_Y2 (FOURTH VIS)))
    (DECLARE (TYPE FIXNUM VIS_X1 VIS_X2 VIS_Y1 VIS_Y2))
    (COND ((EQL -1 LINE.WIDTH) (SETQ LINE.WIDTH (MAX 1 (* PR*SCALING)))))
    (SETQ FROM_X (FLOOR FROM_X) FROM_Y (FLOOR FROM_Y) TO_X (FLOOR TO_X) TO_Y (FLOOR TO_Y))
    (COND ((AND (MULTIPLE-VALUE-SETQ (RESULT U1 U2) (PR=CLIP.TEST (- DX) (- NEW_FROM_X VIS_X1) U1 U2))
		(MULTIPLE-VALUE-SETQ (RESULT U1 U2) (PR=CLIP.TEST DX (- VIS_X2 NEW_FROM_X) U1 U2))
		(SETQ DY (- NEW_TO_Y NEW_FROM_Y))
		(MULTIPLE-VALUE-SETQ (RESULT U1 U2) (PR=CLIP.TEST (- DY) (- NEW_FROM_Y VIS_Y1) U1 U2))
		(MULTIPLE-VALUE-SETQ (RESULT U1 U2) (PR=CLIP.TEST DY (- VIS_Y2 NEW_FROM_Y) U1 U2)))
	   (COND ((> U1 0) (SETQ NEW_FROM_X (+ NEW_FROM_X (* U1 DX)) NEW_FROM_Y (+ NEW_FROM_Y (* U1 DY))))
		 ((< U2 1) (SETQ NEW_TO_X (+ NEW_FROM_X (* U2 DX)) NEW_TO_Y (+ NEW_FROM_Y (* U2 DY)))))
	   (WIN-IO.DRAW.LINE WINDOW (FLOOR NEW_FROM_X) (FLOOR NEW_FROM_Y)
			     (FLOOR NEW_TO_X) (FLOOR NEW_TO_Y) LINE.WIDTH)))))


(defun pr=print.picture (tree filename landscape? fit?)

  (let ((postscripter (ps-open.stream filename :orientation (cond (landscape? :landscape) (t :portrait))
				      :number.of.pages (cond (fit? :one) (t :multiple))
				      :destination (cond (fit? :document.inclusion) (t :laser.printing)))))
    (win-io.draw.rectangle postscripter (pr=obj.width tree) (+ 55 (pr=obj.height tree)) 0 0 2)
    (win-io.draw.line postscripter 0 30 (pr=obj.width tree) 30 2)
    (PR-PRINT.Tree tree postscripter 0 35 (list 0 (pr=obj.width tree) 0 (+ 35 (pr=obj.height tree))) nil)
    (ps-close.stream)))


(defun pr-ps.page (trees filename)

  (let ((postscripter (ps-open.stream filename :orientation :portrait :number.of.pages :one 
				      :destination :laser.printing))
	tree)
    (setq tree (pr-parse.page trees postscripter 1))
    (describe tree)
    (pr-print.tree tree postscripter 0 0 (list 0 (pr=obj.width tree) 0 (pr=obj.height tree)) nil)
    (ps-close.stream)))



(DEFUN PR-SET.LINELENGTH (LL)
  
  ;;; edited : 19. Dec 1987
  ;;; Input  : wished linelength
  ;;; Effect : PR*LINELENGTH is set to wished linelength
  ;;; Value  : Input

  (DECLARE (TYPE FIXNUM LL))
  (SETQ PR*LINELENGTH LL))


(DEFMACRO PR-WITH.LINELENGTH (LL &REST BODY)

  ;;; Input:   wished linelength and a list of sexpressions
  ;;; Effect:  evaluates \verb$BODY$ with linelength \verb$LL$
  ;;; Value:   value of \verb$BODY$

  `(LET ((PR*LINELENGTH ,LL))
     (PROGN . ,BODY)))


(DEFUN PR-PRINT.LITLIST (LITERALS &OPTIONAL VARIABLES (JUNCTION "OR"))
  
  ;;; edited : 21. dec 1987
  ;;; Input  : a list of literals, a list of variables and a junctor
  ;;; Effect : the literals are parsed and transduced into intermediate representation
  ;;; Value  : list of strings of the print representation
  
  (LET (LITLIST)
    (SETQ PR*NEWLINE NIL)
    (SETQ PR*SORTS NIL)
    (SETQ PR*INHIBIT.RENAMING NIL)
    (COND (LITERALS
	   (MAPC #'PR=NAME.VARIABLE VARIABLES)
	   (PR=TO.STRING (CONS (PR=PRINT.LENGTH 
				 (SETQ LITLIST
				       (PR=SEPERATE.LIST (MAPCAR #'PR=PARSE.LITERAL LITERALS) JUNCTION)))
			       LITLIST)))
	  (T (LIST "False")))))


(DEFUN PR-PRINT.NEGATED.FORMULAS (FORMULAS &OPTIONAL VARIABLES)
  
  ;;; edited : 21. dec 1987
  ;;; Input  : a list of literals and a list of variables
  ;;; Effect : the literals are parsed and transduced into intermediate representation
  ;;; Value  : list of strings of the print representation
  
  (LET (LITLIST)
    (SETQ PR*NEWLINE NIL)
    (SETQ PR*SORTS NIL)
    (SETQ PR*INHIBIT.RENAMING NIL)
    (COND (FORMULAS
	   (MAPC #'PR=NAME.VARIABLE VARIABLES)
	   (PR=TO.STRING (CONS (PR=PRINT.LENGTH 
				 (SETQ LITLIST
				       (PR=SEPERATE.LIST (MAPCAR #'(LAMBDA (LIT) 
								     (COND ((DA-LITERAL.IS LIT) (PR=PARSE.LITERAL LIT T))
									   ((EQ 'not (da-gterm.symbol lit)) 
									    (pr=parse.formula (car (da-gterm.termlist lit))))
									   (T (PR=PARSE.FORMULA (DA-FORMULA.NEGATE LIT)))))
								 FORMULAS) '"AND")))
			       LITLIST)))
	  (T (LIST "True.")))))


(DEFUN PR-PRINT.NEGATED.LITLIST (LITERALS &OPTIONAL VARIABLES)
  
  ;;; edited : 21. dec 1987
  ;;; Input  : a list of literals and a list of variables
  ;;; Effect : the literals are parsed and transduced into intermediate representation
  ;;; Value  : list of strings of the print representation
  
  (LET (LITLIST)
    (SETQ PR*NEWLINE NIL)
    (SETQ PR*SORTS NIL)
    (SETQ PR*INHIBIT.RENAMING NIL)
    (COND (LITERALS
	   (MAPC #'PR=NAME.VARIABLE VARIABLES)
	   (PR=TO.STRING (CONS (PR=PRINT.LENGTH 
				 (SETQ LITLIST
				       (PR=SEPERATE.LIST (MAPCAR #'(LAMBDA (LIT) (PR=PARSE.LITERAL LIT T))
								 LITERALS) '"AND")))
			       LITLIST)))
	  (T (LIST "True.")))))


(DEFUN PR-PRINT.FORMULA (FORMULA)
  
  ;;; edited : 26. Oct 1987 
  ;;; Input  : a formula to be printed in prefix representation
  ;;; Effect : \verb$FORMULA$ is parsed and transduced into print representation
  ;;; Value  : list of strings of the print representation
  
  (SETQ PR*NEWLINE NIL)
  (SETQ PR*SORTS NIL)
  (SETQ PR*INHIBIT.RENAMING NIL)
  (PR=TO.STRING (PR=PARSE.FORMULA FORMULA)))


(defun pr-print.gterm (gterm)

  ;;; Input  : a gterm to be printed in prefix representation
  ;;; Effect : \verb$GTERM$ is parsed and transduced into print representation
  ;;; Value  : list of strings of the print representation
  
  (pr-print.formula gterm))



(DEFUN PR-PRINT.MODIFIER (MODIFIER)
  
  ;;; edited : 25. Oct 1989
  ;;; Input  : a modifier to be printed
  ;;; Effect : \verb$MODIFIER$ is parsed and transduced into print representation
  ;;; Value  : list of strings of the print representation
  
  (SETQ PR*NEWLINE NIL)
  (SETQ PR*SORTS NIL)
  (SETQ PR*INHIBIT.RENAMING NIL)
  (PR=TO.STRING (PR=PARSE.MODIFIER MODIFIER)))


(DEFUN PR-PRINT.TERM (FORMULA)
  
;;; edited : 26. Oct 1987 
;;; Input  : a term to be printed in prefix representation
;;; Effect : \verb$TERM$ is parsed and transduced into print representation
;;; Value  : list of strings of the print representation
  
  (SETQ PR*NEWLINE NIL)
  (SETQ PR*SORTS NIL)
  (SETQ PR*INHIBIT.RENAMING NIL)
  (PR=TO.STRING (PR=PARSE.TERM FORMULA)))


(DEFUN PR-PRINT.TERMLIST (TERMLIST)
  
;;; edited : 26. Oct 1987 
;;; Input  : a termlist to be printed in prefix representation
;;; Effect : \verb$TERMLIST$ is parsed and transduced into print representation
;;; Value  : list of strings of the print representation
  
  (SETQ PR*NEWLINE NIL)
  (SETQ PR*SORTS NIL)
  (SETQ PR*INHIBIT.RENAMING NIL)
  (PR=TO.STRING (PR=PARSE.TERMLIST TERMLIST)))


(DEFUN PR=PARSE.FORMULA (FORMULA)
  
  ;;; edited : 26. Oct 1987 
  ;;; Input  : formula in prefix representation
  ;;; Effect : formula is transduced in an intermediate representation
  ;;; Value  : intermediate representation of formula 
  
  (LET (TRIPEL TRIPEL1 TRIPEL2 FORLIS VARIABLES QUANTOR)
    (cond ((DA-LITERAL.IS FORMULA)
	   (PR=PARSE.LITERAL FORMULA))
	  ((DA-TERM.IS FORMULA) (PR=PARSE.TERM FORMULA))
	  (t 
	   (CASE (DA-GTERM.SYMBOL FORMULA)
	     ((ALL EX) 
	      (SETQ FORLIS (DA-FORMULA.QUANTIFICATION.OPEN (DA-GTERM.SYMBOL FORMULA) FORMULA))
	      (SETQ QUANTOR (STRING (DA-GTERM.SYMBOL FORMULA)))
	      (SETQ VARIABLES (PR=PARSE.VARIABLE.LIST (FIRST FORLIS) 'SORT! QUANTOR))
	      (SETQ TRIPEL (PR=PARSE.FORMULA (REST FORLIS)))
	      (CONS (+ 1 (LENGTH QUANTOR) (FIRST VARIABLES) (FIRST TRIPEL))
		    (CONS QUANTOR (CONS VARIABLES (LIST TRIPEL)))))
	     ((AND OR)
	      (SETQ FORLIS (PR=SEPERATE.LIST (MAPCAR #'PR=PARSE.FORMULA
						     (DA-GTERM.TERMLIST FORMULA))
					     (STRING (DA-GTERM.SYMBOL FORMULA))))
	      (CONS (+ 2 (PR=PRINT.LENGTH FORLIS)) 
		    (CONS "(" (NCONC FORLIS (LIST ")")))))
	     ((IMPL EQV)
	      (SETQ TRIPEL1 (PR=PARSE.FORMULA (CAR (DA-GTERM.TERMLIST FORMULA))))
	      (SETQ TRIPEL2 (PR=PARSE.FORMULA (SECOND (DA-GTERM.TERMLIST FORMULA))))
	      (LIST (+ 3 (FIRST TRIPEL1) (LENGTH (STRING (DA-GTERM.SYMBOL FORMULA))) (FIRST TRIPEL2))
		    "("
		    TRIPEL1
		    (STRING (DA-GTERM.SYMBOL FORMULA))
		    TRIPEL2
		    ")"))
	     ((NOT)
	      (SETQ TRIPEL (PR=PARSE.FORMULA (CAR (DA-GTERM.TERMLIST FORMULA))))
	      (LIST (+ 4 (FIRST TRIPEL))
		    "NOT"
		    TRIPEL))
	     (OTHERWISE (PR=PARSE.TERM FORMULA)))))))


(DEFUN PR=PARSE.LITERAL (FORMULA &OPTIONAL NEGATE?)
  
  ;;; edited : 30. Oct 1987
  ;;; Input  : literal in prefix representation
  ;;; Effect : literal is transduced into intermediate representation
  ;;; Value  : intermediate representation of literal
  
  (LET (TRIPEL (COUNT 0))
    (DECLARE (TYPE FIXNUM COUNT))
    (COND
	  ((DA-PREDICATE.IS.EQUALITY (DA-LITERAL.SYMBOL FORMULA))
	   (SETQ TRIPEL (LIST (PR=PARSE.TERM (FIRST (DA-LITERAL.TERMLIST FORMULA)))
			      "="
			      (PR=PARSE.TERM (SECOND (DA-LITERAL.TERMLIST FORMULA)))))
	   (SETQ COUNT (+ 2 (FIRST (FIRST TRIPEL)) (FIRST (THIRD TRIPEL)))))


	  (T (IF (DA-LITERAL.TERMLIST FORMULA)
		 (PROGN (SETQ TRIPEL (LIST (DA-SYMBOL.PNAME (DA-LITERAL.SYMBOL FORMULA))
					   "("
					   (PR=PARSE.TERMLIST (DA-LITERAL.TERMLIST FORMULA))
					   ")"))
			(SETQ COUNT (+ 3 (LENGTH (DA-SYMBOL.PNAME (DA-LITERAL.SYMBOL FORMULA)))
				       (FIRST (THIRD TRIPEL)))))
		 (PROGN (SETQ TRIPEL (LIST (DA-SYMBOL.PNAME (DA-LITERAL.SYMBOL FORMULA))))
			(SETQ COUNT (1+ (LENGTH (DA-SYMBOL.PNAME (DA-LITERAL.SYMBOL FORMULA)))))))))
    (COND ((COND (NEGATE? (DA-SIGN.IS.POSITIVE (DA-LITERAL.SIGN FORMULA)))
		 (T (DA-SIGN.IS.NEGATIVE (DA-LITERAL.SIGN FORMULA))))
	   (SETQ TRIPEL (LIST (+ COUNT 4) "NOT" (CONS COUNT TRIPEL))))
	  (T (CONS COUNT TRIPEL)))))


(DEFUN PR=PARSE.TERMLIST (FORMULA)
  
  ;;; edited : 30. Oct 1987
  ;;; Input  : termlist in prefix representation
  ;;; Effect : termlist is transduced into intermediate representation
  ;;; Value  : intermediate representation of termlist

  (LET (TERMS)
    (SETQ TERMS (cond ((null (cdr formula)) (list (pr=parse.term (car formula))))
		      (T (nconc (MAPCAR #'(LAMBDA (TERM) (PR=PARSE.TERM TERM T))
					(BUTLAST FORMULA))
				(list (pr=parse.term (car (last formula))))))))
    (CONS (PR=PRINT.LENGTH TERMS) TERMS)))



(DEFUN PR=PARSE.TERM (FORMULA &OPTIONAL COMMA)
  
  ;;; edited : 26. Oct 1987
  ;;; Input  : term in prefix representation
  ;;; Effect : term is transduced into intermediate representation
  ;;; Value  : intermediate representation of term 
  
  (LET (TERMS)
    (COND ((DA-TERM.TERMLIST FORMULA)
	   (SETQ TERMS (PR=PARSE.TERMLIST (DA-TERM.TERMLIST FORMULA)))
	   (NCONC (LIST (+ 4 (LENGTH (DA-SYMBOL.PNAME (DA-TERM.SYMBOL FORMULA)))
			   (car TERMS)
			   (COND (COMMA 2) (t 0)))
			(DA-SYMBOL.PNAME (DA-TERM.SYMBOL FORMULA))
			"(")
		  (CDR TERMS)
		  (LIST ")")
		  (COND (COMMA (LIST ",")))))
	  (T
	   (NCONC (LIST (+ (COND (COMMA 3) (t 1))
			   (LENGTH (DA-SYMBOL.PNAME (da-term.symbol FORMULA))))
			(DA-SYMBOL.PNAME (da-term.symbol FORMULA)))
		  (COND (COMMA (LIST ","))))))))


(DEFUN PR=PARSE.MODIFIER (MODIFIER)

  ;;; edited : 25. Oct 1989
  ;;; Input  : a modifier
  ;;; Effect : \verb$MODIFIER$ is transduced into intermediate representation.
  ;;; Value  : intermediate representation of the modifier.

  (LET ((IMPL (DA-LITERAL.IS (DA-MODIFIER.INPUT MODIFIER)))
	PP)
    (SETQ PP (NCONC (COND ((DA-MODIFIER.CONDITION MODIFIER)
			   (NCONC1 (PR=SEPERATE.LIST (MAPCAR #'(LAMBDA (LIT) (PR=PARSE.gterm LIT T))
							    (DA-MODIFIER.CONDITION MODIFIER))
						    '"AND")
				  (LIST 4 "->"))))
		    (COND (IMPL (LIST (PR=PARSE.gterm (DA-MODIFIER.INPUT MODIFIER) T)
				      (LIST 2 "->")
				      (PR=PARSE.FORMULA (DA-MODIFIER.VALUE MODIFIER))))
			  (T (LIST (PR=PARSE.TERM (DA-MODIFIER.INPUT MODIFIER))
				   (LIST 1 "=")
				   (PR=PARSE.TERM (DA-MODIFIER.VALUE MODIFIER)))))))
    (CONS (PR=PRINT.LENGTH PP) PP)))


(DEFUN PR=PARSE.GTERM (FORMULA &OPTIONAL NEGATE?)
  
;;; edited : 30. Oct 1987
;;; Input  : a gterm
;;; Effect : \verb$GTERM$ is transduced into intermediate representation
;;; Value  : intermediate representation of the gterm
  
  (LET (TRIPEL)
    (COND
     	  ((DA-LITERAL.IS FORMULA) (PR=PARSE.LITERAL FORMULA NEGATE?))
	  ((NOT NEGATE?) (PR=PARSE.FORMULA FORMULA))
	  ((AND (EQ (DA-GTERM.SYMBOL FORMULA) 'AND) NEGATE?)
	   (SETQ TRIPEL (PR=SEPERATE.LIST (MAPCAR #'(LAMBDA (GTERM) (PR=PARSE.GTERM GTERM NEGATE?))
						  (DA-GTERM.TERMLIST FORMULA))
					  (STRING 'OR)))
	   (CONS (+ 2 (PR=PRINT.LENGTH TRIPEL)) 
		 (CONS "(" (NCONC TRIPEL (LIST ")")))))
	  ((AND (EQ (DA-GTERM.SYMBOL FORMULA) 'OR) NEGATE?)
	   (SETQ TRIPEL (PR=SEPERATE.LIST (MAPCAR #'(LAMBDA (GTERM) (PR=PARSE.GTERM GTERM NEGATE?))
						  (DA-GTERM.TERMLIST FORMULA))
					  (STRING 'AND)))
	   (CONS (+ 2 (PR=PRINT.LENGTH TRIPEL)) 
		 (CONS "(" (NCONC TRIPEL (LIST ")")))))
	  ((AND (EQ (DA-GTERM.SYMBOL FORMULA) 'NOT) NEGATE?)
	   (SETQ TRIPEL (MAPCAR #'(LAMBDA (GTERM) (PR=PARSE.GTERM GTERM))
						  (DA-GTERM.TERMLIST FORMULA)))
	   (CONS (+ 2 (PR=PRINT.LENGTH TRIPEL)) 
		 (CONS "(" (NCONC TRIPEL (LIST ")"))))))))


(DEFUN PR=PARSE.VARIABLE.LIST (VARLIST SORT? &OPTIONAL (QUANTOR "EX"))
  
;;; edited : nov 1987
;;; Input  : list of variables
;;; Effect : The variables in \verb$VARLIST$ are named, such that variables of the same sort receive the same prefix
;;;          (leading letters of the name of their sort) and a running count when renamed.
;;;          If \verb$SORT?$ is not NIL, the variables are sorted according to their sort, else the order remains. 
;;; Value  : list containing renamed variables and their sort identifiers.
  
  (LET ((COUNT 0) ACTSORT OLDSORT OUT)
    (DECLARE (TYPE FIXNUM COUNT))
    (MAPC #'(LAMBDA (ARG)
	      (SETQ ACTSORT (DA-VARIABLE.SORT ARG))
	      (COND ((EQUAL COUNT 0)
		     (SETQ OLDSORT ACTSORT)
		     (SETQ COUNT (LENGTH (PR=NAME.VARIABLE ARG)))
		     (SETQ OUT (LIST (DA-VARIABLE.PNAME ARG))))
		    ((EQUAL ACTSORT OLDSORT)
		     (INCF COUNT (1+ (LENGTH (PR=NAME.VARIABLE ARG))))
		     (NCONC OUT (LIST "," (DA-VARIABLE.PNAME ARG))))
		    (sort?
		     (INCF COUNT (+ 5 (LENGTH (DA-SORT.PNAME OLDSORT)) (LENGTH (PR=NAME.VARIABLE ARG))))
		     (NCONC OUT (LIST ":" 
				      (DA-SORT.PNAME OLDSORT)
				      QUANTOR
				      (DA-VARIABLE.PNAME ARG)))
		     (SETQ OLDSORT ACTSORT))
		    (T
		     (INCF COUNT (+ 2 (LENGTH (DA-SORT.PNAME OLDSORT)) (LENGTH (PR=NAME.VARIABLE ARG))))
		     (NCONC OUT (LIST ":" 
				      (DA-SORT.PNAME OLDSORT)
				      (DA-VARIABLE.PNAME ARG)))
		     (SETQ OLDSORT ACTSORT))))
	  (IF SORT?
	      (SORT (COPY-LIST VARLIST) #'STRING-LESSP :KEY #'PR=GET.SORT)
	      VARLIST))
    (NCONC OUT (LIST ":" (DA-SORT.PNAME OLDSORT)))
    (CONS (+ 2 COUNT (LENGTH (DA-SORT.PNAME OLDSORT))) OUT)))



(DEFUN PR=PRINT.LENGTH (X)
  
;;; edited : nov 1987
;;; Input  : partial list of the intermediate representation
;;; Effect : see value
;;; Value  : length of the print representation of the list is added to the front of the list.
  
  (LET ((RESULT 0))
    (DECLARE (TYPE FIXNUM RESULT))
    (MAPC #'(LAMBDA (ELEM)
	      (INCF RESULT (COND ((OR (EQUAL ELEM ",") (EQUAL ELEM ":") (EQUAL ELEM "(") (EQUAL ELEM ")"))
				  1)
				 ((STRINGP ELEM)
				  (1+ (LENGTH ELEM)))
				 (T (FIRST ELEM)))))
	  X)
    RESULT))



(DEFUN PR=SEPERATE.LIST (LIST ITEM)
  
;;; edited : nov 1987
;;; Input  : a list
;;; Effect : see value
;;; Value  : between each two elements of the list ITEM is inserted.
  
  (CONS (DA-PNAME (CAR LIST))
	(MAPCAN #'(LAMBDA (ELEM)
		    (LIST ITEM (DA-PNAME ELEM)))
		(CDR LIST))))



(DEFUN PR=NAME.VARIABLE (VAR)

  (DA-VARIABLE.PNAME VAR))



(DEFUN PR=GET.SORT (VAR)
  
;;; edited : 12. Nov 1987
;;; Input  : variable in internal representation
;;; Effect : see value
;;; Value  : pname of the sort of var

  (DA-SORT.PNAME (DA-VARIABLE.SORT VAR)))



(DEFUN PR=TO.STRING (FORMULA)
  
;;; edited : 28. Oct 1987
;;; Input  : intermediate representation of an object
;;; Effect : see value
;;; Value  : print representation of object
  
  (SETQ PR*OUTPUT (LIST (MAKE-STRING PR*LINELENGTH :INITIAL-ELEMENT #\SPACE)))
  (PR=PRINT.FORMULA FORMULA 0) 
  (SETF (FIRST PR*OUTPUT) (STRING-RIGHT-TRIM '(#\SPACE) (FIRST PR*OUTPUT)))
  (NREVERSE PR*OUTPUT))


(DEFUN PR=PRINT.FORMULA (FORMULA START)
  
;;; edited : 28. Oct 1987
;;; Input  : - intermediate representation of part of an object
;;;          - column, where output should start
;;; Effect :
;;; Value  : position, up to which current line is filled

  (DECLARE (TYPE FIXNUM START))
  (LET ((POS START) INDENT)
    (DECLARE (TYPE FIXNUM POS))
    (COND ((< (+ START (FIRST FORMULA)) PR*LINELENGTH)
	   (MAPC #'(LAMBDA (ARG)
		     (SETQ POS (IF (STRINGP ARG)
				   (PR=WRITE.ARGUMENT ARG POS START)
				   (PR=PRINT.FORMULA ARG POS))))
		 (REST FORMULA)))
	  (T (MAPC #'(LAMBDA (ARG) 
		       (IF (PR=EMPTY.LINE)
			   (SETQ POS START))
		       (COND ((STRINGP ARG)
			      (SETQ POS (PR=WRITE.ARGUMENT ARG POS START))
			      (IF (EQUAL ARG "(")
				  (INCF START 1)))
			     (T (IF (NOT INDENT)
				    (SETQ INDENT POS))
				(IF PR*NEWLINE
				    (PROGN (PR=NEWLINE)
					   (SETQ POS INDENT)))
				(SETQ POS (PR=PRINT.FORMULA ARG POS))
				(IF (NOT (PR=EMPTY.LINE))
				    (SETQ PR*NEWLINE T)))))
		   (REST FORMULA))))
    POS))


(DEFUN PR=WRITE.ARGUMENT (ARG POS START)
  
  ;;; edited : 2. Nov 1987
  ;;; Input  : - string to be printed
  ;;;          - position where string is to be inserted into current line
  ;;;          - number of leading blanks in every following line
  ;;; Effect : 
  ;;; Value  : position, up to which current line is filled

  (DECLARE (TYPE STRING ARG) (TYPE FIXNUM POS START))
  (COND ((AND PR*NEWLINE (NOT (MEMBER ARG '(")" ":" ",") :TEST #'EQUAL)))
	 (PR=NEWLINE)
	 (SETQ POS START))
	((> (+ POS (LENGTH ARG)) PR*LINELENGTH)
	 (PR=NEWLINE)
	 (IF (MEMBER ARG '(")" "," ":") :TEST #'EQUAL)
	     (SETQ POS 1)
	     (SETQ POS 0))))
  (COND ((EQUAL ARG ")")
	 (SETF (AREF (FIRST PR*OUTPUT) (1- POS)) #\))
	 (1+ POS))
	((OR (EQUAL ARG ":") )                     ; (EQUAL ARG ",")
	 (SETF (AREF (FIRST PR*OUTPUT) (1- POS)) (IF (EQUAL ARG ",") #\, #\:))
	 POS)
	((EQUAL ARG ",")
	 (SETF (AREF (FIRST PR*OUTPUT) (1- POS))  #\,)
	 (1+ POS))
	((EQUAL ARG "(") 
	 (SETF (AREF (FIRST PR*OUTPUT) POS) #\()
	 (1+ POS))
	((< (+ 1 POS (LENGTH ARG)) PR*LINELENGTH)
	 (REPLACE (FIRST PR*OUTPUT) ARG :START1 POS)
	 (+ 1 POS (LENGTH ARG)))
	(T (PR=NEWLINE (MAX (+ 3 START (LENGTH ARG)) PR*LINELENGTH))
	   (REPLACE (FIRST PR*OUTPUT) ARG :START1 START)
	   (+ 1 START (LENGTH ARG)))))



(DEFUN PR=NEWLINE (&OPTIONAL LENGTH) 
  
;;; edited : nov 1987
;;; Input  : none
;;; Effect : a fresh line is added to the front of PR*OUTPUT, blanks at the end of the last line
  ;          are stripped off.
;;; Value  : PR*OUTPUT with one element more
  
  (COND ((NOT (PR=EMPTY.LINE))
	 (SETF (FIRST PR*OUTPUT) (STRING-RIGHT-TRIM '(#\SPACE) (FIRST PR*OUTPUT))) 
	 (SETQ PR*OUTPUT (CONS (MAKE-STRING (COND (LENGTH) (T PR*LINELENGTH))
					    :INITIAL-ELEMENT #\SPACE) PR*OUTPUT)))
	(LENGTH (SETQ PR*OUTPUT (CONS (MAKE-STRING LENGTH :INITIAL-ELEMENT #\SPACE) (CDR PR*OUTPUT))))
	(T NIL))
  (SETQ PR*NEWLINE NIL))


(DEFUN PR=EMPTY.LINE ()
  
;;; edited : jan 1988
;;; Input  : none
;;; Effect : see value
;;; Value  : T, if the first line in PR*OUTPUT contains only blanks
;;;          NIL else.
  
  (NULL (POSITION-IF-NOT #'(LAMBDA (X) (EQUAL X #\SPACE)) (FIRST PR*OUTPUT))))



(DEFUN PR=ACTUAL.DISTANCE ()

  (MAX 1 (FLOOR (* PR*DISTANCE PR*SCALING))))


(DEFUN PR=ACTUAL.SIZE ()

  (PR=SIZE.COMPUTE PR*ACTUAL.SIZE PR*ACTUAL.SIZEMETRIC PR*SCALING))


(DEFUN PR=SIZE.COMPUTE (SIZE SIZEMETRIC scaling)

  (SETQ SIZE (CASE SIZE (SS 8) (S 10) ((D TOP) 12) (B 14) (BB 18)))
  (PR=SIZE.SCALE (* scaling 
		    (CASE SIZEMETRIC
			  ((Top D) SIZE)
			  (B (+ SIZE 2))
			  (BB (+ SIZE 5))
			  (S (MAX 1 (- SIZE 2)))
			  (SS (MAX 1 (- SIZE 4)))
			  (OTHERWISE SIZE)))))
  

(DEFUN PR=SIZE.NEW.METRIC (TYPE)

  (cond ((null type) 'D)
	(t (CASE PR*ACTUAL.SIZEMETRIC
		 (D TYPE)
		 (S (CASE TYPE (D 'S) (B 'S) (BB 'S) (S 'SS) (SS 'SS)))
		 (SS 'SS)
		 (BB 'BB)
		 (B (case type (D 'B) (B 'BB) (S 'S) (SS 'S)))
		 (OTHERWISE 'D)))))


(DEFUN PR=SIZE.SCALE (SIZE)

  ;;; Input:  a size internally calculated
  ;;; Value:  the next (possibly smaller) really existing size 

  (cond ((< size 5) 2)
	((< size 8) 5)
	((< size 10) 8)
	((< size 12) 10)
	((< size 14) 12)
	((< size 18) 14)
	((< size 23) 18)
	(t 24)))



