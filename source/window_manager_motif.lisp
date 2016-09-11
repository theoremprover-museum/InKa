(in-package :inka)


(defstruct (win*window (:conc-name win=window.))
  
 (command.pipe    0  :TYPE FIXNUM)
 (data.pipe       0  :TYPE FIXNUM)
 (answer.pipe     0  :TYPE FIXNUM)
 type
 hardcopy
 colours
 font
 )

(defvar win*max.buffer 100)

(PROCLAIM '(TYPE FIXNUM win*max.buffer))

(defvar win*buffers (make-array (list 10 (1+ win*max.buffer))))

(defvar win*cursors (make-array '(10) :element-type 'fixnum :initial-element 0))

(defvar win*ends (make-array '(10) :element-type 'fixnum :initial-element 0))


(defvar win*stream.process nil)


(defvar win*active nil)

(defvar win*forced.output.disabled nil)

(defvar win*stream nil)

(defvar win*error.stream nil)


(defvar ps*bitmaps nil)


(defvar win*window.all (mapcar #'(lambda (type)
				   (make-win*window :type type))
			       '(description_1 description_2 description_3 proof main)))


(PROCLAIM '(TYPE (SIMPLE-ARRAY FIXNUM 1) win*cursors win*ends))

(PROCLAIM '(TYPE (SIMPLE-ARRAY * 2) win*buffers))

(PROCLAIM '(TYPE LIST win*window.all))

(PROCLAIM '(TYPE STREAM win*stream win*error.stream))

(PROCLAIM '(TYPE (OR  NIL T) win*active))


(defun win-reset (&optional type)

  ;;; Input:   a boolean
  ;;; Effect:  Initializes the IO of the \verb$INKA$-system, i.e. it creates a C-process which guides
  ;;;          the windows and a lisp-process which communicates with it.
  ;;;          The C-process is always called with at least one argument: the path of the idm directory,
  ;;;          if no other argument is supplied the interface is for pure INKA, 
  ;;;          any other second argument, although it is highly recommended
  ;;;          to use the string ``KIV'', leads to the interface in cooperation with KIV
  ;;; Value:   undefined.

  (let ((directory (append (pathname-directory *inka-pathname*) (list "idm"))))
    (ps-reset)
    (win=windows.create)
    (setq win*stream (pro-run.foreign.process (namestring (make-pathname :directory directory :name "dialog"))
					      :stream :stream nil nil
					      (nconc (list (namestring (make-pathname :directory directory)))
						     (case type (INKA nil) (KIV (list "KIV")) 
							   ))))
    (setq win*stream.process (pro-process.create :name "IO-Listener" :function #'win=handle.input.stream))))


(defun win-delete ()

  ;;; Effect:  closes the pipe to the C-process.
  ;;; Value:   undefined.

  (close win*stream))


(defun win-hardcopy (window &optional file)

  ;;; Input:   a window and a boolean
  ;;; Effect:  enables the hardcopy facility on \verb$WINDOW$. Each output to \verb$WINDOW$
  ;;;          is recorded into the \verb$FILE$.
  ;;; Value:   undefined.

  (setf (win=window.hardcopy window) file))


(defun win=windows.create ()

  ;;; Effect:  createes the internal datastructures to maintain the communication
  ;;;          with the C-process:
  ;;;          \begin{itemize}
  ;;;          \item the answer pipes obtain the channel-numbers 0 - 4
  ;;;          \item the data pipes obtain the channel-numbers 5 - 9
  ;;;          \item the command pipes obtain the channel-numbers 10 - 14
  ;;;          \end{description}
  ;;; Value:   undefined.

  (let ((no -1))
    (declare (type fixnum no))
    (mapc #'(lambda (window)
	      (declare (type win*window window))
	      (setf (win=window.answer.pipe window) (incf no))
	      (setf (win=window.colours window) (list "Black")))	  
	  win*window.all)
    (mapc #'(lambda (window)
	      (declare (type win*window window))
	      (setf (win=window.data.pipe window) (incf no)))
	  win*window.all)
    (mapc #'(lambda (window)
	      (declare (type win*window window))
	      (setf (win=window.command.pipe window) (incf no)))
	  win*window.all)))


(defmacro win-without.forced.output (&rest body)

  `(let ((win*forced.output.disabled t))
    (progn ,@body)))


(defun win=handle.input.stream ()

  ;;; Effect:  reads from the pipe and puts this input into the specified
  ;;;          internal buffer. In case one of these buffers are full the
  ;;;          process is stopped until the buffer is able to accept more
  ;;;          input
  ;;; Value:   undefined
  ;;; Note:    this is an infinite loop. There is no return from this function!

  (let* ((*package* (find-package 'inka)) pipe char new.entry (pipe.no 0))
    (declare (type fixnum pipe.no))
    (sleep 1)
    (catch 'win*io.abort
      (loop
	 (setq pipe (read win*stream nil 'win*io.fail))
	 (cond ((numberp pipe) (setq pipe.no pipe)))
	 (cond ((eq pipe 'win*io.fail) (throw 'win*io.abort 'win*io.fail))
	       ((and (numberp pipe) (< pipe.no 10))
		(cond ((< pipe.no 5) (setq char (win=handle.read)))   ; answer pipe
		      (t (setq char (read-char win*stream nil 'win*io.fail))        ; data pipe
			 (cond ((eq char #\ESC)
				(setq char (win=handle.read))))))
		(cond ((eq char 'win*io.fail)
		       (throw 'win*io.abort 'win*io.fail)))
		(setf (aref win*buffers pipe.no (aref win*ends pipe.no)) char)
		(setq new.entry (cond ((eql (aref win*ends pipe.no) win*max.buffer) 0)
				      (t (1+ (aref win*ends pipe.no)))))
		(setf (aref win*ends pipe.no) new.entry)
		(pro-process.wait "Pipe is full"
				  #'(lambda ()
				      (and (not (eql (1+ (aref win*ends pipe.no)) (aref win*cursors pipe.no)))
					   (not (and (eql (1+ (aref win*ends pipe.no)) win*max.buffer)
						     (eql (aref win*cursors pipe.no) 0))))))))))
    (pro-process.interrupt (edt-main.process) 'edt-error.occured)))


(defun win=handle.read ()

  (let (items)
    (declare (type list items))
    (cond ((eq #\( (peek-char nil win*stream))
	   (read-char win*stream nil 'win*io.fail)
	   (while (and (listen win*stream) (neq #\) (peek-char nil win*stream)))
	     (push (read win*stream nil 'win*io.fail) items))
	   (read-char win*stream nil 'win*io.fail)
	   (reverse items))
	  (t (read win*stream nil 'win*io.fail)))))


;;;; graphic procedures


(defun win-io.draw.bitmap (window width height x-pos y-pos bitmap.file)

  ;;; input:  a window of type \verb$WIN=WINDOW$, the width, height and position of 
  ;;;         the bitmap 
  ;;; effect: draws the specified bitmap on window.
  ;;; value:  none.

  (declare (type fixnum width height x-pos y-pos) 
	   (type (or win*window ps*postscript.handler) window))
  (cond ((eq (type-of window) 'ps*postscript.handler)
	 (ps=draw.bitmap window width height x-pos y-pos bitmap.file))
	(t (setq width (win=bitmap.scale bitmap.file width))
	   (pro-without.scheduling
	    (format win*stream "~D icon ~D ~D ~A" 
		    (win=window.command.pipe window) x-pos y-pos 
		    (format nil "~A_~D.xpm" bitmap.file width))
	    (princ #\NULL win*stream)
	    (princ #\SOH win*stream))
	   (cond ((not win*forced.output.disabled) (force-output win*stream))))))


(defun win-io.draw.rectangle (window width height x-pos y-pos &optional (line.width 1) colour)
    
  ;;; edited: 17.07.89
  ;;; input:  a window of type \verb$WIN=WINDOW$, the width, height and position of the rectangle (in pixel).
  ;;; effect: draws the specified rectangle on window.
  ;;; value:  none.

  (declare (type fixnum width height x-pos y-pos line.width) 
	   (type (or win*window ps*postscript.handler) window))
  (cond ((eq (type-of window) 'ps*postscript.handler)
	 (ps=draw.rectangle window x-pos (+ y-pos height) (+ x-pos width) y-pos
			    :line.thickness (abs line.width) 
			    :ink (cond (colour) (t (ps=psh.current.color window)))
			    :filled (not (null colour)))
	 (cond (colour (ps=draw.rectangle window x-pos (+ y-pos height) (+ x-pos width) y-pos
			    :line.thickness (abs line.width) :ink (ps=psh.current.color window) :filled nil))))
	(t (cond ((null colour) (setq colour "")))
	   (pro-without.scheduling
	    (format win*stream "~D rectangle ~D ~D ~D ~D ~D ~A" 
		    (win=window.command.pipe window) width height x-pos y-pos line.width (car (win=window.colours window)))
	    (princ #\NULL win*stream)
	    (format win*stream "~A" colour)
	    (princ #\NULL win*stream)
	    (princ #\SOH win*stream))
	   (cond ((not win*forced.output.disabled) (force-output win*stream))))))


(defun win-io.invert (window width height x-pos y-pos)
    
  ;;; edited: 17.07.89
  ;;; input:  a window of type \verb$WIN=WINDOW$, the width, height and position of the rectangle (in pixel).
  ;;; effect: draws the invertion of the specified rectangle on window.
  ;;; value:  none.

  (declare (type fixnum width height x-pos y-pos) 
	   (type (or win*window ps*postscript.handler) window))
  (pro-without.scheduling
   (format win*stream "~D invert ~D ~D ~D ~D " (win=window.command.pipe window) width height x-pos y-pos)
   (princ #\SOH win*stream))
  (cond ((not win*forced.output.disabled) (force-output win*stream))))


(defun win-io.draw.circle (window radius x-pos y-pos &optional (line.width 1) colour)
  
  ;;; edited: 17.07.89
  ;;; input:  a window of type \verb$WIN=WINDOW$, the radius and the position of the circle in pixel.
  ;;; effect: draws the specified circle on the window.
  ;;; value:  none.

  (declare (type fixnum radius x-pos y-pos) 
	   (type (or win*window ps*postscript.handler) window))
  (cond ((eq (type-of window) 'ps*postscript.handler)
	 (ps=draw.circle window x-pos y-pos radius :line.thickness line.width 
			 :ink (cond (colour) (t (ps=psh.current.color window)))
			 :filled (not (null colour)))
	 (cond (colour (ps=draw.circle window x-pos y-pos radius :line.thickness line.width 
				       :ink (ps=psh.current.color window) :filled nil))))
	(t (cond ((null colour) (setq colour "")))
	   (pro-without.scheduling
	    (format win*stream "~D circle ~D ~D ~D ~D ~A" (win=window.command.pipe window)
		    radius x-pos y-pos line.width (car (win=window.colours window)))
	    (princ #\NULL win*stream)
	    (format win*stream "~A" colour)
	    (princ #\NULL win*stream)
	    (princ #\SOH win*stream))
	   (cond ((not win*forced.output.disabled) (force-output win*stream))))))


(defun win-io.draw.oval (window x-pos y-pos width height &optional (line.width 1) colour)
  
  ;;; edited: 17.07.89
  ;;; input:  a window of type \verb$WIN=WINDOW$, the upper left position, the width, the height,
  ;;;         and the line width of the oval in pixel.
  ;;; effect: draws the specified oval on the window.
  ;;; value:  none.

  (declare (type fixnum width height x-pos y-pos) 
	   (type (or win*window ps*postscript.handler) window))
  (cond ((eq (type-of window) 'ps*postscript.handler)
	 (let ((x.radius (floor (/ width 2))) (y.radius (floor (/ height 2))))
	   (ps=draw.ellipse window (+ x-pos x.radius)
			    (+ y-pos y.radius) x.radius y.radius :line.thickness line.width 
			    :ink (cond (colour) (t (ps=psh.current.color window)))
			    :filled (not (null colour)))
	   (cond (colour (ps=draw.ellipse window (+ x-pos x.radius)
					  (+ y-pos y.radius) x.radius y.radius
					  :line.thickness line.width 
					  :ink (ps=psh.current.color window) :filled nil)))))
	(t (cond ((null colour) (setq colour "")))
	   (pro-without.scheduling
	    (format win*stream "~D oval ~D ~D ~D ~D ~D ~A" (win=window.command.pipe window) 
		    x-pos y-pos width height line.width (car (win=window.colours window)))
	    (princ #\NULL win*stream)
	    (format win*stream "~A" colour)
	    (princ #\NULL win*stream)
	    (princ #\SOH win*stream))
	   (cond ((not win*forced.output.disabled) (force-output win*stream))))))


(defun win-io.draw.line (window from-x from-y to-x to-y &optional (line.width 1))
  
  ;;; edited: 17.07.89
  ;;; input:  a window of tyep \verb$WIN=WINDOW$, the start and end position of the line in pixel.
  ;;; effect: draws the specified line on the window.
  ;;; value:  none.

  (declare (type fixnum from-x from-y to-x to-y line.width) 
	   (type (or win*window ps*postscript.handler) window))
  (cond ((eq (type-of window) 'ps*postscript.handler)
	 (ps=draw.line window from-x from-y to-x to-y :line.thickness line.width
		       :ink (ps=psh.current.color window)))
	(t (pro-without.scheduling
	    (format win*stream "~D line ~D ~D ~D ~D ~D ~A" (win=window.command.pipe window)
		    from-x from-y to-x to-y line.width
		    (car (win=window.colours window)))
	    (princ #\NULL win*stream)
	    (princ #\SOH win*stream))
	   (cond ((not win*forced.output.disabled) (force-output win*stream))))))


(defun win-io.draw.string (window x-pos y-pos string)

  ;;; Input:  a window of type \verb$WIN=WINDOW$, the position of the left/upper point in pixel
  ;;;         and a string
  ;;; Effect: plots the string at the given position
  ;;; Value:  none

  (declare (type fixnum x-pos y-pos) (type string string) 
	   (type (or win*window ps*postscript.handler) window))
  (cond ((eq (type-of window) 'ps*postscript.handler)
	 (ps=draw.text window string x-pos y-pos :align.y :top
		       :ink (ps=psh.current.color window)
		       :text.style (ps=psh.current.font window)))
	(t (pro-without.scheduling
	    (format win*stream "~D string ~D ~D ~A" (win=window.command.pipe window) x-pos y-pos
		    (car (win=window.colours window)))
	    (princ #\null win*stream)
	    (princ (win=determine.font (win=window.font window)) win*stream)
	    (princ #\null win*stream)
	    (princ string win*stream)
	    (princ #\null win*stream)
	    (princ #\SOH win*stream))
	   (cond ((not win*forced.output.disabled) (force-output win*stream))))))

(defun win=determine.font (font.size)

  (let (font size)
    (setq font (case (car font.size)
		     (bold "-adobe-helvetica-bold-r")
		     (roman "-adobe-helvetica-medium-r")
		     (italic "-adobe-helvetica-medium-o")
		     (symbol "-adobe-symbol-*-*")
		     (otherwise "-adobe-courier-medium-r")))
    (setq size (floor (* (cdr font.size) 10)))
    (format nil "~A-*-*-*-~D-*-*-*-*-*-*" font size)))



(defun win-io.size (window)

  ;;; Input:  a window of type \verb$WIN=WINDOW$
  ;;; Value:  return a multiple value, specifying the size of the window in pixel

  (declare (type (or win*window ps*postscript.handler) window))
  (cond ((eq (type-of window) 'ps*postscript.handler)
	 (values (if (equal (ps=psh.orientation window) :landscape)
		     (- (second (ps=psh.output.device.original.boundaries window))
			(fourth (ps=psh.output.device.original.boundaries window)))
		   (- (third (ps=psh.output.device.original.boundaries window))
		      (first (ps=psh.output.device.original.boundaries window))))
		 (if (equal (ps=psh.orientation window) :landscape)
		     (- (first (ps=psh.output.device.original.boundaries window))
			(third (ps=psh.output.device.original.boundaries window)))
		   (- (second (ps=psh.output.device.original.boundaries window))
		      (fourth (ps=psh.output.device.original.boundaries window))))))
	(t (pro-without.scheduling
	    (format win*stream "~D window.size " (win=window.command.pipe window))
	    (princ #\SOH win*stream))
	   (force-output win*stream)
	   (values-list (win=io.any.tyi (win=window.answer.pipe window))))))


(defun win-io.canvas.coordinates (window)

  ;;; Input:  a window of type \verb$WIN=WINDOW$
  ;;; Value:  return a multiple value, specifying the size of the window in pixel

  (declare (type win*window window))
  (pro-without.scheduling
   (format win*stream "~D canvas.coordinates " (win=window.command.pipe window))
   (princ #\SOH win*stream))
  (force-output win*stream)
  (values-list (win=io.any.tyi (win=window.answer.pipe window))))

(defun win-io.get.offset (window)

  ;;; Input:  a window of type \verb$WIN=WINDOW$
  ;;; Value:  return a multiple value, specifying the offset of the respective canvas

  (declare (type win*window window))
  (pro-without.scheduling
   (format win*stream "~D offset " (win=window.command.pipe window))
   (princ #\SOH win*stream))
  (force-output win*stream)
  (values-list (win=io.any.tyi (win=window.answer.pipe window))))

(defun win-io.window.id (window)

  ;;; Input:  a window of type \verb$WIN=WINDOW$
  ;;; Value:  the X-Identification number of the correspondent X-window

  (declare (type win*window window))
  (pro-without.scheduling
   (format win*stream "~D id " (win=window.command.pipe window))
   (princ #\SOH win*stream))
  (force-output win*stream)
  (car (win=io.any.tyi (win=window.answer.pipe window))))


(defun win-font.size (font size)

  ;;; Input:  a font description by \verb$FONT$ and \verb$SIZE$.
  ;;; Value:  a multiple-value width and height of a character of this font.
  ;;; Note:   this function is only useful for fixed-width fonts

  (declare (type atom font) (type fixnum size))
  (let* ((window (win-window 'main)) result)
    (declare (type win*window window))
    (cond (win*active (pro-process.wait "Requesting" #'(lambda () (not win*active)))))
    (unwind-protect (progn (setq win*active t)
			   (pro-without.scheduling
			    (format win*stream "~D font.size ~A" (win=window.command.pipe window) 
				    (win=determine.font (cons font size)))
			    (princ #\null win*stream)
			    (princ #\SOH win*stream))
			   (force-output win*stream)
			   (setq result (win=io.any.tyi (win=window.answer.pipe window))))
      (setq win*active nil))
    (values-list result)))


(defun win-bitmap.size (bitmap)

  ;;; Input:  a window of type \verb$WIN=WINDOW$ and the name of an bitmap
  ;;; Value:  return a multiple value, specifying the size of the bitmap in pixel

  (let* ((window (win-window 'main)) result)
    (declare (type win*window window))
    (cond (win*active
	   (pro-process.wait "Requesting" #'(lambda () (not win*active)))))
    (unwind-protect (progn (setq win*active t)
			   (pro-without.scheduling
			    (format win*stream "~D icon.size ~A_100.xpm" (win=window.command.pipe window)
				    bitmap)
			    (princ #\NULL win*stream)
			    (princ #\SOH win*stream))
			   (force-output win*stream)
			   (setq result (win=io.any.tyi (win=window.answer.pipe window))))
      (setq win*active nil))
    (values-list result)))


(defun win-io.string.width (font string)

  ;;; Input:  a window of type \verb$WIN=WINDOW$
  ;;; Value:  returns the length of the string in the given font 

  (declare (type cons font) (type string string))
  (let* ((window (win-window 'main)))
    (declare (type win*window window))
    (cond (win*active (pro-process.wait "Requesting" #'(lambda () (not win*active)))))
    (unwind-protect (progn (setq win*active t)
			   (pro-without.scheduling
			    (format win*stream "~D string.size ~A" (win=window.command.pipe window) 
				    (win=determine.font font))
			    (princ #\null win*stream)
			    (princ string win*stream)
			    (princ #\null win*stream)
			    (princ #\SOH win*stream))
			   (force-output win*stream)
			   (car (win=io.any.tyi (win=window.answer.pipe window))))
      (setq win*active nil))))


(defun win-io.shadow (window)

  ;;; Input:   a window of type \verb$WIN=WINDOW$
  ;;; Effect:  hides the specified window
  ;;; Value:   undefined

  (declare (type win*window window))
  (pro-without.scheduling
   (format win*stream "~D invisible " (win=window.command.pipe window))
   (princ #\SOH win*stream))
  (force-output win*stream))


(defun win-io.expose (window)

  ;;; Input:   a window of type \verb$WIN=WINDOW$
  ;;; Effect:  exposes the specified window
  ;;; Value:   undefined

  (declare (type win*window window))
  (pro-without.scheduling
   (format win*stream "~D visible " (win=window.command.pipe window))
   (princ #\SOH win*stream))
  (force-output win*stream))


(defun WIN-WINDOW.WINDOWS.EXPOSE ()

  ;;; Effect:  exposes the main \verb$INKA$-windows: the menu- and proof-window
  ;;; Value:   undefined

  (win-io.expose (win-window 'main)))


(defun WIN-WINDOW.WINDOWS.SHADOW ()
  
  ;;; Effect:  hides the main \verb$INKA$-windows: the menu- and proof-window
  ;;; Value:   undefined
  
  (win-io.shadow (win-window 'main)))


(defun win-io.clear (window)
  
  ;;; edited: 17.07.89
  ;;; input:  a window of type \verb$WIN=WINDOW$
  ;;; effect: clears the viewport and the input stream of \verb$WINDOW$, sets the cursor position to top left.
  ;;; value:  none.

  (declare (type win*window window))
  (pro-without.scheduling
   (format win*stream "~D clear " (win=window.command.pipe window))
   (princ #\SOH win*stream))
  (force-output win*stream))


(defun win-io.clear.input (window)
   
  ;;; edited: 17.07.89
  ;;; input:  a window of type \verb$WIN=WINDOW$
  ;;; effect: clears the input-stream of the \verb$WINDOW$
  ;;; value:  none.

  (declare (type win*window window))
  (setf (aref win*cursors (win=window.data.pipe window))
	(aref win*ends (win=window.data.pipe window))))


(DEFUN WIN-IO.CURSOR.WAIT (WINDOW)

  ;;; Input:  a window of type \verb$WIN=WINDOW$
  ;;; Effect: switches the form of the cursor inside \verb$WINDOW$ to a clock.
  ;;; Value:  undefined

  (declare (type win*window window))
  (pro-without.scheduling
   (format win*stream "~D wait.cursor " (win=window.command.pipe window))
   (princ #\SOH win*stream))
  (force-output win*stream))


(DEFUN WIN-IO.CURSOR.NORMAL (WINDOW)
  
  ;;; Input:  a window of type \verb$WIN=WINDOW$
  ;;; Effect: switches the form of the cursor inside \verb$WINDOW$ to an arrow.
  ;;; Value:  undefined

  (declare (type win*window window))
  (pro-without.scheduling
   (format win*stream "~D normal.cursor " (win=window.command.pipe window))
   (princ #\SOH win*stream))
  (force-output win*stream))


(defun win-io.print (string window &optional no.hc)

  ;;; Input:   a string,  a window of type \verb$WIN=WINDOW$ and a boolean
  ;;; Effect:  prints \verb$STRING$ at the actual cursor-position of \verb$WINDOW$
  ;;;          and performs a newline command. In case \verb$NO.HC$ is set no
  ;;;          hardcopy is done.
  ;;; Value:   undefined

  (declare (type (or stream win*window) window))
  (cond ((eq (type-of window) 'win*window)
	 (cond ((> (length string) 1000)
		(let ((cursor 0))
		  (declare (type fixnum cursor))
		  (while (< cursor (length string))
		    (win-io.princ (subseq string cursor (min (length string) (+ cursor 1000)))
				  window t)
		    (incf cursor 1000))
		  (win-io.print "" window)))	       
	       (t (pro-without.scheduling
		   (princ (win=window.command.pipe window) win*stream)
		   (princ " print " win*stream)
		   (princ string win*stream)
		   (princ #\newline win*stream)
		   (princ #\null win*stream)
		   (princ #\SOH win*stream))
		  (cond ((not win*forced.output.disabled) (force-output win*stream)))))
	 (cond ((and (null no.hc) (win=window.hardcopy window))
		(print string (win=window.hardcopy window)))))
	(t (print string window))))


(defun win-io.princ (string window &optional no.hc)

  ;;; Input:   a string,  a window of type \verb$WIN=WINDOW$ and a boolean
  ;;; Effect:  prints \verb$STRING$ at the actual cursor-position of \verb$WINDOW$
  ;;;          but performs no (!) newline command. In case \verb$NO.HC$ is set no
  ;;;          hardcopy is done.
  ;;; Value:   undefined

  (declare (type (or stream win*window) window))
  (cond ((eq (type-of window) 'win*window)
	 (cond ((> (length string) 1000)
		(let ((cursor 0))
		  (declare (type fixnum cursor))
		  (while (< cursor (length string))
		    (win-io.princ (subseq string cursor (min (length string) (+ cursor 1000)))
				  window t)
		    (incf cursor 1000))))
	       (t (pro-without.scheduling
		   (princ (win=window.command.pipe window) win*stream)
		   (princ " print " win*stream)
		   (princ string win*stream)
		   (princ #\null win*stream)
		   (princ #\SOH win*stream))
		  (cond ((not win*forced.output.disabled) (force-output win*stream)))))
	 (cond ((and (null no.hc) (win=window.hardcopy window))
		(princ string (win=window.hardcopy window)))))
	(t (princ string window))))

(defmacro win-io.format.string (window format.string)

  ;;; Input:   a window of type \verb$WIN=WINDOW$, a format-directive and the arguments of this format-directive.
  ;;; Effect:  prints the value of evaluating \verb$FORMAT$ to \verb$STRING$ with arguments \verb$ARGS$ at the
  ;;;          actual cursor-position of \verb$WINDOW$
  ;;; Value:   undefined

  `(progn (cond ((eq (type-of ,window) 'win*window)
		 (win-io.princ ,format.string ,window))  
		(t (format ,window "~A" ,format.string)))))

(defmacro win-io.format (window format.string &rest args)

  ;;; Input:   a window of type \verb$WIN=WINDOW$, a format-directive and the arguments of this format-directive.
  ;;; Effect:  prints the value of evaluating \verb$FORMAT$ to \verb$STRING$ with arguments \verb$ARGS$ at the
  ;;;          actual cursor-position of \verb$WINDOW$
  ;;; Value:   undefined

  `(progn (cond ((eq (type-of ,window) 'win*window)
		 (win-io.princ (format nil ,format.string ,@args) ,window))  ; ',' vor window eingefuegt
		(t (format ,window ,format.string ,@args)))))


(defun win-io.terpri (window)

  ;;; Input:   a window of type \verb$WIN=WINDOW$
  ;;; Effect:  performs a newline command on \verb$WINDOW$
  ;;; Value:   undefined

  (declare (type (or stream win*window) window))
  (cond ((eq (type-of window) 'win*window) (win-io.print "" window))
	(t (terpri window))))


(defun win-io.print.top (window string)

  ;;; Input:   a window of type \verb$WIN=WINDOW$ and a string
  ;;; Effect:  prints string into the top-line of \verb$WINDOW$.
  ;;; Value:   undefined.

  (declare (type (or win*window ps*postscript.handler) window))
  (cond ((eq (type-of window) 'ps*postscript.handler)
	 (win-io.set.font window (cons 'bold 14))
	 (win-io.draw.string window 5 5 string))
	(t (pro-without.scheduling
	    (princ (win=window.command.pipe window) win*stream)
	    (princ " top " win*stream)
	    (princ string win*stream)
	    (princ #\null win*stream)
	    (princ #\SOH win*stream))
	   (force-output win*stream))))


(defun win-io.print.status (window string)

  ;;; Input:   a window of type \verb$WIN=WINDOW$ and a string
  ;;; Effect:  prints string into the status-line of \verb$WINDOW$.
  ;;; Value:   undefined.

  (declare (type win*window window))
  (pro-without.scheduling
   (princ (win=window.command.pipe window) win*stream)
   (princ " status " win*stream)
   (princ string win*stream)
   (princ #\null win*stream)
   (princ #\SOH win*stream))
  (force-output win*stream))


(DEFUN WIN-IO.INITIALIZE.WINDOW (WINDOW WIDTH HEIGHT X-OFFSET Y-OFFSET)

  ;;; Input:   a window of type \verb$WIN=WINDOW$ and four integers
  ;;; Effect:  exposes \verb$WINDOW$ with the specified size.
  ;;; Value:   undefined

  (declare (type win*window window) (type fixnum WIDTH HEIGHT X-OFFSET Y-OFFSET))
  (PRO-WITHOUT.SCHEDULING
   (FORMAT WIN*STREAM "~D initialize ~D ~D ~D ~D "
	   (WIN=WINDOW.COMMAND.PIPE WINDOW) WIDTH HEIGHT X-OFFSET Y-OFFSET)
   (princ #\SOH win*stream))
  (FORCE-OUTPUT WIN*STREAM))


(defun win-io.actualize.scrollbars (window)
  
  ;;; Input:   a window of type \verb$WIN=WINDOW$
  ;;; Effect:  the scrollbars for the above window are actualized
  ;;; Value:   undefined.

  (declare (type win*window window))
  (pro-without.scheduling
   (format win*stream "~D scrollbars " (win=window.command.pipe window))
   (princ #\SOH win*stream))
  (force-output win*stream))


(defun win-io.draw (window)
  
  ;;; Input:   a window of type \verb$WIN=WINDOW$
  ;;; Effect:  the picture drawn before this command (and yet invisible) is exposed to the X-window.
  ;;; Value:   undefined.

  (declare (type win*window window))
  (pro-without.scheduling
   (format win*stream "~D draw " (win=window.command.pipe window))
   (princ #\SOH win*stream))
  (force-output win*stream))


(defun win-io.any.tyi (window)
  
  ;;; edited: 17.07.89
  ;;; input:  a window of type \verb$WIN=WINDOW$
  ;;; effect: waits for any input (keyboard or mouse)
  ;;; value:  a character of '(button-no x-pos y-pos)

  (declare (type win*window window))
  (win=io.any.tyi (win=window.data.pipe window)))


(defmacro win-io.listen (window)
  
  ;;; edited: 17.07.89
  ;;; input:  a window of type \verb$WIN=WINDOW$
  ;;; effect: waits for any input (keyboard or mouse)
  ;;; value:  a character of '(button-no x-pos y-pos)
  
  (not (eql (aref win*cursors (win=window.data.pipe window))
	    (aref win*ends (win=window.data.pipe window)))))


(defun win-io.set.font (window font)
 
  ;;; Input:   a window of type \verb$WIN=WINDOW$ and a font-description
  ;;; Effect:  sets the actual font of \verb$WINDOW$ to the
  ;;;          specified font-description.
  ;;; Value:   undefined.

  (declare (type (or win*window ps*postscript.handler) window) (type cons font))
  (cond ((eq (type-of window) 'ps*postscript.handler)
	 (ps=check.font window font))
	(t (setf (win=window.font window) font))))


(defmacro win-io.with.colour (window colour &rest body)

  ;;; Input:   a window of type \verb$WIN=WINDOW$ and a colour (see win-io.set.colour)
  ;;; Effect:  changes the default colour to \verb$COLOUR$ executes \verb$BODY$ and
  ;;;          returns to the old default colour.
  ;;; Value:   undefined

  `(progn (cond (,colour (push ,colour (win=window.colours ,window))
			 (win-io.set.colour ,window ,colour)))
	  (progn ,@body)
	  (cond (,colour (pop (win=window.colours ,window))
			 (win-io.set.colour ,window (car (win=window.colours ,window)))))))


(defun win-io.set.colour (window colour)
 
  ;;; Input:   a window of type \verb$WIN=WINDOW$ and a font-description
  ;;; Effect:  sets the actual colour of \verb$WINDOW$ to the
  ;;;          specified colour, it is one of the strings: Black, White, DarkBlue, LightBlue, DargGreen,
  ;;;          LightGreen, DarkRed, LightRed, DarkYellow, LightYellow, DarkPink, LightPink, 
  ;;;          DarkGrey, LightGrey
  ;;; Value:   undefined.

  (declare (type (or win*window ps*postscript.handler) window))
  (cond ((eq (type-of window) 'ps*postscript.handler)
	 (ps=check.grayscale window colour))
	(t  (setf (win=window.colours window)
		  (cons colour (cdr (win=window.colours window)))))))


(defun win-window (type)

  ;;; Input:   a description of a window (e.g. main, proof etc.)
  ;;; Value:   the corresponding \verb$WIN=WINDOW$

  (find-if #'(lambda (window)
	       (eq (win=window.type window) type))
	   win*window.all))


(defun win-stop (window)
  
  ;;; Input:   a window of type \verb$WIN=WINDOW$
  ;;; Effect:  kills the lisp-process listening to the C-process and sends the C-process
  ;;;          a signal to kill itself.
  ;;; Value:   absolutly undefined.

  (declare (type win*window window))
  (pro-process.kill win*stream.process)
  (pro-without.scheduling
   (format win*stream "~D stop " (win=window.command.pipe window))
   (princ #\SOH win*stream))
  (force-output win*stream)
  (finish-output win*stream))


(defun win-mn.popup (window entry.list)

  ;;; Input:   a window of type \verb$WIN=WINDOW$ and a tree like list with
  ;;;          dotted pairs for the menu tree together with the result of the
  ;;;          chosen menu, for example '(("A" . 1) ("B" . 2) ("C" . 3))
  ;;;          as a simple popup menu without cascading submenus
  ;;;          or '(("A" . 1) (("B" ("D" . 2) (("E" ("G" . 3))) ("F" . 5))) ("C" . 7))
  ;;;          for a more sophisticated popup menu with several cascading submenus
  ;;;          Note: only for leafs of the menu tree a return value needs to be specified,
  ;;;                since the dialog manager guarantees that only bottom menus will
  ;;                 be selected.
  ;;; Effect:  exposes a pop-up menu with items build from string of each item of entry.list.
  ;;; Value:   a list of \verb$VALUE$-slots of the selected items.
  ;;; Note:    since only a single menu can be chosen, the list of results should
  ;;;          be changed to a single result 

  (declare (type win*window window))
  (pro-without.scheduling
   (format win*stream "~D popup ~D " (win=window.command.pipe window) (length entry.list))
   (princ (win=popup.print.entry.list entry.list) win*stream)
   (princ #\SOH win*stream))
  (force-output win*stream)
  (win=popup.get.result (car (cdr (car (win=io.any.tyi (win=window.answer.pipe window)))))
			entry.list))

(defun win=popup.get.result (string entry.list)
  (some #'(lambda (entry)
	    (cond ((listp (car entry))
		   (win=popup.get.result string (cdr (car entry))))
		  ((string-equal string (car entry))
		   (list (cdr entry)))))
	entry.list))

(defun win=popup.print.entry.list (entry.list)
  (let ((result ""))
    (mapc #'(lambda (entry)
	    (cond ((listp (car entry))
		   (setq result 
			 (format nil "~A~D ~A~C~A" result (length (cdr (car entry))) (car (car entry))
				 #\null
				 (win=popup.print.entry.list (cdr (car entry))))))
		  (t (setq result (format nil "~A0 ~A~C" result (car entry)
					  #\null)))))
	  entry.list)
    result))


(defun win-mn.choose (window entry.list &optional (message "Choose from:"))

  ;;; Input:   a window of type \verb$WIN=WINDOW$, a boolean flag and a list of dotted pairs (string . value)
  ;;; Effect:  exposes a pop-up menu with items build from string of each item of entry.list.
  ;;; Value:   a list of \verb$VALUE$-slots of the selected items.

  (declare (type win*window window))
  (pro-without.scheduling
   (format win*stream "~D choose ~D ~A" (win=window.command.pipe window) (length entry.list)
	   message)
   (princ #\null win*stream)
   (mapc #'(lambda (entry)
	     (princ (car entry) win*stream)
	     (princ #\null win*stream))
	 entry.list)
   (princ #\SOH win*stream))
  (force-output win*stream)
  (mapcar #'(lambda (no)
	      (declare (type fixnum no))
	      (cdr (nth (1- no) entry.list)))
	  (cdr (car (win=io.any.tyi (win=window.answer.pipe window))))))


(defun win-yes.no (window string)

  ;;; Input:   a window of type \verb$WIN=WINDOW$, and a string
  ;;; Effect:  exposes a window and asks the user a simple yes/no question
  ;;; Value:   the answer which was given by the user.

  (declare (type win*window window))
  (pro-without.scheduling
   (format win*stream "~D yes.no ~A" (win=window.command.pipe window) string)
   (princ #\null win*stream)
   (princ #\SOH win*stream))
  (force-output win*stream)
  (car (win=io.any.tyi (win=window.answer.pipe window))))

(defun win-notify (window string)

  ;;; Input:   a window of type \verb$WIN=WINDOW$, and a string
  ;;; Effect:  exposes a window and notifies the user
  ;;; Value:   NIL

  (declare (type win*window window))
  (pro-without.scheduling
   (format win*stream "~D notify ~A" (win=window.command.pipe window) string)
   (princ #\null win*stream)
   (princ #\SOH win*stream))
  (force-output win*stream))

(defun win-text.input (window string &optional (string2 ""))

  ;;; Input:   a window of type \verb$WIN=WINDOW$, and two strings
  ;;; Effect:  exposes a pop-up menu with the explanation \verb$STRING$ and the
  ;;;          optional default answer \verb$STRING$. Then, the user is asked
  ;;;          an input.
  ;;; Value:   the input which was given by the user.

  (declare (type win*window window))
  (pro-without.scheduling
   (format win*stream "~D question ~A" (win=window.command.pipe window) string)
   (princ #\null win*stream)
   (format win*stream "~A" string2)
   (princ #\null win*stream)
   (princ #\SOH win*stream))
  (force-output win*stream)
  (car (win=io.any.tyi (win=window.answer.pipe window))))


(defun win-io.get.filename (fullname command)
  
  ;;; Input: a string denoting a full file name
  ;;;        and a string denoting either "proof" or "specification"
  ;;; Value: the interface is called to get a filename, the result is either
  ;;;        the empty string denoting that the command has been cancelled, or a string
  ;;;        denoting a full file name

  (let ((window (win-window 'main)))
    (declare (type win*window window))
    (pro-without.scheduling
     (format win*stream "~D file " (win=window.command.pipe window))
     (format win*stream "~A" fullname)
     (princ #\null win*stream)
     (cond ((equalp command "proof") 
	    (format win*stream ".PRV")
	    (princ #\null win*stream))
	   ((equalp command "specification") 
	    (format win*stream ".SPEC")
	    (princ #\null win*stream)))
     (princ #\SOH win*stream))
    (force-output win*stream)
    (car (win=io.any.tyi (win=window.answer.pipe window)))))



(defun win=io.any.tyi (id)

  ;;; Input:  a number denoting an internal buffer
  ;;; Value:  the next character of this buffer
  ;;; Note:   this function waits until some character is in the internal buffer

  (pro-process.wait "tyi" #'(lambda () (not (eql (aref win*cursors id) (aref win*ends id)))))
  (prog1 (aref win*buffers id (aref win*cursors id))
    (cond ((not (eql (aref win*cursors id) win*max.buffer))
	   (incf (aref win*cursors id)))
	  (t (setf (aref win*cursors id) 0)))))


(defun win=bitmap.scale (bitmap width)

  (let* ((org.width (win-bitmap.size bitmap)) (size (/ width org.width)))
    (cond ((null size) 100)
	  ((< size .4) 20)
	  ((< size .9) 50)
	  ((< size 1.1) 100)
	  ((< size 1.6) 120)
	  (t 170))))


(defun win=size.check (size)

  (cond ((< size 5) 2)
	((< size 8) 5)
	((< size 10) 8)
	((< size 12) 10)
	((< size 14) 12)
	((< size 18) 14)
	((< size 24) 18)
	(t 24)))


;;;;;;;=================
;;;;
;;;;;;;===================

;;; Postscript page setup
;;; ---------------------
;;;
;;; 
;;;      The apple laserwriter has a self imposed clipping boundary that has been
;;;   determined to be:
;;;
;;;              Top
;;;              784
;;;     Left 22       593 Right
;;;               8
;;;             Bottom
;;;
;;;   for an 8.5 X 11 sheet of paper.  So, any postscript printing must first 
;;;   move the image within these boundaries, otherwise it will get clipped.
;;;       The postscript coordinates are arranged on a 8.5 x 11 page as follows:
;;;
;;;       y
;;;
;;;       ^
;;;       |
;;;       |
;;;
;;;       0
;;;        0   ---> x  
;;; 
;;;   with (0,0) being in the lower left hand corner.
;;;       Therefore the normal plotting coordinates of a postscript page are:
;;;
;;;               784
;;;             22   593            Normal 8.5 x 11 page
;;;                8
;;;
;;;               -22
;;;             8    784            8.5 x 11 page rotated 90 degrees
;;;              -593
;;;
;;;


(defvar ps*output.device.original.boundaries

  ;;; the boundaries of your laser printer.  Each laser printer has a certain (left, top, right, bottom)
  ;;; set of coordinates past which the postscript drawing gets cliped.  I have computed
  ;;; the coordinates for an Apple Laser Writer to be (22 784 592 8).

  '(22 784 592 8))


(defvar ps*default.plot.label

  ;;; A text string to display at the bottom or top of the drawing. When the date is also displayed,
  ;;; the string will appear to the right of the date. \verb$NIL$ indicates no string to draw

  nil)


(defvar ps*default.label.location

  ;;; location on the page to display the date and plot label
  ;;; \begin{itemize}
  ;;;   \item \verb$:top$  the date/label string starts in the upper left corner
  ;;;   \item \verb$:bottom$  the date/label string starts in the bottom left corner
  ;;; \end{itemize}

  :bottom)


(defvar ps*default.label.scale

  ;;; the scale at which to draw the date/label string (> 1 = enlarged, 1.0 = normal size, < 1 = shrunk)

  0.7)


(defvar ps*default.multi.page.scale

  ;;; the scale of the drawings when ps*number.of.pages is :multiple. (> 1 = enlarged, 1.0 = normal size, < 1 = shrunk)

  0.7)


(defvar ps*postscripter
  
  ;;; the default postscript handler
  
  nil)


(defparameter ps*black "Black")
(defparameter ps*white "White")


;; -------------------------------------------------------------------
;;                           Postscript Handler
;; -------------------------------------------------------------------


(defstruct (ps*postscript.handler (:conc-name ps=psh.))
  
  temp.output.path fonts.in.use font.list current.font current.line.dashes
  postscript.output.file clip.region.active bounding.box output.path destination
  orientation number.of.pages display.date
  (plot.label ps*default.plot.label)
  (label.location ps*default.label.location)
  (label.scale ps*default.label.scale)
  (multi.page.scale ps*default.multi.page.scale)
  (font.index 0)
  (linewidth  1)
  (grayval  "0.0 0.0 0.0")              
  (current.color ps*black)
  (compute.boundingbox t)
  (output.device.boundaries (copy-list ps*output.device.original.boundaries))
  (output.device.original.boundaries  ps*output.device.original.boundaries))


(defstruct (ps*postscript.font (:conc-name ps=psf.))
  
  font.height font.ascent font.descent font.name font.array)



(defun ps-reset ()

  (setq ps*postscripter (make-ps*postscript.handler))
  (ps=initialize.instance ps*postscripter))


(defun ps-open.stream (file &key (postscripter ps*postscripter) (destination :laser.printing)
			    (orientation :landscape) (number.of.pages :one) (dispay.date nil))
  
  ;;; Input:  the destination of the postscript drawing.
  ;;;         \begin{itemize}
  ;;;           \item \verb$:laser.printing$ it will be sent to a laser printer
  ;;;           \item \verb$:document.inclusion$ it will be included in a document, such as LaTeX
  ;;;         \end{itemize}
  ;;;         the orientation of the drawing when it's printed
  ;;;         \begin{itemize}
  ;;;           \item \verb$:portrait$ no chang es are by 90 degrees
  ;;;           \item \verb$:landscape$ all coordinates are rotated by 90 degrees
  ;;;         \end{itemize}
  ;;;         number-of-pages indicates whether to display the drawing across multiple pages or not.
  ;;;          \begin{itemize}
  ;;;            \item \verb$:one$ the drawing will be scaled so that it all fits on one page
  ;;;            \item \verb$:multiple$  the drawing will be divided up with each part being
  ;;;                  drawn on a separate page (this option only works when the destination is 'laser.printing)
  ;;;          \end{itemize}
  ;;; Value:  the postscripter used for output  

  (setq ps*bitmaps nil)
  (ps=initialize.postscript.variables postscripter file destination orientation number.of.pages dispay.date)
  (ps=init.labels postscripter)
  (cond ((and (not (ps=psh.compute.boundingbox postscripter))
	      (eq (ps=psh.number.of.pages postscripter) :one))
	 (setf (ps=psh.postscript.output.file postscripter)
	       (open (ps=psh.output.path postscripter) :direction :output 
		     :if-exists :overwrite :if-does-not-exist :create))
	 (ps=write.postscript.header postscripter)
	 (cond ((eq (ps=psh.destination postscripter) :laser.printing)
		(ps=setup.onepage.coordinates postscripter))))
	(t (setf (ps=psh.temp.output.path postscripter)
		 (concatenate 'string (ps=psh.output.path postscripter) "1temp"))
	   (setf (ps=psh.postscript.output.file postscripter)
		 (open (ps=psh.temp.output.path postscripter)
		       :direction :output :if-exists :overwrite :if-does-not-exist :create))))
  postscripter)


(defun ps-close.stream (&optional (postscripter ps*postscripter))
  
  (when (ps=psh.clip.region.active postscripter)
    (setf (ps=psh.clip.region.active postscripter) nil)
    (format (ps=psh.postscript.output.file postscripter) "  grestore~%"))

  (case (ps=psh.destination postscripter)
    (:document.inclusion
       (if (equal (ps=psh.number.of.pages postscripter) :one)
           (ps=draw.labels postscripter)))
    (:laser.printing
      (when (equal (ps=psh.number.of.pages postscripter) :one)
        (format (ps=psh.postscript.output.file postscripter) "grestore~%")
        (ps=draw.labels postscripter)
        (format (ps=psh.postscript.output.file postscripter) "~&showpage~&"))))

  (close (ps=psh.postscript.output.file postscripter))

  (if (ps=psh.compute.boundingbox postscripter)
      (ps=arrange.output.file postscripter)
      (setf (ps=psh.compute.boundingbox postscripter) t))
  (setq ps*bitmaps nil)
  t)


(defun ps=initialize.instance (psh)

  (dolist (font.metric ps*postscript.font.metrics)
      (let* ((font.name (first font.metric))
	     (font.height (second font.metric))
	     (font.ascent (third font.metric))
	     (font.descent (fourth font.metric))
	     (char.widths (cddddr font.metric))
	     (font.array (make-array 256 :initial-contents char.widths)))
	(push (make-ps*postscript.font
	       :font.height font.height
	       :font.ascent font.ascent
	       :font.descent font.descent
	       :font.name font.name
	       :font.array font.array)
	      (ps=psh.font.list psh))))
  (setf (ps=psh.font.list psh) (nreverse (ps=psh.font.list psh))))


(defun ps=initialize.postscript.variables (psh file destination orientation number.of.pages display.date)

  (setf (ps=psh.output.path psh) file)
  (setf (ps=psh.current.font psh) nil)
  (setf (ps=psh.destination psh) destination)
  (setf (ps=psh.orientation psh) orientation)
  (setf (ps=psh.display.date psh) display.date)
  (setf (ps=psh.number.of.pages psh) number.of.pages)
  (setf (ps=psh.fonts.in.use psh) nil)
  (setf (ps=psh.clip.region.active psh) nil)
  (setf (ps=psh.output.device.boundaries psh)
	(copy-list (ps=psh.output.device.original.boundaries psh)))
  (setf (ps=psh.compute.boundingbox psh) t)
  (setf (ps=psh.bounding.box psh) (list 999999 999999 -999999 -999999)))


(defun ps=init.labels (psh)
  
  (when (or (ps=psh.display.date psh) (ps=psh.plot.label psh))
    (let* ((top.y (if (equal (ps=psh.orientation psh) :landscape)
		      (- (first (ps=psh.output.device.boundaries psh)))
		      (second (ps=psh.output.device.boundaries psh))))
           (bottom.y (if (equal (ps=psh.orientation psh) :landscape)
		         (- (third (ps=psh.output.device.boundaries psh)))
		         (fourth (ps=psh.output.device.boundaries psh))))
           (offset (ceiling (+ 10 (* 12 (ps=psh.label.scale psh))))))

       (case (ps=psh.label.location psh)
         (:bottom
           (setq bottom.y (+ bottom.y offset))
           (if (equal (ps=psh.orientation psh) :landscape)
               (setf (third (ps=psh.output.device.boundaries psh)) (- bottom.y))
               (setf (fourth (ps=psh.output.device.boundaries psh)) bottom.y)))
         (:top
           (setq top.y (- top.y offset))
           (if (equal (ps=psh.orientation psh) :landscape)
               (setf (first (ps=psh.output.device.boundaries psh)) (- top.y))
               (setf (second (ps=psh.output.device.boundaries psh)) top.y)))))))


(defun ps=draw.labels (postscripter &optional multi.page)
  (when (or (ps=psh.display.date postscripter)
	    (stringp (ps=psh.plot.label postscripter)))
    (let* ((top.y (if (equal (ps=psh.orientation postscripter) :landscape)
		      (- (first (ps=psh.output.device.boundaries postscripter)))
		      (second (ps=psh.output.device.boundaries postscripter))))
           (bottom.y (if (equal (ps=psh.orientation postscripter) :landscape)
		         (- (third (ps=psh.output.device.boundaries postscripter)))
		         (fourth (ps=psh.output.device.boundaries postscripter))))
  	   (left.x (if (equal (ps=psh.orientation postscripter) :landscape)
		       (fourth (ps=psh.output.device.boundaries postscripter))
		       (first (ps=psh.output.device.boundaries postscripter))))
           (indent (if multi.page "              " "  "))
           (xdate.string (when (ps=psh.display.date postscripter) (ps=get.current.short.date)))
           (xstart (+ left.x 20))
           (ystart nil)
           (scale (ps=psh.label.scale postscripter))
           (inverse.scale (/ 1 scale))
           (display.string nil))

    (cond ((and (stringp (ps=psh.plot.label postscripter)) (ps=psh.display.date postscripter))
           (setq display.string (concatenate 'string xdate.string "      " (ps=psh.plot.label postscripter))))
          ((stringp (ps=psh.plot.label postscripter))
           (setq display.string (ps=psh.plot.label postscripter)))
          ((ps=psh.display.date postscripter)
           (setq display.string xdate.string)))

    (case (ps=psh.label.location postscripter)
      (:top     (setq ystart (+ top.y 10)))
      (:bottom  (setq ystart (- bottom.y (ceiling (+ 10 (* 12 scale)))))))

    (setq xstart (/ xstart scale))
    (setq ystart (/ ystart scale))

    (unless multi.page
      (format (ps=psh.postscript.output.file postscripter) "~agsave~%" indent))
    (when (equal (ps=psh.number.of.pages postscripter) :one)
      (if (equal (ps=psh.orientation postscripter) :landscape)
          (format (ps=psh.postscript.output.file postscripter) "~a90.0 rotate~%" indent)
          (format (ps=psh.postscript.output.file postscripter) "~a0.0 rotate~%" indent)))
    (format (ps=psh.postscript.output.file postscripter) "~a~,3f ~,3f scale~%" indent scale scale) 
    (format (ps=psh.postscript.output.file postscripter) "~a/Courier-Bold findfont 12 scalefont setfont~%" indent)
    (format (ps=psh.postscript.output.file postscripter) "~a~,2f ~,2f m (~a) show~%" indent xstart ystart display.string)
    (format (ps=psh.postscript.output.file postscripter) "~a~,3f ~,3f scale~%" indent inverse.scale inverse.scale)
    (unless multi.page
      (format (ps=psh.postscript.output.file postscripter) "~agrestore~%" indent)))))


(defun ps=arrange.output.file (postscripter)
  
  (unless (and (not (ps=psh.compute.boundingbox postscripter))
	       (equal (ps=psh.number.of.pages postscripter) :one))
    (close (ps=psh.postscript.output.file postscripter)))
  
  (when (probe-file (ps=psh.output.path postscripter))
    (delete-file (ps=psh.output.path postscripter)))
  (setf (ps=psh.postscript.output.file postscripter)
	(open (ps=psh.output.path postscripter)
	      :direction :output :if-exists :overwrite :if-does-not-exist :create))
  (ps=write.postscript.header postscripter)
  (ps=write.bitmaps postscripter)
  (case (ps=psh.destination postscripter)
    (:laser.printing
     (case (ps=psh.number.of.pages postscripter)
       (:one
	(ps=setup.onepage.coordinates postscripter)
	(close (ps=psh.postscript.output.file postscripter))
	(copy-file (ps=psh.temp.output.path postscripter)
		   (ps=psh.output.path postscripter)
		   :if-exists :append :characters t)
	(delete-file (ps=psh.temp.output.path postscripter)))
       (:multiple
	(ps=process.multipage.setup postscripter))))
    (:document.inclusion
     (close (ps=psh.postscript.output.file postscripter))
     (copy-file (ps=psh.temp.output.path postscripter)
		(ps=psh.output.path postscripter)
		:if-exists :append :characters t)
     (delete-file (ps=psh.temp.output.path postscripter)))))

 

(defun ps=write.bitmaps (postscripter)

  (let ((counter (length ps*bitmaps)) line real.height real.width
	(postscript.output.file (ps=psh.postscript.output.file postscripter)))
    (mapc #'(lambda (bitmap)
	      (multiple-value-bind (bitmap.file width height) (values-list bitmap)
		    (with-open-file 
		     (from.stream bitmap.file  :direction :input)
		     (setq real.height (read from.stream))
		     (setq real.width (read from.stream))
		     (setf (cddr bitmap) (list real.width real.height))
		     (format postscript.output.file "/icon~D ~D string def~%" counter
			     (floor (* real.height real.width)))
		     (format postscript.output.file "currentfile icon~D readhexstring pop~%" counter)
		     (do ()
			 ((eq line :eof))
			 (setf line (read-line from.stream nil :eof))
			 (unless (eq line :eof)
				 (write-line line postscript.output.file))))
		    (decf counter)))
	  ps*bitmaps)))


(defun ps=write.postscript.header (postscripter)
  
  (let ((postscript.output.file (ps=psh.postscript.output.file postscripter)))
  ; (format postscript.output.file "%! -*- Mode: Text -*-~%~%")
    (format postscript.output.file "%!PS-Adobe-3.0~%")
    (format postscript.output.file "%%Title: Postscript Document~%")
    (format postscript.output.file "%%Creator: ~a~%" "INKA")
    (format postscript.output.file "%%CreationDate: ~a~%" (ps=get.current.date))
    (format postscript.output.file "%%For: ~a~%" (ps=get.author))
 ;  (format postscript.output.file "%%DocumentFonts: atend~%")
    (format postscript.output.file "%%Pages: 1~%")
    (format postscript.output.file "%%BoundingBox: ~,2f ~,2f ~,2f ~,2f~%"
	    (first (ps=psh.bounding.box postscripter)) (second (ps=psh.bounding.box postscripter))
	    (third (ps=psh.bounding.box postscripter)) (fourth (ps=psh.bounding.box postscripter)))
    (format postscript.output.file "~%")
    (format postscript.output.file "statusdict /waittimeout 30 put~%")
    (format postscript.output.file "/fontarray 30 array def~%")
    (format postscript.output.file "/f {fontarray exch get setfont} def~%")
    (format postscript.output.file "/estfont {findfont exch scalefont fontarray 3 1 roll put} def~%")
    (format postscript.output.file "/m {moveto} def~%")
    (format postscript.output.file "/format-rotation 0 def~%")
    (format postscript.output.file "/format-y-translation 0 def~%")
    (format postscript.output.file "/new-matrix {0 format-y-translation translate~%")
    (format postscript.output.file "	      format-rotation rotate} def~%")
    (format postscript.output.file "/new-page {showpage new-matrix} def~%")
    (format postscript.output.file "userdict /mtrx matrix put~%")
    (format postscript.output.file "/DrawEllipse {~%")
    (format postscript.output.file "    /endangle exch def~%")
    (format postscript.output.file "    /startangle exch def~%")
    (format postscript.output.file "	/yrad exch def~%")
    (format postscript.output.file "	/xrad exch def~%")
    (format postscript.output.file "	/y exch def~%")
    (format postscript.output.file "	/x exch def~%")
    (format postscript.output.file "    /savematrix mtrx currentmatrix def~%")
    (format postscript.output.file "	x y translate xrad yrad scale 0 0 1 startangle endangle arc~%")
    (format postscript.output.file "    savematrix setmatrix~%")
    (format postscript.output.file "	} def~%")
    (format postscript.output.file "/colorimage where { pop }~%")
    (format postscript.output.file "       {/colortogray {~%")
    (format postscript.output.file "        /npixls 0 def /rgbindx 0 def~%")
    (format postscript.output.file "        /rgbdata exch store rgbdata length 3 idiv~%")
    (format postscript.output.file "        /npixls exch store /rgbindx 0 store ~%")
    (format postscript.output.file "        /grays rgbdata length 3 idiv string def~%")
    (format postscript.output.file "        0 1 npixls 1 sub~%")
    (format postscript.output.file "        {grays exch ~%")
    (format postscript.output.file "           rgbdata rgbindx       get 20 mul ~%")
    (format postscript.output.file "           rgbdata rgbindx 1 add get 32 mul ~%")
    (format postscript.output.file "           rgbdata rgbindx 2 add get 12 mul ~%")
    (format postscript.output.file "           add add 64 idiv put /rgbindx rgbindx 3 add store } for ~%")
    (format postscript.output.file "         } bind def ~%")
    (format postscript.output.file "/colorimage {pop pop colortogray grays image } bind def~%")
    (format postscript.output.file "} ifelse          % end of 'false' case~%")
    (format postscript.output.file "%%EndProlog~%~%")
    (format postscript.output.file "new-matrix~%")
    ))


(defun ps=setup.onepage.coordinates (postscripter)

  ;;;   Effect:  Basically, what happens is
  ;;;            that a scaling factor is computed for both the x and y axis of the plot
  ;;;            which can be applied to the axies to make them reduce the image along that
  ;;;            axis enough to fit on one page.  The axis with the smallest scaling factor
  ;;;            is chosen and then used for both axies.  (This prevents distortion, which
  ;;;            occurrs when one axis is scaled differently than the other)  The
  ;;;            coordinates for the center of the image are then scaled and used to
  ;;;            determine a translation vector that will move the center of the image to
  ;;;            the center of the output device page.
  ;;;                Please note that when the image is rotated 90 degrees, the output
  ;;;            device coordinates become negative on the y-axis.
  
  (let* ((output.device.boundaries (ps=psh.output.device.boundaries postscripter))
	 (orientation (ps=psh.orientation postscripter))
         ;; setup coordinates for the output device.
	 (left.x (if (eq orientation :landscape)
		     (fourth output.device.boundaries)
		     (first output.device.boundaries)))
         (top.y (if (eq orientation :landscape)
		    (- (first output.device.boundaries))
		    (second output.device.boundaries)))
         (right.x (if (eq orientation :landscape)
		      (second output.device.boundaries)
		      (third output.device.boundaries)))
         (bottom.y (if (eq orientation :landscape)
		       (- (third output.device.boundaries))
		       (fourth output.device.boundaries)))
         (dev.x.dist (- right.x left.x))
         (dev.y.dist (- top.y bottom.y))
         (dev.x.center (+ left.x (/ dev.x.dist 2)))
         (dev.y.center (+ bottom.y (/ dev.y.dist 2)))

         ;; setup coordinates of the image.
         (llx (first (ps=psh.bounding.box postscripter)))
         (lly (second (ps=psh.bounding.box postscripter)))
         (urx (third (ps=psh.bounding.box postscripter)))
         (ury (fourth (ps=psh.bounding.box postscripter)))
         (plot.x.dist (- urx llx))                   ;; length and width of the image
         (plot.y.dist (- ury lly))
         (plot.x.center (+ llx (/ plot.x.dist 2)))   ;; center of the image
         (plot.y.center (+ lly (/ plot.y.dist 2)))

         (xscale 1.0)                                ;; scaling necessary to fit
         (yscale 1.0)                                ;;  the image on the page

         (xtrans nil)                                ;; translation necessary to 
         (ytrans nil)                                ;;  center the image on the page
        )

    ;; scale the image to fit on the page.  But, make sure the scale
    ;; is the same for both axes of the image.  Otherwise, the image
    ;; will be skewed.  Also, don't enlarge the image by keeping the
    ;; scale from exceeding 1.0
    (setq xscale (min (/ dev.x.dist plot.x.dist)
		      (/ dev.y.dist plot.y.dist)
		      1.0))
    (setq yscale xscale)

    ;; center the image by translating the drawing window to the center of
    ;; the page, dev.x.center.  Then, move the image to the center of the
    ;; page, (- (* xscale plot.x.center))  Note:  the point needs to be
    ;; scale here, since the scaling is done after the point is added.

    (setq xtrans  (- dev.x.center (* xscale plot.x.center)))
    (if (equal orientation :landscape)
        (setq ytrans (- dev.y.center (* yscale plot.y.center)))
        (setq ytrans (- dev.y.center (* yscale plot.y.center))))

    (format (ps=psh.postscript.output.file postscripter) 
      "~2&% 			New page~2&")

    (format (ps=psh.postscript.output.file postscripter) "gsave~%")
    (if (equal orientation :landscape)
        (format (ps=psh.postscript.output.file postscripter) "90.0 rotate~%")
        (format (ps=psh.postscript.output.file postscripter) "0.0 rotate~%"))

    (format (ps=psh.postscript.output.file postscripter)
	    "~,1f ~,1f translate~%" xtrans ytrans)
    (format (ps=psh.postscript.output.file postscripter)
	    "~,3f ~,3f scale~%" xscale yscale)
 
    (format (ps=psh.postscript.output.file postscripter) "newpath~%~%")
   ))


(defun ps=process.multipage.setup (postscripter)
  
  ;;;   Effect:  It first determines how many pages
  ;;;            will be necessary for printing the whole image.  It then computes the space
  ;;;            that will be left over on the topmost page and the rightmost page if the
  ;;;            image were to be printed starting at the bottom left corner of the multiple
  ;;;            pages.  This space is divided in half for both the axises, which makes it
  ;;;            the space that will border the image if the image is printed centered on the
  ;;;            multiple pages.  Now, all that is necessary is to translate the image, so 
  ;;;            that when it starts printing on the bottom left page, it will print while
  ;;;            maintaining this border space.
  ;;;                The image is then printed across the multiple pages by treating the
  ;;;            image as a virtual image and moving it so that different sections of it
  ;;;            lie over the output device window.  Then the copypage command is issued,
  ;;;            which causes that part of the image to be printed on the output device.
  ;;;                Unfortunately, it is necessary to send the entire image to the printer
  ;;;            each time a page is printed, since its not possible to reset the printer's
  ;;;            clipping window after it has received input.

    (let* ((output.device.boundaries (ps=psh.output.device.boundaries postscripter))
	   (output.device.original.boundaries
	    (ps=psh.output.device.original.boundaries postscripter))
	   (orientation (ps=psh.orientation postscripter))
         ;; setup coordinates for the output device.
	   (left.x (if (equal orientation :landscape)
		       (fourth output.device.boundaries)
		     (first output.device.boundaries)))
	   (top.y (if (equal orientation :landscape)
		      (- (first output.device.boundaries))
		    (second output.device.boundaries)))
	   (right.x (if (equal orientation :landscape)
			(second output.device.boundaries)
		      (third output.device.boundaries)))
	   (bottom.y (if (equal orientation :landscape)
			 (- (third output.device.boundaries))
		       (fourth output.device.boundaries)))
	   (org.left.x (if (equal orientation :landscape)
			   (fourth output.device.original.boundaries)
		         (first output.device.original.boundaries)))
	   (org.top.y (if (equal orientation :landscape)
			  (- (first output.device.original.boundaries))
	 	        (second output.device.original.boundaries)))
	   (org.right.x (if (equal orientation :landscape)
			    (second output.device.original.boundaries)
		          (third output.device.original.boundaries)))
	   (org.bottom.y (if (equal orientation :landscape)
			     (- (third output.device.original.boundaries))
			   (fourth output.device.original.boundaries)))
         ;; reduce its size by 10% so the image on the next page will
	 ;; overlap the image from the previous page.
	   (dev.x.dist (* (- right.x left.x) 0.9))
	   (dev.y.dist (* (- top.y bottom.y) 0.9))

         ;; setup coordinates for the image.
	   (scale (ps=psh.multi.page.scale postscripter))
	   (llx (first (ps=psh.bounding.box postscripter)))
	   (lly (second (ps=psh.bounding.box postscripter)))
	   (urx (third (ps=psh.bounding.box postscripter)))
	   (ury (fourth (ps=psh.bounding.box postscripter)))
	   (plot.x.dist (* (- urx llx) scale))
	   (plot.y.dist (* (- ury lly) scale))

         ;; determine number of pages necessary to print image.
	   (plot.x.pages (ceiling (/ plot.x.dist dev.x.dist)))
	   (plot.y.pages (ceiling (/ plot.y.dist dev.y.dist)))
 
         ;; determine the blank space left over after the image is printed
	 ;; across multiple pages.  Then divide this amount in 2 to get the
	 ;; distance the plot needs to be from the initial boundaries of the
	 ;; first page (left and bottom margins) so that the whole image will
	 ;; end up centered on the multiple pages.
	   (plot.x.fill (/ (mod (- dev.x.dist (rem plot.x.dist dev.x.dist))
				dev.x.dist) 2))
	   (plot.y.fill (/ (mod (- dev.y.dist (rem plot.y.dist dev.y.dist))
				dev.y.dist) 2))

         ;; initial translation necessary to center plot on the multiple pages
	   (xtrans (+ plot.x.fill (* (- llx) scale)))
	   (ytrans nil)

         ;; distances the clipping window needs to move to display other parts
	 ;; of the image.
	   (xtrans.inc dev.x.dist)
	   (ytrans.inc dev.y.dist)

         ;; initial translation that starts the printing at the bounding edge
	 ;; of the output device.
	   (xtransfix left.x)
	   (ytransfix nil)
	   (line.count 0)		;lines read in so far
	   (graphic.blocks 1)		;number of blocks of images
	   (postscript.input.file nil)	;file of drawing commands
	   (postscript.output.file nil)
	   )

      (if (equal orientation :landscape)        ;; compute y translation
	  (progn
	    (setq ytrans (+ (* (- lly) scale) plot.y.fill))
	    (setq ytransfix bottom.y))
        (progn
          (setq ytrans (+ (* (- lly) scale) plot.y.fill))
          (setq ytransfix bottom.y)))

      (close (ps=psh.postscript.output.file postscripter))
      (setq postscript.input.file
	    (open (ps=psh.temp.output.path postscripter) :direction :input))
      (setf (ps=psh.postscript.output.file postscripter)
	    (open (ps=psh.output.path postscripter) :direction :output 
		  :if-exists :append :if-does-not-exist :create))

      (setq postscript.output.file (ps=psh.postscript.output.file postscripter))

      (format postscript.output.file "~%~%/graphic-block~a  {~%" graphic.blocks)

      (do ((input.block nil))
	  ((eq 'eof (setq input.block (read-line postscript.input.file nil 'eof))))
	(incf line.count)
	(format postscript.output.file "   ~a~%" input.block)
	(when (> line.count 75)
	  (setq line.count 1)
	  (format postscript.output.file "  } def~%~%")
	  (incf graphic.blocks)
	  (format postscript.output.file "/graphic-block~a  {~%" graphic.blocks)
	  ))

      (format postscript.output.file "  } def~%~%~%")

      (close postscript.input.file)
      (delete-file (ps=psh.temp.output.path postscripter))

      (format postscript.output.file "%% routine to print each page of the image.~%")
      (format postscript.output.file "    /rows ~a def                    ~%" plot.y.pages)
      (format postscript.output.file "    /columns ~a def                 ~%" plot.x.pages)
      (format postscript.output.file "                                    ~%")
      (if (equal orientation :landscape)
	  (format postscript.output.file "    90.0 rotate                     ~%")
        (format postscript.output.file "    0.0 rotate                      ~%"))
      (format postscript.output.file "                                    ~%")
      (format postscript.output.file "    newpath                         ~%")
      (format postscript.output.file "      ~,2f ~,2f m                  ~%" org.left.x  org.bottom.y)
      (format postscript.output.file "      ~,2f ~,2f lineto                  ~%" org.left.x  org.top.y)
      (format postscript.output.file "      ~,2f ~,2f lineto                  ~%" org.right.x org.top.y)
      (format postscript.output.file "      ~,2f ~,2f lineto                  ~%" org.right.x org.bottom.y)
      (format postscript.output.file "                                    ~%")
      (format postscript.output.file "    closepath                       ~%")
      (format postscript.output.file "    clip                            ~%")
      (format postscript.output.file "    newpath                         ~%")
      (format postscript.output.file "                                    ~%")
      (format postscript.output.file "    0 1 rows 1 sub                  ~%")
      (format postscript.output.file "      {  /rowcount exch def         ~%")
      (format postscript.output.file "        0 1 columns 1 sub           ~%")
      (format postscript.output.file "          { /colcount exch def      ~%")
      (format postscript.output.file "            gsave                   ~%")
      (ps=draw.labels postscripter t)
      (format postscript.output.file "              newpath               ~%")
      (format postscript.output.file "              ~,2f ~,2f m      ~%" left.x  bottom.y)
      (format postscript.output.file "              ~,2f ~,2f lineto      ~%" left.x  top.y)
      (format postscript.output.file "              ~,2f ~,2f lineto      ~%" right.x top.y)
      (format postscript.output.file "              ~,2f ~,2f lineto      ~%" right.x bottom.y)
      (format postscript.output.file "                                    ~%")
      (format postscript.output.file "              closepath             ~%")
      (format postscript.output.file "              clip                  ~%")
      (format postscript.output.file "              newpath               ~%")
      (format postscript.output.file "                                    ~%")
      (format postscript.output.file "              ~,3f ~,3f translate   ~%" xtransfix ytransfix)
      (format postscript.output.file "              ~,2f ~,2f colcount mul sub ~%" xtrans xtrans.inc)
      (format postscript.output.file "                ~,2f ~,2f rowcount mul sub ~%" ytrans ytrans.inc)
      (format postscript.output.file "                 translate          ~%")
      (format postscript.output.file "              ~,3f ~,3f scale       ~%" scale scale)
      (format postscript.output.file "                                    ~%")
      (do ((i 1 (1+ i)))
	  ((> i graphic.blocks))
	(format postscript.output.file "              graphic-block~a       ~%" i))
      (format postscript.output.file "                                    ~%")
      (format postscript.output.file "              copypage              ~%")
      (format postscript.output.file "              erasepage             ~%")
      (format postscript.output.file "            grestore                ~%")
      (format postscript.output.file "          } for                     ~%")
      (format postscript.output.file "      } for                         ~%")
      (format postscript.output.file "                                    ~%")
      (format postscript.output.file "                                    ~%")
      (format postscript.output.file "    newpath                         ~%~%")
      (close postscript.output.file)
      ))
    





;;;;;;;;;;;;
;;;;;
;;;;; Drawing functions
;;;;;
;;;;;


(defun ps=draw.text (postscripter string x y &key text.style
				  (line.thickness 1) (ink ps*black)
				  (bounding.box nil) (align.x :left) (align.y :top))
  
  (cond ((null text.style) (setq text.style (ps=psh.current.font postscripter))))
  (unless (and (eq align.x :left) (eq align.y :baseline))
    (let ((xoff 0) (yoff 0))
      (case align.x
	(:left )
	(:center (setf xoff (- (/ (ps=text.size postscripter string :text.style text.style) 2))))
	(:right  (setf xoff (- (ps=text.size postscripter string :text.style text.style)))))
      (case align.y
	(:baseline )
	(:top (setf yoff (ps=text.style.ascent postscripter text.style)))
	(:center (setf yoff
		       (/ (- (ps=text.style.ascent postscripter text.style)
			     (ps=text.style.descent postscripter text.style))
			  2)))
	(:bottom (setf yoff
		       (- (ps=text.style.descent postscripter text.style)))))
      (incf x xoff)
      (incf y yoff)))
  
  (ps=check.linewidth postscripter line.thickness)
  (ps=check.grayscale postscripter ink)
  (ps=check.font postscripter text.style)
  (when (ps=psh.compute.boundingbox postscripter)
    (if bounding.box
	(ps=check.bounds postscripter bounding.box)
      (let* ((string.len (ps=text.size postscripter string :text.style text.style))
	     (string.ascent (ps=text.style.ascent postscripter text.style))
	     (string.descent (ps=text.style.descent postscripter text.style))
	     (x.end (+ x string.len))
	     (y.top (- y string.ascent))
	     (y.bottom (+ y string.descent)))
	(ps=check.x.bounds postscripter x)
	(ps=check.x.bounds postscripter x.end)
	  (ps=check.y.bounds postscripter (- y.bottom))
	  (ps=check.y.bounds postscripter (- y.top)))))
  (format (ps=psh.postscript.output.file postscripter)
	  "~&~,1f ~,1f m (~a) show~&" x (- y)
	  (ps=string string)		;Slashify #\\, #\( and #\)
	  ))


(defun ps=string (string)
  
  (let ((print.string "")
	(current.char nil))
   ;; make sure string's not a symbol
    (unless (stringp string)
      (setf string (format nil "~s" string)))
    (do ((i (1- (length string)) (1- i)))
	((< i 0))
      (setf current.char (char string i))
      (if (or (char= current.char #\()
	      (char= current.char #\))
	      (char= current.char #\\))
	  (setf print.string
		(concatenate 'string "\\" (string current.char) print.string))
	(setf print.string
	      (concatenate 'string (string current.char) print.string))))
    print.string))

(defun ps=text.size (postscripter text &key text.style (start 0) (end nil))
  
  (let ((ps.font (ps=decode.font postscripter text.style))
	(scale.factor (ps=get.ps.scale.factor text.style)))
    (if (null ps.font)
	(values (* (length text) 6) 60)
      (let* ((array (ps=psf.font.array ps.font))
	     (total.width 0)
	     (char.width nil)
	       (space.width (aref array (char-code #\space))))
	(unless end
	  (setf end (length text)))
	(do ((i start (1+ i)))
	    ((>= i end))
	  (setf char.width (or (aref array (char-code (char text i)))
			       space.width))
	  (incf total.width (* char.width scale.factor)))
	(values total.width (* (ps=psf.font.height ps.font) scale.factor))))))


(defun ps=text.style.ascent (postscripter font)
  
  (let ((ps.font (ps=decode.font postscripter font))
	(scale.factor (ps=get.ps.scale.factor font)))
    (if ps.font
	(* (ps=psf.font.ascent ps.font) scale.factor)
        40)))


(defun ps=text.style.descent (postscripter font)
  
  (let ((ps.font (ps=decode.font postscripter font))
	(scale.factor (ps=get.ps.scale.factor font)))
    (if ps.font
	(* (ps=psf.font.descent ps.font) scale.factor)
        20)))


(defun ps=text.style.height (postscripter font)
  
  (let ((ps.font (ps=decode.font postscripter font))
	(scale.factor (ps=get.ps.scale.factor font)))
    (if ps.font
	(* (ps=psf.font.height ps.font) scale.factor)
        60)))


(defun ps=draw.line (postscripter x1 y1 x2 y2 &key (line.thickness 1) (ink ps*black)
				  (bounding.box nil) (line.dashes nil))
  (let ((old.ink (ps=psh.current.color postscripter)))
    (when (ps=psh.compute.boundingbox postscripter)
	  (if bounding.box
	      (ps=check.bounds postscripter bounding.box)
	    (progn
	      (ps=check.x.bounds postscripter x1)
	      (ps=check.x.bounds postscripter x2)
	      (ps=check.y.bounds postscripter (- y1))
	      (ps=check.y.bounds postscripter (- y2)))))
    (ps=check.linewidth postscripter line.thickness)
    (ps=check.grayscale postscripter ink)
    (ps=check.line.dashes postscripter line.dashes)
    (format (ps=psh.postscript.output.file postscripter)
	    "~&~,1f ~,1f m~&~,1f ~,1f lineto stroke~&"
	    x1 (- y1) x2 (- y2))
    (ps=check.grayscale postscripter old.ink)))


(defun ps=draw.vector (postscripter x1 y1 x2 y2 &key (arrow.head.length 10) (arrow.base.width 5)	
				    (ink ps*black) (filled t) (line.thickness 1))
  (let ((old.ink (ps=psh.current.color postscripter)))
    (multiple-value-bind (xy.points xbas ybas)
			 (ps=triangle.point.translation
			  x1 y1 x2 y2 arrow.base.width arrow.head.length)
			 (ps=draw.line postscripter x1 y1 xbas ybas 
				       :line.thickness line.thickness :ink ink)
			 (ps=draw.polygon postscripter xy.points
					  :closed t :filled filled :ink ink
					  :line.thickness 1))
    (ps=check.grayscale postscripter old.ink)))


(defun ps=triangle.point.translation (from.x from.y to.x to.y arrow.base.width arrow.head.length
					     &aux (halfbase (/ arrow.base.width 2.0)))
  (let* ((dy (- to.y from.y))
	 (dx (float (- to.x from.x)))
	 (alpha (atan dy dx))
	 (beta (atan halfbase arrow.head.length))
	 (len (sqrt (float (+ (* arrow.head.length arrow.head.length)
			      (* halfbase halfbase)))))
	 (xt (- to.x (* len (cos (- alpha beta)))))
	 (yt (- to.y (* len (sin (- alpha beta)))))	
	 (xb (- to.x (* len (cos (+ alpha beta)))))
	 (yb (- to.y (* len (sin (+ alpha beta)))))
	 (xbas (- to.x (* len (cos alpha))))
	 (ybas (- to.y (* len (sin alpha)))))
    (values (list to.x to.y xt yt xb yb)
	    xbas ybas)))


(defun ps=draw.circle (postscripter x y rad
			&key (line.thickness 1) (ink ps*black)
			     (bounding.box nil) (filled nil)
			     (line.dashes nil) (start.angle 0) (end.angle 360))
  (let ((old.ink (ps=psh.current.color postscripter)))
    (when (ps=psh.compute.boundingbox postscripter)
	  (if bounding.box
	      (ps=check.bounds postscripter bounding.box)
	    (progn
	      (ps=check.x.bounds postscripter (- x rad))
	      (ps=check.x.bounds postscripter (+ x rad))
	      (ps=check.y.bounds postscripter (- (- y) rad))
	      (ps=check.y.bounds postscripter (+ (- y) rad)))))
    (ps=check.linewidth postscripter line.thickness)
    (ps=check.grayscale postscripter ink)
    (ps=check.line.dashes postscripter line.dashes)
    
    (if filled
					;draw a filled in circle connecting line from current point.
	(format (ps=psh.postscript.output.file postscripter)    
		"~&newpath ~,2f ~,2f ~,2f ~a ~a arc fill~&"	
		x (- y) rad start.angle end.angle)
      (format (ps=psh.postscript.output.file postscripter)
	      "~&newpath ~,2f ~,2f ~,2f ~a ~a arc stroke~&"
	      x (- y) rad start.angle end.angle))
    (ps=check.grayscale postscripter old.ink)))
  

(defun ps=draw.ellipse (postscripter x y x.rad y.rad
			&key (line.thickness 1) (ink ps*black)
			     (bounding.box nil) (filled nil)
			     (line.dashes nil))
  (let ((old.ink (ps=psh.current.color postscripter)))
    (when (ps=psh.compute.boundingbox postscripter)
	  (if bounding.box
	      (ps=check.bounds postscripter bounding.box)
	    (progn
	      (ps=check.x.bounds postscripter (- x x.rad))
	      (ps=check.x.bounds postscripter (+ x x.rad))
	      (ps=check.y.bounds postscripter (- (- y) y.rad))
	      (ps=check.y.bounds postscripter (+ (- y) y.rad)))))
    (ps=check.linewidth postscripter line.thickness)
    (ps=check.grayscale postscripter ink)
    (ps=check.line.dashes postscripter line.dashes)
    
    (if filled
					;draw a filled in circle connecting line from current point.
	(format (ps=psh.postscript.output.file postscripter)
		"~&newpath ~,2f ~,2f ~,2f ~,2f 0 360 DrawEllipse fill ~&"	
		x (- y) x.rad y.rad)
      (format (ps=psh.postscript.output.file postscripter)
	      "~&newpath ~,2f ~,2f ~,2f ~,2f 0 360 DrawEllipse stroke ~&"
	      x (- y) x.rad y.rad))
    (ps=check.grayscale postscripter old.ink)))


(defun ps=point.dist (x1 y1 x2 y2)
  "This calculates the distance between two points (x1,y1) and (x2,y2)."
  
  (let ((dx (- x2 x1))
	(dy (- y2 y1)))
    (sqrt (+ (* dx dx) (* dy dy)))))


;; This is probably handled by draw.circle

(defun ps=draw.arc (postscripter xc yc xsp ysp deg
				 &key (line.thickness 1) (ink ps*black) (filled nil)
				 (bounding.box nil) (line.dashes nil))
  (unless (or (null ink) (zerop deg))
    
    (setq deg (* (signum deg)  
		 (let ((arc.angle (rem (abs deg) 360)))
		   (if (zerop arc.angle)
		       360
		     arc.angle))))

    (let* ((radians.per.degree 0.0174532925199433)
	   (dx                 (- xsp xc))
	   (dy                 (- (- ysp yc)))
	   (radius             (ps=point.dist xc yc xsp ysp))
	   (start.angle (/ (atan dy dx) radians.per.degree))
           (end.angle nil))
      (if (minusp start.angle)
          (setq start.angle (+ start.angle 360)))
      (if (minusp deg)
          (progn
            (setq end.angle start.angle)
            (setq start.angle (+ end.angle deg))
            (if (minusp start.angle)
                (setq start.angle (+ start.angle 360))))
	(progn
	  (setq end.angle (rem (+ start.angle deg) 360))))
      
      (when (ps=psh.compute.boundingbox postscripter)
        (if bounding.box
	    (ps=check.bounds postscripter bounding.box)
	  (progn
	    (ps=check.x.bounds postscripter (- xc radius))
	    (ps=check.x.bounds postscripter (+ xc radius))
	    (ps=check.y.bounds postscripter (- (- yc) radius))
	    (ps=check.y.bounds postscripter (+ (- yc) radius)))))
      (ps=check.linewidth postscripter line.thickness)
      (ps=check.grayscale postscripter ink)
      (ps=check.line.dashes postscripter line.dashes)
      
      (if filled
					;draw a filled in circle connecting line from current point.
          (format (ps=psh.postscript.output.file postscripter)
	          "~&newpath ~,2f ~,2f ~,2f ~,4f ~,4f arc fill~&"
	          xc (- yc) radius start.angle end.angle)
	(format (ps=psh.postscript.output.file postscripter)
		"~&newpath ~,2f ~,2f ~,2f ~,4f ~,4f arc stroke~&"
		xc (- yc) radius start.angle end.angle)))))


(defun ps=draw.symbol (postscripter x y char.id &key (ink ps*black) (line.thickness 1))
  (ps=check.linewidth postscripter line.thickness)
  (ps=check.grayscale postscripter ink)
  (ps=check.x.bounds postscripter x)
  (ps=check.y.bounds postscripter (- y))
  (ps=check.font postscripter (cons 'symbol 12))
  (format (ps=psh.postscript.output.file postscripter)
	    "~&~,1f ~,1f m (\\~o) show~&" x (- y) char.id))


(defun ps=draw.point (postscripter x y &key (ink ps*black) (line.thickness 1))

  ;; (format (ps=psh.postscript.output.file postscripter)
  ;;	     "~&~,1f ~,1f m  0 0 rlineto  stroke~&" x (- y))
    
  ;; David Throop's Way
  ;; Draw a point in the symbol font centered around (x y).
  ;; It's supposed to be faster than drawing a small circle.  (56 octal = 46)
  ;; (draw-symbol postscripter (- x 1.5) (+ y 1) #8r56 :ink ink
  ;;	       :line-thickness line-thickness)

  ;; This way is as good as any

  (ps=draw.circle postscripter x y line.thickness :filled t :ink ink))


(defun ps=draw.rectangle (postscripter left top right bottom
			   &key (line.thickness 1)(ink ps*black)(filled t)
			        (bounding.box nil) (line.dashes nil))

  (let ((old.ink (ps=psh.current.color postscripter)))
    (when (ps=psh.compute.boundingbox postscripter)
	  (if bounding.box
	      (ps=check.bounds postscripter bounding.box)
	    (progn
	      (ps=check.x.bounds postscripter left)
	      (ps=check.x.bounds postscripter right)
	      (ps=check.y.bounds postscripter (- top))
	      (ps=check.y.bounds postscripter (- bottom)))))
    (ps=check.linewidth postscripter line.thickness)
    (ps=check.grayscale postscripter ink)
    (ps=check.line.dashes postscripter line.dashes)
    
    (if (and (= left right) (= top bottom))
	(ps=draw.point postscripter left right)
      (progn
	(format (ps=psh.postscript.output.file postscripter)
		"~&~,1f ~,1f m       % drawing a box~&~
                   ~,1f ~,1f lineto~&~
                   ~,1f ~,1f lineto~&~
                   ~,1f ~,1f lineto~& closepath"
		left (- top) left (- bottom)
		right (- bottom) right (- top))
	(if filled
	    (format (ps=psh.postscript.output.file postscripter) "  fill~%")
	  (format (ps=psh.postscript.output.file postscripter) "  stroke~%"))))
    (ps=check.grayscale postscripter old.ink)))


(defun ps=draw.bitmap (postscripter width height left top bitmap.file
				    &key (bounding.box nil))

  (let ((right (floor (abs (+ left width)))) (bottom (floor (abs (+ height top))))
	(pathname (namestring (make-pathname :directory 
					     (append (pathname-directory *inka-pathname*) (list "idm" "xpm"))
					     :name bitmap.file
					     :type "rgb")))
	number real.width real.height)
    (when (ps=psh.compute.boundingbox postscripter)
	  (if bounding.box
	      (ps=check.bounds postscripter bounding.box)
	    (progn
	      (ps=check.x.bounds postscripter left)
	      (ps=check.x.bounds postscripter right)
	      (ps=check.y.bounds postscripter (- top))
	      (ps=check.y.bounds postscripter (- bottom)))))
    (cond ((setq number (position-if #'(lambda (x) 
					 (cond ((string-equal (car x) pathname)
						(setq real.width (fourth bitmap))
						(setq real.height (fifth bitmap))
						t)))
				     ps*bitmaps)))
	  (t (setq number (length ps*bitmaps))
	     (push (list pathname width height) ps*bitmaps)))
    (format (ps=psh.postscript.output.file postscripter)
	    "gsave~%")
    (format (ps=psh.postscript.output.file postscripter)
	    "~,1f ~,1f translate~%" left (- bottom))
    (format (ps=psh.postscript.output.file postscripter)
	    "~D ~D scale~%" width height)
    (format (ps=psh.postscript.output.file postscripter)
	    "~D ~D 8~%[~D 0 0 ~D 0 ~D]~%"
	    real.width real.height real.width (- real.height) real.height)
    (format (ps=psh.postscript.output.file postscripter)
	    "icon~D " (1+ number))
    (format (ps=psh.postscript.output.file postscripter)
	    "false 3 colorimage~%")
    (format (ps=psh.postscript.output.file postscripter)
	    "grestore~%")
    ))



(defun ps=draw.segment (postscripter segment
			 &key (line.thickness 1)(ink ps*black)(filled nil)
			 (bounding.box nil))
  (let* ((first.point (car segment))
         (fx (car first.point))
         (fy (- (cadr first.point))))
    (ps=check.linewidth postscripter line.thickness)
    (ps=check.grayscale postscripter ink)
    (when (ps=psh.compute.boundingbox postscripter)
      (if bounding.box
	  (ps=check.bounds postscripter bounding.box)
	(dolist (point segment)
	  (ps=check.x.bounds postscripter (first point))
	  (ps=check.y.bounds postscripter (- (second point))))))
    
    (format (ps=psh.postscript.output.file postscripter) "  ~,1f ~,1f m~%" fx fy)
    (dolist (point (cdr segment))
      (let ((x (car point))
            (y (- (cadr point))))
        (format (ps=psh.postscript.output.file postscripter) "  ~,1f ~,1f lineto~%" x y)))
    
    (when (equal first.point (car (last segment)))
      (format (ps=psh.postscript.output.file postscripter) "  closepath~%"))
    (if filled
	(format (ps=psh.postscript.output.file postscripter) "  fill~%")
      (format (ps=psh.postscript.output.file postscripter) "  stroke~%"))))


(defun ps=draw.lines (postscripter coord.seq
		       &key (line.thickness 1) (ink ps*black)
		            (bounding.box nil) (line.dashes nil))
  (ps=check.linewidth postscripter line.thickness)
  (ps=check.grayscale postscripter ink)
  (ps=check.line.dashes postscripter line.dashes)
  
  (when (ps=psh.compute.boundingbox postscripter)
      (if bounding.box
	  (ps=check.bounds postscripter bounding.box)
	(dolist (pair coord.seq)
	  (let ((p1 (car pair))
		(p2 (cadr pair)))
	      (ps=check.x.bounds postscripter (car p1))
	      (ps=check.x.bounds postscripter (car p2))
	      (ps=check.y.bounds postscripter (- (cdr p1)))
	      (ps=check.y.bounds postscripter (- (cdr p2)))))))
  
    (dolist (pair coord.seq)
      (let ((p1 (car pair))
	    (p2 (cadr pair)))
	(format (ps=psh.postscript.output.file postscripter)
		"~&~,1f ~,1f m~&~,1f ~,1f lineto stroke~&"
		(car p1) (- (cdr p1)) (car p2) (- (cdr p2))))))



;;; PS=DRAW.POLYGON draws a polygon, POINTS is a list of its vertices.
;;; By default, the interior of the polygon is filled - this is the
;;; extension over PS=DRAW-LINES. 
 
(defun ps=draw.polygon (postscripter  xy.points
			 &key (closed nil) (filled nil) (ink ps*black)
			      (line.thickness 1) (bounding.box nil)
			      (line.dashes nil))

  (cond ((oddp (length xy.points))
	(format *terminal-io* "~% ERROR:  draw-polygon called with an ~
                             odd number of points.  The points are:~%  ~a"
		xy.points))
	(t (ps=check.linewidth postscripter line.thickness)
	   (ps=check.grayscale postscripter ink)
	   (ps=check.line.dashes postscripter line.dashes)
	   
	   (when (ps=psh.compute.boundingbox postscripter)
	     (if bounding.box
		 (ps=check.bounds postscripter bounding.box)
	       (do ((points.list xy.points (cddr points.list)))
		   ((null points.list))
		 (ps=check.x.bounds postscripter (car points.list))
		 (ps=check.y.bounds postscripter (- (cadr points.list))))))
	   
	   (format (ps=psh.postscript.output.file postscripter)
		   "~&newpath ~,1f ~,1f m~&" 
		   (car xy.points) (- (cadr xy.points)))
	   
	   (do ((points.list (cddr xy.points) (cddr points.list)))
	       ((null points.list))
	     (format (ps=psh.postscript.output.file postscripter)
		     "~&~,1f ~,1f lineto~&" (car points.list) (- (cadr points.list))))
	   
	   (when closed
	     (format (ps=psh.postscript.output.file postscripter) "closepath "))
	   
	   (if filled
	       (format (ps=psh.postscript.output.file postscripter) "fill~&")
	     (format (ps=psh.postscript.output.file postscripter) "stroke~&")))))


(defun ps=draw.ring (postscripter x y minor.r major.r 
		      &key (ink ps*black) (line.thickness 1)
		      (bounding.box nil) (line.dashes nil))
  (let ((radius (/ (+ major.r minor.r) 2.0)))
    (ps=check.grayscale postscripter ink)
    (ps=check.linewidth postscripter line.thickness)
    (ps=check.line.dashes postscripter line.dashes)
    
    (when (ps=psh.compute.boundingbox postscripter)
      (if bounding.box
	  (ps=check.bounds postscripter bounding.box)
	(progn
	  (ps=check.x.bounds postscripter (+ x radius))
	  (ps=check.x.bounds postscripter (- x radius))
	  (ps=check.y.bounds postscripter (+ y radius))
	  (ps=check.y.bounds postscripter (- y radius)))))
					;The NEWPATH has to be output to stop connecting line from current point.
      (format (ps=psh.postscript.output.file postscripter)
	      " newpath ~,1f ~,1f ~,1f 0 360 arc stroke~&"	
	      x (- y) radius)))


(defun ps=find.num.bits (num.designs)
  (let ((size.limits '((2 . 1) (4 . 2) (16 . 4) (256 . 8)))
	(num.bits nil))
    (dolist (sizes size.limits)
      (when (<= num.designs (car sizes))
	(setf num.bits (cdr sizes))
	(return)))
    (or num.bits 16)))


(defun ps=check.bounds (postscripter bounding.box)
  (ps=check.x.bounds postscripter (first bounding.box))
  (ps=check.y.bounds postscripter (second bounding.box))
  (ps=check.x.bounds postscripter (third bounding.box))
  (ps=check.y.bounds postscripter (fourth bounding.box)))

(defun ps=check.x.bounds (postscripter x)

  (let ((low.x (first (ps=psh.bounding.box postscripter)))
	(high.x (third (ps=psh.bounding.box postscripter))))
    (when (< x low.x)
      (setf (first (ps=psh.bounding.box postscripter)) x))
    (when (> x high.x)
      (setf (third (ps=psh.bounding.box postscripter)) x))))

(defun ps=check.y.bounds (postscripter y)

  (let ((low.y (second (ps=psh.bounding.box postscripter)))
	(high.y (fourth (ps=psh.bounding.box postscripter))))
    (when (< y low.y)
      (setf (second (ps=psh.bounding.box postscripter)) y))
    (when (> y high.y)
      (setf (fourth (ps=psh.bounding.box postscripter)) y))))


(defun ps=check.font (postscripter &optional font)

  (cond ((null font) (setq font (ps=psh.current.font postscripter))))
  (let* ((points (ps=decode.font.size font))
	 (font.name (ps=decode.font.name font))
	 (pair (list font.name points))        ;pair is a list of (font size)
	 (familiar.font (assoc pair (ps=psh.fonts.in.use postscripter) :test #'equal))
	 (gatom (if familiar.font
		    (second familiar.font)
		    (progn
		      (ps=psh.font.index postscripter)
;;		      (incf (ps=psh.font.index postscripter))
		      (gentemp (format nil "~:@(~a-~)" (car pair)))
		      ))))
    (ps=enforce.font postscripter (car pair) familiar.font 
		     (cadr pair) gatom pair font)))


(defun ps=enforce.font (postscripter font familiar.font size gatom pair font.des)
  
  (cond ((not familiar.font)
	 (format (ps=psh.postscript.output.file postscripter)
		 "~& /~s ~&   /~a findfont ~s scalefont def~&~s setfont~&"
		 gatom font size gatom)
;	 (format (ps=psh.postscript.output.file postscripter)
;		 "~& ~d ~d ~s estfont~%" gatom size font)
;	 (format (ps=psh.postscript.output.file postscripter)
;		 "~& ~d f~%" gatom)
	 (push (list pair gatom) (ps=psh.fonts.in.use postscripter))
	 (setf (ps=psh.current.font postscripter) font.des))

	((not (equal font.des (ps=psh.current.font postscripter)))
;	 (format (ps=psh.postscript.output.file postscripter)
;		 "~& ~d f~%" gatom)
	 (format (ps=psh.postscript.output.file postscripter) "~&~s setfont~&" gatom)
	 (setf (ps=psh.current.font postscripter) font.des))

	(t nil)))



;;; Everytime a new font is introduced into a postscript output file,
;;; the font must be loaded and scaled and named.  Keep track of what
;;; fonts have already been used in *used-fonts*.   *Used-fonts* is an
;;; alist of the form (((fontface fontsize) name)((fontface fontsize)
;;; name)...).

;;; The fonts and linewidths stay the same in PostScript until they are
;;; changed.   Keep track of their current values in *linewidth* and
;;; *current-font*.


(defun ps=decode.font (postscripter &optional font)
  
  ;;; Given a string, determine to what PostScript typeface it
  ;;; corresponds.  Do this by looking up the family and face.
  ;;; If this is a new font, we will have to execute
  ;;; PostScript FINDFONT and SCALEFONT commands, (which is expensive, so
  ;;; we only want to do it once.)  Keep track of what fonts we have
  ;;; already seen as an Alist on *used-fonts*.  Associate each new font
  ;;; with a GENTEMP atom in the Alist.     If the font has been seen
  ;;; before (if we find it when we look it up in *used-fonts*), check to
  ;;; see if it is the *current-font*.  If so, do nothing.  If not, tell
  ;;; PostScript to SETFONT to this font.

  (cond ((null font) (setq font (ps=psh.current.font postscripter))))
  (let* ((fname (ps=decode.font.name font))
	 (font.obj (find fname (ps=psh.font.list postscripter)
			 :test #'(lambda (fn fobj)
				   (eq fn (ps=psf.font.name fobj))))))
    
    (unless font.obj
      (format *terminal-io* "~%ERROR:  the font ~a is unknown." fname))
    font.obj))


(defun ps=decode.font.name (font)
  
  (case (car font)
    (roman     :|Helvetica|)
    (italic    :|Helvetica-Oblique|)
    (bold      :|Helvetica-Bold|)
    (fixroman  :|Courier|)
    (fixitalic :|Courier-Italic|)
    (fixbold   :|Courier-Bold|)
    (symbol    :|Symbol|)))


(defun ps=decode.font.size (font)

  (cdr font))



;;;   Available fonts:
;;;   ----------------
;;;
;;;   :|Courier-Bold| :|Courier-Italic| :|Courier-Oblique| :|Courier-BoldItalic| :|Courier-BoldOblique|
;;;     :|Courier-BoldItalic| :|Courier|
;;;   :|Helvetica-Bold| :|Helvetica-Italic| :|Helvetica-Oblique| :|Helvetica-BoldItalic|) :|Helvetica-BoldOblique|
;;;   :|Helvetica-BoldItalic| :|Helvetica|
;;;   :|Times-Bold| :|Times-Italic| :|Times-Oblique| :|Times-BoldItalic| :|Times-BoldOblique| :|Times-BoldItalic| :|Times-Roman|


(defun ps=check.linewidth (postscripter thickness)
  
  ;;; Effect: In PostScript, the linewidth is a global parameter.  Every time we draw 
  ;;;         a line, we check to make sure the linewidth we want is the same as the
  ;;;         last line we drew.  If not, we must change it.
  
  (unless (= (ps=psh.linewidth postscripter) thickness)
    (format (ps=psh.postscript.output.file postscripter) "~&~,3f setlinewidth~&" thickness)
    (setf (ps=psh.linewidth postscripter) thickness)))


(defun ps=check.grayscale (postscripter &optional (color ps*black))
  
  (cond ((not (equal color (ps=psh.current.color postscripter)))
	 (setf (ps=psh.current.color postscripter) color)
	 (setq color (ps=decode.color color))
	 (cond ((not (equal (ps=psh.grayval postscripter) color))
		(setf (ps=psh.grayval postscripter) color)
		(format (ps=psh.postscript.output.file postscripter) "~%~A setrgbcolor~%" color))))))


(defun ps=decode.color (color)
  
  ;;;          Black, White, DarkBlue, LightBlue, DargGreen,
  ;;;          LightGreen, DarkRed, LightRed, DarkYellow, LightYellow, DarkPink, LightPink, 
  ;;;          DarkGrey, LightGrey
  
  ;;; NTSC formula:   luminosity = .299 red + .587 green + .114 blue

  (cond
   ((string-equal color "White") "1.0 1.0 1.0")
   ((string-equal color "Black") "0.0 0.0 0.0")
   ((string-equal color "LightRed") "1.0 0.7 0.7")
   ((string-equal color "LightBlue") "0.7 0.7 1.0")
   ((string-equal color "LightGreen") "0.7 1.0 0.7")
   ((string-equal color "LightYellow") "0.7 1.0 1.0")
   ((string-equal color "LightPink") "1.0 0.4 1.0")
   ((string-equal color "LightGrey") "0.8 0.8 0.8")
   ((string-equal color "DarkRed") "1.0 0.0 0.0")
   ((string-equal color "DarkBlue") "0.0 0.0 1.0")
   ((string-equal color "DarkGreen") "0.0 1.0 0.0")
   ((string-equal color "DarkYellow") "0.0 1.0 1.0")
   ((string-equal color "DarkPink") "0.7 0.0 0.3")
   ((string-equal color "DarkGrey") "0.3 0.3 0.3")
   (t "0.0 0.0 0.0")))


(defun ps=check.line.dashes (postscripter &optional (line.dashes nil) &aux dash.pattern)

  ;;; the dash array is:  [inked gap ...] offset setdash

  (unless (eq (ps=psh.current.line.dashes postscripter) line.dashes)
    (setf (ps=psh.current.line.dashes postscripter) line.dashes)
    (cond ((null line.dashes)
	   (setf dash.pattern "[] 0"))
	  ((typep line.dashes 'array)
	   (let ((len (length line.dashes)))
	     (setf dash.pattern "[")
	     (dotimes (i len)
	       (setf dash.pattern
		     (concatenate 'string dash.pattern
				  (format nil "~a " (aref line.dashes i)))))
	     (setf dash.pattern
		   (concatenate 'string dash.pattern "] 0"))))
	    (t
             ;; this is the default dash pattern
	     (setf dash.pattern "[4 4] 2")))
    (format (ps=psh.postscript.output.file postscripter) "~&~a setdash~&" dash.pattern)))



(defun ps=get.ps.scale.factor (font)
  
  (/ (ps=decode.font.size font)
     1000  ;; scales afm numbers into printer coordinates
     ))


(defun ps=load.ps.font (postscripter font.name font.file)
  
  ;;; Input:       a Abobe Font Metrics (AFM) file, ie Courier.afm, Courier-Bold.afm, etc.
  ;;;              like: /usr/local/tran/sparc/lib/Courier.afm
  
  (cond ((not (probe-file font.file))
	 (format *terminal-io* "~%ERROR:  unable to file file ~a" font.file))
	(t (with-open-file (instream font.file :direction :input)
	     (let (abort char.found ascender descender fontbbox
			 (array (make-array 256 :initial-element nil)))
	       (format *terminal-io* "~%;;;Loading font file ~a" font.file)
	       (do ((line (read-line instream nil 'eof)
			  (read-line instream nil 'eof)))
		   ((or (and (eq line 'eof) (setf abort t))
			(and (>= (length line) 16)
			     (equal (subseq line 0 16) "StartCharMetrics"))))
		 (cond ((and (> (length line) 8)
			     (equal (subseq line 0 8) "Ascender"))
			(setf ascender (read-from-string line :start 8)))
		       ((and (> (length line) 8)
			     (equal (subseq line 0 8) "FontBBox"))
			(setf fontbbox (read-from-string line :start 8)))
		       ((and (> (length line) 9)
			     (equal (subseq line 0 9) "Descender"))
			(setf descender (read-from-string line :start 9)))))
	       
	       (setf ascender nil)  ;; force it to use the FontBBox for now.
	
	       (when (or abort (null ascender) (null descender))
		 (multiple-value-bind (asc desc) (ps=parse.bbox fontbbox)
		   (if (or (null asc) (null desc))
		       (progn
			 (format *terminal-io* "~%ERROR: unable to process file ~a"
				 font.file)
			 (return-from ps=load.ps.font nil))
		     (progn
		       (setf ascender asc)
		       (setf descender desc)))))
	       
	       (do ((line (read-line instream nil 'eof)
			  (read-line instream nil 'eof)))
		   ((or (eq line 'eof)
			(and (>= (length line) 14)
			     (equal (subseq line 0 14) "EndCharMetrics"))))
		 (when (and (> (length line) 0) (char= (char line 0) #\C))
		     (let* ((width (read-from-string (subseq line (1+ (position #\X line)))))  ;;; WX  ...
			    (char (read-from-string (subseq line 2))))
		       (when (and char width (>= char 32) (<= char 255))
			 (setf (aref array char) width)
			 (setf char.found t)))))
	       (unless char.found
		 (format *terminal-io* "~%ERROR: no chars processed in ~a" font.file)
		 (return-from ps=load.ps.font nil))
	       
	       (let ((space.size (aref array (char-code #\space))))
		 (unless space.size
		   (setf space.size 0)
		   (dotimes (x 255)
		     (when (> (aref array x) space.size)
		       (setf space.size (aref array x))))
		   (setf (aref array (char-code #\space)) space.size)))
	       (let ((font.obj (make-ps*postscript.font
					      :font.height (- ascender descender)
					      :font.ascent ascender
					      :font.descent (abs descender)
					      :font.name font.name
					      :font.array array)))
		 (push font.obj (ps=psh.font.list postscripter))
		 font.obj))))))


(defun ps=parse.bbox (fontbbox)
  (let (pos asc desc ignore)
    (cond ((null fontbbox)  (values nil nil))
	  ((string= fontbbox "") (values nil nil))
	  (t (multiple-value-setq (ignore pos) (read-from-string fontbbox))
	     (setf fontbbox (subseq fontbbox pos))
	     (cond ((string= fontbbox "")  (values nil nil))
		   (t (multiple-value-setq (desc pos) (read-from-string fontbbox))
		      (setf fontbbox (subseq fontbbox pos))
		      (cond ((string= fontbbox "") (values nil nil))
			    (t (multiple-value-setq (ignore pos) (read-from-string fontbbox))
			       (setf fontbbox (subseq fontbbox pos))
			       (cond ((string= fontbbox "") (values nil nil))
				     (t (multiple-value-setq (asc pos) (read-from-string fontbbox))
					(values asc desc)))))))))))


      
(defvar ps*postscript.font.metrics '(
(:|Courier| 1085 795 290 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 600 600 600 600 600 600 600 600 600 600 600 600 600 NIL NIL NIL 600 600 600
 600 NIL 600 600 600 600 600 600 600 NIL NIL 600 NIL 600 600 600 600 600 600
 600 600 NIL 600 600 NIL 600 600 600 600 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL 600 NIL NIL NIL NIL 600 600 NIL 600 NIL
 NIL NIL NIL NIL NIL NIL NIL NIL 600 NIL NIL 600 600 NIL 600 NIL NIL NIL NIL)
(:|Courier-Bold| 1205 855 350 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 600 600 600 600 600 600 600 600 600 600 600 600 600 NIL NIL NIL 600 600 600
 600 NIL 600 600 600 600 600 600 600 NIL NIL 600 NIL 600 600 600 600 600 600
 600 600 NIL 600 600 NIL 600 600 600 600 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL 600 NIL NIL NIL NIL 600 600 NIL 600 NIL
 NIL NIL NIL NIL NIL NIL NIL NIL 600 NIL NIL 600 600 NIL 600 NIL NIL NIL NIL)
(:|Courier-Oblique| 1085 795 290 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 600 600 600 600 600 600 600 600 600 600 600 600 600 NIL NIL NIL 600 600 600
 600 NIL 600 600 600 600 600 600 600 NIL NIL 600 NIL 600 600 600 600 600 600
 600 600 NIL 600 600 NIL 600 600 600 600 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL 600 NIL NIL NIL NIL 600 600 NIL 600 NIL
 NIL NIL NIL NIL NIL NIL NIL NIL 600 NIL NIL 600 600 NIL 600 NIL NIL NIL NIL)
(:|Courier-BoldOblique| 1205 855 350 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600 600
 600 600 600 600 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 600 600 600 600 600 600 600 600 600 600 600 600 600 NIL NIL NIL 600 600 600
 600 NIL 600 600 600 600 600 600 600 NIL NIL 600 NIL 600 600 600 600 600 600
 600 600 NIL 600 600 NIL 600 600 600 600 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL 600 NIL NIL NIL NIL 600 600 NIL 600 NIL
 NIL NIL NIL NIL NIL NIL NIL NIL 600 NIL NIL 600 600 NIL 600 NIL NIL NIL NIL)
(:|Helvetica| 1156 939 217 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL 278 278 355 556 556 889 667 222 333 333 389 584 278 333 278
 278 556 556 556 556 556 556 556 556 556 556 278 278 584 584 584 556 1015 667
 667 722 722 667 611 778 722 278 500 667 556 833 722 778 667 778 722 667 611
 722 667 944 667 667 611 278 278 278 469 556 222 556 556 500 556 556 278 556
 556 222 222 500 222 833 556 556 556 556 333 500 278 556 500 722 500 500 500
 334 260 334 584 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 333 556 556 167 556 556 556 556 191 333 556 333 333 500 500 NIL 556 556 556
 278 NIL 537 350 222 333 333 556 1000 1000 NIL 611 NIL 333 333 333 333 333 333
 333 333 NIL 333 333 NIL 333 333 333 1000 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL 1000 NIL 370 NIL NIL NIL NIL 556 778 1000 365 NIL
 NIL NIL NIL NIL 889 NIL NIL NIL 278 NIL NIL 222 611 944 611 NIL NIL NIL NIL)
(:|Helvetica-Narrow| 1164 944 220 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL 228 228 291 456 456 729 547 182 273 273 319 479 228 273 228
 228 456 456 456 456 456 456 456 456 456 456 228 228 479 479 479 456 832 547
 547 592 592 547 501 638 592 228 410 547 456 683 592 638 547 638 592 547 501
 592 547 774 547 547 501 228 228 228 385 456 182 456 456 410 456 456 228 456
 456 182 182 410 182 683 456 456 456 456 273 410 228 456 410 592 410 410 410
 274 213 274 479 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 273 456 456 137 456 456 456 456 157 273 456 273 273 410 410 NIL 456 456 456
 228 NIL 440 287 182 273 273 456 820 820 NIL 501 NIL 273 273 273 273 273 273
 273 273 NIL 273 273 NIL 273 273 273 820 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL 820 NIL 303 NIL NIL NIL NIL 456 638 820 299 NIL
 NIL NIL NIL NIL 729 NIL NIL NIL 228 NIL NIL 182 501 774 501 NIL NIL NIL NIL)
(:|Helvetica-Bold| 1157 936 221 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL 278 333 474 556 556 889 722 278 333 333 389 584 278 333 278
 278 556 556 556 556 556 556 556 556 556 556 333 333 584 584 584 611 975 722
 722 722 722 667 611 778 722 278 556 722 611 833 722 778 667 778 722 667 611
 722 667 944 667 667 611 333 278 333 584 556 278 556 611 556 611 556 333 611
 611 278 278 556 278 889 611 611 611 611 389 556 333 611 556 778 556 556 500
 389 280 389 584 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 333 556 556 167 556 556 556 556 238 500 556 333 333 611 611 NIL 556 556 556
 278 NIL 556 350 278 500 500 556 1000 1000 NIL 611 NIL 333 333 333 333 333 333
 333 333 NIL 333 333 NIL 333 333 333 1000 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL 1000 NIL 370 NIL NIL NIL NIL 611 778 1000 365 NIL
 NIL NIL NIL NIL 889 NIL NIL NIL 278 NIL NIL 278 611 944 611 NIL NIL NIL NIL)
(:|Helvetica-Oblique| 1156 939 217 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL 278 278 355 556 556 889 667 222 333 333 389 584 278 333 278
 278 556 556 556 556 556 556 556 556 556 556 278 278 584 584 584 556 1015 667
 667 722 722 667 611 778 722 278 500 667 556 833 722 778 667 778 722 667 611
 722 667 944 667 667 611 278 278 278 469 556 222 556 556 500 556 556 278 556
 556 222 222 500 222 833 556 556 556 556 333 500 278 556 500 722 500 500 500
 334 260 334 584 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 333 556 556 167 556 556 556 556 191 333 556 333 333 500 500 NIL 556 556 556
 278 NIL 537 350 222 333 333 556 1000 1000 NIL 611 NIL 333 333 333 333 333 333
 333 333 NIL 333 333 NIL 333 333 333 1000 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL 1000 NIL 370 NIL NIL NIL NIL 556 778 1000 365 NIL
 NIL NIL NIL NIL 889 NIL NIL NIL 278 NIL NIL 222 611 944 611 NIL NIL NIL NIL)
(:|Helvetica-BoldOblique| 1157 936 221 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL 278 333 474 556 556 889 722 278 333 333 389 584 278 333 278
 278 556 556 556 556 556 556 556 556 556 556 333 333 584 584 584 611 975 722
 722 722 722 667 611 778 722 278 556 722 611 833 722 778 667 778 722 667 611
 722 667 944 667 667 611 333 278 333 584 556 278 556 611 556 611 556 333 611
 611 278 278 556 278 889 611 611 611 611 389 556 333 611 556 778 556 556 500
 389 280 389 584 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 333 556 556 167 556 556 556 556 238 500 556 333 333 611 611 NIL 556 556 556
 278 NIL 556 350 278 500 500 556 1000 1000 NIL 611 NIL 333 333 333 333 333 333
 333 333 NIL 333 333 NIL 333 333 333 1000 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL 1000 NIL 370 NIL NIL NIL NIL 611 778 1000 365 NIL
 NIL NIL NIL NIL 889 NIL NIL NIL 278 NIL NIL 278 611 944 611 NIL NIL NIL NIL)
(:|Times-Roman| 1156 904 252 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL 250 333 408 500 500 833 778 333 333 333 500 564 250 333 250
 278 500 500 500 500 500 500 500 500 500 500 278 278 564 564 564 444 921 722
 667 667 722 611 556 722 722 333 389 722 611 889 722 722 556 722 667 556 611
 722 722 944 722 722 611 333 278 333 469 500 333 444 500 444 500 444 333 500
 500 278 278 500 278 778 500 500 500 500 333 389 278 500 500 722 500 500 444
 480 200 480 541 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 333 500 500 167 500 500 500 500 180 444 500 333 333 556 556 NIL 500 500 500
 250 NIL 453 350 333 444 444 500 1000 1000 NIL 444 NIL 333 333 333 333 333 333
 333 333 NIL 333 333 NIL 333 333 333 1000 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL 889 NIL 276 NIL NIL NIL NIL 611 722 889 310 NIL
 NIL NIL NIL NIL 667 NIL NIL NIL 278 NIL NIL 278 500 722 500 NIL NIL NIL NIL)
(:|Times-Bold| 1221 965 256 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL 250 333 555 500 500 1000 833 333 333 333 500 570 250 333 250
 278 500 500 500 500 500 500 500 500 500 500 333 333 570 570 570 500 930 722
 667 722 722 667 611 778 778 389 500 778 667 944 722 778 611 778 722 556 667
 722 722 1000 722 722 667 333 278 333 581 500 333 500 556 444 556 444 333 500
 556 278 333 556 278 833 556 500 556 556 444 389 333 556 500 722 500 500 444
 394 220 394 520 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 333 500 500 167 500 500 500 500 278 500 500 333 333 556 556 NIL 500 500 500
 250 NIL 540 350 333 500 500 500 1000 1000 NIL 500 NIL 333 333 333 333 333 333
 333 333 NIL 333 333 NIL 333 333 333 1000 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL 1000 NIL 300 NIL NIL NIL NIL 667 778 1000 330 NIL
 NIL NIL NIL NIL 722 NIL NIL NIL 278 NIL NIL 278 500 722 556 NIL NIL NIL NIL)
(:|Times-Italic| 1182 930 252 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL 250 333 420 500 500 833 778 333 333 333 500 675 250 333 250
 278 500 500 500 500 500 500 500 500 500 500 333 333 675 675 675 500 920 611
 611 667 722 611 611 722 722 333 444 667 556 833 667 722 611 722 611 500 556
 722 611 833 611 556 556 389 278 389 422 500 333 500 500 444 500 444 278 500
 500 278 278 444 278 722 500 500 500 500 389 389 278 500 444 667 444 444 389
 400 275 400 541 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 389 500 500 167 500 500 500 500 214 556 500 333 333 500 500 NIL 500 500 500
 250 NIL 523 350 333 556 556 500 889 1000 NIL 500 NIL 333 333 333 333 333 333
 333 333 NIL 333 333 NIL 333 333 333 889 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL 889 NIL 276 NIL NIL NIL NIL 556 722 944 310 NIL
 NIL NIL NIL NIL 667 NIL NIL NIL 278 NIL NIL 278 500 667 500 NIL NIL NIL NIL)
(:|Times-BoldItalic| 1223 973 250 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL 250 389 555 500 500 833 778 333 333 333 500 570 250 333 250
 278 500 500 500 500 500 500 500 500 500 500 333 333 570 570 570 500 832 667
 667 667 722 667 667 722 778 389 500 667 611 889 722 722 611 722 667 556 611
 722 667 889 667 611 611 333 278 333 570 500 333 500 500 444 500 444 333 500
 556 278 278 500 278 778 556 500 500 500 389 389 278 556 444 667 500 444 389
 348 220 348 570 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 389 500 500 167 500 500 500 500 278 500 500 333 333 556 556 NIL 500 500 500
 250 NIL 500 350 333 500 500 500 1000 1000 NIL 500 NIL 333 333 333 333 333 333
 333 333 NIL 333 333 NIL 333 333 333 1000 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL 944 NIL 266 NIL NIL NIL NIL 611 722 944 300 NIL
 NIL NIL NIL NIL 722 NIL NIL NIL 278 NIL NIL 278 500 722 500 NIL NIL NIL NIL)
(:|Symbol| 1303 1010 293 NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL 250 333 713 500 549 833 778 439 333 333 500 549 250 549 250
 278 500 500 500 500 500 500 500 500 500 500 278 278 549 549 549 444 549 696
 660 710 612 652 763 603 765 351 631 724 686 918 739 750 768 741 580 592 632
 690 439 768 645 795 650 333 863 333 658 500 500 631 549 549 494 439 521 411
 603 329 603 549 549 576 521 549 549 521 549 603 439 576 713 686 493 686 494
 480 200 480 549 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
 620 247 549 167 713 500 753 753 753 753 1042 987 603 987 603 400 549 411 549
 549 713 494 460 549 549 549 549 1000 603 1000 658 823 686 795 987 768 768 823
 768 768 713 713 713 713 713 713 713 768 713 790 790 890 823 549 250 713 603
 603 1042 987 603 987 603 494 329 790 790 786 713 384 384 384 384 384 384 494
 494 494 494 790 329 274 686 686 686 384 384 384 384 384 384 494 494 494 NIL)
))



;;--------------------------------------------------------------------------
;;                            Auxillary Functions
;;--------------------------------------------------------------------------

(defun ps=get.current.short.date ()
  (multiple-value-bind (ignore1 ignore2 ignore3 date month yr)  ;;sec min hr
                       (get-decoded-time)
    (declare (ignore ignore1 ignore2 ignore3))
    (format nil "~D/~2,'0D/~2,'0D" month date (mod yr 100))))

(defun ps=get.current.date ()
  (multiple-value-bind (sec min hr date month yr)
		       (get-decoded-time)
    (format nil "~D/~2,'0D/~2,'0D  ~D:~2,'0D:~2,'0D" 
	    month date (mod yr 100) hr min sec)))

(defun ps=get.author ()
  (string-upcase (pro-environment-variable "USER")))
