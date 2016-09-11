;;; -*- Mode: LISP; Syntax: Common-lisp; Lowercase: Yes -*-

;;; 21.01.92 dh ---              completely revised version
;;; 12.08.92 mp inka-filename    edited :name-slot for XWindows
;;;  7. 7.93 mp ---              addapted for SunView

(in-package "USER")


;;;;;****************************************************************************************************
;;;;;
;;;;; This is the initial boot file to load and maintain the INKA-system
;;;;;
;;;;;****************************************************************************************************
;;;;;
;;;;; 3. Edit the value of *inka-pathname* and *inka-name* in this file (see below) 
;;;;;    if necessary and save the changed version
;;;;; 
;;;;; 5. If there are no binary files (or files of the wrong kind) in the bins-subdirectory then
;;;;;       - remove all files in this subdirectory
;;;;;       - enter common lisp 
;;;;;       - load this file
;;;;;       - type: "4" to choose the compilation of the INKA-system
;;;;;       - exit common lisp
;;;;;
;;;;;****************************************************************************************************
;;;;;
;;;;; How to start INKA:
;;;;;
;;;;;       - enter common lisp
;;;;;       - if you use lucid common lisp initialize the window system: (initialize-windows ...)
;;;;;       - load this directory
;;;;;       - choose "2" to load the binaries
;;;;;       - enter the INKA-package :  (in-package :inka)
;;;;;       - start inka :  (@inka)
;;;;;
;;;;;*****************************************************************************************************


(cond ((not (find-package "INKA"))
       (make-package "INKA" :use (package-use-list (cond ((find-package 'user))
							 ((find-package 'common-lisp-user)))))))


(in-package "INKA")


(PROCLAIM '(OPTIMIZE (SPEED 3) (SAFETY 1) (compilation-speed 0)))


;;;;;**************************************************************************************************
;;;;;
;;;;;  Please change the following lines for your requirements:
;;;;;
;;;;;  *inka-pathname* denotes the directory in which the INKA-system is installed
;;;;;  *inka-name*     stands for your favorite name of the system.
;;;;;
;;;;;***************************************************************************************************


(defvar *inka-pathname* *load-pathname*)

(defconstant *inka-name* "INKA 4.0")


(defconstant *inka-tk-wish* "wish8.0")


;;; Setting *inka-os*: the machine type and the os

(defconstant *inka-os* 
             #+LINUX86                    'I486
             #+(OR SOLARIS SPARC) #+SUN   'SUN
             #-(OR SUN LINUX86)           'UNKNOWN
	     )

;;; Setting *inka-lisp* : the lisp name

(defconstant *inka-lisp*
  
              #+ALLEGRO              'ALLEGRO
              #+LUCID                'LUCID
	      #-(OR ALLEGRO LUCID)   'UNKNOWN
	      )

;;; Setting *inka-lisp-version* the version number of the lisp.


(defconstant *inka-lisp-version*

             #+ALLEGRO-V5.0                  "5-0"
             #+ALLEGRO-V5.0.1                "5-1"
             #+ALLEGRO-V4.3                  "4-3"
             #+LCL4.1                        "4-1"
	     #+LCL4.0 #-LCL4.1               "4-0"
	     #+LCL3.0 #-LCL4.0               "3-0"
	     )



;;;;;****************** never change the following lines exept you are authorized to do that ************


(terpri *standard-output*)
(terpri *standard-output*)
(format *standard-output* "INKA - Bootstrap~%")
(format *standard-output* "----------------~%~%")
(terpri *standard-output*)

(cond ((null (probe-file (make-pathname :directory (append (pathname-directory *inka-pathname*) (list "tcl")))))
       (push :inkaidm *features*))
      ((null (probe-file (make-pathname :directory (append (pathname-directory *inka-pathname*) (list "idm")))))
       (push :inkatcl *features*))
      ((y-or-n-p "Apparently two window managers are available. Shall I use TCL ?")
       (push :inkatcl *features*))
      (t (push :inkaidm *features*)))


(defvar *inka-date* nil)

(defconstant *inka-source-file-type* "lisp")


(defconstant *inka-binary-file-type*
  (cond ((eq *inka-lisp* 'ALLEGRO) "fasl")
	((eq *inka-lisp* 'LUCID) "sbin")
	(t "bin")))


(defconstant *inka-protocol-file-type* "tex")


(defconstant *inka-files* 
	     '(  #+LUCID "process"
		 #+allegro "process_acl"
		 #+inkaidm "window_manager_motif"
		 #+inkatcl "window_manager_tcl"
		 "service"
		 "datastructure"
		 "unification"
		 "print"
		 "deduction"
		 "rule-interpreter"
		 "compile"
		 "normalization"
		 "satisfier"
		 "induction"
		 "generalization"
		 "expression_analyzer"
		 "example_generator"
		 "selection"
		 "recursion"
		 "editor"))


(defun inka-date ()

  ;;; Value:  the date the inka-system was loaded

  *inka-date*)


(defun inka-files ()

  ;;; Value:  a list of strings denoting all modules of the INKA-system

  *inka-files*)


(defun inka-name ()

  ;;; Value:  the name of the INKA-system.  Uh ? What ???

  *inka-name*)


(defun inka-filename (name type &optional relative.directory)

  ;;; Input: a string, a symbol like source, binary, protocol, or patch,
  ;;;        a filenamesuffix indicating the lisp dialect and a pathname
  ;;; Value: a pathname for the specified file in the inka-directory.
  ;;; Notice: symbolics do translates pathnames into uppercase if specified by the
  ;;;         normal keywords.
  
  (make-pathname :directory
		 (append (pathname-directory *inka-pathname*)			   
			 (cond (relative.directory (list relative.directory)))
			 (case type
			   (patch '("newpatches"))
			   (protocol '("prot"))
			   (binary (list (format nil "~A-~A-~A" *inka-os* *inka-lisp* *inka-lisp-version*)))
			   (source '("source"))))

		 :name (pathname-name name) :type 
		 (case type
		   (patch *inka-souce-file-type*)
		   (protocol *inka-protocol-file-type*)
		   (binary *inka-binary-file-type*)
		   (source *inka-source-file-type*))))


(defun inka=load.system (type)

  ;;; Input:   a symbol like source or binary
  ;;; Effect:  loads the complete INKA-system depending on the type and resets *inka-date*
  ;;; Value:   undefined.

  (mapc #'(lambda (file)
            (format *standard-output* "loading ~A ...~%"
		    (namestring (inka-filename file type)))
            (load (inka-filename file type) :verbose nil))
	*inka-files*)
  ; (load (inka-filename "repair" 'source) :verbose nil)
  (multiple-value-bind (hour min sec date month year) (get-decoded-time)
    (setq *inka-date* (format NIL "~D/~D/~D" date month year))))


(defun inka=compile.system (&optional no.loading)

  ;;; Input:   a flag whether the system has to be loaded first.
  ;;; Effect:  (optionally loads and) compiles the complete INKA-system
  ;;; Value:   undefined.

  (cond ((yes-or-no-p "Do you really want to compile the system ?")
	 (cond ((not no.loading) (inka=load.system 'source)))
	 (mapc #'(lambda (file)
		   (compile-file (inka-filename file 'source)
				 :output-file (inka-filename file 'binary))
		   (load (inka-filename file 'binary) :verbose nil))
	       *inka-files*))
	(t (inka=selection))))

  
(defun inka=selection ()

  ;;; Effect:  asks user what to do

  (format *standard-output* "1.) Loading all interpreted INKA-files.~%")
  (format *standard-output* "2.) Loading all compiled INKA-files, e.g. to create a suspendable system ~%")
  (format *standard-output* "3.) Compiling the whole INKA-system without loading it. ~%")
  (format *standard-output* "4.) Compiling the whole INKA-system and loading it before.~%")
  (format *standard-output* "5.) Documentation of all interface functions.~%")
  (format *standard-output* "Please choose one topic: ")
  (let ((choose (read *terminal-io*)))
    (cond ((eql choose 1) (inka=load.system 'source))
	  ((eql choose 2) (inka=load.system 'binary))
	  ((eql choose 3) (inka=compile.system t))
	  ((eql choose 4) (inka=compile.system nil))
	  ((eql choose 5)
	   (load (inka-filename "service" 'binary) :verbose nil)
	   (load (inka-filename "fileservice" 'binary) :verbose nil)
	   (protocol.inka)))))


(inka=load.system 'binary)

(@inka)











