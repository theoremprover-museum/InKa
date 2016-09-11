;;; -*- Syntax: Common-lisp; Package: INKA; Mode: LISP; Base: 10 -*-

;;; 06.01.93 de ---                         add comments 

(IN-PACKAGE :inka)

;;;;;    **************************************************************
;;;;;    *                                                            *
;;;;;    * The PROCESS-Handling of the INKA-System.                   *
;;;;;    * ========================================                   *
;;;;;    *                                                            *
;;;;;    **************************************************************
;;;;;
;;;;;    Note that all functions in this module are extensions to Common Lisp for Allegro Common Lisp
;;;;;


(defun pro-process.actual.process () mp:*current-process*)


(defun pro-run.foreign.process (filename input.stream output.stream error.output wait.fct arguments)

  (excl:run-shell-command (format nil "~A ~{~A ~}" filename arguments)
			  :input input.stream :output output.stream :error-output error.output
			  :wait wait.fct))



(defun PRO-ENVIRONMENT-VARIABLE (string)

  (system:getenv string))


(defmacro pro-without.scheduling (&body body)

  `(excl:without-interrupts ,@body))


(defun pro-quit () (exit))


				
(defmacro pro-process.create (&key name function args)

  ;;;  Input:  name:          name of process
  ;;;          function:      the initial function which starts the process
  ;;;          args:          list of arguments to the initial function
  ;;;          wait-function: the wait function is used by the scheduler to test whether
  ;;;                         the process should run
  ;;;          wait-args:     list of arguments to the wait function
  ;;;  Effect: A process is created.
  ;;;  Value:  A process
  
  `(mp:process-run-function ,name ,function ,@args))

		
(defun pro-process.is.active (process)

  ;;;  Input:  A process
  ;;;  Effect: Test the state of the process.
  ;;;          A process is active, if it is either running or waiting to run.
  ;;;          A process is inactive, if it is a process that is alive but that cannot be run.
  ;;;          A process is dead, if it has been killed or if it has run to completion.
  ;;;  Value:  True, if the process is activ, otherwise Nil.
  
  (if (mp:process-active-p process) t nil))


(defmacro pro-process.wait (whostate function &rest args)

  ;;;  Input:  whostate: specifies a string that will be displayed as the state of the process
  ;;;          function: the wait function is used by the scheduler to test whether the process should run
  ;;;          args:     list of arguments to the wait function
  ;;;  Effect: Suspends the process until function returns a non-nil value when applied to args.
  ;;;  Value:  The non-nil value
  
  `(mp:process-wait ,whostate ,function ,@args))


(defmacro pro-process.wait.with.timeout (whostate seconds function &rest args)

  ;;;  Input:  seconds: the number of seconds to wait
  ;;;          whostate: specifies a string that will be displayed as the state of the process
  ;;;          function: the wait function is used by the scheduler to test whether the process should run
  ;;;          args:     list of arguments to the wait function
  ;;;  Effect: Suspends the process until the function argument returns a non-nil value or the time is out.
  ;;;  Value:  The non-nil value or Nil, if timeout.
  
  `(mp:process-wait-with-timeout ,whostate ,seconds ,function ,@args))


(defun pro-process.activate (process)

  ;;;  Input:  A process
  ;;;  Effect: A inactive process is activated.
  ;;;  Value:  The activated process
  
  (mp:process-enable process))


(defun pro-process.deactivate (process)

  ;;;  Input:  A process
  ;;;  Effect: A active process is deactivated.
  ;;;  Value:  The deactivated process
  
  (mp:process-disable process))


(defmacro pro-process.interrupt (process function &rest args)

  ;;;  Input:  process:  a process
  ;;;          function: a function
  ;;;          args:     the arguments of function
  ;;;  Effect: The execution of process is interrupted and the specified function argument is invoked.
  ;;;          The process resumes its previous computation when the interruption returns.
  ;;;  Value:  The interrupted process
  
  `(mp:process-interrupt ,process ,function ,@args))


(defun pro-process.kill (process)

  ;;;  Input:  A process
  ;;;  Effect: The process is killed. The process cannot be restarted.
  ;;;  Value:  The killed process
  
  (mp:process-kill process))

