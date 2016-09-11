;;; -*- Syntax: Common-lisp; Package: INKA; Mode: LISP; Base: 10 -*-
;;; $Header: /home/inka/system-4-0/source/RCS/process.lisp,v 1.2 1997/08/20 08:03:14 serge Exp hutter $

;;; 06.01.93 de ---                         add comments 

(IN-PACKAGE :inka)

;;;;;    **************************************************************
;;;;;    *                                                            *
;;;;;    * The PROCESS-Handling of the INKA-System.                   *
;;;;;    * ========================================                   *
;;;;;    *                                                            *
;;;;;    **************************************************************
;;;;;
;;;;;    Note that all functions in this module are extensions to Common Lisp for Lucid Common LISP
;;;;;


(defun pro-process.actual.process () multiprocessing:*current-process*)


(defun pro-run.foreign.process (filename input.stream output.stream error.output wait.fct arguments)

  (let (process)
    (setq process (run-program filename arguments :input input.stream :output output.stream :error error.output
			       :wait wait.fct))
    (values (process-input process) (process-output process) (process-output process))))



(defun PRO-ENVIRONMENT-VARIABLE (string)

  (assoc (cond ((string-equal string "INKA") :INKA)
	       ((string-equal string "USER") :USER)
	       ((string-equal string "PROOFDIR") :PROOFDIR))
	 *ENVIRONMENT-LIST*))


(defmacro pro-without.scheduling (&body body)

  `(multiprocessing:without-scheduling (progn . ,body)))


(defun pro-quit () (quit))

				
(defmacro pro-process.create (&key name function args wait-function wait-args)

  ;;;  Input:  name:          name of process
  ;;;          function:      the initial function which starts the process
  ;;;          args:          list of arguments to the initial function
  ;;;          wait-function: the wait function is used by the scheduler to test whether
  ;;;                         the process should run
  ;;;          wait-args:     list of arguments to the wait function
  ;;;  Effect: A process is created.
  ;;;  Value:  A process
  
  (append (list 'multiprocessing:make-process function :name name)
	  (cond ((neq wait-function nil) (list :wait-function wait-function)))
	  (cond ((neq wait-args nil) (list :wait-args wait-args)))))

		
(defun pro-process.is.active (process)

  ;;;  Input:  A process
  ;;;  Effect: Test the state of the process.
  ;;;          A process is active, if it is either running or waiting to run.
  ;;;          A process is inactive, if it is a process that is alive but that cannot be run.
  ;;;          A process is dead, if it has been killed or if it has run to completion.
  ;;;  Value:  True, if the process is activ, otherwise Nil.
  
  (eq (multiprocessing:process-state process) :active))


(defmacro pro-process.wait (whostate function &rest args)

  ;;;  Input:  whostate: specifies a string that will be displayed as the state of the process
  ;;;          function: the wait function is used by the scheduler to test whether the process should run
  ;;;          args:     list of arguments to the wait function
  ;;;  Effect: Suspends the process until function returns a non-nil value when applied to args.
  ;;;  Value:  The non-nil value
  
  `(multiprocessing:process-wait ,whostate ,function ,@args))


(defmacro pro-process.wait.with.timeout (whostate seconds function &rest args)

  ;;;  Input:  seconds: the number of seconds to wait
  ;;;          whostate: specifies a string that will be displayed as the state of the process
  ;;;          function: the wait function is used by the scheduler to test whether the process should run
  ;;;          args:     list of arguments to the wait function
  ;;;  Effect: Suspends the process until the function argument returns a non-nil value or the time is out.
  ;;;  Value:  The non-nil value or Nil, if timeout.
  
  `(multiprocessing:process-wait-with-timeout ,whostate ,seconds ,function ,@args))


(defun pro-process.restart (process)

  ;;;  Input:  A process 
  ;;;  Effect: The process is restarted. It reapplies its initial function, which has been specified when the
  ;;;          process was created, to its initial arguments. Cannot be restarted the initial process, or
  ;;;          a process that has been killed.
  ;;;  Value:  The restarted process
  
  (multiprocessing:restart-process process))


(defun pro-process.activate (process)

  ;;;  Input:  A process
  ;;;  Effect: A inactive process is activated.
  ;;;  Value:  The activated process
  
  (multiprocessing:enable-process process))


(defun pro-process.deactivate (process)

  ;;;  Input:  A process
  ;;;  Effect: A active process is deactivated.
  ;;;  Value:  The deactivated process
  
  (multiprocessing:disable-process process))


(defmacro pro-process.interrupt (process function &rest args)

  ;;;  Input:  process:  a process
  ;;;          function: a function
  ;;;          args:     the arguments of function
  ;;;  Effect: The execution of process is interrupted and the specified function argument is invoked.
  ;;;          The process resumes its previous computation when the interruption returns.
  ;;;  Value:  The interrupted process
  
  `(multiprocessing:process-interrupt ,process ,function ,@args))


(defun pro-process.kill (process)

  ;;;  Input:  A process
  ;;;  Effect: The process is killed. The process cannot be restarted.
  ;;;  Value:  The killed process
  
  (multiprocessing:destroy-process process))

