;;; -*- Syntax: Common-Lisp; Package: INKA -*-

(in-package :inka)

(DEFVAR GEN*START 1)
(DEFVAR GEN*ACTUAL.POWER 0)
(DEFVAR GEN*FINAL.POWER 8)
(defvar gen*all.possibilities nil)
(defvar gen*all.possibilities.result nil)




(DEFUN GEN-GENERALIZE (GTERM NAME DEPTH)

  ;;; Edited : 02-08-92 by cs
  ;;; Input  : a gterm, its name and the induction depth
  ;;; Effect : tries to generalize \verb$GTERM$ by replacing subterms through new variables, since we deal with
  ;;;          negated clause form the subterms are replaced by new skolem constants
  ;;; Value  : the generalized \verb$GTERM$, or the gterm denoting the formula "true" if generalization was not successful

  (COND ((AND (>= DEPTH GEN*START) (GEN=GENERALIZE.SUBTERMS GTERM))
	 GTERM)
	(T (DA-LITERAL.TRUE))))


(DEFUN GEN=GENERALIZE.SUBTERMS (GTERM)

  ;;; EDITED : 02-08-92 BY CS
  ;;; INPUT  : A GTERM
  ;;; EFFECT : STARTING FROM THE VARIABLES (RESP. SKOLEM CONSTANTS) OF THE CORRESPONDING FOMRULA OF GTERM,
  ;;;          THIS FUNCTION GOES TO ALL SUPERTERMS AND
  ;;;          TRIES TO REPLACE THEM THROUGH NEW VARIABLES (RESP. SKOLEM CONSTANTS)
  ;;; VALUE  : T, IF GENERALIZATION IS SUCCESSFUL, NIL ELSE
 
  (LET* ((ALIST (GEN=GTERM.SKOLEM.OCCURRENCES GTERM)))
    (COND ((GEN=INSPECT.SUPERTERMS GTERM (GEN=REMOVE.SINGLES.AND.SUPERS ALIST))
	   (GEN=GENERALIZE.SUBTERMS GTERM)
	   T)
	  ((GEN=REPLACE.PRIMARY.TERMS ALIST GTERM)))))



(DEFUN GEN=INSPECT.SUPERTERMS (GTERM ALIST)
  ;;; EDITED : 02-08-92 BY CS
  ;;; INPUT  : A GTERM AND AN ASSOCIATION LIST OF TERMS OF GTERM WITH THEIR OCCURRENCES
  ;;; EFFECT : STARTING FROM THE SUBTERMS OF GTERM IN ALIST, THIS FUNCTION GOES TO ALL SUPERTERMS AND
  ;;;          TRIES TO REPLACE THEM THROUGH NEW VARIABLES (RESP. SKOLEM CONSTANTS)
  ;;; VALUE  : T, IF GENERALIZATION IS SUCCESSFUL, NIL ELSE

  (COND (ALIST
	 (LET ((SUPER.ALIST (GEN=REMOVE.SINGLES.AND.SUPERS (GEN=MAKE.SUPERTERMS ALIST GTERM))))
	   (COND ((GEN=INSPECT.SUPERTERMS GTERM SUPER.ALIST))
		 (T (GEN=REPLACE.AND.CHECK SUPER.ALIST GTERM)))))))


(defun gen=gterm.skolem.occurrences (gterm)

  ;;; EDITED : 02-08-92 BY CS
  ;;; INPUT  : A GTERM
  ;;; EFFECT : COLLECTS ALL VARIABLES WITH ITS OCCURRENCES OF GTERM AS AN ALIST
  ;;; VALUE  : THE ABOVE MENTIONED ALIST

  (mapcar #'(lambda (skolem)
	      (cons (da-term.create skolem) (da-symbol.occurs.in.gterm skolem gterm)))
	  (da-gterm.constants gterm 'skolem)))


(defun gen=remove.singles.and.supers (alist)

  ;;; EDITED : 02-80-92 BY CS
  ;;; INPUT  : AN ASSOC LIST, TERM AND ITS OCCURRENCES (AS TAFS)
  ;;; EFFECT : 1. REMOVES THOSE TERMS THAT HAVE ONLY A SINGLE OCCURRENCE
  ;;;          2. REMOVES THOSE TERMS WHICH ARE SUPERTERMS OF OTHER TERMS IN ALIST
  ;;; VALUE  : THE MODIFIED ALIST

  (remove-if #'(lambda (entry)
		 (or (null (cdr (cdr entry)))
		     (some #'(lambda (other.entry)
			       (and (not (eq entry other.entry))
				    (remove nil (da-gterm.occurs.in.gterm (car other.entry) (car entry)))))
			   alist)))
	     alist))



(DEFUN GEN=MAKE.SUPERTERMS (ALIST GTERM)
  ;;; EDITED : 02-08-92 BY CS
  ;;; INPUT  : AN ASSOCIATION LIST AND A GTERM
  ;;; EFFECT : CONSTRUCTS A NEW ALIST WITH THE SUPERTERMS OF THE TERMS IN ALIST
  ;;; VALUE  : THE NEW ALIST

  (LET (RESULT)
       (MAPC #'(LAMBDA (TAF)
		 (LET* ((SUPERTAF (DA-TAF.SUPER.TAF TAF))
			(SUBTERM (DA-ACCESS SUPERTAF GTERM))
			ENTRY)
		   (COND ((DA-LITERAL.IS SUBTERM))
			 ((SETQ ENTRY (ASSOC SUBTERM RESULT :TEST 'UNI-TERM.ARE.EQUAL))
			  (RPLACD ENTRY (ADJOIN SUPERTAF (CDR ENTRY):TEST 'EQUAL)))
			 (T (SETQ RESULT (ACONS SUBTERM (LIST SUPERTAF) RESULT))))))
	     (MAPCAN #'(LAMBDA (ENTRY) (COPY-LIST (CDR ENTRY))) ALIST))
       RESULT))






(DEFRULE GEN=REPLACE.AND.CHECK (&OTHERS ALIST GTERM) 
  ;;; EDITED : 02-08-92 BY CS
  ;;; INPUT  : AN ASSOC LIST AND A GTERM
  ;;; EFFECT : GENERALIZATION BY REPLACEMENT OF TERMS IN ALIST THROUGH NEW VARIABLES
  ;;; VALUE  ; T, IF GENERALIZATION IS SUCCESSFUL, NIL ELSE

  (GEN 10 ("replace and check"))

  (LET ((org.gterm (da-term.copy gterm)))
    (MAPC #'(LAMBDA (ENTRY)
	      (LET ((TAFS (CDR ENTRY))
		    (TERM (CAR ENTRY)))
		(RL-with.problem GTERM 'GTERM #'(LAMBDA (OBJ)
						  (COND
						   ;;; ((GEN=REPLACE.INDEPENDENT.AND.COVERING OBJ TERM TAFS))bis covering geloest
						   ((GEN=REPLACE.AND.CHECK.TERM OBJ TERM TAFS))
						   ((GEN=REPLACE.AND.CHECK.PRIMARY OBJ TERM TAFS)))))))
	  ALIST)
    (not (uni-gterm.are.equal gterm org.gterm))))



(DEFUN GEN=REPLACE.TERM (NEW.TERM TAFS OBJECT)
  ;;; EDITED : 04-08-92 BY CS
  ;;; INPUT  : A NEW TERM WHICH IS TO BE REPLACED AT ALL OCCURRENCES (TAFS) IN OBJECT
  ;;; VALUE  : THE MODIFIED GTERM

  (MAPC #'(LAMBDA (TAF)
		  (RL-OBJECT.CHANGE OBJECT NEW.TERM TAF))
	TAFS)
  OBJECT)


(DEFRULE GEN=REPLACE.INDEPENDENT.AND.COVERING (OBJECT &OTHERS TERM TAFS) 
  ;;; EDITED : 12-08-92 BY CS
  ;;; INPUT  : A OBJECT, A TERM WITH TAFS AS ITS OCCURRENCES
  ;;; EFFECT : REPLACES TERM AT ALL OCCURRENCES IN OBJECT

  (GEN 10 ("replace independent and covering"))

  (COND ((AND (GEN=TERM.IS.INDEPENDENT TERM TAFS (RL-OBJECT OBJECT))
	      (GEN=TERM.IS.COVERING TERM))
	 (GEN=REPLACE.TERM (DA-TERM.CREATE (DA-FUNCTION.CREATE NIL (DA-TERM.SORT TERM) NIL T)) TAFS OBJECT)
	 T)))
	 





(DEFRULE GEN=REPLACE.AND.CHECK.TERM (OBJECT &OTHERS TERM TAFS) 
  ;;; EDITED : 04-08-92 BY CS
  ;;; INPUT  : A SUBTERM OF OBJECT AT OCCURRENCES TAFS
  ;;; EFFECT : REPLACES ALL OCCURRENCES (TAFS) OF TERM IN OBJECT BY A NEW VARIABLE (A NEW SKOLEM CONSTANT),
  ;;;          AND CHECKS WHETHER THE RESULTING FORMULA IS NOT OBVIOUS FALSE, OR NOT

  (GEN 10 ("replace and check term"))

  (GEN=CHECKED.PROVABLE (RL-OBJECT (GEN=REPLACE.TERM (DA-TERM.CREATE (DA-FUNCTION.CREATE NIL (DA-TERM.SORT TERM) NIL T))
						     TAFS OBJECT))))
			



(DEFUN GEN=TERM.IS.INDEPENDENT (TERM TAFS GTERM)
  ;;; EDITED : 04-08-92 BY CS
  ;;; INPUT  : A SUBTERM OF GTERM AT OCCURRENCES TAFS
  ;;; VALUE  : T, IF TERM IS INDEPENDENT IN GTERM

  (NOT (SOME #'(LAMBDA (VAR)
		 (SOME #'(LAMBDA (VARTAF)
			   (EVERY #'(LAMBDA (TAF)
				      (NOT (DA-TAF.IS.SUBTAF TAF VARTAF)))
				  TAFS))
		       (DA-SYMBOL.OCCURS.IN.GTERM VAR GTERM)))
	     (DA-GTERM.CONSTANTS TERM 'SKOLEM))))
				   



(DEFUN GEN=TERM.IS.COVERING (TERM)
  ;;; EDITED : 04-08-92 BY CS
  ;;; INPUT  : A TERM
  ;;; VALUE  : T, IF TERM IS COVERING

  (Y-OR-N-P (FORMAT NIL "IST ~A ERSCHOEPFEND ?" TERM)))

  

(DEFUN GEN=REPLACE.PRIMARY.TERMS (ALIST GTERM)
  ;;; EDITED : 02-08-92 BY CS
  ;;; INPUT  : AN ASSOC LIST AND A GTERM
  ;;; EFFECT : REPLACEMENT OF THE TERMS IN ALIST AT PRIMARY POSITIONS
  ;;; VALUE  : T, IF GENERALIZATION IS SUCCESSFUL, NIL ELSE

  (LET ((org.gterm (da-gterm.copy gterm)))
    (MAPC #'(LAMBDA (ENTRY)
	      (RL-with.problem GTERM 'GTERM #'(LAMBDA (OBJ)
						(GEN=REPLACE.AND.CHECK.PRIMARY OBJ (CAR ENTRY) (CDR ENTRY)))))
	     ALIST)
    (not (uni-gterm.are.equal org.gterm gterm))))

  
			   

(DEFRULE GEN=REPLACE.AND.CHECK.PRIMARY (OBJECT &OTHERS TERM TAFS) 
  ;;; EDITED : 04-08-92 BY CS
  ;;; INPUT  : A SUBTERM OF OBJECT AT OCCURRENCES TAFS
  ;;; EFFECT : REPLACES PRIMARY OCCURRENCES OF TERM IN OBJECT (PROBABLY MORE) AND CHECKS
  ;;;          WHETHER THE RESULTING FORULA IS NOT OBVIOUS FALSE
  ;;; VALUE  : T, IF THE MODIFIED OBJECT IS NOT OBVIOUS FALSE, NIL ELSE

  (GEN 10 ("replace and check primary"))

  (LET ((NEW.TERM (DA-TERM.CREATE (DA-FUNCTION.CREATE NIL (DA-TERM.SORT TERM) NIL T)))
	PRIMARY
	OTHER)
       (SETQ GEN*ACTUAL.POWER 0)
       (MULTIPLE-VALUE-SETQ (PRIMARY OTHER) (GEN=DIVIDE.TAFS.IN.PRIMARY.AND.OTHER TAFS (RL-OBJECT OBJECT)))
       (COND ((NULL OTHER) NIL)
	     ((< (LENGTH PRIMARY) 2) NIL)
	     ((GEN=CHECKED.PROVABLE (RL-OBJECT (GEN=REPLACE.TERM NEW.TERM PRIMARY OBJECT))))
	     ((GEN=REPLACE.SOME.TAFS OBJECT OTHER NEW.TERM NIL)))))
			   



(DEFUN GEN=DIVIDE.TAFS.IN.PRIMARY.AND.OTHER (TAFS GTERM)
  ;;; EDITED : 05-08-92 BY CS
  ;;; INPUT  : A LIST OF TAFS AND A GTERM
  ;;; EFFECT : DIVIDES THE TAFS IN THOSE DENOTING TERMS AT PRIMARY POSITIONS AND THE REST
  ;;; VALUES  : PRIMARY TAFS AND THE OTHER TAFS

  (LET (PRIMARY OTHER)
       (MAPC #'(LAMBDA (TAF)
		       (COND ((GEN=TAF.IS.PRIMARY.POSITION TAF GTERM)
			      (SETQ PRIMARY (CONS TAF PRIMARY)))
			     (T (SETQ OTHER (CONS TAF OTHER)))))
	     TAFS)
       (VALUES PRIMARY OTHER)))



(DEFUN GEN=TAF.IS.PRIMARY.POSITION (TAF GTERM)
  ;;; EDITED : 05-08-92 BY CS
  ;;; INPUT  : A TAF AND A GTERM
  ;;; VALUE  : T, IF TAF DENOTES A TERM AT A PRIMARY POSITION IN GTERM

  (COND ((DA-LITERAL.IS (DA-ACCESS TAF GTERM)))
	(T (LET* ((SUPERTERM (DA-ACCESS (DA-TAF.SUPER.TAF TAF) GTERM))
		  (SUPERTERM.REC.POSITIONS (DA-PREFUN.REC.POSITIONS (DA-GTERM.SYMBOL SUPERTERM))))
		 (AND (OR (NULL SUPERTERM.REC.POSITIONS)
			  (MEMBER (DA-TAF.POSITION TAF) SUPERTERM.REC.POSITIONS))
		      (GEN=TAF.IS.PRIMARY.POSITION (DA-TAF.SUPER.TAF TAF) GTERM))))))



(DEFRULE GEN=REPLACE.SOME.TAFS (OBJECT &OTHERS TAFS REPLACEMENT ALL) 
  ;;; EDITED : 05-08-92 BY CS
  ;;; INPUT  : AN OBJECT, A LIST OF TAFS, A TERM AND AND INDICATOR (ALL)
  ;;; EFFECT : TRIES TO REPLACE SOME OF THE TERMS AT OCCURRENCES TAFS BY REPLACEMENT,
  ;;;          IF ALL = T, THEN ALL OCCURRENCES ARE ALLOWED TO BE REPLACED, ELSE THERE MUST BE AT LEAST ONE OCCURENCE WHICH
  ;;;          IS NOT TO BE REPLACED, FURTHERMORE CHECKES WHETHER THE RESULTING GTERM DENOTES A FORMULA WHICH IS NOT OBVIOUS FALSE
  ;;; VALUE  : T, IF GENERALIZATION IS SUCCESSFUL, NIL OTHERWISE

  (GEN 10 ("replace some tafs"))

  (COND ((AND TAFS (< GEN*ACTUAL.POWER GEN*FINAL.POWER))
	 (LET ((TAF (CAR TAFS))
	       (REST (CDR TAFS)))
	      (COND ((GEN=REPLACE.SOME.TAFS OBJECT REST REPLACEMENT T))
		    ((OR REST ALL)
		     (INCF GEN*ACTUAL.POWER)
		     (RL-OBJECT.CHANGE OBJECT REPLACEMENT TAF)
		     (COND ((GEN=CHECKED.PROVABLE (RL-OBJECT OBJECT)))
			   ((GEN=REPLACE.SOME.TAFS OBJECT REST REPLACEMENT ALL)))))))))

(defun gen=checked.provable (gterm)
  (cond ((gen=prove.gterm gterm)
	 (cond (gen*all.possibilities
		(push (da-gterm.copy gterm) gen*all.possibilities.result)
		nil)
	       (t t)))))


(DEFUN GEN=CHECKED.PROVABLE.old (GTERM)
  ;;; EDITED : 05-08-92 BY CS
  ;;; INPUT  : A GTERM IN RULE FORMAT
  ;;; EFFECT : CHECKS WHETHER THE DENOTED FORMULA IS NOT OVIOUSLY FALSE
  ;;; VALUE  : T, IF FORMULA IS NOT OBVIOUSLY FALSE, NIL ELSE

  (LET ((SKOLEM.TERMS (DELETE-DUPLICATES (GEN=GET.ALL.SKOLEM.TERMS GTERM) :TEST #'UNI-TERM.ARE.EQUAL))
	(VARIABLES (DELETE-DUPLICATES (DA-GTERM.VARIABLES GTERM) :TEST #'EQ))
	SUBSTITUTION)
    (MAPC #'(LAMBDA (VAR)
	      (SETQ SUBSTITUTION (UNI-TERMSUBST.CREATE SUBSTITUTION (DA-TERM.CREATE VAR)
						       (DA-TERM.CREATE (DA-FUNCTION.CREATE NIL (DA-SYMBOL.SORT VAR) NIL T)))))
	  VARIABLES)
    (MAPC #'(LAMBDA (TERM)
	      (SETQ SUBSTITUTION (UNI-TERMSUBST.CREATE SUBSTITUTION TERM (DA-TERM.CREATE (DA-VARIABLE.CREATE (DA-TERM.SORT TERM))))))
	  SKOLEM.TERMS)
    (SETQ GTERM (UNI-TERMSUBST.APPLY SUBSTITUTION GTERM))
    
    (COND ((SAT-SATISFY.GTERM GTERM) T))))

  ;(FORMAT *STANDARD-OUTPUT* "~%~A~%" (PR-PRINT.FORMULA (RL-OBJECT GTERM)))
  ;(Y-OR-N-P "FORMULA O.K. ?"))




(DEFUN GEN=GET.ALL.SKOLEM.TERMS (GTERM)
  (COND ((AND (DA-TERM.IS GTERM)
	      (DA-FUNCTION.IS (DA-TERM.SYMBOL GTERM))
	      (DA-FUNCTION.SKOLEM (DA-TERM.SYMBOL GTERM)))
	 (LIST GTERM))
	(T (MAPCAN #'GEN=GET.ALL.SKOLEM.TERMS (DA-GTERM.TERMLIST GTERM)))))





(defun gen-generalize.all.possibilities (gterm)
  (let ((gen*all.possibilities t)
	(gen*all.possibilities.result nil))
    (gen=generalize.subterms gterm)
    gen*all.possibilities.result))


(defun gen-generalize.tafs (gterm tafs)
  (let (all.tafs intersection.tafs)
    (cond ((null tafs) gterm)
	  (t (setq all.tafs (da-gterm.occurs.in.gterm (da-access (first tafs) gterm) gterm))
	     (setq intersection.tafs (intersection all.tafs tafs :test #'equal))
	     (gen-generalize.tafs (gen-generalize.replace.tafs gterm intersection.tafs)
				  (set-difference tafs intersection.tafs :test #'equal))))))


(defun gen-generalize.replace.tafs (gterm tafs)
  (let ((part.gterm (da-access (first tafs) gterm))
	new.gterm)
    (cond ((da-term.is part.gterm)
	   (setq new.gterm (da-term.create (da-function.create nil (da-term.sort part.gterm) nil T))))
	  (t (setq new.gterm (da-literal.true))))
    (mapc #'(lambda (taf)
	      (setq gterm (da-replace taf gterm new.gterm)))
	  tafs)
    gterm))
  
	   




(defun gen=prove.gterm (gterm)
  (let* ((skolem.constants (da-gterm.constants gterm 'skolem))
	 (assignments (gen=get.assignments skolem.constants))
	 result)
    (cond ((some #'(lambda (assignment)
		     (and (da-literal.is (setq result (gen=simplify.assignment gterm  skolem.constants assignment)))
			  (da-literal.is.true result)))
		 assignments)
	   nil)
	  (t t))))


(defun gen=simplify.assignment (gterm constants assignment)
  (let ((new.gterm (da-gterm.copy gterm)))
    (mapc #'(lambda (constant term)
	      (mapc #'(lambda (taf)
			(setq new.gterm (da-replace taf new.gterm (da-term.copy term))))
		    (da-symbol.occurs.in.gterm constant new.gterm)))
	  constants assignment)
    (eg-eval new.gterm)))


(defun gen=get.assignments (constants)
  (let ((maximum 3) result)
    (dotimes (i maximum)
      (push (mapcan #'(lambda (constant)
			(let* ((examples (da-sort.examples (da-symbol.sort constant)))
			       (le (length examples)))
			  (cond ((eql le 0) (list (da-term.create constant)))
				(t (list (da-term.copy (nth (random le) examples)))))))
		    constants)
	    result))
    result))